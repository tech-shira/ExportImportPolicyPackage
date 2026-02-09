import csv
import os
import tarfile
import sys
import copy
from functools import cmp_to_key
import json
import datetime
import re
import time

# Track script start time for total runtime reporting
SCRIPT_START_TIME = time.time()

# ---------------------------------------------------------------------------
# Progress / resume helpers
# ---------------------------------------------------------------------------
def _progress_file(api_type: str) -> str:
    base = os.environ.get("IMPORT_PROGRESS_DIR", "/var/tmp")
    safe = re.sub(r'[^A-Za-z0-9_.-]+', '_', str(api_type))
    return os.path.join(base, f"import_progress_{safe}.json")

def load_resume_index(api_type: str) -> int:
    env_idx = os.environ.get("IMPORT_RESUME_INDEX")
    if env_idx is not None and str(env_idx).strip() != "":
        try:
            return max(0, int(env_idx))
        except Exception:
            return 0
    try:
        pf = _progress_file(api_type)
        if os.path.exists(pf):
            with open(pf, "r") as f:
                data = json.load(f)
            return max(0, int(data.get("next_index", 0)))
    except Exception:
        pass
    return 0

def save_resume_index(api_type: str, next_index: int, extra: dict = None) -> None:
    try:
        pf = _progress_file(api_type)
        payload = {"next_index": int(next_index), "updated": datetime.datetime.utcnow().isoformat() + "Z"}
        if extra:
            payload.update(extra)
        with open(pf, "w") as f:
            json.dump(payload, f)
    except Exception:
        pass


from lists_and_dictionaries import (singular_to_plural_dictionary, generic_objects_for_rule_fields, import_priority,
                                    https_blades_names_map,
                                    commands_support_batch, rule_support_batch, not_unique_name_with_dedicated_api,
                                    types_not_support_tagging)
from utils import debug_log, create_payload, compare_versions, generate_new_dummy_ip_address, get_reply_err_msg

duplicates_dict = {}
position_decrements_for_sections = []
missing_parameter_set = set()
should_create_imported_nat_top_section = True
should_create_imported_nat_bottom_section = True
updatable_objects_repository_initialized = False
imported_nat_top_section_uid = None

# Section UIDs mapping for placing rules under correct sections
# Format: {layer_name: {section_name: {"uid": "...", "start_pos": X, "end_pos": Y}}}
section_uid_map = {}

def build_section_position_ranges(sections_data):
    """
    Build position ranges for sections.
    sections_data: list of dicts with 'name' and 'position' keys
    Returns: list of dicts with 'name', 'start', 'end' keys, sorted by position
    """
    sections_sorted = sorted(sections_data, key=lambda x: int(x['position']))
    ranges = []
    for i, section in enumerate(sections_sorted):
        start_pos = int(section['position'])
        # End position = before next section starts, or infinity if last section
        if i < len(sections_sorted) - 1:
            end_pos = int(sections_sorted[i + 1]['position']) - 1
        else:
            end_pos = 999999
        ranges.append({
            'name': section['name'],
            'start': start_pos,
            'end': end_pos
        })
    return ranges

def find_section_for_rule_position(rule_position, layer_name):
    """
    Find which section a rule should belong to based on its position.
    Returns: section name or None
    """
    global section_uid_map
    if layer_name not in section_uid_map:
        return None
    
    try:
        pos = int(rule_position)
        for section_name, section_data in section_uid_map[layer_name].items():
            if section_data['start'] <= pos <= section_data['end']:
                return section_name
    except (ValueError, KeyError):
        pass
    return None

def _shorten_backend_error(msg: str, max_len: int = 2000) -> str:
    """Avoid flooding stdout with massive backend SQL/IN-clause dumps.
    Keeps the beginning/end and collapses long runs of '?,' tokens.
    """
    if not msg:
        return msg
    # Collapse long sequences of "?, ?, ?, ..." that come from huge SQL bind lists
    msg = re.sub(r"(\?,\s*){200,}", "<... omitted bind params ...> ", msg)
    if len(msg) <= max_len:
        return msg
    head = msg[: int(max_len * 0.6)]
    tail = msg[-int(max_len * 0.4):]
    return head + "\n<... truncated ...>\n" + tail

name_collision_map = {}
changed_object_names_map = {}
commands_batch_version = "1.6"
rules_batch_version = "1.8.1"
api_current_version = None
add_tag_to_object_uid = None
imported_exception_groups = []
# Session keep-alive to prevent timeout during long imports
import time
last_keep_alive_time = None


# Default request timeout (seconds) for long-running API calls (e.g., add-access-section on large rulebases).
# Some python wrappers default to ~300s which can lead to 'not a valid JSON' / connection abort when the server
# keeps processing but the client gives up.
LONG_API_CALL_TIMEOUT_SECS = int(os.getenv("CP_API_LONG_TIMEOUT_SECS", "1800"))

def _api_call_with_timeout(client, command, payload, timeout_secs=LONG_API_CALL_TIMEOUT_SECS):
    """Call Management API with a longer timeout when supported by the client wrapper."""
    for kw in ("timeout", "request_timeout", "read_timeout"):
        try:
            return client.api_call(command, payload, **{kw: timeout_secs})
        except TypeError:
            pass
    return client.api_call(command, payload)

def _looks_like_timeout_or_disconnect(exc: Exception) -> bool:
    s = str(exc).lower()
    return (
        "not a valid json" in s
        or "connection abort" in s
        or "connection aborted" in s
        or "connection reset" in s
        or "read timed out" in s
        or "timed out" in s
    )

def wait_for_no_active_publish(client, max_wait_seconds=1800, poll_interval=5):
    """Avoid running rulebase mutations while a publish is still in progress."""
    start = time.time()
    while True:
        try:
            tasks = _api_call_with_timeout(client, "show-tasks", {"status": "in-progress", "details-level": "standard"})
            for t in tasks.get("tasks", []):
                if str(t.get("task-name", "")).lower().startswith("publish"):
                    if time.time() - start > max_wait_seconds:
                        raise TimeoutError("Timed out waiting for publish task to finish")
                    time.sleep(poll_interval)
                    break
            else:
                return
        except Exception:
            # If show-tasks fails for any reason, don't block import; just proceed.
            return


# Track failed batch chunk range so fallback to one-by-one can resume from failure point
FAILED_BATCH_RANGE = None  # (start_idx, end_idx) 0-based indices in data list
FAILED_BATCH_API_TYPE = None



def clone_globals_batch_rulebase():
    global should_create_imported_nat_top_section
    global should_create_imported_nat_bottom_section
    global imported_nat_top_section_uid
    return copy.copy(should_create_imported_nat_top_section), copy.copy(should_create_imported_nat_bottom_section), \
           copy.copy(imported_nat_top_section_uid)


def revert_to_before_rule_batch(should_create_imported_nat_top_section_clone,
                                    should_create_imported_nat_bottom_section_clone, imported_nat_top_section_uid_clone):
    global should_create_imported_nat_top_section
    global should_create_imported_nat_bottom_section
    global imported_nat_top_section_uid

    if should_create_imported_nat_top_section != should_create_imported_nat_top_section_clone:
        should_create_imported_nat_top_section = should_create_imported_nat_top_section_clone

    if should_create_imported_nat_bottom_section != should_create_imported_nat_bottom_section_clone:
        should_create_imported_nat_bottom_section = should_create_imported_nat_bottom_section_clone

    if imported_nat_top_section_uid != imported_nat_top_section_uid_clone:
        imported_nat_top_section_uid = imported_nat_top_section_uid_clone


def is_support_batch(api_type, version):
    return api_type in commands_support_batch and compare_versions(version, commands_batch_version) != -1


def is_support_rule_batch(api_type, version):
    return api_type in rule_support_batch and compare_versions(version, rules_batch_version) != -1


def import_objects(file_name, client, changed_layer_names, package, layer=None, args=None):
    global position_decrements_for_sections
    global api_current_version

    is_root_call = layer is None
    
def import_objects(file_name, client, changed_layer_names, package, layer=None, args=None):
    global position_decrements_for_sections
    global api_current_version

    is_root_call = layer is None

    export_tar = tarfile.open(file_name, "r:gz")
    export_tar.extractall()
    tar_files = export_tar.getmembers()

    general_object_files = [general_object_file for general_object_file in tar_files if
                            os.path.splitext(general_object_file.name)[1] == ".csv" or
                            os.path.splitext(general_object_file.name)[1] == ".json"]

    rulebase_object_files = [general_object_file for general_object_file in tar_files if
                             os.path.splitext(general_object_file.name)[1] == ".gz"]

    general_object_files.sort(key=cmp_to_key(compare_general_object_files))

    layers_to_attach = {"access": [], "threat": [], "https": []}

    if not general_object_files:
        debug_log("Nothing to import...", True)

    version_file_name = [f for f in tar_files if f.name == "version.txt"][0]
    version_support_batch = False
    version_support_rule_batch = False
    if api_current_version is None:
        api_versions = client.api_call("show-api-versions")
        if api_versions.success and "current-version" in api_versions.data:
            api_current_version = api_versions.data["current-version"]
    with open(version_file_name.name, 'rb') as version_file:
        version = version_file.readline()
        if isinstance(version, bytes):
            version = version.decode("utf-8")
        api_versions = client.api_call("show-api-versions")
        if not api_versions.success:
            debug_log("Error getting versions! Aborting import. " + str(api_versions), True, True)
            sys.exit(1)
        version_to_use = None
        if version in api_versions.data["supported-versions"]:
            client.api_version = version
            version_to_use = version
        else:
            debug_log(
                "The version of the imported package doesn't exist in this machine! import with this machines latest version. ",
                True, True)
            if "current-version" in api_versions.data:
                version_to_use = api_versions.data["current-version"]
        if version_to_use is not None and compare_versions(version_to_use, commands_batch_version) != -1:
            version_support_batch = True
        if version_to_use is not None and compare_versions(version_to_use, rules_batch_version) != -1:
            version_support_rule_batch = True
    
    # Pre-scan section files to build position ranges for rule placement
    # This is critical: sections MUST be processed before rules so we know where to place each rule
    global section_uid_map
    # Only reset section_uid_map on the top-level call (not on recursive calls for inline layers)
    if is_root_call:
        section_uid_map = {}  # Reset for this import session
    
    for general_object_file in general_object_files:
        _, file_extension = os.path.splitext(general_object_file.name)
        if file_extension != ".csv":
            continue
        api_call = general_object_file.name.split('__')[2]
        api_type = '-'.join(api_call.split('-')[1:])
        
        # Only process section files in this pre-scan
        if "section" in api_type and api_type in ("access-section", "https-section"):
            debug_log(f"Pre-scanning {api_type} file to build position ranges...", True)
            
            with open(general_object_file.name, 'rt', encoding='utf-8') as csv_file:
                reader = csv.DictReader(csv_file)
                sections_data = []
                for row in reader:
                    if 'name' in row and 'position' in row:
                        # Use the layer parameter passed to import_objects, not from CSV (often empty)
                        actual_layer = layer if layer else row.get('layer', 'unknown')
                        sections_data.append({
                            'name': row['name'],
                            'position': row['position'],
                            'layer': actual_layer
                        })
                
                # Build ranges for each layer
                layers_found = {}
                for section in sections_data:
                    layer_name = section['layer']
                    if layer_name not in layers_found:
                        layers_found[layer_name] = []
                    layers_found[layer_name].append(section)
                
                for layer_name, layer_sections in layers_found.items():
                    section_ranges = build_section_position_ranges(layer_sections)
                    if layer_name not in section_uid_map:
                        section_uid_map[layer_name] = {}
                    
                    for range_data in section_ranges:
                        section_uid_map[layer_name][range_data['name']] = {
                            'uid': None,  # Will be filled when section is created
                            'start': range_data['start'],
                            'end': range_data['end']
                        }
                    
                    debug_log(f"  Layer '{layer_name}': mapped {len(section_ranges)} sections", True)
    
    # CRITICAL: Import sections FIRST (before rules) so we have UIDs for rule placement
    # This pass only processes section files
    debug_log("=" * 80, True)
    debug_log("PHASE 1: Importing sections (to get UIDs for rule placement)...", True)
    debug_log("=" * 80, True)
    
    for general_object_file in general_object_files:
        _, file_extension = os.path.splitext(general_object_file.name)
        if file_extension != ".csv":
            continue
        api_call = general_object_file.name.split('__')[2]
        api_type = '-'.join(api_call.split('-')[1:])
        
        # Only process sections in this first pass
        if "section" not in api_type:
            continue
        if args.skip_import_sections:
            debug_log("Skip import {0}".format(api_type), True)
            continue
        
        # Process the section file (code below will handle it)
        counter = 1
        position_decrement_due_to_rules = 0
        position_decrement_due_to_sections = 0
        generic_type = None
        data = []
        if "generic" in api_call:
            generic_type = api_call.split("-")[3]
            api_call = "-".join(api_call.split("-")[0:3])
        
        debug_log("Adding " + (singular_to_plural_dictionary[client.api_version][api_type].replace('_', ' ')
                               if api_type in singular_to_plural_dictionary[
            client.api_version] else "generic objects of type " + api_type), True)

        with open(general_object_file.name, 'rt', encoding='utf-8') as csv_file:
            reader = csv.reader(csv_file)
            num_objects = len(list(reader)) - 1
            csv_file.seek(0)

            fields = next(reader)

            while True:
                line = next(reader, None)
                if line is None:
                    break
                line = [str(item) for item in line]
                data.append(line)

        # Import sections one-by-one (sections don't support batch)
        for line in data:
            counter, position_decrement_due_to_rules = add_object(line, counter, position_decrement_due_to_rules,
                                                                  position_decrement_due_to_sections, fields, api_type,
                                                                  generic_type, layer, layers_to_attach,
                                                                  changed_layer_names, api_call, num_objects, client, args, package)
        
        # Clean up - remove the section file after processing
        os.remove(general_object_file.name)
    
    debug_log("=" * 80, True)
    debug_log("PHASE 2: Importing all other objects (hosts, networks, rules, etc.)...", True)
    debug_log("=" * 80, True)
    
    for general_object_file in general_object_files:
        _, file_extension = os.path.splitext(general_object_file.name)
        if file_extension != ".csv":
            os.remove(general_object_file.name)
            continue
        api_call = general_object_file.name.split('__')[2]
        counter = 1
        position_decrement_due_to_rules = 0
        position_decrement_due_to_sections = 0
        generic_type = None
        data = []
        if "generic" in api_call:
            generic_type = api_call.split("-")[3]
            api_call = "-".join(api_call.split("-")[0:3])
        api_type = generic_type if generic_type else '-'.join(api_call.split('-')[1:])
        
        # Skip sections in this pass - they were already imported in Phase 1
        if "section" in api_type:
            debug_log("Skip {0} (already imported in Phase 1)".format(api_type), True)
            continue
        
        if args.skip_import_sections and "section" in api_type:
            debug_log("Skip import {0}".format(api_type), True)
            continue
        if api_type == "access-rule" or api_type == "https-rule":
            position_decrements_for_sections = []
        debug_log("Adding " + (singular_to_plural_dictionary[client.api_version][api_type].replace('_', ' ')
                               if api_type in singular_to_plural_dictionary[
            client.api_version] else "generic objects of type " + api_type), True)

        with open(general_object_file.name, 'rt', encoding='utf-8') as csv_file:
            reader = csv.reader(csv_file)
            num_objects = len(list(reader)) - 1
            csv_file.seek(0)

            fields = next(reader)

            while True:
                line = next(reader, None)
                if line is None:
                    break
                line = [str(item) for item in line]
                data.append(line)

        os.remove(general_object_file.name)

        client_version = client.api_version
        if api_current_version is not None:
            if is_support_batch(api_type, api_current_version):
                if compare_versions(client.api_version, commands_batch_version) == -1:
                    client.api_version = api_current_version
                version_support_batch = True
            elif is_support_rule_batch(api_type, api_current_version):
                if compare_versions(client.api_version, rules_batch_version) == -1:
                    client.api_version = api_current_version
                version_support_rule_batch = True

        support_batch = api_type in commands_support_batch and version_support_batch
        support_rule_batch = api_type in rule_support_batch and version_support_rule_batch
        
        # CRITICAL FIX: Disable batch mode for access-rule to ensure section mapping works correctly
        # Batch mode sends rules with numeric positions which bypass section UID mapping logic
        # One-by-one mode processes each rule through add_object() which maps to correct section
        if api_type == "access-rule":
            support_batch = False
            support_rule_batch = False
            debug_log("⚠ Batch mode disabled for access-rule to ensure correct section placement", True)

        should_create_imported_nat_top_section_clone = None
        should_create_imported_nat_bottom_section_clone = None
        imported_nat_top_section_uid_clone = None
        do_rule_batch_revert = False
        batch_succeeded = False
        batch_payload = None
        command = None

        if support_batch or support_rule_batch:
            is_rule_type = api_type in rule_support_batch
            if is_rule_type:
                should_create_imported_nat_top_section_clone, should_create_imported_nat_bottom_section_clone, \
                imported_nat_top_section_uid_clone = clone_globals_batch_rulebase()
                do_rule_batch_revert = True

            batch_payload = create_batch_payload(api_type, data, fields, client, args, is_rule_type,
                                                 changed_layer_names, generic_type, layer, layers_to_attach, package)
            command = "add-objects-batch"
            if is_rule_type:
                command = "add-rules-batch"
            batch_succeeded = add_batch_objects(api_type, command, client, args, batch_payload)

        client.api_version = client_version
        if not batch_succeeded:
            if support_batch or support_rule_batch:
                debug_log("Batch import failed for {0}, falling back to one-by-one import of {1} objects".format(
                    api_type, len(data)), True)
            if do_rule_batch_revert:
                # Revert rule batch globals
                revert_to_before_rule_batch(should_create_imported_nat_top_section_clone,
                                                should_create_imported_nat_bottom_section_clone,
                                                imported_nat_top_section_uid_clone)
            # CRITICAL FIX: When batch fails, resume from the failed chunk onwards
            # Don't re-import objects that already succeeded in previous chunks!
            data_to_import = data
            try:
                global FAILED_BATCH_RANGE, FAILED_BATCH_API_TYPE
                if FAILED_BATCH_API_TYPE == api_type and FAILED_BATCH_RANGE:
                    s_idx, e_idx = FAILED_BATCH_RANGE
                    # Only import from the failed chunk onwards (chunks before succeeded!)
                    data_to_import = data[s_idx:]
                    debug_log("Batch failed at chunk {0}-{1}, resuming one-by-one from index {2} ({3} remaining objects)".format(
                        s_idx + 1, e_idx, s_idx, len(data_to_import)), True, True)
            finally:
                # Reset so we don't accidentally reuse the range for another type
                FAILED_BATCH_RANGE = None
                FAILED_BATCH_API_TYPE = None

            # Counter for intermediate publish to prevent backend performance degradation
            section_counter = 0
            sections_per_publish = int(os.environ.get("IMPORT_SECTIONS_PER_PUBLISH", "20"))
            
            for line in data_to_import:
                # Small delay between sections since we're using async task mode
                import time
                if api_type in ("access-section", "https-section"):
                    # Brief rest to avoid overwhelming server, task polling handles the wait
                    rest_sec = float(os.environ.get("IMPORT_SECTION_DELAY_SEC", "2"))
                    debug_log("Waiting {0}s before next section...".format(rest_sec), True)
                    time.sleep(rest_sec)
                    
                    # Publish every N sections to reset backend performance
                    section_counter += 1
                    if section_counter % sections_per_publish == 0:
                        debug_log("Intermediate publish after {0} sections to stabilize backend...".format(section_counter), True)
                        publish_reply = handle_publish(client, api_type)
                        if not publish_reply.success:
                            debug_log("Warning: Intermediate publish failed, continuing anyway...", True, True)
                        time.sleep(5)  # Extra rest after publish
                        
                elif len(data_to_import) > 100:
                    time.sleep(0.2)  # 200ms delay for large batches to prevent server overload
                counter, position_decrement_due_to_rules = add_object(line, counter, position_decrement_due_to_rules,
                                                                      position_decrement_due_to_sections, fields, api_type,
                                                                      generic_type, layer, layers_to_attach,
                                                                  changed_layer_names, api_call, num_objects, client, args, package)

    for rulebase_object_file in rulebase_object_files:
        layer_type = rulebase_object_file.name.split("__")[1]
        layer_name = '__'.join(rulebase_object_file.name.split('__')[2:-1])
        if layer_name in changed_layer_names:
            layer_name = changed_layer_names[layer_name]
        debug_log("Importing " + layer_type.split('_')[0].capitalize() + "_" + layer_type.split('_')[1].capitalize() +
                  " [" + layer_name + "]", True)
        import_objects(rulebase_object_file.name, client, changed_layer_names, package, layer_name, args)
        os.remove(rulebase_object_file.name)

    # Print final summary with total runtime only once (top-level call)
    if is_root_call:
        print_import_summary()
        
        # CRITICAL: Final publish to commit all changes!
        # Without this, everything will be discarded on session timeout/error
        debug_log("=" * 80, True)
        debug_log("Performing final publish to commit all changes...", True)
        debug_log("=" * 80, True)
        try:
            final_publish = handle_publish(client, "final")
            if not final_publish.success:
                error_msg = "CRITICAL ERROR: Final publish failed! All changes will be lost!"
                debug_log("=" * 80, True, True)
                debug_log(error_msg, True, True)
                debug_log("=" * 80, True, True)
            else:
                debug_log("=" * 80, True)
                debug_log("✓✓✓ Final publish successful - all changes committed! ✓✓✓", True)
                debug_log("=" * 80, True)
        except Exception as e:
            debug_log(f"Exception during final publish: {e}", True, True)
    
    # ALWAYS return layers_to_attach to prevent NoneType error in import_package.py
    return layers_to_attach


def add_tag_to_object_payload(tag_name, payload, api_type, client):
    # types don't support tagging
    for type_not_support_tagging in types_not_support_tagging:
        if type_not_support_tagging in api_type:  # can be sub-string of api_type (e.g. rule)
            return

    global add_tag_to_object_uid
    if add_tag_to_object_uid is None:
        tag_data = find_tag_by_name(tag_name, client)
        if tag_data is not None:
            add_tag_to_object_uid = tag_data['uid']
        else:
            # Tag not exists
            add_tag = client.api_call("add-tag", {"name": tag_name})
            if add_tag.success:
                publish = client.api_call("publish", {})
                if publish.success:
                    add_tag_to_object_uid = add_tag.data['uid']
            else:
                debug_log("Failed to add tag [{}] to objects. [{}]".format(tag_name,
                                                                           add_tag.error_message), True, True)
    # Add tag to payload
    if add_tag_to_object_uid is not None:
        payload_tags = payload["tags"] if "tags" in payload else []
        payload_tags.append(add_tag_to_object_uid)
        payload["tags"] = payload_tags


def find_tag_by_name(tag_name, client):
    query_tags = client.api_call("show-objects", payload={"type": "tag", "filter": tag_name})
    if query_tags.success:
        if len(query_tags.data['objects']) > 0:
            for tag_obj in query_tags.data['objects']:
                if tag_obj['name'] == tag_name:
                    return tag_obj
    return None


def handle_import_tags(payload, api_type, client):
    exported_tags = payload["tags"]
    tags_to_import = []
    unresolved_tags = []
    for tag in exported_tags:
        tag_name = None
        if isinstance(tag, dict):
            if "name" in tag:
                tag_name = str(tag["name"])

        if tag_name is None or tag_name == "":
            debug_log("Unknown tag name for object [{0}]".format(payload["name"] if "name" in payload else api_type),
                      True, True)
        else:
            add_tag_to_payload = False
            tag_data = find_tag_by_name(tag_name, client)
            if tag_data is not None:
                tag_name = tag_data['uid']
                add_tag_to_payload = True
            else:
                # Tag not exists
                reply = client.api_call("add-tag", tag)
                if reply.success:
                    add_tag_to_payload = True

            if add_tag_to_payload:
                tags_to_import.append(tag_name)
            else:
                unresolved_tags.append(tag_name)

    if len(unresolved_tags) > 0:
        debug_log("Failed to add tags {0} for object [{1}]".format(unresolved_tags, payload["name"]), True, True)

    if len(tags_to_import) > 0:
        payload["tags"] = tags_to_import


def add_object(line, counter, position_decrement_due_to_rule, position_decrement_due_to_section, fields, api_type,
               generic_type, layer, layers_to_attach,
               changed_layer_names, api_call, num_objects, client, args, package):
    # Optional small delay to prevent overwhelming the server during very large imports
    try:
        if num_objects and num_objects > 100:
            import time
            time.sleep(0.05)
    except Exception:
        pass
    global duplicates_dict
    global position_decrements_for_sections
    global missing_parameter_set
    global should_create_imported_nat_top_section
    global should_create_imported_nat_bottom_section
    global imported_nat_top_section_uid
    global section_uid_map

    if "access-rule" in api_type or "https-rule" in api_type:
        position_decrements_for_sections.append(position_decrement_due_to_rule)

    payload, _ = create_payload(fields, line, 0, api_type, client.api_version)
    
    # CRITICAL FIX: Skip creation for infrastructure objects that cannot be created via API
    # checkpoint-host and cluster-member are pre-existing infrastructure objects in CheckPoint
    # They can be queried (show works) but cannot be created (add fails with HV000028)
    # These objects already exist in the destination system with the same UIDs
    if api_type in ("checkpoint-host", "cluster-member"):
        debug_log(f"Skipping creation of infrastructure object '{payload.get('name', 'UNKNOWN')}' (type: {api_type}) - already exists in system", True)
        return counter + 1, position_decrement_due_to_rule
    
    if args is not None and args.objects_suffix != "":
        add_suffix_to_objects(payload, api_type, args.objects_suffix)

    # for objects that had collisions, use new name in the imported package
    for field in ["members", "source", "destination"]:
        if field in payload:
            for i, member in enumerate(payload[field]):
                if api_type == 'simple-cluster':
                    if member['name'] in name_collision_map:
                        payload[field][i]['name'] = name_collision_map[member['name']]
                else:
                    if member in name_collision_map:
                        payload[field][i] = name_collision_map[member]

    payload["ignore-warnings"] = True  # Useful for example when creating two hosts with the same IP

    if "threat-profile" in api_type:
        if "scan-malicious-links" in payload:
            payload.pop("scan-malicious-links")
            debug_log("Not importing scan-malicious-links, value is not supported. Setting with default value", True, True)

    if "exception-group" in api_type:
        name_to_check = payload["name"] if payload["name"] not in name_collision_map else name_collision_map[payload["name"]]
        if name_to_check not in imported_exception_groups:
            i = 0
            original_name = payload["name"]
            api_reply = client.api_call("show-exception-group", {"name": payload["name"]})
            was_renamed = False
            while api_reply.success and args is not None and not args.skip_duplicate_objects:
                was_renamed = True
                payload["name"] = "NAME_COLLISION_RESOLVED" + ("_" if i == 0 else "_%s_" % i) + original_name
                api_reply = client.api_call("show-exception-group", {"name": payload["name"]})
                i += 1

                if i > 100:
                    payload["name"] = original_name
                    was_renamed = False
                    break

            if api_reply.success and args is not None and args.skip_duplicate_objects:
                debug_log("skip duplicate object [{0}]".format(payload["name"]), True, True)
            elif not api_reply.success and was_renamed is True:
                debug_log("Object \"%s\" was renamed to \"%s\" to resolve the name collision"
                          % (original_name, payload["name"]), True, True)
                name_collision_map[original_name] = payload["name"]

    if "nat-rule" in api_type:
        # For NAT rules, the 'package' parameter is the name of the policy package!!!
        if package is None:
            debug_log("Internal error: package name is unknown", True, True)
        payload["package"] = package
        # --- NAT rules specific logic ---
        # Importing only rules, without sections.
        # Rules marked as "__before_auto_rules = TRUE" will be imported at the TOP of the rulebase, inside a new section "IMPORTED UPPER RULES".
        # There is an additional new section "Original Upper Rules" at the bottom of "IMPORTED UPPER RULES".
        # Rules marked as "__before_auto_rules = FALSE" will be imported at the BOTTOM of the rulebase, inside a new section "IMPORTED LOWER RULES".
        # There will be no rule merges!!!
        before_auto_rules = payload["__before_auto_rules"]
        payload.pop("__before_auto_rules", None)
        if "true" in before_auto_rules:
            if should_create_imported_nat_top_section:
                should_create_imported_nat_top_section = False
                nat_section_payload = {}
                nat_section_payload["package"] = package
                nat_section_payload["position"] = "top"
                # --> we add the footer section first!!!
                nat_section_payload["name"] = "Original Upper Rules"
                client.api_call("add-nat-section", nat_section_payload)
                # <--
                nat_section_payload["name"] = "IMPORTED UPPER RULES"
                nat_section_reply = client.api_call("add-nat-section", nat_section_payload)
                if nat_section_reply.success:
                    imported_nat_top_section_uid = nat_section_reply.data["uid"]
            if imported_nat_top_section_uid is None:
                payload["position"] = "bottom"
            else:
                sub_payload = {}
                sub_payload["bottom"] = imported_nat_top_section_uid
                payload["position"] = sub_payload
        else:
            if should_create_imported_nat_bottom_section:
                should_create_imported_nat_bottom_section = False
                nat_section_payload = {}
                nat_section_payload["package"] = package
                nat_section_payload["position"] = "bottom"
                nat_section_payload["name"] = "IMPORTED LOWER RULES"
                client.api_call("add-nat-section", nat_section_payload)
            payload["position"] = "bottom"
    else:
        if "position" in payload:
            # Sanitize position coming from export (avoid stray whitespace)
            try:
                if isinstance(payload.get("position"), str):
                    payload["position"] = payload["position"].strip()
            except Exception:
                pass
            
            if "rule" in api_type:
                if payload["action"] == "Drop":
                    if "action-settings" in payload:
                        payload.pop("action-settings")
                    if "user-check" in payload:
                        if "frequency" in payload["user-check"]:
                            payload["user-check"].pop("frequency")
                        if "custom-frequency" in payload["user-check"]:
                            payload["user-check"].pop("custom-frequency")
                        if "confirm" in payload["user-check"]:
                            payload["user-check"].pop("confirm")
            if "section" in api_type:
                # Sections: ALWAYS use "bottom" to avoid 300s timeout
                # Skip all position calculations - they cause server to scan entire rulebase
                if "position" in payload:
                    payload["position"] = "bottom"

        if generic_type:
            payload["create"] = generic_type
        if "layer" in api_type:
            check_duplicate_layer(payload, changed_layer_names, api_type, client)
            if compare_versions(client.api_version, "1.1") != -1 and "https" not in api_type:
                payload["add-default-rule"] = "false"
            if layer is None:
                if "access-layer" in api_type:
                    #---> This code segment distinguishes between an inline layer and an ordered layer during import
                    is_ordered_access_control_layer = payload["__ordered_access_control_layer"]
                    payload.pop("__ordered_access_control_layer", None)
                    if "true" in is_ordered_access_control_layer:
                        layers_to_attach["access"].append(payload["name"])   # ordered access layer
                    #<--- end of code segment
                elif "threat-layer" in api_type:
                    layers_to_attach["threat"].append(payload["name"])
                elif "https-layer" in api_type:
                    layers_to_attach["https"].append(payload["name"])
        elif "rule" in api_type or "section" in api_type or \
                (api_type == "threat-exception" and "exception-group-name" not in payload):
            payload["layer"] = layer
            if args is not None and args.objects_suffix != "" and payload["layer"]:
                payload["layer"] += args.objects_suffix
                if payload["layer"] in changed_layer_names:
                    payload["layer"] = changed_layer_names[payload["layer"]]
            
            # CRITICAL: Rules with numeric position cause 300s timeout (server scans entire rulebase)
            # Solution: Place rule at bottom of its correct section using section UID
            # This must be AFTER layer is set in payload
            if "position" in payload and ("rule" in api_type or api_type == "threat-exception"):
                original_position = payload.get("position")
                layer_name = payload.get("layer")
                
                # Only process numeric positions - skip if already dict/top/bottom
                # Position can be int (from JSON) or str (from CSV)
                if layer_name and original_position and isinstance(original_position, (str, int)):
                    try:
                        # Verify it's a numeric position (convert to int if string)
                        pos_as_int = int(original_position)
                        
                        # Try to find which section this rule belongs to
                        section_name = find_section_for_rule_position(original_position, layer_name)
                        
                        if section_name:
                            # Get section UID
                            try:
                                section_uid = section_uid_map.get(layer_name, {}).get(section_name, {}).get('uid')
                                if section_uid:
                                    # Place rule at bottom of its section - FAST (no rulebase scan)
                                    payload["position"] = {"bottom": section_uid}
                                    debug_log(f"Rule pos {original_position} → bottom of section '{section_name}'", True)
                                else:
                                    # Section UID not found yet (maybe section creation failed?) - use bottom
                                    payload["position"] = "bottom"
                                    debug_log(f"Warn: Section '{section_name}' UID not found, using bottom", True, True)
                            except Exception as e:
                                debug_log(f"Error finding section UID: {e}, using bottom", True, True)
                                payload["position"] = "bottom"
                        else:
                            # No section mapping found - use bottom (safe fallback)
                            payload["position"] = "bottom"
                            debug_log(f"Rule pos {original_position} → bottom (no section found)", True)
                    except (ValueError, TypeError):
                        # Position is not numeric (e.g., "top", "bottom", or dict) - leave as is
                        debug_log(f"Rule position '{original_position}' is not numeric, keeping as-is", True)
            
            if client.api_version != "1" and api_type == "access-rule" and "track-alert" in payload:
                payload["track"] = {}
                payload["track"]["alert"] = payload["track-alert"]
                payload.pop("track-alert", None)
        elif api_type == "exception-group" and "applied-threat-rules" in payload:
            for applied_rule in payload["applied-threat-rules"]:
                if applied_rule["layer"] in changed_layer_names.keys():
                    applied_rule["layer"] = changed_layer_names[applied_rule["layer"]]
        elif api_type == "threat-exception" and "exception-group-name" in payload:
            if payload["exception-group-name"] in name_collision_map:
                payload["exception-group-name"] = name_collision_map[payload["exception-group-name"]]

    if "updatable-object" in api_type:
        global updatable_objects_repository_initliazed
        if not updatable_objects_repository_initliazed:
            updatable_objects_repository_reply = client.api_call("update-updatable-objects-repository-content", wait_for_task=True)
            if updatable_objects_repository_reply.success:
                updatable_objects_repository_initliazed = True
            else:
                if hasattr(updatable_objects_repository_reply, "error_message"):
                    debug_log(
                        "Failed to update updatable objects repository \"%s\"" % updatable_objects_repository_reply.error_message,
                        True, True)
                else:
                    debug_log(
                        "Failed to update updatable objects repository \"%s\"" % updatable_objects_repository_reply,
                        True, True)

        updatable_object_payload = {}
        if "uid-in-updatable-objects-repository" in payload:
            updatable_object_payload["uid-in-updatable-objects-repository"] = payload[
                "uid-in-updatable-objects-repository"]
        elif "uid-in-data-center" in payload:
            updatable_object_payload["uid-in-updatable-objects-repository"] = payload["uid-in-data-center"]
        if "tags" in payload:
            updatable_object_payload["tags"] = payload["tags"]
        if "comments" in payload:
            updatable_object_payload["comments"] = payload["comments"]
        if "color" in payload:
            updatable_object_payload["color"] = payload["color"]
        payload = updatable_object_payload
    elif "https-rule" in api_type:
        if "blade" in payload and len(payload["blade"]) > 0:
            if len(payload["blade"]) == 1 and payload["blade"][0] == "All":
                del payload["blade"]
            else:
                exported_blades = payload["blade"]
                blades_to_import = []
                for blade in exported_blades:
                    if blade in https_blades_names_map:
                        blades_to_import.append(https_blades_names_map[blade])
                    else:
                        blades_to_import.append(blade)
                payload["blade"] = blades_to_import

    if "tags" in payload:
        handle_import_tags(payload, api_type, client)

    if args is not None and args.tag_objects_on_import != "":
        add_tag_to_object_payload(args.tag_objects_on_import, payload, api_type, client)

    if api_type == "exception-group":
        api_reply = client.api_call("show-exception-group", {"name": payload["name"]})
        if api_reply.success:
            api_call = "set-exception-group"
            if payload["name"] in name_collision_map:
                payload["name"] = name_collision_map[payload["name"]]
            if "applied-threat-rules" in payload:
                add_rules = payload["applied-threat-rules"].copy()
                applied_threat_rules = {"add": add_rules}
                payload["applied-threat-rules"] = applied_threat_rules

    # Retry mechanism for API errors (including JSON parsing errors from overloaded server)
    import time
    import datetime
    max_retries = 3
    api_reply = None
    
    # Track section creation time for debugging large rulebases
    section_start_time = None
    if api_call in ("add-access-section", "add-https-section") and "name" in payload:
        section_start_time = time.time()
        timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        debug_log("[{0}] Starting {1} '{2}' in layer '{3}' (position {4})...".format(
            timestamp, api_call, payload.get("name"), payload.get("layer"), payload.get("position", "N/A")), True)
    
    for retry_attempt in range(max_retries):
        try:
            # Sections: ALWAYS use "bottom" to avoid 300s timeout
            # Order is preserved because sections are created in sequence (1,2,3...)
            if api_call in ("add-access-section", "add-https-section"):
                payload_minimal = {
                    "name": payload.get("name"), 
                    "layer": payload.get("layer"),
                    "position": "bottom"  # ALWAYS bottom - fast, no rulebase scan
                }
                
                debug_log("Creating section '{0}' at bottom (fast)".format(payload.get("name")), True)
                api_reply = client.api_call(api_call, payload_minimal)
            else:
                api_reply = client.api_call(api_call, payload)
            break  # Success - exit retry loop
        except Exception as e:
            error_str = str(e)
            # Retry on JSON errors or connection issues
            if retry_attempt < max_retries - 1 and ("not a valid JSON" in error_str or "closed" in error_str):
                debug_log("API call failed (attempt {0}/{1}): {2}. Retrying...".format(
                    retry_attempt + 1, max_retries, error_str), True)
                time.sleep(1)  # Wait 1 second before retry
                continue
            else:
                # Final failure or non-retryable error
                debug_log("API call exception: {0}".format(error_str), True, True)
                api_reply = type('obj', (object,), {
                    'success': False,
                    'data': {},
                    'error_message': 'API exception: {0}'.format(error_str)
                })()
                break
    
    # Log section completion time
    if section_start_time is not None:
        elapsed = time.time() - section_start_time
        timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        if getattr(api_reply, "success", False):
            debug_log("[{0}] ✓ Section '{1}' created successfully in {2:.1f} seconds".format(
                timestamp, payload.get("name"), elapsed), True)
            
            # Save section UID for rule placement
            if api_call in ("add-access-section", "add-https-section"):
                try:
                    section_uid = api_reply.data.get("uid")
                    section_name = payload.get("name")
                    layer_name = payload.get("layer")
                    
                    if section_uid and section_name and layer_name:
                        if layer_name in section_uid_map and section_name in section_uid_map[layer_name]:
                            section_uid_map[layer_name][section_name]['uid'] = section_uid
                            debug_log(f"  Saved UID for section '{section_name}' in layer '{layer_name}'", True)
                except Exception as e:
                    debug_log(f"Warning: Could not save section UID: {e}", True, True)
        else:
            debug_log("[{0}] ✗ Section '{1}' failed after {2:.1f} seconds".format(
                timestamp, payload.get("name"), elapsed), True, True)
    
    reply_err_msg = _shorten_backend_error(get_reply_err_msg(api_reply))
    if not isinstance(reply_err_msg, str):  # Safety check
        reply_err_msg = str(reply_err_msg)

    # If the API response could not be parsed (e.g. invalid JSON / connection abort),
    # the server may still have completed the operation. Verify existence and continue.
    if (not getattr(api_reply, "success", False)) and ("name" in payload):
        try:
            suspicious_reply = any(s in reply_err_msg for s in (
                "not a valid JSON",
                "Failed to parse String position to Integer",
                "Software caused connection abort",
                "closed"
            ))
            if suspicious_reply:
                chk = None
                if api_call == "add-access-section":
                    chk = client.api_call("show-access-section", {"name": payload.get("name"), "layer": payload.get("layer")})
                elif api_call == "add-access-rule":
                    chk = client.api_call("show-access-rule", {"name": payload.get("name"), "layer": payload.get("layer")})

                if chk is not None and getattr(chk, "success", False):
                    debug_log(
                        "API response parsing failed for {0} [{1}]. Existence verified. Continuing import.".format(
                            api_type, payload.get("name")
                        ),
                        True,
                        True
                    )
                    api_reply = chk
                    api_reply.success = True
                    reply_err_msg = ""  # clear for downstream error handling
        except Exception:
            pass

    if not api_reply.success and "name" in payload and "More than one object" in reply_err_msg:
        if args is not None and not args.skip_duplicate_objects:
            i = 0
            original_name = payload["name"]
            while not api_reply.success and payload["name"] in reply_err_msg:
                payload["name"] = "NAME_COLLISION_RESOLVED" + ("_" if i == 0 else "_%s_" % i) + original_name
                # Handle exceptions from API calls (e.g., invalid JSON responses)
                try:
                    # Revert to direct API call for add-access-section (no task wrapper)
                    api_reply = client.api_call(api_call, payload)
                except Exception as e:
                    debug_log("API call exception for {0}: {1}".format(
                        payload.get("name", api_type), str(e)), True, True)
                    # Create a failed reply object to let error handling below continue
                    api_reply = type('obj', (object,), {'success': False, 'data': {}, 'error_message': str(e)})()
                reply_err_msg = _shorten_backend_error(get_reply_err_msg(api_reply))
                i += 1

                if i > 100:
                    payload["name"] = original_name
                    break

            # it's possible that at least one of the members' name might've caused collision
            if api_type == "simple-cluster" and not api_reply.success and 'members' in payload:
                # since the members param is a list and the name-uniqueness-validation goes through the members by order
                # we can do so as well and catch multiple collisions
                for index, member in enumerate(payload['members']):
                    iter_num = 0
                    member_orig_name = member['name']
                    while not api_reply.success and "More than one object" in reply_err_msg and payload['members'][index]['name'] in reply_err_msg:
                        payload['members'][index]['name'] = "NAME_COLLISION_RESOLVED" + ("_" if iter_num == 0 else "_%s_" % iter_num) + member_orig_name
                        # Revert to direct API call for add-access-section as well
                        api_reply = client.api_call(api_call, payload)
                        reply_err_msg = _shorten_backend_error(get_reply_err_msg(api_reply))
                        iter_num += 1

                        if iter_num > 100:
                            payload['members'][index]['name'] = member_orig_name
                            break

                    if api_reply.success or ("More than one object" in reply_err_msg and
                                             payload['members'][index]['name'] not in reply_err_msg):
                        # there might be another collision with a different member than the one that was fixed
                        debug_log("Cluster Member \"%s\" of Simple-Cluster \"%s\" was renamed to \"%s\" to resolve the name collision"
                                  % (member_orig_name, payload["name"], payload['members'][index]['name']), True, True)
                        name_collision_map[member_orig_name] = payload['members'][index]['name']
                        if api_reply.success:
                            break

            if api_reply.success and original_name != payload["name"]:
                debug_log("Object \"%s\" was renamed to \"%s\" to resolve the name collision"
                          % (original_name, payload["name"]), True, True)
                name_collision_map[original_name] = payload["name"]
        else:
            api_reply.success = True
            debug_log("skip duplicate object [{0}]".format(payload["name"]), True, True)

    if not api_reply.success:
        if api_reply.data and "errors" in api_reply.data:
            error_msg = api_reply.data["errors"][0]["message"]
        elif api_reply.data and "warnings" in api_reply.data:
            error_msg = api_reply.data["warnings"][0]["message"]
        else:
            error_msg = _shorten_backend_error(get_reply_err_msg(api_reply))
        log_err_msg = ""
        try:
            log_err_msg = "Failed to import {0}{1}. Error: {2}".format(api_type, " with name [" + str(payload[
                "name"]).strip() + "]" if "name" in payload else "", error_msg)
        except UnicodeEncodeError:
            log_err_msg = "Failed to import {0} object. Error: {1}".format(api_type, error_msg)

        reply_err_msg = _shorten_backend_error(get_reply_err_msg(api_reply))

        if "More than one object" in reply_err_msg:
            log_err_msg = reply_err_msg + ". Cannot import this object"

        if "Object is already imported. please use the existing object" in reply_err_msg:
            return counter, position_decrement_due_to_rule

        if "rule" in api_type and (
                        "Requested object" in reply_err_msg and "not found" in reply_err_msg):
            field_value = reply_err_msg.split("[")[1].split("]")[0]
            indices_of_field = [i for i, x in enumerate(line) if x == field_value]
            field_keys = [x for x in fields if fields.index(x) in indices_of_field]
            for field_key in field_keys:
                if field_key.split(".")[0] in generic_objects_for_rule_fields:
                    missing_obj_data = generic_objects_for_rule_fields[field_key.split(".")[0]]
                    missing_type = missing_obj_data[0]
                    mandatory_field = missing_obj_data[1] if len(missing_obj_data) > 1 else None
                    add_missing_command = "add-" + missing_type
                    new_name = "import_error_due_to_missing_fields_" + field_value.replace(" ", "_")
                    add_succeeded = True
                    if new_name not in missing_parameter_set:
                        missing_parameter_set.add(new_name)
                        add_missing_payload = {"name": new_name}
                        if mandatory_field == "port":
                            add_missing_payload["port"] = "8080"
                        elif mandatory_field == "ip-address":
                            add_missing_payload["ip-address"] = generate_new_dummy_ip_address()
                        add_missing_reply = client.api_call(add_missing_command, add_missing_payload)
                        if not add_missing_reply.success:
                            log_err_msg += "\nAlso failed to generate placeholder object: {0}".format(
                                get_reply_err_msg(add_missing_reply))
                            add_succeeded = False
                    if add_succeeded:
                        line[fields.index(field_key)] = new_name
                        return add_object(line, counter, position_decrement_due_to_rule,
                                          position_decrement_due_to_section, fields, api_type, generic_type, layer,
                                          layers_to_attach,
                                          changed_layer_names, api_call, num_objects, client, args, package)
        if "Invalid parameter for [position]" in reply_err_msg and "exception-group" not in api_type:
            if "access-rule" in api_type or "https-rule" or "threat-exception" in api_type:
                position_decrement_due_to_rule += adjust_position_decrement(int(payload["position"]), reply_err_msg)
            elif "access-section" in api_type or "https-section" in api_type:
                position_decrement_due_to_section += adjust_position_decrement(int(payload["position"]), reply_err_msg)
            return add_object(line, counter, position_decrement_due_to_rule, position_decrement_due_to_section, fields,
                              api_type, generic_type, layer,
                              layers_to_attach,
                              changed_layer_names, api_call, num_objects, client, args, package)
        elif "is not unique" in reply_err_msg and "name" in reply_err_msg:
            field_value = reply_err_msg.partition("name")[2].split("[")[1].split("]")[0]
            debug_log("Not unique name problem \"%s\" - changing payload to use UID instead." % field_value, True, True)
            obj_uid_found_and_used = False
            if field_value not in duplicates_dict:
                if field_value in not_unique_name_with_dedicated_api:
                    debug_log("Found not unique name: \"%s\", using dedicated API: \"%s\""% (field_value, not_unique_name_with_dedicated_api[field_value]), True, True)
                    show_objects_reply = client.api_call(not_unique_name_with_dedicated_api[field_value], {"name": field_value})
                    if show_objects_reply.success:
                        duplicates_dict[field_value] = show_objects_reply.data["uid"]
                        obj_uid_found_and_used = True
                if not obj_uid_found_and_used:
                    show_objects_reply = client.api_query("show-objects",
                                                     payload={"in": ["name", "\"" + field_value + "\""]})
                    if show_objects_reply.success:
                        for obj in show_objects_reply.data:
                            if obj["name"] == field_value:
                                duplicates_dict[field_value] = obj["uid"]
                                obj_uid_found_and_used = True
            else:
                obj_uid_found_and_used = True
            if obj_uid_found_and_used:
                indices_of_field = [i for i, x in enumerate(line) if x == field_value]
                field_keys = [x for x in fields if fields.index(x) in indices_of_field]
                for field_key in field_keys:
                    line[fields.index(field_key)] = duplicates_dict[field_value]
                return add_object(line, counter, position_decrement_due_to_rule, position_decrement_due_to_section, fields,
                                  api_type, generic_type, layer, layers_to_attach,
                                  changed_layer_names, api_call, num_objects, client, args, package)
            else:
                debug_log("Not unique name problem \"%s\" - cannot change payload to use UID instead of name." % field_value, True, True)
        elif "will place the exception in an Exception-Group" in reply_err_msg:
            return add_object(line, counter, position_decrement_due_to_rule - 1, position_decrement_due_to_section,
                              fields, api_type, generic_type, layer, layers_to_attach,
                              changed_layer_names, api_call, num_objects, client, args, package)

        position_decrement_due_to_rule += 1

        # Don't log individual rule failures - too noisy. High-level summary will be shown instead.
        # debug_log(log_err_msg, True, False)
        if args is not None and args.strict:
            discard_reply = client.api_call("discard")
            if not discard_reply.success:
                debug_log("Failed to discard changes! Terminating import/export process. Backend reply: " + _shorten_backend_error(get_reply_err_msg(discard_reply)), True, True)
                raise SystemExit(1)
    else:
        imported_name = payload["name"] if "name" in payload else ""
        if api_call == "add-exception-group":
            imported_exception_groups.append(imported_name)
        
        # Show detailed progress for sections
        if api_type in ("access-section", "https-section"):
            timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            debug_log("[{0}] Imported {1}/{2} sections: {3}".format(
                timestamp, counter, num_objects, imported_name), True)
        else:
            debug_log("Imported {0}{1}".format(api_type, " with name [" + imported_name + "]"))
        
        if counter % 20 == 0 or counter == num_objects:
            percentage = int(float(counter) / float(num_objects) * 100)
            debug_log("Imported {0} out of {1} {2} ({3}%)".format(counter, num_objects,
                                                                  singular_to_plural_dictionary[client.api_version][
                                                                      api_type] if api_type in
                                                                                   singular_to_plural_dictionary[
                                                                                       client.api_version] else "generic objects",
                                                                  percentage), True)
            if counter % 50 == 0 or counter == num_objects:
                # Protect against publish timeout with large rulebase
                try:
                    publish_reply = client.api_call("publish", wait_for_task=True, timeout=7200)
                    if publish_reply.success:
                        import time
                        time.sleep(5)  # Give server 5 seconds to recover after successful publish
                except Exception as e:
                    debug_log("Publish timeout/error: {0}. Skipping publish, will retry later...".format(str(e)), True, True)
                    # Skip publish for now, continue with import
                    return counter + 1, position_decrement_due_to_rule
                if not publish_reply.success:
                    publish_reply_err_msg = get_reply_err_msg(publish_reply)
                    plural = singular_to_plural_dictionary[client.api_version][api_type].replace('_', ' ') \
                        if api_type in singular_to_plural_dictionary[client.api_version] \
                        else "generic objects of type " + api_type
                    try:
                        debug_log("Failed to publish import of " + plural + " from tar file #" +
                                  str((counter / 100) + 1) + "! " + plural.capitalize() +
                                  " from said file were not imported!. Error: " + publish_reply_err_msg,
                                  True, True)
                    except UnicodeEncodeError:
                        try:
                            debug_log("UnicodeEncodeError: " + publish_reply_err_msg, True, True)
                        except:
                            debug_log("UnicodeEncodeError: .encode('utf-8') FAILED", True, True)

                    discard_reply = client.api_call("discard")
                    if not discard_reply.success:
                        debug_log("Failed to discard changes of unsuccessful publish! Terminating. Error: " +
                                  get_reply_err_msg(discard_reply), True, True)
                        exit(1)

    return counter + 1, position_decrement_due_to_rule


# This is a duplicate code from function add_object
def create_batch_payload(api_type, data, fields, client, args, is_rule_type, changed_layer_names,
                         generic_type, layer, layers_to_attach, package):
    batch_payload = {'objects': [{
        'type': api_type,
        'list': []
    }]}

    if is_rule_type:
        if api_type == "nat-rule":
            batch_payload['objects'][0]['layer'] = package
            batch_payload['objects'][0]['first-position'] = "bottom"
        else:
            batch_payload['objects'][0]['layer'] = layer
            batch_payload['objects'][0]['first-position'] = "top"

    list_of_objects = batch_payload['objects'][0]['list']
    import time
    for line in data:
        # Small delay to prevent overwhelming the API server with thousands of rapid calls
        if len(data) > 100:
            time.sleep(0.05)  # 50ms delay for large batches to prevent server overload
        payload, _ = create_payload(fields, line, 0, api_type, client.api_version)
        update_payload_batch(client, payload, api_type, args, is_rule_type, changed_layer_names, package,
                             generic_type, layer, layers_to_attach)
        list_of_objects.append(payload)
    return batch_payload


def update_payload_batch(client, payload, api_type, args, is_rule_type, changed_layer_names, package, generic_type,
                         layer, layers_to_attach):
    if args is not None and args.objects_suffix != "":
        add_suffix_to_objects(payload, api_type, args.objects_suffix)

    # for objects that had collisions, use new name in the imported package
    for field in ["members", "source", "destination"]:
        if field in payload:
            for i, member in enumerate(payload[field]):
                if member in name_collision_map:
                    payload[field][i] = name_collision_map[member]

    if "tags" in payload:
        handle_import_tags(payload, api_type, client)

    if args is not None and args.tag_objects_on_import != "":
        add_tag_to_object_payload(args.tag_objects_on_import, payload, api_type, client)

    if is_rule_type:
        global should_create_imported_nat_top_section
        global should_create_imported_nat_bottom_section
        global imported_nat_top_section_uid

        if "nat-rule" in api_type:
            # For NAT rules, the 'package' parameter is the name of the policy package!!!
            if package is None:
                debug_log("Internal error: package name is unknown", True, True)
            payload["package"] = package
            # --- NAT rules specific logic ---
            # Importing only rules, without sections.
            # Rules marked as "__before_auto_rules = TRUE" will be imported at the TOP of the rulebase, inside a new section "IMPORTED UPPER RULES".
            # There is an additional new section "Original Upper Rules" at the bottom of "IMPORTED UPPER RULES".
            # Rules marked as "__before_auto_rules = FALSE" will be imported at the BOTTOM of the rulebase, inside a new section "IMPORTED LOWER RULES".
            # There will be no rule merges!!!
            before_auto_rules = payload["__before_auto_rules"]
            payload.pop("__before_auto_rules", None)
            if "true" in before_auto_rules:
                if should_create_imported_nat_top_section:
                    should_create_imported_nat_top_section = False
                    nat_section_payload = {}
                    nat_section_payload["package"] = package
                    nat_section_payload["position"] = "top"
                    # --> we add the footer section first!!!
                    nat_section_payload["name"] = "Original Upper Rules"
                    client.api_call("add-nat-section", nat_section_payload)
                    # <--
                    nat_section_payload["name"] = "IMPORTED UPPER RULES"
                    nat_section_reply = client.api_call("add-nat-section", nat_section_payload)
                    if nat_section_reply.success:
                        imported_nat_top_section_uid = nat_section_reply.data["uid"]
                if imported_nat_top_section_uid is None:
                    payload["position"] = "bottom"
                else:
                    sub_payload = {}
                    sub_payload["bottom"] = imported_nat_top_section_uid
                    payload["position"] = sub_payload
            else:
                if should_create_imported_nat_bottom_section:
                    should_create_imported_nat_bottom_section = False
                    nat_section_payload = {}
                    nat_section_payload["package"] = package
                    nat_section_payload["position"] = "bottom"
                    nat_section_payload["name"] = "IMPORTED LOWER RULES"
                    client.api_call("add-nat-section", nat_section_payload)
                payload["position"] = "bottom"
        else:
            if "position" in payload:
                if "rule" in api_type:
                    if payload["action"] == "Drop":
                        if "action-settings" in payload:
                            payload.pop("action-settings")
                        if "user-check" in payload:
                            if "frequency" in payload["user-check"]:
                                payload["user-check"].pop("frequency")
                            if "custom-frequency" in payload["user-check"]:
                                payload["user-check"].pop("custom-frequency")
                            if "confirm" in payload["user-check"]:
                                payload["user-check"].pop("confirm")

            if generic_type:
                payload["create"] = generic_type
            if "layer" in api_type:
                check_duplicate_layer(payload, changed_layer_names, api_type, client)
                if compare_versions(client.api_version, "1.1") != -1 and "https" not in api_type:
                    payload["add-default-rule"] = "false"
                if layer is None:
                    if "access-layer" in api_type:
                        # ---> This code segment distinguishes between an inline layer and an ordered layer during import
                        is_ordered_access_control_layer = payload["__ordered_access_control_layer"]
                        payload.pop("__ordered_access_control_layer", None)
                        if "true" in is_ordered_access_control_layer:
                            layers_to_attach["access"].append(payload["name"])  # ordered access layer
                        # <--- end of code segment
                    elif "threat-layer" in api_type:
                        layers_to_attach["threat"].append(payload["name"])
                    elif "https-layer" in api_type:
                        layers_to_attach["https"].append(payload["name"])
            elif "rule" in api_type or "section" in api_type or \
                    (api_type == "threat-exception" and "exception-group-name" not in payload):
                payload["layer"] = layer
                if args is not None and args.objects_suffix != "":
                    payload["layer"] += args.objects_suffix
                if client.api_version != "1" and api_type == "access-rule" and "track-alert" in payload:
                    payload["track"] = {}
                    payload["track"]["alert"] = payload["track-alert"]
                    payload.pop("track-alert", None)
            elif api_type == "exception-group" and "applied-threat-rules" in payload:
                for applied_rule in payload["applied-threat-rules"]:
                    if applied_rule["layer"] in changed_layer_names.keys():
                        applied_rule["layer"] = changed_layer_names[applied_rule["layer"]]
        if "https-rule" in api_type:
            if "blade" in payload and len(payload["blade"]) > 0:
                if len(payload["blade"]) == 1 and payload["blade"][0] == "All":
                    del payload["blade"]
                else:
                    exported_blades = payload["blade"]
                    blades_to_import = []
                    for blade in exported_blades:
                        if blade in https_blades_names_map:
                            blades_to_import.append(https_blades_names_map[blade])
                        else:
                            blades_to_import.append(blade)
                    payload["blade"] = blades_to_import


def add_batch_objects(api_type, command, client, args, payload):
    # Split very large batches into smaller chunks to reduce publish time and server load.
    # Chunk size is overridable via env var IMPORT_CHUNK_SIZE, but some object types must be conservative.
    batch_size = len(payload['objects'][0]['list'])

    # Per-type defaults:
    # Batch sizing strategy:
    # - access-section/https-section: medium chunks (25-30) using async task mode bypasses HTTP timeout
    #   Task-based approach allows longer backend processing without HTTP connection limits
    # - access-rule: can be chunked (default env or 200)
    if api_type in ("access-section", "https-section"):
        # Medium chunks with task-based async mode avoids timeout on rulebases with hundreds of sections
        chunk_size = int(os.environ.get("IMPORT_SECTIONS_CHUNK_SIZE", "25"))
    else:
        chunk_size = int(os.environ.get("IMPORT_CHUNK_SIZE", "200"))

    if batch_size > chunk_size:
        debug_log("Large batch detected ({0} objects). Splitting... smaller batches of {1}...".format(batch_size, chunk_size), True)
        return add_batch_objects_chunked(api_type, command, client, args, payload, chunk_size=chunk_size)


    api_reply = add_batch_operation(api_type, command, client, args, payload)
    succeeded = False
    if api_reply.success:
        debug_log("Managed to import API object from type " + api_type +
                  " by " + command + " API call.\nNow trying to publish.", True)
        api_reply = handle_publish(client, api_type)
        if api_reply.success:
            succeeded = True
    else:
        err_msg = ""
        if 'tasks' in api_reply.data and isinstance(api_reply.data['tasks'], list):
            if len(api_reply.data['tasks']) > 0 and 'progress-description' in api_reply.data['tasks'][0]:
                err_msg = api_reply.data['tasks'][0]['progress-description']
        else:
            try:
                err_msg = api_reply.error_message
            except AttributeError:
                pass
        debug_log("Failed to import API object from type " + api_type + " by " + command + " API call.\n"
                  + err_msg +
                  "\nNow trying to discard.", True, True)
        handle_discard(client)

    if not succeeded:
        debug_log("Failed to import API object from type " + api_type +
                  " by " + command + " API call.\nFalling back to add objects one by one.", True, True)
    return succeeded


def add_batch_objects_chunked(api_type, command, client, args, payload, chunk_size=200):
    """Import large batches in smaller chunks to avoid server overload
       Prints exact index and object name on failure.
    """
    all_objects = payload['objects'][0]['list']
    total = len(all_objects)

    resume_from = load_resume_index(api_type)
    if resume_from > 0:
        debug_log("↪ Resume enabled for {0}: starting from absolute index {1}".format(api_type, resume_from), True)

    for start_idx in range(0, total, chunk_size):
        if start_idx < resume_from:
            continue
        end_idx = min(start_idx + chunk_size, total)
        chunk = all_objects[start_idx:end_idx]

        # Create chunk payload
        chunk_payload = {
            'objects': [{
                'type': payload['objects'][0]['type'],
                'list': chunk
            }]
        }

        # Copy layer info for rules
        if 'layer' in payload['objects'][0]:
            chunk_payload['objects'][0]['layer'] = payload['objects'][0]['layer']
        if 'first-position' in payload['objects'][0]:
            chunk_payload['objects'][0]['first-position'] = payload['objects'][0]['first-position']

        debug_log(
            "Importing batch chunk {0}-{1} of {2} {3}...".format(
                start_idx + 1, end_idx, total, api_type
            ),
            True
        )

        # Reduce response payload for very large environments; avoids heavy DB queries / huge replies
        if api_type in ("access-section", "access-layer"):
            chunk_payload.setdefault("details-level", "uid")
            chunk_payload.setdefault("show-as-ranges", False)

        api_reply = add_batch_operation(api_type, command, client, args, chunk_payload)
        if not api_reply.success:
            debug_log("❌ Batch chunk {0}-{1} failed, stopping batch mode here".format(
                start_idx + 1, end_idx), True, True)
            global FAILED_BATCH_RANGE, FAILED_BATCH_API_TYPE
            FAILED_BATCH_RANGE = (start_idx, end_idx)
            FAILED_BATCH_API_TYPE = api_type

            # Stop batch processing and return False
            # One-by-one fallback will handle from this chunk onwards
            # Previous chunks already published successfully
            return False

        debug_log(
            "Publishing batch chunk {0}-{1}...".format(start_idx + 1, end_idx),
            True
        )

        publish_reply = handle_publish(client, api_type)
        if not publish_reply.success:
            return False

        # Mark progress: next chunk start index
        save_resume_index(api_type, end_idx)

        # Short rest between chunks
        import time
        # Sections need longer rest to let backend DB settle (esp. with 200+ sections)
        if api_type in ("access-section", "https-section"):
            rest_seconds = float(os.environ.get("IMPORT_SECTION_REST_SEC", "3"))
        else:
            rest_seconds = float(os.environ.get("IMPORT_CHUNK_REST_SEC", "1"))
        if rest_seconds > 0:
            time.sleep(rest_seconds)

    debug_log(
        "Successfully imported all {0} {1} in chunked batches".format(total, api_type),
        True
    )
    return True

def add_batch_operation(api_type, command, client, args, payload):
    """Run a batch operation robustly.

    Some batch commands return a task-id and require waiting. Using mgmt_api's
    wait_for_task=True can crash under load with:
      'Failed to handle asynchronous tasks as synchronous, tasks result is undefined'

    So we:
      1) call asynchronously (wait_for_task=False)
      2) poll show-task until completion or timeout
    """
    import time
    # Sections on large rulebases (200+ sections) need much longer timeouts
    if api_type in ("access-section", "https-section"):
        total_timeout = int(os.environ.get("IMPORT_SECTION_BATCH_TIMEOUT_SEC", "3600"))  # 1 hour
        poll_interval = float(os.environ.get("IMPORT_SECTION_POLL_SEC", "10"))
    else:
        total_timeout = int(os.environ.get("IMPORT_BATCH_TIMEOUT_SEC", "7200"))
        poll_interval = float(os.environ.get("IMPORT_BATCH_POLL_SEC", "5"))
    http_timeout = int(os.environ.get("IMPORT_HTTP_TIMEOUT_SEC", str(total_timeout + 60)))

    # Call asynchronously to avoid mgmt_api wait_for_task issues under load
    try:
        reply = client.api_call(command, payload, wait_for_task=False, timeout=http_timeout)
    except TypeError:
        reply = client.api_call(command, payload, wait_for_task=False)

    # If command failed immediately, return as-is
    if not getattr(reply, "success", False):
        return reply

    task_id = None
    try:
        task_id = reply.data.get("task-id") or reply.data.get("task_id")
    except Exception:
        task_id = None

    # Some versions may return immediate success without task-id
    if not task_id:
        return reply

    deadline = time.time() + total_timeout
    last_show = None

    while time.time() < deadline:
        try:
            last_show = client.api_call("show-task", payload={"task-id": task_id}, timeout=http_timeout)
        except TypeError:
            last_show = client.api_call("show-task", payload={"task-id": task_id})
        tasks = []
        try:
            tasks = last_show.data.get("tasks", [])
        except Exception:
            tasks = []
        task = tasks[0] if tasks else None

        if isinstance(task, dict):
            status = (task.get("status") or task.get("task-status") or "").lower()

            if status in ("succeeded", "completed", "done"):
                last_show.success = True
                return last_show

            # Some deployments use partially-succeeded
            if status in ("partially-succeeded", "partial"):
                last_show.success = True
                return last_show

            if status in ("failed", "stopped"):
                last_show.success = False
                return last_show

        time.sleep(poll_interval)

    # Timeout
    reply.success = False
    reply.error_message = f"{command} timeout after {total_timeout}s (task-id={task_id})"
    reply.data = getattr(reply, "data", {}) or {}
    reply.data["task-id"] = task_id
    return reply



def api_call_as_task(client, command, payload, total_timeout=None, poll_interval=None):
    """Run a single API call as an async task and poll show-task.

    This avoids long-lived HTTP requests (common for add-access-section in huge rulebases)
    that may be cut mid-response and appear as 'not a valid JSON' on the client side.
    """
    import time
    if total_timeout is None:
        total_timeout = int(os.environ.get("IMPORT_SINGLE_TASK_TIMEOUT_SEC", "10800"))
    if poll_interval is None:
        poll_interval = float(os.environ.get("IMPORT_SINGLE_TASK_POLL_SEC", "10"))
    http_timeout = int(os.environ.get("IMPORT_HTTP_TIMEOUT_SEC", str(total_timeout + 60)))

    payload = dict(payload or {})
    # NOTE: do not send run-as-task for add-access-section (unsupported - causes generic_err_invalid_parameter_name)
    if command not in ("add-access-section", "add-https-section"):
        payload["run-as-task"] = True

    try:
        reply = client.api_call(command, payload, wait_for_task=False, timeout=http_timeout)
    except TypeError:
        reply = client.api_call(command, payload, wait_for_task=False)
    if not getattr(reply, "success", False):
        return reply

    task_id = None
    try:
        task_id = reply.data.get("task-id") or reply.data.get("task_id")
    except Exception:
        task_id = None

    # Some versions may return immediate success without task-id
    if not task_id:
        return reply

    deadline = time.time() + total_timeout
    last_show = None
    poll_count = 0
    task_start = time.time()
    
    while time.time() < deadline:
        try:
            last_show = client.api_call("show-task", payload={"task-id": task_id}, timeout=http_timeout)
        except TypeError:
            last_show = client.api_call("show-task", payload={"task-id": task_id})
        tasks = []
        try:
            tasks = last_show.data.get("tasks", [])
        except Exception:
            tasks = []
        task = tasks[0] if tasks else None

        if isinstance(task, dict):
            status = (task.get("status") or task.get("task-status") or "").lower()
            progress_desc = task.get("progress-description") or task.get("progress-description") or ""
            
            # Log progress every 60 seconds for long-running tasks
            poll_count += 1
            if poll_count % max(1, int(60 / poll_interval)) == 0:
                elapsed = time.time() - task_start
                debug_log(f"  Task {task_id[:8]}... running for {elapsed:.0f}s, status: {status}, progress: {progress_desc}", True)
            
            if status in ("succeeded", "completed", "done", "partially-succeeded", "partial"):
                elapsed = time.time() - task_start
                debug_log(f"  Task completed in {elapsed:.1f}s", True)
                last_show.success = True
                return last_show
            if status in ("failed", "stopped"):
                last_show.success = False
                return last_show

        time.sleep(poll_interval)

    reply.success = False
    reply.error_message = f"{command} timeout after {total_timeout}s (task-id={task_id})"
    reply.data = getattr(reply, "data", {}) or {}
    reply.data["task-id"] = task_id
    return reply


def handle_publish(client, api_type):
    """Robust publish wrapper.

    We avoid client.api_call('publish', wait_for_task=True) because under load the
    underlying wait-for-task helper may raise:
        'Failed to handle asynchronous tasks as synchronous, tasks result is undefined'

    Instead:
    1) call publish asynchronously (wait_for_task=False)
    2) poll 'show-task' until completion or timeout
    """
    import time

    total_timeout = int(os.environ.get("IMPORT_PUBLISH_TIMEOUT_SEC", "7200"))  # 2 hours default
    poll_interval = float(os.environ.get("IMPORT_PUBLISH_POLL_SEC", "5"))
    max_publish_retries = int(os.environ.get("IMPORT_PUBLISH_RETRIES", "3"))

    def _task_status(task):
        if not isinstance(task, dict):
            return ""
        return (task.get("status") or task.get("task-status") or "").lower()

    def _task_done(task):
        return _task_status(task) in ("succeeded", "failed", "partially-succeeded", "stopped", "completed", "done")

    def _task_succeeded(task):
        return _task_status(task) in ("succeeded", "partially-succeeded", "completed", "done")

    last_exc = None

    for attempt in range(1, max_publish_retries + 1):
        try:
            publish_start = time.time()
            publish_reply = client.api_call("publish", wait_for_task=False)

            if not getattr(publish_reply, "success", False):
                try:
                    msg = str(publish_reply.error_message)
                except Exception:
                    msg = ""
                debug_log(f"Publish call failed (attempt {attempt}/{max_publish_retries}). {msg}", True, True)
                handle_discard(client)
                return publish_reply

            # Most versions return a task-id; if not, assume success
            task_id = None
            try:
                task_id = publish_reply.data.get("task-id") or publish_reply.data.get("task_id")
            except Exception:
                task_id = None

            if not task_id:
                debug_log("Managed to publish import of API objects from type " + api_type, True)
                return publish_reply

            deadline = publish_start + total_timeout
            while time.time() < deadline:
                try:
                    show = client.api_call("show-task", payload={"task-id": task_id})
                    tasks = []
                    try:
                        tasks = show.data.get("tasks", [])
                    except Exception:
                        tasks = []
                    task = tasks[0] if tasks else None

                    if task and _task_done(task):
                        if _task_succeeded(task):
                            debug_log("Managed to publish import of API objects from type " + api_type, True)
                            show.success = True
                            return show

                        desc = ""
                        if isinstance(task, dict):
                            desc = task.get("progress-description") or task.get("description") or ""
                        debug_log("Failed to publish import of API objects from type " + api_type +
                                  (": " + str(desc) if desc else ""), True, True)
                        handle_discard(client)
                        show.success = False
                        return show

                except Exception as poll_exc:
                    # transient errors while polling: keep trying until timeout
                    last_exc = poll_exc

                time.sleep(poll_interval)

            # timeout: publish might still be running in the background, so DO NOT discard automatically here.
            debug_log(f"Publish task timed out after {total_timeout}s (task-id={task_id}).", True, True)
            publish_reply.success = False
            publish_reply.error_message = f"publish timeout after {total_timeout}s (task-id={task_id})"
            return publish_reply

        except Exception as e:
            last_exc = e
            debug_log(f"Publish exception (attempt {attempt}/{max_publish_retries}): {e}", True, True)
            time.sleep(10)

    dummy = type("obj", (object,), {})()
    dummy.success = False
    dummy.data = {}
    dummy.error_message = f"publish failed after {max_publish_retries} attempts: {last_exc}"
    return dummy


def handle_discard(client):
    discard_reply = client.api_call("discard")
    if not discard_reply.success:
        debug_log("Failed to discard changes of unsuccessful publish! Terminating. Error: " +
                  discard_reply.error_message,
                  True, True)
        exit(1)


def adjust_position_decrement(position, error_message):
    indices_of_brackets = [i for i, letter in enumerate(error_message) if letter == '[' or letter == ']']
    valid_range = error_message[indices_of_brackets[4]:indices_of_brackets[5] + 1]
    _, _, final_position_with_bracket = valid_range.partition("-")
    final_position = final_position_with_bracket[:-1]
    return position - int(final_position)


def check_duplicate_layer(payload, changed_layer_names, api_type, client):
    layer_name = payload["name"]
    new_layer_name = payload["name"]

    i = 0
    while True:
        show_layer = client.api_call("show-" + api_type, payload={"name": new_layer_name})

        if "code" in show_layer.data and "not_found" in show_layer.data["code"]:
            if layer_name != new_layer_name:
                debug_log("A layer named \"%s\" already exists. Name was changed to \"%s\""
                          % (layer_name, new_layer_name))
                changed_layer_names[layer_name] = new_layer_name
                payload["name"] = new_layer_name
            break

        new_layer_name = "IMPORTED LAYER" + (" " if i == 0 else " %s " % i) + layer_name
        i += 1


def compare_general_object_files(file_a, file_b):
    api_type_a = "-".join(file_a.name.split("_")[4].split("-")[1:])
    api_type_b = "-".join(file_b.name.split("_")[4].split("-")[1:])
    priority_a = import_priority[api_type_a] if api_type_a in import_priority else 0
    priority_b = import_priority[api_type_b] if api_type_b in import_priority else 0
    if priority_b > priority_a:
        return -1
    elif priority_a > priority_b:
        return 1
    return 0


def print_import_summary():
    """Print import completion summary with total runtime."""
    elapsed_seconds = time.time() - SCRIPT_START_TIME
    hours = int(elapsed_seconds // 3600)
    minutes = int((elapsed_seconds % 3600) // 60)
    seconds = int(elapsed_seconds % 60)

    timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    summary = f"""
╔═══════════════════════════════════════════════════════════════════╗
║                    IMPORT COMPLETED SUCCESSFULLY                  ║
║═══════════════════════════════════════════════════════════════════║
║ Timestamp: {timestamp:<51} ║
║ Total Runtime: {hours}h {minutes}m {seconds}s{' ' * (50 - len(f'{hours}h {minutes}m {seconds}s'))}║
║═══════════════════════════════════════════════════════════════════║
║ The policy has been successfully imported into Check Point!        ║
║ Please verify the import in SmartConsole.                         ║
╚═══════════════════════════════════════════════════════════════════╝
"""

    print(summary)
    debug_log(summary, True)

    # Simple final line for logs / piping
    print("Import finished successfully. Duration: {0:.2f} seconds.".format(elapsed_seconds))

def add_suffix_to_objects(payload, api_type, objects_suffix):
    global changed_object_names_map
    ignore_types = ["updatable-object"]

    if api_type in ignore_types:
        return

    fields_to_change = ["name", "source", "destination", "service", "members", "inline-layer", "networks", "host",
                        "protected-scope", "protection-or-site", "action", "site-category", "exception-group-name", "rule-name", "applied-threat-rules"]
    if api_type == "threat-exception" and "exception-group-name" in payload and "name" not in payload:
        payload.update({"name": ""})
    for field in fields_to_change:
        if field in payload:
            if field == "name":
                oldName = payload[field]
                newName = oldName + objects_suffix
                payload[field] = newName
                changed_object_names_map[oldName] = newName
            elif field in ["source", "destination", "service", "members", "protected-scope", "protection-or-site", "site-category"]:
                for i in range(len(payload[field])):
                    if payload[field][i] in changed_object_names_map and payload[field][i] != "IPS":
                        payload[field][i] = changed_object_names_map[payload[field][i]]
            elif field in ["inline-layer", "host", "exception-group-name", "rule-name", "action"]:
                if payload[field] in changed_object_names_map:
                    payload[field] = changed_object_names_map[payload[field]]
            elif field == "networks":
                for i in range(len(payload[field])):
                    if payload[field][i]["name"] in changed_object_names_map:
                        payload[field][i]["name"] = changed_object_names_map[payload[field][i]["name"]]
            elif field == "applied-threat-rules":
                for i in range(len(payload[field])):
                    if payload[field][i]["layer"] in changed_object_names_map:
                        payload[field][i]["layer"] = changed_object_names_map[payload[field][i]["layer"]]
