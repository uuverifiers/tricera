
import os
import json
import re

# Paths
grammar_file = "concurrentC.cf"
metadata_file = "../src/main/resources/META-INF/native-image/uuverifiers/tricera/reflect-config.json"

def extract_classes_from_grammar(grammar_path):
    classes = set()
    with open(grammar_path, 'r') as f:
        for line in f:
            line = line.strip()
            match = re.match(r'^(\w+)\s*\.', line)
            if match:
                cls_name = match.group(1)
                # Ignore internal or separator keywords if any (BNFC specific)
                if cls_name not in ["rules", "token", "comment", "separator", "coercions", "entrypoints", "internal", "_"]:
                    classes.add(cls_name)
    return sorted(list(classes))

def update_metadata(classes):
    os.makedirs(os.path.dirname(metadata_file), exist_ok=True)
    
    current_data = []
    if os.path.exists(metadata_file):
        with open(metadata_file, 'r') as f:
            try:
                current_data = json.load(f)
            except json.JSONDecodeError:
                pass
    
    # Ensure it's a list
    if not isinstance(current_data, list):
        current_data = []

    
    # Define grammars and their package prefixes
    grammars = [
        (grammar_file, "tricera.concurrency.concurrent_c.Absyn."),
        ("../acsl-parser/acsl.cf", "tricera.acsl.Absyn.")
    ]
    
    all_ast_entries = set()
    
    # Process all grammars
    for g_file, prefix in grammars:
        if os.path.exists(g_file):
            g_classes = extract_classes_from_grammar(g_file)
            for cls in g_classes:
                all_ast_entries.add(prefix + cls)
        else:
            print(f"Warning: Grammar file {g_file} not found.")

    # Remove stale AST entries
    cleaned_data = []
    removed_count = 0
    
    # Prefixes to manage
    managed_prefixes = [p for _, p in grammars]
    
    for entry in current_data:
        name = entry.get("name", "")
        # Check if this entry belongs to one of our managed packages
        is_managed = any(name.startswith(prefix) for prefix in managed_prefixes)
        
        if is_managed:
            if name in all_ast_entries:
                cleaned_data.append(entry)
            else:
                removed_count += 1
        else:
            cleaned_data.append(entry)
            
    current_data = cleaned_data
    existing_types = {entry["name"] for entry in current_data if "name" in entry}
    
    fields_config = [
        {"name": "col_num"},
        {"name": "line_num"},
        {"name": "offset"}
    ]

    added_count = 0
    
    for full_name in sorted(list(all_ast_entries)):
        if full_name not in existing_types:
            entry = {
                "name": full_name,
                "fields": fields_config
            }
            current_data.append(entry)
            added_count += 1
            
    with open(metadata_file, 'w') as f:
        json.dump(current_data, f, indent=2)
        
    print(f"Added {added_count} new AST classes.")
    print(f"Removed {removed_count} stale AST classes.")
    print(f"Total entries: {len(current_data)}")

if __name__ == "__main__":
    # We no longer need to pass classes explicitly as update_metadata scans both grammars
    update_metadata(None)
