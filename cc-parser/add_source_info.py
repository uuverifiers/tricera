import os
import re
import sys

def process_directory(directory, provider_package):
    """
    Iterates over Java files in the directory.
    If a file contains line_num, col_num, and offset fields,
    it makes the class implement SourceInfoProvider and adds accessors.
    """
    
    interface_name = "SourceInfoProvider"
    interface_content = f"""package {provider_package};

public interface {interface_name} {{
  public int getLineNum();
  public void setLineNum(int value);
  public int getColNum();
  public void setColNum(int value);
  public int getOffset();
  public void setOffset(int value);
}}
"""
    
    interface_path = os.path.join(directory, f"{interface_name}.java")
    
    src_files_modified = 0
    
    for root, dirs, files in os.walk(directory):
        for filename in files:
            if filename.endswith(".java"):
                filepath = os.path.join(root, filename)
                with open(filepath, 'r') as f:
                    content = f.read()
                
                # Check for fields
                if "public int line_num, col_num, offset;" in content:
                    # It's an AST node
                    # Find package declaration to know where we are
                    package_match = re.search(r'package\s+([\w\.]+);', content)
                    current_package = package_match.group(1) if package_match else ""
           
                    new_content = content
                    
                    if provider_package != current_package:
                        # Insert import after package decl
                        import_stm = f"\nimport {provider_package}.{interface_name};\n"
                        new_content = re.sub(r'(package\s+[\w\.]+;)', r'\g<1>' + import_stm, new_content, count=1)
                    
                    # Add implements
                    # Class declaration: public class X extends Y ... { or public class X ... {
                    # We want to append implements SourceInfoProvider.
                    # It might already extend something.
                    
                    class_decl_pattern = r'(public\s+class\s+\w+)(\s+extends\s+[\w\.]+)?(\s+implements\s+[\w\.,\s]+)?(\s*\{)'
                    
                    def replacement(match):
                        prefix = match.group(1)
                        extends_clause = match.group(2) or ""
                        implements_clause = match.group(3) or ""
                        suffix = match.group(4)
                        
                        if implements_clause:
                            if interface_name not in implements_clause:
                                implements_clause += f", {interface_name}"
                        else:
                            implements_clause = f" implements {interface_name}"
                        
                        return f"{prefix}{extends_clause}{implements_clause}{suffix}"

                    new_content = re.sub(class_decl_pattern, replacement, new_content, count=1)
                    
                    # Add getters and setters before the last closing brace                   
                    accessors = """
  public int getLineNum() { return line_num; }
  public void setLineNum(int value) { line_num = value; }
  public int getColNum() { return col_num; }
  public void setColNum(int value) { col_num = value; }
  public int getOffset() { return offset; }
  public void setOffset(int value) { offset = value; }
"""
                    last_brace_index = new_content.rfind('}')
                    if last_brace_index != -1:
                        new_content = new_content[:last_brace_index] + accessors + new_content[last_brace_index:]
                        
                        with open(filepath, 'w') as f:
                            f.write(new_content)
                        src_files_modified += 1

                elif "public abstract class" in content and "Visitor" in content:
                    # Abstract AST node (category)
                    # Find package declaration to know where we are
                    package_match = re.search(r'package\s+([\w\.]+);', content)
                    current_package = package_match.group(1) if package_match else ""
                    
                    new_content = content
                    
                    if provider_package != current_package:
                         # Insert import after package decl
                         import_stm = f"\nimport {provider_package}.{interface_name};\n"
                         new_content = re.sub(r'(package\s+[\w\.]+;)', r'\g<1>' + import_stm, new_content, count=1)

                    # Only process abstract classes if they are in the Absyn package
                    if not current_package.endswith(".Absyn"):
                        continue

                    if f"implements {interface_name}" not in new_content:
                        # "public abstract class Stm implements java.io.Serializable {"
                        pattern = r"(public abstract class \w+.*?)( \{)"
                        # Check if it already implements something
                        if "implements" in new_content:
                             replacement = f"\\1, {interface_name}\\2"
                        else:
                             replacement = f"\\1 implements {interface_name}\\2"
                        
                        new_content = re.sub(pattern, replacement, new_content, count=1)

                        # Add abstract getters and setters
                        abstract_accessors = """
  public abstract int getLineNum();
  public abstract void setLineNum(int value);
  public abstract int getColNum();
  public abstract void setColNum(int value);
  public abstract int getOffset();
  public abstract void setOffset(int value);
"""
                        # Insert before last brace
                        last_brace_index = new_content.rfind("}")
                        if last_brace_index != -1:
                            new_content = new_content[:last_brace_index] + abstract_accessors + new_content[last_brace_index:]

                        with open(filepath, 'w') as f:
                            f.write(new_content)
                        src_files_modified += 1


    print(f"Modified {src_files_modified} files in {directory}")

    # Create the interface file
    package_path = provider_package.replace('.', os.sep)
    full_interface_path = os.path.join(directory, package_path, f"{interface_name}.java")
    
    os.makedirs(os.path.dirname(full_interface_path), exist_ok=True)
    with open(full_interface_path, 'w') as f:
        f.write(interface_content)
    print(f"Created interface at {full_interface_path}")

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python3 add_source_info.py <source_root_dir> <provider_package>")
        sys.exit(1)
        
    source_root = sys.argv[1]
    package = sys.argv[2]
    
    process_directory(source_root, package)
