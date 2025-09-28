#!/usr/bin/env python3
import glob

def fix_curly_quotes(file_path):
    """Fix curly quotes in a file."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original_content = content
    
    # Replace curly quotes with straight quotes
    content = content.replace(''', "'")  # left single quote
    content = content.replace(''', "'")  # right single quote  
    content = content.replace('"', '"')  # left double quote
    content = content.replace('"', '"')  # right double quote
    
    if content != original_content:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
        print(f"✅ Fixed curly quotes in {file_path}")
        return True
    else:
        print(f"ℹ️  No curly quotes found in {file_path}")
        return False

# Process all notebooks
notebooks = glob.glob('notebooks/*.ipynb') + glob.glob('*.ipynb')
fixed_count = 0

for notebook in notebooks:
    if fix_curly_quotes(notebook):
        fixed_count += 1

print(f"\n🎉 Fixed curly quotes in {fixed_count} files")