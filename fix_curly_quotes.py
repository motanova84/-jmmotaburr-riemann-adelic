#!/usr/bin/env python3
import glob
import json

def fix_unicode_in_notebook(file_path):
    with open(file_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    replacements = {
        ''': "'",   # Left single quotation mark
        ''': "'",   # Right single quotation mark  
        '"': '"',   # Left double quotation mark
        '"': '"',   # Right double quotation mark
    }
    
    changed = False
    def replace_in_obj(obj):
        nonlocal changed
        if isinstance(obj, dict):
            for key, value in obj.items():
                obj[key] = replace_in_obj(value)
        elif isinstance(obj, list):
            for i, item in enumerate(obj):
                obj[i] = replace_in_obj(item)
        elif isinstance(obj, str):
            original = obj
            for old, new in replacements.items():
                obj = obj.replace(old, new)
            if obj != original:
                changed = True
        return obj
    
    replace_in_obj(data)
    
    if changed:
        with open(file_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=1, ensure_ascii=False)
        print(f'✅ Fixed curly quotes in {file_path}')
        return True
    else:
        print(f'ℹ️  No curly quotes found in {file_path}')
        return False

# Process all notebooks
notebooks = glob.glob('notebooks/*.ipynb') + glob.glob('*.ipynb')
for notebook in notebooks:
    fix_unicode_in_notebook(notebook)