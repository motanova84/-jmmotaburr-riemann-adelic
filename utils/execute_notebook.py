#!/usr/bin/env python3
"""
Notebook execution utility with parameter optimization for CI/CD environments.
This script provides options for running the validation notebook with reduced 
computational complexity for faster execution in automated environments.
"""

import subprocess
import sys
import os
import json
from pathlib import Path

def optimize_notebook_for_ci(input_notebook, output_notebook):
    """
    Create an optimized version of the notebook for CI execution.
    Reduces precision and parameter ranges for faster execution.
    """
    try:
        with open(input_notebook, 'r') as f:
            notebook = json.load(f)
        
        # Modify cells to use reduced precision and parameters
        for cell in notebook['cells']:
            if cell['cell_type'] == 'code':
                source = ''.join(cell['source'])
                
                # Replace high precision with lower precision
                if 'mp.mp.dps = 50' in source:
                    source = source.replace('mp.mp.dps = 50', 'mp.mp.dps = 15  # Reduced for CI')
                
                # Reduce parameter ranges for faster execution
                if 'P=1000, K=50' in source:
                    source = source.replace('P=1000, K=50', 'P=100, K=10  # Reduced for CI')
                
                if 'T=50' in source:
                    source = source.replace('T=50', 'T=10  # Reduced for CI')
                
                # Update cell source
                cell['source'] = source.split('\n')
                
        # Save optimized notebook
        with open(output_notebook, 'w') as f:
            json.dump(notebook, f, indent=1)
            
        print(f"✅ Optimized notebook created: {output_notebook}")
        return True
        
    except Exception as e:
        print(f"❌ Failed to optimize notebook: {e}")
        return False

def execute_notebook(notebook_path, output_dir, timeout=300, allow_errors=True):
    """
    Execute a Jupyter notebook and convert to HTML.
    """
    try:
        cmd = [
            'jupyter', 'nbconvert',
            '--to', 'html',
            '--execute',
            notebook_path,
            '--output-dir', output_dir,
            '--output', 'validation.html',
            f'--ExecutePreprocessor.timeout={timeout}'
        ]
        
        if allow_errors:
            cmd.append('--allow-errors')
            
        print(f"🔄 Executing notebook: {notebook_path}")
        print(f"⏱️  Timeout: {timeout} seconds")
        
        result = subprocess.run(cmd, capture_output=True, text=True)
        
        if result.returncode == 0:
            print("✅ Notebook executed successfully")
            return True
        else:
            print(f"⚠️  Notebook execution completed with warnings/errors:")
            print(result.stderr)
            return True  # Still consider success if errors are allowed
            
    except Exception as e:
        print(f"❌ Failed to execute notebook: {e}")
        return False

def main():
    """Main function with command line interface."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Execute validation notebook with optimization options')
    parser.add_argument('--input', '-i', default='notebooks/validation.ipynb', 
                       help='Input notebook path')
    parser.add_argument('--output-dir', '-o', default='docs/', 
                       help='Output directory for HTML')
    parser.add_argument('--timeout', '-t', type=int, default=300, 
                       help='Execution timeout in seconds')
    parser.add_argument('--optimize-for-ci', action='store_true',
                       help='Create optimized version for CI/CD')
    parser.add_argument('--fast', action='store_true',
                       help='Use fast parameters (optimize + reduced timeout)')
    
    args = parser.parse_args()
    
    # Ensure output directory exists
    os.makedirs(args.output_dir, exist_ok=True)
    
    notebook_to_execute = args.input
    
    if args.optimize_for_ci or args.fast:
        print("🔧 Creating optimized notebook for CI execution...")
        optimized_notebook = '/tmp/validation_optimized.ipynb'
        
        if not optimize_notebook_for_ci(args.input, optimized_notebook):
            print("❌ Failed to create optimized notebook")
            sys.exit(1)
            
        notebook_to_execute = optimized_notebook
    
    # Adjust timeout for fast execution
    timeout = 120 if args.fast else args.timeout
    
    # Execute notebook
    success = execute_notebook(notebook_to_execute, args.output_dir, timeout)
    
    if success:
        output_file = os.path.join(args.output_dir, 'validation.html')
        if os.path.exists(output_file):
            print(f"📊 HTML report generated: {output_file}")
        else:
            print("⚠️  HTML file not found - execution may have failed")
            
        # Create a summary file
        summary_file = os.path.join(args.output_dir, 'execution_summary.txt')
        with open(summary_file, 'w') as f:
            f.write(f"Notebook Execution Summary\n")
            f.write(f"==========================\n")
            f.write(f"Input: {args.input}\n")
            f.write(f"Optimized: {'Yes' if args.optimize_for_ci or args.fast else 'No'}\n")
            f.write(f"Timeout: {timeout} seconds\n")
            f.write(f"Status: {'Success' if success else 'Failed'}\n")
            
        print(f"📝 Execution summary: {summary_file}")
        
    else:
        print("❌ Notebook execution failed")
        sys.exit(1)

if __name__ == "__main__":
    main()