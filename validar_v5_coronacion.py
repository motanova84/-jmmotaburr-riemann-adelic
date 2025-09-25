#!/usr/bin/env python3
"""
Universal wrapper for V5 Coronación validation script.

This wrapper provides universal access to the V5 Coronación validation functionality
and can be called with:
  python3 validar_v5_coronacion.py [options]
  ./validar_v5_coronacion.py [options]

It forwards all arguments to the main validate_v5_coronacion.py script.
"""

import sys
import subprocess
import os

def main():
    """Main wrapper function that forwards to validate_v5_coronacion.py"""
    # Get the directory where this script is located
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    # Path to the main validation script
    main_script = os.path.join(script_dir, 'validate_v5_coronacion.py')
    
    # Check if main script exists
    if not os.path.exists(main_script):
        print(f"❌ Error: Main validation script not found at {main_script}")
        print("Please ensure validate_v5_coronacion.py exists in the same directory.")
        return 1
    
    # Forward all command line arguments to the main script
    try:
        # Use python3 explicitly to ensure compatibility
        cmd = [sys.executable, main_script] + sys.argv[1:]
        result = subprocess.run(cmd, check=False)
        return result.returncode
    except Exception as e:
        print(f"❌ Error executing validation script: {e}")
        return 1

if __name__ == '__main__':
    sys.exit(main())