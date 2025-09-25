#!/usr/bin/env python3
"""
Wrapper script for validar_v5_coronacion.py

This is a convenience alias that forwards to the actual validation script.
Users can run 'python validar_v5_coronacion.py' as expected.
"""

import subprocess
import sys
import os

# Path to the actual validation script
target = os.path.join(os.path.dirname(__file__), "validate_v5_coronacion.py")

# Forward all arguments to the target script and exit with the same code
sys.exit(subprocess.call([sys.executable, target] + sys.argv[1:]))