#!/usr/bin/env python3
"""
Validador V5 Coronación — Wrapper
---------------------------------
Conveniencia para ejecutar la validación completa del marco de la
Hipótesis de Riemann basado en sistemas adélicos S-finitos.

Permite a los usuarios invocar:
    python validar_v5_coronacion.py [args]
y esto reenvía la ejecución al script real:
    validate_v5_coronacion.py
"""

import os
import subprocess
import sys

# Ruta al script real
target = os.path.join(os.path.dirname(__file__), "validate_v5_coronacion.py")

# Reenviar todos los argumentos y salir con el mismo código
sys.exit(subprocess.call([sys.executable, target] + sys.argv[1:]))
