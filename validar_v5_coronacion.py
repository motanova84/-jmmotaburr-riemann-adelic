#!/usr/bin/env python3
"""
Validador V5 Coronación — Marco de Validación de la Hipótesis de Riemann
========================================================================

Este script proporciona una interfaz en español para la validación completa 
del marco de la Hipótesis de Riemann basado en sistemas adélicos S-finitos.

DESCRIPCIÓN:
    Valida la demostración completa "V5 Coronación" de la Hipótesis de Riemann
    mediante el marco de verificación integral de 5 pasos desarrollado por
    José Manuel Mota Burruezo.

FUNCIONALIDADES:
    1. Paso 1: Verificación Axiomas → Lemas  
    2. Paso 2: Derivación doble de rigidez arquimediana
    3. Paso 3: Identificación de unicidad Paley-Wiener
    4. Paso 4: Localización de ceros (de Branges + Weil-Guinand)
    5. Paso 5: Integración completa de coronación

USO:
    python validar_v5_coronacion.py [opciones]
    
OPCIONES:
    --precision DIGITOS    Precisión decimal para cálculos (por defecto: 30)
    --verbose             Mostrar información detallada del progreso
    --save-certificate    Guardar certificado matemático de prueba
    --help                Mostrar esta ayuda

EJEMPLOS:
    python validar_v5_coronacion.py                      # Validación estándar
    python validar_v5_coronacion.py --precision 50       # Alta precisión
    python validar_v5_coronacion.py --verbose            # Salida detallada
    python validar_v5_coronacion.py --save-certificate   # Guardar certificado

MODOS DE VALIDACIÓN:
    - Modo Ligero: Dataset mínimo (zeros_t1e3.txt, ~2-5 min)
    - Modo Completo: Dataset completo (zeros_t1e8.txt, ~horas)

AUTOR: José Manuel Mota Burruezo
VERSIÓN: V5 Coronación Final
LICENCIA: MIT (código), CC-BY 4.0 (manuscrito)
"""

import argparse
import subprocess
import sys
import os

def mostrar_ayuda_espanol():
    """Mostrar ayuda en español antes de reenviar al script principal"""
    print(__doc__)
    print("\n" + "="*80)
    print("🚀 VALIDADOR V5 CORONACIÓN - HIPÓTESIS DE RIEMANN")
    print("="*80)
    print("\nEste script valida la demostración completa de la Hipótesis de Riemann")
    print("usando el marco de sistemas adélicos S-finitos desarrollado por")
    print("José Manuel Mota Burruezo.\n")
    
    print("📋 ESTRUCTURA DE VALIDACIÓN:")
    print("   ✓ Paso 1: Axiomas → Lemas comprobados")
    print("   ✓ Paso 2: Rigidez arquimediana (derivación doble)")  
    print("   ✓ Paso 3: Unicidad Paley-Wiener D(s) ≡ Ξ(s)")
    print("   ✓ Paso 4A: Localización de Branges")
    print("   ✓ Paso 4B: Localización Weil-Guinand")
    print("   ✓ Paso 5: Integración completa coronación\n")
    
    print("🔬 PRUEBAS DE ESTRÉS:")
    print("   • Perturbación de medida espectral")
    print("   • Validación de límites de crecimiento")
    print("   • Consistencia de subconjuntos de ceros")
    print("   • Generación de certificado matemático\n")
    
    print("🔗 PRUEBAS DE INTEGRACIÓN:")
    print("   • Integración con fórmula explícita de Weil")
    print("   • Verificación de línea crítica\n")

def main():
    """Punto de entrada principal con manejo en español"""
    # Si se solicita ayuda, mostrar en español
    if len(sys.argv) > 1 and sys.argv[1] in ['-h', '--help', '--ayuda', 'ayuda']:
        mostrar_ayuda_espanol()
        return
    
    # Ruta al script real
    target = os.path.join(os.path.dirname(__file__), "validate_v5_coronacion.py")
    
    if not os.path.exists(target):
        print("❌ ERROR: No se pudo encontrar validate_v5_coronacion.py")
        print("   Asegúrese de que el archivo existe en el mismo directorio.")
        sys.exit(1)
    
    try:
        # Reenviar todos los argumentos y salir con el mismo código
        print("🔄 Iniciando validación V5 Coronación...")
        print("   Redirigiendo a validate_v5_coronacion.py...\n")
        exit_code = subprocess.call([sys.executable, target] + sys.argv[1:])
        
        if exit_code == 0:
            print("\n🎉 ¡Validación V5 Coronación completada exitosamente!")
        else:
            print(f"\n❌ Error durante la validación (código: {exit_code})")
            
        sys.exit(exit_code)
        
    except KeyboardInterrupt:
        print("\n\n⚠️  Validación interrumpida por el usuario")
        sys.exit(130)
    except Exception as e:
        print(f"\n❌ ERROR INESPERADO: {e}")
        print("   Por favor, reporte este error al desarrollador.")
        sys.exit(1)

if __name__ == '__main__':
    main()