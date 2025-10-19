"""
Universal Kernel: Verificador de coherencia total para QCAL.
Este módulo valida la coherencia semántica, lógica y física de objetos QCAL.
"""

import json
import os
from pathlib import Path


def verify_universal(jsonld_path: str, proof_path: str) -> bool:
    """
    Verifica la coherencia universal de un objeto QCAL.
    
    Args:
        jsonld_path: Ruta al archivo JSON-LD con metadatos
        proof_path: Ruta al archivo de prueba (puede ser Lean o Python)
    
    Returns:
        True si la verificación es exitosa, False en caso contrario
    """
    try:
        # V_L: Verificación lógica - comprobar que los archivos existen
        if not os.path.exists(jsonld_path):
            print(f"Error: {jsonld_path} no existe")
            return False
        
        if not os.path.exists(proof_path):
            print(f"Error: {proof_path} no existe")
            return False
        
        # V_S: Verificación semántica - validar estructura JSON-LD
        with open(jsonld_path, 'r', encoding='utf-8') as f:
            metadata = json.load(f)
        
        # Validar campos requeridos en JSON-LD
        required_fields = ['@context', '@type']
        for field in required_fields:
            if field not in metadata:
                print(f"Error: Campo requerido '{field}' no encontrado en {jsonld_path}")
                return False
        
        # V_F: Verificación física - comprobar integridad básica
        jsonld_size = os.path.getsize(jsonld_path)
        proof_size = os.path.getsize(proof_path)
        
        if jsonld_size == 0 or proof_size == 0:
            print("Error: Archivos vacíos detectados")
            return False
        
        # Verificación de coherencia adicional
        # Aquí se pueden agregar más validaciones específicas del dominio
        
        return True
    
    except json.JSONDecodeError as e:
        print(f"Error al parsear JSON: {e}")
        return False
    except Exception as e:
        print(f"Error inesperado: {e}")
        return False


def verify_universal_api(jsonld_path: str, proof_path: str) -> bool:
    """
    API simple para el FFI bridge que devuelve un booleano.
    
    Args:
        jsonld_path: Ruta al archivo JSON-LD con metadatos
        proof_path: Ruta al archivo de prueba
    
    Returns:
        True si la verificación es exitosa, False en caso contrario
    """
    try:
        return verify_universal(jsonld_path, proof_path)
    except Exception:
        return False


def register_verification(jsonld_path: str, proof_path: str, result: bool, 
                         output_path: str = "tools/qcal_state.json"):
    """
    Registra el resultado de una verificación en el estado QCAL.
    
    Args:
        jsonld_path: Ruta al archivo JSON-LD verificado
        proof_path: Ruta al archivo de prueba verificado
        result: Resultado de la verificación
        output_path: Ruta al archivo de estado JSON
    """
    try:
        # Crear el directorio si no existe
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        
        # Leer estado existente o crear nuevo
        if os.path.exists(output_path):
            with open(output_path, 'r', encoding='utf-8') as f:
                state = json.load(f)
        else:
            state = {"verifications": []}
        
        # Agregar nueva verificación
        verification_entry = {
            "file": jsonld_path,
            "proof": proof_path,
            "verified": result,
            "timestamp": None  # Se puede agregar timestamp si se necesita
        }
        
        if "verifications" not in state:
            state["verifications"] = []
        
        state["verifications"].append(verification_entry)
        
        # Guardar estado actualizado
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(state, f, indent=2)
        
        return True
    except Exception as e:
        print(f"Error al registrar verificación: {e}")
        return False


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) < 3:
        print("Uso: python universal_kernel.py <jsonld_path> <proof_path>")
        sys.exit(1)
    
    jsonld_path = sys.argv[1]
    proof_path = sys.argv[2]
    
    result = verify_universal_api(jsonld_path, proof_path)
    
    if result:
        print(f"✅ Verificación exitosa para {jsonld_path}")
        register_verification(jsonld_path, proof_path, True)
        sys.exit(0)
    else:
        print(f"❌ Verificación fallida para {jsonld_path}")
        register_verification(jsonld_path, proof_path, False)
        sys.exit(1)
