#!/usr/bin/env python3
"""
Verificador de metadatos para artefactos formales.

Este script valida que los archivos de metadatos JSON-LD contengan
todos los campos requeridos para la ingestión y verificación de
artefactos formales.

Campos obligatorios:
- @id: Identificador único del artefacto
- dc:title: Título descriptivo
- dc:creator: Autor o sistema de origen
- format: Formato del archivo (e.g., text/x-lean4)
- origin: Sistema o proyecto de origen
- kernel: Sistema de verificación formal (e.g., lean4, coq, isabelle)
- checksum: Hash SHA-256 del contenido para verificar integridad

Uso:
    python tools/verify_metadata.py schema/metadata_example.jsonld
"""

import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple


def load_metadata(filepath: Path) -> Dict[str, Any]:
    """Carga un archivo JSON-LD de metadatos."""
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            return json.load(f)
    except json.JSONDecodeError as e:
        print(f"ERROR: Archivo JSON inválido: {e}")
        sys.exit(1)
    except FileNotFoundError:
        print(f"ERROR: Archivo no encontrado: {filepath}")
        sys.exit(1)


def validate_required_fields(metadata: Dict[str, Any]) -> Tuple[bool, List[str]]:
    """
    Valida que los campos obligatorios estén presentes.

    Returns:
        Tuple[bool, List[str]]: (es_válido, lista_de_errores)
    """
    required_fields = {
        "@id": "Identificador único del artefacto",
        "dc:title": "Título descriptivo",
        "dc:creator": "Autor o sistema de origen",
        "format": "Formato del archivo",
        "origin": "Sistema o proyecto de origen",
        "kernel": "Sistema de verificación formal",
        "checksum": "Hash SHA-256 del contenido",
    }

    errors = []
    for field, description in required_fields.items():
        if field not in metadata or not metadata[field]:
            errors.append(f"Campo obligatorio faltante o vacío: '{field}' ({description})")

    return len(errors) == 0, errors


def validate_checksum_format(checksum: str) -> Tuple[bool, str]:
    """Valida el formato del checksum."""
    if not checksum.startswith("sha256:"):
        return False, "El checksum debe comenzar con 'sha256:'"

    hash_value = checksum.replace("sha256:", "")
    if len(hash_value) != 64:
        return False, "El hash SHA-256 debe tener 64 caracteres hexadecimales"

    if not all(c in "0123456789abcdef" for c in hash_value.lower()):
        return False, "El hash debe contener solo caracteres hexadecimales"

    return True, ""


def validate_metadata(metadata: Dict[str, Any]) -> Tuple[bool, List[str]]:
    """
    Realiza todas las validaciones de metadatos.

    Returns:
        Tuple[bool, List[str]]: (es_válido, lista_de_errores_y_advertencias)
    """
    all_messages = []

    # Validar campos obligatorios
    is_valid, errors = validate_required_fields(metadata)
    all_messages.extend(errors)

    # Validar formato de checksum si está presente
    if "checksum" in metadata:
        checksum_valid, checksum_error = validate_checksum_format(metadata["checksum"])
        if not checksum_valid:
            all_messages.append(f"Formato de checksum inválido: {checksum_error}")
            is_valid = False

    # Advertencias (no bloquean la validación)
    if "@context" not in metadata:
        all_messages.append("ADVERTENCIA: Falta el campo '@context' (recomendado para JSON-LD)")

    if "@type" not in metadata:
        all_messages.append("ADVERTENCIA: Falta el campo '@type' (recomendado para JSON-LD)")

    return is_valid, all_messages


def main():
    """Función principal."""
    if len(sys.argv) < 2:
        print("Uso: python tools/verify_metadata.py <archivo_metadata.jsonld>")
        print("Ejemplo: python tools/verify_metadata.py schema/metadata_example.jsonld")
        sys.exit(1)

    filepath = Path(sys.argv[1])
    print(f"Validando metadatos: {filepath}")
    print("-" * 60)

    # Cargar metadatos
    metadata = load_metadata(filepath)

    # Validar metadatos
    is_valid, messages = validate_metadata(metadata)

    # Mostrar resultados
    if messages:
        for message in messages:
            print(message)
        print("-" * 60)

    if is_valid:
        print("✓ METADATA OK: Todos los campos obligatorios están presentes")
        print(f"  - ID: {metadata.get('@id', 'N/A')}")
        print(f"  - Título: {metadata.get('dc:title', 'N/A')}")
        print(f"  - Kernel: {metadata.get('kernel', 'N/A')}")
        print(f"  - Formato: {metadata.get('format', 'N/A')}")
        sys.exit(0)
    else:
        print("✗ METADATA INVALID: Faltan campos obligatorios o hay errores")
        sys.exit(1)


if __name__ == "__main__":
    main()
