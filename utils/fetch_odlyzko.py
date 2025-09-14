import requests, gzip, os, hashlib, warnings

def calculate_sha256(filepath):
    """Calculate SHA256 hash of a file."""
    sha256_hash = hashlib.sha256()
    with open(filepath, "rb") as f:
        for byte_block in iter(lambda: f.read(4096), b""):
            sha256_hash.update(byte_block)
    return sha256_hash.hexdigest()

def download_and_extract(url, out_txt, expected_sha256=None, max_retries=3):
    """
    🧠 Copilot Prompt:
    Añade verificación de integridad SHA256 tras la descarga del archivo zeros_t1e8.txt.gz.
    Si el hash no coincide, vuelve a descargar. Muestra advertencia visible en el workflow.
    """
    gz_path = out_txt + ".gz"
    
    for attempt in range(max_retries):
        print(f"🔽 Descargando (intento {attempt + 1}/{max_retries}): {url}")
        
        try:
            r = requests.get(url, stream=True, timeout=60)
            r.raise_for_status()
            
            with open(gz_path, 'wb') as f:
                for chunk in r.iter_content(chunk_size=8192):
                    f.write(chunk)
            
            print("✅ Descargado. Verificando integridad SHA256...")
            
            # Calculate SHA256 hash of downloaded file
            actual_sha256 = calculate_sha256(gz_path)
            print(f"🔍 SHA256 calculado: {actual_sha256}")
            
            # Verify hash if expected is provided
            if expected_sha256:
                if actual_sha256 == expected_sha256:
                    print("✅ Verificación SHA256 exitosa")
                else:
                    warning_msg = (f"⚠️  ADVERTENCIA: SHA256 no coincide para {url}\n"
                                 f"   Esperado: {expected_sha256}\n"
                                 f"   Obtenido: {actual_sha256}")
                    print(warning_msg)
                    warnings.warn(warning_msg, UserWarning)
                    
                    if attempt < max_retries - 1:
                        print("🔄 Reintentando descarga...")
                        os.remove(gz_path)
                        continue
                    else:
                        print("❌ Máximo de reintentos alcanzado")
                        # Continue with extraction despite hash mismatch
            
            # Extract file
            print("📂 Extrayendo...")
            with gzip.open(gz_path, 'rb') as gz_in:
                with open(out_txt, 'wb') as txt_out:
                    txt_out.write(gz_in.read())
            
            os.remove(gz_path)
            print(f"📂 Guardado en: {out_txt}")
            
            # Calculate hash of extracted file for reference
            extracted_sha256 = calculate_sha256(out_txt)
            print(f"🔍 SHA256 del archivo extraído: {extracted_sha256}")
            
            return actual_sha256
            
        except Exception as e:
            print(f"❌ Error en intento {attempt + 1}: {e}")
            if os.path.exists(gz_path):
                os.remove(gz_path)
            
            if attempt < max_retries - 1:
                print("🔄 Reintentando...")
            else:
                print("❌ Descarga fallida después de todos los intentos")
                raise

# Tablas de Odlyzko (ejemplos) with SHA256 hashes
odlyzko_sources = {
    "t1e8": {
        "url": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeros1",
        "expected_sha256": None  # To be updated with actual hash when available
    },
    "t1e10": {
        "url": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e10_1e4_1e6.txt.gz",
        "expected_sha256": None  # To be updated with actual hash when available
    },
    "t1e12": {
        "url": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e12_1e4_1e6.txt.gz", 
        "expected_sha256": None  # To be updated with actual hash when available
    }
}

def main():
    """Download and verify Odlyzko zero tables."""
    os.makedirs("zeros", exist_ok=True)
    
    print("🚀 Iniciando descarga de tablas de ceros de Odlyzko...")
    
    for label, source_info in odlyzko_sources.items():
        print(f"\n📦 Procesando tabla: {label}")
        out_file = f"zeros/zeros_{label}.txt"
        
        url = source_info["url"]
        expected_hash = source_info["expected_sha256"]
        
        try:
            actual_hash = download_and_extract(url, out_file, expected_hash)
            
            # Store the actual hash for future reference
            print(f"📝 Nota: El SHA256 real para {label} es: {actual_hash}")
            
        except Exception as e:
            print(f"❌ Error procesando {label}: {e}")
            continue
    
    print("\n✅ Proceso de descarga completado.")
    
    # Display summary
    print("\n📊 Resumen de archivos descargados:")
    for label in odlyzko_sources.keys():
        out_file = f"zeros/zeros_{label}.txt"
        if os.path.exists(out_file):
            size = os.path.getsize(out_file)
            print(f"  ✅ {out_file} ({size:,} bytes)")
        else:
            print(f"  ❌ {out_file} (no descargado)")

if __name__ == "__main__":
    main()

