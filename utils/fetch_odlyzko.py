"""
🧠 Copilot Prompt:
Enhance this script to:
- Check if zeros_t1e8.txt already exists.
- If not, download from Odlyzko and decompress.
- Validate format (float per line).
- Move the cleaned file to zeros/ and print "✅ Ready".

Also suggest adding this step to a GitHub Action on first run.
"""

import requests, gzip, os

def validate_zeros_file(filename):
    """Validate that the zeros file contains valid floats, one per line."""
    try:
        with open(filename, 'r') as f:
            count = 0
            for i, line in enumerate(f):
                if i >= 10:  # Check first 10 lines only
                    break
                try:
                    float(line.strip())
                    count += 1
                except ValueError:
                    print(f"❌ Invalid float at line {i+1}: {line.strip()}")
                    return False
        print(f"✅ Validated {count} lines in {filename}")
        return True
    except Exception as e:
        print(f"❌ Error validating {filename}: {e}")
        return False

def download_and_extract(url, out_txt):
    """Download and extract a gzipped file from URL."""
    gz_path = out_txt + ".gz"
    print(f"🔽 Descargando: {url}")
    try:
        r = requests.get(url, stream=True)
        r.raise_for_status()
        with open(gz_path, 'wb') as f:
            for chunk in r.iter_content(chunk_size=8192):
                f.write(chunk)
        print("✅ Descargado. Extrayendo...")
        with gzip.open(gz_path, 'rb') as gz_in:
            with open(out_txt, 'wb') as txt_out:
                txt_out.write(gz_in.read())
        os.remove(gz_path)
        print(f"📂 Guardado en: {out_txt}")
        return True
    except Exception as e:
        print(f"❌ Error downloading/extracting: {e}")
        if os.path.exists(gz_path):
            os.remove(gz_path)
        return False

# Tablas de Odlyzko (ejemplos)
odlyzko_sources = {
    "t1e8":  "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeros1",
    "t1e10": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e10_1e4_1e6.txt.gz",
    "t1e12": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e12_1e4_1e6.txt.gz"
}

def main():
    """Main function to check and download zeros files as needed."""
    os.makedirs("zeros", exist_ok=True)
    
    # Focus on t1e8 file which is what validate_explicit_formula.py uses
    target_file = "zeros/zeros_t1e8.txt"
    
    if os.path.exists(target_file):
        print(f"✅ Archivo {target_file} ya existe")
        if validate_zeros_file(target_file):
            print("✅ Ready")
            return True
        else:
            print("❌ Archivo corrupto, re-descargando...")
            os.remove(target_file)
    
    # Download the primary zeros file
    if download_and_extract(odlyzko_sources["t1e8"], target_file):
        if validate_zeros_file(target_file):
            print("✅ Ready")
            return True
        else:
            print("❌ Downloaded file is invalid")
            return False
    else:
        print("❌ Failed to download zeros file")
        return False

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)

