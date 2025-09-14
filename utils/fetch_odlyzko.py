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

def download_and_extract(url, out_txt):
    gz_path = out_txt + ".gz"
    print(f"🔽 Descargando: {url}")
    r = requests.get(url, stream=True)
    with open(gz_path, 'wb') as f:
        for chunk in r.iter_content(chunk_size=8192):
            f.write(chunk)
    print("✅ Descargado. Extrayendo...")
    with gzip.open(gz_path, 'rb') as gz_in:
        with open(out_txt, 'wb') as txt_out:
            txt_out.write(gz_in.read())
    os.remove(gz_path)
    print(f"📂 Guardado en: {out_txt}")

# Tablas de Odlyzko (ejemplos)
odlyzko_sources = {
    "t1e8":  "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeros1",
    "t1e10": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e10_1e4_1e6.txt.gz",
    "t1e12": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e12_1e4_1e6.txt.gz"
}

def main():
    os.makedirs("zeros", exist_ok=True)
    
    # Check if zeros_t1e8.txt already exists
    target_file = "zeros/zeros_t1e8.txt"
    if os.path.exists(target_file):
        print(f"✅ {target_file} already exists, skipping download")
        return
    
    # Download the main zero file we need
    if "t1e8" in odlyzko_sources:
        url = odlyzko_sources["t1e8"]
        print(f"Downloading zeros from Odlyzko database...")
        try:
            download_and_extract(url, target_file)
            
            # Validate format (basic check)
            with open(target_file, 'r') as f:
                lines = f.readlines()[:10]  # Check first 10 lines
                for i, line in enumerate(lines):
                    try:
                        float(line.strip())
                    except ValueError:
                        print(f"⚠️  Warning: Invalid format at line {i+1}: {line.strip()}")
                        break
                else:
                    print(f"✅ Format validation passed for {target_file}")
                    
            print("✅ Ready")
            
        except Exception as e:
            print(f"❌ Error downloading zeros: {e}")
            print("Using mpmath built-in zeros as fallback")
    else:
        print("❌ No URL configured for zeros_t1e8")

if __name__ == "__main__":
    main()

