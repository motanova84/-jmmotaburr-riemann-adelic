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
    for label, url in odlyzko_sources.items():
        out_file = f"zeros/zeros_{label}.txt"
        download_and_extract(url, out_file)

if __name__ == "__main__":
    main()

