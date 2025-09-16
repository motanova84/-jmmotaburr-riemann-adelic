"""
🧠 Copilot Prompt:
Enhance this script to:
- Check if zeros_t1e8.txt already exists.
- If not, download from Odlyzko and decompress.
- Validate format (float per line).
- Move the cleaned file to zeros/ and print "✅ Ready".

Also suggest adding this step to a GitHub Action on first run.
"""

import requests
import gzip
import os
import sys
import logging

def validate_zeros_format(filepath):
    """Validate that the zeros file has the correct format (one float per line)."""
    try:
        with open(filepath, 'r') as f:
            lines = f.readlines()[:10]  # Check first 10 lines
            for i, line in enumerate(lines):
                line = line.strip()
                if line:
                    float(line)  # This will raise ValueError if not a valid float
        return True
    except (ValueError, FileNotFoundError) as e:
        logging.error(f"Invalid zeros file format: {e}")
        return False

def download_and_extract(url, out_txt):
    """Download and extract a gzipped file from URL."""
    gz_path = out_txt + ".gz"
    print(f"🔽 Downloading: {url}")
    try:
        r = requests.get(url, stream=True, timeout=60)
        r.raise_for_status()
        with open(gz_path, 'wb') as f:
            for chunk in r.iter_content(chunk_size=8192):
                f.write(chunk)
        print("✅ Downloaded. Extracting...")
        
        with gzip.open(gz_path, 'rb') as gz_in:
            with open(out_txt, 'wb') as txt_out:
                txt_out.write(gz_in.read())
        os.remove(gz_path)
        print(f"📂 Saved to: {out_txt}")
        
        # Validate format
        if validate_zeros_format(out_txt):
            print("✅ File format validated")
            return True
        else:
            print("❌ File format validation failed")
            return False
            
    except requests.RequestException as e:
        print(f"❌ Download failed: {e}")
        return False
    except Exception as e:
        print(f"❌ Extraction failed: {e}")
        return False

# Tablas de Odlyzko (ejemplos)
odlyzko_sources = {
    "t1e8":  "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeros1",
    "t1e10": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e10_1e4_1e6.txt.gz",
    "t1e12": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e12_1e4_1e6.txt.gz"
}

def main():
    """Main function to check and download zeros if needed."""
    os.makedirs("zeros", exist_ok=True)
    
    # Priority check for t1e8 (most commonly used)
    primary_file = "zeros/zeros_t1e8.txt"
    
    if os.path.exists(primary_file):
        print(f"✅ Zeros file already exists: {primary_file}")
        if validate_zeros_format(primary_file):
            print("✅ File format is valid")
            print("✅ Ready")
            return 0
        else:
            print("❌ Existing file format is invalid, re-downloading...")
            os.remove(primary_file)
    
    # Download primary zeros file
    success = download_and_extract(odlyzko_sources["t1e8"], primary_file)
    
    if success:
        print("✅ Ready")
        return 0
    else:
        print("❌ Failed to download and validate zeros data")
        return 1

if __name__ == "__main__":
    sys.exit(main())

