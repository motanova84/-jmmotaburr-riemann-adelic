import requests
import gzip  
import os
import sys
import argparse
from pathlib import Path

def download_and_extract(url, out_txt):
    """Download and extract gzipped file."""
    gz_path = out_txt + ".gz"
    print(f"🔽 Descargando: {url}")
    
    try:
        r = requests.get(url, stream=True, timeout=30)
        r.raise_for_status()
        
        with open(gz_path, 'wb') as f:
            for chunk in r.iter_content(chunk_size=8192):
                f.write(chunk)
        
        print("✅ Descargado. Extrayendo...")
        
        # Check if file is actually gzipped
        try:
            with gzip.open(gz_path, 'rb') as gz_in:
                with open(out_txt, 'wb') as txt_out:
                    txt_out.write(gz_in.read())
        except gzip.BadGzipFile:
            # File might already be plain text
            print("⚠️  File appears to be plain text, copying directly...")
            os.rename(gz_path, out_txt)
        
        if os.path.exists(gz_path):
            os.remove(gz_path)
            
        print(f"📂 Guardado en: {out_txt}")
        
        # Validate content
        validate_zeros_file(out_txt)
        
    except Exception as e:
        print(f"❌ Error downloading {url}: {e}")
        return False
        
    return True

def validate_zeros_file(filename):
    """Validate that zeros file contains valid numerical data."""
    if not os.path.exists(filename):
        print(f"❌ File {filename} does not exist")
        return False
        
    try:
        with open(filename, 'r') as f:
            lines = f.readlines()
            
        if len(lines) < 100:
            print(f"⚠️  File {filename} has only {len(lines)} lines (expected more)")
            return False
            
        # Check first few lines are valid numbers
        valid_count = 0
        for i, line in enumerate(lines[:10]):
            try:
                gamma = float(line.strip())
                if gamma > 0:
                    valid_count += 1
            except ValueError:
                print(f"⚠️  Invalid line {i}: {line.strip()}")
                
        if valid_count < 8:
            print(f"❌ File validation failed - only {valid_count}/10 valid entries")
            return False
            
        print(f"✅ File validation passed - {len(lines)} zeros, first 10 entries valid")
        return True
        
    except Exception as e:
        print(f"❌ Error validating {filename}: {e}")
        return False

# Tablas de Odlyzko (ejemplos)
odlyzko_sources = {
    "t1e8":  "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeros1",
    "t1e10": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e10_1e4_1e6.txt.gz",
    "t1e12": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e12_1e4_1e6.txt.gz"
}

def ensure_zeros_available():
    """Ensure zeros file exists and is valid."""
    zeros_file = "zeros/zeros_t1e8.txt"
    
    if os.path.exists(zeros_file) and validate_zeros_file(zeros_file):
        print(f"✅ Zeros file already available: {zeros_file}")
        return True
        
    print("📥 Zeros file missing or invalid, attempting to create/download...")
    
    # First try to extract from existing .gz file
    gz_file = "zeros/zeros_t1e8.txt.gz"
    if os.path.exists(gz_file):
        print("Found existing .gz file, attempting extraction...")
        try:
            # Check if it's actually gzipped or just plain text
            with open(gz_file, 'rb') as f:
                header = f.read(2)
            
            if header == b'\x1f\x8b':  # Gzip magic number
                with gzip.open(gz_file, 'rb') as gz_in:
                    with open(zeros_file, 'wb') as txt_out:
                        txt_out.write(gz_in.read())
            else:
                # Plain text file with .gz extension
                import shutil
                shutil.copy2(gz_file, zeros_file)
                
            if validate_zeros_file(zeros_file):
                print(f"✅ Successfully extracted zeros to {zeros_file}")
                return True
                
        except Exception as e:
            print(f"❌ Error extracting from {gz_file}: {e}")
    
    # Try downloading from Odlyzko
    os.makedirs("zeros", exist_ok=True)
    
    for label, url in odlyzko_sources.items():
        out_file = f"zeros/zeros_{label}.txt"
        print(f"Attempting to download {label} from {url}...")
        
        if download_and_extract(url, out_file):
            # If this is the t1e8 file, copy it to the standard location
            if label == "t1e8" and out_file != zeros_file:
                import shutil
                shutil.copy2(out_file, zeros_file)
            return True
    
    print("❌ All download attempts failed")
    return False

def main():
    """Main function with argument parsing."""
    parser = argparse.ArgumentParser(description="Download and manage Riemann zeta zeros data")
    parser.add_argument("--check", action="store_true", 
                       help="Check if zeros file exists and is valid")
    parser.add_argument("--force-download", action="store_true",
                       help="Force download even if file exists") 
    parser.add_argument("--dataset", choices=list(odlyzko_sources.keys()),
                       help="Specify which dataset to download")
    
    args = parser.parse_args()
    
    if args.check:
        zeros_file = "zeros/zeros_t1e8.txt"
        if os.path.exists(zeros_file):
            valid = validate_zeros_file(zeros_file)
            sys.exit(0 if valid else 1)
        else:
            print(f"❌ Zeros file {zeros_file} does not exist")
            sys.exit(1)
    
    if args.force_download or not os.path.exists("zeros/zeros_t1e8.txt"):
        success = ensure_zeros_available()
        sys.exit(0 if success else 1)
    else:
        print("✅ Zeros file already exists. Use --force-download to re-download.")

if __name__ == "__main__":
    main()

