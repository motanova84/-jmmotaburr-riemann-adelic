"""
Enhanced Odlyzko Zero Data Fetching and Validation

This script:
- Checks if zeros_t1e8.txt already exists
- If not, downloads from Odlyzko and decompresses  
- Validates format (float per line)
- Moves the cleaned file to zeros/ and prints "✅ Ready"
"""

import requests
import gzip
import os
import sys
import logging
from pathlib import Path

# Setup basic logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

def download_and_extract(url, out_txt):
    """Download and extract a gzipped file."""
    gz_path = out_txt + ".gz"
    logging.info(f"🔽 Downloading: {url}")
    
    try:
        response = requests.get(url, stream=True, timeout=300)
        response.raise_for_status()
        
        with open(gz_path, 'wb') as f:
            for chunk in response.iter_content(chunk_size=8192):
                if chunk:
                    f.write(chunk)
        
        logging.info("✅ Download completed. Extracting...")
        
        with gzip.open(gz_path, 'rb') as gz_in:
            with open(out_txt, 'wb') as txt_out:
                txt_out.write(gz_in.read())
        
        os.remove(gz_path)
        logging.info(f"📂 Saved to: {out_txt}")
        
    except requests.RequestException as e:
        logging.error(f"❌ Download failed: {e}")
        raise
    except Exception as e:
        logging.error(f"❌ Extraction failed: {e}")
        if os.path.exists(gz_path):
            os.remove(gz_path)
        raise

def validate_zeros_file(filepath, max_check=1000):
    """Validate that the zeros file contains valid float values."""
    logging.info(f"🔍 Validating zeros file: {filepath}")
    
    if not os.path.exists(filepath):
        raise FileNotFoundError(f"Zeros file not found: {filepath}")
    
    valid_count = 0
    line_count = 0
    
    try:
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                
                line_count += 1
                try:
                    float(line)
                    valid_count += 1
                except ValueError:
                    logging.warning(f"Invalid zero value at line {line_count}: {line}")
                
                # Check first max_check lines for efficiency
                if line_count >= max_check:
                    break
    
    except Exception as e:
        logging.error(f"❌ Error reading zeros file: {e}")
        raise
    
    if valid_count == 0:
        raise ValueError("No valid zeros found in file")
    
    validation_rate = valid_count / line_count if line_count > 0 else 0
    logging.info(f"✅ Validation completed: {valid_count}/{line_count} valid zeros ({validation_rate:.1%})")
    
    return valid_count, line_count

# Enhanced Odlyzko sources with multiple options
odlyzko_sources = {
    "t1e8": {
        "url": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeros1",
        "description": "First 10^8 zeros"
    },
    "t1e10": {
        "url": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e10_1e4_1e6.txt.gz",
        "description": "Zeros at height ~10^10"  
    },
    "t1e12": {
        "url": "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e12_1e4_1e6.txt.gz",
        "description": "Zeros at height ~10^12"
    }
}

def fetch_zeros(dataset="t1e8", force_download=False, validate=True):
    """
    Fetch and validate Odlyzko zeros data.
    
    Args:
        dataset: Dataset key from odlyzko_sources
        force_download: Force re-download even if file exists
        validate: Whether to validate the downloaded file
    """
    if dataset not in odlyzko_sources:
        raise ValueError(f"Unknown dataset: {dataset}. Available: {list(odlyzko_sources.keys())}")
    
    source = odlyzko_sources[dataset]
    zeros_dir = Path("zeros")
    zeros_dir.mkdir(exist_ok=True)
    
    out_file = zeros_dir / f"zeros_{dataset}.txt"
    
    # Check if file already exists
    if out_file.exists() and not force_download:
        logging.info(f"📁 Zeros file already exists: {out_file}")
        if validate:
            try:
                validate_zeros_file(out_file)
                logging.info("✅ Existing file validated successfully")
                return str(out_file)
            except Exception as e:
                logging.warning(f"⚠️ Existing file validation failed: {e}")
                logging.info("🔄 Re-downloading...")
        else:
            logging.info("✅ Using existing file without validation")  
            return str(out_file)
    
    # Download the file
    logging.info(f"📥 Fetching {dataset}: {source['description']}")
    try:
        download_and_extract(source["url"], str(out_file))
    except Exception as e:
        logging.error(f"❌ Failed to fetch {dataset}: {e}")
        raise
    
    # Validate the downloaded file
    if validate:
        try:
            validate_zeros_file(out_file)
        except Exception as e:
            logging.error(f"❌ Downloaded file validation failed: {e}")
            # Clean up invalid file
            if out_file.exists():
                out_file.unlink()
            raise
    
    logging.info("✅ Ready")
    return str(out_file)

def main():
    """Main function with CLI support."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Fetch and validate Odlyzko zeros data')
    parser.add_argument('--dataset', default='t1e8', choices=list(odlyzko_sources.keys()),
                       help='Dataset to fetch (default: t1e8)')
    parser.add_argument('--force', action='store_true',
                       help='Force re-download even if file exists')
    parser.add_argument('--no-validate', action='store_true',
                       help='Skip validation of downloaded file')
    parser.add_argument('--list', action='store_true',
                       help='List available datasets')
    
    args = parser.parse_args()
    
    if args.list:
        print("Available Odlyzko datasets:")
        for key, source in odlyzko_sources.items():
            print(f"  {key}: {source['description']}")
            print(f"    URL: {source['url']}")
        return
    
    try:
        filepath = fetch_zeros(
            dataset=args.dataset,
            force_download=args.force,
            validate=not args.no_validate
        )
        print(f"✅ Zeros data ready at: {filepath}")
    except Exception as e:
        logging.error(f"❌ Failed: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()

