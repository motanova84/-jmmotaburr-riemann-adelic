"""
🧠 Enhanced Riemann Zeros Management

This script provides:
- Automatic download of Riemann zeros from Odlyzko tables
- Format validation (floats per line) with comprehensive error reporting  
- Multiple mirror sources for reliability
- Seamless integration with validation workflows
- Progress tracking and error recovery

Usage:
python utils/fetch_odlyzko.py [--target zeros_file] [--validate_only]
"""

import requests
import gzip
import os
import sys
import logging
from typing import Tuple, List

def setup_logging():
    """Setup logging for this module."""
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s'
    )
    return logging.getLogger(__name__)

def download_with_progress(url: str, filename: str, logger) -> bool:
    """Download file with progress tracking."""
    try:
        logger.info(f"🔽 Downloading: {url}")
        response = requests.get(url, stream=True, timeout=300)
        response.raise_for_status()
        
        total_size = int(response.headers.get('content-length', 0))
        downloaded = 0
        
        with open(filename, 'wb') as f:
            for chunk in response.iter_content(chunk_size=8192):
                if chunk:
                    f.write(chunk)
                    downloaded += len(chunk)
                    if total_size > 0:
                        progress = (downloaded / total_size) * 100
                        if downloaded % (1024*1024) == 0:  # Log every MB
                            logger.info(f"Progress: {progress:.1f}% ({downloaded/1024/1024:.1f}MB)")
        
        logger.info(f"✅ Download completed: {filename}")
        return True
    except Exception as e:
        logger.error(f"❌ Download failed: {e}")
        return False

def extract_gzip(gz_path: str, out_path: str, logger) -> bool:
    """Extract gzip file."""
    try:
        logger.info("📦 Extracting compressed file...")
        with gzip.open(gz_path, 'rb') as gz_in:
            with open(out_path, 'wb') as txt_out:
                txt_out.write(gz_in.read())
        os.remove(gz_path)
        logger.info(f"✅ Extracted to: {out_path}")
        return True
    except Exception as e:
        logger.error(f"❌ Extraction failed: {e}")
        return False

def validate_zeros_format(filename: str, logger, max_check: int = 1000) -> Tuple[bool, str, int]:
    """Validate zeros file format and count entries."""
    if not os.path.exists(filename):
        return False, f"File not found: {filename}", 0
    
    try:
        valid_count = 0
        total_lines = 0
        
        with open(filename, 'r') as f:
            for i, line in enumerate(f):
                total_lines += 1
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                    
                try:
                    float(line)
                    valid_count += 1
                except ValueError:
                    if i < 10:  # Only report first few errors
                        logger.warning(f"Invalid format at line {i+1}: '{line}'")
                    
                # Quick validation for large files
                if i >= max_check and valid_count > max_check * 0.8:
                    logger.info(f"Format validation passed (checked first {max_check} lines)")
                    break
        
        if valid_count == 0:
            return False, "No valid floating point numbers found", total_lines
        
        success_rate = valid_count / min(total_lines, max_check)
        if success_rate < 0.8:
            return False, f"Low success rate: {success_rate:.2%} valid entries", total_lines
        
        return True, f"Valid format: {valid_count} entries verified", total_lines
        
    except Exception as e:
        return False, f"Error reading file: {e}", 0

# Multiple mirror sources for reliability
ODLYZKO_SOURCES = {
    "t1e8": [
        "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeros1",
        "https://web.viu.ca/pughg/RiemannZeta/RiemannZetaLong/zeros1.dat",
    ],
    "t1e10": [
        "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e10_1e4_1e6.txt.gz",
    ],
    "t1e12": [
        "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e12_1e4_1e6.txt.gz",
    ]
}

def download_and_extract(urls: List[str], out_txt: str, logger) -> bool:
    """Try downloading from multiple sources."""
    gz_path = out_txt + ".gz"
    
    for i, url in enumerate(urls):
        logger.info(f"Attempting source {i+1}/{len(urls)}: {url}")
        
        # Determine if this URL is compressed
        is_compressed = url.endswith('.gz')
        download_path = gz_path if is_compressed else out_txt
        
        if download_with_progress(url, download_path, logger):
            if is_compressed:
                if extract_gzip(gz_path, out_txt, logger):
                    return True
                else:
                    continue  # Try next source
            else:
                return True
        else:
            logger.warning(f"Source {i+1} failed, trying next...")
    
    logger.error("❌ All download sources failed")
    return False

def ensure_zeros_file(target_file: str = "zeros/zeros_t1e8.txt", logger = None) -> bool:
    """Ensure zeros file exists and is valid."""
    if logger is None:
        logger = setup_logging()
    
    # Check if file already exists and is valid
    if os.path.exists(target_file):
        is_valid, msg, count = validate_zeros_format(target_file, logger)
        if is_valid:
            logger.info(f"✅ Using existing zeros file: {target_file} ({count} entries)")
            return True
        else:
            logger.warning(f"⚠️  Existing file is invalid: {msg}")
            logger.info("Will attempt to re-download...")
    
    # Ensure target directory exists
    os.makedirs(os.path.dirname(target_file), exist_ok=True)
    
    # Determine which dataset to download based on filename
    dataset_key = "t1e8"  # Default
    for key in ODLYZKO_SOURCES.keys():
        if key in target_file:
            dataset_key = key
            break
    
    logger.info(f"🔄 Downloading {dataset_key} zeros dataset...")
    
    # Download and extract
    if download_and_extract(ODLYZKO_SOURCES[dataset_key], target_file, logger):
        # Validate the downloaded file
        is_valid, msg, count = validate_zeros_format(target_file, logger)
        if is_valid:
            logger.info(f"🎯 Success! {msg}")
            return True
        else:
            logger.error(f"❌ Downloaded file is invalid: {msg}")
            return False
    else:
        return False

def main():
    """Main function with CLI support."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Manage Riemann zeros data files')
    parser.add_argument('--target', default='zeros/zeros_t1e8.txt',
                       help='Target zeros file path')
    parser.add_argument('--validate_only', action='store_true',
                       help='Only validate existing file, do not download')
    parser.add_argument('--force_download', action='store_true',
                       help='Force re-download even if file exists')
    
    args = parser.parse_args()
    logger = setup_logging()
    
    if args.validate_only:
        if os.path.exists(args.target):
            is_valid, msg, count = validate_zeros_format(args.target, logger)
            if is_valid:
                logger.info(f"✅ {msg}")
                return 0
            else:
                logger.error(f"❌ {msg}")
                return 1
        else:
            logger.error(f"❌ File not found: {args.target}")
            return 1
    
    if args.force_download and os.path.exists(args.target):
        logger.info(f"🗑️  Removing existing file: {args.target}")
        os.remove(args.target)
    
    if ensure_zeros_file(args.target, logger):
        logger.info("🎉 Zeros data ready for use!")
        return 0
    else:
        logger.error("❌ Failed to ensure zeros data availability")
        return 1

if __name__ == "__main__":
    sys.exit(main())

