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

def download_and_extract(url, out_file):
    """Download and extract a gzipped file from Odlyzko's website."""
    if os.path.exists(out_file):
        print(f"✅ {out_file} already exists, skipping download.")
        return True
    
    try:
        gz_path = out_file + ".gz"
        print(f"🔽 Downloading: {url}")
        
        # Download with timeout and error handling
        response = requests.get(url, stream=True, timeout=30)
        response.raise_for_status()
        
        with open(gz_path, 'wb') as f:
            for chunk in response.iter_content(chunk_size=8192):
                if chunk:
                    f.write(chunk)
        
        print("✅ Downloaded. Extracting...")
        
        # Extract gzip file
        with gzip.open(gz_path, 'rb') as gz_in:
            with open(out_file, 'wb') as txt_out:
                txt_out.write(gz_in.read())
        
        # Clean up gz file
        os.remove(gz_path)
        
        # Validate format (check first few lines are floats)
        if validate_zeros_format(out_file):
            print(f"✅ Downloaded and validated: {out_file}")
            return True
        else:
            print(f"❌ Invalid format in: {out_file}")
            os.remove(out_file)
            return False
            
    except requests.RequestException as e:
        print(f"❌ Failed to download {url}: {e}")
        if os.path.exists(gz_path):
            os.remove(gz_path)
        return False
    except Exception as e:
        print(f"❌ Error processing {url}: {e}")
        if os.path.exists(gz_path):
            os.remove(gz_path)
        if os.path.exists(out_file):
            os.remove(out_file)
        return False

def validate_zeros_format(filename, max_check=10):
    """Validate that the file contains floating point numbers, one per line."""
    try:
        with open(filename, 'r') as f:
            for i, line in enumerate(f):
                if i >= max_check:
                    break
                line = line.strip()
                if not line:
                    continue
                float(line)  # This will raise ValueError if not a valid float
        return True
    except (ValueError, IOError):
        return False

# Odlyzko sources - using correct URLs from problem statement
odlyzko_sources = {
    "t1e8":  "https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1.gz",
    # Additional sources for scalability
    "t1e12": "https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros12.gz",
}

def main():
    """Main function to download Odlyzko zeros data."""
    os.makedirs("zeros", exist_ok=True)
    
    success_count = 0
    total_count = 0
    
    for label, url in odlyzko_sources.items():
        out_file = f"zeros/zeros_{label}.txt"
        total_count += 1
        
        if download_and_extract(url, out_file):
            success_count += 1
        
        # Only download the first file (t1e8) by default unless specifically requested
        if label == "t1e8":
            break
    
    if success_count > 0:
        print(f"✅ Ready! Successfully processed {success_count}/{total_count} files")
    else:
        print("❌ No files were successfully downloaded")
        sys.exit(1)

if __name__ == "__main__":
    main()

