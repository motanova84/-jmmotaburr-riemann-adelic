# utils/fetch_odlyzko.py
import requests, gzip, os

def download_and_extract(url, out_txt):
    """Download and extract Odlyzko zeros if not present."""
    if os.path.exists(out_txt):
        print("✅ zeros_t1e8.txt already exists, skipping download.")
        return
    try:
        response = requests.get(url, timeout=10)
        response.raise_for_status()
        with open(out_txt + '.gz', 'wb') as f:
            f.write(response.content)
        with gzip.open(out_txt + '.gz', 'rb') as f_in:
            with open(out_txt, 'wb') as f_out:
                f_out.write(f_in.read())
        os.remove(out_txt + '.gz')
        print("✅ Downloaded and extracted zeros_t1e8.txt.")
    except requests.RequestException as e:
        print(f"Warning: Failed to download zeros: {e}")

if __name__ == "__main__":
    url = "https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1"
    out_txt = "zeros/zeros_t1e8.txt"
    download_and_extract(url, out_txt)

