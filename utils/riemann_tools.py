import mpmath as mp
from pathlib import Path

try:
    from .path_utils import get_project_path
except ImportError:
    # Fallback for direct execution
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from utils.path_utils import get_project_path

def t_to_n(t):
    """Inversa aproximada de la fórmula de Riemann–von Mangoldt: estima n dado t."""
    return int((t / (2 * mp.pi)) * mp.log(t / (2 * mp.pi)) - (t / (2 * mp.pi)) + 0.875)

def load_zeros_near_t(filename, t_min, t_max):
    """Carga los ceros entre t_min y t_max desde un archivo de texto con un gamma por línea.
    
    Args:
        filename: Path to zeros file (can be relative to project root or absolute)
        t_min: Minimum value of gamma to load
        t_max: Maximum value of gamma to load
        
    Returns:
        List of zeros as mpmath.mpf values
    """
    zeros = []
    # Convert to absolute path if it's a relative path
    filepath = Path(filename)
    if not filepath.is_absolute():
        filepath = get_project_path(filename)
    
    with open(filepath) as f:
        for line in f:
            gamma = float(line.strip())
            if t_min <= gamma <= t_max:
                zeros.append(mp.mpf(gamma))
    return zeros

