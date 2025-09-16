import mpmath as mp
import os

def t_to_n(t):
    """
    Inversa aproximada de la fórmula de Riemann–von Mangoldt: estima n dado t.
    
    Args:
        t: Height parameter
        
    Returns:
        Estimated n value
    """
    if t <= 0:
        raise ValueError("t must be positive")
    return int((t / (2 * mp.pi)) * mp.log(t / (2 * mp.pi)) - (t / (2 * mp.pi)) + 0.875)

def load_zeros_near_t(filename, t_min, t_max):
    """
    Carga los ceros entre t_min y t_max desde un archivo de texto con un gamma por línea.
    
    Args:
        filename: Path to zeros file
        t_min: Minimum t value
        t_max: Maximum t value
        
    Returns:
        List of zeros in the specified range
    """
    if not os.path.exists(filename):
        raise FileNotFoundError(f"Zeros file not found: {filename}")
    
    if t_min >= t_max:
        raise ValueError("t_min must be less than t_max")
    
    zeros = []
    try:
        with open(filename, 'r') as f:
            for line_num, line in enumerate(f, 1):
                try:
                    gamma = float(line.strip())
                    if t_min <= gamma <= t_max:
                        zeros.append(mp.mpf(gamma))
                except ValueError:
                    print(f"Warning: Invalid number at line {line_num}: '{line.strip()}'")
                    continue
    except Exception as e:
        raise RuntimeError(f"Error reading zeros file: {e}")
    
    return zeros

