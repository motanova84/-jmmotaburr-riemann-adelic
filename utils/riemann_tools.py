import mpmath as mp

def t_to_n(t):
    """Inversa aproximada de la fórmula de Riemann–von Mangoldt: estima n dado t.
    
    Fixed to ensure proper mpmath type handling and avoid float/mp mismatches.
    """
    # Ensure t is mpmath
    if not isinstance(t, mp.mpf):
        t = mp.mpf(t)
    
    two_pi = 2 * mp.pi
    log_term = mp.log(t / two_pi)
    result = (t / two_pi) * log_term - (t / two_pi) + mp.mpf('0.875')
    return int(result)

def load_zeros_near_t(filename, t_min, t_max):
    """Carga los ceros entre t_min y t_max desde un archivo de texto con un gamma por línea.
    
    Fixed to ensure proper mpmath type handling and avoid float/mp mismatches.
    """
    zeros = []
    # Ensure bounds are mpmath
    if not isinstance(t_min, mp.mpf):
        t_min = mp.mpf(t_min)
    if not isinstance(t_max, mp.mpf):
        t_max = mp.mpf(t_max)
        
    with open(filename, 'r') as f:
        for line in f:
            try:
                gamma_str = line.strip()
                if not gamma_str:  # Skip empty lines
                    continue
                # Convert directly to mpmath to avoid float intermediate step
                gamma = mp.mpf(gamma_str)
                if t_min <= gamma <= t_max:
                    zeros.append(gamma)
            except (ValueError, TypeError) as e:
                print(f"Warning: Skipping invalid zero value '{line.strip()}': {e}")
                continue
    return zeros

