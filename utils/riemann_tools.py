import mpmath as mp


def t_to_n(t):
    """Inversa aproximada de la fórmula de Riemann–von Mangoldt: estima n dado t."""
    return int((t / (2 * mp.pi)) * mp.log(t / (2 * mp.pi)) - (t / (2 * mp.pi)) + 0.875)


def load_zeros_near_t(filename, t_min, t_max):
    """Carga los ceros entre t_min y t_max desde un archivo de texto con un gamma por línea."""
    zeros = []
    with open(filename) as f:
        for line in f:
            gamma = float(line.strip())
            if t_min <= gamma <= t_max:
                zeros.append(mp.mpf(gamma))
    return zeros
