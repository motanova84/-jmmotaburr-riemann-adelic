import numpy as np
from numpy.linalg import eigvals

def K_t(x, y, t=1e-2, N=200):
    """
    Núcleo resolvente suavizado K_t(x,y).
    
    Args:
        x: Point x
        y: Point y
        t: Regularization parameter (default: 1e-2)
        N: Number of integration points (default: 200)
        
    Returns:
        Complex kernel value K_t(x,y)
    """
    u = np.linspace(-50, 50, N)
    integrand = np.exp(-t * (u**2 + 0.25)) * np.exp(1j * u * (np.log(x) - np.log(y)))
    return np.trapezoid(integrand, u)

def R_t_matrix(grid, t=1e-2):
    """
    Matriz discretizada del operador R_t en una base {log grid}.
    
    Args:
        grid: Grid of points
        t: Regularization parameter (default: 1e-2)
        
    Returns:
        Complex matrix representing R_t
    """
    n = len(grid)
    M = np.zeros((n, n), dtype=complex)
    for i, xi in enumerate(grid):
        for j, yj in enumerate(grid):
            M[i, j] = K_t(xi, yj, t)
    return M

def approximate_spectrum(grid, t=1e-2):
    """
    Aproxima espectro de H vía diagonalización de R_t.
    
    Args:
        grid: Grid of points
        t: Regularization parameter (default: 1e-2)
        
    Returns:
        Sorted array of real eigenvalues
    """
    M = R_t_matrix(grid, t)
    vals = eigvals(M)
    return np.sort(np.real(vals))
