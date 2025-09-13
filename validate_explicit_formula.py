import mpmath as mp
from utils.mellin import truncated_gaussian, mellin_transform

mp.mp.dps = 50

# Parámetros del experimento
P = 10000          # Máximo primo
K = 5              # Potencias máximas por primo
sigma0 = 2.0
T = 100
lim_u = 5.0

def prime_sum(f, P, K):
    total = mp.mpf('0')
    primes = list(mp.primepi(P))  # DEVUELVE el número de primos <= P
    for i in range(1, primes + 1):
        p = mp.prime(i)
        lp = mp.log(p)
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total

def archimedean_sum(f, sigma0, T, lim_u):
    def integrand(t):
        s = sigma0 + 1j * t
        kernel = mp.digamma(s / 2) - mp.log(mp.pi)
        return kernel * mellin_transform(f, s, lim_u)
    integral, err = mp.quad(integrand, [-T, T], error=True)
    return (integral / (2j * mp.pi)).real

def zero_sum(f, filename, lim_u=5):
    total = mp.mpf('0')
    with open(filename) as file:
        for line in file:
            gamma = mp.mpf(line.strip())
            total += mellin_transform(f, 1j * gamma, lim_u).real
    return total

if __name__ == "__main__":
    f = truncated_gaussian
    A = prime_sum(f, P, K) + archimedean_sum(f, sigma0, T, lim_u)
    Z = zero_sum(f, 'zeros/zeros_t1e8.txt', lim_u)

    print(f"Aritmético (Primes + Arch): {A}")
    print(f"Zero side (explicit sum):   {Z}")
    error = abs(A - Z)
    print(f"Error absoluto:             {error}")
    print(f"Error relativo:             {error / abs(A)}")

