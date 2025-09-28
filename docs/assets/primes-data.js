// First 100 prime numbers for demonstration
window.PRIMES = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
    421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
    509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607
];

// Generate von Mangoldt function Λ(n) values
// Λ(n) = log(p) if n = p^k for prime p, 0 otherwise
window.VON_MANGOLDT = {};

// Fill von Mangoldt values for prime powers up to reasonable limit
for (let i = 0; i < window.PRIMES.length; i++) {
    const p = window.PRIMES[i];
    if (p > 1000) break; // Limit for demonstration
    
    // Λ(p) = log(p)
    window.VON_MANGOLDT[p] = Math.log(p);
    
    // Λ(p^k) = log(p) for k > 1, up to reasonable limit
    let pk = p * p;
    while (pk <= 1000) {
        window.VON_MANGOLDT[pk] = Math.log(p);
        pk *= p;
    }
}

// Export for use in other modules
if (typeof module !== 'undefined' && module.exports) {
    module.exports = { 
        PRIMES: window.PRIMES, 
        VON_MANGOLDT: window.VON_MANGOLDT 
    };
}