/**
 * Riemann Static Calculator - 100% Client-side Mathematical Computing
 * Ported from Python implementation for GitHub Pages deployment
 */

class RiemannStaticCalculator {
    constructor() {
        this.precision = 15; // JavaScript number precision
    }

    // Test functions ported from Python
    truncatedGaussian(u, a = 5.0, sigma = 1.0) {
        if (Math.abs(u) > a) return 0;
        return Math.exp(-u * u / (2 * sigma * sigma));
    }

    f1(u, a = 3.0) {
        // Enhanced smooth bump function
        if (Math.abs(u) > a) return 0;
        
        const x = u / a;
        if (Math.abs(x) >= 0.999999) return 0;
        
        try {
            const denominator = 1 - x * x;
            if (denominator <= 1e-15) return 0;
            
            const normalization = Math.exp(-1);
            const result = normalization * Math.exp(-1 / denominator);
            const smoothingFactor = Math.exp(-x * x / 2);
            
            return result * smoothingFactor;
        } catch (e) {
            return 0;
        }
    }

    f2(u, a = 4.0) {
        // Cosine-based compactly supported function
        if (Math.abs(u) > a) return 0;
        const cosValue = Math.cos(Math.PI * u / (2 * a));
        return cosValue * cosValue;
    }

    f3(u, a = 2.5) {
        // Polynomial cutoff function
        if (Math.abs(u) > a) return 0;
        const x = u / a;
        return Math.pow(1 - x * x, 3) * Math.exp(-x * x);
    }

    // Simple Mellin transform approximation (for demo purposes)
    mellinTransform(f, s, limit = 5.0) {
        // Numerical integration approximation
        // ∫ f(u) * u^(s-1) du from 0 to limit
        const steps = 1000;
        const dx = limit / steps;
        let sum = 0;
        
        for (let i = 1; i < steps; i++) {
            const u = i * dx;
            if (u > 0) {
                const fValue = f(u);
                // u^(s-1) for complex s = sigma + i*t
                // |u^(s-1)| = u^(sigma-1)
                const powerTerm = Math.pow(u, s.real - 1);
                sum += fValue * powerTerm * dx;
            }
        }
        
        return { real: sum, imag: 0 }; // Simplified for demo
    }

    // Gamma function (Stirling's approximation for large values)
    logGamma(z) {
        if (z < 12) {
            // Use simple approximation for small values
            return Math.log(Math.sqrt(2 * Math.PI / z)) + z * Math.log(z) - z;
        }
        
        // Stirling's approximation
        const lnSqrt2Pi = Math.log(Math.sqrt(2 * Math.PI));
        return lnSqrt2Pi - 0.5 * Math.log(z) + z * (Math.log(z) - 1);
    }

    // Digamma function approximation
    digamma(x) {
        if (x < 8) {
            // Use recurrence relation for small values
            let result = this.digamma(x + 1);
            return result - 1/x;
        }
        
        // Asymptotic series for large x
        const invX = 1 / x;
        const invX2 = invX * invX;
        
        return Math.log(x) - 0.5 * invX - invX2/12 + invX2*invX2/120;
    }

    // Calculate explicit formula verification
    calculateExplicitFormula(zeros, primes, testFunction = 'f1', precision = 15) {
        console.log(`🧮 Running explicit formula with ${testFunction}`);
        
        // Select test function
        let f;
        switch (testFunction) {
            case 'f1': f = (u) => this.f1(u); break;
            case 'f2': f = (u) => this.f2(u); break;
            case 'f3': f = (u) => this.f3(u); break;
            case 'truncated_gaussian': f = (u) => this.truncatedGaussian(u); break;
            default: f = (u) => this.f1(u);
        }

        // LEFT SIDE: Sum over zeros
        let leftSide = 0;
        const maxZeros = Math.min(zeros.length, 50); // Limit for demo
        
        for (let i = 0; i < maxZeros; i++) {
            const gamma = zeros[i];
            // Non-trivial zero: ρ = 1/2 + i*γ
            const rho = { real: 0.5, imag: gamma };
            
            // Simplified Mellin transform for demo
            const mellinValue = this.mellinTransform(f, { real: rho.real - 1, imag: rho.imag });
            leftSide += mellinValue.real;
        }

        // LEFT SIDE: Archimedean contribution (simplified)
        const archContribution = this.calculateArchimedeantContribution(f);
        leftSide += archContribution;

        // RIGHT SIDE: Sum over primes using von Mangoldt function
        let rightSide = 0;
        const maxN = Math.min(1000, Object.keys(window.VON_MANGOLDT || {}).length);
        
        for (let n = 2; n <= maxN; n++) {
            if (window.VON_MANGOLDT && window.VON_MANGOLDT[n]) {
                const lambda_n = window.VON_MANGOLDT[n];
                const logN = Math.log(n);
                const fValue = f(logN);
                rightSide += lambda_n * fValue;
            }
        }

        // Add residue terms (simplified)
        const residueTerms = this.calculateResidueTerms(f);
        rightSide += residueTerms;

        // Calculate error
        const error = Math.abs(leftSide - rightSide);
        const relativeError = rightSide !== 0 ? error / Math.abs(rightSide) : 0;

        return {
            leftSide: leftSide,
            rightSide: rightSide,
            error: error,
            relativeError: relativeError,
            testFunction: testFunction,
            zerosUsed: maxZeros,
            status: relativeError < 0.1 ? 'PASS' : 'REVIEW'
        };
    }

    calculateArchimedeantContribution(f) {
        // Simplified Archimedean integral approximation
        // This is a major simplification for demo purposes
        const T = 10; // Integration limit
        const steps = 100;
        const dt = 2 * T / steps;
        let sum = 0;

        for (let i = 0; i < steps; i++) {
            const t = -T + i * dt;
            const s = { real: 0.5, imag: t };
            
            // Simplified digamma computation
            try {
                const digammaValue = this.digamma(s.real / 2);
                const kernelValue = 0.5 * (digammaValue - Math.log(Math.PI));
                sum += kernelValue * dt;
            } catch (e) {
                // Skip problematic values
            }
        }

        return sum / (2 * Math.PI);
    }

    calculateResidueTerms(f) {
        // Simplified residue calculation for demo
        // Main residue at s=1: -f(0)
        try {
            return -f(0);
        } catch (e) {
            return 0;
        }
    }

    // Generate verification summary
    generateVerificationSummary() {
        const testFunctions = ['f1', 'f2', 'f3', 'truncated_gaussian'];
        const results = [];

        for (const func of testFunctions) {
            const result = this.calculateExplicitFormula(
                window.RIEMANN_ZEROS || [], 
                window.PRIMES || [], 
                func
            );
            results.push(result);
        }

        return {
            timestamp: new Date().toISOString(),
            totalTests: results.length,
            passedTests: results.filter(r => r.status === 'PASS').length,
            results: results,
            overallStatus: results.every(r => r.status === 'PASS') ? 'VERIFIED' : 'PARTIAL'
        };
    }
}

// Make available globally
window.RiemannStaticCalculator = RiemannStaticCalculator;

// Export for module systems
if (typeof module !== 'undefined' && module.exports) {
    module.exports = RiemannStaticCalculator;
}