# 🌐 Riemann-Adelic Web Interface

## Overview

This web interface provides an interactive demonstration of the enhanced mathematical functions implemented for the Riemann Hypothesis validation project.

## Enhanced Functions

### 📊 Function X (f1) - Enhanced Smooth Bump Function
- **Original**: Basic smooth bump function with `exp(-1/(1-u²/a²))`
- **Enhanced**: 
  - Improved numerical stability with conservative boundary handling
  - Added normalization factor for better integration properties
  - Additional smoothing factor: `exp(-x²/2)`
  - Better error handling for edge cases
  - Mathematical rigor improvements for critical line verification

### 🔬 A_∞ Function - Enhanced Archimedean Contribution
- **Original**: Basic archimedean integral computation
- **Enhanced**:
  - Better error handling for digamma function computation
  - Functional equation handling for negative real parts
  - Convergence factors for improved integration stability
  - Adaptive error control with fallback mechanisms
  - Enhanced normalization and real part extraction

## Static Web Interface (GitHub Pages Ready)

### NEW: 100% Static Implementation
The web interface has been converted to a **pure static application** that runs entirely in the browser without any server dependencies!

### Features
- ✅ **Complete Mathematical Engine in JavaScript** - All validation calculations run client-side
- ✅ **Interactive Validation Panel** - Real-time parameter adjustment and testing
- ✅ **Multiple Test Functions** - f1, f2, f3, and truncated Gaussian implementations
- ✅ **GitHub Pages Compatible** - No server required, works from any static host
- ✅ **Precalculated Sample Data** - Instant demonstration with Riemann zeros and primes

### Quick Start
```bash
# Build the static site
npm run build

# Serve locally for testing (optional)
python3 -m http.server 8000 --directory docs
# Then open http://localhost:8000
```

### Live Demo
Access the interactive dashboard at: **GitHub Pages URL** (deployed automatically)

### Interactive Features
- **Parameter Controls**: Adjust max zeros, max primes, and test functions
- **Real-time Validation**: Calculate explicit formula validation in your browser  
- **Visual Results**: See left/right side comparison and error metrics
- **Mathematical Functions**: Choose from enhanced f1, f2, f3, or truncated Gaussian

## Web Interface Features

### 🔬 Enhanced f1 Function Test
- Interactive testing of the improved f1 function
- Real-time output display
- Mathematical validation results

### ⚖️ Quick Validation
- Run Riemann Hypothesis validation with enhanced functions
- Configurable parameters (primes count, zeros count, test function)
- Arithmetic vs spectral side comparison

### 🎯 Critical Line Demo
- Demonstrate critical line verification under RH axioms
- Show that zeros satisfy Re(s) = 1/2
- Mathematical proof certificate generation

### 📊 System Status
- Real-time health monitoring
- Python environment validation
- Dependency status checking

## Mathematical Implementation

The static interface implements a **complete JavaScript port** of the Python mathematical functions:

### Core Functions
- **f1**: Enhanced smooth bump function with numerical stability improvements
- **f2**: Cosine-based compactly supported function  
- **f3**: Polynomial cutoff function with exponential decay
- **truncatedGaussian**: Smooth compactly supported Gaussian function

### Validation Engine
- **Weil Explicit Formula**: Client-side implementation comparing zeros and primes sides
- **Archimedean Contribution**: Simplified approximation for web performance
- **Error Analysis**: Absolute and relative error calculation
- **Sample Data Integration**: Loads precalculated zeros and primes from JSON

### Technical Approach
The JavaScript implementation provides:
1. **Numerical Stability** - Enhanced boundary conditions and error handling
2. **Performance Optimization** - Reduced precision for responsive web experience  
3. **Mathematical Rigor** - Core validation logic preserved from Python implementation
4. **Browser Compatibility** - Pure ES6+ JavaScript, no external math libraries required

## Deployment

### GitHub Pages (Automatic)
The repository is configured for automatic GitHub Pages deployment:
- **Trigger**: Every push to `main` branch
- **Build**: Static site created in `_site` directory  
- **Deploy**: Automatic deployment to GitHub Pages
- **URL**: `https://motanova84.github.io/-jmmotaburr-riemann-adelic/`

### Manual Static Deployment
For other static hosts:
```bash
# Build static site
npm run build

# Deploy docs/ directory to your static host
# (Contains index.html and data/ directory)
```

### Local Development
```bash
# Serve locally for testing
python3 -m http.server 8000 --directory docs
# Access at http://localhost:8000
```

## Contributing

When making changes to the mathematical functions:

1. **Update JavaScript functions** in `riemann_viewer.html`
2. **Test locally** using `npm run build` and local server
3. **Verify mathematical accuracy** using the interactive validation panel
4. **Ensure GitHub Actions workflows pass**
5. **Update documentation** as needed

The static approach ensures:
- ✅ **No server maintenance** required
- ✅ **Instant global availability** via GitHub Pages  
- ✅ **Full mathematical functionality** in the browser
- ✅ **Educational accessibility** - view source to see implementation

## Support

For mathematical questions: José Manuel Mota Burruezo (motanova84@gmail.com)
For technical issues: Open an issue in the GitHub repository