# 🧮 Riemann Hypothesis Verification - Static GitHub Pages Site

This directory contains the **100% static implementation** of the Riemann Hypothesis verification dashboard, designed for GitHub Pages deployment.

## 🚀 Quick Deployment

To deploy this site on GitHub Pages:

1. Go to your repository **Settings** → **Pages**
2. Select **Source**: "Deploy from a branch"
3. Select **Branch**: `main`, **Folder**: `/docs`
4. Click **Save**

The site will be available at: `https://motanova84.github.io/-jmmotaburr-riemann-adelic/`

## 📁 Structure

```
docs/
├── index.html              # Main dashboard page
├── assets/
│   ├── zeros-data.js       # First 116 Riemann zeros
│   ├── primes-data.js      # First 111 primes + von Mangoldt function
│   └── math-worker.js      # Complete JavaScript mathematical engine
├── styles/
│   └── main.css           # Professional responsive styling
└── README.md              # This file
```

## 🧮 Features

- **100% Client-side**: No server dependencies, pure JavaScript
- **Interactive Verification**: Real-time mathematical calculations
- **4 Test Functions**: f1, f2, f3, and truncated Gaussian implementations
- **Responsive Design**: Works on desktop and mobile
- **Mathematical Accuracy**: Implements Weil explicit formula
- **Professional UI**: Modern gradient design with interactive charts

## 🔬 Mathematical Implementation

The static calculator implements:

- **Weil Explicit Formula**: Core mathematical framework
- **Mellin Transforms**: Numerical integration for test functions
- **Von Mangoldt Function**: Prime number theory calculations
- **Archimedean Contributions**: Complex analysis components
- **Error Analysis**: Relative and absolute error calculations

## 📊 Test Results

All test functions execute successfully with:
- Real-time error calculations
- Status indicators (PASS/REVIEW)
- Interactive data visualization
- Complete verification summaries

## 👨‍💻 Author

**José Manuel Mota Burruezo**  
Instituto Conciencia Cuántica (ICQ)  
Riemann Hypothesis Verification Project

---

*This implementation provides the first complete static deployment of the Riemann Hypothesis verification system for GitHub Pages.*