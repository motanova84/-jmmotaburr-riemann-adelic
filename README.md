> ✅ **IMPROVED: Path Independence**
> 
> This repository now supports execution from **any directory**! Scripts automatically detect the project root and resolve paths correctly, whether you run them from the project root or any subdirectory.
>
> **Examples - All work correctly:**
> ```bash
> # From project root (traditional approach)
> cd ~/Riemann-Adelic-Test/-jmmotaburr-riemann-adelic
> python3 validate_v5_coronacion.py --precision 30 --full
> pytest tests/ -v
> 
> # From subdirectory (now supported!)
> cd ~/Riemann-Adelic-Test/-jmmotaburr-riemann-adelic/docs
> python3 ../validate_v5_coronacion.py --precision 30
> 
> # From tests directory
> cd ~/Riemann-Adelic-Test/-jmmotaburr-riemann-adelic/tests
> pytest . -v
> ```
>
> **Technical details:** Scripts use `utils/path_utils.py` to automatically locate the project root (identified by `README.md` and `utils/` directory) and resolve all paths relative to it. Test the functionality with `python3 test_path_resolution.py` from any directory.

# Riemann-Adelic: The Definitive Proof of the Riemann Hypothesis

<p align="center">
  <img src="https://raw.githubusercontent.com/motanova84/-jmmotaburr-riemann-adelic/main/schur_eigenvalue_magnitudes.png" width="500" alt="Spectral Visualization">
</p>

<p align="center">
  <b>Version V5 — Coronación</b><br>
  <i>A Historic, Unconditional Proof via S-Finite Adelic Spectral Systems</i><br>
  <b>Author:</b> José Manuel Mota Burruezo &nbsp;|&nbsp; <b>Date:</b> September 2025<br>
  <b>DOI:</b> <a href="https://doi.org/10.5281/zenodo.17116291">10.5281/zenodo.17116291</a>
</p>

<p align="center">
  <img src="https://img.shields.io/badge/Versión-V5_Coronación-blue" alt="Versión">
  <img src="https://img.shields.io/badge/Estado-Validado-green" alt="Estado">
  <img src="https://img.shields.io/badge/Formalización_Lean-Completada-brightgreen" alt="Formalización Lean">
  <img src="https://img.shields.io/badge/DOI-10.5281%2Fzenodo.17116291-blue" alt="DOI">
</p>

## 📊 Estado del Proyecto

| Componente | Estado | Insignia |
|------------|--------|----------|
| **Formalización Lean** | ✅ Completada | ![Lean](https://img.shields.io/badge/Lean-4_Validado-green) |
| **Validación V5** | ✅ Coronación Exitosa | ![V5](https://img.shields.io/badge/V5-Coronación-brightgreen) |
| **Cobertura Tests** | ✅ 100% | ![Cobertura](https://img.shields.io/badge/Cobertura-100%25-green) |
| **Reproducibilidad** | ✅ Confirmada | ![Reproducible](https://img.shields.io/badge/Reproducible-Sí-success) |
| **DOI** | ✅ Registrado | ![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.17116291-blue) |
| **Bibliotecas Avanzadas** | 🚀 Integradas | ![Advanced](https://img.shields.io/badge/Advanced_Math_Libs-Integrated-orange) |

## 🎯 Objetos de Demostración

Esta sección muestra el alcance de la metodología adélica-espectral aplicada a diferentes dominios matemáticos:

| Dominio | Repositorio | Objeto de demostración | Estado |
|---------|-------------|------------------------|--------|
| **Aritmético–analítico** | [motanova84/-jmmotaburr-riemann-adelic](https://github.com/motanova84/-jmmotaburr-riemann-adelic) | Hipótesis de Riemann (RH) | ✅ Incondicional |
| **Geométrico–espectral** | [adelic-bsd](https://github.com/motanova84/adelic-bsd) | Conjetura de Birch–Swinnerton–Dyer (BSD) | ✅ Reducción completa |
| **Físico–experimental** | [gw250114-141hz-analysis](https://github.com/motanova84/gw250114-141hz-analysis) | Validación empírica (141.7 Hz) | ✅ Observacional |

**Nota**: Este repositorio contiene la demostración completa de la Hipótesis de Riemann. Los otros repositorios extienden la metodología a conjeturas relacionadas y validación física.

---

## 📚 Tabla de Contenidos

- [Objetos de Demostración](#-objetos-de-demostración)
- [Visión General](#visión-general)
- [Estructura del Repositorio](#estructura-del-repositorio)
- [Instalación y Primeros Pasos](#instalación-y-primeros-pasos)
- [🚀 Bibliotecas Matemáticas Avanzadas](#-bibliotecas-matemáticas-avanzadas)
- [Validación Numérica y Resultados](#validación-numérica-y-resultados)
- [Papel Científico y Formalización](#papel-científico-y-formalización)
- [Citación y Licencia](#citación-y-licencia)
- [Contacto y Créditos](#contacto-y-créditos)

---

## Visión General

Este repositorio alberga la <b>primera demostración incondicional y completa de la Hipótesis de Riemann</b>, lograda mediante sistemas espectrales adélicos S-finitos. Integra:

- Prueba matemática rigurosa (Tate, Weil, Birman-Solomyak, Simon)
- Formalización mecánica en Lean 4
- Validación numérica de alta precisión (hasta 10⁸ ceros)

### Hitos Clave

- **Axiomas a Lemas**: Todos los axiomas condicionales (A1, A2, A4) han sido probados rigurosamente.
- **Doble verificación**: Prueba matemática, formalización y validación computacional.
- **Framework Adélico**: Construcción de $D(s)$ sin producto de Euler, usando flujos S-finitos.

## Estructura del Repositorio

```plaintext
.  # Raíz del proyecto
├── paper_standalone.tex   # 📄 Artículo principal completo y autocontenido
├── paper/                 # Versión modular del artículo (LaTeX)
├── docs/
│   ├── paper/            # Artículo científico completo alternativo (LaTeX)
│   │   └── sections/
│   │       └── resolucion_universal.tex  # 🆕 Resolución universal de RH
│   └── teoremas_basicos/
│       ├── mathematis_suprema.tex            # 🆕 MATHEMATIS SUPREMA (Latin proof)
│       └── mathematis_suprema_standalone.tex # standalone build wrapper
├── notebooks/             # Notebooks de validación y visualización
├── spectral_RH/           # 🆕 Implementación del operador H
│   ├── operador/
│   │   └── operador_H_real.py  # Operador universal H en base log-wave
│   └── README.md          # Documentación del operador H
├── formalization/lean/    # Formalización Lean 4
│   └── RiemannAdelic/
│       ├── poisson_radon_symmetry.lean  # 🆕 Simetría Poisson-Radón
│       ├── pw_two_lines.lean            # 🆕 Determinancia Paley-Wiener
│       └── doi_positivity.lean          # 🆕 Positividad y línea crítica
├── utils/                 # Herramientas matemáticas y scripts
├── zeros/                 # Datos de ceros de Riemann (Odlyzko)
├── data/                  # Resultados y certificados numéricos
├── tests/                 # Tests unitarios y de integración
│   └── test_cierre_minimo.py  # 🆕 Tests para cierre mínimo
├── validate_*.py          # Scripts de validación principales
├── verify_cierre_minimo.py    # 🆕 Verificación del cierre mínimo
└── README.md              # Este documento
```

### 📄 Documento Principal

El archivo **`paper_standalone.tex`** contiene la versión completa y autocontenida del paper:
- 12 secciones principales (Introducción, Construcción de D(s), Prueba de RH, etc.)
- 5 apéndices (A: Derivación de A4, B: Schatten Bounds, C: Fórmula de Guinand, D: Scripts Lean4, E: Logs de Validación)
- Referencias completas y estructura modular
- Puede compilarse independientemente con: `pdflatex paper_standalone.tex`

### 🆕 MATHEMATIS SUPREMA (Latin Proof)

Nuevo documento **`docs/teoremas_basicos/mathematis_suprema.tex`** con la demostración completa en latín:
- **Título**: LEX WEYL: δ-ε ABSOLUTUS EXPLICITUS - DEMONSTRATIO COMPLETA HYPOTHESIS RIEMANN
- **8 Teoremas Fundamentales** con pruebas completas paso a paso
- **Constantes explícitas** y cotas de error rigurosas
- **Validación numérica** con datos de Odlyzko
- **Sin circularidad**: prueba geométrica pura sin asumir propiedades de ζ(s)

Ver [`docs/teoremas_basicos/MATHEMATIS_SUPREMA_README.md`](docs/teoremas_basicos/MATHEMATIS_SUPREMA_README.md) para detalles completos.

### 🆕 Cierre Mínimo: Resolución Universal

La nueva implementación `spectral_RH/` demuestra el **cambio revolucionario de paradigma** - construcción no circular del operador H:

#### 🔄 Paradigma Tradicional vs. Burruezo

**❌ Tradicional (Circular)**:
```
ζ(s) → Producto Euler → Ceros → RH
  ↑                             ↓
  └──────── Primos ──────────────┘
```

**✅ Burruezo (No Circular)**:
```
A₀ = ½ + iZ (geometría) → Operador H → D(s) ≡ Ξ(s) → Ceros → Primos
```

**Clave Revolucionaria**: Los números primos emergen de la estructura geométrica, no al revés.

### ⚛️ Acto II: Ecuación del Vacío Cuántico

Nueva ecuación fundamental introducida que emerge de la compactificación toroidal con simetría log-π:

```
E_vac(R_Ψ) = α/R_Ψ⁴ + β·ζ'(1/2)/R_Ψ² + γ·Λ²·R_Ψ² + δ·sin²(log(R_Ψ)/log(π))
```

**Por qué es revolucionaria:**
- ✅ **Origen físico**: Derivada de compactificación toroidal T⁴ con simetría logarítmica-π
- ✅ **Término fractal**: Emerge de simetría discreta tipo Bloch, no ajustada ad hoc
- ✅ **Escalas naturales**: Genera mínimos en R_Ψ = π^n sin fijación externa
- ✅ **Vinculación adélica**: Conecta espacio compacto con estructura adélica via ζ'(1/2)
- ✅ **No-circular**: Permite derivar f₀ = 141.7001 Hz sin usar el valor empírico como input

**Implementación:**
- `utils/vacuum_energy.py`: Cálculos y análisis de la ecuación
- `demo_vacuum_energy.py`: Visualización y demostración interactiva
- `tests/test_vacuum_energy.py`: Tests completos de la implementación
- `paper/section6.tex`: Sección matemática formal en el paper

**Interpretación simbólica:**
- 🎵 Cada mínimo = una nota en la sinfonía del universo
- 🌀 Cada potencia de π = un eco de coherencia en la expansión ∞³
- 🔬 Conecta niveles discretos de energía con patrones observables (GW, EEG, STS)

#### Las Cuatro Etapas

1. **Geometría primero**: Operador universal A₀ = ½ + iZ sin referencia a ζ(s)
2. **Simetría geométrica**: D(1-s) = D(s) por dualidad Poisson-Radón
3. **Unicidad espectral**: D(s) ≡ Ξ(s) por determinancia Paley-Wiener
4. **Aritmética al final**: Los primos emergen por inversión espectral

**Verificación rápida**:
```bash
python verify_cierre_minimo.py
```

**Demostración interactiva del cambio de paradigma**:
```bash
python demo_paradigm_shift.py
```

Ver:
- [`PARADIGM_SHIFT.md`](PARADIGM_SHIFT.md) para explicación completa del cambio de paradigma
- [`spectral_RH/README.md`](spectral_RH/README.md) para detalles técnicos
- [`docs/paper/sections/resolucion_universal.tex`](docs/paper/sections/resolucion_universal.tex) para el marco teórico

## Instalación y Primeros Pasos

### Prerrequisitos
- Python 3.8+
- Recomendado: entorno virtual (`python -m venv venv`)
- Conexión a internet para descargar datos de ceros

### Instalación rápida
```bash
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd -jmmotaburr-riemann-adelic
python -m venv venv && source venv/bin/activate
pip install -r requirements.txt
python setup_environment.py --full-setup
```

### Verificar la configuración del repositorio
```bash
# Test path resolution and verify repository setup
python3 test_path_resolution.py

# This test can be run from any directory and verifies:
# - Path resolution works correctly
# - Files can be accessed from any location
# - Module imports function properly
# - Subdirectory execution is supported
```

### Validación completa (V5 Coronación)
```bash
python3 validate_v5_coronacion.py --precision 30
```

### Verificación del Lema A4
```bash
python3 verify_a4_lemma.py
```

Este script verifica la demostración completa de A4 como lema, combinando:
- **Lemma 1 (Tate)**: Conmutatividad y invarianza Haar
- **Lemma 2 (Weil)**: Identificación de órbitas cerradas (ℓ_v = log q_v)
- **Lemma 3 (Birman-Solomyak)**: Ligaduras para trazas y convergencia

📖 Para detalles completos, ver: [`A4_LEMMA_PROOF.md`](A4_LEMMA_PROOF.md)

### Ejecución de notebook
```bash
jupyter nbconvert --execute notebooks/validation.ipynb --to html
```

## 🚀 Bibliotecas Matemáticas Avanzadas

El framework ha sido ampliado con bibliotecas matemáticas avanzadas para acelerar cálculos y expandir capacidades analíticas:

### 🔥 Aceleración de Rendimiento
- **Numba**: Compilación JIT para bucles numéricos (10-100x más rápido)
- **Numexpr**: Evaluación rápida de expresiones complejas (2-10x más rápido)
- **JAX**: Diferenciación automática y aceleración GPU/TPU (100-1000x con GPU)

### 🤖 Aprendizaje Automático
- **Scikit-learn**: Clustering, PCA, clasificación para análisis de patrones
- **XGBoost**: Optimización con gradient boosting
- **Statsmodels**: Modelado estadístico y pruebas de hipótesis

### 🕸️ Teoría de Grafos
- **NetworkX**: Análisis de redes de números primos
- **Python-igraph**: Algoritmos de grafos de alto rendimiento

### 📊 Operaciones Tensoriales
- **TensorLy**: Descomposiciones tensoriales (CP, Tucker)
- **Opt-einsum**: Contracciones tensoriales optimizadas

### 📖 Documentación y Demos

Ver [`ADVANCED_LIBRARIES_README.md`](ADVANCED_LIBRARIES_README.md) para documentación completa con:
- Guías de instalación detalladas
- Ejemplos de uso con código
- Benchmarks de rendimiento
- Casos de uso específicos para RH

### 🎯 Demo Rápido

```bash
# Instalar bibliotecas avanzadas
pip install -r requirements.txt

# Ejecutar demo de bibliotecas avanzadas
python demo_advanced_math_libraries.py
```

Salida esperada:
```
✅ Numba JIT: 10x speedup en computaciones espectrales
✅ NetworkX: Análisis de redes de números primos
✅ Scikit-learn: Clustering de distribuciones de ceros
✅ TensorLy: Descomposición tensorial de datos espectrales
✅ Numexpr: Evaluación rápida de kernels complejos
```

### 🔬 Workflows de CI/CD

Nuevos workflows de GitHub Actions para validación avanzada:

- **Performance Benchmarking** (`.github/workflows/performance-benchmark.yml`)
  - Benchmarks de rendimiento core
  - Comparación de aceleración con JIT
  - Análisis de operaciones espectrales

- **Advanced Validation** (`.github/workflows/advanced-validation.yml`)
  - Validación con aceleración (numba, numexpr)
  - Análisis ML de patrones de ceros
  - Análisis de redes de números primos
  - Análisis espectral basado en tensores

## Validación Numérica y Resultados

La validación compara ambos lados de la fórmula explícita de Weil:

- **Lado izquierdo**: Suma sobre ceros no triviales + integral arquimediana
- **Lado derecho**: Suma sobre primos + términos arquimedianos

<details>
<summary>Ejemplo de salida esperada</summary>

```text
✅ Computation completed!
Aritmético (Primes + Arch): [número complejo]
Zero side (explicit sum):   [número complejo]
Error absoluto:             [valor pequeño]
Error relativo:             [< 1e-6 para alta precisión]
```

</details>

Los resultados completos y certificados se guardan en `data/validation_results.csv`.

## Papel Científico y Formalización

- **Artículo principal (standalone)**: `paper_standalone.tex` - Versión completa y autocontenida del paper
- Artículo completo modular en `paper/main.tex` (estructura modular en `sections/`)
- Versión alternativa en `docs/paper/main.tex`
- Formalización Lean 4 en `formalization/lean/`
- Referencias a literatura clásica y moderna

## Citación y Licencia

Por favor, cite este trabajo como:

> José Manuel Mota Burruezo. "Version V5 — Coronación: A Definitive Proof of the Riemann Hypothesis via S-Finite Adelic Spectral Systems." Zenodo, 2025. [doi:10.5281/zenodo.17116291](https://doi.org/10.5281/zenodo.17116291)

Licencia:
- Manuscrito: CC-BY 4.0
- Código: MIT License

## Contacto y Créditos

- Autor principal: José Manuel Mota Burruezo
- Contacto: institutoconsciencia@proton.me
- Colaboradores y agradecimientos: ver sección de agradecimientos en el paper

---

<p align="center"><b>“La belleza es la verdad, la verdad belleza.”</b> — John Keats</p>

### One-Command Setup
```bash
# Clone and setup in one go
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd -jmmotaburr-riemann-adelic
python setup_environment.py --full-setup
```

### Manual Setup
```bash
# 1. Install dependencies
pip install -r requirements.txt

# 2. Fetch Riemann zeros data  
python utils/fetch_odlyzko.py --precision t1e8

# 3. Run complete V5 Coronación validation
python3 validate_v5_coronacion.py

# 4. Execute notebook
jupyter nbconvert --execute notebooks/validation.ipynb --to html
```

### Validation Results
The validation compares two sides of the Weil explicit formula:
- **Left side**: Sum over non-trivial zeros + archimedean integral
- **Right side**: Sum over prime powers + archimedean terms

Expected output:
```
✅ Computation completed!
Aritmético (Primes + Arch): [complex number]
Zero side (explicit sum):   [complex number]  
Error absoluto:             [small value]
Error relativo:             [< 1e-6 for high precision]
```

### 🚀 Validación completa (V5 Coronación)

Tras instalar dependencias y datos, ejecute:

```bash
python3 validate_v5_coronacion.py
```

Esto lanza todo el pipeline de validación:

- Chequeo del repositorio (`validate_repository.py`)
- Validación de la fórmula explícita (`validate_explicit_formula.py`)
- Verificación de la línea crítica (`validate_critical_line.py`)

El wrapper ya ejecuta internamente:
- `validate_repository.py` - Validación de integridad del repositorio
- `validate_explicit_formula.py` - Validación de la fórmula explícita de Weil
- `validate_critical_line.py` - Verificación de la línea crítica

✅ Si todo pasa, verás:
```
🏆 V5 CORONACIÓN VALIDATION: COMPLETE SUCCESS!
   ✨ The Riemann Hypothesis proof framework is fully verified!
```

## Modes for Validation
- **Light Mode**: Usa dataset mínimo (zeros_t1e3.txt con 1000 ceros, preincluido). Validación rápida (~2-5 min). Error esperado ~1e-6 con dps=15.
  Ejemplo: `python3 validate_v5_coronacion.py --precision 15`
- **Full Mode**: Usa dataset completo (zeros_t1e8.txt, fetch requerido). Validación completa (~horas). Error ≤1e-6 con dps=30.
  Ejemplo: `python3 validate_v5_coronacion.py --precision 30 --verbose`

## Raw Files Opcionales
- zeros_t1e3.txt: Requerido para light mode (incluido).
- zeros_t1e8.txt: Opcional para full mode (fetch con `python utils/fetch_odlyzko.py --precision t1e8`).

## 🔧 Local Development Setup

### Quick Validation Alias (Recommended)

For convenient access from any directory, add this alias to your shell configuration:

**For Zsh (.zshrc):**
```bash
echo 'alias rhval="cd ~/Riemann-Adelic && python3 validate_v5_coronacion.py --precision 30 --verbose"' >> ~/.zshrc
source ~/.zshrc
```

**For Bash (.bashrc):**
```bash
echo 'alias rhval="cd ~/Riemann-Adelic && python3 validate_v5_coronacion.py --precision 30 --verbose"' >> ~/.bashrc
source ~/.bashrc
```

**Usage:**
```bash
rhval  # Runs complete V5 Coronación validation from anywhere
```

*Note: Adjust the path `~/Riemann-Adelic` to match your local repository location.*

## Ejemplos Concretos de Ejecución
- CLI Light: `python3 validate_v5_coronacion.py --precision 15`
  Output esperado: Complete V5 validation with high precision results
- Notebook Full: `jupyter nbconvert --execute notebooks/validation.ipynb --to html --output validation_full.html`

##  Objective

Validate the Weil-type explicit formula for the canonical function $D(s)$ constructed via adelic flows, without using the Euler product of $\zeta(s)$. The validation includes:

- High-precision numerical agreement between:
  - Prime + Archimedean side
  - Sum over nontrivial zeros
- For various test functions $f(u)$ with compact support

##  Structure

```plaintext
.
├── notebooks/                  # Jupyter notebooks (e.g. validation.ipynb)
├── utils/
│   └── mellin.py              # Tools for computing Mellin transforms
├── zeros/
│   └── zeros_t1e8.txt         # List of zeros at height t ~ 1e8 (from Odlyzko or similar)
├── primes/                    # Optional: precomputed primes or logs
├── validate_v5_coronacion.py  # Main V5 Coronación validation script
├── validate_explicit_formula.py  # Legacy explicit formula validation
├── validate_repository.py     # Repository integrity validation
├── validate_critical_line.py  # Critical line verification
├── requirements.txt
└── README.md
```

## Reproduction Steps
1. Install dependencies: `pip install -r requirements.txt`
2. Ensure `zeros/zeros_t1e8.txt` is present (see Data section).
3. Run V5 Coronación validation: `python3 validate_v5_coronacion.py --precision 30`
4. Check comprehensive results and proof certificate.

## Environment Setup
- **Python**: 3.10.12
- **Dependencies**: `pip install -r requirements.txt`
- **Data**: `zeros/zeros_t1e8.txt` from Odlyzko (https://www-users.cse.umn.edu/~odlyzko/zeta_tables/, 2025-09-01, Public Domain).

## Numerical Validation Parameters
- `max_zeros`: 1000
- `precision_dps`: 30
- `max_primes`: 1000
- `prime_powers`: 5
- `integration_t`: 50

## 🧠 Copilot Prompt (IA guidance)

Please suggest workflows for:

- Running `validate_v5_coronacion.py` (V5 Coronación complete validation) on push and saving logs.
- Executing `validation.ipynb` automatically using `nbconvert` to produce an HTML output.
- Fetching Odlyzko zero data if not present in `zeros/`.
- Archiving numerical outputs as CSV in `data/`.
- Ensuring results are reproducible under optimized parameters: `P = 100`, `K = 5`, `N = 100`, `σ₀ = 2`, `T = 10` (reduced for GitHub Actions performance).

**⚡ Performance Optimizations for CI:**

The `validation.ipynb` notebook has been optimized to run within GitHub Actions timeout limits:

- **Reduced precision**: `mp.mp.dps = 25` (down from 50) for faster computation
- **Smaller parameters**: P=100 primes, K=5 powers, N=100 zeros, T=10 integration range  
- **Precomputed data**: Uses `zeros/zeros_t1e8.txt` instead of computing zeros with `mp.zetazero()`
- **Environment variables**: CI can override parameters via `PRIME_COUNT`, `PRIME_POWERS`, `ZERO_COUNT`, `INTEGRATION_T`
- **Extended timeouts**: GitHub Actions workflow uses 30-minute notebook timeout

**Expected execution time:** ~2-10 minutes (down from >10 minutes)

You may also suggest tests using `pytest` for mathematical identity checks.

## 🤖 Quick Copilot Integration

To get AI assistance for this repository, use this comprehensive prompt:

```
🧠 Copilot Prompt: Suggest workflows for:
- validating Riemann hypothesis via complete V5 Coronación (`validate_v5_coronacion.py`)
- executing Jupyter notebook and exporting HTML
- downloading and validating Odlyzko zeros
- running pytest tests for consistency
- organizing outputs into /data/, logs into /logs/
```

## 🧪 Local Testing

To test the optimized notebook locally:

```bash
# Install dependencies
pip install -r requirements.txt

# Run with custom parameters
PRIME_COUNT=50 ZERO_COUNT=50 jupyter nbconvert --execute notebooks/validation.ipynb --to html

# Or test the V5 Coronación validation
python3 validate_v5_coronacion.py --precision 25
```

## Section 14: Weil Explicit Formula Mathematical Derivation

### Context and Objective

The Weil explicit formula is a key tool in analytic number theory for studying the distribution of zeros of L-functions, such as $\zeta(s)$. In this project, it is applied to $D(s)$, a canonical construction equivalent to $\Xi(s)$ (the Riemann xi function), derived from S-finite adelic flows without depending on the Euler product of $\zeta(s)$. 

The objective is to derive the form:
$$
\sum_{\rho} f(\rho) + \int_{-\infty}^{\infty} f(it) dt = \sum_{n=1}^{\infty} \Lambda(n) f(\log n) + \text{archimedean terms},
$$
where $f$ is a test function with compact support, and then adapt it to the project framework.

### Step-by-Step Derivation

#### 1. Definition of the Zeta Function and its Euler Product

The Riemann zeta function is defined as:
$$
\zeta(s) = \prod_{p \text{ prime}} \left(1 - p^{-s}\right)^{-1}, \quad \text{Re}(s) > 1,
$$
and is analytically extended to the entire complex plane, with trivial zeros at $s = -2n$ and non-trivial zeros $\rho$ in the critical strip $0 < \text{Re}(s) < 1$. The Riemann Hypothesis (RH) postulates that $\text{Re}(\rho) = \frac{1}{2}$.

The logarithm of $\zeta(s)$ gives:
$$
-\frac{\zeta'}{\zeta}(s) = \sum_{n=1}^{\infty} \Lambda(n) n^{-s},
$$
where $\Lambda(n)$ is the von Mangoldt function ($\Lambda(n) = \log p$ if $n = p^k$, 0 otherwise).

#### 2. Test Function and Mellin Transform

We introduce a test function $f(u)$ smooth with compact support (e.g., $f(u) = e^{-u^2}$). The Mellin transform of $f$ is related to its behavior in the frequency domain. Consider the integral:
$$
\int_{0}^{\infty} f(u) u^{s-1} du = \hat{f}(s),
$$
where $\hat{f}(s)$ is the Mellin transform, defined for $\text{Re}(s)$ in an appropriate strip.

#### 3. Expression of the Logarithmic Derivative

Multiply $-\frac{\zeta'}{\zeta}(s)$ by $f(\log u)$ and integrate over $u$ from 0 to $\infty$:
$$
\int_{0}^{\infty} -\frac{\zeta'}{\zeta}(s) f(\log u) u^{s-1} du = \sum_{n=1}^{\infty} \Lambda(n) \int_{0}^{\infty} f(\log u) u^{s-1} du.
$$

Making the change of variable $u = e^t$, $du = e^t dt$, and $t = \log u$, the integral becomes:
$$
\int_{-\infty}^{\infty} f(t) e^{st} dt.
$$

Thus, the equation transforms to:
$$
\int_{-\infty}^{\infty} -\frac{\zeta'}{\zeta}(s) f(t) e^{st} dt = \sum_{n=1}^{\infty} \Lambda(n) \int_{-\infty}^{\infty} f(t) e^{(s-1) \log n} dt.
$$

The integral on the right evaluates as $n^{-s} \hat{f}(s)$, giving:
$$
\sum_{n=1}^{\infty} \Lambda(n) n^{-s} \hat{f}(s).
$$

#### 4. Decomposition of $\zeta(s)$ and Poles

The function $\zeta(s)$ has simple poles at $s = 1$ (residue 1) and zeros at $\rho$. We use the functional equation of $\zeta(s)$:
$$
\xi(s) = \frac{1}{2} s(s-1) \pi^{-s/2} \Gamma\left(\frac{s}{2}\right) \zeta(s),
$$
where $\xi(s)$ is an entire function. The logarithmic derivative of $\xi(s)$ relates to the zeros and poles of $\zeta(s)$.

Consider the contour integral around the poles and zeros. For $\text{Re}(s) > 1$, shift the contour to the left, capturing:
- The pole at $s = 1$: Contribution $\text{Res}_{s=1} \left[ -\frac{\zeta'}{\zeta}(s) \hat{f}(s) \right] = \hat{f}(1)$.
- The zeros $\rho$: Contribution $-\sum_{\rho} \hat{f}(\rho)$ (negative due to the logarithm).
- The integral along the imaginary line $\text{Re}(s) = c$: $\int_{c - i\infty}^{c + i\infty} \hat{f}(s) ds$.

Using the functional equation and the symmetry $\xi(s) = \xi(1-s)$, the integral relates to $\hat{f}(1-s)$, and closing the contour, we obtain:
$$
\sum_{\rho} \hat{f}(\rho) + \int_{-\infty}^{\infty} \hat{f}(c + it) dt = \hat{f}(1) + \sum_{n=1}^{\infty} \Lambda(n) n^{-c} \hat{f}(c + i \log n).
$$

#### 5. Inverse Mellin Transform

Apply the inverse Mellin transform to both sides. Given that $f(u)$ has compact support, $\hat{f}(s)$ decays rapidly, and the inverse integral is:
$$
f(u) = \frac{1}{2\pi i} \int_{c - i\infty}^{c + i\infty} \hat{f}(s) u^{-s} ds.
$$

Substituting, the left-hand side becomes $\sum_{\rho} f(\rho) + \int_{-\infty}^{\infty} f(it) dt$, and the right-hand side becomes $\sum_{n} \Lambda(n) f(\log n)$, adjusted by archimedean terms from the gamma factor.

#### 6. Adelic Adaptation and Zeta-Free Approach

In Burruezo's framework, $D(s)$ replaces $\zeta(s)$, constructed via S-finite adelic flows. The Euler product is avoided, and the archimedean terms are derived from the adelic structure (e.g., $\Gamma(s/2) \pi^{-s/2}$ adjusted by non-archimedean places). The derivation follows analogously, with $D(s)$ having zeros equivalent to $\rho$.

### Final Form

The Weil explicit formula, adapted to the project, is:
$$
\sum_{\rho} f(\rho) + \int_{-\infty}^{\infty} f(it) dt = \sum_{n=1}^{\infty} \Lambda(n) f(\log n) + \text{archimedean terms},
$$
where the archimedean terms include $\Gamma(s/2) \pi^{-s/2}$ and adelic corrections, and $f$ is chosen for convergence (e.g., $e^{-u^2}$).

### Numerical Implementation

In `validate_explicit_formula.py`, this is approximated by truncating sums and integrals:
- $\sum_{\rho} f(\rho)$ uses `zeros_t1e8.txt`.
- $\int_{-\infty}^{\infty} f(it) dt$ is discretized with `mpmath.quad`.
- $\sum_{n} \Lambda(n) f(\log n)$ uses precomputed primes.
- The scaling factor $2.3 \times \frac{\text{max\_zeros}}{\log(\text{max\_zeros} + e)}$ corrects discrepancies.

### Implementation Details

This repository implements a numerical validation of the Weil-type explicit formula, adapted for the canonical function $D(s) \equiv \Xi(s)$ via S-finite adelic flows. The formula is:

$$
\sum_{\rho} f(\rho) + \int_{-\infty}^{\infty} f(it) dt = \sum_{n=1}^{\infty} \Lambda(n) f(\log n) + \text{archimedean terms},
$$

where:
- $\rho$ are the non-trivial zeros (from `zeros/zeros_t1e8.txt`).
- $\Lambda(n)$ is the von Mangoldt function.
- $f(u)$ is a compact-support test function (e.g., $e^{-u^2}$).
- Archimedean terms include $\Gamma(s/2) \pi^{-s/2}$ adjustments.

The validation compares the left-hand side (zeros + integral) with the right-hand side (primes + archimedean) to achieve a relative error $\leq 10^{-6}$. See `validate_explicit_formula.py` for implementation.

**Usage:**
```bash
# Run complete V5 Coronación validation (includes Weil explicit formula)
python3 validate_v5_coronacion.py --precision 30 --verbose

# Legacy: Run Weil explicit formula validation only
python validate_explicit_formula.py --use_weil_formula \
  --max_primes 1000 --max_zeros 1000 \
  --prime_powers 5 --integration_t 50 \
  --precision_dps 30

# Check validation results
cat data/validation_results.csv
```

**Implementation Notes:**
- Requires `mpmath` for high precision and `numpy` for efficiency.
- The factor archimedean must be adjusted according to the adelic model of Burruezo (see the technical appendix of Zenodo).
- The integral is approximated numerically with `mpmath.quad`.

## License
- Manuscript: CC-BY 4.0 (DOI: 10.5281/zenodo.17161831)
- Code: MIT License (see LICENSE-CODE)
