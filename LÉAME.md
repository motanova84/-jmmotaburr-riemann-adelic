# Riemann-Adelic

Este repositorio contiene código de validación numérica para el artículo:

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Final Conditional Version V4.1)**  
Autor: José Manuel Mota Burruezo  
Fecha: 13 de septiembre, 2025  
DOI: [10.5281/zenodo.17161831](https://doi.org/10.5281/zenodo.17161831)

## 📋 Marco Teórico

**Importante**: Este artículo es condicional bajo axiomas S-finitos:
- **A1**: Flujo escala finito
- **A2**: Simetría 
- **A4**: Regularidad espectral

## 📖 Estado Actual

Desde marco condicional → Hacia prueba incondicional (hito V5 Coronación).

## 🚀 Inicio Rápido

### Prerrequisitos
- Python 3.8+ 
- Conexión a internet (para descargar datos de ceros de Riemann)

### Configuración con Un Comando
```bash
# Clonar y configurar en uno
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd -jmmotaburr-riemann-adelic
python setup_environment.py --full-setup
```

### Configuración Manual
```bash
# 1. Instalar dependencias
pip install -r requirements.txt

# 2. Obtener datos de ceros de Riemann  
python utils/fetch_odlyzko.py --precision t1e8

# 3. Ejecutar validación rápida
python validar_v5_coronacion.py

# 4. Ejecutar notebook
jupyter nbconvert --execute notebooks/validation.ipynb --to html
```

### Resultados de Validación
La validación compara dos lados de la fórmula explícita de Weil:
- **Lado izquierdo**: Suma sobre ceros no triviales + integral arquimediana
- **Lado derecho**: Suma sobre potencias de primos + términos arquimedianos

Salida esperada:
```
✅ Cálculo completado!
Aritmético (Primos + Arch): [número complejo]
Lado de ceros (suma explícita): [número complejo]  
Error absoluto:             [valor pequeño]
Error relativo:             [< 1e-6 para alta precisión]
```

## Modos para Validación
- **Modo Ligero**: Usa dataset mínimo (zeros_t1e3.txt con 1000 ceros, preincluido). Validación rápida (~2-5 min). Error esperado ~1e-6 con dps=15.
  Ejemplo: `python validar_v5_coronacion.py`
- **Modo Completo**: Usa dataset completo (zeros_t1e8.txt, fetch requerido). Validación completa (~horas). Error ≤1e-6 con dps=30.
  Ejemplo: `python validar_v5_coronacion.py --precision 50`

## Ejemplos Concretos de Ejecución
- CLI: `python validar_v5_coronacion.py --verbose`
  Output esperado: Error Relativo ~1e-6, guardado en data/validation_results.csv.
- Notebook Completo: `jupyter nbconvert --execute notebooks/validation.ipynb --to html --output validation_full.html`

## Objetivo

Validar la fórmula explícita tipo Weil para la función canónica $D(s)$ construida vía flujos adélicos, sin usar el producto de Euler de $\zeta(s)$. La validación incluye:

- Acuerdo numérico de alta precisión entre:
  - Lado de primos + arquimediano
  - Suma sobre ceros no triviales
- Para varias funciones de prueba $f(u)$ con soporte compacto

## Estructura

```plaintext
.
├── notebooks/                  # Jupyter notebooks (e.g. validation.ipynb)
├── utils/
│   └── mellin.py              # Herramientas para calcular transformadas de Mellin
├── zeros/
│   └── zeros_t1e8.txt         # Lista de ceros en altura t ~ 1e8 (de Odlyzko o similar)
├── primes/                    # Opcional: primos precomputados o logs
├── validar_v5_coronacion.py   # Script principal de validación CLI
├── requirements.txt
└── README.md
```

## Pasos de Reproducción
1. Instalar dependencias: `pip install -r requirements.txt`
2. Asegurar que `zeros/zeros_t1e8.txt` esté presente (ver sección Data).
3. Ejecutar validación: `python validar_v5_coronacion.py`
4. Verificar resultados en `data/validation_results.csv`.

## Configuración del Entorno
- **Python**: 3.10.12
- **Dependencias**: `pip install -r requirements.txt`
- **Datos**: `zeros/zeros_t1e8.txt` de Odlyzko (https://www-users.cse.umn.edu/~odlyzko/zeta_tables/, 2025-09-01, Dominio Público).

## Parámetros de Validación Numérica
- `max_zeros`: 1000
- `precision_dps`: 30
- `max_primes`: 1000
- `prime_powers`: 5
- `integration_t`: 50

## 🧠 Prompt de Copilot (guía IA)

Por favor sugiere flujos de trabajo para:

- Ejecutar `python validar_v5_coronacion.py` en push y guardar logs.
- Ejecutar `validation.ipynb` automáticamente usando `nbconvert` para producir salida HTML.
- Obtener datos de ceros de Odlyzko si no están presentes en `zeros/`.
- Archivar salidas numéricas como CSV en `data/`.
- Asegurar que los resultados sean reproducibles bajo parámetros optimizados: `P = 100`, `K = 5`, `N = 100`, `σ₀ = 2`, `T = 10` (reducido para rendimiento de GitHub Actions).

## 🤖 Integración Rápida de Copilot

Para obtener asistencia de IA para este repositorio, usa este prompt integral:

```
🧠 Prompt de Copilot: Sugiere flujos de trabajo para:
- validar fórmula explícita de Riemann vía `python validar_v5_coronacion.py`
- ejecutar notebook Jupyter y exportar HTML
- descargar y validar ceros de Odlyzko
- ejecutar pruebas pytest para consistencia
- organizar salidas en /data/, logs en /logs/
```

## 🧪 Pruebas Locales

Para probar el notebook optimizado localmente:

```bash
# Instalar dependencias
pip install -r requirements.txt

# Ejecutar con parámetros personalizados
PRIME_COUNT=50 ZERO_COUNT=50 jupyter nbconvert --execute notebooks/validation.ipynb --to html

# O probar la validación CLI
python validar_v5_coronacion.py
```

## Implementación

Este repositorio implementa una validación numérica de la fórmula explícita tipo Weil, adaptada para la función canónica $D(s) \equiv \Xi(s)$ vía flujos adélicos S-finitos. La fórmula es:

$$
\sum_{\rho} f(\rho) + \int_{-\infty}^{\infty} f(it) dt = \sum_{n=1}^{\infty} \Lambda(n) f(\log n) + \text{términos arquimedianos},
$$

donde:
- $\rho$ son los ceros no triviales (de `zeros/zeros_t1e8.txt`).
- $\Lambda(n)$ es la función de von Mangoldt.
- $f(u)$ es una función de prueba de soporte compacto (ej., $e^{-u^2}$).
- Los términos arquimedianos incluyen ajustes de $\Gamma(s/2) \pi^{-s/2}$.

La validación compara el lado izquierdo (ceros + integral) con el lado derecho (primos + arquimediano) para lograr un error relativo $\leq 10^{-6}$. Usa `python validar_v5_coronacion.py` para la implementación.

**Uso:**
```bash
# Ejecutar validación
python validar_v5_coronacion.py

# Ejecutar con alta precisión
python validar_v5_coronacion.py --precision 50

# Ejecutar con salida detallada
python validar_v5_coronacion.py --verbose

# Guardar certificado de prueba
python validar_v5_coronacion.py --save-certificate
```

**Notas de Implementación:**
- Requiere `mpmath` para alta precisión y `numpy` para eficiencia.
- El factor arquimediano debe ajustarse según el modelo adélico de Burruezo (ver apéndice técnico de Zenodo).
- La integral se aproxima numéricamente con `mpmath.quad`.

## Licencia
- Manuscrito: CC-BY 4.0 (DOI: 10.5281/zenodo.17161831)
- Código: Licencia MIT (ver LICENSE-CODE)