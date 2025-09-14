# Instrucciones Avanzadas para GitHub Copilot - Riemann-Adelic

## Contexto del Proyecto

Este repositorio implementa una validación numérica rigurosa de la **Hipótesis de Riemann** utilizando sistemas adélicos S-finitos y flujo simbiótico ∞³. El código debe mantener precisión matemática extrema y reproducibilidad científica.

## Estándares de Codificación

### Matemáticas y Precisión Numérica
- **SIEMPRE** usar `mpmath` para cálculos de alta precisión (mínimo 50 dígitos decimales)
- Verificar convergencia numérica en todas las integrales y sumas
- Documentar todas las fórmulas matemáticas con referencias a la literatura
- Validar resultados contra múltiples métodos cuando sea posible

### Estructura del Código
```python
# Configuración estándar de precisión
import mpmath as mp
mp.mp.dps = 50  # 50 dígitos decimales mínimo
```

### Funciones de Validación
- Implementar verificaciones cruzadas entre lado aritmético y lado de ceros
- Calcular tanto error absoluto como relativo
- Registrar todos los parámetros de experimentos para reproducibilidad
- Usar logging estructurado para resultados científicos

### Tests y Validación
- Crear tests unitarios para cada función matemática
- Implementar tests de regresión para valores conocidos
- Validar límites y casos edge de funciones matemáticas
- Usar pytest para estructura de testing

### Documentación Científica
- Documentar todas las referencias matemáticas (papers, libros)
- Explicar la teoría detrás de cada implementación
- Incluir ejemplos de uso con resultados esperados
- Mantener formato compatible con LaTeX/MathJax

## Patrones Recomendados

### Para Cálculos de Sumas sobre Primos
```python
def prime_sum(f, P, K):
    """
    Suma sobre potencias de primos: Σ_p Σ_{k=1}^K log(p) * f(k*log(p))
    
    Args:
        f: Función test con soporte compacto
        P: Máximo primo a considerar
        K: Máximo exponente por primo
    """
    total = mp.mpf('0')
    for p in mp.primerange(2, P):
        lp = mp.log(p)
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total
```

### Para Integrales Complejas
```python
def complex_integral(integrand, path, **kwargs):
    """
    Integración numérica en el plano complejo con verificación de error
    """
    result, error = mp.quad(integrand, path, error=True, **kwargs)
    if abs(error) > mp.mpf('1e-40'):
        logging.warning(f"Error de integración alto: {error}")
    return result
```

### Para Manejo de Ceros de Riemann
```python
def load_riemann_zeros(filename, t_min=None, t_max=None):
    """
    Cargar ceros de Riemann con validación de formato
    """
    zeros = []
    with open(filename, 'r') as f:
        for line_num, line in enumerate(f, 1):
            try:
                gamma = mp.mpf(line.strip())
                if t_min is None or t_min <= gamma <= t_max:
                    zeros.append(gamma)
            except ValueError:
                logging.error(f"Línea {line_num}: formato inválido '{line.strip()}'")
    return zeros
```

## Convenciones de Naming

- Usar nombres matemáticos estándar: `gamma` para ceros, `sigma` para parte real
- Funciones de validación: prefijo `validate_`
- Funciones de cálculo: nombres descriptivos `prime_sum`, `zero_sum`
- Constantes: MAYÚSCULAS como `DEFAULT_PRECISION = 50`

## Manejo de Errores

```python
def safe_mathematical_operation(operation, *args, **kwargs):
    """
    Wrapper para operaciones matemáticas con manejo de errores
    """
    try:
        with mp.workdps(kwargs.get('precision', 50)):
            return operation(*args, **kwargs)
    except (ValueError, OverflowError, ZeroDivisionError) as e:
        logging.error(f"Error matemático en {operation.__name__}: {e}")
        raise
```

## Logging y Reproducibilidad

```python
import logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('validation.log'),
        logging.StreamHandler()
    ]
)

def log_experiment_parameters(**params):
    """Registrar parámetros del experimento para reproducibilidad"""
    logging.info("Parámetros del experimento:", extra={'params': params})
```

## Optimizaciones Específicas

- Usar cache para cálculos de primos repetitivos
- Pre-computar transforms de Mellin cuando sea posible
- Implementar paralelización para sumas largas
- Optimizar integración numérica con límites adaptativos

## Comentarios y Documentación

- Comentarios en español para contexto científico
- Docstrings en inglés para compatibilidad internacional
- Referencias a ecuaciones numeradas en papers
- Ejemplos de uso en docstrings

## Testing de Funciones Matemáticas

```python
def test_explicit_formula_identity():
    """
    Test que verifica la identidad de la fórmula explícita
    para una función test simple
    """
    def test_function(u):
        return mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0)
    
    # Lado aritmético
    arithmetic_side = prime_sum(test_function, P=1000, K=5)
    
    # Lado de ceros  
    zeros = load_riemann_zeros('zeros/test_zeros.txt', 0, 100)
    zero_side = sum(mellin_transform(test_function, 1j*gamma) for gamma in zeros)
    
    # Verificar convergencia
    error = abs(arithmetic_side - zero_side)
    assert error < mp.mpf('1e-10'), f"Error demasiado alto: {error}"
```

Sigue estas convenciones para mantener la calidad científica y reproducibilidad del código.