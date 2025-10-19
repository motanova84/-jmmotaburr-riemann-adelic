# Guía de Contribución

¡Gracias por tu interés en contribuir al proyecto Riemann-Adelic! Este documento proporciona directrices para asegurar que las contribuciones sean consistentes y de alta calidad.

## Tabla de Contenidos

- [Código de Conducta](#código-de-conducta)
- [Cómo Contribuir](#cómo-contribuir)
- [Configuración del Entorno de Desarrollo](#configuración-del-entorno-de-desarrollo)
- [Flujo de Trabajo](#flujo-de-trabajo)
- [Estándares de Código](#estándares-de-código)
- [Tests y Validación](#tests-y-validación)
- [Metadatos y Artefactos Formales](#metadatos-y-artefactos-formales)
- [Documentación](#documentación)

## Código de Conducta

Al participar en este proyecto, te comprometes a mantener un ambiente respetuoso y colaborativo. Por favor, trata a todos los colaboradores con cortesía y profesionalismo.

## Cómo Contribuir

### Reportar Bugs

Si encuentras un error:
1. Busca en los [issues existentes](https://github.com/motanova84/-jmmotaburr-riemann-adelic/issues) para evitar duplicados
2. Si el bug no ha sido reportado, abre un nuevo issue con:
   - Descripción clara del problema
   - Pasos para reproducirlo
   - Comportamiento esperado vs. comportamiento actual
   - Versión de Python y dependencias relevantes

### Proponer Mejoras

Para proponer nuevas características o mejoras:
1. Abre un issue describiendo la propuesta
2. Explica el caso de uso y los beneficios
3. Espera retroalimentación antes de implementar

### Pull Requests

1. Haz fork del repositorio
2. Crea una rama desde `main` con un nombre descriptivo: `feature/nueva-funcionalidad` o `fix/correccion-bug`
3. Implementa tus cambios siguiendo los estándares del proyecto
4. Asegúrate de que todos los tests pasen
5. Actualiza la documentación si es necesario
6. Envía el PR con una descripción clara de los cambios

## Configuración del Entorno de Desarrollo

### Requisitos Previos

- Python 3.10 o superior
- Git
- (Opcional) Lean 4 para trabajar con formalizaciones

### Instalación

```bash
# Clonar el repositorio
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd -jmmotaburr-riemann-adelic

# Crear entorno virtual (recomendado)
python -m venv venv
source venv/bin/activate  # En Windows: venv\Scripts\activate

# Instalar dependencias
python -m pip install --upgrade pip
pip install -r requirements.txt

# Instalar pre-commit hooks
pip install pre-commit
pre-commit install
```

## Flujo de Trabajo

1. **Crear rama**: `git checkout -b tipo/descripcion`
   - Tipos: `feature`, `fix`, `docs`, `chore`, `refactor`, `test`
   
2. **Realizar cambios**: Implementa tus modificaciones siguiendo los estándares

3. **Ejecutar checks localmente**:
   ```bash
   # Formatear código
   black .
   isort .
   
   # Verificar estilo
   flake8 .
   
   # Ejecutar tests
   pytest -q
   
   # Validar metadatos (si aplica)
   python tools/verify_metadata.py schema/metadata_example.jsonld
   ```

4. **Commit**: 
   ```bash
   git add .
   git commit -m "tipo: descripción breve del cambio"
   ```
   
   Formato de mensajes de commit:
   - `feat:` nueva funcionalidad
   - `fix:` corrección de bug
   - `docs:` cambios en documentación
   - `chore:` tareas de mantenimiento
   - `test:` añadir o modificar tests
   - `refactor:` refactorización de código

5. **Push y PR**: 
   ```bash
   git push origin tipo/descripcion
   ```
   Luego abre un Pull Request en GitHub

## Estándares de Código

### Python

- **Formateo**: Usa `black` con longitud de línea 120
- **Imports**: Organiza con `isort` (perfil black)
- **Estilo**: Sigue PEP 8 con las siguientes excepciones en `.flake8`:
  - `E203`: Espacios antes de ':'
  - `W503`: Salto de línea antes de operador binario
  - `E501`: Línea demasiado larga (manejado por black)
- **Type hints**: Usa anotaciones de tipo cuando sea posible
- **Docstrings**: Documenta funciones y clases con docstrings descriptivos

### Lean

- Sigue las convenciones de Mathlib cuando sea aplicable
- Usa nombres descriptivos en español o inglés de forma consistente
- Documenta teoremas y definiciones importantes

## Tests y Validación

### Escribir Tests

- Coloca los tests en el directorio `tests/`
- Nombra los archivos como `test_*.py`
- Usa `pytest` para escribir tests
- Busca una cobertura > 80%

Ejemplo:
```python
import pytest
from my_module import my_function

def test_my_function():
    """Test que verifica el comportamiento esperado"""
    result = my_function(input_data)
    assert result == expected_output
```

### Ejecutar Tests

```bash
# Todos los tests
pytest tests/ -v

# Un archivo específico
pytest tests/test_example.py -v

# Con cobertura
pytest tests/ --cov=. --cov-report=html
```

### CI/CD

El pipeline de CI ejecuta automáticamente:
- Linters (black, flake8, isort)
- Tests con pytest
- Validación de metadatos
- Verificación de conversión de artefactos formales

Asegúrate de que todos los checks pasen antes de solicitar revisión.

## Metadatos y Artefactos Formales

### Estructura de Metadatos

Los artefactos formales (formalizaciones Lean, pruebas, etc.) deben incluir metadatos en formato JSON-LD:

```json
{
  "@context": "https://schema.org/",
  "@type": "SoftwareSourceCode",
  "@id": "unique-identifier",
  "dc:title": "Título del artefacto",
  "dc:creator": "Autor",
  "dc:date": "2025-10-19",
  "format": "text/x-lean4",
  "origin": "source-system",
  "kernel": "lean4",
  "checksum": "sha256:..."
}
```

### Validación

Antes de hacer commit de metadatos:
```bash
python tools/verify_metadata.py schema/metadata_example.jsonld
```

Campos obligatorios:
- `@id`: Identificador único
- `dc:title`: Título descriptivo
- `dc:creator`: Autor o sistema de origen
- `format`: Formato del archivo
- `origin`: Sistema o proyecto de origen
- `kernel`: Sistema de verificación (e.g., lean4, coq, isabelle)
- `checksum`: Hash del contenido para integridad

### Convertidores

Si añades un nuevo formato de artefacto formal:
1. Crea un convertidor en `tools/convert_<formato>.py`
2. Implementa la función principal de conversión
3. Añade tests en `tests/test_convert_<formato>.py`
4. Actualiza la documentación

## Documentación

- Mantén el README.md actualizado
- Documenta cambios significativos en CHANGELOG.md
- Añade docstrings a funciones y clases públicas
- Actualiza los archivos de documentación en `docs/` si aplica

### Generar Documentación

```bash
# Si usas Sphinx u otra herramienta de documentación
cd docs/
make html
```

## Preguntas o Ayuda

Si tienes dudas:
- Abre un issue con la etiqueta `question`
- Contacta al mantenedor: @motanova84
- Revisa la documentación existente en `docs/`

## Licencia

Al contribuir, aceptas que tus contribuciones se licencien bajo la misma licencia del proyecto. Consulta el archivo LICENSE para más detalles.

---

¡Gracias por contribuir al avance de la investigación matemática y la verificación formal!
