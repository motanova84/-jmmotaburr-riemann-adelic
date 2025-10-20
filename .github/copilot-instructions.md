# 🤖 Copilot Agent Instructions for -jmmotaburr-riemann-adelic

## QCAL ∞³ Copilot Behavior

### 1️⃣ Mathematical Accuracy & Validation Priority

- **Siempre prioriza exactitud matemática y reproducibilidad.**
- Ejecuta o sugiere scripts de validación (`validate_v5_coronacion.py`, `Evac_Rpsi`) antes de generar código nuevo.
- Valida siempre coherencia antes de sugerir commits usando:
  - `validate_v5_coronacion.py` para validación completa V5 Coronación
  - `Evac_Rpsi_data.csv` para datos de validación espectral
  - Frecuencia base: **141.7001 Hz**
- Mantén consistencia con la ecuación fundamental: **Ψ = I × A_eff² × C^∞**
- Preserva la coherencia QCAL con **C = 244.36**

### 2️⃣ Reference & Citation Integrity

- **Nunca elimines referencias a Zenodo DOI, Lean4 o QCAL-CLOUD.**
- Mantén consistencia con el formato del DOI Zenodo principal: `10.5281/zenodo.17379721`
- Preserva todas las referencias DOI en el archivo `.qcal_beacon`:
  - `doi_infinito`, `doi_pnp`, `doi_goldbach`, `doi_bsd`, `doi_rh_conditional`, `doi_rh_final`
- No modifiques las líneas que contienen: **"C = I × A_eff²"** ni las etiquetas QCAL
- Mantén intactas las referencias a:
  - Instituto de Conciencia Cuántica (ICQ)
  - José Manuel Mota Burruezo Ψ ✧ ∞³
  - ORCID: `0009-0002-1923-0773`

### 3️⃣ Performance Optimization

- **Sugiere mejoras de rendimiento cuando detectes bucles intensivos:**
  - Numba JIT compilation para loops numéricos
  - JAX para diferenciación automática y GPU acceleration
  - CuPy para operaciones matriciales en GPU
- Identifica oportunidades de vectorización con NumPy/SciPy
- Sugiere paralelización cuando sea apropiado (multiprocessing, concurrent.futures)

### 4️⃣ Code Quality & Documentation

- **Añade automáticamente docstrings y anotaciones de tipo en Python:**
  - Usa docstrings en formato Google/NumPy style
  - Incluye type hints (typing module) en todas las funciones
  - Documenta parámetros, retornos y excepciones
- **Al crear un nuevo módulo, vincúlalo en `IMPLEMENTATION_SUMMARY.md`:**
  - Añade entrada descriptiva del nuevo módulo
  - Documenta su propósito y relación con otros componentes
  - Lista los archivos creados o modificados
- Añade comentarios Lean4 o LaTeX si el código es matemático
- Mantén estilo consistente con el resto del código

### 5️⃣ External Dependencies & APIs

- **No uses APIs externas sin confirmación.**
- Prefiere código reproducible sin dependencias innecesarias
- Si una API externa es necesaria:
  - Solicita confirmación explícita del usuario
  - Documenta la razón y alternativas consideradas
  - Añade manejo de errores robusto

### 6️⃣ Testing & CI/CD Integration

- Al cerrar un PR exitoso, comenta:
  > ✅ Validación completada. Coherencia QCAL confirmada.
  
- Tras pasar las pruebas CI, sugiere commit con mensaje:
  > ♾️ QCAL Node evolution complete – validation coherent.

- Ejecuta tests relevantes antes de sugerir commits:
  - `pytest tests/` para tests unitarios
  - Scripts de validación específicos según el área modificada
  - Verifica que todos los tests pasen antes de commit

### 7️⃣ Mathematical Formalization

- Respeta la estructura de formalización Lean4 en `formalization/lean/`
- Mantén consistencia entre implementación Python y formalización Lean4
- Al modificar teoremas o lemas, considera actualizar ambas versiones
- Preserva comentarios matemáticos y referencias a papers

### 8️⃣ Repository Structure

- Ejecuta siempre desde la raíz del proyecto
- No modifiques scripts desde subdirectorios
- Respeta la estructura de carpetas existente:
  - `/tests/` para tests
  - `/formalization/` para Lean4
  - `/utils/` para utilidades
  - `/data/` para datos
  - `/docs/` para documentación

### 9️⃣ Specific File Preservation

- **NUNCA modifiques o elimines:**
  - `.qcal_beacon` (archivo de configuración QCAL)
  - `Evac_Rpsi_data.csv` (datos de validación)
  - PDFs de papers (JMMBRIEMANN.pdf, etc.)
  - Archivos de certificación en `/data/`
- Preserva archivos de configuración:
  - `.github/workflows/*.yml`
  - `pytest.ini`, `.flake8`, `.coveragerc`

### 🔟 Commit Message Standards

- Usa mensajes descriptivos y concisos
- Incluye contexto QCAL cuando sea relevante
- Formato sugerido para commits relacionados con validación:
  ```
  ♾️ [QCAL] <área>: <descripción>
  
  - Cambios específicos
  - Validación: <script usado>
  - Estado: <resultado>
  ```

## Summary

Este repositorio implementa la **prueba definitiva de la Hipótesis de Riemann** mediante sistemas espectrales adélicos S-finitos. El sistema QCAL ∞³ opera a la frecuencia fundamental de 141.7001 Hz y requiere coherencia matemática estricta en todas las modificaciones de código.

**Prioridades:**
1. Exactitud matemática y reproducibilidad
2. Preservación de referencias y DOIs
3. Calidad de código y documentación
4. Validación antes de commits
5. Coherencia QCAL en todo momento
