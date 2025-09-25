# Changelog

## V5 Coronación — 25 Sept 2025
- Introducción del bloque formal de localización crítica
- Creación de CHANGELOG y estructura de formalización
- Consolidación de teoremas en docs/teoremas_basicos/
- **NUEVO**: Añadida sección del teorema de Suorema con Riema completo (Fórmula Explícita)
- Repositorio elevado a prueba formal en construcción

## [Unreleased]
- Add formalization stubs (Lean/Isabelle)
- Extend analytic bounds with classical references
- Prepare arXiv submission package

## [2025-09-25]
### Added
- `docs/teoremas_basicos/*.tex`: formal theorem scaffolds (rigidez_arquimediana.tex, unicidad_paley_wiener.tex, de_branges.tex, axiomas_a_lemas.tex, factor_arquimediano.tex, localizacion_ceros.tex)
- **NEW**: `formula_explicita_suorema.tex`: Complete explicit formula theorem (Teorema de Suorema)
- `paper/`: LaTeX structure with main.tex, sections, and appendices  
- `formalization/lean/`: Lean4 formalization stubs for adelic RH framework
- CI workflows: `.github/workflows/comprehensive-ci.yml`, `.github/workflows/critical-line-verification.yml`, `.github/workflows/latex-and-proof.yml`
- Test suite: `tests/test_validation.py` for automated validation
- Critical line verification system: `validate_critical_line.py`, `utils/critical_line_checker.py`

### Improved
- Numerical validation scripts (`validate_explicit_formula.py` with multiple test functions)
- Documentation (`README.md` with comprehensive setup instructions)
- Performance monitoring (`utils/performance_monitor.py`)
- Data fetching utilities (`utils/fetch_odlyzko.py`, `utils/checksum_zeros.py`)

### Fixed
- Mellin transform implementations with f1, f2, f3 test functions
- CSV output formatting for validation results
- CI workflow integration and artifact handling