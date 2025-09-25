# Changelog

## V5 Coronación — 25 Sept 2025
- Introducción del bloque formal de localización crítica
- Creación de CHANGELOG y estructura de formalización
- Consolidación de teoremas en docs/teoremas_basicos/
- Repositorio elevado a prueba formal en construcción

## [Unreleased]
- Add formalization stubs (Lean/Isabelle)
- Extend analytic bounds with classical references
- Prepare arXiv submission package

## [2025-09-26] - V5 Wrapper and Python3 Compatibility
### Added
- `validar_v5_coronacion.py`: Universal wrapper script with proper shebang for both `python3 validar_v5_coronacion.py` and `./validar_v5_coronacion.py` execution modes
- Explicit note in README Quick Start section about using python3 for compatibility
### Fixed
- Updated all README.md python command examples to use python3 instead of python to avoid 'python: command not found' errors on systems where python is not linked

## [2025-09-25]
### Added
- `docs/teoremas_basicos/*.tex`: formal theorem scaffolds (rigidez_arquimediana.tex, unicidad_paley_wiener.tex, de_branges.tex, axiomas_a_lemas.tex, factor_arquimediano.tex, localizacion_ceros.tex)
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