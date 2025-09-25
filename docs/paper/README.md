# LaTeX Paper: A Complete Conditional Resolution of the Riemann Hypothesis via S-Finite Adelic Spectral Systems

## Overview

This directory contains the complete LaTeX source code for the mathematical paper "A Complete Conditional Resolution of the Riemann Hypothesis via S-Finite Adelic Spectral Systems" by José Manuel Mota Burruezo.

## File Structure

- `main.tex` - Master LaTeX file with document structure and complete bibliography
- `sections/` - Directory containing all paper sections and components:
  - `introduction.tex` - Introduction and motivation
  - `axiomas_a_lemas.tex` - Axiomatic Scale Flow and Spectral System  
  - `rigidez_arquimediana.tex` - Archimedean Rigidity theorem
  - `unicidad_paley_wiener.tex` - Paley-Wiener Uniqueness results
  - `de_branges.tex` - de Branges Framework application
  - `factor_arquimediano.tex` - Archimedean Factor analysis
  - `localizacion_ceros.tex` - Critical Line Localization (main result)
  - `conclusion.tex` - Conclusions and future work
  - `appendix_traces.tex` - Trace-Class Convergence proofs
  - `appendix_numerical.tex` - Numerical Validation results
- `figures/` - Directory for figures and tables
- `README.md` - This file with building instructions

## Quick Start

To build the complete RH paper:

```bash
cd docs/paper
pdflatex main.tex
pdflatex main.tex  # Run twice for cross-references and table of contents
```

## Compilation Instructions

### Standard LaTeX compilation:
```bash
pdflatex main.tex
pdflatex main.tex  # Second run resolves cross-references
```

### Alternative Compilation Methods

- **Using latexmk (recommended):**
  ```bash
  latexmk -pdf main.tex
  ```

- **Using make (if Makefile exists):**
  ```bash
  make
  ```

- **Using Overleaf:** Upload all `.tex` files and compile online

- **Using VS Code with LaTeX Workshop:** Open `main.tex` and use the LaTeX Workshop extension

## Package Dependencies

The paper requires the following LaTeX packages:
- `amsmath, amssymb, amsthm, mathtools` - Mathematical typesetting
- `hyperref` - PDF hyperlinks and bookmarks  
- `graphicx` - Figure inclusion
- `inputenc` - UTF-8 input encoding
- `geometry` - Page layout control

Most modern LaTeX distributions include these packages by default.

## Repository Integration

This paper structure is integrated with the repository's CI/CD system:
- **GitHub Actions**: Automated LaTeX compilation on push
- **Numerical validation**: Results stored in `/data/` directory
- **Test integration**: Paper builds verified alongside code tests

## Theorem Scaffolds

The paper incorporates formal theorem scaffolds covering:
- S-finite adelic spectral system axioms
- Archimedean rigidity and uniqueness results  
- de Branges theory application to RH
- Critical line localization via dual proof methods
- Complete trace-class convergence analysis

## Output

Successful compilation generates:
- `main.pdf` - The complete paper with all sections
- Auxiliary files (`.aux`, `.log`, `.out`, etc.) - automatically managed

## Troubleshooting

- **Missing packages:** Install via your LaTeX distribution (e.g., `tlmgr install packagename` for TeX Live)
- **Compilation errors:** Check the `.log` file for detailed error messages
- **Missing sections:** Ensure all `.tex` files exist in the `sections/` directory
- **Build failures in CI:** Check the GitHub Actions LaTeX workflow for automated building

## License

This work is licensed under CC-BY 4.0. See repository `LICENSE` file for details.

## Contact

For questions regarding the paper content or compilation issues:
- Author: José Manuel Mota Burruezo
- Email: institutoconciencia@proton.me
- GitHub: https://github.com/motanova84/-jmmotaburr-riemann-adelic
- Zenodo DOI: 10.5281/zenodo.17116291