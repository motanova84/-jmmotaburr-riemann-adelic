# Makefile for Riemann-Adelic Repository
# Main target for validation

.PHONY: validar test clean setup help

# Default target
validar:
	python validar_v5_coronacion.py

# Alternative validation targets
validar-verbose:
	python validar_v5_coronacion.py --verbose

validar-precision:
	python validar_v5_coronacion.py --precision 50

validar-certificate:
	python validar_v5_coronacion.py --save-certificate

# Setup environment
setup:
	pip install -r requirements.txt
	python setup_environment.py --full-setup

# Run tests
test:
	python -m pytest tests/ -v

# Clean generated files
clean:
	rm -rf data/*.csv
	rm -rf logs/*.log
	rm -rf docs/*.html
	find . -name "*.pyc" -delete
	find . -name "__pycache__" -delete

# Build paper (if LaTeX is available)
paper:
	cd docs/paper && make

# Help target
help:
	@echo "Available targets:"
	@echo "  validar           - Run main validation (default)"
	@echo "  validar-verbose   - Run validation with detailed output"
	@echo "  validar-precision - Run validation with high precision"
	@echo "  validar-certificate - Run validation and save proof certificate"
	@echo "  setup             - Install dependencies and setup environment"
	@echo "  test              - Run test suite"
	@echo "  clean             - Clean generated files"
	@echo "  paper             - Build LaTeX paper (requires LaTeX)"
	@echo "  help              - Show this help message"