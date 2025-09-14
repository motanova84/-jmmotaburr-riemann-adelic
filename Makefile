# Makefile para ejecución validación, test y notebook
.PHONY: help install validate test notebook clean docker-build docker-run docs

# Variables
PYTHON := python
PIP := pip
JUPYTER := jupyter
DOCKER := docker

help: ## Mostrar esta ayuda
	@echo "Comandos disponibles para validación simbiótica ∞³:"
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-15s\033[0m %s\n", $$1, $$2}'

install: ## Instalar dependencias
	$(PIP) install -r requirements.txt

fetch-zeros: ## Descargar ceros de Riemann desde Odlyzko
	$(PYTHON) utils/fetch_odlyzko.py

validate: ## Ejecutar validación numérica completa
	@echo "🧮 Ejecutando validación simbiótica..."
	$(PYTHON) validate_explicit_formula.py
	@echo "✅ Validación completada"

validate-by-height: ## Validar por altura específica (uso: make validate-by-height HEIGHT=14.134)
	$(PYTHON) validate_by_height.py $(HEIGHT)

test: ## Ejecutar tests automáticos
	@echo "🧪 Ejecutando tests..."
	$(PYTHON) -m pytest tests/ -v
	@echo "✅ Tests completados"

notebook: ## Iniciar Jupyter notebook
	@echo "📓 Iniciando Jupyter notebook..."
	$(JUPYTER) notebook notebooks/

notebook-run: ## Ejecutar notebook de validación
	@echo "🏃 Ejecutando notebook de validación..."
	$(JUPYTER) nbconvert --to notebook --execute notebooks/validation.ipynb
	@echo "✅ Notebook ejecutado"

docs: ## Generar documentación HTML
	@echo "📚 Generando documentación..."
	mkdir -p docs
	pandoc README.md -o docs/README.html --standalone --css=https://cdn.jsdelivr.net/gh/sindresorhus/github-markdown-css@4/github-markdown.css
	@echo "✅ Documentación generada en docs/"

docker-build: ## Construir imagen Docker
	$(DOCKER) build -t riemann-adelic:latest .

docker-run: ## Ejecutar container Docker
	$(DOCKER) run --rm -it -p 8888:8888 riemann-adelic:latest

docker-notebook: ## Ejecutar Jupyter en Docker
	$(DOCKER) run --rm -it -p 8888:8888 riemann-adelic:latest jupyter notebook --ip=0.0.0.0 --no-browser --allow-root

clean: ## Limpiar archivos temporales
	@echo "🧹 Limpiando archivos temporales..."
	find . -type f -name "*.pyc" -delete
	find . -type d -name "__pycache__" -exec rm -rf {} +
	find . -type f -name "*.log" -delete
	rm -rf .pytest_cache/
	@echo "✅ Limpieza completada"

all: install fetch-zeros validate test ## Ejecutar instalación, descarga de ceros, validación y tests

# Target para CI/CD
ci: install test validate ## Pipeline completo para integración continua