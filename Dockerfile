# Dockerfile mínimo para reproducibilidad simbiótica
FROM python:3.12-slim

WORKDIR /app

# Instalar dependencias del sistema necesarias para computación científica
RUN apt-get update && apt-get install -y \
    gcc \
    g++ \
    make \
    pandoc \
    && rm -rf /var/lib/apt/lists/*

# Copiar requirements y código
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .

# Crear directorios necesarios
RUN mkdir -p zeros docs data tests

# Exponer puerto para Jupyter
EXPOSE 8888

# Comando por defecto: ejecutar validación
CMD ["python", "validate_explicit_formula.py"]