# V5 Coronación - Dockerfile for Riemann Hypothesis Proof Validation
FROM python:3.10-slim

# Set working directory
WORKDIR /app

# Copy requirements first for better caching
COPY requirements.txt .

# Install Python dependencies with trusted hosts
RUN pip install --no-cache-dir --trusted-host pypi.org --trusted-host pypi.python.org --trusted-host files.pythonhosted.org -r requirements.txt

# Copy the entire project
COPY . .

# Create data directory if it doesn't exist
RUN mkdir -p data logs

# Set executable permissions for scripts  
RUN chmod +x *.py

# Set Python path
ENV PYTHONPATH=/app

# Default command: run V5 Coronación validation with high precision
CMD ["python3", "validate_v5_coronacion.py", "--precision", "30", "--verbose", "--save-certificate"]

# Alternative commands (can be overridden):
# docker run rh-proof python3 validate_v5_coronacion.py --precision 15
# docker run rh-proof python3 validate_explicit_formula.py --use_weil_formula
# docker run rh-proof python3 validate_critical_line.py --generate-certificate