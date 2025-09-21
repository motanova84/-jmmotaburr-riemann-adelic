FROM python:3.12-slim
WORKDIR /app
COPY requirements.txt .
RUN pip install --trusted-host pypi.org --trusted-host pypi.python.org --trusted-host files.pythonhosted.org --no-cache-dir -r requirements.txt
COPY . .
CMD ["python", "validate_explicit_formula.py", "--max_primes", "100", "--max_zeros", "200"]