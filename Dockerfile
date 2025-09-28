# Dockerfile for Riemann-Adelic: Reproducible Mathematical Environment
# This container ensures exact reproducibility of Riemann Hypothesis validation results
# across different systems and time periods.

FROM python:3.12.3-slim-bookworm

LABEL maintainer="José Manuel Mota Burruezo <motanova84@example.com>"
LABEL description="Reproducible Riemann Hypothesis Validation Environment"
LABEL version="1.0.0"
LABEL institute="Instituto Conciencia Cuántica (ICQ)"

# Set environment variables for reproducibility
ENV PYTHONUNBUFFERED=1
ENV PYTHONDONTWRITEBYTECODE=1
ENV PIP_DISABLE_PIP_VERSION_CHECK=1
ENV PIP_NO_CACHE_DIR=1

# Set fixed locale
ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8

# Install system dependencies with fixed versions where possible
RUN apt-get update && apt-get install -y --no-install-recommends \
    git=1:2.39.2-1.1 \
    gcc=4:12.2.0-3 \
    g++=4:12.2.0-3 \
    make=4.3-4.1 \
    libgmp-dev=2:6.2.1+dfsg1-1.1 \
    libmpfr-dev=4.2.0-1 \
    libmpc-dev=1.3.1-1 \
    libffi-dev=3.4.4-1 \
    libssl-dev=3.0.11-1~deb12u2 \
    && rm -rf /var/lib/apt/lists/*

# Create application directory
WORKDIR /app

# Copy requirements first for better Docker layer caching
COPY requirements.txt .

# Install Python dependencies with fixed versions
RUN pip install --no-cache-dir -r requirements.txt

# Install additional dependencies for containerized environment
RUN pip install --no-cache-dir \
    jupyterlab==4.2.5 \
    ipython==8.25.0

# Copy application code
COPY . .

# Create necessary directories
RUN mkdir -p data logs zeros notebooks

# Set proper permissions
RUN chmod +x *.py
RUN chmod +x *.sh

# Create non-root user for security
RUN groupadd -r riemann && useradd -r -g riemann -d /app -s /bin/bash riemann
RUN chown -R riemann:riemann /app

# Switch to non-root user
USER riemann

# Set up Python path
ENV PYTHONPATH=/app:/app/utils

# Health check to verify mathematical environment
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD python -c "import mpmath; import numpy; import sympy; print('OK')" || exit 1

# Default command - run validation
CMD ["python", "validate_v5_coronacion.py", "--precision", "25", "--verbose"]

# Multi-stage build option for smaller production image
FROM python:3.12.3-slim-bookworm AS production

ENV PYTHONUNBUFFERED=1
ENV PYTHONDONTWRITEBYTECODE=1
ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8

# Install minimal runtime dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    libgmp10=2:6.2.1+dfsg1-1.1 \
    libmpfr6=4.2.0-1 \
    libmpc3=1.3.1-1 \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Copy from development stage
COPY --from=0 /usr/local/lib/python3.12/site-packages /usr/local/lib/python3.12/site-packages
COPY --from=0 /usr/local/bin /usr/local/bin
COPY --from=0 /app /app

# Create non-root user
RUN groupadd -r riemann && useradd -r -g riemann -d /app -s /bin/bash riemann
RUN chown -R riemann:riemann /app

USER riemann

ENV PYTHONPATH=/app:/app/utils

HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD python -c "import mpmath; import numpy; import sympy; print('OK')" || exit 1

CMD ["python", "validate_v5_coronacion.py", "--precision", "25", "--verbose"]