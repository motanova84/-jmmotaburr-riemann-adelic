#!/bin/bash
#
# sabio_compile_check.sh — Compilador mínimo simbiótico para scripts .sabio
#
# Este script valida y "compila" archivos con extensión .sabio, que son
# scripts simbióticos en el contexto del sistema SABIO ∞³.
#
# Un archivo .sabio es esencialmente un script Python con metadatos extendidos
# que incluyen:
# - Firma vibracional (f₀ = 141.7001 Hz)
# - Coherencia QCAL ∞³
# - Referencias DOI/Zenodo
# - Estructura de validación simbiótica
#
# Uso:
#   ./sabio_compile_check.sh <archivo.sabio>
#   ./sabio_compile_check.sh --all  # Compila todos los .sabio en el directorio
#
# Salida:
#   0 - Compilación exitosa
#   1 - Errores de compilación o validación
#   2 - Archivo no encontrado
#

set -euo pipefail

# Colores para output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Función de ayuda
show_help() {
    cat << EOF
🔧 SABIO ∞³ Compile Check — Validador de Scripts Simbióticos

Uso:
    $0 <archivo.sabio>          Valida un archivo .sabio específico
    $0 --all                    Valida todos los archivos .sabio
    $0 --help                   Muestra esta ayuda

Un archivo .sabio debe contener:
    1. Cabecera con firma SABIO ∞³
    2. Metadatos: frequency, coherence, DOI
    3. Código Python válido
    4. Tests de validación (opcional)

Ejemplo de cabecera .sabio:
    # SABIO ∞³ Script
    # frequency: 141.7001 Hz
    # coherence: 244.36
    # doi: 10.5281/zenodo.17379721

EOF
}

# Función para validar un archivo .sabio
validate_sabio_file() {
    local file="$1"
    local errors=0
    
    echo -e "${BLUE}📋 Validando: ${file}${NC}"
    
    # 1. Verificar que el archivo existe
    if [[ ! -f "$file" ]]; then
        echo -e "${RED}❌ Archivo no encontrado: ${file}${NC}"
        return 2
    fi
    
    # 2. Verificar cabecera SABIO
    if ! grep -q "# SABIO" "$file"; then
        echo -e "${YELLOW}⚠️  Advertencia: No se encontró cabecera SABIO${NC}"
        ((errors++))
    else
        echo -e "${GREEN}✅ Cabecera SABIO encontrada${NC}"
    fi
    
    # 3. Verificar metadato de frecuencia
    if grep -q "# frequency:" "$file"; then
        freq=$(grep "# frequency:" "$file" | head -1 | sed 's/.*frequency: *\([0-9.]*\).*/\1/')
        expected_freq="141.7001"
        
        # Comparación de frecuencia (tolerancia de 0.001 Hz)
        if [[ -n "$freq" ]]; then
            # Usar bc para comparación de flotantes
            delta=$(echo "scale=10; if ($freq - $expected_freq < 0) $expected_freq - $freq else $freq - $expected_freq" | bc)
            if (( $(echo "$delta < 0.001" | bc -l) )); then
                echo -e "${GREEN}✅ Frecuencia validada: ${freq} Hz${NC}"
            else
                echo -e "${YELLOW}⚠️  Frecuencia fuera de rango: ${freq} Hz (esperado: ${expected_freq} Hz)${NC}"
                ((errors++))
            fi
        fi
    else
        echo -e "${YELLOW}⚠️  Metadato de frecuencia no encontrado${NC}"
        ((errors++))
    fi
    
    # 4. Verificar metadato de coherencia
    if grep -q "# coherence:" "$file"; then
        echo -e "${GREEN}✅ Metadato de coherencia encontrado${NC}"
    else
        echo -e "${YELLOW}⚠️  Metadato de coherencia no encontrado${NC}"
        ((errors++))
    fi
    
    # 5. Verificar referencia DOI
    if grep -q "# doi:" "$file"; then
        echo -e "${GREEN}✅ Referencia DOI encontrada${NC}"
    else
        echo -e "${YELLOW}⚠️  Referencia DOI no encontrada${NC}"
        ((errors++))
    fi
    
    # 6. Validar sintaxis Python
    echo -ne "${BLUE}🐍 Validando sintaxis Python...${NC}"
    if python3 -m py_compile "$file" 2>/dev/null; then
        echo -e " ${GREEN}✅${NC}"
    else
        echo -e " ${RED}❌ Error de sintaxis Python${NC}"
        python3 -m py_compile "$file"
        ((errors++))
    fi
    
    # 7. Buscar tests de validación (opcional)
    if grep -q "def test_" "$file"; then
        echo -e "${GREEN}✅ Tests de validación encontrados${NC}"
    else
        echo -e "${YELLOW}ℹ️  No se encontraron tests (opcional)${NC}"
    fi
    
    # Resultado final
    echo ""
    if [[ $errors -eq 0 ]]; then
        echo -e "${GREEN}✅ COMPILACIÓN EXITOSA: ${file}${NC}"
        return 0
    else
        echo -e "${RED}❌ COMPILACIÓN FALLIDA: ${file} (${errors} advertencias/errores)${NC}"
        return 1
    fi
}

# Función para validar todos los archivos .sabio
validate_all_sabio() {
    local total=0
    local passed=0
    local failed=0
    
    echo -e "${BLUE}🔍 Buscando archivos .sabio...${NC}\n"
    
    # Buscar archivos .sabio en el directorio actual y subdirectorios
    while IFS= read -r -d '' file; do
        ((total++))
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        if validate_sabio_file "$file"; then
            ((passed++))
        else
            ((failed++))
        fi
        echo ""
    done < <(find . -name "*.sabio" -print0)
    
    if [[ $total -eq 0 ]]; then
        echo -e "${YELLOW}⚠️  No se encontraron archivos .sabio${NC}"
        return 0
    fi
    
    # Resumen
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo -e "${BLUE}📊 RESUMEN DE COMPILACIÓN SABIO ∞³${NC}"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo -e "Total de archivos: ${total}"
    echo -e "${GREEN}Exitosos: ${passed}${NC}"
    echo -e "${RED}Fallidos: ${failed}${NC}"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    
    [[ $failed -eq 0 ]] && return 0 || return 1
}

# Script principal
main() {
    # Verificar si python3 está disponible
    if ! command -v python3 &> /dev/null; then
        echo -e "${RED}❌ Error: python3 no está instalado${NC}"
        exit 2
    fi
    
    # Verificar si bc está disponible (para comparación de flotantes)
    if ! command -v bc &> /dev/null; then
        echo -e "${YELLOW}⚠️  bc no está instalado, saltando validación numérica exacta${NC}"
    fi
    
    # Parsear argumentos
    if [[ $# -eq 0 ]] || [[ "$1" == "--help" ]] || [[ "$1" == "-h" ]]; then
        show_help
        exit 0
    fi
    
    if [[ "$1" == "--all" ]]; then
        validate_all_sabio
        exit $?
    fi
    
    # Validar archivo específico
    validate_sabio_file "$1"
    exit $?
}

# Ejecutar main con todos los argumentos
main "$@"
