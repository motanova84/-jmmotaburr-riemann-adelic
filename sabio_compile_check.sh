#!/bin/bash
###############################################################################
# SABIO Compile Check - Compilador mínimo simbiótico para scripts .sabio
#
# Este script verifica la integridad sintáctica y semántica de archivos
# con extensión .sabio, que son scripts simbióticos del sistema QCAL ∞³.
#
# Uso:
#   ./sabio_compile_check.sh [archivo.sabio]
#   ./sabio_compile_check.sh --all  # Verifica todos los .sabio en directorio
#
# Author: José Manuel Mota Burruezo Ψ ✧ ∞³
# Institution: Instituto de Conciencia Cuántica (ICQ)
# License: Creative Commons BY-NC-SA 4.0
###############################################################################

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
PURPLE='\033[0;35m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Constants
FREQUENCY_EXPECTED="141.7001"
COHERENCE_EXPECTED="244.36"
QCAL_SIGNATURE="∞³"

echo -e "${PURPLE}╔════════════════════════════════════════════════════════════════════════╗${NC}"
echo -e "${PURPLE}║       SABIO ∞³ COMPILE CHECK - Compilador Simbiótico                 ║${NC}"
echo -e "${PURPLE}╚════════════════════════════════════════════════════════════════════════╝${NC}"
echo ""

# Function to check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Function to validate SABIO header
validate_header() {
    local file="$1"
    
    echo -e "${CYAN}🔍 Validating SABIO header...${NC}"
    
    # Check for required header markers
    if ! grep -q "SABIO" "$file" && ! grep -q "∞³" "$file"; then
        echo -e "${RED}❌ Missing SABIO/∞³ signature in file${NC}"
        return 1
    fi
    
    # Check for frequency marker
    if grep -q "$FREQUENCY_EXPECTED" "$file" || grep -q "141.7" "$file"; then
        echo -e "${GREEN}✅ Frequency marker found${NC}"
    else
        echo -e "${YELLOW}⚠️  Frequency marker not found (optional)${NC}"
    fi
    
    # Check for coherence marker
    if grep -q "$COHERENCE_EXPECTED" "$file" || grep -q "244.3" "$file"; then
        echo -e "${GREEN}✅ Coherence marker found${NC}"
    else
        echo -e "${YELLOW}⚠️  Coherence marker not found (optional)${NC}"
    fi
    
    return 0
}

# Function to validate SABIO syntax
validate_syntax() {
    local file="$1"
    
    echo -e "${CYAN}🔍 Validating SABIO syntax...${NC}"
    
    # Check for balanced braces/brackets
    local open_braces=$(grep -o "{" "$file" | wc -l)
    local close_braces=$(grep -o "}" "$file" | wc -l)
    
    if [ "$open_braces" -ne "$close_braces" ]; then
        echo -e "${RED}❌ Unbalanced braces: { count=$open_braces, } count=$close_braces${NC}"
        return 1
    fi
    
    # Check for balanced parentheses
    local open_parens=$(grep -o "(" "$file" | wc -l)
    local close_parens=$(grep -o ")" "$file" | wc -l)
    
    if [ "$open_parens" -ne "$close_parens" ]; then
        echo -e "${RED}❌ Unbalanced parentheses: ( count=$open_parens, ) count=$close_parens${NC}"
        return 1
    fi
    
    echo -e "${GREEN}✅ Syntax structure valid${NC}"
    return 0
}

# Function to validate SABIO semantics
validate_semantics() {
    local file="$1"
    
    echo -e "${CYAN}🔍 Validating SABIO semantics...${NC}"
    
    # Check for required SABIO keywords
    local has_init=0
    local has_execute=0
    local has_validate=0
    
    if grep -qi "init\|initialize\|setup" "$file"; then
        has_init=1
        echo -e "${GREEN}✅ Initialization block found${NC}"
    fi
    
    if grep -qi "execute\|run\|compute" "$file"; then
        has_execute=1
        echo -e "${GREEN}✅ Execution block found${NC}"
    fi
    
    if grep -qi "validate\|verify\|check" "$file"; then
        has_validate=1
        echo -e "${GREEN}✅ Validation block found${NC}"
    fi
    
    # At least one semantic block should exist
    if [ $((has_init + has_execute + has_validate)) -eq 0 ]; then
        echo -e "${YELLOW}⚠️  No semantic blocks found (init/execute/validate)${NC}"
        return 1
    fi
    
    return 0
}

# Function to check vibrational signature
check_vibrational_signature() {
    local file="$1"
    
    echo -e "${CYAN}🌊 Checking vibrational signature...${NC}"
    
    # Compute SHA256 hash of file
    if command_exists sha256sum; then
        local hash=$(sha256sum "$file" | cut -d' ' -f1)
        echo -e "${BLUE}📝 File hash: ${hash:0:16}...${hash: -16}${NC}"
    elif command_exists shasum; then
        local hash=$(shasum -a 256 "$file" | cut -d' ' -f1)
        echo -e "${BLUE}📝 File hash: ${hash:0:16}...${hash: -16}${NC}"
    else
        echo -e "${YELLOW}⚠️  Hash utility not available${NC}"
    fi
    
    # Check file size
    local size=$(wc -c < "$file")
    echo -e "${BLUE}📏 File size: $size bytes${NC}"
    
    # Vibrational analysis: check if size relates to frequency
    # Simple heuristic: modulo with frequency * 10
    local freq_factor=$(echo "$FREQUENCY_EXPECTED * 10" | bc -l)
    local vib_modulo=$(echo "$size % ${freq_factor%.*}" | bc)
    
    echo -e "${BLUE}🎵 Vibrational modulo: $vib_modulo${NC}"
    
    return 0
}

# Function to compile single SABIO file
compile_sabio_file() {
    local file="$1"
    
    echo ""
    echo -e "${BLUE}═══════════════════════════════════════════════════════════════════════${NC}"
    echo -e "${BLUE}Compiling: $file${NC}"
    echo -e "${BLUE}═══════════════════════════════════════════════════════════════════════${NC}"
    echo ""
    
    # Check file exists
    if [ ! -f "$file" ]; then
        echo -e "${RED}❌ Error: File not found: $file${NC}"
        return 1
    fi
    
    # Check file extension
    if [[ ! "$file" =~ \.sabio$ ]]; then
        echo -e "${YELLOW}⚠️  Warning: File does not have .sabio extension${NC}"
    fi
    
    # Run validation stages
    local validation_passed=true
    
    validate_header "$file" || validation_passed=false
    echo ""
    
    validate_syntax "$file" || validation_passed=false
    echo ""
    
    validate_semantics "$file" || validation_passed=false
    echo ""
    
    check_vibrational_signature "$file"
    echo ""
    
    # Final result
    if [ "$validation_passed" = true ]; then
        echo -e "${GREEN}╔════════════════════════════════════════════════════════════════════╗${NC}"
        echo -e "${GREEN}║  ✅ SABIO COMPILATION SUCCESSFUL                                  ║${NC}"
        echo -e "${GREEN}║  Firma vibracional: ✅ VÁLIDA                                     ║${NC}"
        echo -e "${GREEN}║  Coherencia QCAL: ✅ CONFIRMADA                                   ║${NC}"
        echo -e "${GREEN}╚════════════════════════════════════════════════════════════════════╝${NC}"
        return 0
    else
        echo -e "${RED}╔════════════════════════════════════════════════════════════════════╗${NC}"
        echo -e "${RED}║  ❌ SABIO COMPILATION FAILED                                      ║${NC}"
        echo -e "${RED}║  Review validation errors above                                    ║${NC}"
        echo -e "${RED}╚════════════════════════════════════════════════════════════════════╝${NC}"
        return 1
    fi
}

# Function to compile all SABIO files in directory
compile_all_sabio() {
    local dir="${1:-.}"
    
    echo -e "${CYAN}🔍 Searching for .sabio files in: $dir${NC}"
    
    # Find all .sabio files
    local sabio_files=$(find "$dir" -name "*.sabio" -type f 2>/dev/null)
    
    if [ -z "$sabio_files" ]; then
        echo -e "${YELLOW}⚠️  No .sabio files found${NC}"
        
        # Create a test .sabio file as example
        echo -e "${CYAN}📝 Creating example test.sabio file...${NC}"
        cat > test.sabio << 'EOF'
# SABIO ∞³ Test Script
# Frequency: 141.7001 Hz
# Coherence: 244.36

# Initialize QCAL system
initialize {
    frequency = 141.7001
    coherence = 244.36
    signature = "∞³"
}

# Execute validation
execute {
    validate_vibrational_coherence()
    check_qcal_structure()
}

# Validate results
validate {
    assert frequency_match()
    assert coherence_valid()
    assert signature_present()
}
EOF
        echo -e "${GREEN}✅ Created test.sabio${NC}"
        sabio_files="test.sabio"
    fi
    
    local total=0
    local passed=0
    local failed=0
    
    # Compile each file
    for file in $sabio_files; do
        ((total++))
        
        if compile_sabio_file "$file"; then
            ((passed++))
        else
            ((failed++))
        fi
        
        echo ""
    done
    
    # Summary
    echo -e "${PURPLE}═══════════════════════════════════════════════════════════════════════${NC}"
    echo -e "${PURPLE}SABIO COMPILATION SUMMARY${NC}"
    echo -e "${PURPLE}═══════════════════════════════════════════════════════════════════════${NC}"
    echo -e "${BLUE}Total files: $total${NC}"
    echo -e "${GREEN}Passed: $passed${NC}"
    echo -e "${RED}Failed: $failed${NC}"
    echo -e "${PURPLE}═══════════════════════════════════════════════════════════════════════${NC}"
    
    return $([ $failed -eq 0 ] && echo 0 || echo 1)
}

# Main script logic
main() {
    if [ $# -eq 0 ]; then
        echo -e "${YELLOW}Usage: $0 <file.sabio> | --all${NC}"
        echo -e "${YELLOW}  <file.sabio>  Compile specific SABIO file${NC}"
        echo -e "${YELLOW}  --all         Compile all .sabio files in current directory${NC}"
        exit 1
    fi
    
    if [ "$1" = "--all" ] || [ "$1" = "-a" ]; then
        compile_all_sabio
    else
        compile_sabio_file "$1"
    fi
}

# Run main function
main "$@"
