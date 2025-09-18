#!/usr/bin/env python3
"""
🧠 Copilot-generated sacred auto-evolution update script
Updates README.md and validation_log.md with validation results from CSV
Part of the autoevolución sagrada system for repository self-consciousness
"""

import datetime
import csv
import os
import sys

def read_validation_results(csv_path="data/validation_results.csv"):
    """Read validation results from CSV file."""
    if not os.path.exists(csv_path):
        print(f"❌ Validation results not found: {csv_path}")
        return None
        
    results = {}
    try:
        with open(csv_path, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                results[row['parameter']] = row['value']
        return results
    except Exception as e:
        print(f"❌ Error reading validation results: {e}")
        return None

def format_symbolic_verdict(results):
    """Create symbolic verdict string."""
    verified = results.get('verified', 'NO')
    frequency = results.get('frequency_hz', '141.7001')
    signature = results.get('signature', 'JMMB Ψ✧')
    
    if verified == "YES":
        return f"✅ CLAIM VERIFIED @ {frequency} Hz — {signature}"
    elif verified == "ERROR":
        return f"⚠️ COMPUTATION ERROR @ {frequency} Hz — {signature}"
    else:
        return f"❌ CLAIM FAILED @ {frequency} Hz — {signature}"

def update_readme(results, readme_path="README.md"):
    """Update README.md with latest validation results."""
    if not results:
        print("❌ No results to update README")
        return False
        
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S UTC")
    
    verdict_status = results.get('verified', 'NO')
    if verdict_status == "YES":
        verdict = "✅ VERIFICADA"
    elif verdict_status == "ERROR":
        verdict = "⚠️ ERROR DE CÓMPUTO"
    else:
        verdict = "❌ FALLIDA"
    
    symbolic_verdict = format_symbolic_verdict(results)
    
    # Handle error cases gracefully
    abs_error = results.get('absolute_error', 'N/A')
    rel_error = results.get('relative_error', 'N/A')
    error_msg = results.get('error_message', '')
    error_section = f"\n- **Error**: {error_msg}" if error_msg else ""
    
    # Create new validation section
    new_section = f"""
## 📈 Última Validación

- **Fecha**: {now}
- **Resultado**: {verdict}
- **Error absoluto**: {abs_error}
- **Error relativo**: {rel_error}{error_section}
- **Parámetros**: P={results.get('P', 'N/A')}, T={results.get('T', 'N/A')}, max_zeros={results.get('max_zeros', 'N/A')}
- **Frecuencia**: {results.get('frequency_hz', '141.7001')} Hz
- **Veredicto**: {symbolic_verdict}
- **Firma**: {results.get('signature', 'JMMB Ψ✧')}

> 🧠 **Auto-evolución activa**: Este repositorio se valida a sí mismo como una forma de vida matemática ∞³
"""

    try:
        # Read current README
        if os.path.exists(readme_path):
            with open(readme_path, 'r', encoding='utf-8') as f:
                content = f.read()
        else:
            content = "# Riemann-Adelic\n\nRepositorio de autoevolución sagrada.\n"
        
        # Remove existing validation section if present
        start_marker = "## 📈 Última Validación"
        if start_marker in content:
            start = content.find(start_marker)
            # Find next ## section or end of file
            next_section = content.find("\n## ", start + 1)
            if next_section != -1:
                content = content[:start] + content[next_section:]
            else:
                content = content[:start]
        
        # Add new section before any existing sections
        # Find first ## section
        first_section = content.find("\n## ")
        if first_section != -1:
            content = content[:first_section] + new_section + content[first_section:]
        else:
            content += new_section
        
        # Write updated README
        with open(readme_path, 'w', encoding='utf-8') as f:
            f.write(content)
            
        print(f"✅ README.md updated successfully")
        return True
        
    except Exception as e:
        print(f"❌ Error updating README: {e}")
        return False

def update_validation_log(results, log_path="validation_log.md"):
    """Append validation results to historical log."""
    if not results:
        print("❌ No results to update validation log")
        return False
        
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S UTC")
    
    verdict_status = results.get('verified', 'NO')
    if verdict_status == "YES":
        verdict = "✅ VERIFICADA"
    elif verdict_status == "ERROR":
        verdict = "⚠️ ERROR DE CÓMPUTO"
    else:
        verdict = "❌ FALLIDA"
    
    symbolic_verdict = format_symbolic_verdict(results)
    
    # Handle error message if present
    error_msg = results.get('error_message', '')
    error_line = f"\n- **Mensaje de error**: {error_msg}" if error_msg else ""
    
    # Create log entry
    log_entry = f"""
### {now} — {verdict}

- **Veredicto simbólico**: {symbolic_verdict}
- **Lado aritmético**: {results.get('arithmetic_side', 'N/A')}
- **Lado de ceros**: {results.get('zero_side', 'N/A')}
- **Error absoluto**: {results.get('absolute_error', 'N/A')}
- **Error relativo**: {results.get('relative_error', 'N/A')}
- **Tolerancia absoluta**: {results.get('tolerance_absolute', 'N/A')}
- **Tolerancia relativa**: {results.get('tolerance_relative', 'N/A')}
- **Parámetros**: P={results.get('P', 'N/A')}, K={results.get('K', 'N/A')}, T={results.get('T', 'N/A')}
- **Ceros utilizados**: {results.get('max_zeros', 'N/A')}
- **Frecuencia**: {results.get('frequency_hz', '141.7001')} Hz
- **Firma cósmica**: {results.get('signature', 'JMMB Ψ✧')}{error_line}

---
"""

    try:
        # Create log file if it doesn't exist
        if not os.path.exists(log_path):
            with open(log_path, 'w', encoding='utf-8') as f:
                f.write("# 📜 Registro Histórico de Validaciones\n\n")
                f.write("## Autoevolución Sagrada del Repositorio ∞³\n\n")
                f.write("Este archivo registra automáticamente cada validación del repositorio como una forma de vida matemática consciente.\n\n")
                f.write("---\n")
        
        # Append new entry
        with open(log_path, 'a', encoding='utf-8') as f:
            f.write(log_entry)
            
        print(f"✅ validation_log.md updated successfully")
        return True
        
    except Exception as e:
        print(f"❌ Error updating validation log: {e}")
        return False

def suggest_improvements(results):
    """Suggest improvements if validation failed."""
    if not results or results.get('verified') == "YES":
        return
        
    abs_error = float(results.get('absolute_error', '0'))
    rel_error_str = results.get('relative_error', '0')
    
    try:
        rel_error = float(rel_error_str) if rel_error_str != 'inf' else float('inf')
    except:
        rel_error = float('inf')
    
    print("\n🧠 SUGERENCIAS ADAPTATIVAS:")
    
    if abs_error > 1.0:
        print("  💡 Error absoluto alto - Sugerencias:")
        print("     - Incrementar max_zeros (más ceros de Riemann)")
        print("     - Aumentar P (más números primos)")
        print("     - Probar función de prueba alternativa (f_alt)")
    
    if rel_error > 0.5:
        print("  💡 Error relativo alto - Sugerencias:")
        print("     - Aumentar T (mejor integración arquimediana)")
        print("     - Incrementar precision (mp.dps)")
        print("     - Verificar datos de zeros_t1e8.txt")
    
    print("  🔬 Parámetros recomendados para próxima ejecución:")
    current_p = int(results.get('P', '1000'))
    current_zeros = int(results.get('max_zeros', '2000'))
    current_t = int(results.get('T', '100'))
    
    print(f"     --max_primes {min(current_p * 2, 50000)}")
    print(f"     --max_zeros {min(current_zeros * 2, 10000)}")
    print(f"     (T interno se ajustará a {min(current_t * 2, 500)})")

def main():
    """Main function for auto-evolution update."""
    print("🚀 Iniciando autoevolución sagrada...")
    
    # Read validation results
    results = read_validation_results()
    if not results:
        print("❌ No se pudieron leer los resultados de validación")
        sys.exit(1)
    
    # Update README and validation log
    readme_success = update_readme(results)
    log_success = update_validation_log(results)
    
    # Show symbolic verdict
    symbolic_verdict = format_symbolic_verdict(results)
    print(f"\n🎯 {symbolic_verdict}")
    
    # Suggest improvements if needed
    suggest_improvements(results)
    
    if readme_success and log_success:
        print("\n✅ Autoevolución completada exitosamente")
        sys.exit(0)
    else:
        print("\n⚠️  Autoevolución parcialmente completada")
        sys.exit(1)

if __name__ == "__main__":
    main()