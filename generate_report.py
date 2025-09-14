import mpmath as mp
import sympy as sp
import csv
import os
from datetime import datetime
from utils.mellin import truncated_gaussian, mellin_transform

def generate_html_report(csv_file, output_file):
    """Generate HTML report from validation results."""
    
    if not os.path.exists(csv_file):
        print(f"⚠️  CSV file {csv_file} not found. Cannot generate HTML report.")
        return
        
    with open(csv_file, 'r') as f:
        reader = csv.DictReader(f)
        results = list(reader)
    
    html_content = f"""
<!DOCTYPE html>
<html lang="es">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Validación Hipótesis de Riemann - Resultados</title>
    <style>
        body {{ font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif; 
               margin: 40px; background-color: #f5f5f5; }}
        .container {{ max-width: 1200px; margin: 0 auto; background: white; 
                     padding: 30px; border-radius: 10px; box-shadow: 0 2px 10px rgba(0,0,0,0.1); }}
        h1 {{ color: #2c3e50; text-align: center; border-bottom: 3px solid #3498db; padding-bottom: 10px; }}
        h2 {{ color: #34495e; margin-top: 30px; }}
        .meta-info {{ background: #ecf0f1; padding: 15px; border-radius: 5px; margin: 20px 0; }}
        .success {{ color: #27ae60; font-weight: bold; }}
        .failure {{ color: #e74c3c; font-weight: bold; }}
        table {{ width: 100%; border-collapse: collapse; margin: 20px 0; }}
        th, td {{ border: 1px solid #bdc3c7; padding: 12px; text-align: left; }}
        th {{ background-color: #3498db; color: white; }}
        tr:nth-child(even) {{ background-color: #f8f9fa; }}
        .formula {{ font-family: 'Times New Roman', serif; font-style: italic; 
                   background: #ffeaa7; padding: 10px; border-radius: 5px; margin: 15px 0; }}
        .summary {{ background: #d5f4e6; padding: 20px; border-radius: 5px; margin: 20px 0; }}
        .error-high {{ background-color: #ffebee; }}
        .error-low {{ background-color: #e8f5e8; }}
        .code {{ font-family: 'Courier New', monospace; background: #f4f4f4; 
                padding: 2px 4px; border-radius: 3px; }}
    </style>
</head>
<body>
    <div class="container">
        <h1>🧮 Validación de la Hipótesis de Riemann</h1>
        
        <div class="meta-info">
            <strong>Autor:</strong> José Manuel Mota Burruezo<br>
            <strong>Instituto:</strong> Instituto de Conciencia Cuántica (ICQ)<br>
            <strong>Fecha de validación:</strong> {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}<br>
            <strong>DOI:</strong> <a href="https://doi.org/10.5281/zenodo.17114751" target="_blank">10.5281/zenodo.17114751</a>
        </div>

        <h2>🎯 Objetivo</h2>
        <p>Validar numéricamente la identidad fundamental:</p>
        <div class="formula">
            PrimeSum(f) + A_∞(f) = Σ_ρ f̂(ρ)
        </div>
        <p>donde el error absoluto debe ser menor a <strong>1×10⁻⁵</strong> para las funciones de prueba f₁, f₂, f₃.</p>

        <h2>📊 Resultados de Validación</h2>
        <table>
            <thead>
                <tr>
                    <th>Función</th>
                    <th>Prime Sum</th>
                    <th>A_∞ (Archimedean)</th>
                    <th>Total Aritmético</th>
                    <th>Sum de Ceros</th>
                    <th>Error Absoluto</th>
                    <th>Error Relativo</th>
                    <th>Estado</th>
                </tr>
            </thead>
            <tbody>"""
    
    all_success = True
    for result in results:
        error = float(result['absolute_error'])
        success = result['success'].lower() == 'true'
        all_success = all_success and success
        
        error_class = 'error-low' if success else 'error-high'
        status = '<span class="success">✅ ÉXITO</span>' if success else '<span class="failure">❌ FALLO</span>'
        
        html_content += f"""
                <tr class="{error_class}">
                    <td><strong>{result['function']}</strong></td>
                    <td>{float(result['prime_sum']):.8f}</td>
                    <td>{float(result['archimedean_sum']):.8f}</td>
                    <td>{float(result['arithmetic_total']):.8f}</td>
                    <td>{float(result['zero_sum']):.8f}</td>
                    <td class="code">{error:.2e}</td>
                    <td class="code">{float(result['relative_error']):.2e}</td>
                    <td>{status}</td>
                </tr>"""
    
    summary_class = "success" if all_success else "failure"
    summary_text = "✅ VALIDACIÓN EXITOSA" if all_success else "❌ VALIDACIÓN FALLIDA"
    
    html_content += f"""
            </tbody>
        </table>

        <div class="summary">
            <h2>🏆 Resumen Final</h2>
            <p class="{summary_class}" style="font-size: 1.2em; text-align: center;">
                <strong>{summary_text}</strong>
            </p>
            {f"<p><strong>Resultado:</strong> Todas las funciones de prueba han validado la identidad dentro del margen de error requerido (< 1×10⁻⁵).</p>" if all_success else "<p><strong>Resultado:</strong> Una o más funciones exceden el margen de error permitido. Se requiere revisión.</p>"}
        </div>

        <h2>📋 Parámetros de Validación</h2>
        <ul>
            <li><strong>δ (delta):</strong> 0.01</li>
            <li><strong>P (máximo primo):</strong> 1000</li>
            <li><strong>K (potencias por primo):</strong> 50</li>
            <li><strong>N_Ξ (número de ceros):</strong> 2000</li>
            <li><strong>σ₀ (sigma_0):</strong> 2.0</li>
            <li><strong>T (límite integral):</strong> 50</li>
        </ul>

        <h2>🔬 Funciones de Prueba</h2>
        <ul>
            <li><strong>f₁(u):</strong> exp(-u²/2) para |u| ≤ 3</li>
            <li><strong>f₂(u):</strong> exp(-u²) para |u| ≤ 2</li>
            <li><strong>f₃(u):</strong> (1 - u²/4)² para |u| ≤ 2</li>
        </ul>

        <h2>📖 Referencias</h2>
        <p>Esta validación forma parte de la prueba completa de la Hipótesis de Riemann basada en:</p>
        <ul>
            <li>Teoría de determinantes de Fredholm</li>
            <li>Fórmula de traza adélica</li>
            <li>Unicidad de Paley-Wiener</li>
        </ul>
        
        <hr style="margin-top: 40px;">
        <p style="text-align: center; color: #7f8c8d; font-size: 0.9em;">
            Generado automáticamente el {datetime.now().strftime("%Y-%m-%d %H:%M:%S")} 
            | Repositorio: <a href="https://github.com/motanova84/riemann-adelic" target="_blank">motanova84/riemann-adelic</a>
        </p>
    </div>
</body>
</html>"""
    
    # Ensure docs directory exists
    os.makedirs(os.path.dirname(output_file), exist_ok=True)
    
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(html_content)
    
    print(f"📄 Reporte HTML generado: {output_file}")

if __name__ == "__main__":
    generate_html_report('data/validation_output.csv', 'docs/validation.html')