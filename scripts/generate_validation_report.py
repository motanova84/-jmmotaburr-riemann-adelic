"""Generate an HTML report summarising RH & D≡Ξ validation results."""

from __future__ import annotations

import json
from datetime import datetime
from pathlib import Path


def generate_html_report() -> None:
    """Render validation results (if present) into an HTML report."""

    results_file = Path("data/validation/rh_ds_validation_results.json")
    if not results_file.exists():
        print("❌ No se encontraron resultados de validación")
        return

    with results_file.open("r", encoding="utf-8") as f:
        results = json.load(f)

    validation = results.get("validation_summary", {})
    detailed = results.get("detailed_results", {})

    all_passed = validation.get("all_tests_passed", False)
    status_class = "success" if all_passed else "failure"
    status_text = "✅ TODAS LAS PRUEBAS PASARON" if all_passed else "❌ ALGUNAS PRUEBAS FALLARON"

    html_content = f"""
    <!DOCTYPE html>
    <html>
    <head>
        <meta charset=\"utf-8\" />
        <title>Validación RH &amp; D(s) ≡ Ξ(s) - Riemann-Adelic</title>
        <style>
            body {{ font-family: Arial, sans-serif; margin: 40px; }}
            .success {{ color: green; font-weight: bold; }}
            .failure {{ color: red; font-weight: bold; }}
            .test-result {{ margin: 10px 0; padding: 10px; border-left: 4px solid; }}
            .passed {{ border-color: green; background: #f0fff0; }}
            .failed {{ border-color: red; background: #fff0f0; }}
            .details {{ margin-top: 20px; padding: 15px; background: #f5f5f5; }}
            pre {{ white-space: pre-wrap; word-break: break-word; }}
        </style>
    </head>
    <body>
        <h1>🏆 Validación Riemann Hypothesis &amp; D(s) ≡ Ξ(s)</h1>
        <h2>Repositorio: motanova84/-jmmotaburr-riemann-adelic</h2>
        <p>Fecha del reporte: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p>

        <div class=\"test-result {'passed' if all_passed else 'failed'}\">
            <h3>Estado General: <span class=\"{status_class}\">{status_text}</span></h3>
        </div>
    """

    for test_name, passed in validation.items():
        if test_name == "all_tests_passed":
            continue
        html_content += f"""
        <div class=\"test-result {'passed' if passed else 'failed'}\">
            <h4>{test_name}: {'✅ PASÓ' if passed else '❌ FALLÓ'}</h4>
        </div>
        """

    html_content += """
        <div class=\"details\">
            <h4>Detalles Técnicos:</h4>
            <pre>{json.dumps(detailed, indent=2, ensure_ascii=False)}</pre>
        </div>

        <hr />
        <p><em>Generado automáticamente por el sistema de validación Riemann-Adelic.</em></p>
    </body>
    </html>
    """

    report_file = Path("data/validation/validation_report.html")
    report_file.parent.mkdir(parents=True, exist_ok=True)
    with report_file.open("w", encoding="utf-8") as f:
        f.write(html_content)

    print(f"📊 Reporte HTML generado: {report_file}")


if __name__ == "__main__":
    generate_html_report()
