"""
Tests for metadata validation and conversion tools.

These tests verify the infrastructure for formal artifact ingestion,
including metadata validation and conversion pipelines.
"""

import json
import subprocess
import sys
from pathlib import Path


def test_metadata_validation():
    """Test that metadata validation script works correctly."""
    result = subprocess.run(
        [sys.executable, "tools/verify_metadata.py", "schema/metadata_example.jsonld"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"Metadata validation failed: {result.stderr}"
    assert "METADATA OK" in result.stdout


def test_metadata_validation_missing_file():
    """Test that metadata validation fails for missing files."""
    result = subprocess.run(
        [sys.executable, "tools/verify_metadata.py", "schema/nonexistent.jsonld"],
        capture_output=True,
        text=True,
    )
    assert result.returncode != 0


def test_metadata_schema_structure():
    """Test that the metadata schema has required fields."""
    metadata_path = Path("schema/metadata_example.jsonld")
    assert metadata_path.exists(), "Metadata example file not found"

    with open(metadata_path, "r", encoding="utf-8") as f:
        metadata = json.load(f)

    # Verify required fields
    required_fields = ["@id", "dc:title", "dc:creator", "format", "origin", "kernel", "checksum"]
    for field in required_fields:
        assert field in metadata, f"Required field '{field}' missing from metadata"

    # Verify checksum format
    assert metadata["checksum"].startswith("sha256:"), "Checksum should start with 'sha256:'"
    hash_part = metadata["checksum"].replace("sha256:", "")
    assert len(hash_part) == 64, "SHA-256 hash should be 64 characters"


def test_conversion_pipeline():
    """Test that the conversion pipeline works correctly."""
    # Clean up any existing intermediate file
    intermediate_file = Path("tests/examples/example_lean.intermediate.json")
    if intermediate_file.exists():
        intermediate_file.unlink()

    # Run conversion
    result = subprocess.run(
        [sys.executable, "tools/convert_example.py", "tests/examples/example_lean.lean"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"Conversion failed: {result.stderr}"
    assert "Conversión completada" in result.stdout

    # Verify intermediate file was created
    assert intermediate_file.exists(), "Intermediate file was not created"

    # Verify intermediate file structure
    with open(intermediate_file, "r", encoding="utf-8") as f:
        intermediate_data = json.load(f)

    assert "@type" in intermediate_data
    assert intermediate_data["@type"] == "IntermediateRepresentation"
    assert "source" in intermediate_data
    assert "checksum" in intermediate_data
    assert intermediate_data["checksum"].startswith("sha256:")

    # Clean up
    intermediate_file.unlink()


def test_example_lean_file_exists():
    """Test that the example Lean file exists."""
    lean_file = Path("tests/examples/example_lean.lean")
    assert lean_file.exists(), "Example Lean file not found"

    # Verify it has some content
    content = lean_file.read_text()
    assert len(content) > 0, "Example Lean file is empty"
    assert "theorem" in content, "Example Lean file should contain theorems"


def test_contributing_guidelines_exist():
    """Test that CONTRIBUTING.md exists and has content."""
    contributing = Path("CONTRIBUTING.md")
    assert contributing.exists(), "CONTRIBUTING.md not found"

    content = contributing.read_text()
    assert "Guía de Contribución" in content or "Contribution" in content
    assert len(content) > 1000, "CONTRIBUTING.md should have substantial content"


def test_pyproject_toml_exists():
    """Test that pyproject.toml exists and has required sections."""
    pyproject = Path("pyproject.toml")
    assert pyproject.exists(), "pyproject.toml not found"

    content = pyproject.read_text()
    assert "[project]" in content
    assert "[tool.black]" in content
    assert "[tool.isort]" in content
    assert "[tool.pytest.ini_options]" in content


def test_codeowners_exists():
    """Test that CODEOWNERS file exists."""
    codeowners = Path(".github/CODEOWNERS")
    assert codeowners.exists(), "CODEOWNERS not found"

    content = codeowners.read_text()
    assert "@motanova84" in content


def test_pr_template_exists():
    """Test that PR template exists."""
    pr_template = Path(".github/PULL_REQUEST_TEMPLATE.md")
    assert pr_template.exists(), "PR template not found"

    content = pr_template.read_text()
    assert "Objetivo" in content or "Purpose" in content
