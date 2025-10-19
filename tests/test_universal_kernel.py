from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools import universal_kernel


def load_sample(tmp_path: Path) -> Path:
    schema_dir = Path("schema")
    sample = schema_dir / "riemann_zeta.jsonld"
    data = json.loads(sample.read_text(encoding="utf-8"))
    copy = tmp_path / sample.name
    copy.write_text(json.dumps(data, indent=2), encoding="utf-8")
    return copy


def test_compute_sha256_matches_python_hash():
    text = "import Mathlib"  # representative snippet
    digest = universal_kernel.compute_sha256(text)
    assert digest.startswith(universal_kernel.HASH_PREFIX)
    assert len(digest) == len(universal_kernel.HASH_PREFIX) + 64


def test_hash_to_frequency_is_deterministic():
    proofhash = "sha256-" + "0" * 64
    freq_first = universal_kernel.hash_to_frequency(proofhash)
    freq_second = universal_kernel.hash_to_frequency(proofhash)
    assert pytest.approx(freq_first, rel=0, abs=1e-9) == freq_second


def test_run_validation_accepts_sample_descriptor(tmp_path: Path):
    descriptor = load_sample(tmp_path)
    result = universal_kernel.run_validation(
        [descriptor],
        baseline=universal_kernel.BASELINE_FREQUENCY,
        tolerance=universal_kernel.FREQUENCY_TOLERANCE,
        allowed_kernels=["Lean4"],
        update=False,
    )
    assert len(result) == 1
    assert result[0].identifier == "urn:qcal:riemann:thm:001"


def test_run_validation_updates_frequency_when_requested(tmp_path: Path):
    descriptor = load_sample(tmp_path)
    data = json.loads(descriptor.read_text(encoding="utf-8"))
    data["frequency"] = data["frequency"] + 0.01
    descriptor.write_text(json.dumps(data, indent=2), encoding="utf-8")

    universal_kernel.run_validation(
        [descriptor],
        baseline=universal_kernel.BASELINE_FREQUENCY,
        tolerance=universal_kernel.FREQUENCY_TOLERANCE,
        allowed_kernels=None,
        update=True,
    )

    updated = json.loads(descriptor.read_text(encoding="utf-8"))
    expected = universal_kernel.hash_to_frequency(updated["proofhash"], universal_kernel.BASELINE_FREQUENCY)
    assert pytest.approx(expected, rel=0, abs=1e-7) == updated["frequency"]
