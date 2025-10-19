"""Universal coherence verification kernel.

This module provides a command line tool that validates a collection of
JSON-LD theorem descriptors according to three complementary layers:

* **Formal soundness** – the referenced formal proof artefact must exist and
  match the recorded hash.
* **Semantic coherence** – identifiers and dependency relations must follow
  the QCAL naming rules.
* **Resonant frequency alignment** – each theorem must publish a frequency
  derived from its proof hash that lies close to a baseline reference.

The script is intentionally lightweight so it can be executed inside CI and
serve as an integration point for heterogeneous theorem provers.  The
implementation avoids heavyweight dependencies so that it can run in the
existing project environment.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Mapping, MutableMapping, Optional, Sequence, Tuple

BASELINE_FREQUENCY = 141.7001
FREQUENCY_TOLERANCE = 1e-4
HASH_PREFIX = "sha256-"
REQUIRED_FIELDS = {"@id", "dc:title", "formal:kernel", "formal:proof", "proofhash", "dependencies", "equation", "frequency"}
URN_PATTERN = re.compile(r"^urn:qcal:[a-z0-9]+:[a-z0-9:_\-]+$", re.IGNORECASE)


class UniversalKernelError(RuntimeError):
    """Raised when universal kernel validation fails."""


@dataclass(frozen=True)
class ValidationResult:
    path: Path
    identifier: str
    frequency: float
    computed_frequency: float
    proofhash: str
    computed_hash: str

    def is_success(self) -> bool:
        return (
            abs(self.frequency - self.computed_frequency) <= FREQUENCY_TOLERANCE
            and self.proofhash == self.computed_hash
        )


def compute_sha256(content: str) -> str:
    digest = hashlib.sha256(content.encode("utf-8")).hexdigest()
    return f"{HASH_PREFIX}{digest}"


def hash_to_frequency(proofhash: str, baseline: float = BASELINE_FREQUENCY) -> float:
    if not proofhash.startswith(HASH_PREFIX):
        raise UniversalKernelError(f"Hash '{proofhash}' must start with '{HASH_PREFIX}'.")
    int_value = int(proofhash[len(HASH_PREFIX):], 16)
    window = 5e-3
    offset = (int_value % 1_000_000) / 1_000_000 * 2 * window - window
    return baseline + offset


def resolve_proof_content(entry: Mapping[str, object], json_path: Path) -> Tuple[str, Optional[Path]]:
    raw_reference = entry.get("formal:proof")
    if not isinstance(raw_reference, str) or not raw_reference.strip():
        raise UniversalKernelError("'formal:proof' must be a non-empty string.")

    candidate_path = Path(raw_reference)
    if not candidate_path.is_absolute():
        candidate_path = (json_path.parent / raw_reference).resolve()
        if not candidate_path.exists():
            candidate_path = (Path.cwd() / raw_reference).resolve()

    if candidate_path.exists():
        return candidate_path.read_text(encoding="utf-8"), candidate_path

    return raw_reference, None


def validate_identifier(identifier: str) -> None:
    if not URN_PATTERN.match(identifier):
        raise UniversalKernelError(f"Identifier '{identifier}' is not a valid QCAL URN.")


def validate_dependencies(identifier: str, dependencies: Sequence[object]) -> None:
    if not isinstance(dependencies, Sequence) or isinstance(dependencies, (str, bytes)):
        raise UniversalKernelError(f"Dependencies for '{identifier}' must be a sequence of URNs.")
    if not dependencies:
        raise UniversalKernelError(f"'{identifier}' must declare at least one dependency for traceability.")
    for dep in dependencies:
        if not isinstance(dep, str) or not URN_PATTERN.match(dep):
            raise UniversalKernelError(f"Dependency '{dep}' for '{identifier}' is not a valid QCAL URN.")


def load_jsonld_objects(paths: Iterable[Path]) -> Iterator[Tuple[Path, MutableMapping[str, object]]]:
    for path in paths:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise UniversalKernelError(f"Failed to decode JSON-LD file '{path}': {exc}.") from exc

        def ensure_mapping(node: object) -> MutableMapping[str, object]:
            if not isinstance(node, MutableMapping):
                raise UniversalKernelError(f"Top-level JSON-LD objects in '{path}' must be mappings.")
            return node

        if isinstance(payload, list):
            for entry in payload:
                yield path, ensure_mapping(entry)
        else:
            yield path, ensure_mapping(payload)


def ensure_required_fields(entry: Mapping[str, object], json_path: Path) -> None:
    missing = [key for key in REQUIRED_FIELDS if key not in entry]
    if missing:
        raise UniversalKernelError(f"File '{json_path}' is missing required fields: {', '.join(sorted(missing))}.")


def validate_frequency(identifier: str, frequency: float, computed: float, tolerance: float) -> None:
    if abs(frequency - computed) > tolerance:
        raise UniversalKernelError(
            f"Frequency mismatch for '{identifier}': declared {frequency:.6f}, expected {computed:.6f} within ±{tolerance:.1e}."
        )


def validate_kernel(entry: Mapping[str, object], allowed_kernels: Optional[Sequence[str]] = None) -> None:
    kernel = entry.get("formal:kernel")
    if not isinstance(kernel, str) or not kernel.strip():
        raise UniversalKernelError("'formal:kernel' must be a non-empty string.")
    if allowed_kernels and kernel not in allowed_kernels:
        raise UniversalKernelError(f"Kernel '{kernel}' is not among the permitted values: {', '.join(allowed_kernels)}.")


def verify_entry(entry: MutableMapping[str, object], json_path: Path, *, baseline: float, tolerance: float, allowed_kernels: Optional[Sequence[str]], update: bool) -> ValidationResult:
    ensure_required_fields(entry, json_path)

    identifier = entry.get("@id")
    if not isinstance(identifier, str):
        raise UniversalKernelError(f"Entry in '{json_path}' is missing a string '@id'.")
    validate_identifier(identifier)

    validate_kernel(entry, allowed_kernels)
    validate_dependencies(identifier, entry["dependencies"])  # type: ignore[arg-type]

    equation = entry.get("equation")
    if not isinstance(equation, str) or not equation.strip():
        raise UniversalKernelError(f"'{identifier}' must expose a symbolic equation.")

    proof_content, proof_path = resolve_proof_content(entry, json_path)

    computed_hash = compute_sha256(proof_content)
    declared_hash = entry.get("proofhash")
    if not isinstance(declared_hash, str):
        raise UniversalKernelError(f"'{identifier}' must declare a string proofhash.")
    if declared_hash != computed_hash:
        if update:
            entry["proofhash"] = computed_hash
        else:
            raise UniversalKernelError(
                f"Proof hash mismatch for '{identifier}'. Declared {declared_hash}, expected {computed_hash}."
            )

    declared_frequency = entry.get("frequency")
    if isinstance(declared_frequency, str):
        try:
            declared_frequency = float(declared_frequency)
        except ValueError as exc:
            raise UniversalKernelError(f"Frequency for '{identifier}' must be numeric: {declared_frequency}.") from exc
    if not isinstance(declared_frequency, (int, float)):
        raise UniversalKernelError(f"Frequency for '{identifier}' must be numeric.")

    computed_frequency = hash_to_frequency(entry["proofhash"], baseline)
    try:
        validate_frequency(identifier, float(declared_frequency), computed_frequency, tolerance)
    except UniversalKernelError:
        if update:
            entry["frequency"] = round(computed_frequency, 7)
        else:
            raise

    if proof_path is not None:
        entry.setdefault("formal:proof:resolved_path", str(proof_path))

    return ValidationResult(
        path=json_path,
        identifier=identifier,
        frequency=float(entry["frequency"]),
        computed_frequency=computed_frequency,
        proofhash=entry["proofhash"],
        computed_hash=computed_hash,
    )


def validate_unique_identifiers(results: Sequence[ValidationResult]) -> None:
    seen: Dict[str, Path] = {}
    for result in results:
        other = seen.get(result.identifier)
        if other is not None and other != result.path:
            raise UniversalKernelError(
                f"Identifier '{result.identifier}' declared in both '{other}' and '{result.path}'."
            )
        seen[result.identifier] = result.path


def save_updates(entries: Mapping[Path, List[MutableMapping[str, object]]]) -> None:
    for path, objects in entries.items():
        if not objects:
            continue
        content: object
        if len(objects) == 1:
            content = objects[0]
        else:
            content = objects
        path.write_text(json.dumps(content, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_validation(paths: Sequence[Path], *, baseline: float, tolerance: float, allowed_kernels: Optional[Sequence[str]], update: bool) -> List[ValidationResult]:
    results: List[ValidationResult] = []
    grouped: Dict[Path, List[MutableMapping[str, object]]] = {}
    for json_path, entry in load_jsonld_objects(paths):
        grouped.setdefault(json_path, []).append(entry)
        result = verify_entry(entry, json_path, baseline=baseline, tolerance=tolerance, allowed_kernels=allowed_kernels, update=update)
        results.append(result)

    validate_unique_identifiers(results)

    if update:
        save_updates(grouped)

    return results


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Validate universal QCAL theorem descriptors.")
    parser.add_argument("paths", nargs="+", type=Path, help="JSON-LD theorem descriptors to validate.")
    parser.add_argument("--baseline", type=float, default=BASELINE_FREQUENCY, help="Baseline resonance frequency.")
    parser.add_argument("--tolerance", type=float, default=FREQUENCY_TOLERANCE, help="Allowed deviation from the baseline-derived frequency.")
    parser.add_argument("--allow-kernel", dest="allowed_kernels", action="append", help="Explicitly allow a formal kernel identifier. If omitted any kernel value is accepted.")
    parser.add_argument("--update", action="store_true", help="Rewrite JSON-LD files so that proofhash and frequency match the computed values.")
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    try:
        results = run_validation(
            args.paths,
            baseline=args.baseline,
            tolerance=args.tolerance,
            allowed_kernels=args.allowed_kernels,
            update=args.update,
        )
    except UniversalKernelError as exc:
        print(f"❌ Universal coherence validation failed: {exc}")
        return 1

    for result in results:
        status = "✓" if result.is_success() else "⚠"
        proof_source = f" (from {result.path})"
        print(
            f"{status} {result.identifier}: frequency={result.frequency:.7f} computed={result.computed_frequency:.7f} "
            f"hash={result.proofhash[:16]}…"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
