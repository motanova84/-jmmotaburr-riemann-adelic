# Schema Directory - QCAL Metadata

This directory contains JSON-LD metadata files for mathematical objects in the QCAL (Quantum Coherent Adelic Logic) framework.

## Purpose

Each JSON-LD file defines:
- **Identity**: Unique URN identifier
- **Semantics**: Title, description, dependencies
- **Formal Structure**: Associated axioms and theorems
- **Verification**: Provenance, hash, frequency

## Files

### zeta_function.jsonld

Metadata for the Riemann zeta function ζ(s).

**Key Properties**:
- Analytic continuation from Re(s) > 1
- Functional equation
- Euler product representation

### natural_numbers.jsonld

Metadata for the natural numbers ℕ with Peano axioms.

**Key Properties**:
- Zero constructor
- Successor function
- Mathematical induction

## JSON-LD Schema

All files follow this structure:

```json
{
  "@context": {
    "dc": "http://purl.org/dc/terms/",
    "formal": "http://qcal.org/formal#",
    "sem": "http://qcal.org/semantic#",
    "prov": "http://www.w3.org/ns/prov#",
    "hash": "http://qcal.org/hash#",
    "freq": "http://qcal.org/frequency#"
  },
  "@id": "urn:qcal:namespace:object",
  "@type": "MathematicalObject",
  "dc:title": "Object Title",
  "dc:description": "Detailed description",
  "formal:kernel": "Dedukti|LF|Lean",
  "formal:axioms": ["Axiom1", "Axiom2"],
  "sem:dependsOn": ["urn:qcal:dependency:1"],
  "sem:relatedTo": ["urn:qcal:related:1"],
  "prov:wasGeneratedBy": "motanova84/-jmmotaburr-riemann-adelic",
  "prov:generatedAtTime": "2025-10-19T18:00:00Z",
  "hash:sha256": "HEXHASH",
  "freq:Hz": 141.7001,
  "verification:status": "proven|axiomatized|conjectured",
  "verification:method": "method-name"
}
```

## Verification

All schemas are verified by the Universal Kernel:

```bash
# Verify metadata
python tools/universal_kernel.py schema/zeta_function.jsonld

# Verify with proof
python tools/universal_kernel.py schema/natural_numbers.jsonld formalization/dedukti/nat.dk
```

## Creating New Schemas

1. Create a new JSON-LD file following the template above
2. Ensure required fields are present: `@id`, `dc:title`
3. Set frequency to `141.7001` Hz (reference constant)
4. Run verification: `python tools/universal_kernel.py schema/your_file.jsonld`

## References

- JSON-LD: https://json-ld.org/
- RDF: https://www.w3.org/RDF/
- Dublin Core: http://purl.org/dc/terms/
- PROV-O: https://www.w3.org/TR/prov-o/
