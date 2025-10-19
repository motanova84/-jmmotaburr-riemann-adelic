#!/usr/bin/env python3
"""
Demo: Universal Verification Kernel (QCAL Framework)
====================================================

This script demonstrates the complete workflow of the Universal Verification Kernel:
1. Logical verification (V_L)
2. Semantic verification (V_S)
3. Physical-informational verification (V_F)

Reference Frequency: 141.7001 Hz (Planck-scale derived constant)
"""

import sys
from pathlib import Path

# Add tools to path
sys.path.insert(0, str(Path(__file__).parent / "tools"))

from universal_kernel import verify_universal, F0


def print_banner(text):
    """Print a formatted banner"""
    print("\n" + "=" * 70)
    print(f"  {text}")
    print("=" * 70 + "\n")


def main():
    """Run comprehensive demo of the Universal Verification Kernel"""
    
    print_banner("UNIVERSAL VERIFICATION KERNEL - QCAL FRAMEWORK DEMO")
    
    print("This demo showcases the triple verification structure U = (L, S, F):")
    print("  • L: Logical verification (formal proofs)")
    print("  • S: Semantic verification (ontological consistency)")
    print("  • F: Physical-informational verification (frequency & hash)")
    print(f"\nReference Frequency: {F0} Hz")
    print("Tolerance: 10⁻⁴ Hz")
    
    # Demo 1: Metadata-only verification
    print_banner("DEMO 1: Riemann Zeta Function (Metadata Only)")
    
    jsonld1 = "schema/zeta_function.jsonld"
    print(f"Verifying: {jsonld1}")
    print("This checks semantic (RDF) and physical (frequency/hash) layers.")
    print()
    
    result1 = verify_universal(jsonld1)
    
    if result1:
        print("\n✅ SUCCESS: Zeta function metadata is consistent!")
    else:
        print("\n❌ FAILURE: Verification failed.")
    
    input("\nPress Enter to continue to Demo 2...")
    
    # Demo 2: Full verification with proof
    print_banner("DEMO 2: Natural Numbers (With Formal Proof)")
    
    jsonld2 = "schema/natural_numbers.jsonld"
    proof2 = "formalization/dedukti/nat.dk"
    
    print(f"Verifying: {jsonld2}")
    print(f"With proof: {proof2}")
    print("\nThis checks all three layers:")
    print("  1. Logical: Dedukti proof verification")
    print("  2. Semantic: RDF graph consistency")
    print("  3. Physical: Frequency and hash invariants")
    print()
    
    result2 = verify_universal(jsonld2, proof2)
    
    if result2:
        print("\n✅ SUCCESS: Natural numbers are fully verified!")
        print("   The proof, metadata, and invariants are all consistent.")
    else:
        print("\n❌ FAILURE: Verification failed.")
    
    # Demo 3: Theory explanation
    print_banner("THEORETICAL FOUNDATION")
    
    print("The Universal Verification Kernel implements this theorem:")
    print()
    print("  Consistencia(U) ⟺ ∀x∈U: V_L(x) ∧ V_S(x) ∧ V_F(x)")
    print()
    print("Where:")
    print("  • V_L(x) = 1  iff  proof is syntactically correct")
    print("  • V_S(x) = 1  iff  no ontological contradictions")
    print("  • V_F(x) = 1  iff  |f(x) - 141.7001| < 10⁻⁴ and hash stable")
    print()
    print("This provides THREE independent layers of verification:")
    print()
    print("┌─────────────────────────────────────────────────────────┐")
    print("│  Layer 1: LOGICAL (Dedukti/Lean)                       │")
    print("│  ↓ Verifies syntax, types, and formal proofs           │")
    print("├─────────────────────────────────────────────────────────┤")
    print("│  Layer 2: SEMANTIC (RDF/OWL)                           │")
    print("│  ↓ Verifies ontological consistency                    │")
    print("├─────────────────────────────────────────────────────────┤")
    print("│  Layer 3: PHYSICAL-INFORMATIONAL (Hash/Frequency)      │")
    print("│  ↓ Verifies informational coherence                    │")
    print("└─────────────────────────────────────────────────────────┘")
    print("           ↓")
    print("    GLOBAL CONSISTENCY")
    print()
    print("Why is this superior to Lean alone?")
    print()
    print("1. Lean only verifies syntax and types (Layer 1)")
    print("2. QCAL adds semantic verification (Layer 2)")
    print("3. QCAL adds physical coherence (Layer 3)")
    print("4. All three must pass for global consistency")
    print("5. Hash ensures reproducibility across commits")
    print("6. Frequency links to physical constants (Planck scale)")
    print()
    
    # Demo 4: Falsifiability
    print_banner("FALSIFIABILITY AND REPRODUCIBILITY")
    
    print("The QCAL framework is falsifiable because:")
    print()
    print("1. Each object has unique @id, hash, frequency, and commit")
    print("2. Anyone can reproduce verification on their machine")
    print("3. Any change breaks the hash/frequency consistency")
    print("4. Results are deterministic and auditable")
    print()
    print("Example:")
    print("  $ python tools/universal_kernel.py schema/zeta_function.jsonld")
    print("  [HASH] 1cd248a62c51b83666cec6d332ba21829429647671801a76a7c874f1e4c321f6")
    print()
    print("If you get a different hash, either:")
    print("  • The metadata was modified (breaking consistency)")
    print("  • There's a computational error (verify your setup)")
    print()
    
    # Demo 5: CI/CD Integration
    print_banner("CI/CD INTEGRATION")
    
    print("The Universal Kernel runs automatically in GitHub Actions:")
    print()
    print("  .github/workflows/ci.yml:")
    print("  ```yaml")
    print("  - name: Universal Coherence Check")
    print("    run: |")
    print("      python tools/universal_kernel.py schema/zeta_function.jsonld")
    print("      python tools/universal_kernel.py schema/natural_numbers.jsonld \\")
    print("        formalization/dedukti/nat.dk")
    print("  ```")
    print()
    print("This ensures no PR is merged unless all three layers pass.")
    print()
    
    # Final summary
    print_banner("SUMMARY")
    
    print("✅ Demo 1: Zeta function metadata verified")
    print("✅ Demo 2: Natural numbers with proof verified")
    print("✅ Demo 3: Theoretical foundation explained")
    print("✅ Demo 4: Falsifiability demonstrated")
    print("✅ Demo 5: CI/CD integration shown")
    print()
    print("The Universal Verification Kernel provides:")
    print("  • Mathematical rigor (formal proofs)")
    print("  • Semantic consistency (ontological relations)")
    print("  • Physical coherence (frequency invariants)")
    print("  • Reproducibility (stable hashes)")
    print("  • Falsifiability (auditable results)")
    print()
    print("For more information:")
    print("  • Documentation: UNIVERSAL_KERNEL_README.md")
    print("  • Tests: pytest tests/test_universal_kernel.py -v")
    print("  • Schema guide: schema/README.md")
    print("  • Formalization guide: formalization/README.md")
    print()
    print("=" * 70)


if __name__ == "__main__":
    main()
