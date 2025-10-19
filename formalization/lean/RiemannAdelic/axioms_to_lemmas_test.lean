-- Test file for axioms_to_lemmas.lean
-- Ensures that all axioms and lemmas compile correctly

import RiemannAdelic.axioms_to_lemmas

open RiemannAdelic

-- Test that axioms are properly declared
#check A1_finite_scale_flow
#check A2_poisson_adelic_symmetry
#check A4_spectral_regularity

-- Test that foundation definition compiles
#check adelic_foundation

-- Test that proof sketches compile
#check A1_proof_sketch
#check A2_proof_sketch  
#check A4_proof_sketch

-- Test main consistency theorem
#check adelic_foundation_consistent

-- Print success message
#eval IO.println "✅ All axioms_to_lemmas declarations compile successfully!"