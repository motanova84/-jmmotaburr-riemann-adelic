-- Test file to validate Lean 4 syntax correctness
-- This file should compile without errors if our syntax fixes are correct

import RiemannAdelic.axioms_to_lemmas
import RiemannAdelic.entire_order

-- Simple test to verify our axioms can be referenced
def test_axioms_available : Prop := 
  adelic_foundation

-- Test that we can reference the foundation
#check adelic_foundation

-- Test basic Lean 4 syntax
def simple_test : ℕ := 42

-- Test complex number operations (basic check that imports work)
def complex_test : ℂ := Complex.I

-- This file existing and having valid syntax indicates our fixes work