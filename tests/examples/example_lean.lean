-- Example Lean 4 file for testing converter
-- This is a minimal example for CI validation

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic

-- Example theorem: basic property
theorem example_property (x : ℝ) (h : x > 0) : x + 1 > 1 := by
  linarith

-- Example definition
def critical_line (s : ℂ) : Prop :=
  s.re = 1/2

-- Example lemma
lemma critical_line_symmetric (s : ℂ) :
  critical_line s → critical_line (Complex.conj s) := by
  intro h
  unfold critical_line at *
  simp [Complex.conj_re, h]
