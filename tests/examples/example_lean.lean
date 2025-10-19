-- Ejemplo básico de formalización en Lean 4
-- Este es un archivo de ejemplo para demostrar el pipeline de conversión

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- Definición simple de una función
def double (n : ℕ) : ℕ := n + n

-- Teorema básico: el doble de un número es par
theorem double_is_even (n : ℕ) : Even (double n) := by
  use n
  rfl

-- Otro teorema simple
theorem double_zero : double 0 = 0 := by
  rfl

-- Definición de suma de primeros n números naturales
def sum_to (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => (n + 1) + sum_to n

-- Teorema sobre la suma
theorem sum_to_formula (n : ℕ) : 2 * sum_to n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [sum_to]
    ring_nf
    rw [ih]
    ring

-- Este archivo es un stub para demostrar el pipeline
-- En el proyecto real, aquí irían las formalizaciones de
-- teoremas relacionados con la Hipótesis de Riemann
