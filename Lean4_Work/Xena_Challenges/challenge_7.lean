import Mathlib.Data.Rat.Defs

/-!
# Challenge 7: Proving whether there is a Rational Number whose Reciprocal is Zero

While the mathematical answer is surely not -- Lean's answer for the notation 1 / x where x : ℚ must be defined on all inputs, including zero denominator. In fact, 1 / 0 is defined as zero in Lean. Thus, we `use 0` and simplify to concluce that, indeed, there is a rational number whose reciprocal is zero.
-/

#eval (1 : ℚ) / 0 -- shows that the rational 1 / 0 is defined as zero in Lean

theorem reciprocal_is_zero : (∃ x : ℚ, 1 / x = 0) := by
  use 0
  rfl
