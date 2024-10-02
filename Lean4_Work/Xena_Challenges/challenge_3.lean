import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Challenge 3: Proving 2 + 2 ≠ 5 for Reals

I make use of a few basic ways to deduce facts about equalities/inequalities between numbers in Lean4 with the help of the `mathlib4` library.

1. `contradiction`: only works for naturals, can simplify left and right hand sides of a comparison to verify it
2. `Eq.trans`: transitivity of equality: `a = b ∧ b = c → a = c`
3. `norm_num`: "normalizes numerical expressions", and makes use of the `simp` set of simplification tactics

I first show multiple proofs for how I'd solve this problem if it were about natural numbers, and then present two solutions for what the challenge really asks: reals.
-/

theorem nat_version_solution_1 : 2 + 2 ≠ 5 := by
  intro h -- name the goal as `h`
  let g : 4 = 2 + 2 := rfl -- reflection simplifies RHS before checking for match
  have : 4 = 5 := Eq.trans g h -- apply transitivity
  contradiction -- like reflection, has decision tactics for naturals

theorem nat_version_solution_2 : 2 + 2 ≠ 5 := by
  intro -- introduces 2 + 2 = 5
  contradiction -- contradiction is strong enough to do all the steps we already did in the previous proof

theorem nat_version_solution_3 : 2 + 2 ≠ 5 := by
  norm_num -- norm_num is also strong

theorem nat_version_solution_4 : 2 + 2 ≠ 5 := by
  simp -- simplifies arithmetic expressions on Nats

theorem challenge3_solution_1 : (2 : ℝ) + 2 ≠ 5 := by
  norm_num

theorem challenge3_solution_2 : (2 : ℝ) + 2 ≠ 5 := by
  intro h
  have g : 4 = (2 : ℝ) + 2 := by norm_num
  have : (4 : ℝ) = 5 := Eq.trans g h
  norm_num at this
