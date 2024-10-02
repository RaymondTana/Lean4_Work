import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Basic
/-!
# Challenge 8:  Proving (ghk^{-1})^{-1} = kh^{-1}g^{-1}.

This can be done in many ways. The simplest is to appeal to the `group` tactic that can simplify expressions like these automatically.

More explicitly, one may rewrite according to some standard rules:
- `mul_inv_rev` for the fact that (a b)⁻¹ = b⁻¹ a⁻¹
- `inv_inv` for the fact that (a⁻¹)⁻¹ = a
- `mul_assoc` for the fact that group multiplication is associative

Other lemmas that may have been useful in other solutions could include:
- `one_mul` for the fact that 1 * a = a
- `mul_one` for the fact that a * 1 = a
- `inv_mul_cancel` for the fact that a⁻¹ * a = 1
- `mul_inv_cancel` for the fact that a * a⁻¹ = 1
- `inv_mul_cancel_right` for the fact that a * b⁻¹ * b = a
- `mul_inv_cancel_right` for the fact that a * b * b⁻¹ = a
etc.
-/

theorem challenge8_solution_1 (G : Type) [Group G] (g h k : G) : (g * h * k⁻¹)⁻¹ = k * h⁻¹ * g⁻¹ := by
  group

theorem challenge8_solution_2 (G : Type) [Group G] (g h k : G) : (g * h * k⁻¹)⁻¹ = k * h⁻¹ * g⁻¹ := by
  rw [mul_inv_rev, inv_inv, mul_inv_rev, mul_assoc]
