import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Challenge 5: Proving Sum of First n positive odd numbers is n^2

This problem is naturally provable by induction. The key ingredients provided by Lean in order to resolve the successor case include:
- `Finset.range`: a tactic for producing a list of the form {0, ..., n - 1}
- `Finset.sum`: a tactic for summing terms given a function defined on a `Finset.range`
- `Finset.sum_range_succ`: a tactic for rewriting a sum that ends at a successor instead as the sum of indices before that successor plus the term from the successor
- `ring`: a tactic which simplifies and proves identities that involve addition, multiplication, and exponentiation in commutative rings
-/

-- demonstrate how Finset.sum_range_succ works
example : ∑ x in Finset.range 5, (x + 1) = 15 := by
  simp [Finset.sum_range_succ]

-- the n'th odd number (start counting at zero)
def odd (n : ℕ) := 2 * n + 1

theorem challenge5 (n : ℕ) : (Finset.range n).sum (odd) = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n' ih => rw [Finset.sum_range_succ, ih, odd]; ring
