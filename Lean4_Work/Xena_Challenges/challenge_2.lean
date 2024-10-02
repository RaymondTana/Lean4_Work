import Mathlib.Data.Real.Basic

/-!
# Challenge 2: Proving a Set of Reals has at most one Supremum

The idea here is to think of the two parts of the definition of being a least upper bound: (1) being an upper bound and (2) being a lower bound to all upper bounds. The tactics below would help make this more clear:

```
  unfold is_lub at ha
  unfold is_least at ha
  -- ha.left : a ∈ upper_bounds S
  -- ha.right : a ∈ lower_bounds (upper_bounds S)
```
-/

-- basic definitions
def upper_bounds (S : Set ℝ) : Set ℝ := { b | ∀s ∈ S, s ≤ b }
def lower_bounds (S : Set ℝ) : Set ℝ := { b | ∀s ∈ S, b ≤ s }
def is_least (S : Set ℝ) (l : ℝ) : Prop := l ∈ S ∧ l ∈ lower_bounds S
def is_lub (S : Set ℝ) (l : ℝ) : Prop := is_least (upper_bounds S) l

theorem challenge2 (S : Set ℝ) (a b : ℝ) (ha : is_lub S a) (hb : is_lub S b) : a = b := by
  apply le_antisymm
  {
    apply ha.right
    exact hb.left
  }
  {
    apply hb.right
    exact ha.left
  }
