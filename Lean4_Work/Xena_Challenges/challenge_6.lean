import Mathlib.Data.Set.Basic
import MathLib.Tactic.Cases

/-!
# Challenge 6: Proving an Equivalence Class for an Equivalence Relation is Non-empty.

Idea:
- `Set.nonempty_iff_ne_empty` proves `s.Nonempty` iff `s ≠ ∅`
- Reflectivity `hR.refl` of the equivalence relation `hR` proves that `x ∈ Equivalence_class R x`
- `Set.nonempty_of_mem` proves `x ∈ s → s.Nonempty`
-/

def Equivalence_class {X : Type} (R : X → X → Prop) (x : X) := {y : X | R x y}

example (X : Type) (R : X → X → Prop) (hR : Equivalence R) (x : X) : Equivalence_class R x ≠ ∅ := by
  rw [<- Set.nonempty_iff_ne_empty]
  exact Set.nonempty_of_mem (hR.refl x)
