import Mathlib.Tactic

/-!
# Challenge 4: Proving if (g ∘ f) is Surjective, then so is g

The idea of the proof is to unfold the definition of Function.Surjective: introduce the hypothesis that g ∘ f is surjective and introduce a fixed output b.

Take a to be the guaranteed preimage to b under g ∘ f. Then (f a) is the preimage we're after for b under g.
-/

theorem challenge4 (X Y Z : Type) (f : X → Y) (g : Y → Z) : Function.Surjective (g ∘ f) → Function.Surjective g := by
  intro hb b
  obtain ⟨a, gfa⟩ := by apply hb b
  use f a
  exact gfa
