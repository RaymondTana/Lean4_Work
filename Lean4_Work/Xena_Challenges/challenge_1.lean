/-!
# Challenge 1: Proving the Composite of Injective Functions is Injective.

The idea behind the proof is to introduce the terms and hypothesis in the definition of injectivity, then to apply the hypotheses of the theorem.
-/

variable {X Y Z : Type}

def injective (f : X → Y)  : Prop :=
  ∀ a b : X, f a = f b → a = b

theorem challenge1
  (f : X → Y) (hf : injective f)
  (g : Y → Z) (hg : injective g) :
injective (g ∘ f) := by
  intro a b hgf
  apply hf
  apply hg
  exact hgf
