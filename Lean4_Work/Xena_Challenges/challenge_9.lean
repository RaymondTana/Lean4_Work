import Mathlib.Data.Set.Basic

variable (R A : Type)
variable (𝕍 : Set R → Set A) (𝕀 : Set A → Set R)

-- 𝕍 𝕀 𝕍 = 𝕍 for a contravariant Galois connection
-- for example the one between R=k[X₁,X₂,…,Xₙ] and A=𝔸ⁿ
-- in the theory of algebraic varieties

-- my first proof
example
  (𝕍_antimono : ∀ J₁ J₂ : Set R, J₁ ⊆ J₂ → 𝕍 J₂ ⊆ 𝕍 J₁)
  (𝕀_antimono : ∀ W₁ W₂ : Set A, W₁ ⊆ W₂ → 𝕀 W₂ ⊆ 𝕀 W₁)
  (galois : ∀ J : Set R, ∀ W : Set A, J ⊆ 𝕀 W ↔ W ⊆ 𝕍 J) :
  ∀ J : Set R, 𝕍 (𝕀 (𝕍 J)) = 𝕍 J := by

    -- work with explicit J rather than doing universal quantification
    intro J

    -- split into ⊆ and ⊇ cases
    apply Set.Subset.antisymm
    {
      apply (𝕍_antimono J (𝕀 (𝕍 J))) -- antimonotonicity of 𝕍 implies the 𝕍 (𝕀 (𝕍 J)) ⊆ 𝕍 J
      apply (galois J (𝕍 J)).mpr -- treating W := 𝕍 J and J := 𝕍 J in LHS of galois, reduce to RHS, which merely asks 𝕍 J ⊆ 𝕍 J
      rfl -- obvious
    }
    {
      apply (galois (𝕀 (𝕍 J)) (𝕍 J)).mp -- use forward direction of galois to simplify
      apply (𝕀_antimono (𝕍 J) (𝕍 J)) -- use antimonotonicity of 𝕀 to simplify
      rfl -- obvious
    }

-- alternate proof: turns out 𝕀_antimono isn't necessary!
example
  (𝕍_antimono : ∀ J₁ J₂ : Set R, J₁ ⊆ J₂ → 𝕍 J₂ ⊆ 𝕍 J₁)
  (𝕀_antimono : ∀ W₁ W₂ : Set A, W₁ ⊆ W₂ → 𝕀 W₂ ⊆ 𝕀 W₁)
  (galois : ∀ J : Set R, ∀ W : Set A, J ⊆ 𝕀 W ↔ W ⊆ 𝕍 J) :
  ∀ J : Set R, 𝕍 (𝕀 (𝕍 J)) = 𝕍 J := by
    intro J
    apply Set.Subset.antisymm
    {
      apply (𝕍_antimono J (𝕀 (𝕍 J)))
      rw [galois]
    }
    {
      rw [←galois]
    }
