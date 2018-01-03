------------------------------------------------------------------------
-- Convenient syntax for "equational reasoning" using a indexed preorder
------------------------------------------------------------------------

open import Relation.Binary.Indexed.Extra

module Relation.Binary.Indexed.PreorderReasoning {𝒾} {I : Set 𝒾} {𝒸 ℓ₁ ℓ₂} (P : Preorder I 𝒸 ℓ₁ ℓ₂) where

open Preorder P

infix  4 _IsRelatedTo_
infix  1 begin_
infix  3 _∎
infixr 2 _∼⟨_⟩_ _≈⟨_⟩_ _≈⟨⟩_

data _IsRelatedTo_ {i j : I} (x : Carrier i) (y : Carrier j) : Set ℓ₂ where
    relTo : (x∼y : x ∼ y) → x IsRelatedTo y

begin_ : ∀ {i j : I} {x : Carrier i} {y : Carrier j} →  x IsRelatedTo y → x ∼ y
begin relTo x∼y = x∼y

_∼⟨_⟩_ : ∀ {i j k : I} → (x : Carrier i)
    → {y : Carrier j} {z : Carrier k}
    → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
_ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

_≈⟨_⟩_ : ∀ {i j k : I} → (x : Carrier i)
    → {y : Carrier j} {z : Carrier k}
    → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
_ ≈⟨ x≈y ⟩ relTo y∼z = relTo (trans (reflexive x≈y) y∼z)

_≈⟨⟩_ : ∀ {i j : I} → (x : Carrier i) → {y : Carrier j}
    → x IsRelatedTo y → x IsRelatedTo y
_ ≈⟨⟩ x∼y = x∼y

_∎ : ∀ {i : I} (x : Carrier i) → x IsRelatedTo x
_∎ _ = relTo refl
