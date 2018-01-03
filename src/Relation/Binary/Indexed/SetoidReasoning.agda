------------------------------------------------------------------------
-- Convenient syntax for "equational reasoning" in multiple Indexed Setoids
------------------------------------------------------------------------

-- Example use:
--
--   open import Data.Maybe
--   import Relation.Binary.Indexed.SetoidReasoning as SetR
--
--   begin⟨ S ⟩
--     x
--       ≈⟨ drop-just (begin⟨ setoid S ⟩
--          just x
--            ≈⟨ justx≈mz ⟩
--          mz
--            ≈⟨ mz≈justy ⟩
--          just y ∎) ⟩
--     y
--       ≈⟨ y≈z ⟩
--     z ∎

open import Relation.Binary.Indexed.EqReasoning as EqR using (_IsRelatedTo_)
open import Relation.Binary.Indexed
open import Relation.Binary.Core using (_≡_)

open Setoid

module Relation.Binary.Indexed.SetoidReasoning where

infix 1 begin⟨_⟩_
infixr 2 _≈⟨_⟩_
infix 3 _∎

begin⟨_⟩_ : ∀ {𝒾 𝒸 ℓ} {I : Set 𝒾} (S : Setoid I 𝒸 ℓ) → {i j : I}
    → {x : Carrier S i} → {y : Carrier S j}
    → _IsRelatedTo_ S x y → _≈_ S x y
begin⟨_⟩_ S p = EqR.begin_ S p


_∎ :  ∀ {𝒾 𝒸 ℓ} {I : Set 𝒾} {S : Setoid I 𝒸 ℓ} → {i : I} → (x : Carrier S i)
    → _IsRelatedTo_ S x x
_∎ {S = S} = EqR._∎ S --EqR._∎ S

_≈⟨_⟩_ : ∀ {𝒾 𝒸 ℓ} {I : Set 𝒾} {S : Setoid I 𝒸 ℓ} → {i j k : I}
    → (x : Carrier S i) → {y : Carrier S j} → {z : Carrier S k}
    → _≈_ S x y → _IsRelatedTo_ S y z → _IsRelatedTo_ S x z
_≈⟨_⟩_ {S = S} = EqR._≈⟨_⟩_ S


-- _≡⟨_⟩_ : ∀ {𝒾 𝒸 ℓ} {I : Set 𝒾} {S : Setoid I 𝒸 ℓ} {i j : I}
--     → (x : Carrier S i) → {y : Carrier S i} → {z : Carrier S j}
--     → x ≡ y → _IsRelatedTo_ S y z → _IsRelatedTo_ S x z
-- _≡⟨_⟩_ {S = S} {i = i} {j = j} = {! EqR._≡⟨_⟩_ S {i = i} {j = i} {k = j}  !}
