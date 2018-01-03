------------------------------------------------------------------------
-- Extension The Agda standard library
--
-- Properties of indexed binary relations
------------------------------------------------------------------------

module Relation.Binary.Indexed.Extra where

open import Data.Product
open import Data.Sum
open import Function
open import Level
-- import Relation.Binary.PropositionalEquality.Core as PropEq
-- open import Relation.Binary.Consequences as Consequences
open import Relation.Binary.Core as Core using (_≡_)
open import Relation.Binary.Indexed.Core
open import Relation.Binary.Indexed
import Relation.Binary as B


------------------------------------------------------------------------
-- Simple properties and equivalence relations

-- open Core public hiding (_≡_; refl; _≢_)
--
-- open Consequences public using (Total)

------------------------------------------------------------------------
-- Simple properties of indexed binary relations

-- Implication/containment. Could also be written ⊆.
[_][_]_⇒_ : ∀ {i₁ i₂ a b ℓ₁ ℓ₂} {I₁ : Set i₁} {I₂ : Set i₂}
    (A : I₁ → Set a) (B : I₂ → Set b)
    → REL A B ℓ₁ → REL A B ℓ₂ → Set _
[ A ][ B ] P ⇒ Q = ∀ {i₁ i₂} {x : A i₁} {y : B i₂} → P x y → Q x y

-- _Preserves_⟶_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : A → Set b} →
--           ((x : A) → B x) → B.Rel A ℓ₁ → Rel B ℓ₂ → Set (ℓ₂ ⊔ (ℓ₁ ⊔ a))
-- f Preserves P ⟶ Q = P =[ f ]⇒ Q

_Respects_ : ∀ {𝒾 a ℓ₁ ℓ₂} {I : Set 𝒾} {A : I → Set a} {i : I}
    → (A i → Set ℓ₁) → Rel A ℓ₂ → Set (ℓ₂ ⊔ (ℓ₁ ⊔ a))
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y

[_]_Respects₂_ : ∀ {𝒾 a ℓ₁ ℓ₂} {I : Set 𝒾} (A : I → Set a)
    → Rel A ℓ₁ → Rel A ℓ₂ → Set (ℓ₂ ⊔ (ℓ₁ ⊔ (a ⊔ 𝒾)))
[ A ] P Respects₂ _∼_ =
      (∀ {i} {x : A i} → _Respects_ {A = A} {i = i} (P x) _∼_) ×
      (∀ {i} {y : A i} → _Respects_ {A = A} {i = i} (flip P y) _∼_)

------------------------------------------------------------------------
-- Preorders

record IsPreorder {𝒾 a ℓ₁ ℓ₂} {I : Set 𝒾} (A : I → Set a)
                  (_≈_ : Rel A ℓ₁) -- The underlying equality.
                  (_∼_ : Rel A ℓ₂) -- The relation.
                  : Set (𝒾 ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
        isEquivalence : IsEquivalence A _≈_
        -- Reflexivity is expressed in terms of an underlying equality:
        reflexive     : [ A ][ A ] _≈_ ⇒ _∼_
        trans         : Transitive A _∼_

    module Eq = IsEquivalence isEquivalence

    refl : Reflexive A _∼_
    refl = reflexive Eq.refl

    ∼-resp-≈ : [ A ] _∼_ Respects₂ _≈_
    ∼-resp-≈ = (λ x≈y z∼x → trans z∼x (reflexive x≈y))
           , (λ x≈y x∼z → trans (reflexive $ Eq.sym x≈y) x∼z)

record Preorder {i} (I : Set i) c ℓ₁ ℓ₂ : Set (suc (i ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where
    infix 4 _≈_ _∼_
    field
        Carrier    : I → Set c
        _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
        _∼_        : Rel Carrier ℓ₂  -- The relation.
        isPreorder : IsPreorder Carrier _≈_ _∼_

    open IsPreorder isPreorder public

SetoidIsPreorder : ∀ {𝒾} {I : Set 𝒾} {c ℓ} (S : Setoid I c ℓ) → IsPreorder (Setoid.Carrier S) (Setoid._≈_ S) (Setoid._≈_ S)
SetoidIsPreorder {𝒾} {I} S = record
    { isEquivalence = isEquivalence
    ; reflexive = id
    ; trans = IsEquivalence.trans isEquivalence
    }
    where
        open Setoid S

Setoid⇒Preorder : ∀ {𝒾} {I : Set 𝒾} {c ℓ} (S : Setoid I c ℓ) → Preorder I c ℓ ℓ
Setoid⇒Preorder S = record { isPreorder = SetoidIsPreorder S }
    -- record
    -- { Carrier = {!   !}
    -- ; _≈_ = {!   !}
    -- ; _∼_ = {!   !}
    -- ; isPreorder = {!   !}
    -- }

    -- IsEquivalence.reflexive (Setoid.isEquivalence S)
    -- where   open IsEquivalence {!   !}
    --
    -- isPreorder : IsPreorder _≡_ _≈_
    -- isPreorder = record
    --     { isEquivalence = PropEq.isEquivalence
    --     ; reflexive     = reflexive
    --     ; trans         = trans
    --     }
      --
      -- preorder : Preorder c c ℓ
      -- preorder = record { isPreorder = isPreorder }
