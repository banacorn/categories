module Category.Instance where

open import Level
open import Category.Core

𝟙 : Category _ _
𝟙 = record
    { ObjectSetoid = record
        { Carrier = ⊤
        ; _≈_ = λ _ _ → ⊤
        ; isEquivalence = _
        }
    ; Morphism = record
        { Carrier = λ x → ⊤
        ; _≈_ = λ _ _ → ⊤
        ; isEquivalence = _
        ; _∘_ = λ _ _ → tt
        ; id = λ a → tt
        ; isMorphism = _
        }
    }
    where
        open import Data.Unit

-- "pointing" an element with a functor from 𝟙
point : ∀ {𝒸 ℓ} → {C : Category 𝒸 ℓ} → Category.Object C → Functor 𝟙 C
point {_} {_} {C} c = record
    { mapObject = λ _ → c
    ; mapMorphism = λ _ → id c
    ; isFunctor = record
        { preserve-id = λ a → MorphEq.refl
        ; preserve-∘ = λ _ _ → MorphEq.sym (left-identity (id c))
        }
    }
    where
        open Category C
        open import Relation.Binary.Indexed
        module MorphEq = IsEquivalence (MorphismStructure.isEquivalence Morphism)

        open IsMorphism isMorphism

-- the identity functo
identity : ∀ {𝒸 ℓ} → (C : Category 𝒸 ℓ) → Functor C C
identity C = record
    { mapObject = λ x → x
    ; mapMorphism = λ x → x
    ; isFunctor = record
        { preserve-id = λ a → MorphEq.refl
        ; preserve-∘ = λ f g → MorphEq.refl
        }
    }
    where
        open Category C
        open import Relation.Binary.Indexed
        module MorphEq = IsEquivalence (MorphismStructure.isEquivalence Morphism)

        open IsMorphism isMorphism
