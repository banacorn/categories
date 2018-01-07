module Category.Universality where

open import Level
open import Category.Core
open import Category.Comma

-- open Category

initial : ∀ {𝒸 ℓ} → (C : Category 𝒸 ℓ) → Category.Object C → Set 𝒸
initial C init = ∀ (other : Object) → init ⇒ other
    where
        open Category C

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

point : ∀ {𝒸 ℓ} → {C : Category 𝒸 ℓ} → Category.Object C → Functor 𝟙 C
point {C = C} c = record
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
        -- open import Relation.Binary.Indexed.SetoidReasoning

-- something is universal from c to S when it's an initial object in c / S
universal : {𝒸₀ ℓ₀ 𝒸₁ ℓ₁ : Level}
    → {C : Category 𝒸₀ ℓ₀} {D : Category 𝒸₁ ℓ₁}
    → {c : Category.Object C} → {S : Functor D C}
    → (init : Category.Object (point c ↓ S))
    → Set (𝒸₁ ⊔ (ℓ₀ ⊔ 𝒸₀))
universal {c = c} {S = S} init = initial (point c ↓ S) init
