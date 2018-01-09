module Category.Universality where

open import Level
open import Category.Core
open import Category.Comma
open import Category.Instance

-- something is universal from c to S when it's an initial object in c / S
universal : {𝒸₀ ℓ₀ 𝒸₁ ℓ₁ : Level}
    → {C : Category 𝒸₀ ℓ₀} {D : Category 𝒸₁ ℓ₁}
    → {c : Category.Object C} → {S : Functor D C}
    → (init : Category.Object (point c ↓ S))
    → Set (𝒸₁ ⊔ (ℓ₀ ⊔ 𝒸₀))
universal {c = c} {S = S} init = initial (point c ↓ S) init
    where
        initial : ∀ {𝒸 ℓ} → (C : Category 𝒸 ℓ) → Category.Object C → Set 𝒸
        initial C init = ∀ (other : Object) → init ⇒ other
            where
                open Category C

initial : ∀ {𝒸 ℓ} (C : Category 𝒸 ℓ) → Category.Object C → Set (𝒸 ⊔ (ℓ ⊔ 𝒸))
initial C c = universal {C = C} {D = C} {c} {identity C} (record
        { source = tt
        ; target = c
        ; morphism = id c
        })
        where
            open import Data.Unit
            open Category C

-- initial-prop : ∀ {𝒸 ℓ} {C : Category 𝒸 ℓ}
--     → (init : Category.Object C)
--     → initial C init
--     → (other : Category.Object C)
--     → Category._⇒_ C init other
-- initial-prop {C = C} obj obj-init other = {!   !}
--     where
--         open Category C

-- prop1 : {!   !}
-- prop1 = {! initial  !}
