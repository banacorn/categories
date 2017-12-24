open import Level
open import Category.Core

module Category {c ℓ : Level} (C : Category {c} {ℓ}) where

open import Data.Product
open import Relation.Binary.Indexed

open Category C

Initial : Object → Set c
Initial init = ∀ obj → init ⇒ obj

Terminal : Object → Set c
Terminal term = ∀ obj → obj ⇒ term

record IsProduct    (product fst snd : Object)
                    (π₁ : product ⇒ fst) (π₂ : product ⇒ snd)
                    (y : Object)
                    (f₁ : y ⇒ fst) (f₂ : y ⇒ snd)
                    : Set (suc (c ⊔ ℓ)) where
    field
        morphism : y ⇒ product
        commute₁ : f₁ ≈ π₁ ∘ morphism
        commute₂ : f₂ ≈ π₂ ∘ morphism


-- Product : Object → Set
-- Product prod =
--     Σ[ i ∈ Object ] Σ[ πᵢ ∈ prod ⇒ i ]
--     Σ[ j ∈ Object ] Σ[ πⱼ ∈ prod ⇒ j ]
--     ∀ (x : Object) (fᵢ : x ⇒ i) (fⱼ : x ⇒ j)
--     → Σ[ f ∈ x ⇒ prod ] (fᵢ ≈ πᵢ ∘ f × fⱼ ≈ πⱼ ∘ f)
record Product (product : Object) : Set (suc (c ⊔ ℓ)) where
    field
        fst snd : Object
        π₁ : product ⇒ fst
        π₂ : product ⇒ snd
        isProduct : ∀ y f₁ f₂ → IsProduct product fst snd π₁ π₂ y f₁ f₂

module Properties where

    -- Product-right-identity : (p : Object)
    --     → (proof : Product p)
    --     → Initial (Product.fst proof)
    --     → Product.fst proof ≅ p
    -- Product-right-identity p proof initial = initial p , Product.π₁ proof

    -- Terminal-unique : {p q : Object}
    --     → Terminal p → Terminal q
    --     → p ≅ q
    -- Terminal-unique {p} {q} p-term q-term = q-term p , p-term q
