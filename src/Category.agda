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

    Product-right-identity : (p : Object)
        → (proof : Product p)
        → Initial (Product.fst proof)
        → Product.fst proof ≅ p
    Product-right-identity p proof initial = initial p , Product.π₁ proof

    Terminal-unique : {p q : Object}
        → Terminal p → Terminal q
        → p ≅ q
    Terminal-unique {p} {q} p-term q-term = q-term p , p-term q

-- -- module Example where
-- --
-- --     open import Data.Unit
-- --     open import Data.Empty
-- --     open import Data.Bool
-- --     open import Algebra
-- --     open import Level
-- --     -- open import Relation.Binary.PropositionalEquality
-- --
-- --     --
-- --     --  false → true
-- --     --
-- --
-- --     two-morph : Bool → Bool → Set
-- --     two-morph true true = ⊤
-- --     two-morph true false = ⊥
-- --     two-morph false y = ⊤
-- --
-- --     two-∘ : {a b c : Bool}
-- --         → two-morph b c
-- --         → two-morph a b
-- --         → two-morph a c
-- --     two-∘ {true} {true} {c} b→c a→b = b→c
-- --     two-∘ {true} {false} {true} b→c a→b = tt
-- --     two-∘ {true} {false} {false} b→c a→b = a→b
-- --     two-∘ {false} {b} {c} b→c a→b = tt
-- --
-- --     two-id : {a : Bool} → two-morph a a
-- --     two-id {false} = tt
-- --     two-id {true} = tt
-- --
-- --     two-assoc :  {a b c d : Bool}
-- --         → (f : two-morph a b) (g : two-morph b c) (h : two-morph c d)
-- --         → two-∘ {a} {b} {d} (two-∘ {b} {c} {d} h g) f ≡ two-∘ {a} {c} {d} h (two-∘ {a} {b} {c} g f)
-- --     two-assoc {false} f g h = refl
-- --     two-assoc {true} {false} () g h
-- --     two-assoc {true} {true} {false} f g h = refl
-- --     two-assoc {true} {true} {true} f g h = refl
-- --
-- --     two-∘-left-identity : {a b : Bool} (f : two-morph a b) → two-∘ {a} (two-id {b}) f ≡ f
-- --     two-∘-left-identity {false} {b} tt = refl
-- --     two-∘-left-identity {true} {false} f = refl
-- --     two-∘-left-identity {true} {true} tt = refl
-- --
-- --     two-∘-right-identity : {a b : Bool} (f : two-morph a b) → two-∘ {a} f (two-id {a}) ≡ f
-- --     two-∘-right-identity {false} tt = refl
-- --     two-∘-right-identity {true} f = refl
-- --
-- --     two : Category
-- --     two = record
-- --         { Object = Bool
-- --         ; Morphism = two-morph
-- --         ; compose = λ {a} {b} {c} → two-∘ {a} {b} {c}
-- --         ; id = λ {a} → two-id {a}
-- --         ; isCategory = record
-- --             { assoc = λ {a} {b} {c} {d} → two-assoc {a} {b} {c} {d}
-- --             ; ∘-left-identity = λ {a} {b} → two-∘-left-identity {a} {b}
-- --             ; ∘-right-identity = λ {a} {b} → two-∘-right-identity {a} {b} }
-- --         }
