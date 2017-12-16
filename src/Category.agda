module Category where

open import Level
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Function using (flip)
open import Relation.Binary.Indexed

record IsCategory   {c ℓ : Level}
                    {Object : Set c}
                    (Morphism : Setoid (Object × Object) c ℓ)
                    (_∘_ : ∀ {a b c}
                        → Setoid.Carrier Morphism (b , c)
                        → Setoid.Carrier Morphism (a , b)
                        → Setoid.Carrier Morphism (a , c))
                    (id : (a : Object) → Setoid.Carrier Morphism (a , a))
                    : Set (suc (c ⊔ ℓ)) where
    open Setoid Morphism using (_≈_)
    _⇒_ = curry (Setoid.Carrier Morphism)
    field
        assoc : ∀ {a b c d : Object}
            → (f : a ⇒ b) → (g : b ⇒ c) → (h : c ⇒ d)
            → ((h ∘ g) ∘ f) ≈ (h ∘ (g ∘ f))
        ∘-left-identity : ∀ {a b : Object}
            → (f : a ⇒ b)
            → (id b ∘ f) ≈ f
        ∘-right-identity : ∀ {a b : Object}
            → (f : a ⇒ b)
            → (f ∘ id a) ≈ f

record Category : Set₁ where
    field
        Object : Set
        Morphism : Setoid (Object × Object) _ _
        _∘_ : ∀ {a b c : Object}
            → Setoid.Carrier Morphism (b , c)
            → Setoid.Carrier Morphism (a , b)
            → Setoid.Carrier Morphism (a , c)
        id : (a : Object) → Setoid.Carrier Morphism (a , a)
        isCategory : IsCategory Morphism _∘_ id

Opposite : Category → Category
Opposite C = record
    { Object = C.Object
    ; Morphism = record
        { Carrier = λ idx → M.Carrier (swap idx)
        ; _≈_ = λ f g → M._≈_ g f
        ; isEquivalence = record
            { refl = Eq.refl
            ; sym = Eq.sym
            ; trans = λ f g → Eq.trans g f
            }
        }
    ; _∘_ = λ f g → C._∘_ g f
    ; id = C.id
    ; isCategory = record
        { assoc = λ f g h → isC.assoc h g f
        ; ∘-left-identity = λ f → Eq.sym (isC.∘-right-identity f)
        ; ∘-right-identity = λ f → Eq.sym (isC.∘-left-identity f)
        }
    }
    where
        module C = Category C
        module M = Setoid C.Morphism
        module Eq = IsEquivalence M.isEquivalence
        module isC = IsCategory C.isCategory

module Test (C : Category) where

    open Category C

    infixr 9 _∘_
    infix 4 _≈_

    -- Arrows
    _⇒_ : Object → Object → Set
    _⇒_ = curry (Setoid.Carrier Morphism)

    -- Object Isomorphism
    _≅_ : (a b : Object) → Set
    a ≅ b = a ⇒ b × b ⇒ a

    -- Arrow Equivalence
    _≈_ : {a b : Object} → (f g : a ⇒ b) → Set
    _≈_ = Setoid._≈_ Morphism

    Initial : Object → Set
    Initial init = ∀ obj → init ⇒ obj

    Terminal : Object → Set
    Terminal term = ∀ obj → obj ⇒ term

    record IsProduct    (product fst snd : Object)
                        (π₁ : product ⇒ fst) (π₂ : product ⇒ snd)
                        (y : Object)
                        (f₁ : y ⇒ fst) (f₂ : y ⇒ snd)
                        : Set where
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
    record Product (product : Object) : Set₁ where
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
