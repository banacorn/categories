module Category where

open import Level
open import Data.Product
open import Function using (flip)
open import Relation.Binary.PropositionalEquality
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
        compose : ∀ {a b c : Object}
            → Setoid.Carrier Morphism (b , c)
            → Setoid.Carrier Morphism (a , b)
            → Setoid.Carrier Morphism (a , c)
        id : (a : Object) → Setoid.Carrier Morphism (a , a)
        isCategory : IsCategory Morphism compose id


open Category
-- open IsCategory

Hom[_] : (C : Category) → Object C → Object C → Set
Hom[ C ] = curry (Setoid.Carrier (Morphism C))

-- _∘_ : {C : Category} {a b c : Object C} → Hom[ C ] b c → Hom[ C ] a b → Hom[ C ] a c
-- _∘_ {C} = compose C

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
    ; compose = λ f g → C.compose g f
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

Initial : {C : Category} → Object C → Set
Initial {C} init = ∀ obj → Hom[ C ] init obj

Terminal : {C : Category} → Object C → Set
Terminal {C} term = ∀ obj → Hom[ C ] obj term

Initial-Terminal-Opposite : {C : Category} {init : Object C}
    → Initial {C} init → Terminal {Opposite C} init
Initial-Terminal-Opposite proof = proof

record IsProduct    {C : Category}
                    (product fst snd : Object C)
                    (π₁ : Hom[ C ] product fst) (π₂ : Hom[ C ] product snd)
                    (y : Object C)
                    (f₁ : Hom[ C ] y fst) (f₂ : Hom[ C ] y snd)
                    : Set where
    _⇒_ = Hom[ C ]
    _∘_ = compose C
    field
        morphism : y ⇒ product
        commute₁ : f₁ ≡ π₁ ∘ morphism
        commute₂ : f₂ ≡ π₂ ∘ morphism

--
-- Product : {C : Category} → Object C → Set
-- Product {C} prod =
--     Σ[ i ∈ Object C ] Σ[ πᵢ ∈ prod ⇒ i ]
--     Σ[ j ∈ Object C ] Σ[ πⱼ ∈ prod ⇒ j ]
--     ∀ (x : Object C) (fᵢ : x ⇒ i) (fⱼ : x ⇒ j)
--     → Σ[ f ∈ x ⇒ prod ] (fᵢ ≡ πᵢ ∘ f × fⱼ ≡ πⱼ ∘ f)
record Product {C : Category} (product : Object C) : Set₁ where
    _⇒_ = Hom[ C ]
    _∘_ = compose C
    field
        fst snd : Object C
        π₁ : product ⇒ fst
        π₂ : product ⇒ snd
        isProduct : ∀ y f₁ f₂ → IsProduct {C} product fst snd π₁ π₂ y f₁ f₂
--
-- module Example where
--
--     open import Data.Unit
--     open import Data.Empty
--     open import Data.Bool
--     open import Algebra
--     open import Level
--     -- open import Relation.Binary.PropositionalEquality
--
--     --
--     --  false → true
--     --
--
--     two-morph : Bool → Bool → Set
--     two-morph true true = ⊤
--     two-morph true false = ⊥
--     two-morph false y = ⊤
--
--     two-∘ : {a b c : Bool}
--         → two-morph b c
--         → two-morph a b
--         → two-morph a c
--     two-∘ {true} {true} {c} b→c a→b = b→c
--     two-∘ {true} {false} {true} b→c a→b = tt
--     two-∘ {true} {false} {false} b→c a→b = a→b
--     two-∘ {false} {b} {c} b→c a→b = tt
--
--     two-id : {a : Bool} → two-morph a a
--     two-id {false} = tt
--     two-id {true} = tt
--
--     two-assoc :  {a b c d : Bool}
--         → (f : two-morph a b) (g : two-morph b c) (h : two-morph c d)
--         → two-∘ {a} {b} {d} (two-∘ {b} {c} {d} h g) f ≡ two-∘ {a} {c} {d} h (two-∘ {a} {b} {c} g f)
--     two-assoc {false} f g h = refl
--     two-assoc {true} {false} () g h
--     two-assoc {true} {true} {false} f g h = refl
--     two-assoc {true} {true} {true} f g h = refl
--
--     two-∘-left-identity : {a b : Bool} (f : two-morph a b) → two-∘ {a} (two-id {b}) f ≡ f
--     two-∘-left-identity {false} {b} tt = refl
--     two-∘-left-identity {true} {false} f = refl
--     two-∘-left-identity {true} {true} tt = refl
--
--     two-∘-right-identity : {a b : Bool} (f : two-morph a b) → two-∘ {a} f (two-id {a}) ≡ f
--     two-∘-right-identity {false} tt = refl
--     two-∘-right-identity {true} f = refl
--
--     two : Category
--     two = record
--         { Object = Bool
--         ; Morphism = two-morph
--         ; compose = λ {a} {b} {c} → two-∘ {a} {b} {c}
--         ; id = λ {a} → two-id {a}
--         ; isCategory = record
--             { assoc = λ {a} {b} {c} {d} → two-assoc {a} {b} {c} {d}
--             ; ∘-left-identity = λ {a} {b} → two-∘-left-identity {a} {b}
--             ; ∘-right-identity = λ {a} {b} → two-∘-right-identity {a} {b} }
--         }
