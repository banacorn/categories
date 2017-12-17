module Category.Core where

open import Level
open import Data.Product
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

record Category {c ℓ : Level} : Set (suc (c ⊔ ℓ)) where
    infixr 9 _∘_
    field
        Object : Set c
        Morphism : Setoid (Object × Object) c ℓ
        _∘_ : ∀ {a b c : Object}
            → Setoid.Carrier Morphism (b , c)
            → Setoid.Carrier Morphism (a , b)
            → Setoid.Carrier Morphism (a , c)
        id : (a : Object) → Setoid.Carrier Morphism (a , a)
        isCategory : IsCategory Morphism _∘_ id

Opposite : {c ℓ : Level} → Category {c} {ℓ} → Category {c} {ℓ}
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
