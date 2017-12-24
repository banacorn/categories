module Category.Core where

open import Level
open import Data.Product
-- open import Relation.Binary as B using ()
open import Relation.Binary.Indexed
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

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
    infix 4 _≈_
    field
        Object : Set c
        Morphism : Setoid (Object × Object) c (ℓ ⊔ c)
        _∘_ : ∀ {a b c : Object}
            → Setoid.Carrier Morphism (b , c)
            → Setoid.Carrier Morphism (a , b)
            → Setoid.Carrier Morphism (a , c)
        id : (a : Object) → Setoid.Carrier Morphism (a , a)
        isCategory : IsCategory Morphism _∘_ id

    -- Arrows
    _⇒_ : Object → Object → Set c
    _⇒_ = curry (Setoid.Carrier Morphism)

    -- -- Object Isomorphism
    -- _≅_ : (a b : Object) → Set c
    -- a ≅ b = a ⇒ b × b ⇒ a

    -- Arrow Equivalence
    _≈_ : {a b : Object} → (f g : a ⇒ b) → Set (ℓ ⊔ c)
    _≈_ = Setoid._≈_ Morphism

    hom[-,_] : Object → Set c
    hom[-, b ] = Σ[ a ∈ Object ] Setoid.Carrier Morphism (a , b)

record IsFunctor {c ℓ : Level} {C D : Category {c} {ℓ}}
    (mapObject : Category.Object C → Category.Object D)
    (mapMorphism : ∀ {a b}
            → (Category._⇒_ C) a b
            → (Category._⇒_ D) (mapObject a) (mapObject b))
    : Set (suc (c ⊔ ℓ)) where

    module C = Category C
    open Category D

    field
        preserve-id : (a : C.Object)
            → mapMorphism (C.id a) ≈ id (mapObject a)
        preserve-∘ : {a b c : C.Object}
            {f : a C.⇒ b} {g : b C.⇒ c}
            → (mapMorphism (C._∘_ g f)) ≈ mapMorphism g ∘ mapMorphism f

record Functor {c ℓ : Level} (C D : Category {c} {ℓ}) : Set (suc (c ⊔ ℓ)) where
    module C = Category C
    module D = Category D
    field
        mapObject : C.Object → D.Object
        mapMorphism : ∀ {a b} → a C.⇒ b → mapObject a D.⇒ mapObject b
        isFunctor : IsFunctor {c} {ℓ} {C} {D} mapObject mapMorphism


opposite : {c ℓ : Level} → Category {c} {ℓ} → Category {c} {ℓ}
opposite C = record
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

constant : ∀ {c ℓ}
    → (C : Category {c} {ℓ})
    → {D : Category {c} {ℓ}}
    → (d : Category.Object D) → Functor C D
constant C {D} d = record
    { mapObject = λ _ → d
    ; mapMorphism = λ _ → id d
    ; isFunctor = record
        { preserve-id = λ _ → Morphism.refl
        ; preserve-∘ = Morphism.sym (∘-right-identity (id d))
        }
    }
    where
        module C = Category C
        open Category D
        open IsCategory isCategory
        module Morphism = IsEquivalence (Setoid.isEquivalence Morphism)
