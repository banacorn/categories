module Category.Core where

open import Level
open import Data.Product
-- open import Relation.Binary as B using ()
open import Relation.Binary as B using ()
open import Relation.Binary.Indexed
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

record IsCategory   {𝒸 ℓ : Level}
                    {Object : Set 𝒸}
                    (MorphismSetoid : Setoid (Object × Object) 𝒸 ℓ)
                    (_∘_ : ∀ {a b c}
                        → Setoid.Carrier MorphismSetoid (b , c)
                        → Setoid.Carrier MorphismSetoid (a , b)
                        → Setoid.Carrier MorphismSetoid (a , c))
                    (id : (a : Object) → Setoid.Carrier MorphismSetoid (a , a))
                    : Set (suc (𝒸 ⊔ ℓ)) where
    open Setoid MorphismSetoid using (_≈_)
    _⇒_ = curry (Setoid.Carrier MorphismSetoid)
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

record Category {𝒸 ℓ : Level} : Set (suc (𝒸 ⊔ ℓ)) where
    infixr 9 _∘_
    infix 4 _≈_

    field
        ObjectSetoid : B.Setoid 𝒸 ℓ

    Object : Set 𝒸
    Object = B.Setoid.Carrier ObjectSetoid

    _≈o_ : Object → Object → Set ℓ
    _≈o_ = B.Setoid._≈_ ObjectSetoid

    field
        MorphismSetoid : Setoid (Object × Object) 𝒸 ℓ

    -- Arrows
    _⇒_ : Object → Object → Set 𝒸
    _⇒_ = curry (Setoid.Carrier MorphismSetoid)

    field
        _∘_ : ∀ {a b c : Object}
            → b ⇒ c
            → a ⇒ b
            → a ⇒ c
        id : (a : Object) → a ⇒ a
        isCategory : IsCategory MorphismSetoid _∘_ id


    -- Arrow Equivalence
    -- [_]_≈_[_] : {a b a' b' : Object} → a  a' → a ⇒ b → a' ⇒ b' → b ≡ b' → Set ℓ
    -- [ refl ] a→b ≈ a'→b' [ refl ] = a→b ≈ a'→b'

    _≈_ : {a b a' b' : Object} → (f : a ⇒ b) → (g : a' ⇒ b') → Set ℓ
    _≈_ = Setoid._≈_ MorphismSetoid

    hom[-,_] : Object → Set 𝒸
    hom[-, b ] = Σ[ a ∈ Object ] a ⇒ b

    -- hom[_,_] : Object → Object → Set 𝒸
    -- hom[ a , b ] = a ⇒ b

record IsFunctor {𝒸 ℓ : Level} {C D : Category {𝒸} {ℓ}}
    (mapObject : Category.Object C → Category.Object D)
    (mapMorphism : ∀ {a b}
            → (Category._⇒_ C) a             b
            → (Category._⇒_ D) (mapObject a) (mapObject b))
    : Set (suc (𝒸 ⊔ ℓ)) where

    module C = Category C
    open Category D

    field
        preserve-id : (a : C.Object)
            → mapMorphism (C.id a) ≈ id (mapObject a)
        preserve-∘ : {a b c : C.Object} {f : a C.⇒ b} {g : b C.⇒ c}
            → mapMorphism (C._∘_ g f) ≈ mapMorphism g ∘ mapMorphism f

record Functor {𝒸 ℓ : Level} (C D : Category {𝒸} {ℓ}) : Set (suc (𝒸 ⊔ ℓ)) where
    module C = Category C
    module D = Category D
    field
        mapObject : C.Object → D.Object
        mapMorphism : ∀ {a b} → a C.⇒ b → mapObject a D.⇒ mapObject b
        isFunctor : IsFunctor {𝒸} {ℓ} {C} {D} mapObject mapMorphism

--
-- opposite : {𝒸 ℓ : Level} → Category {c} {ℓ} → Category {c} {ℓ}
-- opposite C = record
--     { Object = C.Object
--     ; Morphism = record
--         { Carrier = λ idx → M.Carrier (swap idx)
--         ; _≈_ = λ f g → M._≈_ g f
--         ; isEquivalence = record
--             { refl = Eq.refl
--             ; sym = Eq.sym
--             ; trans = λ f g → Eq.trans g f
--             }
--         }
--     ; _∘_ = λ f g → C._∘_ g f
--     ; id = C.id
--     ; isCategory = record
--         { assoc = λ f g h → isC.assoc h g f
--         ; ∘-left-identity = λ f → Eq.sym (isC.∘-right-identity f)
--         ; ∘-right-identity = λ f → Eq.sym (isC.∘-left-identity f)
--         }
--     }
--     where
--         module C = Category C
--         module M = Setoid C.Morphism
--         module Eq = IsEquivalence M.isEquivalence
--         module isC = IsCategory C.isCategory
--
-- constant : ∀ {𝒸 ℓ}
--     → (C : Category {c} {ℓ})
--     → {D : Category {c} {ℓ}}
--     → (d : Category.Object D) → Functor C D
-- constant C {D} d = record
--     { mapObject = λ _ → d
--     ; mapMorphism = λ _ → id d
--     ; isFunctor = record
--         { preserve-id = λ _ → Morphism.refl
--         ; preserve-∘ = Morphism.sym (∘-right-identity (id d))
--         }
--     }
--     where
--         module C = Category C
--         open Category D
--         open IsCategory isCategory
--         module Morphism = IsEquivalence (Setoid.isEquivalence Morphism)
