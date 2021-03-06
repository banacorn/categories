module Category.Core where

open import Level
open import Data.Product
-- open import Relation.Binary as B using ()
open import Relation.Binary as B using ()
open import Relation.Binary.Indexed
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

record IsMorphism   {𝒸 ℓ : Level}
                    {Object : Set 𝒸}
                    {Carrier : (Object × Object) → Set 𝒸}
                    (_≈_ : Rel Carrier ℓ)
                    (_∘_ : ∀ {a b c} → Carrier (b , c) → Carrier (a , b) → Carrier (a , c))
                    (id : (a : Object) → Carrier (a , a))
                    : Set (suc (𝒸 ⊔ ℓ)) where
    _⇒_ = curry Carrier
    field
        assoc : ∀ {a b c d : Object}
            → (f : a ⇒ b) → (g : b ⇒ c) → (h : c ⇒ d)
            → ((h ∘ g) ∘ f) ≈ (h ∘ (g ∘ f))
        left-identity : ∀ {a b : Object}
            → (f : a ⇒ b)
            → (id b ∘ f) ≈ f
        right-identity : ∀ {a b : Object}
            → (f : a ⇒ b)
            → (f ∘ id a) ≈ f
        cong : ∀ {a b c a' b' c' : Object}
            {x : Carrier (b , c)} {y : Carrier (b' , c')}
            {u : Carrier (a , b)} {v : Carrier (a' , b')}
            → x ≈ y → u ≈ v → (x ∘ u) ≈ (y ∘ v)

record MorphismStructure (𝒸 ℓ : Level) (Object : Set 𝒸) : Set (suc (𝒸 ⊔ ℓ)) where
    infixr 9 _∘_
    infix 4 _≈_
    field
        Carrier : (Object × Object) → Set 𝒸
        _≈_ : Rel Carrier ℓ
        isEquivalence : IsEquivalence Carrier _≈_

    setoid : Setoid (Object × Object) _ _
    setoid = record { isEquivalence = isEquivalence }

    -- Arrows
    _⇒_ : Object → Object → Set 𝒸
    _⇒_ = curry Carrier

    field
        _∘_ : ∀ {a b c : Object}
            → b ⇒ c
            → a ⇒ b
            → a ⇒ c
        id : (a : Object) → a ⇒ a
        isMorphism : IsMorphism _≈_ _∘_ id


record Category (𝒸 ℓ : Level) : Set (suc (𝒸 ⊔ ℓ)) where

    field
        Objects : B.Setoid 𝒸 ℓ

    Object : Set 𝒸
    Object = B.Setoid.Carrier Objects

    _≈o_ : Object → Object → Set ℓ
    _≈o_ = B.Setoid._≈_ Objects

    field
        Morphisms : MorphismStructure 𝒸 ℓ Object

    open MorphismStructure Morphisms public

    hom[-,_] : Object → Set 𝒸
    hom[-, b ] = Σ[ a ∈ Object ] a ⇒ b

    -- hom[_,_] : Object → Object → Set 𝒸
    -- hom[ a , b ] = a ⇒ b

record IsFunctor {𝒸₀ ℓ₀ 𝒸₁ ℓ₁ : Level}
    {C : Category 𝒸₀ ℓ₀} {D : Category 𝒸₁ ℓ₁}
    (mapObject : Category.Object C → Category.Object D)
    (mapMorphism : ∀ {a b}
            → (Category._⇒_ C) a             b
            → (Category._⇒_ D) (mapObject a) (mapObject b))
    : Set (𝒸₀ ⊔ ℓ₀ ⊔ 𝒸₁ ⊔ ℓ₁) where

    module C = Category C
    open Category D

    field
        preserve-id : (a : C.Object)
            → mapMorphism (C.id a) ≈ id (mapObject a)
        preserve-∘ : {a b c : C.Object} (f : a C.⇒ b) (g : b C.⇒ c)
            → mapMorphism (C._∘_ g f) ≈ mapMorphism g ∘ mapMorphism f


record Functor {𝒸₀ ℓ₀ 𝒸₁ ℓ₁ : Level}
    (C : Category 𝒸₀ ℓ₀) (D : Category 𝒸₁ ℓ₁) : Set (𝒸₀ ⊔ ℓ₀ ⊔ 𝒸₁ ⊔ ℓ₁) where
    module C = Category C
    module D = Category D
    field
        mapObject : C.Object → D.Object
        mapMorphism : ∀ {a b} → a C.⇒ b → mapObject a D.⇒ mapObject b
        isFunctor : IsFunctor {𝒸₀} {ℓ₀} {𝒸₁} {ℓ₁} {C} {D} mapObject mapMorphism
