module Category.Comma where

open import Level
open import Data.Product
open import Category.Core
open import Relation.Binary.Indexed
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

_/_ : ∀ {c ℓ} → (C : Category {c} {ℓ}) → (b : Category.Object C) → Category {c} {ℓ}
_/_ {c} {ℓ} C b = record
    { Object = hom[-, b ]
    ; Morphism = Slice-Morphism
    ; _∘_ = Slice-∘
    ; id = Slice-id
    ; isCategory = Slice-isCategory
    }
    where
        open Category C
        module MorphEq = IsEquivalence (Setoid.isEquivalence Morphism)

        record SliceMorphism (dom-cod : hom[-, b ] × hom[-, b ]) : Set c where
            field
                morphism : proj₁ (proj₁ dom-cod) ⇒ proj₁ (proj₂ dom-cod)

            domain : Object
            domain = proj₁ (proj₁ dom-cod)

            codomain : Object
            codomain = proj₁ (proj₂ dom-cod)


        _≈_[_,_] : {a b a' b' : hom[-, b ]}
            → (f : SliceMorphism (a , b)) → (g : SliceMorphism (a' , b'))
            → SliceMorphism.domain f ≡ SliceMorphism.domain g
            → SliceMorphism.codomain f ≡ SliceMorphism.codomain g
            → Set (ℓ ⊔ c)
        f ≈ g [ refl , refl ] = morphism f ≈ morphism g
            where   open SliceMorphism

        eq : Rel SliceMorphism (ℓ ⊔ c)
        eq f g = Σ[ dom-≡ ∈ domain f ≡ domain g ]
            Σ[ cod-≡ ∈ codomain f ≡ codomain g ]
            (f ≈ g [ dom-≡ , cod-≡ ])
            where   open SliceMorphism

        eq-Symmetric : Symmetric SliceMorphism eq
        eq-Symmetric (refl , refl , i≈j) = refl , refl , (MorphEq.sym i≈j)

        eq-Transitive : Transitive SliceMorphism eq
        eq-Transitive (refl , refl , i≈j) (refl , refl , j≈k)
            = refl , refl , MorphEq.trans i≈j j≈k

        eq-isEquivalence : IsEquivalence SliceMorphism eq
        eq-isEquivalence = record
            { refl = refl , (refl , MorphEq.refl)
            ; sym = eq-Symmetric
            ; trans = eq-Transitive
            }

        Slice-Morphism : Setoid (hom[-, b ] × hom[-, b ]) c (ℓ ⊔ c)
        Slice-Morphism = record
            { Carrier = SliceMorphism
            ; _≈_ = eq
            ; isEquivalence = eq-isEquivalence
            }

        Slice-∘ : ∀ {a b c}
            → SliceMorphism (b , c)
            → SliceMorphism (a , b)
            → SliceMorphism (a , c)
        Slice-∘ f g = record { morphism = morphism f ∘ morphism g }
            where   open SliceMorphism

        Slice-id : ∀ a → SliceMorphism (a , a)
        Slice-id (a , _) = record { morphism = id a }

        Slice-isCategory : IsCategory Slice-Morphism Slice-∘ Slice-id
        Slice-isCategory = record
            { assoc = λ f g h → refl , refl , assoc (morphism f) (morphism g) (morphism h)
            ; ∘-left-identity = λ f → refl , refl , ∘-left-identity (morphism f)
            ; ∘-right-identity = λ f → refl , refl , ∘-right-identity (morphism f)
            }
            where
                open IsCategory isCategory
                open SliceMorphism

--     S     T
--  C --> E <-- D
--
_↓_ : ∀ {𝒸 ℓ} → {C D E : Category {𝒸} {ℓ}}
    → (S : Functor C E) → (T : Functor D E)
    → Category {𝒸 ⊔ ℓ} {ℓ}
_↓_ {𝒸} {ℓ} {C} {D} {E} S T = record
    { Object = CommaObject
    ; Morphism = morphism
    ; _∘_ = {!   !}
    ; id = {!   !}
    ; isCategory = {!   !}
    }
    where
        module C = Category C
        module D = Category D
        module S = Functor S
        module T = Functor T
        open Category E


        record CommaObject : Set (𝒸 ⊔ ℓ) where
            field
                source : C.Object
                target : D.Object
                morphism : hom[ S.mapObject source , T.mapObject target ]

        record CommaMorphism (src : CommaObject) (tar : CommaObject) : Set (𝒸 ⊔ ℓ) where
            module SRC = CommaObject src
            module TAR = CommaObject tar
            field
                morphismBetweenSources : hom[ S.mapObject SRC.source , S.mapObject TAR.source ]
                morphismBetweenTargets : hom[ T.mapObject SRC.target , T.mapObject TAR.target ]
                commutes : TAR.morphism ∘ morphismBetweenSources ≈ morphismBetweenTargets ∘ SRC.morphism

        -- _≈_[_,_,_,_] : {f-src f-tar g-tar g-src : CommaObject}
        --     → (f : CommaMorphism f-src f-tar) → (g : CommaMorphism g-tar g-src)
        --     → CommaObject.source f-src ≡ CommaObject.source g-src
        --     → CommaObject.source f-tar ≡ CommaObject.source g-tar
        --     → CommaObject.target f-src ≡ CommaObject.target g-src
        --     → CommaObject.target f-tar ≡ CommaObject.target g-tar
        --     → Set {!   !}
        -- f ≈ g [ a , b , c , d ] = {! b  !}

        Morphism-≈ : Rel (uncurry CommaMorphism) (ℓ ⊔ 𝒸)
        Morphism-≈ {f-src , f-tar} {g-src , g-tar} f g = {!   !}

        morphism : Setoid (CommaObject × CommaObject) (𝒸 ⊔ ℓ) (𝒸 ⊔ ℓ)
        morphism = record
            { Carrier = uncurry CommaMorphism
            ; _≈_ = Morphism-≈
            ; isEquivalence = {!   !}
            }
