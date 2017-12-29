module Category.Comma where

open import Level
open import Data.Product
open import Category.Core
open import Relation.Binary as B using ()
open import Relation.Binary.Indexed
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

_/_ : ∀ {𝒸 ℓ} → (C : Category {𝒸} {ℓ}) → (b : Category.Object C) → Category {𝒸} {ℓ}
_/_ {𝒸} {ℓ} C b = record
    { ObjectSetoid = SliceObjectSetoid -- SliceObjectSetoid
    ; MorphismSetoid = SliceMorphismSetoid -- SliceMorphismSetoid
    ; _∘_ = Slice-∘
    ; id = Slice-id
    ; isCategory = Slice-isCategory
    }
    where
        open Category C
        module ObjEq = B.IsEquivalence (B.Setoid.isEquivalence ObjectSetoid)
        module MorphEq = IsEquivalence (Setoid.isEquivalence MorphismSetoid)

        -- -- a device for unifying the source of arrows
        -- -- so that we can compare them with _≈_
        -- _≈_[_] : ∀ {x y} → x ⇒ b → y ⇒ b → x ≡ y → Set ℓ
        -- x→b ≈ y→b [ refl ] = x→b ≈ y→b

        SliceObject-≈ : B.Rel hom[-, b ] ℓ
        SliceObject-≈ (x , x→b) (y , y→b) = Σ[ x≈y ∈ x ≈o y ] x→b ≈ y→b

        SliceObject-≈-Symmetric : B.Symmetric SliceObject-≈
        SliceObject-≈-Symmetric (≈src , f≈g) = (ObjEq.sym ≈src) , MorphEq.sym f≈g

        SliceObject-≈-Transitive : B.Transitive SliceObject-≈
        SliceObject-≈-Transitive (≈src₁ , f≈g) (≈src₂ , g≈h) =
            (ObjEq.trans ≈src₁ ≈src₂) , (MorphEq.trans f≈g g≈h)

        SliceObject-≈-IsEquivalence : B.IsEquivalence SliceObject-≈
        SliceObject-≈-IsEquivalence = record
            { refl = ObjEq.refl , MorphEq.refl
            ; sym = SliceObject-≈-Symmetric
            ; trans = SliceObject-≈-Transitive
            }

        SliceObjectSetoid : B.Setoid 𝒸 ℓ
        SliceObjectSetoid = record
            { Carrier = hom[-, b ]
            ; _≈_ = SliceObject-≈
            ; isEquivalence = SliceObject-≈-IsEquivalence
            }

        record SliceMorphism (src tar : hom[-, b ]) : Set 𝒸 where

            source : Object
            source = proj₁ src

            target : Object
            target = proj₁ tar

            field
                morphism : source ⇒ target

        -- record SliceMorphism-≈
        --         {f-src g-src f-tar g-tar : hom[-, b ]}
        --         (f : SliceMorphism f-src g-src)
        --         (g : SliceMorphism f-tar g-tar)
        --         : Set ℓ where
        --     open SliceMorphism
        --     field
        --         source-≈ : SliceObject-≈ f-src g-src
        --         target-≈ : SliceObject-≈ f-tar g-tar
        --         ≈ : morphism f ≈ morphism g

        SliceMorphism-≈ : Rel (uncurry SliceMorphism) ℓ
        SliceMorphism-≈ {f-src , f-tar} {g-src , g-tar} f g =
            Σ[ source-≈ ∈ SliceObject-≈ f-src g-src ]
            Σ[ target-≈ ∈ SliceObject-≈ f-tar g-tar ]
            morphism f ≈ morphism g
            where
                open SliceMorphism

        module SliceObjectEq = B.IsEquivalence SliceObject-≈-IsEquivalence

        SliceMorphism-≈-Symmetric : Symmetric (uncurry SliceMorphism) SliceMorphism-≈ -- Symmetric SliceMorphism-≈ ?
        SliceMorphism-≈-Symmetric (≈src₁ , ≈src₂ , f≈g) =
            SliceObjectEq.sym ≈src₁ , SliceObjectEq.sym ≈src₂ , MorphEq.sym f≈g

        SliceMorphism-≈-Transitive : Transitive (uncurry SliceMorphism) SliceMorphism-≈ -- Symmetric SliceMorphism-≈ ?
        SliceMorphism-≈-Transitive (≈src₁ , ≈src₂ , f≈g) (≈src₃ , ≈src₄ , g≈h) =
            SliceObjectEq.trans ≈src₁ ≈src₃ ,
            SliceObjectEq.trans ≈src₂ ≈src₄ ,
            MorphEq.trans f≈g g≈h

        SliceMorphism-≈-IsEquivalence : IsEquivalence (uncurry SliceMorphism) SliceMorphism-≈
        SliceMorphism-≈-IsEquivalence = record
            { refl = SliceObjectEq.refl , SliceObjectEq.refl , MorphEq.refl
            ; sym = λ {i} {j} {f} {g} → SliceMorphism-≈-Symmetric {i} {j} {f} {g}
            ; trans = λ {i} {j} {k} {f} {g} {h} → SliceMorphism-≈-Transitive {i} {j} {k} {f} {g} {h} --
            }

        SliceMorphismSetoid : Setoid (hom[-, b ] × hom[-, b ]) 𝒸 ℓ
        SliceMorphismSetoid = record
            { Carrier = uncurry SliceMorphism
            ; _≈_ = SliceMorphism-≈
            ; isEquivalence = SliceMorphism-≈-IsEquivalence
            }

        Slice-∘ : ∀ {a b c}
            → SliceMorphism b c
            → SliceMorphism a b
            → SliceMorphism a c
        Slice-∘ f g = record { morphism = morphism f ∘ morphism g }
            where   open SliceMorphism

        Slice-id : ∀ a → SliceMorphism a a
        Slice-id (a , _) = record { morphism = id a }

        Slice-isCategory : IsCategory SliceMorphismSetoid Slice-∘ Slice-id
        Slice-isCategory = record
            { assoc = λ f g h → SliceObjectEq.refl , SliceObjectEq.refl , assoc (morphism f) (morphism g) (morphism h)
            ; ∘-left-identity = λ f → SliceObjectEq.refl , SliceObjectEq.refl , ∘-left-identity (morphism f)
            ; ∘-right-identity = λ f → SliceObjectEq.refl , SliceObjectEq.refl , ∘-right-identity (morphism f)
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
    { ObjectSetoid = CommaObjectSetoid -- CommaObject
    ; MorphismSetoid = CommaMorphismSetoid -- morphism
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

        module ObjEq = B.IsEquivalence (B.Setoid.isEquivalence ObjectSetoid)
        module MorphEq = IsEquivalence (Setoid.isEquivalence MorphismSetoid)

        record CommaObject : Set (𝒸 ⊔ ℓ) where
            field
                source : C.Object
                target : D.Object
                morphism : S.mapObject source ⇒ T.mapObject target

        open CommaObject

        CommaObject-≈ : B.Rel CommaObject ℓ
        CommaObject-≈ f g =
            Σ[ source-≈ ∈ S.mapObject (source f) ≈o S.mapObject (source g) ]
            Σ[ target-≈ ∈ T.mapObject (target f) ≈o T.mapObject (target g) ]
            morphism f ≈ morphism g

        CommaObject-≈-Symmetric : B.Symmetric CommaObject-≈
        CommaObject-≈-Symmetric (source-≈ , target-≈ , f≈g) =
            (ObjEq.sym source-≈) , (ObjEq.sym target-≈) , (MorphEq.sym f≈g)

        CommaObject-≈-Transitive : B.Transitive CommaObject-≈
        CommaObject-≈-Transitive (source-≈₁ , target-≈₁ , f≈g) (source-≈₂ , target-≈₂ , g≈h)
            =   (ObjEq.trans source-≈₁ source-≈₂) ,
                (ObjEq.trans target-≈₁ target-≈₂) ,
                (MorphEq.trans f≈g g≈h)

        CommaObject-≈-IsEquivalence : B.IsEquivalence CommaObject-≈
        CommaObject-≈-IsEquivalence = record
            { refl = ObjEq.refl , ObjEq.refl , MorphEq.refl
            ; sym = λ {i} {f} → CommaObject-≈-Symmetric {i} {f}
            ; trans = λ {f} {g} {h} → CommaObject-≈-Transitive {f} {g} {h}
            }

        CommaObjectSetoid : B.Setoid (𝒸 ⊔ ℓ) ℓ
        CommaObjectSetoid = record
            { Carrier = CommaObject
            ; _≈_ = CommaObject-≈
            ; isEquivalence = CommaObject-≈-IsEquivalence
            }

        record CommaMorphism (src : CommaObject) (tar : CommaObject) : Set (𝒸 ⊔ ℓ) where
            module SRC = CommaObject src
            module TAR = CommaObject tar
            field
                morphismBetweenSources : S.mapObject SRC.source ⇒ S.mapObject TAR.source
                morphismBetweenTargets : T.mapObject SRC.target ⇒ T.mapObject TAR.target
                commutes : TAR.morphism ∘ morphismBetweenSources ≈ morphismBetweenTargets ∘ SRC.morphism

        open CommaMorphism

        CommaMorphism-≈ : Rel (uncurry CommaMorphism) ℓ
        CommaMorphism-≈ {f-src , f-tar} {g-src , g-tar} f g =
            (morphismBetweenSources f ≈ morphismBetweenSources g) ×
            (morphismBetweenTargets f ≈ morphismBetweenTargets g)

        CommaMorphism-≈-Symmetric : Symmetric (uncurry CommaMorphism) CommaMorphism-≈
        CommaMorphism-≈-Symmetric (source-≈ , target-≈) = (MorphEq.sym source-≈) , (MorphEq.sym target-≈)

        CommaMorphism-≈-Transitive : Transitive (uncurry CommaMorphism) CommaMorphism-≈
        CommaMorphism-≈-Transitive (source₁-≈ , target₁-≈) (source₂-≈ , target₂-≈) =
            (MorphEq.trans source₁-≈ source₂-≈) , (MorphEq.trans target₁-≈ target₂-≈)

        CommaMorphism-≈-IsEquivalence : IsEquivalence (uncurry CommaMorphism) CommaMorphism-≈
        CommaMorphism-≈-IsEquivalence = record
            { refl = MorphEq.refl , MorphEq.refl
            ; sym = λ {i} {j} {f} {g} → CommaMorphism-≈-Symmetric {i} {j} {f} {g}
            ; trans = λ {i} {j} {k} {f} {g} {h} → CommaMorphism-≈-Transitive {i} {j} {k} {f} {g} {h}
            }

        CommaMorphismSetoid : Setoid (CommaObject × CommaObject) (𝒸 ⊔ ℓ) ℓ
        CommaMorphismSetoid = record
            { Carrier = uncurry CommaMorphism
            ; _≈_ = CommaMorphism-≈
            ; isEquivalence = CommaMorphism-≈-IsEquivalence
            }


        -- ≈-isPreorder : B.IsPreorder
        --     (λ x y → x ≡ y)
        --     (λ x y → {!   !}) -- CommaMorphism-≈)
        -- ≈-isPreorder = record
        --     { isEquivalence = PropEq.isEquivalence
        --     ; reflexive     = ≈-isPreorder-reflexive
        --     ; trans         = λ {i} {j} {k} f g → CommaMorphism-≈-Transitive {{! f  !} , {!   !}} f g -- CommaMorphism-≈-Transitive f g
        --     }
        --     where
        --         ≈-isPreorder-reflexive : _≡_ B.⇒ CommaMorphism-≈
        --         ≈-isPreorder-reflexive refl = MorphEq.refl , MorphEq.refl


        Comma-∘ : ∀ {a b c}
            → CommaMorphism b c
            → CommaMorphism a b
            → CommaMorphism a c
        Comma-∘ f g = record
            { morphismBetweenSources = morphismBetweenSources f ∘ morphismBetweenSources g
            ; morphismBetweenTargets = morphismBetweenTargets f ∘ morphismBetweenTargets g
            ; commutes = {!   !}
            }
            where   open CommaMorphism
                    open import Relation.Binary using (IsPreorder)
