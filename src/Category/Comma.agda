module Category.Comma where

open import Level
open import Data.Product
open import Category.Core
open import Relation.Binary as B using ()
open import Relation.Binary.Indexed
open import Relation.Binary.Indexed.Extra
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

_/_ : ∀ {𝒸 ℓ} → (C : Category 𝒸 ℓ) → (b : Category.Object C) → Category 𝒸 ℓ
_/_ {𝒸} {ℓ} C b = record
    { Objects = SliceObjectSetoid
    ; Morphisms = SliceMorphismStructure
    }
    where
        open Category C
        module ObjEq = B.IsEquivalence (B.Setoid.isEquivalence Objects)
        module MorphEq = IsEquivalence (MorphismStructure.isEquivalence Morphisms)

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

        Slice-∘ : ∀ {a b c}
            → SliceMorphism b c
            → SliceMorphism a b
            → SliceMorphism a c
        Slice-∘ f g = record { morphism = morphism f ∘ morphism g }
            where   open SliceMorphism

        Slice-id : ∀ a → SliceMorphism a a
        Slice-id (a , _) = record { morphism = id a }

        SliceMorphismIsMorphism : IsMorphism SliceMorphism-≈ Slice-∘ Slice-id
        SliceMorphismIsMorphism = record
            { assoc = λ f g h → SliceObjectEq.refl , SliceObjectEq.refl , assoc (morphism f) (morphism g) (morphism h)
            ; left-identity = λ f → SliceObjectEq.refl , SliceObjectEq.refl , left-identity (morphism f)
            ; right-identity = λ f → SliceObjectEq.refl , SliceObjectEq.refl , right-identity (morphism f)
            ; cong = λ {x} {y} {u} {v} x≈y u≈v → proj₁ u≈v , proj₁ (proj₂ x≈y) , cong (proj₂ (proj₂ x≈y)) (proj₂ (proj₂ u≈v))
            }
            where
                open IsMorphism isMorphism
                open SliceMorphism
                open import Relation.Binary.Indexed.SetoidReasoning

        SliceMorphismStructure : MorphismStructure 𝒸 ℓ hom[-, b ]
        SliceMorphismStructure = record
            { Carrier = uncurry SliceMorphism
            ; _≈_ = SliceMorphism-≈
            ; isEquivalence = SliceMorphism-≈-IsEquivalence
            ; _∘_ = Slice-∘
            ; id = Slice-id
            ; isMorphism = SliceMorphismIsMorphism
            }

--     S     T
--  C --> E <-- D
--
_↓_ : {𝒸₀ ℓ₀ 𝒸₁ ℓ₁ 𝒸₂ ℓ₂ : Level}
    {C : Category 𝒸₀ ℓ₀} {D : Category 𝒸₁ ℓ₁} {E : Category 𝒸₂ ℓ₂}
    → (S : Functor C E) → (T : Functor D E)
    → Category (𝒸₀ ⊔ 𝒸₁ ⊔ 𝒸₂ ⊔ ℓ₂) ℓ₂
_↓_ {𝒸₀} {ℓ₀} {𝒸₁} {ℓ₁} {𝒸₂} {ℓ₂} {C} {D} {E} S T = record
    { Objects = CommaObjectSetoid
    ; Morphisms = CommaMorphismStructure
    }
    where
        module C = Category C
        module D = Category D
        module S = Functor S
        module T = Functor T
        open Category E

        module ObjEq = B.IsEquivalence (B.Setoid.isEquivalence Objects)
        module MorphEq = IsEquivalence (MorphismStructure.isEquivalence Morphisms)

        record CommaObject : Set (𝒸₀ ⊔ 𝒸₁ ⊔ 𝒸₂ ⊔ ℓ₂) where
            field
                source : C.Object
                target : D.Object
                morphism : S.mapObject source ⇒ T.mapObject target

        open CommaObject

        CommaObject-≈ : B.Rel CommaObject ℓ₂
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

        CommaObjectSetoid : B.Setoid (𝒸₀ ⊔ 𝒸₁ ⊔ 𝒸₂ ⊔ ℓ₂) ℓ₂
        CommaObjectSetoid = record
            { Carrier = CommaObject
            ; _≈_ = CommaObject-≈
            ; isEquivalence = CommaObject-≈-IsEquivalence
            }

        record CommaMorphism (src : CommaObject) (tar : CommaObject) : Set (𝒸₀ ⊔ 𝒸₁ ⊔ 𝒸₂ ⊔ ℓ₂) where
            module SRC = CommaObject src
            module TAR = CommaObject tar
            field
                morphismBetweenSources : S.mapObject SRC.source ⇒ S.mapObject TAR.source
                morphismBetweenTargets : T.mapObject SRC.target ⇒ T.mapObject TAR.target
                commutes : TAR.morphism ∘ morphismBetweenSources ≈ morphismBetweenTargets ∘ SRC.morphism

        open CommaMorphism public

        CommaMorphism-≈ : Rel (uncurry CommaMorphism) ℓ₂
        CommaMorphism-≈ f g =
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

        Comma-∘ : ∀ {a b c}
            → CommaMorphism b c
            → CommaMorphism a b
            → CommaMorphism a c
        Comma-∘ {a} {b} {c} f g = record
            { morphismBetweenSources = morphismBetweenSources f ∘ morphismBetweenSources g
            ; morphismBetweenTargets = morphismBetweenTargets f ∘ morphismBetweenTargets g
            ; commutes =
                begin⟨ setoid ⟩
                    morphism c ∘ (morphismBetweenSources f ∘ morphismBetweenSources g)
                ≈⟨ sym (assoc (morphismBetweenSources g) (morphismBetweenSources f) (morphism c)) ⟩
                    (morphism c ∘ morphismBetweenSources f) ∘ morphismBetweenSources g
                ≈⟨ cong (commutes f) MorphEq.refl ⟩
                    (morphismBetweenTargets f ∘ morphism b) ∘ morphismBetweenSources g
                ≈⟨ assoc (morphismBetweenSources g) (morphism b) (morphismBetweenTargets f) ⟩
                    morphismBetweenTargets f ∘ (morphism b ∘ morphismBetweenSources g)
                ≈⟨ cong MorphEq.refl (commutes g) ⟩
                    morphismBetweenTargets f ∘ (morphismBetweenTargets g ∘ morphism a)
                ≈⟨ sym (assoc (morphism a) (morphismBetweenTargets g) (morphismBetweenTargets f)) ⟩
                    (morphismBetweenTargets f ∘ morphismBetweenTargets g) ∘ morphism a
                ∎
            }
            where
                open CommaMorphism
                open import Relation.Binary.Indexed.SetoidReasoning
                open IsMorphism isMorphism
                open IsEquivalence (MorphismStructure.isEquivalence Morphisms)

        Comma-id : ∀ a → CommaMorphism a a
        Comma-id a = record
            { morphismBetweenSources = id (S.mapObject (source a))
            ; morphismBetweenTargets = id (T.mapObject (target a))
            ; commutes =
                begin⟨ setoid ⟩
                    morphism a ∘ id (S.mapObject (source a))
                ≈⟨ right-identity (morphism a) ⟩
                    morphism a
                ≈⟨ sym (left-identity (morphism a)) ⟩
                    id (T.mapObject (target a)) ∘ morphism a
                ∎
            }
            where
                open IsMorphism isMorphism
                open import Relation.Binary.Indexed.SetoidReasoning
                open IsEquivalence (MorphismStructure.isEquivalence Morphisms)

        CommaMorphismIsMorphism : IsMorphism CommaMorphism-≈ Comma-∘ Comma-id
        CommaMorphismIsMorphism = record
            { assoc = λ f g h →
                assoc (morphismBetweenSources f) (morphismBetweenSources g) (morphismBetweenSources h) ,
                assoc (morphismBetweenTargets f) (morphismBetweenTargets g) (morphismBetweenTargets h)
            ; left-identity = λ f → (left-identity (morphismBetweenSources f)) , (left-identity (morphismBetweenTargets f))
            ; right-identity = λ f → (right-identity (morphismBetweenSources f)) , (right-identity (morphismBetweenTargets f))
            ; cong = λ x≈y u≈v → (cong (proj₁ x≈y) (proj₁ u≈v)) , (cong (proj₂ x≈y) (proj₂ u≈v))
            }
            where open IsMorphism isMorphism

        CommaMorphismStructure : MorphismStructure (𝒸₀ ⊔ 𝒸₁ ⊔ 𝒸₂ ⊔ ℓ₂) ℓ₂ CommaObject
        CommaMorphismStructure = record
            { Carrier = uncurry CommaMorphism
            ; _≈_ = CommaMorphism-≈
            ; isEquivalence = CommaMorphism-≈-IsEquivalence
            ; _∘_ = Comma-∘
            ; id = Comma-id
            ; isMorphism = CommaMorphismIsMorphism
            }
