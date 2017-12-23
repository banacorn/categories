module Example.Poset where

open import Category.Core

open import Level
open import Data.Product
open import Relation.Binary
open import Relation.Binary.Indexed
-- open import Function using (flip)
-- open import Data.Unit using (⊤; tt)

open Poset



Poset→Category : Poset zero zero zero → Category {zero} {zero}
Poset→Category poset = record
    { Object = Poset.Carrier poset
    ; Morphism = record { Carrier = {!   !} ; _≈_ = {!   !} ; isEquivalence = {!   !} }
    ; _∘_ = {!   !}
    ; id = {!   !}
    ; isCategory = {!   !}
    }
-- open IsPartialOrder

-- a poset = trans (isPreorder (isPartcialOrder poset))

-- Poset-IsCategory : (poset : Poset zero zero zero)
--     → IsCategory {!   !} {!   !} {!   !}
-- Poset-IsCategory = {!   !}
--         (_≤_ poset)
--         (λ a b → ⊤)
--         (flip (IsPreorder.trans (IsPartialOrder.isPreorder (isPartialOrder poset))))
--         (IsPreorder.refl (IsPartialOrder.isPreorder (isPartialOrder poset)))
--
-- Poset-IsCategory poset = record
--     { assoc = λ a≤b b≤c c≤d → tt
--     ; ∘-left-identity = λ {a} {b} f → tt
--     ; ∘-right-identity = λ {a} {b} f → tt
--     }
