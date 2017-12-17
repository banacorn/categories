module Example.Poset where
-- open import Category
open import Level
open import Relation.Binary
open import Function using (flip)
open import Data.Unit using (⊤; tt)
open Poset

open IsPartialOrder

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
