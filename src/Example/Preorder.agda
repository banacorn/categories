module Example.Preorder where

open import Category.Core

open import Level
open import Data.Product
open import Relation.Binary 
open import Function using (flip)
open import Data.Unit using (⊤; tt)

Preorder→Category : Preorder zero zero zero → Category {zero} {zero}
Preorder→Category preorder = record
    { Object = Preorder.Carrier preorder
    ; Morphism = record
        { Carrier = uncurry _∼_ -- uncurry _∼_
        ; _≈_ = λ _ _ → ⊤
        ; isEquivalence = _
        }
    ; _∘_ = flip trans
    ; id = λ _ → refl
    ; isCategory = _
    }
    where
        open Preorder preorder
