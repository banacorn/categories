open import Relation.Binary.Indexed

module Relation.Binary.Indexed.EqReasoning {𝒾} {I : Set 𝒾} {𝒸 ℓ} (S : Setoid I 𝒸 ℓ) where

open Setoid S
import Relation.Binary.Indexed.PreorderReasoning as PreR
open import Relation.Binary.Indexed.Extra using (Setoid⇒Preorder)
open PreR (Setoid⇒Preorder S) public
       renaming ( _∼⟨_⟩_  to _≈⟨_⟩_
                ; _≈⟨_⟩_  to _≡⟨_⟩_
                ; _≈⟨⟩_  to _≡⟨⟩_
                )
