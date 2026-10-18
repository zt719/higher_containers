{-# OPTIONS --without-K #-}

module Data.Cont.Base where

open import Data.Product
open import Function

------------------------------------------------------------------------
-- Definition

infix 0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

-- Interpretation

⟦_⟧ : Cont → Set → Set
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

⟦_⟧₁ : (SP : Cont) {X Y : Set} (f : X → Y)
       → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g (s , f) = s , g ∘ f
