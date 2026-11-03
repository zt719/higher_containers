{-# OPTIONS --cubical --guardedness #-}

module Data.Cont.Base where

open import Prelude

------------------------------------------------------------------------
-- Definition

infix 0 _◃_
record Cont : Type₁ where
  constructor _◃_
  field
    S : Type
    P : S → Type

-- Interpretation

⟦_⟧ : Cont → Type → Type
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

⟦_⟧₁ : (SP : Cont) {X Y : Type} (f : X → Y)
       → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g (s , f) = s , g ∘ f
