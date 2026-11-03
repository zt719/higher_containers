{-# OPTIONS --cubical --guardedness #-}

module Data.Cont.Morphism where

open import Prelude
open import Data.Cont.Base

private
  variable
    SP TQ UV : Cont

------------------------------------------------------------------------
-- Morphism

infixr 0 _→ᶜ_
record _→ᶜ_ (SP TQ : Cont) : Type where
  constructor _◃_
  pattern  
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    fS : S → T
    fP : (s : S) → Q (fS s) → P s

idᶜ : SP →ᶜ SP
idᶜ = id ◃ λ s → id

infixr 9 _∘ᶜ_
_∘ᶜ_ : TQ →ᶜ UV → SP →ᶜ TQ → SP →ᶜ UV
(fT ◃  fQ) ∘ᶜ (fS ◃ fP) = (fT ∘ fS) ◃ (λ s → fP s ∘ fQ (fS s))

------------------------------------------------------------------------
-- Interpretation

⟦_⟧→ᶜ : SP →ᶜ TQ → (X : Type) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ fS ◃ fP ⟧→ᶜ X (s , f) = fS s , f ∘ fP s
