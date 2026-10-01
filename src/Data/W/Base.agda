module Data.W.Base where

open import Data.Product using (_,_)
open import Data.Cont using (Cont; ⟦_⟧; ⟦_⟧₁)
open import Function using (_∘_)

------------------------------------------------------------------------
-- Definition

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

------------------------------------------------------------------------
-- Induction

elimW : ∀ {ℓ} {SP : Cont} (open Cont SP)
        (Q : W SP → Set ℓ) →
        (h : (s : S) (f : P s → W SP)
             → ((p : P s) → Q (f p))
             → Q (sup (s , f)))
        (w : W SP) → Q w
elimW Q h (sup (s , f)) = h s f (elimW Q h ∘ f)

------------------------------------------------------------------------
-- Folding
  
foldW : {SP : Cont} {A : Set}
        (α : ⟦ SP ⟧ A → A)
        → W SP → A
foldW α (sup (s , f)) = α (s , foldW α ∘ f)
