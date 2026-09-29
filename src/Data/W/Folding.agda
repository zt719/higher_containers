module Data.W.Folding where

open import Data.Product using (_,_)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong-app)
open import Data.Cont using (Cont; ⟦_⟧; ⟦_⟧₁)
open import Data.W.Base
open import Prelude

------------------------------------------------------------------------
-- Folding

module _  {SP : Cont} {A : Set} (α : ⟦ SP ⟧ A → A) where
  
  foldW : W SP → A
  foldW (sup (s , f)) = α (s , foldW ∘ f)

  commute : foldW ∘ sup ≡ α ∘ ⟦ SP ⟧₁ foldW
  commute = refl

  unique-go : (foldW' : W SP → A)
              (commute' : foldW' ∘ sup ≡ α ∘ ⟦ SP ⟧₁ foldW')
              (w : W SP)
              → foldW' w ≡ foldW w
  unique-go foldW' commute' (sup (s , f)) =
    trans (cong-app commute' (s , f))
      (cong (λ g → α (s , g))
        (funExt λ p →
          unique-go foldW' commute' (f p)))

  unique : (foldW' : W SP → A)
           (commute' : foldW' ∘ sup ≡ α ∘ ⟦ SP ⟧₁ foldW')
           → foldW' ≡ foldW
  unique foldW' commute' = funExt (unique-go foldW' commute')
