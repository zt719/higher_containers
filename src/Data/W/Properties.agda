module Data.W.Properties where

open import Data.Product using (_,_)
open import Data.Cont using (Cont; _◃_; ⟦_⟧; ⟦_⟧₁)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong-app)
  
open import Data.W.Base
open import Prelude using (funExt≡)

------------------------------------------------------------------------
-- Lambek's lemma

sup⁻ : {SP : Cont} → W SP → ⟦ SP ⟧ (W SP)
sup⁻ (sup x) = x

sup⁻∘sup≡id : {SP : Cont} → sup⁻ ∘ sup ≡ id {A = ⟦ SP ⟧ (W SP)}
sup⁻∘sup≡id = funExt≡ (λ _ → refl)

sup∘sup⁻≡id : {SP : Cont} → sup ∘ sup⁻ ≡ id {A = W SP}
sup∘sup⁻≡id = funExt≡ λ{ (sup _) → refl }

------------------------------------------------------------------------
-- Folding commutes and is unique

module _  {SP : Cont} {A : Set} (α : ⟦ SP ⟧ A → A) where

  commute : foldW α ∘ sup ≡ α ∘ ⟦ SP ⟧₁ (foldW α)
  commute = refl

  unique-go : (foldW' : W SP → A)
              (commute' : foldW' ∘ sup ≡ α ∘ ⟦ SP ⟧₁ foldW')
              (w : W SP)
              → foldW' w ≡ foldW α w
  unique-go foldW' commute' (sup (s , f)) =
    trans (cong-app commute' (s , f))
      (cong (λ g → α (s , g))
        (funExt≡ λ p →
          unique-go foldW' commute' (f p)))

  unique : (foldW' : W SP → A)
           (commute' : foldW' ∘ sup ≡ α ∘ ⟦ SP ⟧₁ foldW')
           → foldW' ≡ foldW α
  unique foldW' commute' = funExt≡ (unique-go foldW' commute')
