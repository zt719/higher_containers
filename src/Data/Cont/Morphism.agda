module Data.Cont.Morphism where

open import Data.Product using (_,_)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Cont.Base using (Cont; _◃_; ⟦_⟧; ⟦_⟧₁)
open import Prelude

private
  variable
    SP SP' TQ TQ' UV : Cont

------------------------------------------------------------------------
-- Morphism

infixr 0 _→ᶜ_
record _→ᶜ_ (SP TQ : Cont) : Set where
  constructor _◃_
  pattern  
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    fS : S → T
    fP : (s : S) → Q (fS s) → P s

idᶜ : SP →ᶜ SP
idᶜ = id ◃ id*

infixr 9 _∘ᶜ_
_∘ᶜ_ : TQ →ᶜ UV → SP →ᶜ TQ → SP →ᶜ UV
(fT ◃  fQ) ∘ᶜ (fS ◃ fP) = (fT ∘ fS) ◃ (fP ∘* (fQ ∘ fS))

⟦_⟧→ᶜ : SP →ᶜ TQ → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ fS ◃ fP ⟧→ᶜ X (s , f) = fS s , f ∘ fP s

⟦_⟧→ᶜ-nat : (α : SP →ᶜ TQ) {X Y : Set} (g : X → Y)
            → ⟦ α ⟧→ᶜ Y ∘ ⟦ SP ⟧₁ g ≡ ⟦ TQ ⟧₁ g ∘ ⟦ α ⟧→ᶜ X
⟦ fS ◃ fP ⟧→ᶜ-nat g = refl
