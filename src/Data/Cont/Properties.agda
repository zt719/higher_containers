{-# OPTIONS --without-K #-}

module Data.Cont.Properties where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Cont.Base
open import Data.Cont.Morphism

private
  variable
    SP SP' TQ TQ' UV : Cont

------------------------------------------------------------------------
-- Natural transformations

⟦_⟧-id : (SP : Cont)
         {X : Set}
         → ⟦ SP ⟧₁ (id {A = X}) ≡ id
⟦_⟧-id SP = refl

⟦_⟧-∘ : (SP : Cont)
        {X Y Z : Set}
        (f : Y → Z) (g : X → Y)
        → ⟦ SP ⟧₁ (f ∘ g) ≡ ⟦ SP ⟧₁ f ∘ ⟦ SP ⟧₁ g
⟦ SP ⟧-∘ f g = refl

⟦_⟧→ᶜ-nat : (α : SP →ᶜ TQ) {X Y : Set} (g : X → Y)
            → ⟦ α ⟧→ᶜ Y ∘ ⟦ SP ⟧₁ g ≡ ⟦ TQ ⟧₁ g ∘ ⟦ α ⟧→ᶜ X
⟦ fS ◃ fP ⟧→ᶜ-nat g = refl

Nat : Cont → Cont → Set₁
Nat SP TQ =
  Σ[ α ∈ (∀ (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X) ]
    (∀ {X Y : Set} (g : X → Y)
       → α Y ∘ ⟦ SP ⟧₁ g ≡ ⟦ TQ ⟧₁ g ∘ α X)

to : SP →ᶜ TQ → Nat SP TQ
to m = ⟦ m ⟧→ᶜ , ⟦ m ⟧→ᶜ-nat

from : Nat SP TQ → SP →ᶜ TQ
from {SP = S ◃ P} (α , nat) =
    (λ s → proj₁ (α (P s) (s , id)))
  ◃ (λ s → proj₂ (α (P s) (s , id)))

from-to : (m : SP →ᶜ TQ) → from (to m) ≡ m
from-to (fS ◃ fP) = refl

to-from : (n : Nat SP TQ) (X : Set) (x : ⟦ SP ⟧ X)
        → proj₁ (to (from n)) X x ≡ proj₁ n X x
to-from (α , nat) X (s , k) = sym (cong-app (nat k) (s , id))

------------------------------------------------------------------------
-- Corollaries

faithful : (m m′ : SP →ᶜ TQ) → to m ≡ to m′ → m ≡ m′
faithful m m′ eq = trans (sym (from-to m)) (trans (cong from eq) (from-to m′))
