{-# OPTIONS --cubical --guardedness #-}

module Data.Cont.Properties where

open import Prelude
open import Data.Cont.Base
open import Data.Cont.Morphism

private
  variable
    SP SP' TQ TQ' UV : Cont

------------------------------------------------------------------------
-- Natural transformations

⟦_⟧-id : (SP : Cont)
         {X : Type}
         → ⟦ SP ⟧₁ (id {A = X}) ≡ id
⟦_⟧-id SP = refl

⟦_⟧-∘ : (SP : Cont)
        {X Y Z : Type}
        (f : Y → Z) (g : X → Y)
        → ⟦ SP ⟧₁ (f ∘ g) ≡ ⟦ SP ⟧₁ f ∘ ⟦ SP ⟧₁ g
⟦ SP ⟧-∘ f g = refl

⟦_⟧→ᶜ-nat : (α : SP →ᶜ TQ) {X Y : Type} (g : X → Y)
            → ⟦ α ⟧→ᶜ Y ∘ ⟦ SP ⟧₁ g ≡ ⟦ TQ ⟧₁ g ∘ ⟦ α ⟧→ᶜ X
⟦ fS ◃ fP ⟧→ᶜ-nat g = refl
