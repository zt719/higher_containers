module Data.Cont.Base where

open import Data.Product using (Σ; Σ-syntax; _,_)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

⟦_⟧₁ : (SP : Cont)
       {X Y : Set}
       (f : X → Y)
       → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g (s , f) = s , g ∘ f

⟦_⟧-id : (SP : Cont)
         {X : Set}
         → ⟦ SP ⟧₁ (id {A = X}) ≡ id
⟦_⟧-id SP = refl

⟦_⟧-∘ : (SP : Cont)
        {X Y Z : Set}
        (f : Y → Z) (g : X → Y)
        → ⟦ SP ⟧₁ (f ∘ g) ≡ ⟦ SP ⟧₁ f ∘ ⟦ SP ⟧₁ g
⟦ SP ⟧-∘ f g = refl
