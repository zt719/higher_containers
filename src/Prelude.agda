module Prelude where

open import Level using (Level; _⊔_)
open import Axiom.Extensionality.Heterogeneous
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; ≡-to-≅; ≅-to-≡)

private
  variable
    ℓ ℓ′ ℓ″ : Level

------------------------------------------------------------------------
-- Function extensionality for heterogeneous equality

postulate
  ext : Extensionality ℓ ℓ′

funExt : {A : Set ℓ}
         {B : A → Set ℓ′}
         {f g : (x : A) → B x}
         → ((x : A) → f x ≅ g x)
         → f ≅ g
funExt = ext (λ x → refl)

funExt≡ : {A : Set ℓ}
          {B : A → Set ℓ′}
          {f g : (x : A) → B x}
          → ((x : A) → f x ≡ g x)
          → f ≡ g
funExt≡ h = ≅-to-≡ (funExt λ x → ≡-to-≅ (h x))
