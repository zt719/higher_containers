{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function public
open import Cubical.Data.Unit public
  renaming (Unit to ⊤)
open import Cubical.Data.Empty public
  using (⊥)
  renaming (elim to ⊥-elim)
open import Cubical.Data.Sigma public
open import Cubical.Data.Sum public

id : ∀ {ℓ} {A : Type ℓ} → A → A
id a = a

case : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ}
       {B : Type ℓ′} {C : Type ℓ″}
     → (A → C)
     → (B → C)
     → A ⊎ B → C
case f g (inl a) = f a
case f g (inr b) = g b

pair : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ}
       {B : Type ℓ′} {C : Type ℓ″}
     → (A → B)
     → (A → C)
     → A → B × C
pair f g a = f a , g a     
