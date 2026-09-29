module Prelude where

open import Agda.Primitive using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong-app)
open import Function.Base

private
  variable
    ℓ ℓ′ ℓ″ : Level

------------------------------------------------------------------------
-- Function extensionality

module _
  {ℓ ℓ'}
  {A : Set ℓ}
  {B : A → Set ℓ'}
  {f g : (x : A) → B x}
  where

  funExt⁻ : f ≡ g → (x : A) → f x ≡ g x
  funExt⁻ p x = cong (λ h → h x) p

  postulate
    funExt : ((x : A) → f x ≡ g x) → f ≡ g
    funExt-β : (p : (x : A) → f x ≡ g x) (x : A) → cong (λ h → h x) (funExt p) ≡ p x
    funExt-η : (p : f ≡ g) → funExt (λ x → cong (λ h → h x) p) ≡ p

funExt₂ :
  ∀ {ℓ ℓ' ℓ''}
  {A : Set ℓ}
  {B : A → Set ℓ'}
  {C : (a : A) → B a → Set ℓ''}
  {f g : (a : A) (b : B a) → C a b}
  → ((a : A) (b : B a) → f a b ≡ g a b)
  → f ≡ g
funExt₂ p = funExt λ a → funExt λ b → p a b

------------------------------------------------------------------------
-- HAHA

_→*_ : ∀ {ℓ ℓ′ ℓ″} {I : Set ℓ}
  → (I → Set ℓ′) → (I → Set ℓ″) → Set (ℓ ⊔ ℓ′ ⊔ ℓ″)
_→*_ {I = I} A B = (i : I) → A i → B i

id* : ∀ {ℓ} {I : Set ℓ} {A : I → Set ℓ′} → A →* A
id* i a = a

_∘*_ : ∀ {ℓ ℓ′ ℓ″ ℓ‴}
  {I : Set ℓ}
  {A : I → Set ℓ′}
  {B : I → Set ℓ″}
  {C : I → Set ℓ‴}
  → B →* C → A →* B → A →* C
(f ∘* g) = λ i a → f i (g i a)
{-# INLINE _∘*_ #-}

------------------------------------------------------------------------
-- Heterogeneous Equality & Function Extensionality

data Heq {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} : (x y : A) → B x → B y → Set (ℓ ⊔ ℓ′) where
  refl : {a : A} {b : B a} → Heq a a b b

data Heq₂ {ℓ ℓ′ ℓ″}
  {A : Set ℓ}
  {B : A → Set ℓ′}
  {C : (a : A) → B a → Set ℓ″}
  : (x y : A) (u : B x) (v : B y) → C x u → C y v → Set (ℓ ⊔ ℓ′ ⊔ ℓ″)
  where
  refl : {a : A} {b : B a} {c : C a b} → Heq₂ a a b b c c

elimHeq : {A : Set ℓ}
  {B : A → Set ℓ′}
  (M : {x y : A} {u : B x} {v : B y} → Heq x y u v → Set ℓ″)
  (m-refl : {x : A} {u : B x} → M {x} {x} {u} {u} refl)
  {x y : A} {u : B x} {v : B y} (p : Heq x y u v)
  → M {x} {y} {u} {v} p
elimHeq M m-refl refl = m-refl

hcong :
  {A : Set ℓ}
  {B : A → Set ℓ′}
  (f : (x : A) → B x)
  {x y : A} →
  x ≡ y →
  Heq x y (f x) (f y)
hcong f refl = refl

hcong₂ :
  ∀ {A : Set ℓ}
  {B : A → Set ℓ′}
  {C : (x : A) → B x → Set ℓ″}
  (f : (x : A) (y : B x) → C x y)
  {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
  (p : x₁ ≡ x₂) (q : Heq x₁ x₂ y₁ y₂)
  → Heq₂ x₁ x₂ y₁ y₂ (f x₁ y₁) (f x₂ y₂)
hcong₂ f refl refl = refl

module _
  {ℓ ℓ'}
  {A : Set ℓ}
  {B : A → Set ℓ'}
  {f g : (x : A) → B x}
  where

  HfunExt⁻ : f ≡ g → (x y : A) → x ≡ y → Heq x y (f x) (g y)
  HfunExt⁻ refl x x refl = refl

  postulate
    HfunExt : ((x y : A) → x ≡ y → Heq x y (f x) (g y)) → f ≡ g
    HfunExt-β : (dp : (x y : A) → x ≡ y → Heq x y (f x) (g y)) (x y : A) (p : x ≡ y)
      → HfunExt⁻ (HfunExt dp) x y p ≡ dp x y p
    HfunExt-η : (eq : f ≡ g) → HfunExt (HfunExt⁻ eq) ≡ eq
