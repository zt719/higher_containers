{-# OPTIONS --cubical #-}

module Prelude where

open import Agda.Primitive
open import Agda.Primitive.Cubical public
  renaming ( primIMin to _∧_ ; primIMax to _∨_ ; primINeg to ~_
           ; primHComp to hcomp ; primComp to comp ; primTransp to transp )
open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public
  renaming (primSubOut to outS)

-- Builtin types, taken from the standard builtin modules.
open import Agda.Builtin.Unit  public
open import Agda.Builtin.Bool  public
open import Agda.Builtin.Nat   public
  renaming (Nat to ℕ)
  using (zero; suc)
open import Agda.Builtin.List  public
open import Agda.Builtin.Sigma public
  renaming (fst to proj₁; snd to proj₂)

variable
  ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------
-- Path types (as before)
------------------------------------------------------------------------

refl : {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} = λ _ → x

sym : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym p = λ i → p (~ i)

cong : {A : Type ℓ} {B : Type ℓ'} {x y : A}
     → (f : A → B) → x ≡ y → f x ≡ f y
cong f p = λ i → f (p i)

apd : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
    → (f : (i : I) → (a : A i) → B i a)
    → {x : A i0} {y : A i1} (p : PathP A x y)
    → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
apd f p = λ i → f i (p i)

------------------------------------------------------------------------
-- Kan operations and path composition
------------------------------------------------------------------------

hfill : {A : Type ℓ} {φ : I} (u : (i : I) → Partial φ A)
      (u0 : Sub A φ (u i0)) (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) itIsOne ; (i = i0) → outS u0 })
        (outS u0)

infixr 30 _∙_

compPath-filler : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
                → I → I → A
compPath-filler {x = x} p q j i =
  hfill (λ j → λ { (i = i0) → x ; (i = i1) → q j }) (inS (p i)) j

_∙_ : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(p ∙ q) i = compPath-filler p q i1 i

compPathP' : {A : Type ℓ} {B : A → Type ℓ'} {x y z : A}
             {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
           → PathP (λ i → B (p i)) x' y'
           → PathP (λ i → B (q i)) y' z'
           → PathP (λ i → B ((p ∙ q) i)) x' z'
compPathP' {B = B} {x' = x'} {p = p} {q = q} P Q i =
  comp (λ j → B (compPath-filler p q j i))
       (λ j → λ { (i = i0) → x' ; (i = i1) → Q j })
       (P i)

------------------------------------------------------------------------
-- Functions
------------------------------------------------------------------------

id : {A : Type ℓ} → A → A
id a = a

infixr 9 _∘_
_∘_ : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
    → ({a : A} (b : B a) → C a b) → (g : (a : A) → B a) → (a : A) → C a (g a)
(f ∘ g) a = f (g a)
{-# INLINE _∘_ #-}

------------------------------------------------------------------------
-- Universe lifting
------------------------------------------------------------------------

record Lift (ℓ' : Level) (A : Type ℓ) : Type (ℓ ⊔ ℓ') where
  constructor lift
  field lower : A

open Lift public

------------------------------------------------------------------------
-- Empty type ⊥ (not in Agda.Builtin, so defined here)
------------------------------------------------------------------------

data ⊥ : Type where

⊥-elim : {A : Type ℓ} → ⊥ → A
⊥-elim ()

------------------------------------------------------------------------
-- Product A × B, defined as a non-dependent Σ
------------------------------------------------------------------------

infixr 2 _×_

_×_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)

-- Cubical-library-style names for the projections.
fst : {A : Type ℓ} {B : A → Type ℓ'} → Σ A B → A
fst = proj₁

snd : {A : Type ℓ} {B : A → Type ℓ'} (p : Σ A B) → B (fst p)
snd = proj₂

pair : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
     → (A → B) → (A → C) → A → B × C
pair f g a = f a , g a

------------------------------------------------------------------------
-- Sums A ⊎ B (not in Agda.Builtin, so defined here)
------------------------------------------------------------------------

infixr 1 _⊎_

data _⊎_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Cubical-library-style names for the injections.
pattern inl a = inj₁ a
pattern inr b = inj₂ b

case : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
     → (A → C) → (B → C) → A ⊎ B → C
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

------------------------------------------------------------------------
-- Dependent function type Π
------------------------------------------------------------------------

Π : (A : Type ℓ) → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Π A B = (x : A) → B x

infix 2 Π-syntax
Π-syntax : (A : Type ℓ) → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Π-syntax = Π

syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B

------------------------------------------------------------------------
-- Sigma syntax Σ[ x ∈ A ] B  (the Σ type itself is builtin)
------------------------------------------------------------------------

infix 2 Σ-syntax
Σ-syntax : (A : Type ℓ) → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

------------------------------------------------------------------------
-- Finite sets Fin n (not in Agda.Builtin, so defined here)
------------------------------------------------------------------------

data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

------------------------------------------------------------------------
-- Vectors Vec A n (not in Agda.Builtin, so defined here).
-- The constructors have the same names as List's, so they live in
-- their own module. Only the type Vec is opened unqualified.
------------------------------------------------------------------------

infixr 5 _∷_
data Vec (A : Type ℓ) : ℕ → Type ℓ where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
