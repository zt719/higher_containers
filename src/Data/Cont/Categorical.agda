{-# OPTIONS --cubical --guardedness #-}

module Data.Cont.Categorical where

open import Prelude hiding (I)
open import Data.Cont.Base
open import Data.Cont.Morphism

private
  variable
    SP SP' TQ TQ' UV : Cont

------------------------------------------------------------------------
-- Terminal and initial

⊤ᶜ : Cont
⊤ᶜ = ⊤ ◃ λ _ → ⊥

¿ᶜ : (SP : Cont) → SP →ᶜ ⊤ᶜ
¿ᶜ (S ◃ P) = (λ _ → tt) ◃ λ s ()

⊥ᶜ : Cont
⊥ᶜ = ⊥ ◃ λ ()

!ᶜ : (SP : Cont) → ⊥ᶜ →ᶜ SP
!ᶜ (S ◃ P) = ⊥-elim ◃ λ ()

-- Binary product and coproduct

infixr 2 _×ᶜ_
_×ᶜ_ : Cont → Cont → Cont
(S ◃ P) ×ᶜ (T ◃ Q) = S × T ◃ λ (s , t) → P s ⊎ Q t

_×ᶜ₁_ : SP →ᶜ TQ → SP' →ᶜ TQ' → SP ×ᶜ SP' →ᶜ TQ ×ᶜ TQ'
(g ◃ h) ×ᶜ₁ (g' ◃ h')
  = (λ (s , s') → g s , g' s')
  ◃ λ{ (s , s') (inl p) → inl (h s p) ; (s , s') (inr p') → inr (h' s' p') }

projlᶜ : SP ×ᶜ TQ →ᶜ SP
projlᶜ = fst ◃ λ{ (S , T) p → inl p }

projrᶜ : SP ×ᶜ TQ →ᶜ TQ
projrᶜ = snd ◃ λ{ (S , T) q → inr q }

-- pairᶜ : SP →ᶜ TQ → SP →ᶜ TQ' → SP →ᶜ TQ ×ᶜ TQ'
-- pairᶜ (f ◃ g) (f' ◃ g') = pair f f' ◃ λ{ s (inl p) → g s p ; s (inr q) → g' s q }

infixr 1 _⊎ᶜ_
_⊎ᶜ_ : Cont → Cont → Cont
(S ◃ P) ⊎ᶜ (T ◃ Q) = S ⊎ T ◃ λ{ (inl s) → P s ; (inr t) → Q t }

_⊎ᶜ₁_ : SP →ᶜ TQ → SP' →ᶜ TQ' → SP ⊎ᶜ SP' →ᶜ TQ ⊎ᶜ TQ'
(g ◃ h) ⊎ᶜ₁ (g' ◃ h')
  = (λ{ (inl s) → inl (g s) ; (inr s') → inr (g' s') })
  ◃ λ{ (inl s) p → h s p ; (inr s') p' → h' s' p' }

inlᶜ : SP →ᶜ SP ⊎ᶜ TQ
inlᶜ = inl ◃ λ s p → p

inrᶜ : TQ →ᶜ SP ⊎ᶜ TQ
inrᶜ = inr ◃ λ s q → q

caseᶜ : SP →ᶜ TQ → SP' →ᶜ TQ → SP ⊎ᶜ SP' →ᶜ TQ
caseᶜ (f ◃ g) (f' ◃ g') = case f  f' ◃ λ{ (inl s) p → g s p ; (inr s') q → g' s' q }

-- Product and coproduct

private
  variable
    I : Type
    F G : I → Cont

Πᶜ : (I : Type) (F : I → Cont) → Cont
Πᶜ I F = ((i : I) → let S ◃ P = F i in S)
  ◃ λ f → Σ[ i ∈ I ] let S ◃ P = F i in P (f i)

infix 2 Πᶜ-syntax

Πᶜ-syntax : (I : Type) (F : I → Cont) → Cont
Πᶜ-syntax = Πᶜ

syntax Πᶜ-syntax A (λ x → B) = Πᶜ[ x ∈ A ] B

Πᶜ₁ : ((i : I) → F i →ᶜ G i) → Πᶜ I F →ᶜ Πᶜ I G
Πᶜ₁ f = (λ s i → let g ◃ h = f i in g (s i))
  ◃ λ s (i , p) → i , let g ◃ h = f i in h (s i) p

projᶜ : (i : I) → Πᶜ[ i ∈ I ] F i →ᶜ F i
projᶜ i = (λ f → f i) ◃ λ s p → i , p

Σᶜ : (I : Type) (F : I → Cont) → Cont
Σᶜ I F = (Σ[ i ∈ I ] let S ◃ P = F i in S)
  ◃ λ (i , s) → let S ◃ P = F i in P s

infix 2 Σᶜ-syntax

Σᶜ-syntax : (I : Type) (F : I → Cont) → Cont
Σᶜ-syntax = Σᶜ

syntax Σᶜ-syntax A (λ x → B) = Σᶜ[ x ∈ A ] B

Σᶜ₁ : ((i : I) → F i →ᶜ G i) → Σᶜ I F →ᶜ Σᶜ I G
Σᶜ₁ f = (λ (i , s) → i , let g ◃ h = f i in g s)
  ◃ λ (i , s) p → let g ◃ h = f i in h s p

injᶜ : (i : I) → F i →ᶜ Σᶜ[ i ∈ I ] F i
injᶜ i = (λ s → i , s) ◃ λ s p → p

-- Commutative semiring

lunit⊎ᶜ : ⊥ᶜ ⊎ᶜ SP →ᶜ SP
lunit⊎ᶜ = (λ{ (inr s) → s }) ◃ λ{ (inr s) p → p }

runit⊎ᶜ : SP ⊎ᶜ ⊥ᶜ →ᶜ SP
runit⊎ᶜ = (λ{ (inl s) → s }) ◃ λ{ (inl s) p → p }

comm⊎ᶜ : SP ⊎ᶜ TQ →ᶜ TQ ⊎ᶜ SP
comm⊎ᶜ = (λ{ (inl s) → inr s ; (inr t) → inl t }) ◃ λ{ (inl t) q → q ; (inr s) p → p }

assoc⊎ᶜ : (SP ⊎ᶜ TQ) ⊎ᶜ UV →ᶜ SP ⊎ᶜ (TQ ⊎ᶜ UV)
assoc⊎ᶜ = (λ{ (inl (inl s)) → inl s ; (inl (inr t)) → inr (inl t) ; (inr u) → inr (inr u) })
  ◃ λ{ (inl (inl s)) p → p ; (inl (inr t)) q → q ; (inr u) v → v }

lunit×ᶜ : ⊤ᶜ ×ᶜ SP →ᶜ SP
lunit×ᶜ = (λ (tt , s) → s) ◃ λ (tt , s) p → inr p

runit×ᶜ : SP ×ᶜ ⊤ᶜ →ᶜ SP
runit×ᶜ = (λ (s , tt) → s) ◃ λ (s , tt) p → inl p

comm×ᶜ : SP ×ᶜ TQ →ᶜ TQ ×ᶜ SP
comm×ᶜ = (λ (s , t) → t , s) ◃ λ{ (s , t) (inl q) → inr q ; (s , t) (inr p) → inl p }

assoc×ᶜ : (SP ×ᶜ TQ) ×ᶜ UV →ᶜ SP ×ᶜ (TQ ×ᶜ UV)
assoc×ᶜ = (λ ((s , t) , u) → s , t , u)
  ◃ λ{ ((s , t) , u) (inl p) → inl (inl p) ; ((s , t) , u) (inr (inl q)) → inl (inr q) ; ((s , t) , u) (inr (inr v)) → inr v }

labsᶜ : ⊥ᶜ ×ᶜ SP →ᶜ ⊥ᶜ
labsᶜ = (λ ()) ◃ λ ()

rabsᶜ : SP ×ᶜ ⊥ᶜ →ᶜ ⊥ᶜ
rabsᶜ = (λ ()) ◃ λ ()

ldistrᶜ : SP ×ᶜ (TQ ⊎ᶜ UV) →ᶜ SP ×ᶜ TQ ⊎ᶜ SP ×ᶜ UV
ldistrᶜ = (λ{ (s , inl t) → inl (s , t) ; (s , inr u) → inr (s , u) })
        ◃ λ{ (s , inl t) (inl p) → inl p ; (s , inl t) (inr q) → inr q
           ; (s , inr u) (inl p) → inl p ; (s , inr u) (inr v) → inr v }

rdistrᶜ : (SP ⊎ᶜ TQ) ×ᶜ UV →ᶜ SP ×ᶜ UV ⊎ᶜ TQ ×ᶜ UV
rdistrᶜ = (λ{ (inl s , u) → inl (s , u) ; (inr t , u) → inr (t , u) })
        ◃ λ{ (inl s , u) (inl p) → inl p ; (inl s , u) (inr v) → inr v
           ; (inr t , u) (inl q) → inl q ; (inr t , u) (inr v) → inr v }

-- Infinitary commutative semiring

module _ (I : Type) (J : I → Type) (F : (i : I) → J i → Cont) where

  assocΣᶜ : Σᶜ[ (i , j) ∈ Σ I J ] F i j →ᶜ Σᶜ[ i ∈ I ] Σᶜ[ j ∈ J i ] F i j
  assocΣᶜ = (λ ((i , j) , c) → i , j , c) ◃ λ s p → p

  curryᶜ : Πᶜ[ (i , j) ∈ Σ I J ] F i j →ᶜ Πᶜ[ i ∈ I ] Πᶜ[ j ∈ J i ] F i j
  curryᶜ = (λ c i j → c (i , j)) ◃ λ s (i , j , c) → (i , j) , c

  choiceᶜ : Σᶜ[ f ∈ ((i : I) → J i) ] Πᶜ[ i ∈ I ] F i (f i) →ᶜ Πᶜ[ i ∈ I ] Σᶜ[ j ∈ J i ] F i j
  choiceᶜ = (λ (f , g) i → f i , g i) ◃ λ s p → p

-- Composition

Iᶜ : Cont
Iᶜ = ⊤ ◃ λ{ tt → ⊤ }

infixr 3 _⊚ᶜ_

_⊚ᶜ_ : Cont → Cont → Cont
(S ◃ P) ⊚ᶜ (T ◃ Q) = (Σ[ s ∈ S ] (P s → T)) ◃ λ (s , f) → Σ[ p ∈ P s ] Q (f p)

_⊚ᶜ₁_ : SP →ᶜ TQ → SP' →ᶜ TQ' → SP ⊚ᶜ SP' →ᶜ TQ ⊚ᶜ TQ'
(g ◃ h) ⊚ᶜ₁ (g' ◃ h') = (λ (s , f) → g s , g' ∘ f ∘ h s)
  ◃ λ{ (s , f) (q , q') → h s q , h' (f (h s q)) q' }

λᶜ : Iᶜ ⊚ᶜ SP →ᶜ SP
λᶜ = (λ{ (tt , f) → f tt }) ◃ λ{ (tt , f) p → tt , p }

λ⁻ᶜ : SP →ᶜ Iᶜ ⊚ᶜ SP
λ⁻ᶜ = (λ s → tt , λ _ → s) ◃ λ{ s (tt , p) → p }

ρᶜ : SP ⊚ᶜ Iᶜ →ᶜ SP
ρᶜ = (λ{ (s , _) → s }) ◃ λ{ (s , _) p → p , tt }

ρ⁻ᶜ : SP →ᶜ SP ⊚ᶜ Iᶜ
ρ⁻ᶜ = (λ s → s , λ _ → tt) ◃ λ{ s (p , tt) → p }

αᶜ : (SP ⊚ᶜ TQ) ⊚ᶜ UV →ᶜ SP ⊚ᶜ (TQ ⊚ᶜ UV)
αᶜ = (λ{ ((s , f) , g) → s , λ p → (f p , λ q → g (p , q)) })
   ◃ λ{ ((s , f) , g) (p , (q , v)) → ((p , q) , v) }

α⁻ᶜ : SP ⊚ᶜ (TQ ⊚ᶜ UV) →ᶜ (SP ⊚ᶜ TQ) ⊚ᶜ UV
α⁻ᶜ = (λ{ (s , f) → (s , λ p → let (t , g) = f p in t) , λ (p , q) → let (t , g) = f p in g q })
     ◃ λ{ (s , f) ((p , q) , v) → (p , (q , v)) }

-- Finitary compositions

open import Cubical.Data.Nat
open import Cubical.Data.Fin

{-
Fin⊚ᶜ : {n : ℕ} → (Fin n → Cont) → Cont
Fin⊚ᶜ f = Fin⊚ᶜS f ◃ Fin⊚ᶜP f
  where
  Fin⊚ᶜS : {n : ℕ} → (Fin n → Cont) → Type
  Fin⊚ᶜS {zero} f = ⊤
  Fin⊚ᶜS {suc n} f with f zero
  ... | S ◃ P = Σ[ s ∈ S ] (P s → Fin⊚ᶜS {n} (f ∘ suc))

  Fin⊚ᶜP : {n : ℕ} (f : Fin n → Cont) → Fin⊚ᶜS {n} f → Type
  Fin⊚ᶜP {zero} f tt = ⊤
  Fin⊚ᶜP {suc n} f (s , g) with f zero
  ... | S ◃ P = Σ[ p ∈ P s ] Fin⊚ᶜP {n} (f ∘ suc) (g p)
-}
