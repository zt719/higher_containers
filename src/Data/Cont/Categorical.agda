module Data.Cont.Categorical where

open import Data.Unit using (⊤; tt) 
open import Data.Empty using (⊥; ⊥-elim) 
open import Data.Product
  using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; curry; uncurry)
  renaming (<_,_> to pair)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Function.Base using (id; _∘_)
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
  ◃ λ{ (s , s') (inj₁ p) → inj₁ (h s p) ; (s , s') (inj₂ p') → inj₂ (h' s' p') }

proj₁ᶜ : SP ×ᶜ TQ →ᶜ SP
proj₁ᶜ = proj₁ ◃ λ{ (S , T) p → inj₁ p }

proj₂ᶜ : SP ×ᶜ TQ →ᶜ TQ
proj₂ᶜ = proj₂ ◃ λ{ (S , T) q → inj₂ q }

pairᶜ : SP →ᶜ TQ → SP →ᶜ TQ' → SP →ᶜ TQ ×ᶜ TQ'
pairᶜ (f ◃ g) (f' ◃ g') = pair f f' ◃ λ{ s (inj₁ p) → g s p ; s (inj₂ q) → g' s q }

infixr 1 _⊎ᶜ_
_⊎ᶜ_ : Cont → Cont → Cont
(S ◃ P) ⊎ᶜ (T ◃ Q) = S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t }

_⊎ᶜ₁_ : SP →ᶜ TQ → SP' →ᶜ TQ' → SP ⊎ᶜ SP' →ᶜ TQ ⊎ᶜ TQ'
(g ◃ h) ⊎ᶜ₁ (g' ◃ h')
  = (λ{ (inj₁ s) → inj₁ (g s) ; (inj₂ s') → inj₂ (g' s') })
  ◃ λ{ (inj₁ s) p → h s p ; (inj₂ s') p' → h' s' p' }

inj₁ᶜ : SP →ᶜ SP ⊎ᶜ TQ
inj₁ᶜ = inj₁ ◃ λ s p → p

inj₂ᶜ : TQ →ᶜ SP ⊎ᶜ TQ
inj₂ᶜ = inj₂ ◃ λ s q → q

caseᶜ : SP →ᶜ TQ → SP' →ᶜ TQ → SP ⊎ᶜ SP' →ᶜ TQ
caseᶜ (f ◃ g) (f' ◃ g') = case f  f' ◃ λ{ (inj₁ s) p → g s p ; (inj₂ s') q → g' s' q }

-- Product and coproduct

private
  variable
    I : Set
    F G : I → Cont

Πᶜ : (I : Set) (F : I → Cont) → Cont
Πᶜ I F = ((i : I) → let S ◃ P = F i in S)
  ◃ λ f → Σ[ i ∈ I ] let S ◃ P = F i in P (f i)

infix 2 Πᶜ-syntax

Πᶜ-syntax : (I : Set) (F : I → Cont) → Cont
Πᶜ-syntax = Πᶜ

syntax Πᶜ-syntax A (λ x → B) = Πᶜ[ x ∈ A ] B

Πᶜ₁ : ((i : I) → F i →ᶜ G i) → Πᶜ I F →ᶜ Πᶜ I G
Πᶜ₁ f = (λ s i → let g ◃ h = f i in g (s i))
  ◃ λ s (i , p) → i , let g ◃ h = f i in h (s i) p

projᶜ : (i : I) → Πᶜ[ i ∈ I ] F i →ᶜ F i
projᶜ i = (λ f → f i) ◃ λ s p → i , p

Σᶜ : (I : Set) (F : I → Cont) → Cont
Σᶜ I F = (Σ[ i ∈ I ] let S ◃ P = F i in S)
  ◃ λ (i , s) → let S ◃ P = F i in P s

infix 2 Σᶜ-syntax

Σᶜ-syntax : (I : Set) (F : I → Cont) → Cont
Σᶜ-syntax = Σᶜ

syntax Σᶜ-syntax A (λ x → B) = Σᶜ[ x ∈ A ] B

Σᶜ₁ : ((i : I) → F i →ᶜ G i) → Σᶜ I F →ᶜ Σᶜ I G
Σᶜ₁ f = (λ (i , s) → i , let g ◃ h = f i in g s)
  ◃ λ (i , s) p → let g ◃ h = f i in h s p

injᶜ : (i : I) → F i →ᶜ Σᶜ[ i ∈ I ] F i
injᶜ i = (λ s → i , s) ◃ λ s p → p

-- Commutative semiring

lunit⊎ᶜ : ⊥ᶜ ⊎ᶜ SP →ᶜ SP
lunit⊎ᶜ = (λ{ (inj₂ s) → s }) ◃ λ{ (inj₂ s) p → p }

runit⊎ᶜ : SP ⊎ᶜ ⊥ᶜ →ᶜ SP
runit⊎ᶜ = (λ{ (inj₁ s) → s }) ◃ λ{ (inj₁ s) p → p }

comm⊎ᶜ : SP ⊎ᶜ TQ →ᶜ TQ ⊎ᶜ SP
comm⊎ᶜ = (λ{ (inj₁ s) → inj₂ s ; (inj₂ t) → inj₁ t }) ◃ λ{ (inj₁ t) q → q ; (inj₂ s) p → p }

assoc⊎ᶜ : (SP ⊎ᶜ TQ) ⊎ᶜ UV →ᶜ SP ⊎ᶜ (TQ ⊎ᶜ UV)
assoc⊎ᶜ = (λ{ (inj₁ (inj₁ s)) → inj₁ s ; (inj₁ (inj₂ t)) → inj₂ (inj₁ t) ; (inj₂ u) → inj₂ (inj₂ u) })
  ◃ λ{ (inj₁ (inj₁ s)) p → p ; (inj₁ (inj₂ t)) q → q ; (inj₂ u) v → v }

lunit×ᶜ : ⊤ᶜ ×ᶜ SP →ᶜ SP
lunit×ᶜ = (λ (tt , s) → s) ◃ λ (tt , s) p → inj₂ p

runit×ᶜ : SP ×ᶜ ⊤ᶜ →ᶜ SP
runit×ᶜ = (λ (s , tt) → s) ◃ λ (s , tt) p → inj₁ p

comm×ᶜ : SP ×ᶜ TQ →ᶜ TQ ×ᶜ SP
comm×ᶜ = (λ (s , t) → t , s) ◃ λ{ (s , t) (inj₁ q) → inj₂ q ; (s , t) (inj₂ p) → inj₁ p }

assoc×ᶜ : (SP ×ᶜ TQ) ×ᶜ UV →ᶜ SP ×ᶜ (TQ ×ᶜ UV)
assoc×ᶜ = (λ ((s , t) , u) → s , t , u)
  ◃ λ{ ((s , t) , u) (inj₁ p) → inj₁ (inj₁ p) ; ((s , t) , u) (inj₂ (inj₁ q)) → inj₁ (inj₂ q) ; ((s , t) , u) (inj₂ (inj₂ v)) → inj₂ v }

labsᶜ : ⊥ᶜ ×ᶜ SP →ᶜ ⊥ᶜ
labsᶜ = (λ ()) ◃ λ ()

rabsᶜ : SP ×ᶜ ⊥ᶜ →ᶜ ⊥ᶜ
rabsᶜ = (λ ()) ◃ λ ()

ldistrᶜ : SP ×ᶜ (TQ ⊎ᶜ UV) →ᶜ SP ×ᶜ TQ ⊎ᶜ SP ×ᶜ UV
ldistrᶜ = (λ{ (s , inj₁ t) → inj₁ (s , t) ; (s , inj₂ u) → inj₂ (s , u) })
        ◃ λ{ (s , inj₁ t) (inj₁ p) → inj₁ p ; (s , inj₁ t) (inj₂ q) → inj₂ q
           ; (s , inj₂ u) (inj₁ p) → inj₁ p ; (s , inj₂ u) (inj₂ v) → inj₂ v }

rdistrᶜ : (SP ⊎ᶜ TQ) ×ᶜ UV →ᶜ SP ×ᶜ UV ⊎ᶜ TQ ×ᶜ UV
rdistrᶜ = (λ{ (inj₁ s , u) → inj₁ (s , u) ; (inj₂ t , u) → inj₂ (t , u) })
        ◃ λ{ (inj₁ s , u) (inj₁ p) → inj₁ p ; (inj₁ s , u) (inj₂ v) → inj₂ v
           ; (inj₂ t , u) (inj₁ q) → inj₁ q ; (inj₂ t , u) (inj₂ v) → inj₂ v }

-- Infinitary commutative semiring

module _ (I : Set) (J : I → Set) (F : (i : I) → J i → Cont) where

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

Fin⊚ᶜ : {n : ℕ} → (Fin n → Cont) → Cont
Fin⊚ᶜ f = Fin⊚ᶜS f ◃ Fin⊚ᶜP f
  where
  Fin⊚ᶜS : {n : ℕ} → (Fin n → Cont) → Set
  Fin⊚ᶜS {zero} f = ⊤
  Fin⊚ᶜS {suc n} f with f zero
  ... | S ◃ P = Σ[ s ∈ S ] (P s → Fin⊚ᶜS {n} (f ∘ suc))

  Fin⊚ᶜP : {n : ℕ} (f : Fin n → Cont) → Fin⊚ᶜS {n} f → Set
  Fin⊚ᶜP {zero} f tt = ⊤
  Fin⊚ᶜP {suc n} f (s , g) with f zero
  ... | S ◃ P = Σ[ p ∈ P s ] Fin⊚ᶜP {n} (f ∘ suc) (g p)
