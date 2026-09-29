module Data.2Cont.Base where

open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Cont using (Cont; _◃_; _→ᶜ_)

------------------------------------------------------------------------
-- Definition

record 2Cont : Set₁ where
  pattern
  inductive
  constructor _◃_+_+_
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

-- Interpretation / Application

appS : 2Cont → Cont → Set
appS (S ◃ PX + PF + RF) (T ◃ Q) =
  Σ[ s ∈ S ] ((pF : PF s) → Σ[ t ∈ T ] (Q t → appS (RF s pF) (T ◃ Q)))

appP : (H : 2Cont) (F : Cont) → appS H F → Set
appP (S ◃ PX + PF + RF) (T ◃ Q) (s , f) =
  PX s ⊎ Σ[ pF ∈ PF s ] let (t , g) = f pF in
    Σ[ q ∈ Q t ] appP (RF s pF) (T ◃ Q) (g q)

app : 2Cont → Cont → Cont
app H F = appS H F ◃ appP H F

appS₁ : (H : 2Cont) {TQ UV : Cont}
        → TQ →ᶜ UV
        → appS H TQ → appS H UV
appS₁ (S ◃ PX + PF + RF) (αS ◃ αP) (s , f) =
  s , λ pF → let (t , g) = f pF in
    αS t , λ q → appS₁ (RF s pF) (αS ◃ αP) (g (αP t q))

appP₁ : (H : 2Cont) {TQ UV : Cont}
        (α : TQ →ᶜ UV)
        (s : appS H TQ) → appP H UV (appS₁ H α s) → appP H TQ s
appP₁ (S ◃ PX + PF + RF) (αS ◃ αP) (s , f) (inj₁ pX) = inj₁ pX
appP₁ (S ◃ PX + PF + RF) (αS ◃ αP) (s , f) (inj₂ (pF , q , rp)) =
  inj₂ (pF , let (t , g) = f pF in
    αP t q , appP₁ (RF s pF) (αS ◃ αP) (g (αP t q)) rp)

app₁ : (H : 2Cont)
       {TQ UV : Cont}
       → TQ →ᶜ UV
       → app H TQ →ᶜ app H UV
app₁ H α = appS₁ H α ◃ appP₁ H α
