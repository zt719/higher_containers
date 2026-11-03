{-# OPTIONS --cubical --guardedness #-}

module Data.2Cont.Base where

open import Prelude
open import Data.Cont

------------------------------------------------------------------------
-- Definition

record 2Cont : Type₁ where
  pattern
  inductive
  constructor _◃_+_+_
  field
    S : Type
    PX : S → Type
    PF : S → Type
    RF : (s : S) → PF s → 2Cont

-- Interpretation / Application

appS : 2Cont → Cont → Type
appS (S ◃ PX + PF + RF) (T ◃ Q) =
  Σ[ s ∈ S ] ((pF : PF s) → Σ[ t ∈ T ] (Q t → appS (RF s pF) (T ◃ Q)))

appP : (H : 2Cont) (F : Cont) → appS H F → Type
appP (S ◃ PX + PF + RF) (T ◃ Q) (s , f) =
  PX s ⊎ (Σ[ pF ∈ PF s ] let (t , g) = f pF in
    Σ[ q ∈ Q t ] appP (RF s pF) (T ◃ Q) (g q))

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
appP₁ (S ◃ PX + PF + RF) (αS ◃ αP) (s , f) (inl pX) =
  inl pX
appP₁ (S ◃ PX + PF + RF) (αS ◃ αP) (s , f) (inr (pF , q , rp)) =
  let (t , g) = f pF in
    inr (pF , αP t q , appP₁ (RF s pF) (αS ◃ αP) (g (αP t q)) rp)

app₁ : (H : 2Cont)
       {TQ UV : Cont}
       → TQ →ᶜ UV
       → app H TQ →ᶜ app H UV
app₁ H α = appS₁ H α ◃ appP₁ H α

2⟦_⟧ : 2Cont → (Type → Type) → Type → Type
2⟦ S ◃ PX + PF + RF ⟧ F X =
  Σ[ s ∈ S ] ((PX s → X) × ((pF : PF s) → F (2⟦ RF s pF ⟧ F X)))
