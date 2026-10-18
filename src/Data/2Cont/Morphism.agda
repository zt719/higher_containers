{-# OPTIONS --without-K #-}

module Data.2Cont.Morphism where

open import Data.2Cont.Base
open import Data.Product
open import Data.Sum
open import Data.Cont

------------------------------------------------------------------------
-- Definition

record _→²ᶜ_ (H J : 2Cont) : Set₁ where
  pattern
  inductive
  constructor _◃_+_+_
  open 2Cont H
  open 2Cont J renaming
    (S to T ; PX to QX ; PF to QF ; RF to LF)
  field
    fS : S → T
    fPX : (s : S) → QX (fS s) → PX s
    fPF : (s : S) → QF (fS s) → PF s
    fRF : (s : S) (qF : QF (fS s)) → RF s (fPF s qF) →²ᶜ LF (fS s) qF

-- Interpretation / Application

app→²ᶜS : {H J : 2Cont} → H →²ᶜ J
      → (F : Cont) → appS H F → appS J F
app→²ᶜS {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (αS ◃ αPX + αPF + αRF) F (s , f)
  = αS s , λ qF → let (t , g) = f (αPF s qF) in t , λ q → app→²ᶜS (αRF s qF) F (g q)

app→²ᶜP : {H J : 2Cont} (α : H →²ᶜ J) (F : Cont) (s : appS H F) → appP J F (app→²ᶜS α F s) → appP H F s
app→²ᶜP {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (αS ◃ αPX + αPF + αRF) F (s , f) (inj₁ pX) =
  inj₁ (αPX s pX)
app→²ᶜP {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (αS ◃ αPX + αPF + αRF) F (s , f) (inj₂ (pF , q , rp)) =
  let (t , g) = f (αPF s pF) in
    inj₂ (αPF s pF , q , app→²ᶜP (αRF s pF) F (g q) rp)

app→²ᶜ : {H J : 2Cont}
         → H →²ᶜ J
         → (F : Cont) → app H F →ᶜ app J F
app→²ᶜ α F = app→²ᶜS α F ◃ app→²ᶜP α F
