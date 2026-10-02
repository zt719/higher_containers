{-# OPTIONS --guardedness #-}

module Data.2M.Base where

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Cont using (Cont; _→ᶜ_; _◃_)
open import Data.2Cont using (2Cont; _◃_+_+_; appS; appP; app)

------------------------------------------------------------------------
-- Definition

record 2MS-d (H' H : 2Cont) : Set

data 2MP-d (H' H : 2Cont) (2ws : 2MS-d H' H) : Set

record 2MS-d H' H where
  coinductive
  open 2Cont H'
  field
    s : S
    f : (pF : PF s) → Σ[ t ∈ 2MS-d H H ] (2MP-d H H t → 2MS-d (RF s pF) H)

data 2MP-d H' H ws where
  posX : (open 2Cont H') (open 2MS-d ws)
         → PX s
         → 2MP-d H' H ws
  posF : (open 2Cont H') (open 2MS-d ws)
         → (Σ[ pF ∈ PF s ] let (t , g) = f pF in
             Σ[ q ∈ 2MP-d H H t ] 2MP-d (RF s pF) H (g q))
         → 2MP-d H' H ws

2MS : 2Cont → Set
2MS H = 2MS-d H H

2MP : (H : 2Cont) → 2MS H → Set
2MP H = 2MP-d H H

2M-d : 2Cont → 2Cont → Cont
2M-d H' H = 2MS-d H' H ◃ 2MP-d H' H

2M : 2Cont → Cont
2M H = 2M-d H H

------------------------------------------------------------------------
-- Infimum

module _ {H : 2Cont} where

  2infS-d : {H′ : 2Cont} → 2MS-d H′ H → appS H′ (2M H)
  2infS-d {S ◃ PX + PF + RF} ms =
    let s = ms .2MS-d.s
        f = ms .2MS-d.f in
    s , λ pF →
    let (t , g) = f pF in
    t , λ q → 2infS-d {RF s pF} (g q)

  2infP-d : {H′ : 2Cont}
            (s : 2MS-d H′ H)
            → appP H′ (2M H) (2infS-d s)
            → 2MP-d H′ H s
  2infP-d {S ◃ PX + PF + RF} ms (inj₁ pX) =
    posX pX
  2infP-d {S ◃ PX + PF + RF} ms (inj₂ (pF , q , rp)) =
    let s = ms .2MS-d.s
        f = ms .2MS-d.f
        (t , g) = f pF  in
    posF (pF , q , 2infP-d {RF s pF} (g q) rp)

  2inf-d : {H′ : 2Cont} → 2M-d H′ H →ᶜ app H′ (2M H)
  2inf-d = 2infS-d ◃ 2infP-d

  2inf : 2M H →ᶜ app H (2M H)
  2inf = 2inf-d


------------------------------------------------------------------------
-- Unfolding

module _ {H : 2Cont} {TQ : Cont} (α : TQ →ᶜ app H TQ) where

  open Cont TQ renaming (S to T ; P to Q)
  open _→ᶜ_ α renaming (fS to αS ; fP to αP)

  auxS : {H′ : 2Cont} → appS H′ TQ → 2MS-d H′ H

  auxP : {H′ : 2Cont} (t : appS H′ TQ)
    → 2MP-d H′ H (auxS t) → appP H′ TQ t

  unfold2MS : T → 2MS H

  unfold2MP : (t : T) → 2MP H (unfold2MS t) → Q t

  auxS {S ◃ PX + PF + RF} (s , f) .2MS-d.s = s
  auxS {S ◃ PX + PF + RF} (s , f) .2MS-d.f =
    λ pF → let (t , g) = f pF in
      unfold2MS t , λ q → auxS {RF s pF} (g (unfold2MP t q))

  auxP {S ◃ PX + PF + RF} (s , f) (posX pX) = inj₁ pX
  auxP {S ◃ PX + PF + RF} (s , f) (posF (pF , q , rp)) =
    let (t , g) = f pF in
      inj₂ (pF , unfold2MP t q , auxP {RF s pF} (g (unfold2MP t q)) rp)

  unfold2MS s = auxS (αS s)

  unfold2MP s q = αP s (auxP (αS s) q)

  aux : {H′ : 2Cont} → app H′ TQ →ᶜ 2M-d H′ H
  aux = auxS ◃ auxP

  unfold2M : TQ →ᶜ 2M H
  unfold2M = unfold2MS ◃ unfold2MP
