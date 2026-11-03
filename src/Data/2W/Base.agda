{-# OPTIONS --cubical --guardedness #-}

module Data.2W.Base where

open import Prelude
open import Data.Cont
open import Data.2Cont

------------------------------------------------------------------------
-- Definition

record 2WS-d (H' H : 2Cont) : Type

data 2WP-d (H' H : 2Cont) (2ws : 2WS-d H' H) : Type

record 2WS-d H' H where
  constructor mk
  inductive
  pattern
  open 2Cont H'
  field
    s : S
    f : (pF : PF s) → Σ[ t ∈ 2WS-d H H ] (2WP-d H H t → 2WS-d (RF s pF) H)

data 2WP-d H' H ws where
  posX : (open 2Cont H') (open 2WS-d ws)
         → PX s
         → 2WP-d H' H ws
  posF : (open 2Cont H') (open 2WS-d ws)
         → (Σ[ pF ∈ PF s ] let (t , g) = f pF in
             Σ[ q ∈ 2WP-d H H t ] 2WP-d (RF s pF) H (g q))
         → 2WP-d H' H ws

2WS : 2Cont → Type
2WS H = 2WS-d H H

2WP : (H : 2Cont) → 2WS H → Type
2WP H = 2WP-d H H

2W-d : 2Cont → 2Cont → Cont
2W-d H' H = 2WS-d H' H ◃ 2WP-d H' H

2W : 2Cont → Cont
2W H = 2W-d H H

------------------------------------------------------------------------
-- Supremum

module _ {H : 2Cont} where

  2supS-d : {H' : 2Cont} → appS H' (2W H) → 2WS-d H' H
  2supS-d {S ◃ PX + PF + RF} (s , f) =
    mk s (λ pF → let (t , g) = f pF in t , λ q → 2supS-d {RF s pF} (g q))

  2supS : appS H (2W H) → 2WS H
  2supS = 2supS-d

  2supP-d : {H' : 2Cont} (s : appS H' (2W H)) → 2WP-d H' H (2supS-d s) → appP H' (2W H) s
  2supP-d {S ◃ PX + PF + RF} (s , f) (posX pX) =
    inl pX
  2supP-d {S ◃ PX + PF + RF} (s , f) (posF (pF , q , rp)) =
    let (t , g) = f pF in
      inr (pF , q , 2supP-d (g q) rp)

  2supP : (s : appS H (2W H)) → 2WP H (2supS s) → appP H (2W H) s
  2supP = 2supP-d

  2sup-d : {H' : 2Cont} → app H' (2W H) →ᶜ 2W-d H' H
  2sup-d = 2supS-d ◃ 2supP-d

  2sup : app H (2W H) →ᶜ 2W H
  2sup = 2sup-d

  2supS⁻-d : {H' : 2Cont} → 2WS-d H' H → appS H' (2W H)
  2supS⁻-d {S ◃ PX + PF + RF} (mk s f) = s , λ pF → let (t , g) = f pF in t , λ q → 2supS⁻-d (g q)

  2supP⁻-d : {H' : 2Cont} (s : 2WS-d H' H) → appP H' (2W H) (2supS⁻-d s) → 2WP-d H' H s
  2supP⁻-d {S ◃ PX + PF + RF} (mk s f) (inl pX) = posX pX
  2supP⁻-d {S ◃ PX + PF + RF} (mk s f) (inr (pF , q , rp)) =
    posF (pF , q , let (t , g) = f pF in 2supP⁻-d {RF s pF} (g q) rp)

  2sup⁻-d : {H' : 2Cont} → 2W-d H' H →ᶜ app H' (2W H)
  2sup⁻-d = 2supS⁻-d ◃ 2supP⁻-d

  2sup⁻ : 2W H →ᶜ app H (2W H)
  2sup⁻ = 2sup⁻-d

------------------------------------------------------------------------
-- Folding

module _ {H : 2Cont} {TQ : Cont} (α : app H TQ →ᶜ TQ) where

  open Cont TQ renaming (S to T ; P to Q)
  open _→ᶜ_ α renaming (fS to αS ; fP to αP)

  auxS : {H' : 2Cont} → 2WS-d H' H → appS H' TQ
  
  auxP : {H' : 2Cont} (s : 2WS-d H' H)
    → appP H' TQ (auxS s) → 2WP-d H' H s

  fold2WS : 2WS H → T
  
  fold2WP : (s : 2WS H) → Q (fold2WS s) → 2WP H s

  auxS {S ◃ PX + PF + RF} (mk s f) =
    s , λ pF → let (t , g) = f pF in 
      fold2WS t , λ q → auxS (g (fold2WP t q))

  auxP {S ◃ PX + PF + RF} (mk s f) (inl pX) =
    posX pX
  auxP {S ◃ PX + PF + RF} (mk s f) (inr (pF , q , rp)) =
    posF (pF , let (t , g) = f pF in
      fold2WP t q , auxP (g (fold2WP t q)) rp)

  fold2WS s = αS (auxS s)
  
  fold2WP s q = auxP s (αP (auxS s) q)

  aux : {H' : 2Cont} → 2W-d H' H →ᶜ app H' TQ
  aux = auxS ◃ auxP

  fold2W : 2W H →ᶜ TQ
  fold2W = fold2WS ◃ fold2WP
