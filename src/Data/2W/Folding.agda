module Data.2W.Folding where

open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Cont using (Cont; _→ᶜ_; _◃_)
open import Data.2Cont using (2Cont; _◃_+_+_; appS; appP; app)
open import Data.2W.Base

-- Folding

module _
  {H : 2Cont}
  {TQ : Cont}
  (α : app H TQ →ᶜ TQ)
  where

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

  auxP {S ◃ PX + PF + RF} (mk s f) (inj₁ pX) = posX pX
  auxP {S ◃ PX + PF + RF} (mk s f) (inj₂ (pF , q , rp)) =
      posF (pF , let (t , g) = f pF in
        fold2WP t q , auxP (g (fold2WP t q)) rp)

  fold2WS s = αS (auxS s)
  
  fold2WP s q = auxP s (αP (auxS s) q)

  aux : {H' : 2Cont} → 2W-d H' H →ᶜ app H' TQ
  aux = auxS ◃ auxP

  fold2W : 2W H →ᶜ TQ
  fold2W = fold2WS ◃ fold2WP
