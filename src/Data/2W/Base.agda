module Data.2W.Base where

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Cont using (Cont; _→ᶜ_; _◃_)
open import Data.2Cont using (2Cont; _◃_+_+_; appS; appP; app)

------------------------------------------------------------------------
-- Definition

record 2WS-d (H' H : 2Cont) : Set

data 2WP-d (H' H : 2Cont) (2ws : 2WS-d H' H) : Set

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

2WS : 2Cont → Set
2WS H = 2WS-d H H

2WP : (H : 2Cont) → 2WS H → Set
2WP H = 2WP-d H H

2W-d : 2Cont → 2Cont → Cont
2W-d H' H = 2WS-d H' H ◃ 2WP-d H' H

2W : 2Cont → Cont
2W H = 2W-d H H

------------------------------------------------------------------------
-- Induction

module _
  {H : 2Cont}
  (WSᴾ : {H' : 2Cont} → 2WS-d H' H → Set)
  (WPᴾ : {H' : 2Cont} (ws : 2WS-d H' H) → 2WP-d H' H ws → Set)
  
  (mkᴾ : {H' : 2Cont} (open 2Cont H')
         (s : S)
         (f : (pF : PF s) → Σ[ t ∈ 2WS-d H H ] (2WP-d H H t → 2WS-d (RF s pF) H))
         (fᴾ : (pF : PF s) → let (t , g) = f pF in
           WSᴾ t × ((q : 2WP-d H H t)
             → WPᴾ t q × WSᴾ (g q) × ((rp : 2WP-d (RF s pF) H (g q))
               → WPᴾ (g q) rp)))
         → WSᴾ {H'} (mk s f))

  (posXᴾ : {H' : 2Cont} (open 2Cont H')
           (ws : 2WS-d H' H) (open 2WS-d ws)
           (pX : PX s)
           → WPᴾ ws (posX pX))

  (posFᴾ : {H' : 2Cont} (open 2Cont H')
           (ws : 2WS-d H' H) (open 2WS-d ws)
           (pF : PF s) → let (t , g) = f pF in 
           (q : 2WP-d H H t)
           (rp : 2WP-d (RF s pF) H (g q))
           → WSᴾ t
           → WPᴾ t q
           → WSᴾ (g q)
           → WPᴾ (g q) rp
           → WPᴾ ws (posF (pF , q , rp)))
  where

  elimS : {H' : 2Cont} (ws : 2WS-d H' H) → WSᴾ ws

  elimP : {H' : 2Cont} (ws : 2WS-d H' H) (wp : 2WP-d H' H ws) → WPᴾ ws wp

  elimS (mk s f) = mkᴾ s f λ pF → let (t , g) = f pF in
    elimS t , λ q → elimP t q , elimS (g q) , elimP (g q)

  elimP w (posX pX) =
    posXᴾ w pX
  elimP (mk s f) (posF (pF , q , rp)) = let (t , g) = f pF in
    posFᴾ (mk s f) pF q rp (elimS t) (elimP t q) (elimS (g q)) (elimP (g q) rp)

------------------------------------------------------------------------
-- Supremum

module _ {H : 2Cont} where

  2supS-d : {H' : 2Cont} → appS H' (2W H) → 2WS-d H' H
  2supS-d {S ◃ PX + PF + RF} (s , f) =
    mk s (λ pF → let (t , g) = f pF in t , λ q → 2supS-d {RF s pF} (g q))

  2supS : appS H (2W H) → 2WS H
  2supS = 2supS-d

  2supP-d : {H' : 2Cont} (s : appS H' (2W H)) → 2WP-d H' H (2supS-d s) → appP H' (2W H) s
  2supP-d {S ◃ PX + PF + RF} (s , f) (posX pX) = inj₁ pX
  2supP-d {S ◃ PX + PF + RF} (s , f) (posF (pF , q , rp)) =
    inj₂ (pF , q , let (t , g) = f pF in 2supP-d (g q) rp)

  2supP : (s : appS H (2W H)) → 2WP H (2supS s) → appP H (2W H) s
  2supP = 2supP-d

  2sup-d : {H' : 2Cont} → app H' (2W H) →ᶜ 2W-d H' H
  2sup-d = 2supS-d ◃ 2supP-d

  2sup : app H (2W H) →ᶜ 2W H
  2sup = 2sup-d
