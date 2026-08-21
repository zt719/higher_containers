open import Data.Product
open import Data.Sum
open import Function.Base
open import Relation.Binary.PropositionalEquality

infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

infixr 0 _→ᶜ_
record _→ᶜ_ (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    fS : S → T
    fP : (s : S) → Q (fS s) → P s

→ᶜ≡ : {S : Set} {P : S → Set} {T : Set} {Q : T → Set}
  → (fS fS' : S → T)
  → (fP : (s : S) → Q (fS s) → P s)
  → (fP' : (s : S) → Q (fS' s) → P s)
  → (eq : fS ≡ fS')
  → subst (λ fS → (s : S) → Q (fS s) → P s) eq fP ≡ fP'
  → _≡_ {A = (S ◃ P) →ᶜ (T ◃ Q)} (fS ◃ fP) (fS' ◃ fP')
→ᶜ≡ fS fS' fP fP' refl refl = refl

infixr 9 _∘ᶜ_
_∘ᶜ_ : {SP TQ UV : Cont} → TQ →ᶜ UV → SP →ᶜ TQ → SP →ᶜ UV
(fT ◃ fQ) ∘ᶜ (fS ◃ fP) = (fT ∘ fS) ◃ λ s → fP s ∘ fQ (fS s)

record Cont2 : Set₁ where
  pattern
  inductive
  constructor _◃_+_+_
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → Cont2

appS : Cont2 → Cont → Set
appS (S ◃ PX + PF + RF) (T ◃ Q) =
  Σ[ s ∈ S ] ((pF : PF s) → Σ[ t ∈ T ] (Q t → appS (RF s pF) (T ◃ Q)))

appP : (H : Cont2) (F : Cont) → appS H F → Set
appP (S ◃ PX + PF + RF) (T ◃ Q) (s , f) =
  PX s ⊎ Σ[ pF ∈ PF s ] let (t , g) = f pF in Σ[ q ∈ Q t ] appP (RF s pF) (T ◃ Q) (g q)

app : Cont2 → Cont → Cont
app H F = appS H F ◃ appP H F

appS₁ : (H : Cont2) {TQ UV : Cont} → TQ →ᶜ UV → appS H TQ → appS H UV
appS₁ (S ◃ PX + PF + RF) (fT ◃ fQ) (s , f) =
  s , λ pF → let (t , g) = f pF in fT t , λ q → appS₁ (RF s pF) (fT ◃ fQ) (g (fQ t q))

appP₁ : (H : Cont2) {TQ UV : Cont} (α : TQ →ᶜ UV) (s : appS H TQ) → appP H UV (appS₁ H α s) → appP H TQ s
appP₁ (S ◃ PX + PF + RF) (fT ◃ fQ) (s , f) (inj₁ pX) =
  inj₁ pX
appP₁ (S ◃ PX + PF + RF) (fT ◃ fQ) (s , f) (inj₂ (pF , v , p')) =
  inj₂ (pF , let (t , g) = f pF in (fQ t v , appP₁ (RF s pF) (fT ◃ fQ) (g (fQ t v)) p'))

app₁ : (H : Cont2) {TQ UV : Cont} → TQ →ᶜ UV → app H TQ →ᶜ app H UV
app₁ H α = appS₁ H α ◃ appP₁ H α

record 2WS-d (H' H : Cont2) : Set

data 2WP-d (H' H : Cont2) (ws : 2WS-d H' H) : Set

record 2WS-d H' H where
  constructor mk
  inductive
  pattern
  open Cont2 H'
  field
    s : S
    f : (pF : PF s) → Σ[ t ∈ 2WS-d H H ] (2WP-d H H t → 2WS-d (RF s pF) H)

data 2WP-d H' H ws where
  posX : (open Cont2 H') (open 2WS-d ws)
    → PX s
    → 2WP-d H' H ws
  posF : (open Cont2 H') (open 2WS-d ws)
    → (Σ[ pF ∈ PF s ] let (t , g) = f pF in Σ[ q ∈ 2WP-d H H t ] 2WP-d (RF s pF) H (g q))
    → 2WP-d H' H ws

2WS : Cont2 → Set
2WS H = 2WS-d H H

2WP : (H : Cont2) → 2WS H → Set
2WP H = 2WP-d H H

2W-d : Cont2 → Cont2 → Cont
2W-d H' H = 2WS-d H' H ◃ 2WP-d H' H

2W : Cont2 → Cont
2W H = 2W-d H H

2supS-d : {H' H : Cont2} → appS H' (2W H) → 2WS-d H' H
2supS-d {S ◃ PX + PF + RF} (s , f) =
  mk s (λ pF → let (t , g) = f pF in t , λ q → 2supS-d {RF s pF} (g q))

2supS : {H : Cont2} → appS H (2W H) → 2WS H
2supS = 2supS-d

2supP-d : {H' H : Cont2} (sf : appS H' (2W H)) → 2WP-d H' H (2supS-d sf) → appP H' (2W H) sf
2supP-d {S ◃ PX + PF + RF} (s , f) (posX pX) = inj₁ pX
2supP-d {S ◃ PX + PF + RF} (s , f) (posF (pF , q , rp)) =
  inj₂ (pF , q , let (t , g) = f pF in 2supP-d (g q) rp)

2sup-d : {H' H : Cont2} → app H' (2W H) →ᶜ 2W-d H' H
2sup-d = 2supS-d ◃ 2supP-d

2sup : {H : Cont2} → app H (2W H) →ᶜ 2W H
2sup = 2sup-d

2supS-dᵢ : {H' H : Cont2} → 2WS-d H' H → appS H' (2W H)
2supS-dᵢ {S ◃ PX + PF + RF} (mk s f) = s , λ pF → let (t , g) = f pF in t , λ q → 2supS-dᵢ (g q)

2supP-dᵢ : {H' H : Cont2} (ws : 2WS-d H' H) → appP H' (2W H) (2supS-dᵢ ws) → 2WP-d H' H ws
2supP-dᵢ {S ◃ PX + PF + RF} (mk s f) (inj₁ pX) = posX pX
2supP-dᵢ {S ◃ PX + PF + RF} (mk s f) (inj₂ (pF , q , rp)) =
  posF (pF , q , let (t , g) = f pF in 2supP-dᵢ (g q) rp)

2sup-dᵢ : {H' H : Cont2} → 2W-d H' H →ᶜ app H' (2W H)
2sup-dᵢ = 2supS-dᵢ ◃ 2supP-dᵢ

2supᵢ : {H : Cont2} → 2W H →ᶜ app H (2W H)
2supᵢ = 2sup-dᵢ

{- folding  -}
module _
  {H : Cont2}
  {TQ : Cont}
  (α : app H TQ →ᶜ TQ)
  where

  open Cont TQ renaming (S to T ; P to Q)
  open _→ᶜ_ α renaming (fS to αS ; fP to αP)

  auxS : {H' : Cont2} → 2WS-d H' H → appS H' TQ
  
  auxP : {H' : Cont2} (ws : 2WS-d H' H)
    → appP H' TQ (auxS ws) → 2WP-d H' H ws

  {- aux shoud be app H (fold H) ∘ 2supᵢ -}

  fold2WS : 2WS H → T
  
  fold2WP : (ws : 2WS H) → Q (fold2WS ws) → 2WP H ws

  auxS {S ◃ PX + PF + RF} (mk s f) = s , λ pF → let (t , g) = f pF in 
    fold2WS t , λ q → auxS (g (fold2WP t q))

  auxP {S ◃ PX + PF + RF} (mk s f) (inj₁ pX) =
    posX pX
  auxP {S ◃ PX + PF + RF} (mk s f) (inj₂ (pF , q , rp)) =
    let (t , g) = f pF in posF (pF , fold2WP t q , auxP (g (fold2WP t q)) rp)

  fold2WS ws = αS (auxS ws)
  
  fold2WP ws q = auxP ws (αP (auxS ws) q)

  aux : {H' : Cont2} → 2W-d H' H →ᶜ app H' TQ
  aux = auxS ◃ auxP

  fold2W : 2W H →ᶜ TQ
  fold2W = fold2WS ◃ fold2WP

{-
{- eliminator -}

{- WARNING : maybe wrong -}
module 2WElim
  {H : Cont2}
  (WSᴾ : {H' : Cont2} → 2WS-d H' H → Set)
  (WPᴾ : {H' : Cont2} (ws : 2WS-d H' H) → 2WP-d H' H ws → Set)
  
  (mkᴾ : {H' : Cont2} (open Cont2 H')
    (s : S)
    (f : (pF : PF s) → Σ[ t ∈ 2WS-d H H ] (2WP-d H H t → 2WS-d (RF s pF) H))
    (fᴾ : (pF : PF s) → let (t , g) = f pF in WSᴾ t ×
      ((q : 2WP-d H H t) → WPᴾ t q × WSᴾ (g q) × ((rp : 2WP-d (RF s pF) H (g q))
      → WPᴾ (g q) rp)))
    → WSᴾ {H'} (mk s f))
    
  (posXᴾ :
    {H' : Cont2} (open Cont2 H')
    (ws : 2WS-d H' H) (open 2WS-d ws)
    (pX : PX s)
    → WPᴾ ws (posX pX))

  (posFᴾ :
    {H' : Cont2} (open Cont2 H')
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

  elimS : {H' : Cont2} (ws : 2WS-d H' H) → WSᴾ ws

  elimP : {H' : Cont2} (ws : 2WS-d H' H) (wp : 2WP-d H' H ws) → WPᴾ ws wp

  elimS (mk s f) = mkᴾ s f λ pF → let (t , g) = f pF in
    elimS t , λ q → elimP t q , elimS (g q) , λ rp → elimP (g q) rp

  elimP w (posX pX) =
    posXᴾ w pX
  elimP (mk s f) (posF (pF , q , rp)) = let (t , g) = f pF in
    posFᴾ (mk s f) pF q rp (elimS t) (elimP t q) (elimS (g q)) (elimP (g q) rp)
-}
