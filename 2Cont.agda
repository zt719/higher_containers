{-# OPTIONS --guardedness #-}

module 2Cont where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_]; J)

open import Cont

record 2Cont : Set₁ where
  inductive
  pattern
  constructor _◃_+_+_
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

variable H J SPPR TQQL : 2Cont

2⟦_⟧T : 2Cont → (Set → Set) → Set → Set
2⟦ S ◃ PX + PF + RF ⟧T F X
  = Σ[ s ∈ S ] (PX s → X × ((pF : PF s) → 2⟦ RF s pF ⟧T F X))

2⟦_⟧S : (H : 2Cont) (TQ : Cont) → Set
2⟦ S ◃ PX + PF + RF ⟧S (T ◃ Q) = Σ[ s ∈ S ] ((pF : PF s) → Σ[ t ∈ T ] (Q t → 2⟦ RF s pF ⟧S (T ◃ Q)))

2⟦_⟧P : (H : 2Cont) (TQ : Cont) → 2⟦ H ⟧S TQ → Set
2⟦ S ◃ PX + PF + RF ⟧P (T ◃ Q) (s , f) =
  Σ[ pF ∈ PF s ] let (t , f') = f pF in
    Σ[ q ∈ Q t ] (2⟦ RF s pF ⟧P (T ◃ Q) (f' q) ⊎ PX s)

2⟦_⟧ : 2Cont → Cont → Cont
2⟦ H ⟧ F = 2⟦ H ⟧S F ◃ 2⟦ H ⟧P F

2⟦_⟧S₁ : (H : 2Cont) → TQ →ᶜ UV → 2⟦ H ⟧S TQ → 2⟦ H ⟧S UV
2⟦ S ◃ PX + PF + RF ⟧S₁ (fT ◃ fQ) (s , f) =
  s , λ pF → let (t , f') = f pF in fT t , λ q → 2⟦ RF s pF ⟧S₁ (fT ◃ fQ) (f' (fQ t q))

2⟦_⟧P₁ : (H : 2Cont) (α : TQ →ᶜ UV) (s : 2⟦ H ⟧S TQ) → 2⟦ H ⟧P UV (2⟦ H ⟧S₁ α s) → 2⟦ H ⟧P TQ s
2⟦ S ◃ PX + PF + RF ⟧P₁ (fT ◃ fQ) (s , f) (pF , q , inj₁ p')
  = let (t , f') = f pF in pF , fQ t q , inj₁ (2⟦ RF s pF ⟧P₁ (fT ◃ fQ) (f' (fQ t q)) p')
2⟦ S ◃ PX + PF + RF ⟧P₁ (fT ◃ fQ) (s , f) (pF , q , inj₂ px)
  = let (t , f') = f pF in pF , fQ t q , inj₂ px

2⟦_⟧₁ : (H : 2Cont) → TQ →ᶜ UV → 2⟦ H ⟧ TQ →ᶜ 2⟦ H ⟧ UV
2⟦ H ⟧₁ α = 2⟦ H ⟧S₁ α ◃ 2⟦ H ⟧P₁ α

record _→²ᶜ_ (SPPR TQQL : 2Cont) : Set₁ where
  inductive
  constructor _◃_+_+_
  pattern
  open 2Cont SPPR
  open 2Cont TQQL renaming (S to T; PX to QX; PF to QF; RF to LF)
  field
    fS : S → T
    fPX : (s : S) → QX (fS s) → PX s
    fPF : (s : S) → QF (fS s) → PF s
    fRF : (s : S) (qF : QF (fS s)) → RF s (fPF s qF) →²ᶜ LF (fS s) qF

⟦_⟧→²ᶜ : H →²ᶜ J → (F : Cont) → 2⟦ H ⟧ F →ᶜ 2⟦ J ⟧ F
⟦ α ⟧→²ᶜ F = gS α F ◃ gP α F
  where
  gS : H →²ᶜ J → (F : Cont) → 2⟦ H ⟧S F → 2⟦ J ⟧S F
  gS {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (fS ◃ fPX + fPF + fRF) F (s , f)
    = fS s , λ qF → let (u , f') = f (fPF s qF) in u , λ v → gS (fRF s qF) F (f' v)

  gP : (α : H →²ᶜ J) (F : Cont) (s : 2⟦ H ⟧S F) → 2⟦ J ⟧P F (gS α F s) → 2⟦ H ⟧P F s
  gP {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (fS ◃ fPX + fPF + fRF) F (s , f) (qF , v , inj₁ pr)
    = fPF s qF , let (u , f') = f (fPF s qF) in v , inj₁ (gP (fRF s qF) F (f' v) pr)
  gP {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (fS ◃ fPX + fPF + fRF) F (s , f) (qF , v , inj₂ qX)
    = fPF s qF , v , inj₂ (fPX s qX)

{- 2W -}

record 2WS' (H H' : 2Cont) : Set

2WP' : (H H' : 2Cont) → 2WS' H H' → Set

record 2WS' H H' where
  constructor _,_
  inductive
  pattern
  open 2Cont H'
  field
    s : S
    f : (pF : PF s) → Σ[ t ∈ 2WS' H H ] (2WP' H H t → 2WS' H (RF s pF))

2WP' H (S ◃ PX + PF + RF) (s , f) =
  Σ[ pF ∈ PF s ] let (s' , f') = f pF in
  Σ[ q ∈ 2WP' H H s' ] (2WP' H (RF s pF) (f' q) ⊎ PX s)

2W : 2Cont → Cont
2W H = 2WS' H H ◃ 2WP' H H

2supS' : {H H' : 2Cont} → 2⟦ H' ⟧S (2W H) → 2WS' H H'
2supS' {H} {S ◃ PX + PF + RF} (s , f) = s , λ pF → let (s' , f') = f pF in s' , λ p' → 2supS' (f' p')

2supP' : {H H' : 2Cont} (s : 2⟦ H' ⟧S (2W H)) →
  2WP' H H' (2supS' s) → 2⟦ H' ⟧P (2W H) s
2supP' {H} {S ◃ PX + PF + RF} (s , f) (pF , p' , inj₁ pR) =
  let (s' , f') = f pF in pF , p' , inj₁ (2supP' (f' p') pR)
2supP' {H} {S ◃ PX + PF + RF} (s , f) (pF , p' , inj₂ pX) =
  pF , p' , inj₂ pX

2sup : {H : 2Cont} → 2⟦ H ⟧ (2W H) →ᶜ 2W H
2sup = 2supS' ◃ 2supP'

2supS'⁻ : {H H' : 2Cont} → 2WS' H H' → 2⟦ H' ⟧S (2W H)
2supS'⁻ {H} {S ◃ PX + PF + RF} (s , f) =
  s , λ pF → let (s' , f') = f pF in s' , λ p' → 2supS'⁻ (f' p')

2supP'⁻ : {H H' : 2Cont} (s : 2WS' H H')
  → 2⟦ H' ⟧P (2W H) (2supS'⁻ s) → 2WP' H H' s
2supP'⁻ {H} {S ◃ PX + PF + RF} (s , f) (pF , p' , inj₁ pr) =
  let (s' , f') = f pF in pF , p' , inj₁ (2supP'⁻ (f' p') pr)
2supP'⁻ {H} {S ◃ PX + PF + RF} (s , f) (pF , p' , inj₂ pX) =
  pF , p' , inj₂ pX
   
2sup⁻ : {H : 2Cont} → 2W H →ᶜ 2⟦ H ⟧ (2W H)
2sup⁻ = 2supS'⁻ ◃ 2supP'⁻

{- Example -- List -}

ListSig : (Set → Set) → Set → Set
ListSig F X = ⊤ ⊎ F X

ListSigCont : 2Cont
ListSigCont =
  (⊤ ⊎ ⊤) ◃ (λ x → ⊥) + (λ{ (inj₁ tt) → ⊥ ; (inj₂ tt) → ⊤ }) + λ{ (inj₂ tt) tt →
  ⊤ ◃ (λ x → ⊤) + (λ x → ⊥) + λ _ () }

Listᶜ : Cont
Listᶜ = 2W ListSigCont

List : Set → Set
List = ⟦ Listᶜ ⟧

------

app' : 2Cont → Cont → Cont
app' (S ◃ PX + PF + RF) TQ
  = Σᶜ[ s ∈ S ] ((⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ[ pf ∈ PF s ] (TQ ⊗ᶜ app' (RF s pf) TQ)))

{-
  IH : (s : S) (pf : PF s) → 2⟦ RF s pf ⟧ TQ X ≃ ⟦ app (RF s pf) TQ ⟧ X

  2⟦ S ◃ PX + PF + RF ⟧ TQ X
≃ Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⟧ (2⟦ RF s pf ⟧ TQ X))
≃ Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⟧ (⟦ app (RF s pf) TQ ⟧ X))
≃ Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⊗ᶜ app (RF s pf) TQ ⟧ X)
≃ Σ s : S, (PX s → X) × (⟦ Πᶜ pf : PF s, TQ ⊗ᶜ app (RF s pf) TQ ⟧ X)
≃ Σ s : S, (⟦ ⊤ ◃ λ _ → PX s ⟧ X) × (⟦ Πᶜ pf : PF s, TQ ⊗ᶜ app (RF s pf) TQ ⟧ X)
≃ Σ s : S, ⟦ (⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, TQ ⊗ᶜ app (RF s pf) TQ) ⟧ X
≃ ⟦ Σᶜ s : S, (⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, TQ ⊗ᶜ (app (RF s pf) TQ)) ⟧ X
≃ ⟦ app (S ◃ PX + PF + RF) TQ ⟧ X
-}

