\begin{code}
{-# OPTIONS --cubical #-}

module HCont where

open import Agda.Primitive using (lzero; lsuc)
open import Prelude

{- Kinds & Contexts & Variables -}

infixr 20 _⇒_
data Kind : Type where
  * : Kind
  _⇒_ : Kind → Kind → Kind

variable A B C : Kind

infixl 5 _▹_
data ConK : Type where
  •   : ConK
  _▹_ : ConK → Kind → ConK

variable Γ Δ Θ : ConK

data Var : ConK → Kind → Type where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y : Var Γ A

{- Normal Forms -}

infixr 4 _,_

mutual

  data Nf : ConK → Kind → Type₁ where
    lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
    ne  : Ne Γ * → Nf Γ *

  record Ne (Γ : ConK) (B : Kind) : Type₁ where
    constructor _◃_◃_
    inductive
    field
      S : Type
      P : S → Var Γ A → Type
      R : (s : S) (x : Var Γ A) → P s x → Sp Γ A B

  data Sp : ConK → Kind → Kind → Type₁ where  
    ε   : Sp Γ A A
    _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

HCont : Kind → Type₁
HCont = Nf •

variable t u w : Nf Γ A
variable m n : Ne Γ A
variable ts us ws : Sp Γ A B

ap : Nf Γ (A ⇒ B) → Nf (Γ ▹ A) B
ap (lam t) = t

en : Nf Γ * → Ne Γ *
en (ne spr) = spr

{- Variable Weakening & (Heterogeneous) Equality -}

_-_ : (Γ : ConK) → Var Γ A → ConK
• - ()
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - (vs x) = (Γ - x) ▹ A

wkv : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

data EqVar : Var Γ A → Var Γ B → Type where
  same : EqVar x x
  diff : (x : Var Γ A) (y : Var (Γ - x) B) → EqVar x (wkv x y)

eq : (x : Var Γ A) (y : Var Γ B) → EqVar x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
eq (vs x) (vs .x)          | same = same
eq (vs x) (vs .(wkv x y′)) | diff .x y′ = diff (vs x) (vs y′)

{- Normal Forms Weakening -}

wkNf : (x : Var Γ A) → Nf (Γ - x) B → Nf Γ B

wkNe : (x : Var Γ A) → Ne (Γ - x) B → Ne Γ B

wkSp : (x : Var Γ A) → Sp (Γ - x) B C → Sp Γ B C

wkNf x (lam t) = lam (wkNf (vs x) t)
wkNf x (ne spr) = ne (wkNe x spr)

wkNe {Γ} {A} {C} x (S ◃ P ◃ R) = S′ ◃ P′ ◃ R′
  where
  S′ : Type
  S′ = S
  
  P′ : S → Var Γ B → Type
  P′ s y with eq x y
  P′ s .x | same = ⊥
  P′ s y  | diff .x y′ = P s y′

  R′ : (s : S) (y : Var Γ B) → P′ s y → Sp Γ B C
  R′ s y p with eq x y
  R′ s y p | diff .x y′ = wkSp x (R s y′ p)

wkSp x ε = ε
wkSp x (t , ts) = wkNf x t , wkSp x ts

{- η-expansion -}

appSp : Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
appSp ε u = u , ε
appSp (t , ts) u = t , appSp ts u

nvar : Var Γ A → Nf Γ A

ne2nf : Ne Γ A → Nf Γ A

nvar {Γ} {B} x = ne2nf (S ◃ P ◃ R)
  where
  S : Type
  S = ⊤

  P : S → Var Γ A → Type
  P tt y with eq x y
  P tt .x | same = ⊤
  P tt y  | diff .x y′ = ⊥

  R : (s : S) (y : Var Γ A) → P s y → Sp Γ A B
  R tt y p with eq x y
  R tt .x p | same = ε
  R tt y () | diff .x y′

ne2nf {Γ} {*} spr = ne spr
ne2nf {Γ} {A ⇒ C} (S ◃ P ◃ R) = lam (ne2nf (S ◃ P′ ◃ R′))
  where
  P′ : S → Var (Γ ▹ A) B → Type
  P′ s vz = ⊥
  P′ s (vs x) = P s x

  R′ : (s : S) (x : Var (Γ ▹ A) B) → P′ s x → Sp (Γ ▹ A) B C
  R′ s vz ()
  R′ s (vs x) p = appSp (wkSp vz (R s x p)) (nvar vz)

{- Normalization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

_◇_ : Nf Γ A → Sp Γ A B → Nf Γ B

lam t [ x := u ] = lam (t [ vs x := wkNf vz u ])
_[_:=_] {Γ} (ne (S ◃ P ◃ R)) x u = ne (S′ ◃ P′ ◃ R′)
  where
  -- each occurrence of x is replaced by u applied to its spine
  arg : (s : S) → P s x → Ne (Γ - x) *
  arg s p = en (u ◇ (R s x p < x := u >))

  S′ : Type
  S′ = Σ[ s ∈ S ] ((p : P s x) → Ne.S (arg s p))

  P′ : S′ → Var (Γ - x) C → Type
  P′ (s , f) y = P s (wkv x y) ⊎ (Σ[ p ∈ P s x ] Ne.P (arg s p) (f p) y)

  R′ : (s : S′) (y : Var (Γ - x) C) → P′ s y → Sp (Γ - x) C *
  R′ (s , f) y (inj₁ p) = R s (wkv x y) p < x := u >
  R′ (s , f) y (inj₂ (p , q)) = Ne.R (arg s p) (f p) y q

ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

napp (lam t) u = t [ vz := u ]

t ◇ ε = t
t ◇ (u , us) = napp t u ◇ us

{- Morphisms -}

mutual

  data NfHom : (Γ : ConK) → Nf Γ A → Nf Γ A → Type₁ where
    lam : NfHom (Γ ▹ A) t u → NfHom Γ (lam t) (lam u)
    ne  : NeHom Γ m n → NfHom Γ (ne m) (ne n)

  record NeHom Γ {B} (m n : Ne Γ B) : Type₁ where 
    constructor _◃_◃_
    inductive
    open Ne m
    open Ne n renaming (S to T; P to Q; R to L)
    field
      f : S → T
      g : (s : S) (x : Var Γ A) → Q (f s) x → P s x
      h : (s : S) (x : Var Γ A) (q : Q (f s) x)
        → SpHom Γ (R s x (g s x q)) (L (f s) x q)

  data SpHom : (Γ : ConK) → Sp Γ A B → Sp Γ A B → Type₁ where  
    ε   : SpHom Γ ts ts
    _,_ : NfHom Γ t u → SpHom Γ ts us → SpHom Γ (t , ts) (u , us)

HContHom : HCont A → HCont A → Type₁
HContHom = NfHom •

{- Semantics -}

{- One Interpreation -}

⟦_⟧k : Kind → Type₁
⟦ * ⟧k = Type
⟦ A ⇒ B ⟧k = ⟦ A ⟧k → ⟦ B ⟧k

⟦_⟧c : ConK → Type₁
⟦ • ⟧c = Lift (lsuc lzero) ⊤
⟦ Γ ▹ A ⟧c = ⟦ Γ ⟧c × ⟦ A ⟧k

⟦_⟧v : Var Γ A → ⟦ Γ ⟧c → ⟦ A ⟧k
⟦ vz ⟧v (as , a) = a
⟦ vs x ⟧v (as , a) = ⟦ x ⟧v as

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧c → ⟦ A ⟧k

⟦_⟧ne : Ne Γ * → ⟦ Γ ⟧c → Type

⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧c → ⟦ A ⟧k → ⟦ B ⟧k

⟦ lam t ⟧nf as a = ⟦ t ⟧nf (as , a)
⟦ ne spr ⟧nf as = ⟦ spr ⟧ne as

⟦_⟧ne {Γ} (S ◃ P ◃ R) as =
  Σ[ s ∈ S ] ({A : Kind} (x : Var Γ A) (p : P s x)
  → ⟦ R s x p ⟧sp as (⟦ x ⟧v as))

⟦ ε ⟧sp as a = a
⟦ t , ts ⟧sp as f = ⟦ ts ⟧sp as (f (⟦ t ⟧nf as))

H⟦_⟧ : HCont A → ⟦ A ⟧k
H⟦ x ⟧ = ⟦ x ⟧nf (lift tt)

{- Λ Terms -}

postulate
  HW : HCont (A ⇒ A) → HCont A

SigWᶜ : HCont (((* ⇒ *) ⇒ *) ⇒ (* ⇒ *) ⇒ *)
SigWᶜ = lam (lam (napp (nvar vz) (napp (nvar (vs vz)) (nvar vz))))

Wᶜ : HCont ((* ⇒ *) ⇒ *)
Wᶜ = HW SigWᶜ

W : HCont (* ⇒ *) → HCont *
W = napp Wᶜ

W-bad : (Type → Type) → Type
W-bad = H⟦ Wᶜ ⟧
\end{code}
