\begin{code}
{-# OPTIONS --cubical #-}

module HContNaive where

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
    ne  : Ne Γ → Nf Γ *

  record Ne (Γ : ConK) : Type₁ where
    constructor _◃_◃_
    inductive
    field
      S : Type
      P : S → Var Γ A → Type
      R : (s : S) (x : Var Γ A) → P s x → Sp Γ A

  data Sp : ConK → Kind → Type₁ where
    ε   : Sp Γ A
    _,_ : Nf Γ A → Sp Γ B → Sp Γ (A ⇒ B)

HCont : Kind → Type₁
HCont = Nf •
\end{code}
