\begin{code}
{-# OPTIONS --cubical --guardedness #-}

open import Prelude hiding (case)
open import Agda.Primitive

variable
  ℓ ℓ' ℓ'' : Level

infix 0 _◃_
record Cont : Type₁ where
  constructor _◃_
  field
    S : Type
    P : S → Type

⟦_⟧ : Cont → Type → Type
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)
    
data W (SP : Cont) : Type where
  sup : ⟦ SP ⟧ (W SP) → W SP

infixr 0 _→ᶜ_
record _→ᶜ_ (SP TQ : Cont) : Type where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    fS : S → T
    fP : (s : S) → Q (fS s) → P s

variable
  SP TQ UV : Cont

idᶜ : SP →ᶜ SP
idᶜ = id ◃ λ s → id

infixr 9 _∘ᶜ_
_∘ᶜ_ : TQ →ᶜ UV → SP →ᶜ TQ → SP →ᶜ UV
(fT ◃  fQ) ∘ᶜ (fS ◃ fP) = fT ∘ fS ◃ λ s → fP s ∘ fQ (fS s)

variable X : Type

module head-example where

  head : List X → Maybe X
  head [] = nothing
  head (x ∷ xs) = just x

  Listᶜ : Cont
  Listᶜ = ℕ ◃ Fin

  isTrue : Bool → Type
  isTrue false = ⊥
  isTrue true = ⊤

  Maybeᶜ : Cont
  Maybeᶜ = Bool ◃ isTrue

  fS : ℕ → Bool
  fS zero = false
  fS (suc n) = true

  fP : (n : ℕ) → isTrue (fS n) → Fin n
  fP (suc n) tt = fzero

  headᶜ : Listᶜ →ᶜ Maybeᶜ
  headᶜ = fS ◃ fP

⊤ᶜ : Cont
⊤ᶜ = ⊤ ◃ λ{ tt → ⊥ }

⊥ᶜ : Cont
⊥ᶜ = ⊥ ◃ λ ()

_×ᶜ_ : Cont → Cont → Cont
(S ◃ P) ×ᶜ (T ◃ Q) = S × T ◃ λ{ (s , t) → P s ⊎ Q t }

_⊎ᶜ_ : Cont → Cont → Cont
(S ◃ P) ⊎ᶜ (T ◃ Q) = S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t }

1ᶜ : Cont
1ᶜ = ⊤ ◃ λ{ tt → ⊤ }

_⊗ᶜ_ : Cont → Cont → Cont
(S ◃ P) ⊗ᶜ (T ◃ Q) = Σ[ s ∈ S ] (P s → T) ◃ λ{ (s , f) → Σ[ p ∈ P s ] Q (f p) }

SigBush : (Type → Type) → Type → Type
SigBush F X = ⊤ ⊎ X × F (F X)

SigBushᶜ : Cont → Cont
SigBushᶜ SP = ⊤ᶜ ⊎ᶜ (1ᶜ ×ᶜ (SP ⊗ᶜ SP))

data BTree : Type where
  leaf : BTree
  node : BTree → BTree → BTree

record Bush∞ (X : Type) : Type where
  coinductive
  field
    head : X
    tail : Bush∞ (Bush∞ X)

data Bush (X : Type) : Type where
  []  : Bush X
  _∷_ : X → Bush (Bush X) → Bush X
\end{code}

\begin{code}[hide]
variable
  A B C : Type ℓ
\end{code}

\begin{code}
case : (A → C) → (B → C) → A ⊎ B → C
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b
\end{code}

\begin{code}[hide]

module Bush-example where
  mutual
\end{code}

\begin{code}
    record S : Type where
      inductive
      field
        desS : ⊤ ⊎ Σ[ s ∈ S ] (P s → S)

    record P (s : S) : Type where
      inductive
      field
        desP : case (λ{ tt → ⊥ }) (λ{ (s , f) → ⊤ ⊎ Σ[ p ∈ P s ] P (f p) }) (S.desS s)

  Bushᶜ : Cont
  Bushᶜ = S ◃ P

record 2Cont : Type₁ where
  inductive
  pattern  
  constructor _◃_+_+_
  field
    S : Type
    PX : S → Type
    PF : S → Type
    RF : (s : S) → PF s → 2Cont

2⟦_⟧ : 2Cont → (Type → Type) → Type → Type
2⟦ S ◃ PX + PF + RF ⟧ F X =
  Σ[ s ∈ S ] ((PX s → X) × ((pF : PF s) → F (2⟦ RF s pF ⟧ F X)))

-- Interpretation / Application

appS : 2Cont → Cont → Type
appS (S ◃ PX + PF + RF) (T ◃ Q) =
  Σ[ s ∈ S ] ((pF : PF s) → Σ[ t ∈ T ] (Q t → appS (RF s pF) (T ◃ Q)))

appP : (H : 2Cont) (F : Cont) → appS H F → Type
appP (S ◃ PX + PF + RF) (T ◃ Q) (s , f) =
  PX s ⊎ Σ[ pF ∈ PF s ] let (t , g) = f pF in
    Σ[ q ∈ Q t ] appP (RF s pF) (T ◃ Q) (g q)

app : 2Cont → Cont → Cont
app H F = appS H F ◃ appP H F
\end{code}

\begin{code}[hide]
module bad2W where

mutual
\end{code}

\begin{code}
  {-# NO_POSITIVITY_CHECK #-}
  data 2WS (H : 2Cont) : Type where
    2supS : appS H (2W H) → 2WS H

  data 2WP (H : 2Cont) (2ws : 2WS H) : Type where
    2supP⁻ : appP H (2W H) (2supS⁻ 2ws) → 2WP H 2ws

  2W : 2Cont → Cont
  2W H = 2WS H ◃ 2WP H

  2supS⁻ : {H : 2Cont} → 2WS H → appS H (2W H)
  2supS⁻ (2supS s) = s
\end{code}

\begin{code}[hide]
mutual
\end{code}

\begin{code}
  record 2WS-d (H' H : 2Cont) : Type where
    constructor mk
    inductive
    pattern
    open 2Cont H'
    field
      s : S
      f : (pF : PF s) → Σ[ t ∈ 2WS-d H H ] (2WP-d H H t → 2WS-d (RF s pF) H)

  data 2WP-d (H' H : 2Cont) (2ws : 2WS-d H' H) : Type where
    posX : (open 2Cont H') (open 2WS-d 2ws)
         → PX s
         → 2WP-d H' H 2ws
    posF : (open 2Cont H') (open 2WS-d 2ws)
         → (Σ[ pF ∈ PF s ] let (t , g) = f pF in
             Σ[ q ∈ 2WP-d H H t ] 2WP-d (RF s pF) H (g q))
         → 2WP-d H' H 2ws

{-
2WS : 2Cont → Type
2WS H = 2WS-d H H

2WP : (H : 2Cont) → 2WS H → Type
2WP H = 2WP-d H H

2W-d : 2Cont → 2Cont → Cont
2W-d H' H = 2WS-d H' H ◃ 2WP-d H' H

2W : 2Cont → Cont
2W H = 2W-d H H
-}
\end{code}

\begin{code}
record MaybeT (M : Type → Type) (X : Type) : Type where
  constructor mkMaybeT
  field
    runMaybeT : M (Maybe X)

data Free (SP : Cont) (X : Type) : Type where
  pure : X → Free SP X
  free : ⟦ SP ⟧ (Free SP X) → Free SP X
\end{code}
