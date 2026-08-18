{- Nat = mu (X. 1 + X), exercising mu/con/iter.

   Now that _[_]T is a real (computing) substitution and Ty-β/Σ-β are
   available, `subst` along Ty-β bridges the one remaining redex
   (app NatF (mu NatF) doesn't reduce definitionally, since app/lam are
   inert constructors) — everything on the other side of that bridge
   (substituting mu NatF into NatF's body) computes for free. -}

open import hcont-f-omega using (Kind; *; _⇒_; ConK; •; _▷_)
open import h-cont-f-omega-munu
open import Relation.Binary.PropositionalEquality

data Bool2 : Set where
  true false : Bool2

data Zero2 : Set where

NatBody : Ty (• ▷ *) *
NatBody = Σ Bool2 (λ{ true → Π Zero2 (λ ()) ; false → zero })

NatF : Ty • (* ⇒ *)
NatF = lam {κ = *} NatBody

NatTy : Ty • *
NatTy = mu NatF

-- bridges the one non-computing redex: app NatF (mu NatF) ≡ NatBody [ mu NatF ]T
unfold : app NatF (mu NatF) ≡ NatBody [ mu NatF ]T
unfold = Ty-β NatBody (mu NatF)

zeroTm : Tm • • NatTy
zeroTm = con NatF ε (subst (Tm • •) (sym unfold) (inj _ true (pair _ (λ ()))))

sucTm : Tm • • NatTy → Tm • • NatTy
sucTm n = con NatF ε (subst (Tm • •) (sym unfold) (inj _ false n))

-- iterator: fold to some target C, algebra as a term with a free var
foldNat : (C : Ty • *) → Tm • (• ▷ apSp (app NatF C) ε) C → Tm • • NatTy → Tm • • C
foldNat C alg n = iter NatF C (λ{ ε → alg }) ε n
