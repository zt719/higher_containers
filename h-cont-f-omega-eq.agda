{- Equational theory for hcont-f-omega's Ty and Tm layers.

   The substitution operations and the β/η laws below are postulated
   rather than derived: defining substitution properly (with the
   accompanying weakening lemmas) is real mechanical work, deferred
   until the shape of the equations themselves has been settled. -}

open import hcont-f-omega
open import Relation.Binary.PropositionalEquality

postulate
  -- plain substitution: replace the head variable by a term over the same tail context
  _[_]₀ : Tm Θ (Δ ▷ σ) τ → Tm Θ Δ σ → Tm Θ Δ τ

  -- substitution under a fresh head variable: replace the head variable by a term
  -- built from a *new* head variable of type σ', landing in the σ'-extended context
  _[_]₁ : {σ' : Ty Θ *} → Tm Θ (Δ ▷ σ) τ → Tm Θ (Δ ▷ σ') σ → Tm Θ (Δ ▷ σ') τ

  -- plain substitution at the type level, same shape as _[_]₀ but for Ty
  _[_]T : Ty (Θ ▷ κ) κ' → Ty Θ κ → Ty Θ κ'

postulate
  Ty-β : (t : Ty (Θ ▷ κ) κ') (u : Ty Θ κ) → app (lam t) u ≡ t [ u ]T
  Ty-η : (t : Ty Θ (κ ⇒ κ')) → lam (app (suc t) zero) ≡ t

postulate
  Σ-β : (F : I → Ty Θ *) (k : (i : I) → Tm Θ (Δ ▷ F i) τ) (i : I) (t : Tm Θ Δ (F i))
      → case F k [ inj F i t ]₀ ≡ (k i) [ t ]₀

  Π-β : (F : I → Ty Θ *) (f : (i : I) → Tm Θ Δ (F i)) (i : I)
      → prj F (pair F f) i ≡ f i

  Π-η : (F : I → Ty Θ *) (t : Tm Θ Δ (Π I F))
      → pair F (λ i → prj F t i) ≡ t

  Σ-η : (F : I → Ty Θ *) (t : Tm Θ (Δ ▷ Σ I F) τ)
      → case F (λ i → t [ inj F i zero ]₁) ≡ t
