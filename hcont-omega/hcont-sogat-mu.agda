open import hcont-sogat
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
    μ : Ty ((K ⇒ K) ⇒ K)

μ* : Ty ((* ⇒ *) ⇒ *)
μ* = μ {K = *}

-- Spines: a Kind is built up by iterating _⇒_ over a (possibly empty)
-- sequence of argument Kinds, ending in *. A Spine records exactly that
-- sequence of assumptions; ⇒* folds a Spine back down into the Kind it
-- stands for. The claim that every Kind arises this way, uniquely, is
-- the postulated iso Spine ≅ Kind.

Spine : Set
Spine = List Kind

⇒* : Spine → Kind
⇒* []       = *
⇒* (K ∷ Ks) = K ⇒ ⇒* Ks

postulate
    Dom    : Kind → Spine
    ⇒*∘Dom : (κ : Kind) → ⇒* (Dom κ) ≡ κ
    Dom∘⇒* : (S : Spine) → Dom (⇒* S) ≡ S
    funExt : {A : Set} {B : A → Set} {f g : (a : A) → B a}
             → ((a : A) → f a ≡ g a) → f ≡ g

Spine-iso : Spine ≅ Kind
Spine-iso = record
    { to      = ⇒*
    ; from    = Dom
    ; to∘from = funExt ⇒*∘Dom
    ; from∘to = funExt Dom∘⇒*
    }

-- Fix F is μ applied (via APP) to an endofunctor F : Ty (K ⇒ K).
Fix : Ty (K ⇒ K) → Ty K
Fix F = APP μ F

-- Args S is the tuple of actual Ty arguments needed to saturate a Ty
-- of kind ⇒* S down to kind *, one per entry of the spine; apArgs feeds
-- them in via APP, mirroring Sp/apSp in h-cont-f-omega-munu.agda but
-- driven by our List-Kind Spine instead of pattern-matching on Kind
-- itself (Kind has no eliminator here, only the postulated constructors).

Args : Spine → Set
Args []       = ⊤
Args (K ∷ Ks) = Ty K × Args Ks

apArgs : (S : Spine) → Ty (⇒* S) → Args S → Ty *
apArgs []       t tt       = t
apArgs (K ∷ Ks) t (A , as) = apArgs Ks (APP t A) as

-- con/fold, uniform in the spine, matching con/iter in
-- h-cont-f-omega-munu.agda: con unfolds/reveals one layer of F at every
-- saturating instantiation of Fix F, and fold is the F-algebra-into-C
-- iterator over Fix F. Unlike that file's Tm, ours has no context Δ to
-- extend, so the algebra step in fold is just a plain Agda function
-- (no strict-positivity concern — these are postulates, not con/iter
-- constructors of an inductive Tm).

postulate
    con : (S : Spine) (F : Ty (⇒* S ⇒ ⇒* S)) (args : Args S)
        → Tm (apArgs S (APP F (Fix F)) args)
        → Tm (apArgs S (Fix F) args)

    fold : (S : Spine) (F : Ty (⇒* S ⇒ ⇒* S)) (C : Ty (⇒* S))
        → ((args : Args S) → Tm (apArgs S (APP F C) args) → Tm (apArgs S C args))
        → (args : Args S) → Tm (apArgs S (Fix F) args) → Tm (apArgs S C args)

-- Sanity check: at the empty spine (kind *), con/fold specialise down
-- to the ordinary first-order in/cata this was meant to generalise —
-- con [] F tt : Tm (APP F (Fix F)) → Tm (Fix F), matching the earlier
-- "in* : Tm (F @ (μ* F)) → Tm (μ* F)" sketch, with args erased to tt.
