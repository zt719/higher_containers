{- hcont-f-omega, extended with mu and nu, together with its equational
   theory.

   Ty/ConT/Tm are redeclared rather than imported, since Agda datatypes
   are closed and mu/nu add genuinely new Ty constructors (and
   con/iter/out/coiter genuinely new Tm constructors) that couldn't
   otherwise be spliced in. Kind and ConK are unaffected by mu/nu, so
   those are reused as-is.

   As in h-cont-f-omega-eq.agda, substitution and the β/η laws are
   postulated rather than derived, to keep this step light. -}

open import hcont-f-omega using (Kind; *; _⇒_; ConK; •; _▷_)
open import Relation.Binary.PropositionalEquality

variable κ κ' : Kind
variable Θ Θ' : ConK

data Ty : ConK → Kind → Set₁ where
  zero : Ty (Θ ▷ κ) κ
  suc  : Ty Θ κ → Ty (Θ ▷ κ') κ
  lam  : Ty (Θ ▷ κ) κ' → Ty Θ (κ ⇒ κ')
  app  : Ty Θ (κ ⇒ κ') → Ty Θ κ → Ty Θ κ'
  Π    : (I : Set) → (I → Ty Θ *) → Ty Θ *
  Σ    : (I : Set) → (I → Ty Θ *) → Ty Θ *
  mu   : Ty Θ (κ ⇒ κ) → Ty Θ κ
  nu   : Ty Θ (κ ⇒ κ) → Ty Θ κ

{- Substitution for Ty, by simultaneous substitutions rather than a single
   hereditary one: suc already gives O(1) weakening at the top of the
   context for free, which is exactly what wkSub1/_↑ need under lam. -}

data Sub (Θ' : ConK) : ConK → Set₁ where
  ε   : Sub Θ' •
  _,_ : Sub Θ' Θ → Ty Θ' κ → Sub Θ' (Θ ▷ κ)

wkSub1 : Sub Θ' Θ → Sub (Θ' ▷ κ) Θ
wkSub1 ε = ε
wkSub1 (ρ , t) = wkSub1 ρ , suc t

_↑ : Sub Θ' Θ → Sub (Θ' ▷ κ) (Θ ▷ κ)
ρ ↑ = wkSub1 ρ , zero

idSub : Sub Θ Θ
idSub {Θ = •} = ε
idSub {Θ = Θ ▷ κ} = idSub ↑

_[_]Ty : Ty Θ κ → Sub Θ' Θ → Ty Θ' κ
zero    [ ρ , t ]Ty = t
suc s   [ ρ , t ]Ty = s [ ρ ]Ty
lam s   [ ρ ]Ty = lam (s [ ρ ↑ ]Ty)
app s u [ ρ ]Ty = app (s [ ρ ]Ty) (u [ ρ ]Ty)
Π I f   [ ρ ]Ty = Π I (λ i → f i [ ρ ]Ty)
Σ I f   [ ρ ]Ty = Σ I (λ i → f i [ ρ ]Ty)
mu F    [ ρ ]Ty = mu (F [ ρ ]Ty)
nu F    [ ρ ]Ty = nu (F [ ρ ]Ty)

_[_]T : Ty (Θ ▷ κ) κ' → Ty Θ κ → Ty Θ κ'
t [ u ]T = t [ idSub , u ]Ty

-- t [ idSub ]Ty ≡ t doesn't hold by refl: _[_]Ty rebuilds the whole spine
-- rather than short-circuiting on the identity, so this needs an actual
-- induction over Ty that we haven't done. Postulated for now, same as
-- everything else — needed to relate a substituted-through-many-layers
-- occurrence of a closed type back to that type directly (e.g. in
-- h-cont-f-omega-munu-bush.agda, relating a nested self-application inside
-- BushF's body back to a direct application of mu BushF).
postulate
  Ty-substId : (t : Ty Θ κ) → t [ idSub ]Ty ≡ t

data ConT (Θ : ConK) : Set₁ where
  •   : ConT Θ
  _▷_ : ConT Θ → Ty Θ * → ConT Θ

variable Γ Δ : ConT Θ
variable σ τ : Ty Θ *
variable I : Set

{- Every kind κ is, by construction, a spine κ₁ ⇒ κ₂ ⇒ ... ⇒ κₙ ⇒ * ending
   in *. Sp Θ κ is the type of argument lists that fully apply a Θ-type of
   kind κ down to kind *; this is what lets con/iter be stated purely at
   kind *, uniformly for any κ (including higher/indexed kinds). -}
data Sp (Θ : ConK) : Kind → Set₁ where
  ε   : Sp Θ *
  _,_ : Ty Θ κ → Sp Θ κ' → Sp Θ (κ ⇒ κ')

apSp : Ty Θ κ → Sp Θ κ → Ty Θ *
apSp t ε = t
apSp t (u , sp) = apSp (app t u) sp

data Tm : (Θ : ConK) → ConT Θ → Ty Θ * → Set₁ where
  zero : Tm Θ (Δ ▷ σ) σ
  suc  : Tm Θ Δ σ → Tm Θ (Δ ▷ τ) σ
  inj  : (F : I → Ty Θ *) (i : I) → Tm Θ Δ (F i) → Tm Θ Δ (Σ I F)
  case : (F : I → Ty Θ *) (s : Tm Θ Δ (Σ I F)) → ((i : I) → Tm Θ (Δ ▷ F i) τ) → Tm Θ Δ τ
  prj  : (F : I → Ty Θ *) → Tm Θ Δ (Π I F) → (i : I) → Tm Θ Δ (F i)
  pair : (F : I → Ty Θ *) → ((i : I) → Tm Θ Δ (F i)) → Tm Θ Δ (Π I F)

  -- constructor: one layer of F unfolded at every spine instantiation
  con  : (F : Ty Θ (κ ⇒ κ)) (sp : Sp Θ κ)
       → Tm Θ Δ (apSp (app F (mu F)) sp) → Tm Θ Δ (apSp (mu F) sp)

  -- iterator: an F-algebra into C, uniform in the spine, folded over mu F.
  -- The algebra step is a term with a free variable of type (F C) at that
  -- spine instantiation, not an Agda function Tm → Tm — the latter would
  -- put Tm to the left of an arrow inside its own constructor and fail the
  -- strict positivity check (same reason case/pair extend Δ instead of
  -- taking a Tm argument).
  iter : (F : Ty Θ (κ ⇒ κ)) (C : Ty Θ κ)
       → ((sp : Sp Θ κ) → Tm Θ (Δ ▷ apSp (app F C) sp) (apSp C sp))
       → (sp : Sp Θ κ) → Tm Θ Δ (apSp (mu F) sp) → Tm Θ Δ (apSp C sp)

  -- destructor: dual of con, one layer of F revealed at every spine
  -- instantiation. A plain, direct Tm argument, exactly like prj/con —
  -- no positivity issue here at all.
  out  : (F : Ty Θ (κ ⇒ κ)) (sp : Sp Θ κ)
       → Tm Θ Δ (apSp (nu F) sp) → Tm Θ Δ (apSp (app F (nu F)) sp)

  -- co-iterator: dual of iter. A C-coalgebra, uniform in the spine,
  -- unfolded into nu F from a seed c : C. The coalgebra step is a term
  -- with a free variable of type C (not an Agda function Tm → Tm), for
  -- the same strict-positivity reason as iter's algebra.
  coiter : (F : Ty Θ (κ ⇒ κ)) (C : Ty Θ κ)
       → ((sp : Sp Θ κ) → Tm Θ (Δ ▷ apSp C sp) (apSp (app F C) sp))
       → (sp : Sp Θ κ) → Tm Θ Δ (apSp C sp) → Tm Θ Δ (apSp (nu F) sp)

{- Substitution for Tm, same shape as Sub/Ty above but over a fixed Θ -}

data SubTm (Θ : ConK) (Γ : ConT Θ) : ConT Θ → Set₁ where
  ε   : SubTm Θ Γ •
  _,_ : SubTm Θ Γ Δ → Tm Θ Γ σ → SubTm Θ Γ (Δ ▷ σ)

wkSubTm1 : SubTm Θ Γ Δ → SubTm Θ (Γ ▷ τ) Δ
wkSubTm1 ε = ε
wkSubTm1 (ρ , t) = wkSubTm1 ρ , suc t

_↑tm : SubTm Θ Γ Δ → SubTm Θ (Γ ▷ σ) (Δ ▷ σ)
ρ ↑tm = wkSubTm1 ρ , zero

idSubTm : SubTm Θ Δ Δ
idSubTm {Δ = •} = ε
idSubTm {Δ = Δ ▷ σ} = idSubTm ↑tm

_[_]Tm : Tm Θ Δ τ → SubTm Θ Γ Δ → Tm Θ Γ τ
zero              [ ρ , t ]Tm = t
suc s             [ ρ , t ]Tm = s [ ρ ]Tm
inj F i s         [ ρ ]Tm = inj F i (s [ ρ ]Tm)
case F s k        [ ρ ]Tm = case F (s [ ρ ]Tm) (λ i → k i [ ρ ↑tm ]Tm)
prj F s i         [ ρ ]Tm = prj F (s [ ρ ]Tm) i
pair F f          [ ρ ]Tm = pair F (λ i → f i [ ρ ]Tm)
con F sp s        [ ρ ]Tm = con F sp (s [ ρ ]Tm)
iter F C alg sp s [ ρ ]Tm = iter F C (λ sp' → alg sp' [ ρ ↑tm ]Tm) sp (s [ ρ ]Tm)
out F sp s        [ ρ ]Tm = out F sp (s [ ρ ]Tm)
coiter F C coalg sp c [ ρ ]Tm = coiter F C (λ sp' → coalg sp' [ ρ ↑tm ]Tm) sp (c [ ρ ]Tm)

_[_]₀ : Tm Θ (Δ ▷ σ) τ → Tm Θ Δ σ → Tm Θ Δ τ
t [ u ]₀ = t [ idSubTm , u ]Tm

{- Equational theory: the remaining β/η/mu laws are genuine axioms about
   inert constructors (app/lam, con/iter never reduce on their own), so
   they stay postulated even though substitution is now real. -}

postulate
  Ty-β : (t : Ty (Θ ▷ κ) κ') (u : Ty Θ κ) → app (lam t) u ≡ t [ u ]T
  Ty-η : (t : Ty Θ (κ ⇒ κ')) → lam (app (suc t) zero) ≡ t

postulate
  Σ-β : (F : I → Ty Θ *) (k : (i : I) → Tm Θ (Δ ▷ F i) τ) (i : I) (t : Tm Θ Δ (F i))
      → case F (inj F i t) k ≡ (k i) [ t ]₀

  Π-β : (F : I → Ty Θ *) (f : (i : I) → Tm Θ Δ (F i)) (i : I)
      → prj F (pair F f) i ≡ f i

  Π-η : (F : I → Ty Θ *) (t : Tm Θ Δ (Π I F))
      → pair F (λ i → prj F t i) ≡ t

  Σ-η : (F : I → Ty Θ *) (s : Tm Θ Δ (Σ I F))
      → case F s (λ i → inj F i zero) ≡ s

postulate
  -- the functorial action of F on spine-uniform term maps. F is built only
  -- from lam/app/zero/suc/Π/Σ, so it is automatically covariant (there is
  -- no negative type-former at kind * to build a contravariant F with) —
  -- this should be derivable by induction on F, but is postulated here
  -- along with everything else.
  Fmap : (F : Ty Θ (κ ⇒ κ)) {A B : Ty Θ κ}
       → ((sp : Sp Θ κ) → Tm Θ Δ (apSp A sp) → Tm Θ Δ (apSp B sp))
       → (sp : Sp Θ κ) → Tm Θ Δ (apSp (app F A) sp) → Tm Θ Δ (apSp (app F B) sp)

postulate
  -- mu-β (cata of con): unfold one layer of con, mapping the recursive
  -- calls (via iter itself) through F before splicing into the algebra step
  mu-β : (F : Ty Θ (κ ⇒ κ)) (C : Ty Θ κ)
       → (alg : (sp : Sp Θ κ) → Tm Θ (Δ ▷ apSp (app F C) sp) (apSp C sp))
       → (sp : Sp Θ κ) (t : Tm Θ Δ (apSp (app F (mu F)) sp))
       → iter F C alg sp (con F sp t) ≡ (alg sp) [ Fmap F (iter F C alg) sp t ]₀

postulate
  -- mu-η: initiality. Any h satisfying the same recursive equation as
  -- iter must equal iter — this is just "mu F is the initial F-algebra",
  -- no different in kind from what Agda's own inductive types already
  -- satisfy. It's safe as a postulate here: as far as we can add up, no
  -- inconsistency is derivable (F can never put mu F left of an arrow,
  -- since Tm has no value-level ⇒ — that closes off the classical
  -- Lawvere-style reflexive-domain route; and Π/Σ's index (I : Set) sits
  -- one universe below Ty Θ * : Set₁, so they can never quantify over
  -- Ty Θ * itself — that closes off the classical Girard/Hurkens
  -- impredicativity route). And postulates are computationally inert —
  -- Agda never auto-unfolds them — so adding this one can't make Agda's
  -- own type-checking loop either.
  --
  -- The real caveat is narrower and lands later: if this equational
  -- theory is ever turned into an actual computation rule (e.g. eta-
  -- expanding neutrals for an NbE-style normalizer, the way HCont.agda's
  -- ne2nf already does for Σ/Π), that specific construction would not
  -- terminate for mu. Σ/Π-eta-expansion recurses on the *kind* (finite,
  -- structural). Eta-expanding a neutral n : mu F would recurse on the
  -- *value* revealed by unfolding n — but for a genuinely neutral n that
  -- revealed structure is itself just as neutral, so the recursion never
  -- bottoms out. This is exactly why unrestricted eta for general
  -- (non-record) inductive types is avoided in practice (Coq and Agda
  -- don't give it either) — a real problem, but one for the eventual
  -- normalizer to solve (e.g. by restricting expansion, or not eta-
  -- expanding mu at all), not a reason to withhold the axiom itself.
  mu-η : (F : Ty Θ (κ ⇒ κ)) (C : Ty Θ κ)
       → (alg : (sp : Sp Θ κ) → Tm Θ (Δ ▷ apSp (app F C) sp) (apSp C sp))
       → (h : (sp : Sp Θ κ) → Tm Θ Δ (apSp (mu F) sp) → Tm Θ Δ (apSp C sp))
       → ((sp : Sp Θ κ) (t : Tm Θ Δ (apSp (app F (mu F)) sp))
          → h sp (con F sp t) ≡ (alg sp) [ Fmap F h sp t ]₀)
       → (sp : Sp Θ κ) (n : Tm Θ Δ (apSp (mu F) sp)) → h sp n ≡ iter F C alg sp n

postulate
  -- nu-β (out of coiter): dual of mu-β. Unfold one coiter step: reveal
  -- one F-layer of the seed via coalg, then map the *rest* of the
  -- coiteration through F. Unlike mu-β this is exactly a "guarded"
  -- one-step unfolding — out (coiter ...) always reduces in one step to
  -- something F-shaped that may contain further, still-unevaluated
  -- coiter applications nested inside via Fmap, never needing to unfold
  -- arbitrarily deep. This is the standard, terminating shape of
  -- corecursion (matches Cont.agda/HCont-coind.agda's own use of
  -- --guardedness elsewhere in this project).
  nu-β : (F : Ty Θ (κ ⇒ κ)) (C : Ty Θ κ)
       → (coalg : (sp : Sp Θ κ) → Tm Θ (Δ ▷ apSp C sp) (apSp (app F C) sp))
       → (sp : Sp Θ κ) (c : Tm Θ Δ (apSp C sp))
       → out F sp (coiter F C coalg sp c) ≡ Fmap F (coiter F C coalg) sp ((coalg sp) [ c ]₀)

postulate
  -- nu-η: finality, dual of mu-η. Any h satisfying the same corecursive
  -- equation as coiter must equal coiter — "nu F is the terminal
  -- F-coalgebra". As a postulate (requiring an explicit proof of the
  -- fourth argument to invoke) this is exactly as inert/safe as mu-η —
  -- nothing here is decided automatically.
  --
  -- Careful what "safe to compute" would mean later, though: only the
  -- *shallow* instance — h = id, coalg = out, giving n ≡ coiter F (nu F)
  -- out sp n for a neutral n — is the terminating, single-step wrap that
  -- matches Agda's own definitional eta for coinductive records
  -- (p ≡ record{head = head p; tail = tail p}). The *full* statement
  -- above, quantified over arbitrary h, is not something a normalizer
  -- could decide: using it to compare two independently-built
  -- corecursive terms is exactly deciding bisimilarity, which is
  -- undecidable in general. So nu-η isn't "the safe one" versus mu-η's
  -- problem — it has its own, different obstruction to ever being fully
  -- automatic; it just isn't the nontermination mu-η has.
  nu-η : (F : Ty Θ (κ ⇒ κ)) (C : Ty Θ κ)
       → (coalg : (sp : Sp Θ κ) → Tm Θ (Δ ▷ apSp C sp) (apSp (app F C) sp))
       → (h : (sp : Sp Θ κ) → Tm Θ Δ (apSp C sp) → Tm Θ Δ (apSp (nu F) sp))
       → ((sp : Sp Θ κ) (c : Tm Θ Δ (apSp C sp))
          → out F sp (h sp c) ≡ Fmap F h sp ((coalg sp) [ c ]₀))
       → (sp : Sp Θ κ) (c : Tm Θ Δ (apSp C sp)) → h sp c ≡ coiter F C coalg sp c
