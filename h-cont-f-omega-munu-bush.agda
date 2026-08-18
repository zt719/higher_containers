{- Bush, the classic nested/non-regular datatype (Bird & Meertens),
   exercising mu/nu at a *higher* kind, (* ⇒ *) ⇒ (* ⇒ *), rather than
   just * ⇒ *: the functor abstracts over a type OPERATOR G, not a type,
   and the recursive occurrence G (G X) is nested rather than a plain
   X-shaped self-call — exactly why Bush needs genuine type-level
   recursion at all.

   Inductive Bush = mu BushF, BushF G X = 1 + X × G (G X): the "1 +" is
   what lets a bush be finite (the Nil option). Coinductive CoBush = nu
   CoBushF uses a *different* functor, CoBushF G X = X × G (G X) — no
   "1 +", hence no partiality: a CoBush is infinite by construction, an
   always-Cons stream of nested bushes, so there's nothing to case-split
   on and no Nil case to reject. Reusing BushF for nu would have given
   "possibly-finite bush" (a partiality monad on top of Bush), which is a
   different, coarser type than genuinely-infinite bushes. -}

open import hcont-f-omega using (Kind; *; _⇒_; ConK; •; _▷_)
open import h-cont-f-omega-munu
open import Relation.Binary.PropositionalEquality

data Bool2 : Set where
  true false : Bool2

data Zero2 : Set where

-- unfolds apSp (app (lam {* ⇒ *} (lam {*} Body)) G) (A , ε) down to Body
-- with G and X substituted, for any Body — shared by BushF and CoBushF,
-- since both are curried G-then-X the same way
unfoldFAt : (Body : Ty ((• ▷ (* ⇒ *)) ▷ *) *) (G : Ty • (* ⇒ *)) (A : Ty • *)
          → apSp (app (lam {κ = * ⇒ *} (lam {κ = *} Body)) G) (A , ε) ≡ _
unfoldFAt Body G A =
  trans (cong (λ t → app t A) (Ty-β (lam {κ = *} Body) G)) (Ty-β _ A)

-- the recursive slot G (G X), once G and X are substituted in, collapses
-- to a direct application app G (app G A) — shared by both functors too,
-- since it doesn't depend on Body at all
bushRecTy : (G : Ty • (* ⇒ *)) (A : Ty • *)
          → app (suc zero) (app (suc zero) zero) [ (idSub , G) ↑ ]Ty [ idSub , A ]Ty
          ≡ app G (app G A)
bushRecTy G A = cong₂ app (Ty-substId G) (cong (λ x → app x A) (Ty-substId G))

{- Inductive Bush: BushF G X = 1 + X × G (G X) -}

BushBody : Ty ((• ▷ (* ⇒ *)) ▷ *) *
BushBody = Σ Bool2 (λ{ true  → Π Zero2 (λ ())
                     ; false → Π Bool2 (λ{ true  → zero
                                          ; false → app (suc zero) (app (suc zero) zero) }) })

BushF : Ty • ((* ⇒ *) ⇒ (* ⇒ *))
BushF = lam {κ = * ⇒ *} (lam {κ = *} BushBody)

Bush : Ty • (* ⇒ *)
Bush = mu BushF

nilBush : (A : Ty • *) → Tm • • (apSp Bush (A , ε))
nilBush A = con BushF (A , ε)
  (subst (Tm • •) (sym (unfoldFAt BushBody (mu BushF) A)) (inj _ true (pair _ (λ ()))))

consBush : (A : Ty • *) → Tm • • A
         → Tm • • (apSp Bush (app Bush A , ε))  -- Bush (Bush A)
         → Tm • • (apSp Bush (A , ε))
consBush A a b = con BushF (A , ε)
  (subst (Tm • •) (sym (unfoldFAt BushBody (mu BushF) A))
    (inj _ false (pair _ (λ{ true → a
                            ; false → subst (Tm • •) (sym (bushRecTy (mu BushF) A)) b }))))

{- Coinductive CoBush: CoBushF G X = X × G (G X), no "1 +" -}

CoBushBody : Ty ((• ▷ (* ⇒ *)) ▷ *) *
CoBushBody = Π Bool2 (λ{ true → zero ; false → app (suc zero) (app (suc zero) zero) })

CoBushF : Ty • ((* ⇒ *) ⇒ (* ⇒ *))
CoBushF = lam {κ = * ⇒ *} (lam {κ = *} CoBushBody)

CoBush : Ty • (* ⇒ *)
CoBush = nu CoBushF

headBush : (A : Ty • *) → Tm • • (apSp CoBush (A , ε)) → Tm • • A
headBush A b = prj _ (subst (Tm • •) (unfoldFAt CoBushBody (nu CoBushF) A) (out CoBushF (A , ε) b)) true

tailBush : (A : Ty • *) → Tm • • (apSp CoBush (A , ε)) → Tm • • (apSp CoBush (app CoBush A , ε))
tailBush A b = subst (Tm • •) (bushRecTy (nu CoBushF) A)
  (prj _ (subst (Tm • •) (unfoldFAt CoBushBody (nu CoBushF) A) (out CoBushF (A , ε) b)) false)
