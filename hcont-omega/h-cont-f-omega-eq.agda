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

{-
define the calculus w.o. mu-nu incuding substitutions 
(ok we can reduce substutions)
show that HCont are basically the normal forms. 
HCont -> HCont omega 
Ty -> KI
Tm -> TY
[[_]] -> TM

F : * -> *
F X = 1 + X 

FF : Set -> Set
FF = [[ F ]]

TM F is a representation of FF
eg there is 
X : * ; empty |- in1 () : F @ X
X : * ; x : X |- in2 x : F @  X        

add mu , [[-]] doesn't work 
f-omega works , compute a head normal form 

Nat = mu F : * 

Semantics : basic calculus , Cont are the free coproducts 
1st order containers : Given a category C, 
what happens if you freely add coproducts : Cont C

S : Set, P : S -> C  
S <| P : C => Set
S <| P c = Sigma s : S . C(P x , c)

eg S = 2 , P 0, P 1
(P0 + P1) c = C(P0 , c) x C(P 1, c) 

products come for free 

what happens for higher order, can we use this to find semantics of HCont?

how can we understand mu , nu (maybe via colimits , limits) 
free colimits = PSh (accessible)


-}