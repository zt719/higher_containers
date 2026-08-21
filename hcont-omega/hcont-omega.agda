{- Algebraic (initial-algebra) semantics for the hcontmunu calculus
   (h-cont-f-omega-munu.agda), in the style of initial-algebra semantics
   for QIITs: instead of `data Ty`/`data Tm` plus separately postulated
   β/η laws, define what it means to be a *model* (Algebra) of the
   theory — carriers with all the same operations, satisfying all the
   same equations, as one record — then postulate that an initial one
   exists. The constructors and equations both fall out as projections
   from the initial algebra; evaluation into any other model falls out
   as the (postulated) unique algebra homomorphism out of the initial one.

   Substitution (_[_]TyA, _[_]TmA) is simultaneous (Sub/SubTm-indexed,
   mirroring h-cont-f-omega-munu.agda's own Sub/SubTm) and primitive, but
   — unlike an earlier draft of this file — comes with the same eight/ten
   "commutes with each constructor" laws that were free (definitional
   pattern-matching clauses) in h-cont-f-omega-munu.agda's recursively
   defined _[_]Ty/_[_]Tm: since here substitution is just another
   primitive operation rather than a recursive definition, those clauses
   have to be given explicitly as algebra laws instead. Full CwF-style
   identity/composition/associativity laws for Sub itself (as attempted,
   incompletely, in SCWF.agda/TmSCWF.agda for a simpler calculus) remain
   out of scope. -}

open import hcont-f-omega using (Kind; *; _⇒_; ConK; •; _▷_)
open import Relation.Binary.PropositionalEquality

variable κ κ' : Kind
variable Θ Θ' : ConK
variable I : Set

{- Generic helpers, parametrized over an arbitrary Ty-carrier -}

data ConTOf (TyA : ConK → Kind → Set₁) (Θ : ConK) : Set₁ where
  •   : ConTOf TyA Θ
  _▷_ : ConTOf TyA Θ → TyA Θ * → ConTOf TyA Θ

ConTHOf : {TyA1 TyA2 : ConK → Kind → Set₁}
        → ({Θ : ConK} {κ : Kind} → TyA1 Θ κ → TyA2 Θ κ)
        → ConTOf TyA1 Θ → ConTOf TyA2 Θ
ConTHOf f • = •
ConTHOf f (Δ ▷ σ) = ConTHOf f Δ ▷ f σ

{- Simultaneous substitutions for an arbitrary Ty-carrier. Unlike Sp,
   this stays generic (built from TyA) rather than becoming primitive
   algebra structure: nothing quantifies "uniformly over all
   substitutions" the way iterA/coiterA/FmapA quantify over all spines,
   so a homomorphism can always derive the matching target-side
   substitution pointwise from TyH (see SubHOf below) — no analogous
   naturality complication. -}

data SubOf (TyA : ConK → Kind → Set₁) (Θ' : ConK) : ConK → Set₁ where
  ε   : SubOf TyA Θ' •
  _,_ : SubOf TyA Θ' Θ → TyA Θ' κ → SubOf TyA Θ' (Θ ▷ κ)

wkSub1Of : {TyA : ConK → Kind → Set₁}
         → ({Θ : ConK} {κ κ' : Kind} → TyA Θ κ → TyA (Θ ▷ κ') κ)
         → SubOf TyA Θ' Θ → SubOf TyA (Θ' ▷ κ') Θ
wkSub1Of sucA ε = ε
wkSub1Of sucA (ρ , t) = wkSub1Of sucA ρ , sucA t

liftSubOf : {TyA : ConK → Kind → Set₁}
          → ({Θ : ConK} {κ : Kind} → TyA (Θ ▷ κ) κ)
          → ({Θ : ConK} {κ κ' : Kind} → TyA Θ κ → TyA (Θ ▷ κ') κ)
          → SubOf TyA Θ' Θ → SubOf TyA (Θ' ▷ κ) (Θ ▷ κ)
liftSubOf zeroA sucA ρ = wkSub1Of sucA ρ , zeroA

idSubOf : {TyA : ConK → Kind → Set₁}
        → ({Θ : ConK} {κ : Kind} → TyA (Θ ▷ κ) κ)
        → ({Θ : ConK} {κ κ' : Kind} → TyA Θ κ → TyA (Θ ▷ κ') κ)
        → (Θ : ConK) → SubOf TyA Θ Θ
idSubOf zeroA sucA • = ε
idSubOf zeroA sucA (Θ ▷ κ) = liftSubOf zeroA sucA (idSubOf zeroA sucA Θ)

SubHOf : {TyA1 TyA2 : ConK → Kind → Set₁}
       → ({Θ : ConK} {κ : Kind} → TyA1 Θ κ → TyA2 Θ κ)
       → SubOf TyA1 Θ' Θ → SubOf TyA2 Θ' Θ
SubHOf f ε = ε
SubHOf f (ρ , t) = SubHOf f ρ , f t

{- Same shape, for Tm — a substitution over a fixed Θ, parametrized by an
   arbitrary Tm-carrier TmA (over ConTOf TyA-contexts). -}

data SubTmOf {TyA : ConK → Kind → Set₁} (TmA : (Θ : ConK) → ConTOf TyA Θ → TyA Θ * → Set₁)
             (Θ : ConK) (Γ : ConTOf TyA Θ) : ConTOf TyA Θ → Set₁ where
  ε   : SubTmOf TmA Θ Γ •
  _,_ : {Δ : ConTOf TyA Θ} {σ : TyA Θ *} → SubTmOf TmA Θ Γ Δ → TmA Θ Γ σ → SubTmOf TmA Θ Γ (Δ ▷ σ)

wkSub1TmOf : {TyA : ConK → Kind → Set₁} {TmA : (Θ : ConK) → ConTOf TyA Θ → TyA Θ * → Set₁}
           → ({Θ : ConK} {Γ : ConTOf TyA Θ} {σ τ : TyA Θ *} → TmA Θ Γ σ → TmA Θ (Γ ▷ τ) σ)
           → {Θ : ConK} {Γ Δ : ConTOf TyA Θ} {τ : TyA Θ *} → SubTmOf TmA Θ Γ Δ → SubTmOf TmA Θ (Γ ▷ τ) Δ
wkSub1TmOf sucTmA ε = ε
wkSub1TmOf sucTmA (ρ , t) = wkSub1TmOf sucTmA ρ , sucTmA t

liftSubTmOf : {TyA : ConK → Kind → Set₁} {TmA : (Θ : ConK) → ConTOf TyA Θ → TyA Θ * → Set₁}
            → ({Θ : ConK} {Γ : ConTOf TyA Θ} {σ : TyA Θ *} → TmA Θ (Γ ▷ σ) σ)
            → ({Θ : ConK} {Γ : ConTOf TyA Θ} {σ τ : TyA Θ *} → TmA Θ Γ σ → TmA Θ (Γ ▷ τ) σ)
            → {Θ : ConK} {Γ Δ : ConTOf TyA Θ} {σ : TyA Θ *} → SubTmOf TmA Θ Γ Δ → SubTmOf TmA Θ (Γ ▷ σ) (Δ ▷ σ)
liftSubTmOf zeroTmA sucTmA ρ = wkSub1TmOf sucTmA ρ , zeroTmA

idSubTmOf : {TyA : ConK → Kind → Set₁} {TmA : (Θ : ConK) → ConTOf TyA Θ → TyA Θ * → Set₁}
          → ({Θ : ConK} {Γ : ConTOf TyA Θ} {σ : TyA Θ *} → TmA Θ (Γ ▷ σ) σ)
          → ({Θ : ConK} {Γ : ConTOf TyA Θ} {σ τ : TyA Θ *} → TmA Θ Γ σ → TmA Θ (Γ ▷ τ) σ)
          → {Θ : ConK} (Γ : ConTOf TyA Θ) → SubTmOf TmA Θ Γ Γ
idSubTmOf zeroTmA sucTmA • = ε
idSubTmOf zeroTmA sucTmA (Γ ▷ σ) = liftSubTmOf zeroTmA sucTmA (idSubTmOf zeroTmA sucTmA Γ)

SubTmHOf : {TyA1 TyA2 : ConK → Kind → Set₁}
         → {TmA1 : (Θ : ConK) → ConTOf TyA1 Θ → TyA1 Θ * → Set₁} {TmA2 : (Θ : ConK) → ConTOf TyA2 Θ → TyA2 Θ * → Set₁}
         → (TyH : {Θ : ConK} {κ : Kind} → TyA1 Θ κ → TyA2 Θ κ)
         → ({Θ : ConK} {Γ : ConTOf TyA1 Θ} {σ : TyA1 Θ *} → TmA1 Θ Γ σ → TmA2 Θ (ConTHOf TyH Γ) (TyH σ))
         → {Θ : ConK} {Γ Δ : ConTOf TyA1 Θ} → SubTmOf TmA1 Θ Γ Δ → SubTmOf TmA2 Θ (ConTHOf TyH Γ) (ConTHOf TyH Δ)
SubTmHOf TyH TmH ε = ε
SubTmHOf TyH TmH (ρ , t) = SubTmHOf TyH TmH ρ , TmH t

{- A model of hcontmunu -}

record Algebra : Set₂ where
  field
    {- Ty -}
    TyA   : ConK → Kind → Set₁
    zeroA : TyA (Θ ▷ κ) κ
    sucA  : TyA Θ κ → TyA (Θ ▷ κ') κ
    lamA  : TyA (Θ ▷ κ) κ' → TyA Θ (κ ⇒ κ')
    appA  : TyA Θ (κ ⇒ κ') → TyA Θ κ → TyA Θ κ'
    ΠA    : (I : Set) → (I → TyA Θ *) → TyA Θ *
    ΣA    : (I : Set) → (I → TyA Θ *) → TyA Θ *
    muA   : TyA Θ (κ ⇒ κ) → TyA Θ κ
    nuA   : TyA Θ (κ ⇒ κ) → TyA Θ κ

    {- Simultaneous substitution, primitive, together with the eight
       laws that were previously "for free" as the recursive clauses of
       h-cont-f-omega-munu.agda's _[_]Ty — since here _[_]TyA is just
       another primitive operation (not defined by recursion on t), those
       clauses have to be given explicitly as algebra laws instead. -}
    _[_]TyA : TyA Θ κ → SubOf TyA Θ' Θ → TyA Θ' κ

    subTy-zeroA : (ρ : SubOf TyA Θ' Θ) (t : TyA Θ' κ) → zeroA [ ρ , t ]TyA ≡ t
    subTy-sucA  : (s : TyA Θ κ) (ρ : SubOf TyA Θ' Θ) (t : TyA Θ' κ') → sucA s [ ρ , t ]TyA ≡ s [ ρ ]TyA
    subTy-lamA  : (s : TyA (Θ ▷ κ) κ') (ρ : SubOf TyA Θ' Θ)
                → lamA s [ ρ ]TyA ≡ lamA (s [ liftSubOf zeroA sucA ρ ]TyA)
    subTy-appA  : (s : TyA Θ (κ ⇒ κ')) (u : TyA Θ κ) (ρ : SubOf TyA Θ' Θ)
                → appA s u [ ρ ]TyA ≡ appA (s [ ρ ]TyA) (u [ ρ ]TyA)
    subTy-ΠA    : (f : I → TyA Θ *) (ρ : SubOf TyA Θ' Θ) → ΠA I f [ ρ ]TyA ≡ ΠA I (λ i → f i [ ρ ]TyA)
    subTy-ΣA    : (f : I → TyA Θ *) (ρ : SubOf TyA Θ' Θ) → ΣA I f [ ρ ]TyA ≡ ΣA I (λ i → f i [ ρ ]TyA)
    subTy-muA   : (F : TyA Θ (κ ⇒ κ)) (ρ : SubOf TyA Θ' Θ) → muA F [ ρ ]TyA ≡ muA (F [ ρ ]TyA)
    subTy-nuA   : (F : TyA Θ (κ ⇒ κ)) (ρ : SubOf TyA Θ' Θ) → nuA F [ ρ ]TyA ≡ nuA (F [ ρ ]TyA)

    Ty-βA : (t : TyA (Θ ▷ κ) κ') (u : TyA Θ κ) → appA (lamA t) u ≡ t [ idSubOf zeroA sucA Θ , u ]TyA
    Ty-ηA : (t : TyA Θ (κ ⇒ κ')) → lamA (appA (sucA t) zeroA) ≡ t

    {- Spines: argument lists that fully apply a Θ-type of kind κ down to
       kind *. Kept primitive (a field, like TyA) rather than derived
       from TyA — a homomorphism needs to treat SpH as independent
       structure, not something forced to be TyH mapped pointwise, for
       iterA/coiterA/FmapA's "uniform in the spine" arguments below to
       have a sensible preservation condition at all. -}
    SpA  : ConK → Kind → Set₁
    εA   : SpA Θ *
    _,A_ : TyA Θ κ → SpA Θ κ' → SpA Θ (κ ⇒ κ')
    apA  : TyA Θ κ → SpA Θ κ → TyA Θ *

    {- Tm, over contexts of TyA-types. Δ/σ/τ are bound per-field (rather
       than via a top-level `variable`) since they depend on TyA, itself
       a field of this same record. -}
    TmA   : (Θ : ConK) → ConTOf TyA Θ → TyA Θ * → Set₁

    zeroTmA : {Δ : ConTOf TyA Θ} {σ : TyA Θ *} → TmA Θ (Δ ▷ σ) σ
    sucTmA  : {Δ : ConTOf TyA Θ} {σ τ : TyA Θ *} → TmA Θ Δ σ → TmA Θ (Δ ▷ τ) σ
    injA    : {Δ : ConTOf TyA Θ} (F : I → TyA Θ *) (i : I) → TmA Θ Δ (F i) → TmA Θ Δ (ΣA I F)
    caseA   : {Δ : ConTOf TyA Θ} {τ : TyA Θ *} (F : I → TyA Θ *) (s : TmA Θ Δ (ΣA I F))
            → ((i : I) → TmA Θ (Δ ▷ F i) τ) → TmA Θ Δ τ
    prjA    : {Δ : ConTOf TyA Θ} (F : I → TyA Θ *) → TmA Θ Δ (ΠA I F) → (i : I) → TmA Θ Δ (F i)
    pairA   : {Δ : ConTOf TyA Θ} (F : I → TyA Θ *) → ((i : I) → TmA Θ Δ (F i)) → TmA Θ Δ (ΠA I F)

    conA   : {Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (sp : SpA Θ κ)
           → TmA Θ Δ (apA (appA F (muA F)) sp) → TmA Θ Δ (apA (muA F) sp)
    iterA  : {Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (C : TyA Θ κ)
           → ((sp : SpA Θ κ) → TmA Θ (Δ ▷ apA (appA F C) sp) (apA C sp))
           → (sp : SpA Θ κ) → TmA Θ Δ (apA (muA F) sp) → TmA Θ Δ (apA C sp)
    outA   : {Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (sp : SpA Θ κ)
           → TmA Θ Δ (apA (nuA F) sp) → TmA Θ Δ (apA (appA F (nuA F)) sp)
    coiterA : {Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (C : TyA Θ κ)
           → ((sp : SpA Θ κ) → TmA Θ (Δ ▷ apA C sp) (apA (appA F C) sp))
           → (sp : SpA Θ κ) → TmA Θ Δ (apA C sp) → TmA Θ Δ (apA (nuA F) sp)

    {- Simultaneous Tm substitution, primitive, together with the ten
       laws that were the recursive clauses of h-cont-f-omega-munu.agda's
       _[_]Tm, for the same reason as _[_]TyA above. -}
    _[_]TmA : {Γ Δ : ConTOf TyA Θ} {σ : TyA Θ *} → TmA Θ Δ σ → SubTmOf TmA Θ Γ Δ → TmA Θ Γ σ

    subTm-zeroA : {Γ Δ : ConTOf TyA Θ} {σ : TyA Θ *} (ρ : SubTmOf TmA Θ Γ Δ) (t : TmA Θ Γ σ)
                → zeroTmA [ ρ , t ]TmA ≡ t
    subTm-sucA  : {Γ Δ : ConTOf TyA Θ} {σ τ : TyA Θ *} (s : TmA Θ Δ σ) (ρ : SubTmOf TmA Θ Γ Δ) (t : TmA Θ Γ τ)
                → sucTmA s [ ρ , t ]TmA ≡ s [ ρ ]TmA
    subTm-injA  : {Γ Δ : ConTOf TyA Θ} (F : I → TyA Θ *) (i : I) (s : TmA Θ Δ (F i)) (ρ : SubTmOf TmA Θ Γ Δ)
                → injA F i s [ ρ ]TmA ≡ injA F i (s [ ρ ]TmA)
    subTm-caseA : {Γ Δ : ConTOf TyA Θ} {τ : TyA Θ *} (F : I → TyA Θ *) (s : TmA Θ Δ (ΣA I F))
                  (k : (i : I) → TmA Θ (Δ ▷ F i) τ) (ρ : SubTmOf TmA Θ Γ Δ)
                → caseA F s k [ ρ ]TmA ≡ caseA F (s [ ρ ]TmA) (λ i → k i [ liftSubTmOf zeroTmA sucTmA ρ ]TmA)
    subTm-prjA  : {Γ Δ : ConTOf TyA Θ} (F : I → TyA Θ *) (s : TmA Θ Δ (ΠA I F)) (i : I) (ρ : SubTmOf TmA Θ Γ Δ)
                → prjA F s i [ ρ ]TmA ≡ prjA F (s [ ρ ]TmA) i
    subTm-pairA : {Γ Δ : ConTOf TyA Θ} (F : I → TyA Θ *) (f : (i : I) → TmA Θ Δ (F i)) (ρ : SubTmOf TmA Θ Γ Δ)
                → pairA F f [ ρ ]TmA ≡ pairA F (λ i → f i [ ρ ]TmA)
    subTm-conA  : {Γ Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (sp : SpA Θ κ)
                  (s : TmA Θ Δ (apA (appA F (muA F)) sp)) (ρ : SubTmOf TmA Θ Γ Δ)
                → conA F sp s [ ρ ]TmA ≡ conA F sp (s [ ρ ]TmA)
    subTm-iterA : {Γ Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (C : TyA Θ κ)
                  (alg : (sp : SpA Θ κ) → TmA Θ (Δ ▷ apA (appA F C) sp) (apA C sp))
                  (sp : SpA Θ κ) (s : TmA Θ Δ (apA (muA F) sp)) (ρ : SubTmOf TmA Θ Γ Δ)
                → iterA F C alg sp s [ ρ ]TmA
                  ≡ iterA F C (λ sp' → alg sp' [ liftSubTmOf zeroTmA sucTmA ρ ]TmA) sp (s [ ρ ]TmA)
    subTm-outA  : {Γ Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (sp : SpA Θ κ)
                  (s : TmA Θ Δ (apA (nuA F) sp)) (ρ : SubTmOf TmA Θ Γ Δ)
                → outA F sp s [ ρ ]TmA ≡ outA F sp (s [ ρ ]TmA)
    subTm-coiterA : {Γ Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (C : TyA Θ κ)
                  (coalg : (sp : SpA Θ κ) → TmA Θ (Δ ▷ apA C sp) (apA (appA F C) sp))
                  (sp : SpA Θ κ) (c : TmA Θ Δ (apA C sp)) (ρ : SubTmOf TmA Θ Γ Δ)
                → coiterA F C coalg sp c [ ρ ]TmA
                  ≡ coiterA F C (λ sp' → coalg sp' [ liftSubTmOf zeroTmA sucTmA ρ ]TmA) sp (c [ ρ ]TmA)

    Σ-βA : {Δ : ConTOf TyA Θ} {τ : TyA Θ *} (F : I → TyA Θ *) (k : (i : I) → TmA Θ (Δ ▷ F i) τ)
           (i : I) (t : TmA Θ Δ (F i))
         → caseA F (injA F i t) k ≡ (k i) [ idSubTmOf zeroTmA sucTmA Δ , t ]TmA

    Π-βA : {Δ : ConTOf TyA Θ} (F : I → TyA Θ *) (f : (i : I) → TmA Θ Δ (F i)) (i : I)
         → prjA F (pairA F f) i ≡ f i

    Π-ηA : {Δ : ConTOf TyA Θ} (F : I → TyA Θ *) (t : TmA Θ Δ (ΠA I F))
         → pairA F (λ i → prjA F t i) ≡ t

    Σ-ηA : {Δ : ConTOf TyA Θ} (F : I → TyA Θ *) (s : TmA Θ Δ (ΣA I F))
         → caseA F s (λ i → injA F i zeroTmA) ≡ s

    FmapA : {Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) {A B : TyA Θ κ}
          → ((sp : SpA Θ κ) → TmA Θ Δ (apA A sp) → TmA Θ Δ (apA B sp))
          → (sp : SpA Θ κ) → TmA Θ Δ (apA (appA F A) sp) → TmA Θ Δ (apA (appA F B) sp)

    mu-βA : {Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (C : TyA Θ κ)
          → (alg : (sp : SpA Θ κ) → TmA Θ (Δ ▷ apA (appA F C) sp) (apA C sp))
          → (sp : SpA Θ κ) (t : TmA Θ Δ (apA (appA F (muA F)) sp))
          → iterA F C alg sp (conA F sp t) ≡ (alg sp) [ idSubTmOf zeroTmA sucTmA Δ , FmapA F (iterA F C alg) sp t ]TmA

    mu-ηA : {Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (C : TyA Θ κ)
          → (alg : (sp : SpA Θ κ) → TmA Θ (Δ ▷ apA (appA F C) sp) (apA C sp))
          → (h : (sp : SpA Θ κ) → TmA Θ Δ (apA (muA F) sp) → TmA Θ Δ (apA C sp))
          → ((sp : SpA Θ κ) (t : TmA Θ Δ (apA (appA F (muA F)) sp))
             → h sp (conA F sp t) ≡ (alg sp) [ idSubTmOf zeroTmA sucTmA Δ , FmapA F h sp t ]TmA)
          → (sp : SpA Θ κ) (n : TmA Θ Δ (apA (muA F) sp)) → h sp n ≡ iterA F C alg sp n

    nu-βA : {Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (C : TyA Θ κ)
          → (coalg : (sp : SpA Θ κ) → TmA Θ (Δ ▷ apA C sp) (apA (appA F C) sp))
          → (sp : SpA Θ κ) (c : TmA Θ Δ (apA C sp))
          → outA F sp (coiterA F C coalg sp c)
            ≡ FmapA F (coiterA F C coalg) sp ((coalg sp) [ idSubTmOf zeroTmA sucTmA Δ , c ]TmA)

    nu-ηA : {Δ : ConTOf TyA Θ} (F : TyA Θ (κ ⇒ κ)) (C : TyA Θ κ)
          → (coalg : (sp : SpA Θ κ) → TmA Θ (Δ ▷ apA C sp) (apA (appA F C) sp))
          → (h : (sp : SpA Θ κ) → TmA Θ Δ (apA C sp) → TmA Θ Δ (apA (nuA F) sp))
          → ((sp : SpA Θ κ) (c : TmA Θ Δ (apA C sp))
             → outA F sp (h sp c) ≡ FmapA F h sp ((coalg sp) [ idSubTmOf zeroTmA sucTmA Δ , c ]TmA))
          → (sp : SpA Θ κ) (c : TmA Θ Δ (apA C sp)) → h sp c ≡ coiterA F C coalg sp c

{- A homomorphism of models: preserves every constructor and every
   substitution/spine operation. Preserving the equations (Ty-βA, Σ-βA,
   mu-βA, …) doesn't need to be stated separately — it's automatic (cong)
   once the constructors are preserved. -}

record AlgebraHom (𝔸 𝔹 : Algebra) : Set₂ where
  private
    module A = Algebra 𝔸
    module B = Algebra 𝔹

  field
    TyH : {Θ : ConK} {κ : Kind} → A.TyA Θ κ → B.TyA Θ κ

    TyH-zero : TyH (A.zeroA {Θ = Θ} {κ = κ}) ≡ B.zeroA
    TyH-suc  : (t : A.TyA Θ κ) → TyH (A.sucA {κ' = κ'} t) ≡ B.sucA (TyH t)
    TyH-lam  : (t : A.TyA (Θ ▷ κ) κ') → TyH (A.lamA t) ≡ B.lamA (TyH t)
    TyH-app  : (t : A.TyA Θ (κ ⇒ κ')) (u : A.TyA Θ κ) → TyH (A.appA t u) ≡ B.appA (TyH t) (TyH u)
    TyH-Π    : (f : I → A.TyA Θ *) → TyH (A.ΠA I f) ≡ B.ΠA I (λ i → TyH (f i))
    TyH-Σ    : (f : I → A.TyA Θ *) → TyH (A.ΣA I f) ≡ B.ΣA I (λ i → TyH (f i))
    TyH-mu   : (F : A.TyA Θ (κ ⇒ κ)) → TyH (A.muA F) ≡ B.muA (TyH F)
    TyH-nu   : (F : A.TyA Θ (κ ⇒ κ)) → TyH (A.nuA F) ≡ B.nuA (TyH F)
    TyH-sub  : (t : A.TyA Θ κ) (ρ : SubOf A.TyA Θ' Θ) → TyH (t A.[ ρ ]TyA) ≡ TyH t B.[ SubHOf TyH ρ ]TyA

    SpH   : {Θ : ConK} {κ : Kind} → A.SpA Θ κ → B.SpA Θ κ
    SpH-ε : SpH (A.εA {Θ = Θ}) ≡ B.εA
    SpH-, : (t : A.TyA Θ κ) (sp : A.SpA Θ κ') → SpH (t A.,A sp) ≡ TyH t B.,A SpH sp
    apH   : (t : A.TyA Θ κ) (sp : A.SpA Θ κ) → TyH (A.apA t sp) ≡ B.apA (TyH t) (SpH sp)

    {- Tm. Written using ConTHOf TyH directly (rather than a locally
       bound abbreviation) since Agda records don't allow non-field
       declarations before the last field block, and there's more field
       block to come. -}
    TmH : {Θ : ConK} {Δ : ConTOf A.TyA Θ} {σ : A.TyA Θ *} → A.TmA Θ Δ σ → B.TmA Θ (ConTHOf TyH Δ) (TyH σ)

    TmH-zero : {Δ : ConTOf A.TyA Θ} {σ : A.TyA Θ *} → TmH (A.zeroTmA {Δ = Δ} {σ = σ}) ≡ B.zeroTmA
    TmH-suc  : {Δ : ConTOf A.TyA Θ} {σ τ : A.TyA Θ *} (t : A.TmA Θ Δ σ)
             → TmH (A.sucTmA {τ = τ} t) ≡ B.sucTmA (TmH t)

    TmH-inj : {Δ : ConTOf A.TyA Θ} (F : I → A.TyA Θ *) (i : I) (t : A.TmA Θ Δ (F i))
            → subst (B.TmA Θ (ConTHOf TyH Δ)) (TyH-Σ F) (TmH (A.injA F i t)) ≡ B.injA (λ i → TyH (F i)) i (TmH t)

    TmH-case : {Δ : ConTOf A.TyA Θ} {τ : A.TyA Θ *} (F : I → A.TyA Θ *) (s : A.TmA Θ Δ (A.ΣA I F))
               (k : (i : I) → A.TmA Θ (Δ ▷ F i) τ)
             → TmH (A.caseA F s k) ≡ B.caseA (λ i → TyH (F i)) (subst (B.TmA Θ (ConTHOf TyH Δ)) (TyH-Σ F) (TmH s)) (λ i → TmH (k i))

    TmH-prj : {Δ : ConTOf A.TyA Θ} (F : I → A.TyA Θ *) (t : A.TmA Θ Δ (A.ΠA I F)) (i : I)
            → TmH (A.prjA F t i) ≡ B.prjA (λ i → TyH (F i)) (subst (B.TmA Θ (ConTHOf TyH Δ)) (TyH-Π F) (TmH t)) i

    TmH-pair : {Δ : ConTOf A.TyA Θ} (F : I → A.TyA Θ *) (f : (i : I) → A.TmA Θ Δ (F i))
             → subst (B.TmA Θ (ConTHOf TyH Δ)) (TyH-Π F) (TmH (A.pairA F f)) ≡ B.pairA (λ i → TyH (F i)) (λ i → TmH (f i))

    TmH-sub : {Γ Δ : ConTOf A.TyA Θ} {σ : A.TyA Θ *} (t : A.TmA Θ Δ σ) (ρ : SubTmOf A.TmA Θ Γ Δ)
            → TmH (t A.[ ρ ]TmA) ≡ TmH t B.[ SubTmHOf TyH TmH ρ ]TmA

    TmH-con : {Δ : ConTOf A.TyA Θ} (F : A.TyA Θ (κ ⇒ κ)) (sp : A.SpA Θ κ) (t : A.TmA Θ Δ (A.apA (A.appA F (A.muA F)) sp))
            → subst (B.TmA Θ (ConTHOf TyH Δ))
                     (trans (apH (A.muA F) sp) (cong (λ x → B.apA x (SpH sp)) (TyH-mu F)))
                     (TmH (A.conA F sp t))
              ≡ B.conA (TyH F) (SpH sp)
                  (subst (B.TmA Θ (ConTHOf TyH Δ))
                         (trans (apH (A.appA F (A.muA F)) sp)
                                (cong (λ x → B.apA x (SpH sp)) (trans (TyH-app F (A.muA F)) (cong (B.appA (TyH F)) (TyH-mu F)))))
                         (TmH t))

    TmH-out : {Δ : ConTOf A.TyA Θ} (F : A.TyA Θ (κ ⇒ κ)) (sp : A.SpA Θ κ) (t : A.TmA Θ Δ (A.apA (A.nuA F) sp))
            → subst (B.TmA Θ (ConTHOf TyH Δ))
                     (trans (apH (A.appA F (A.nuA F)) sp)
                            (cong (λ x → B.apA x (SpH sp)) (trans (TyH-app F (A.nuA F)) (cong (B.appA (TyH F)) (TyH-nu F)))))
                     (TmH (A.outA F sp t))
              ≡ B.outA (TyH F) (SpH sp)
                  (subst (B.TmA Θ (ConTHOf TyH Δ))
                         (trans (apH (A.nuA F) sp) (cong (λ x → B.apA x (SpH sp)) (TyH-nu F)))
                         (TmH t))

    {- iterA/coiterA/FmapA are each "uniform in the spine": their
       higher-order argument (alg/coalg/f) is a function of an arbitrary
       sp. A homomorphism can't derive a matching B-side function from
       just TmH (TyH/SpH aren't surjective in general), so preservation
       needs an independently-given target-side function plus a
       naturality hypothesis connecting the two via TmH, rather than a
       single equation — standard for morphisms of algebras with
       HOAS-style/parametrized operations. -}

    TmH-iter : {Δ : ConTOf A.TyA Θ} (F : A.TyA Θ (κ ⇒ κ)) (C : A.TyA Θ κ)
             → (alg : (sp : A.SpA Θ κ) → A.TmA Θ (Δ ▷ A.apA (A.appA F C) sp) (A.apA C sp))
             → (algB : (sp : B.SpA Θ κ) → B.TmA Θ (ConTHOf TyH Δ ▷ B.apA (B.appA (TyH F) (TyH C)) sp) (B.apA (TyH C) sp))
             → ((sp : A.SpA Θ κ)
                → subst₂ (λ x y → B.TmA Θ (ConTHOf TyH Δ ▷ x) y)
                         (trans (apH (A.appA F C) sp) (cong (λ x → B.apA x (SpH sp)) (TyH-app F C)))
                         (apH C sp)
                         (TmH (alg sp))
                  ≡ algB (SpH sp))
             → (sp : A.SpA Θ κ) (t : A.TmA Θ Δ (A.apA (A.muA F) sp))
             → subst (B.TmA Θ (ConTHOf TyH Δ)) (apH C sp) (TmH (A.iterA F C alg sp t))
               ≡ B.iterA (TyH F) (TyH C) algB (SpH sp)
                   (subst (B.TmA Θ (ConTHOf TyH Δ))
                          (trans (apH (A.muA F) sp) (cong (λ x → B.apA x (SpH sp)) (TyH-mu F)))
                          (TmH t))

    TmH-coiter : {Δ : ConTOf A.TyA Θ} (F : A.TyA Θ (κ ⇒ κ)) (C : A.TyA Θ κ)
               → (coalg : (sp : A.SpA Θ κ) → A.TmA Θ (Δ ▷ A.apA C sp) (A.apA (A.appA F C) sp))
               → (coalgB : (sp : B.SpA Θ κ) → B.TmA Θ (ConTHOf TyH Δ ▷ B.apA (TyH C) sp) (B.apA (B.appA (TyH F) (TyH C)) sp))
               → ((sp : A.SpA Θ κ)
                  → subst₂ (λ x y → B.TmA Θ (ConTHOf TyH Δ ▷ x) y)
                           (apH C sp)
                           (trans (apH (A.appA F C) sp) (cong (λ x → B.apA x (SpH sp)) (TyH-app F C)))
                           (TmH (coalg sp))
                    ≡ coalgB (SpH sp))
               → (sp : A.SpA Θ κ) (c : A.TmA Θ Δ (A.apA C sp))
               → subst (B.TmA Θ (ConTHOf TyH Δ))
                        (trans (apH (A.nuA F) sp) (cong (λ x → B.apA x (SpH sp)) (TyH-nu F)))
                        (TmH (A.coiterA F C coalg sp c))
                 ≡ B.coiterA (TyH F) (TyH C) coalgB (SpH sp)
                     (subst (B.TmA Θ (ConTHOf TyH Δ)) (apH C sp) (TmH c))

    TmH-Fmap : {Δ : ConTOf A.TyA Θ} (F : A.TyA Θ (κ ⇒ κ)) {X Y : A.TyA Θ κ}
             → (f : (sp : A.SpA Θ κ) → A.TmA Θ Δ (A.apA X sp) → A.TmA Θ Δ (A.apA Y sp))
             → (fB : (sp : B.SpA Θ κ) → B.TmA Θ (ConTHOf TyH Δ) (B.apA (TyH X) sp) → B.TmA Θ (ConTHOf TyH Δ) (B.apA (TyH Y) sp))
             → ((sp : A.SpA Θ κ) (x : A.TmA Θ Δ (A.apA X sp))
                → subst (B.TmA Θ (ConTHOf TyH Δ)) (apH Y sp) (TmH (f sp x))
                  ≡ fB (SpH sp) (subst (B.TmA Θ (ConTHOf TyH Δ)) (apH X sp) (TmH x)))
             → (sp : A.SpA Θ κ) (t : A.TmA Θ Δ (A.apA (A.appA F X) sp))
             → subst (B.TmA Θ (ConTHOf TyH Δ))
                      (trans (apH (A.appA F Y) sp) (cong (λ x → B.apA x (SpH sp)) (TyH-app F Y)))
                      (TmH (A.FmapA F f sp t))
               ≡ B.FmapA (TyH F) fB (SpH sp)
                   (subst (B.TmA Θ (ConTHOf TyH Δ))
                          (trans (apH (A.appA F X) sp) (cong (λ x → B.apA x (SpH sp)) (TyH-app F X)))
                          (TmH t))

{- Initiality, postulated -}

postulate
  𝕀           : Algebra
  init        : (𝔸 : Algebra) → AlgebraHom 𝕀 𝔸
  init-unique : (𝔸 : Algebra) (f g : AlgebraHom 𝕀 𝔸) → f ≡ g

{- The constructors and equations of hcontmunu, derived as projections
   from the initial algebra rather than declared as data + separate
   postulates. h-cont-f-omega-munu.agda overloads zero/suc between Ty and
   Tm (Agda's constructor-overload resolution, which only applies to
   `data` constructors); `open...renaming` can't recreate that for record
   projections (renaming two different fields to the same name is
   reported as ambiguous, not resolved by expected type), so Tm's copies
   are named zeroTm/sucTm here instead. -}

open Algebra 𝕀 public
  renaming
    ( TyA to Ty
    ; zeroA to zero
    ; sucA to suc
    ; lamA to lam
    ; appA to app
    ; ΠA to Π
    ; ΣA to Σ
    ; muA to mu
    ; nuA to nu
    ; _[_]TyA to _[_]Ty
    ; Ty-βA to Ty-β
    ; Ty-ηA to Ty-η
    ; SpA to Sp
    ; εA to εSp
    ; _,A_ to _,Sp_
    ; apA to apSp
    ; TmA to Tm
    ; zeroTmA to zeroTm
    ; sucTmA to sucTm
    ; injA to inj
    ; caseA to case
    ; prjA to prj
    ; pairA to pair
    ; conA to con
    ; iterA to iter
    ; outA to out
    ; coiterA to coiter
    ; _[_]TmA to _[_]Tm
    ; Σ-βA to Σ-β
    ; Π-βA to Π-β
    ; Π-ηA to Π-η
    ; Σ-ηA to Σ-η
    ; FmapA to Fmap
    ; mu-βA to mu-β
    ; mu-ηA to mu-η
    ; nu-βA to nu-β
    ; nu-ηA to nu-η
    )

ConT : ConK → Set₁
ConT Θ = ConTOf Ty Θ
