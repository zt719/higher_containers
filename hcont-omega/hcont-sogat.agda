open import Function.Base using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (_,_) renaming (Σ to Sigma)

record _≅_ (A B : Set) : Set where
    field
        to      : A → B
        from    : B → A
        to∘from : to ∘ from ≡ id
        from∘to : from ∘ to ≡ id
open _≅_ public

postulate
    Kind : Set
    Ty : Kind → Set
    
variable 
    K L : Kind
    I : Set

postulate

    * : Kind
    _⇒_ : Kind → Kind → Kind

    ⇒-iso : (Ty K → Ty L) ≅ Ty (K ⇒ L)

    Tm : Ty * → Set

    Π : (I : Set)(F : I → Ty *) → Ty *
    prod : (F : I → Ty *)
            → ((i : I) → Tm (F i)) ≅ Tm (Π I F) 

    Σ : (I : Set)(F : I → Ty *) → Ty *
    inj : (F : I → Ty *)
            → Sigma I (λ i → Tm (F i)) ≅ Tm (Σ I F)

LAM : (Ty K → Ty L) → Ty (K ⇒ L)
LAM = to ⇒-iso

APP : Ty (K ⇒ L) → (Ty K → Ty L)
APP = from ⇒-iso

TUP : (F : I → Ty *) → ((i : I) → Tm (F i)) → Tm (Π I F)
TUP F = to (prod F)

PROJ : (F : I → Ty *) → Tm (Π I F) → (i : I) → Tm (F i)
PROJ F = from (prod F)

INJ : (F : I → Ty *) → Sigma I (λ i → Tm (F i)) → Tm (Σ I F)
INJ F = to (inj F)

OUT : (F : I → Ty *) → Tm (Σ I F) → Sigma I (λ i → Tm (F i))
OUT F = from (inj F)

inj-at : (F : I → Ty *) (i : I) → Tm (F i) → Tm (Σ I F)
inj-at F i t = INJ F (i , t)

{-
If we want to interpret the SOGAT directly we need to define a category of contexts. In terms of the GAT that would be
Θ : ConK, Γ : ConT Θ
and morphisms are pairs of substitutions. In our intended semantics this would correspond to
⟦Θ⟧ : Cat , ⟦Γ⟧ : ⟦Θ⟧ ⇒ Set
and morphisms are functors and natural transformations.

I think it is a bit weird to interpret Kinds as presheaves because they should be constant. In general it seems that the SOGAT semantics introduces too many dependencies in a non-dependent setting. Maybe you know a way around this?

----------------------------------------------------------------------

The way around it: the context category above is bigger than this SOGAT
needs. Read off which operations bind an object variable. Only

    ⇒-iso : (Ty K → Ty L) ≅ Ty (K ⇒ L)

binds, and it binds a Ty K. Nothing binds a Tm: in Π/Σ/prod/inj the
I : Set is a parameter and i : I a metavariable of parameter sort, not a
bound term variable. So this SOGAT has exactly ONE variable sort, Ty,
indexed by the PARAMETER Kind. Its category of contexts is just

    𝓒_K = ConK          -- telescopes of type variables tagged by Kinds

with no Γ. (The Γ : ConT Θ belongs to the GAT, which reintroduces
explicit term variables; the SOGAT never does.)

Kind is a parameter, not a variable sort, so it is not interpreted as a
nontrivial presheaf at all -- it lives in the base. That is the "should
be constant" you wanted; it is constant because it is a parameter.

    ⟦Kind⟧ : Set₁       ⟦Kind⟧    = Cat
    ⟦*⟧                 ⟦*⟧       = Set
    ⟦_⇒_⟧               ⟦K ⇒ L⟧   = [ ⟦K⟧ , ⟦L⟧ ]      -- functor category

The three sorts:

    ⟦Kind⟧  : object of the base                       = Cat
    ⟦Ty⟧    : presheaf on ∫⟦Kind⟧ over 𝓒_K (DepPsh Kind)
              ⟦Ty⟧ Θ κ = [ ⟦Θ⟧ , ⟦κ⟧ ]
              with ⟦•⟧ = 𝟙,  ⟦Θ ▷ κ⟧ = ⟦Θ⟧ × ⟦κ⟧
    ⟦Tm⟧    : dependent presheaf on ∫(⟦Ty⟧ at *), NO further context
              ⟦Tm⟧ Θ σ = ∫_(X : ⟦Θ⟧) ⟦σ⟧ X = lim ⟦σ⟧

Ty is the only sort that genuinely uses presheaf structure, and it uses
it for the binder. Tm is just global sections: every ⟦κ⟧ has an initial
object, hence so does ⟦Θ⟧, and lim ⟦σ⟧ = ⟦σ⟧ at the empty type
environment.

⇒-iso = local representability of Ty in the 𝓒_K direction

    𝓒_K(Δ , Θ ▷ κ) ≅ Σ (f : 𝓒_K(Δ , Θ)) . ⟦Ty⟧ Δ κ

together with the Π/exponential structure of that CwF:

    ⟦Ty⟧ Θ (κ ⇒ κ')        ≅ ⟦Ty⟧ (Θ ▷ κ) κ'
    [ ⟦Θ⟧ , [ ⟦κ⟧ , ⟦κ'⟧ ] ] ≅ [ ⟦Θ⟧ × ⟦κ⟧ , ⟦κ'⟧ ]      -- currying

LAM / APP are the two transports. The binder needs no term context.

prod : Π_i lim ⟦F i⟧ ≅ lim (Π_i ⟦F i⟧)   -- limits commute with products, always
inj  : Σ_i lim ⟦F i⟧ ≅ lim (Σ_i ⟦F i⟧)   -- only because ⟦Θ⟧ has an initial object

That fragility is the point: in the GAT, Σ is NOT a closed-term iso but
inj/case + Σ-β/Σ-η fibred over an arbitrary Δ and τ, and that fibred form

    Nat(⟦Δ⟧ × ⟦Σ I F⟧ , ⟦τ⟧) ≅ Π_i Nat(⟦Δ⟧ × ⟦F i⟧ , ⟦τ⟧)

holds structurally (product distributes over coproduct pointwise), with
no initial-object assumption. Same medicine as for Γ: fibre the law over
contexts, don't state it on closed terms.

Relation to hcont-f-omega.agda: same theory, after (i) de Bruijn type
variables (zero/suc/lam/app for ⇒-iso) and (ii) an explicit term context
Γ. Its ⟦Γ⟧ : ⟦Θ⟧ ⇒ Set, ⟦a⟧ ∈ ∫_X ⟦Γ⟧ X → ⟦σ⟧ X restricts at Γ = • to
the SOGAT's ⟦Tm⟧ Θ σ = ∫_X ⟦σ⟧ X. The Γ-dependency is the first-order
presentation, not something the SOGAT forces.

If you DO want the flat model over (Θ , Γ) pairs (for gluing / canonicity
/ normalisation): objects (Θ , Γ), morphisms (δ , γ) = type-variable
substitution + term substitution; semantic category is the Grothendieck
construction

    𝓢 = ∫^(𝓚 : Cat) [ 𝓚 , Set ]

objects (𝓚 , G : 𝓚 ⇒ Set), morphisms (𝓚₁,G₁) → (𝓚₀,G₀) =
(H : 𝓚₁ ⇒ 𝓚₀ , α : G₁ ⇒ G₀ ∘ H) -- a functor and a natural
transformation, as above. ⟦_⟧ : 𝓒 → 𝓢 is the model, a map of fibrations
over 𝓒_K → Cat. The redundant dependencies then reappear as: ⟦Kind⟧ and
⟦Ty⟧ must be pulled back along 𝓒 → 𝓒_K → 𝟙. That is not a hack -- it is
exactly "Kind is a parameter" and "Ty is term-context-independent", and
it is automatic if the model is built as a tower of CwFs (base ↦ Cat;
kind-context layer carrying ⟦Ty⟧; term-context layer carrying ⟦Tm⟧)
rather than one flat Psh(𝓒). The choice of base (1 vs Cat vs syntactic)
is orthogonal: it only picks which presheaf topos you land in.

Pointers:
  Uemura, A general framework for the semantics of type theory (MSCS 2023)
    -- representable map categories; SOGAT = GAT + representability.
  Bocquet–Kaposi–Sattler, For the metatheory of type theory, internal
    sconing is enough (FSCD 2023) -- tower of CwFs, parameters vs sorts.
  Fiore–Hur, Second-order equational logic; Fiore–Mahmoud, Second-order
    algebraic theories -- parameters vs variable sorts, Psh(𝔽) models.
  Harper, equational LF -- sorts as locally representable presheaves.
-}