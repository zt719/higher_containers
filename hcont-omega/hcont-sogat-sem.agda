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

{-
Simple semantics (GAT)

K : Kind
⟦ K ⟧ : Cat
⟦ * ⟧ = Set
⟦ K ⇒ L ⟧ = ⟦ K ⟧ ⇒ ⟦ L ⟧ (functors)

A : Ty K
⟦ A ⟧ : |⟦ K ⟧

more general
Γ : KindCon
⟦ Γ ⟧ : Cat (product cat)

A : Ty Γ K
⟦ A ⟧ : ⟦ Γ ⟧ ⇒ ⟦ A ⟧

Δ : TyCon Γ
⟦ Δ ⟧ : ⟦ Γ ⟧ ⇒ Set

Δ : TyCon Γ, A : Ty Γ *
a : Tm Γ Δ A
⟦ a ⟧ : ∫_(X : ⟦ Γ ⟧) → ⟦ Δ ⟧ X → ⟦ A ⟧ X




Ty, Tm are locally representable
Given Cont : Cat

[| Kind |] : Psh Cont
* : ∫_X [| Kind |] X
⇒ : ∫_X (Kind X) → Kind X → Kind X

Ty : Psh (∫ Kind) = DepPsh Kind

Tm : DepPSh (Σ Kind Ty)

for example Cont = 1, Cat
Kind C = C => Set

=> = Functors

GAT
Kind => Cat
* = Set
=> = Functor

KindCon = Product

Ty Γ K = Γ => K
Ty * * = Set => Set : Set

TyCon = Set

-}


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



    Spine : Set  -- List Kind
    Dom : Kind → Spine
    Tys : Spine → Set 
      
    -}
