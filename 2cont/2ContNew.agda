{-# OPTIONS --guardedness --with-K --type-in-type #-}

module 2ContNew where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality

variable X Y : Set

uip : ∀ {ℓ} {A : Set ℓ} {x y : A}
  (p q : x ≡ y) → p ≡ q
uip refl refl = refl

postulate
  funExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
    {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

funExt⁻ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
  {f g : (a : A) → B a}
  → f ≡ g
  → (a : A) → f a ≡ g a
funExt⁻ refl a = refl

open import Agda.Primitive

record _≅_ {ℓ} (A B : Set ℓ) : Set (lsuc ℓ) where
  field
    to : A → B
    from : B → A
    to∘from : to ∘ from ≡ id
    from∘to : from ∘ to ≡ id

postulate
  setExt : ∀ {ℓ} {A B : Set ℓ}
    → A ≅ B → A ≡ B
  
setExt⁻ : ∀ {ℓ} {A B : Set ℓ}
  → A ≡ B → A ≅ B
setExt⁻ refl = record { to = id ; from = id ; to∘from = refl ; from∘to = refl }

Σ-≡ :
  ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
  Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂) →
  (a₁ , b₁) ≡ (a₂ , b₂)
Σ-≡ (refl , refl) = refl

{- Containers -}

infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set
    
variable
  SP TQ SP' TQ' UV UV' F G : Cont

⟦_⟧ : Cont → Set → Set
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

⟦_⟧₁ : (SP : Cont) → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g  (s , f) = s , g ∘ f

{- Category of Containers -}

infixr 0 _→ᶜ_
record _→ᶜ_ (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    fS : S → T
    fP : (s : S) → Q (fS s) → P s

⟦_⟧→ᶜ : SP →ᶜ TQ → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ fS ◃ fP ⟧→ᶜ X (s , f) = fS s , f ∘ fP s

→ᶜ-≡-intro :
  {S T : Set} {P : S → Set} {Q : T → Set}
  {fS fS' : S → T} {fP : (s : S) → Q (fS s) → P s}
  {fP' : (s : S) → Q (fS' s) → P s}
  → (eqfS : fS ≡ fS')
  → (fP ≡ λ s q → fP' s (subst (λ v → Q (v s)) eqfS q))
  → _≡_ {_} {(S ◃ P) →ᶜ (T ◃ Q)} (fS ◃ fP) (fS' ◃ fP')
→ᶜ-≡-intro refl refl = refl

idᶜ : SP →ᶜ SP
idᶜ = id ◃ λ s → id

infixr 9 _∘ᶜ_
_∘ᶜ_ : TQ →ᶜ UV → SP →ᶜ TQ → SP →ᶜ UV
(g ◃ h) ∘ᶜ (g' ◃ h') = (g ∘ g') ◃ λ s → h' s ∘ h (g' s)

{- WM -}

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

sup⁻ : W SP → ⟦ SP ⟧ (W SP)
sup⁻ (sup (s , f)) = s , f

W₁ : SP →ᶜ TQ → W SP → W TQ
W₁ (g ◃ h) (sup (s , f)) = sup (g s , λ q → W₁ (g ◃ h) (f (h s q)))

{-
module _ (X : Set) (SP : Cont) (g : ⟦ SP ⟧ X → X) where

  foldW : W SP → X
  foldW (sup (s , f)) = g (s , foldW ∘ f)

  commuteW : (sf : ⟦ SP ⟧ (W SP)) → foldW (sup sf) ≡ g (⟦ SP ⟧₁ foldW sf)
  commuteW sf = refl

  !foldW : (foldW' : W SP → X)
    (commuteW' : (sf : ⟦ SP ⟧ (W SP)) → foldW' (sup sf) ≡ g (⟦ SP ⟧₁ foldW' sf))
    → (w : W SP) → foldW' w ≡ foldW w
  !foldW foldW' commuteW' (sup (s , f)) = trans (commuteW' (s , f))
    (cong g (Σ-≡ (refl , funExt λ a → !foldW foldW' commuteW' (f a))))
-}

{- 2nd Order Container -}

record 2Cont : Set₁ where
  inductive
  pattern
  constructor _◃_+_+_
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

variable H J SPPR TQQL : 2Cont

2⟦_⟧T : 2Cont → (Set → Set) → Set → Set
2⟦ S ◃ PX + PF + RF ⟧T F X
  = Σ[ s ∈ S ] (PX s → X × ((pF : PF s) → 2⟦ RF s pF ⟧T F X))

2⟦_⟧T₁ : (H : 2Cont) (F : Set → Set) → (X → Y) → 2⟦ H ⟧T F X → 2⟦ H ⟧T F Y
2⟦ S ◃ PX + PF + RF ⟧T₁ F g (s , f) =
  s , λ pX → let (x , h) = f pX in g x , λ pF → 2⟦ RF s pF ⟧T₁ F g (h pF)

Func : Set₁
Func = Σ[ F ∈ (Set → Set) ] (∀ {X Y} → (X → Y) → F X → F Y)

2⟦_⟧F : 2Cont → Func → Func
2⟦ H ⟧F SP = 2⟦ H ⟧T (SP .proj₁) , 2⟦ H ⟧T₁ (SP .proj₁)


2⟦_⟧S : (H : 2Cont) (TQ : Cont) → Set
2⟦ S ◃ PX + PF + RF ⟧S (T ◃ Q) = Σ[ s ∈ S ] ((pF : PF s) → Σ[ t ∈ T ] (Q t → 2⟦ RF s pF ⟧S (T ◃ Q)))

2⟦_⟧P : (H : 2Cont) (TQ : Cont) → 2⟦ H ⟧S TQ → Set
2⟦ S ◃ PX + PF + RF ⟧P (T ◃ Q) (s , f) =
  Σ[ pF ∈ PF s ] let (t , f') = f pF in
    Σ[ q ∈ Q t ] (2⟦ RF s pF ⟧P (T ◃ Q) (f' q) ⊎ PX s)

2⟦_⟧S' : (H : 2Cont) (TQ : Cont) → Set
2⟦ S ◃ PX + PF + RF ⟧S' (T ◃ Q) =
  Σ[ s ∈ S ] Σ[ ff ∈ (PF s → T) ] ((pF : PF s) → Q (ff pF) → 2⟦ RF s pF ⟧S (T ◃ Q)) 

2⟦_⟧ : 2Cont → Cont → Cont
2⟦ H ⟧ F = 2⟦ H ⟧S F ◃ 2⟦ H ⟧P F

2⟦_⟧S₁ : (H : 2Cont) → TQ →ᶜ UV → 2⟦ H ⟧S TQ → 2⟦ H ⟧S UV
2⟦ S ◃ PX + PF + RF ⟧S₁ (fT ◃ fQ) (s , f) =
  s , λ pF → let (t , f') = f pF in fT t , λ q → 2⟦ RF s pF ⟧S₁ (fT ◃ fQ) (f' (fQ t q))

2⟦_⟧P₁ : (H : 2Cont) (α : TQ →ᶜ UV) (s : 2⟦ H ⟧S TQ) → 2⟦ H ⟧P UV (2⟦ H ⟧S₁ α s) → 2⟦ H ⟧P TQ s
2⟦ S ◃ PX + PF + RF ⟧P₁ (fT ◃ fQ) (s , f) (pF , q , inj₁ p')
  = let (t , f') = f pF in pF , fQ t q , inj₁ (2⟦ RF s pF ⟧P₁ (fT ◃ fQ) (f' (fQ t q)) p')
2⟦ S ◃ PX + PF + RF ⟧P₁ (fT ◃ fQ) (s , f) (pF , q , inj₂ px)
  = let (t , f') = f pF in pF , fQ t q , inj₂ px

2⟦_⟧₁ : (H : 2Cont) → TQ →ᶜ UV → 2⟦ H ⟧ TQ →ᶜ 2⟦ H ⟧ UV
2⟦ H ⟧₁ α = 2⟦ H ⟧S₁ α ◃ 2⟦ H ⟧P₁ α

record _→²ᶜ_ (SPPR TQQL : 2Cont) : Set₁ where
  inductive
  constructor _◃_+_+_
  pattern
  open 2Cont SPPR
  open 2Cont TQQL renaming (S to T; PX to QX; PF to QF; RF to LF)
  field
    fS : S → T
    fPX : (s : S) → QX (fS s) → PX s
    fPF : (s : S) → QF (fS s) → PF s
    fRF : (s : S) (qF : QF (fS s)) → RF s (fPF s qF) →²ᶜ LF (fS s) qF

⟦_⟧→²ᶜ : H →²ᶜ J → (F : Cont) → 2⟦ H ⟧ F →ᶜ 2⟦ J ⟧ F
⟦ α ⟧→²ᶜ F = gS α F ◃ gP α F
  where
  gS : H →²ᶜ J → (F : Cont) → 2⟦ H ⟧S F → 2⟦ J ⟧S F
  gS {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (fS ◃ fPX + fPF + fRF) F (s , f)
    = fS s , λ qF → let (u , f') = f (fPF s qF) in u , λ v → gS (fRF s qF) F (f' v)

  gP : (α : H →²ᶜ J) (F : Cont) (s : 2⟦ H ⟧S F) → 2⟦ J ⟧P F (gS α F s) → 2⟦ H ⟧P F s
  gP {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (fS ◃ fPX + fPF + fRF) F (s , f) (qF , v , inj₁ pr)
    = fPF s qF , let (u , f') = f (fPF s qF) in v , inj₁ (gP (fRF s qF) F (f' v) pr)
  gP {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (fS ◃ fPX + fPF + fRF) F (s , f) (qF , v , inj₂ qX)
    = fPF s qF , v , inj₂ (fPX s qX)

{- 2W -}

-- record 2WS' (H H' : 2Cont) : Set

-- 2WP' : (H H' : 2Cont) → 2WS' H H' → Set

-- record 2WS' H H' where
--   constructor _,_
--   inductive
--   pattern
--   open 2Cont H'
--   field
--     s : S
--     f : (pF : PF s) → Σ[ t ∈ 2WS' H H ] (2WP' H H t → 2WS' H (RF s pF))

-- 2WP' H (S ◃ PX + PF + RF) (s , f) =
--   Σ[ pF ∈ PF s ] let (s' , f') = f pF in
--   Σ[ q ∈ 2WP' H H s' ] (2WP' H (RF s pF) (f' q) ⊎ PX s)

-- 2W : 2Cont → Cont
-- 2W H = 2WS' H H ◃ 2WP' H H

{-
2supS' : {H H' : 2Cont} → 2⟦ H' ⟧S (2W H) → 2WS' H H'
2supS' {H} {S ◃ PX + PF + RF} (s , f) = s , λ pF → let (s' , f') = f pF in s' , λ p' → 2supS' (f' p')

2supP' : {H H' : 2Cont} (s : 2⟦ H' ⟧S (2W H)) →
  2WP' H H' (2supS' s) → 2⟦ H' ⟧P (2W H) s
2supP' {H} {S ◃ PX + PF + RF} (s , f) (pF , p' , inj₁ pR) =
  let (s' , f') = f pF in pF , p' , inj₁ (2supP' (f' p') pR)
2supP' {H} {S ◃ PX + PF + RF} (s , f) (pF , p' , inj₂ pX) =
  pF , p' , inj₂ pX

2sup : {H : 2Cont} → 2⟦ H ⟧ (2W H) →ᶜ 2W H
2sup = 2supS' ◃ 2supP'

2supS'⁻ : {H H' : 2Cont} → 2WS' H H' → 2⟦ H' ⟧S (2W H)
2supS'⁻ {H} {S ◃ PX + PF + RF} (s , f) =
  s , λ pF → let (s' , f') = f pF in s' , λ p' → 2supS'⁻ (f' p')

2supP'⁻ : {H H' : 2Cont} (s : 2WS' H H')
  → 2⟦ H' ⟧P (2W H) (2supS'⁻ s) → 2WP' H H' s
2supP'⁻ {H} {S ◃ PX + PF + RF} (s , f) (pF , p' , inj₁ pr) =
  let (s' , f') = f pF in pF , p' , inj₁ (2supP'⁻ (f' p') pr)
2supP'⁻ {H} {S ◃ PX + PF + RF} (s , f) (pF , p' , inj₂ pX) =
  pF , p' , inj₂ pX

2sup⁻ : {H : 2Cont} → 2W H →ᶜ 2⟦ H ⟧ (2W H)
2sup⁻ = 2supS'⁻ ◃ 2supP'⁻
-}



{-
{-# TERMINATING #-}
fold2W : {H : 2Cont} {TQ : Cont}
  → 2⟦ H ⟧ TQ →ᶜ TQ
  → 2W H →ᶜ TQ
fold2W {H} α = α ∘ᶜ 2⟦ H ⟧₁ (fold2W {H} α) ∘ᶜ 2sup⁻ 
-}

{-
fold2WS' : {T : Set} {Q : T → Set} {H H' : 2Cont}
  → (2⟦ H ⟧ (T ◃ Q) →ᶜ (T ◃ Q))
  → (2⟦ H' ⟧ (T ◃ Q) →ᶜ (T ◃ Q))
  → 2WS' H H' → T

fold2WP' : {T : Set} {Q : T → Set} {H H' : 2Cont} 
  → (α : 2⟦ H ⟧ (T ◃ Q) →ᶜ (T ◃ Q))  
  → (α' : 2⟦ H' ⟧ (T ◃ Q) →ᶜ (T ◃ Q))
  → (s : 2WS' H H') → Q (fold2WS' α α' s) → 2WP' H H' s

fold2WS' {T} {Q} {H} {S ◃ PX + PF + RF} α (αS' ◃ αP') (s , f) = 
  αS' (s , λ pF → let (t , g) = f pF in fold2WS' α α t , λ q → 
  2⟦ RF s pF ⟧S₁ (fold2WS' α α ◃ fold2WP' α α) (2supS'⁻ (g (fold2WP' α α t q))))

fold2WP' = {!!}


fold2W : {TQ : Cont} {H : 2Cont} 
  → 2⟦ H ⟧ TQ →ᶜ TQ
  → 2W H →ᶜ TQ
fold2W α = fold2WS' α α ◃ fold2WP' α α
-}

-- record 2MS' (H H' : 2Cont) : Set

-- record 2MP' (H H' : 2Cont) (s : 2MS' H H') : Set

-- record 2MS' H H' where
--   coinductive
--   open 2Cont H'
--   field
--     out : Σ[ s ∈ S ] ((pF : PF s) → Σ[ t ∈ 2MS' H H ] (2MP' H H t → 2MS' H (RF s pF)))
-- open 2MS'    

-- record 2MP' H H' 2ms where
--   inductive
--   open 2Cont H'
--   field
--     out : let (s , f) = out 2ms in
--       Σ[ pF ∈ PF s ] let (s' , f') = f pF in
--       Σ[ q ∈ 2MP' H H s' ] (2MP' H (RF s pF) (f' q) ⊎ PX s)

-- 2MS : 2Cont → Set
-- 2MS H = 2MS' H H

-- 2MP : (H : 2Cont) → 2MS H → Set
-- 2MP H = 2MP' H H

-- 2M : 2Cont → Cont
-- 2M H = 2MS H ◃ 2MP H

---

{- Indexed containers and the W-type construction for 2Cont.

   The goal is to construct 2W H, the initial algebra of a 2Cont H, and
   prove its initiality. The direct IR definition of 2WS'/2WP' makes this
   hard: the induction hypothesis for initiality requires simultaneously
   handling all the sub-containers RF s pF, but with the IR definition
   there is no uniform way to state this.

   The solution is to use indexed containers ICont over U = Set.  An
   ICont I has shapes S : I → Set and positions P : (i : I) → S i → I → Set.
   Its action ⟦ C ⟧I on a family A : I → Set at index i is
     Σ[ s ∈ S i ] ((j : I) → P i s j → A j)
   The indexed W-type WI C : I → Set is initial for ⟦ C ⟧I.

   Crucially, the initiality proof for WI uses a single induction hypothesis
   that quantifies over ALL indices simultaneously:
     ∀ (X : I) → WI C X → A X
   This is exactly the right strength to handle the recursive sub-containers
   RF s pF that appear in the 2Cont definition — they correspond to other
   indices in the family.

   The translation appICont : 2Cont → ICont Set encodes a 2Cont H as an
   indexed container over Set, so that WI (appICont H) gives the shapes of
   2W H and the initiality of WI gives the fold for 2W H with the correct
   induction hypothesis.

   To define appICont H, we first factor the action of H on fibrations
   (Set → Set) via the Cont ↔ Fib equivalence:
     Cont→Fib (S ◃ P) X = Σ[ s ∈ S ] (P s ≡ X)   (fiber over X)
     Fib→Cont F         = Σ Set F ◃ proj₁           (total space with projection)
   These translate between families P : S → Set and display maps via the
   Grothendieck construction.  The action appFib H F = Cont→Fib (app H (Fib→Cont F))
   describes how H transforms fibrations.

   A shape of app H F splits into an F-free skeleton (appS') and F-inputs:
     appS'  — tree skeletons recording intermediate types A and continuations,
              but not the elements of F A at each branch
     appP'  — X-position type of a skeleton; F-free since it only depends
              on A and the continuations, not on the F-elements
     appFP  — for skeleton sh, appFP H sh Y is the set of locations where
              an element of F Y is needed to fill a branch
   The ICont Set encoding is then:
     SI X     = skeletons sh with appP' H sh ≡ X
     PI X s Y = F-query locations of type Y in skeleton s
   Providing (j : Set) → PI X s j → F j fills in all F-elements in the
   skeleton, recovering a full shape of app H (Fib→Cont F), giving the
   isomorphism ⟦ appICont H ⟧I F ≅ appFib H F.

   The same construction works for M-types (coinductive 2Cont algebras):
   replacing the indexed W-type WI with the indexed M-type MI (the final
   coalgebra of ⟦ appICont H ⟧I) gives the coinductive counterpart 2M H,
   and the initiality/finality proofs are structurally identical.

   Currently we use --type-in-type (Set : Set) to allow 2Cont : Set, so
   that U = Set can serve as the index type for ICont.  This is a cheat
   that should be eliminated by replacing U with a proper inductive-recursive
   universe: a type U of codes together with a decoding El : U → Set defined
   simultaneously by induction-recursion, large enough to contain codes for
   all the sets that arise in the construction (in particular, 2Cont itself
   and all the sets appS' H, appP' H sh, etc.).
-}

record ICont (I : Set) : Set where
  constructor _◃I_
  field
    S : I → Set
    P : (i : I) → S i → I → Set

⟦_⟧I : {I : Set} → ICont I → (I → Set) → I → Set
⟦ S ◃I P ⟧I A i = Σ[ s ∈ S i ] ((j : _) → P i s j → A j)

record WI {I} (C : ICont I) (i : I) : Set where
  inductive
  constructor supI
  open ICont C
  field
    shape : S i
    child : (j : I) → P i shape j → WI C j

U : Set -- should be replaced by an IR universe
U = Set

2Cont→ICont : 2Cont → ICont U
2Cont→ICont (S ◃ PX + PF + RF) = {!   !}

app : 2Cont → Cont → Cont
app H (T ◃ Q) = appS H ◃ appP H
  where
    appS : 2Cont → Set
    appS (S ◃ PX + PF + RF) =
      Σ[ s ∈ S ] ((pF : PF s) → Σ[ t ∈ T ] (Q t → appS (RF s pF)))

    appP : (H' : 2Cont) → appS H' → Set
    appP (S ◃ PX + PF + RF) (s , f) =
      Σ[ pF ∈ PF s ] let (t , f') = f pF in
      Σ[ q ∈ Q t ] (appP (RF s pF) (f' q) ⊎ PX s)


Fib : Set₁
Fib = Set → Set

Cont→Fib : Cont → Fib
Cont→Fib (S ◃ P) X = Σ[ s ∈ S ] (P s ≡ X)

Fib→Cont : Fib → Cont
Fib→Cont F = Σ Set F ◃ proj₁

appFib : 2Cont → Fib → Fib 
appFib H F = Cont→Fib (app H (Fib→Cont F))

appICont : 2Cont → ICont Set
appICont H = SI ◃I PI
  {- such that ⟦ appICont H ⟧I ≅ appFib H -}
  where
    appS' : 2Cont → Set
    appS' (S ◃ PX + PF + RF) =
      Σ[ s ∈ S ] ((pF : PF s) → Σ[ A ∈ Set ] (A → appS' (RF s pF)))

    appP' : (H' : 2Cont) → appS' H' → Set
    appP' (S ◃ PX + PF + RF) (s , g) =
      Σ[ pF ∈ PF s ] Σ[ a ∈ proj₁ (g pF) ] (appP' (RF s pF) (proj₂ (g pF) a) ⊎ PX s)

    appFP : (H' : 2Cont) → appS' H' → Set → Set
    appFP (S ◃ PX + PF + RF) (s , g) Y =
      Σ[ pF ∈ PF s ] (Y ≡ proj₁ (g pF) ⊎ Σ[ a ∈ proj₁ (g pF) ] appFP (RF s pF) (proj₂ (g pF) a) Y)

    SI : Set → Set
    SI X = Σ[ sh ∈ appS' H ] (appP' H sh ≡ X)

    PI : (X : Set) → SI X → Set → Set
    PI _ (sh , _) Y = appFP H sh Y

2W : 2Cont → Cont
2W H = Fib→Cont (WI (appICont H))

record MI {I} (C : ICont I) (i : I) : Set where
  coinductive
  constructor supI
  open ICont C
  field
    shape : S i
    child : (j : I) → P i shape j → WI C j

2M : 2Cont → Cont
2M H = Fib→Cont (MI (appICont H))