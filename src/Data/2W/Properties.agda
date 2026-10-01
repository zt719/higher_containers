module Data.2W.Properties where

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; ≅-to-≡; cong)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function
open import Data.Cont
open import Data.2Cont
open import Data.2W.Base
open import Prelude using (funExt; ext)

private
  variable
    ℓ ℓ′ ℓ″ : Level

------------------------------------------------------------------------
-- Equality of Hom

→ᶜ-≅ :
  {SP TQ : Cont}
  (open Cont SP)
  (open Cont TQ renaming (S to T; P to Q))
  {f f′ : S → T}
  {g  : (s : S) → Q (f s)  → P s}
  {g′ : (s : S) → Q (f′ s) → P s}
  (eS : f ≅ f′)
  (eP : g ≅ g′)
  → _≅_ {A = SP →ᶜ TQ} (f ◃ g) {B = SP →ᶜ TQ} (f′ ◃ g′)
→ᶜ-≅ refl refl = refl

→ᶜ-≅-go : {SP TQ : Cont} (open Cont SP)
          (open Cont TQ renaming (S to T; P to Q))
          {f f′ : S → T}
          {g  : (s : S) → Q (f s)  → P s}
          {g′ : (s : S) → Q (f′ s) → P s}
          (eS-go : (s : S) → f s ≅ f′ s)
          (eP-go : (s : S) (q : Q (f s)) (q' : Q (f′ s))
            → q ≅ q' → g s q ≅ g′ s q')
          → _≅_ {A = SP →ᶜ TQ} (f ◃ g) {B = SP →ᶜ TQ} (f′ ◃ g′)
→ᶜ-≅-go {SP} {TQ} {f} {f′} {g} {g′} eS-go eP-go = →ᶜ-≅ eS eP
  where
    open Cont SP
    open Cont TQ renaming (S to T; P to Q)

    eS : f ≅ f′
    eS = funExt eS-go

    lem₁ : {f f′ : S → T}
         → f ≅ f′
         → (s : S) → (Q (f s) → P s) ≡ (Q (f′ s) → P s)
    lem₁ refl s = refl

    lem₂ : {f f′ : S → T}
          → f ≅ f′
          → (s : S)
          {a : Q (f s) → P s}
          {b : Q (f′ s) → P s}
          → ((q : Q (f s)) (q′ : Q (f′ s))
            → q ≅ q′ → a q ≅ b q′)
          → a ≅ b
    lem₂ refl s h = funExt (λ x → h x x refl)

    eP : g ≅ g′
    eP = ext (λ s → lem₁ eS s) (λ s → lem₂ eS s (eP-go s))

------------------------------------------------------------------------
-- Folding commutes

-- Some lemmas

inj₁-inj : {A : Set ℓ} {B B′ : Set ℓ′} {x y : A}
         → B ≅ B′
         → _≅_ {A = A ⊎ B} (inj₁ x) {B = A ⊎ B′} (inj₁ y)
         → x ≅ y
inj₁-inj refl refl = refl

inj₂-inj : {A : Set ℓ} {B B′ : Set ℓ′} {x : B} {y : B′}
         → B ≅ B′
         → _≅_ {A = A ⊎ B} (inj₂ x) {B = A ⊎ B′} (inj₂ y)
         → x ≅ y
inj₂-inj refl refl = refl

inj₁≇inj₂ : {A : Set ℓ} {B B′ : Set ℓ′} {x : A} {y : B′}
          → B ≅ B′
          → _≅_ {A = A ⊎ B} (inj₁ x) {B = A ⊎ B′} (inj₂ y)
          → ⊥
inj₁≇inj₂ refl ()

inj₂≇inj₁ : {A : Set ℓ} {B B′ : Set ℓ′} {x : B} {y : A}
          → B ≅ B′
          → _≅_ {A = A ⊎ B} (inj₂ x) {B = A ⊎ B′} (inj₁ y)
          → ⊥
inj₂≇inj₁ refl ()

Σ₃-inj : {A A′ : Set ℓ}
         {B  : A  → Set ℓ′} {B′ : A′ → Set ℓ′}
         {C  : (a : A)  → B a   → Set ℓ″}
         {C′ : (a : A′) → B′ a  → Set ℓ″}
         {a : A} {b : B a} {c : C a b}
         {a′ : A′} {b′ : B′ a′} {c′ : C′ a′ b′}
         → A ≅ A′
         → B ≅ B′
         → C ≅ C′
         → _≅_ {A = Σ A (λ x → Σ (B x) (C x))} (a , b , c)
               {B = Σ A′ (λ x → Σ (B′ x) (C′ x))} (a′ , b′ , c′)
       → a ≅ a′ × b ≅ b′ × c ≅ c′
Σ₃-inj refl refl refl refl = refl , refl , refl

-- Proof

module Commutes
  {H : 2Cont}
  {TQ : Cont}
  (α : app H TQ →ᶜ TQ)
  where

  open Cont TQ renaming (S to T; P to Q)

  onS : {H′ : 2Cont}
        (s : appS H′ (2W H))
        → auxS α (2supS-d s) ≅ appS₁ H′ (fold2W α) s
  onS {S ◃ PX + PF + RF} (s , f) =
    cong (s ,_) (funExt λ pF →
      let (t , g) = f pF in
        cong (fold2WS α t ,_) (funExt λ q →
          onS (g (fold2WP α t q))))

  lem : {H′ : 2Cont} (open 2Cont H′)
        (s : S)
        (f : (pF : PF s) → Σ[ t ∈ 2WS-d H H ] (2WP-d H H t → appS (RF s pF) (2W H)))
        → (Σ[ pF ∈ PF s ] let (t , g) = f pF in
            Σ[ q ∈ Q (fold2WS α t) ] appP (RF s pF) TQ (auxS α (2supS-d (g (fold2WP α t q)))))
        ≅ (Σ[ pF ∈ PF s ] let (t , g) = f pF in
            Σ[ q ∈ Q (fold2WS α t) ]
              appP (RF s pF) TQ (appS₁ (RF s pF) (fold2W α) (g (fold2WP α t q))))
  lem {S ◃ PX + PF + RF} s f =
    cong (Σ (PF s)) (funExt λ pF → let (t , g) = f pF in
      cong (Σ (Q (fold2WS α t))) (funExt λ q →
        cong (appP (RF s pF) TQ) (onS {RF s pF} (g (fold2WP α t q)))))

  onP : {H′ : 2Cont}
        (s : appS H′ (2W H))
        (q : appP H′ TQ (auxS α (2supS-d s)))
        (q′ : appP H′ TQ (appS₁ H′ (fold2W α) s))
        → q ≅ q′
        → 2supP-d s (auxP α (2supS-d s) q) ≅ appP₁ H′ (fold2W α) s q′
  onP {H′@(S ◃ PX + PF + RF)} (s , f) (inj₁ _) (inj₁ _) q≅q′ =
    cong inj₁ (inj₁-inj (lem {H′} s f) q≅q′)
  onP {H′@(S ◃ PX + PF + RF)} (s , f) (inj₁ _) (inj₂ _) q≅q′ =
    ⊥-elim (inj₁≇inj₂ (lem {H′} s f) q≅q′)
  onP {H′@(S ◃ PX + PF + RF)} (s , f) (inj₂ _) (inj₁ _) q≅q′ =
    ⊥-elim ((inj₂≇inj₁ (lem {H′} s f) q≅q′))
  onP {H′@(S ◃ PX + PF + RF)} (s , f) (inj₂ (pF , q , rp)) (inj₂ (pF′ , q′ , rp′)) q≅q′
    with Σ₃-inj refl refl
         (funExt λ pF → funExt λ q → let (t , g) = f pF in
           cong (appP (RF s pF) TQ) (onS (g (fold2WP α (t) q))))
         (inj₂-inj (lem {H′} s f) q≅q′)
  ... | refl , refl , rp≅rp′ = let (t , g) = f pF in
    cong (λ r → inj₂ (pF , fold2WP α t q , r))
      (onP {RF s pF} (g (fold2WP α t q)) rp rp′ rp≅rp′)
  
  aux∘ᶜ2sup-d : {H′ : 2Cont}
    → aux α ∘ᶜ 2sup-d ≅ app₁ H′ (fold2W α)
  aux∘ᶜ2sup-d {H′} = →ᶜ-≅-go onS onP
  
  commute : fold2W α ∘ᶜ 2sup ≅ α ∘ᶜ app₁ H (fold2W α)
  commute = cong (α ∘ᶜ_) aux∘ᶜ2sup-d
