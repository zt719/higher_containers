module Data.2W.Properties where

open import Level
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning  
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
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
         → (s : S) → (Q (f s) → P s) ≅ (Q (f′ s) → P s)
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
-- 2sup ∘ᶜ 2sup⁻ ≡ idᶜ

module 2sup∘ᶜ2sup⁻≡idᶜ {H : 2Cont} where

  onS : {H′ : 2Cont}
        (s : 2WS-d H′ H)
        → 2supS-d (2supS⁻-d s) ≅ s
  onS {S ◃ PX + PF + RF} (mk s f) =
    cong (mk s) (funExt λ pF →
      let (t , g) = f pF in
        cong (t ,_) (funExt λ q →
          onS {RF s pF} (g q)))
          
  posX-inj : {H′ : 2Cont} (open 2Cont H′)
             {ws : 2WS-d H′ H} (open 2WS-d ws)
             {pX : PX s}
             {ws′ : 2WS-d H′ H} (open 2WS-d ws′ renaming (s to s′; f to f′))
             {pX′ : PX s′}
             → ws ≅ ws′
             → _≅_ {A = 2WP-d H′ H ws} (posX pX) {B = 2WP-d H′ H ws′} (posX pX′)
             → pX ≅ pX′
  posX-inj refl refl = refl

  posF-inj : {H′ : 2Cont} (open 2Cont H′)
             {ws : 2WS-d H′ H} (open 2WS-d ws)
             {pF : PF s}
             → let (t , g) = f pF in
             {q : 2WP-d H H t}
             {rp : 2WP-d (RF s pF) H (g q)}
             {ws′ : 2WS-d H′ H} (open 2WS-d ws′ renaming (s to s′; f to f′))
             {pF′ : PF s′}
             → let (t′ , g′) = f′ pF′ in
             {q′ : 2WP-d H H t′}
             {rp′ : 2WP-d (RF s′ pF′) H (g′ q′)}
             → ws ≅ ws′
             → _≅_ {A = 2WP-d H′ H ws} (posF (pF , q , rp))
                   {B = 2WP-d H′ H ws′} (posF (pF′ , q′ , rp′))
             → pF ≅ pF′ × q ≅ q′ × rp ≅ rp′
  posF-inj refl refl = refl , refl , refl

  posX≇posF : {H′ : 2Cont} (open 2Cont H′)
              {ws : 2WS-d H′ H} (open 2WS-d ws)
              {pX : PX s}
              {ws′ : 2WS-d H′ H} (open 2WS-d ws′ renaming (s to s′; f to f′))
              {r : Σ[ pF ∈ PF s′ ] let (t , g) = f′ pF in
                   Σ[ q ∈ 2WP-d H H t ] 2WP-d (RF s′ pF) H (g q)}
              → ws ≅ ws′
              → _≅_ {A = 2WP-d H′ H ws} (posX pX) {B = 2WP-d H′ H ws′} (posF r)
              → ⊥
  posX≇posF refl ()

  posF≇posX : {H′ : 2Cont} (open 2Cont H′)
              {ws : 2WS-d H′ H} (open 2WS-d ws)
              {r : Σ[ pF ∈ PF s ] let (t , g) = f pF in
                   Σ[ q ∈ 2WP-d H H t ] 2WP-d (RF s pF) H (g q)}
              {ws′ : 2WS-d H′ H} (open 2WS-d ws′ renaming (s to s′))
              {pX : PX s′}
              → ws ≅ ws′
              → _≅_ {A = 2WP-d H′ H ws} (posF r) {B = 2WP-d H′ H ws′} (posX pX)
              → ⊥
  posF≇posX refl ()

  onP : {H′ : 2Cont}
        (s : 2WS-d H′ H)
        (q : 2WP-d H′ H (2supS-d (2supS⁻-d s)))
        (q′ : 2WP-d H′ H s)
        (q≅q′ : q ≅ q′)
        → 2supP⁻-d s (2supP-d (2supS⁻-d s) q) ≅ q′
  onP {H′@(S ◃ PX + PF + RF)} (ws@(mk s f)) (posX x) (posX x₁) q≅q′ =
    cong posX (posX-inj (onS ws) q≅q′)
  onP {H′@(S ◃ PX + PF + RF)} (ws@(mk s f)) (posX x) (posF x₁) q≅q′ =
    ⊥-elim (posX≇posF (onS ws) q≅q′)
  onP {H′@(S ◃ PX + PF + RF)} (ws@(mk s f)) (posF x) (posX x₁) q≅q′ =
    ⊥-elim (posF≇posX (onS ws) q≅q′)
  onP {H′@(S ◃ PX + PF + RF)} (ws@(mk s f)) (posF (pF , q , rp)) (posF (pF′ , q′ , rp′)) q≅q′
    with posF-inj (onS ws) q≅q′
  ... | refl , refl , rp≅rp′ = let (t , g) = f pF in
    cong (λ r → posF (pF , q , r)) (onP {RF s pF} (g q) rp rp′ rp≅rp′)

  2sup-d∘ᶜ2sup⁻-d : {H′ : 2Cont} → 2sup-d {H} {H′} ∘ᶜ 2sup⁻-d ≅ idᶜ
  2sup-d∘ᶜ2sup⁻-d {H′} = →ᶜ-≅-go onS onP

  2sup∘ᶜ2sup⁻ : 2sup ∘ᶜ 2sup⁻ ≅ idᶜ
  2sup∘ᶜ2sup⁻ = 2sup-d∘ᶜ2sup⁻-d

  oneway : 2sup {H} ∘ᶜ 2sup⁻ ≡ idᶜ
  oneway = ≅-to-≡ 2sup∘ᶜ2sup⁻

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

  aux∘ᶜ2sup-d : {H′ : 2Cont} → aux α ∘ᶜ 2sup-d ≅ app₁ H′ (fold2W α)
  aux∘ᶜ2sup-d {H′} = →ᶜ-≅-go onS onP

  aux∘ᶜ2sup : aux α ∘ᶜ 2sup-d ≅ app₁ H (fold2W α)
  aux∘ᶜ2sup = aux∘ᶜ2sup-d {H} 
  
  comm : fold2W α ∘ᶜ 2sup ≅ α ∘ᶜ app₁ H (fold2W α)
  comm = cong (α ∘ᶜ_) aux∘ᶜ2sup

------------------------------------------------------------------------
-- Uniqueness

-- pointwise extraction from an equality of morphisms
module _
  {SP TQ : Cont}
  {α β : SP →ᶜ TQ}
  where

  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  open _→ᶜ_ α renaming (fS to αS; fP to αP)
  open _→ᶜ_ β renaming (fS to βS; fP to βP)

  fS-≅ : α ≅ β
         → (s : S)
         → αS s ≅ βS s
  fS-≅ refl s = refl

  fP-≅ : α ≅ β
         → (s : S)
         (q : Q (αS s)) (q′ : Q (βS s))
         → q ≅ q′
         → αP s q ≅ βP s q′
  fP-≅ refl s q q′ refl = refl

pairQ : {T : Set} {Q : T → Set} {X : Set} {t t′ : T}
        {h : Q t → X} {h′ : Q t′ → X}
        → t ≅ t′
        → ((q : Q t) (q′ : Q t′) → q ≅ q′ → h q ≅ h′ q′)
        → _≅_ {A = Σ T (λ t → Q t → X)} (t , h)
              {B = Σ T (λ t → Q t → X)} (t′ , h′)
pairQ {t = t} refl k = cong (t ,_) (funExt λ q → k q q refl)

-- congruence for dependent binary application
app-≅ : {A : Set} {B C : A → Set} (f : (a : A) → B a → C a)
        {a a′ : A} {b : B a} {b′ : B a′}
      → a ≅ a′ → b ≅ b′ → f a b ≅ f a′ b′
app-≅ f refl refl = refl

cast : {A B : Set} → A ≅ B → A → B
cast refl a = a

cast-≅ : {A B : Set} (e : A ≅ B) (a : A) → cast e a ≅ a
cast-≅ refl a = refl

appP-tail : (H : 2Cont) (F : Cont) → appS H F → Set
appP-tail (S ◃ PX + PF + RF) (T ◃ Q) (s , f) =
  Σ[ pF ∈ PF s ] let (t , g) = f pF in
    Σ[ q ∈ Q t ] appP (RF s pF) (T ◃ Q) (g q)

inj₂-Σ₃-inj : {L A A′ : Set}
              {B : A → Set} {B′ : A′ → Set}
              {C : (a : A) → B a → Set} {C′ : (a : A′) → B′ a → Set}
              {a : A} {b : B a} {c : C a b}
              {a′ : A′} {b′ : B′ a′} {c′ : C′ a′ b′}
            → A ≅ A′ → B ≅ B′ → C ≅ C′
            → _≅_ {A = L ⊎ Σ A (λ x → Σ (B x) (C x))} (inj₂ (a , b , c))
                  {B = L ⊎ Σ A′ (λ x → Σ (B′ x) (C′ x))} (inj₂ (a′ , b′ , c′))
            → a ≅ a′ × b ≅ b′ × c ≅ c′
inj₂-Σ₃-inj refl refl refl refl = refl , refl , refl

module Uniqueness
  {H : 2Cont}
  {TQ : Cont}
  (α : app H TQ →ᶜ TQ)
  (fold2W′ : 2W H →ᶜ TQ)
  (comm′ : fold2W′ ∘ᶜ 2sup ≅ α ∘ᶜ app₁ H fold2W′) where

  open 2sup∘ᶜ2sup⁻≡idᶜ
  open Cont TQ renaming (S to T; P to Q)
  open _→ᶜ_ α  renaming (fS to αS; fP to αP)


  fold2WS′ : 2WS H → T
  fold2WS′ = fold2W′ ._→ᶜ_.fS

  fold2WP′ : (s : 2WS H) → Q (fold2WS′ s) → 2WP H s
  fold2WP′ = fold2W′ ._→ᶜ_.fP

  commS′ : (s : appS H (2W H))
           → fold2WS′ (2supS s) ≅ αS (appS₁ H fold2W′ s)
  commS′ = fS-≅ comm′

  commP′ : (s : appS H (2W H))
           (q : Q (fold2WS′ (2supS s)))
           (q′ : Q (αS (appS₁ H fold2W′ s)))
           → q ≅ q′
           → 2supP s (fold2WP′ (2supS s) q)
           ≅ appP₁ H fold2W′ s (αP (appS₁ H fold2W′ s) q′)
  commP′ = fP-≅ comm′




  onAuxS : {H′ : 2Cont} (s : 2WS-d H′ H)
           → auxS α s ≅ appS₁ H′ fold2W′ (2supS⁻-d s)

  onAuxP : {H′ : 2Cont} (s : 2WS-d H′ H)
           (q : appP H′ TQ (auxS α s))
           (q′  : appP H′ TQ (appS₁ H′ fold2W′ (2supS⁻-d s)))
           → q ≅ q′
           → auxP α s q ≅ 2supP⁻-d s (appP₁ H′ fold2W′ (2supS⁻-d s) q′)

  onFold2WS : (s : 2WS H) → fold2WS α s ≅ fold2WS′ s

  onFold2WP : (s : 2WS H)
              (q : Q (fold2WS α s))
              (q′ : Q (fold2WS′ s))
              → q ≅ q′
              → fold2WP α s q ≅ fold2WP′ s q′

  onAuxS {S ◃ PX + PF + Q′F} (mk s f) =
    cong (s ,_) (funExt λ pF →
      let (t , g) = f pF in
        pairQ (onFold2WS t) λ q q′ q≅q′ →
    begin
      auxS α (g (fold2WP α t q))
    ≅⟨ cong (λ p → auxS α (g p)) (onFold2WP t q q′ q≅q′) ⟩
      auxS α (g (fold2WP′ t q′))
    ≅⟨ onAuxS {Q′F s pF} (g (fold2WP′ t q′)) ⟩
      appS₁ (Q′F s pF) fold2W′ (2supS⁻-d (g (fold2WP′ t q′)))
    ∎)

  onFold2WS s =
    begin
      fold2WS α s
    ≡⟨⟩
      αS (auxS α s)
    ≅⟨ cong αS (onAuxS s) ⟩
      αS (appS₁ H fold2W′ (2supS⁻-d s))
    ≅⟨ sym (commS′ (2supS⁻-d s)) ⟩
      fold2WS′ (2supS (2supS⁻-d s))
    ≅⟨ cong fold2WS′ (onS s) ⟩
      fold2WS′ s
    ∎

  onFold2WP s q q₁ q≅q₁ =
    begin
      fold2WP α s q
    ≡⟨⟩
      auxP α s (αP (auxS α s) q)
    ≅⟨ onAuxP s (αP (auxS α s) q)
       (αP (appS₁ H fold2W′ (2supS⁻-d s)) q₂) (app-≅ αP (onAuxS s) (sym q₂≅q)) ⟩
      2supP⁻-d s (appP₁ H fold2W′ (2supS⁻-d s) (αP (appS₁ H fold2W′ (2supS⁻-d s)) q₂))
    ≅⟨ cong (2supP⁻-d s) (sym (commP′ (2supS⁻-d s) q₃ q₂ q₃≅q₂)) ⟩
      2supP⁻-d s (2supP (2supS⁻-d s) (fold2WP′ (2supS (2supS⁻-d s)) q₃))
    ≅⟨ onP s (fold2WP′ (2supS (2supS⁻-d s)) q₃) (fold2WP′ s q₁) (app-≅ fold2WP′ (onS s) q₃≅q₁) ⟩
      fold2WP′ s q₁
    ∎
    where
      q₂ : Q (αS (appS₁ H fold2W′ (2supS⁻-d s)))
      q₂ = cast (cong (λ y → Q (αS y)) (onAuxS s)) q
      
      q₂≅q : q₂ ≅ q
      q₂≅q = cast-≅ _ q

      q₃ : Q (fold2WS′ (2supS (2supS⁻-d s)))
      q₃ = cast (cong (λ v → Q (fold2WS′ v)) (sym (onS s))) q₁
      
      q₃≅q₁ : q₃ ≅ q₁
      q₃≅q₁ = cast-≅ _ q₁

      q₃≅q₂ : q₃ ≅ q₂
      q₃≅q₂ = trans q₃≅q₁ (trans (sym q≅q₁) (sym q₂≅q))

  -- A ≅ A′ is just `refl` (both are PF s)

  eqB : {S : Set} {PX PF : S → Set} {RF : (s : S) → PF s → 2Cont} (s : S)
        (f : (pF : PF s) → Σ[ t ∈ 2WS-d H H ] (2WP-d H H t → 2WS-d (RF s pF) H))
      → (λ pF → Q (fold2WS α (proj₁ (f pF))))
      ≅ (λ pF → Q (fold2WS′ (proj₁ (f pF))))
  eqB s f = funExt (λ pF → cong Q (onFold2WS (proj₁ (f pF))))

  eqC : {S : Set} {PX PF : S → Set} {RF : (s : S) → PF s → 2Cont} (s : S)
        (f : (pF : PF s) → Σ[ t ∈ 2WS-d H H ] (2WP-d H H t → 2WS-d (RF s pF) H))
      → (λ pF q → appP (RF s pF) TQ
                    (auxS α (proj₂ (f pF) (fold2WP α (proj₁ (f pF)) q))))
      ≅ (λ pF q → appP (RF s pF) TQ
                    (appS₁ (RF s pF) fold2W′
                      (2supS⁻-d (proj₂ (f pF) (fold2WP′ (proj₁ (f pF)) q)))))
  eqC {RF = RF} s f =
    ext (λ pF → cong (λ fold → (Q (fold (proj₁ (f pF)))) → Set) (funExt onFold2WS))
         (λ pF → Π-≅ (cong Q (onFold2WS (proj₁ (f pF)))) λ q q′ e →
            cong (appP (RF s pF) TQ)
              (trans (cong (λ p → auxS α (proj₂ (f pF) p))
                           (onFold2WP (proj₁ (f pF)) q q′ e))
                     (onAuxS {RF s pF} (proj₂ (f pF) (fold2WP′ (proj₁ (f pF)) q′)))))
                     where
    Π-≅ : {X Y : Set} {Z : X → Set} {Z′ : Y → Set}
        → X ≅ Y
        → ((x : X) (y : Y) → x ≅ y → Z x ≅ Z′ y)
        → Z ≅ Z′
    Π-≅ refl h = funExt (λ x → h x x refl)

  inj₂-eqs : {H′ : 2Cont} (open 2Cont H′)
             (s : S)
             (f : (pF : PF s) → Σ[ t ∈ 2WS-d H H ]
                                  (2WP-d H H t → 2WS-d (RF s pF) H))
             (pF′ pF : PF s)
             (q′ : Q (fold2WS α (proj₁ (f pF′))))
             (q  : Q (fold2WS′  (proj₁ (f pF))))
             (rp′ : appP (RF s pF′) TQ
                      (auxS α (proj₂ (f pF′) (fold2WP α (proj₁ (f pF′)) q′))))
             (rp  : appP (RF s pF) TQ
                      (appS₁ (RF s pF) fold2W′
                        (2supS⁻-d (proj₂ (f pF) (fold2WP′ (proj₁ (f pF)) q)))))
           → _≅_ {A = appP (S ◃ PX + PF + RF) TQ (auxS α (mk s f))}
                 (inj₂ (pF′ , q′ , rp′))
                 {B = appP (S ◃ PX + PF + RF) TQ
                        (appS₁ (S ◃ PX + PF + RF) fold2W′ (2supS⁻-d (mk s f)))}
                 (inj₂ (pF , q , rp))
           → pF′ ≅ pF × q′ ≅ q × rp′ ≅ rp
  inj₂-eqs s f pF′ pF q′ q rp′ rp e =
    inj₂-Σ₃-inj refl (eqB s f) (eqC s f) e

  onAuxP {H′@(S ◃ PX + PF + RF)} w@(mk s f) (inj₁ _) (inj₁ _) e =
    cong posX (inj₁-inj (cong (appP-tail H′ TQ) (onAuxS w)) e)

  onAuxP {H′@(S ◃ PX + PF + RF)} w@(mk s f) (inj₁ _) (inj₂ _) e =
    ⊥-elim (inj₁≇inj₂ (cong (appP-tail H′ TQ) (onAuxS w)) e)

  onAuxP {H′@(S ◃ PX + PF + RF)} w@(mk s f) (inj₂ _) (inj₁ _) e =
    ⊥-elim (inj₂≇inj₁ (cong (appP-tail H′ TQ) (onAuxS w)) e)

  onAuxP {H′@(S ◃ PX + PF + RF)} w@(mk s f)
         (inj₂ (pF′ , q′ , rp′)) (inj₂ (pF , q , rp)) e = {!!}
  
           


  
  uniq : fold2W α ≅ fold2W′
  uniq = →ᶜ-≅-go onFold2WS onFold2WP
