module Data.2W.Lambeks where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; refl; ≅-to-≡; cong)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Prelude using (funExt; ext)
open import Data.Cont
open import Data.2Cont
open import Data.2W.Base

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
-- Lambek's lemma

module 2sup∘ᶜ2sup⁻≅idᶜ {H : 2Cont} where

  2supS⁻-d : {H' : 2Cont} → 2WS-d H' H → appS H' (2W H)
  2supS⁻-d {S ◃ PX + PF + RF} (mk s f) = s , λ pF → let (t , g) = f pF in t , λ q → 2supS⁻-d (g q)

  2supP⁻-d : {H' : 2Cont} (s : 2WS-d H' H) → appP H' (2W H) (2supS⁻-d s) → 2WP-d H' H s
  2supP⁻-d {S ◃ PX + PF + RF} (mk s f) (inj₁ pX) = posX pX
  2supP⁻-d {S ◃ PX + PF + RF} (mk s f) (inj₂ (pF , q , rp)) =
    posF (pF , q , let (t , g) = f pF in 2supP⁻-d {RF s pF} (g q) rp)

  2sup⁻-d : {H' : 2Cont} → 2W-d H' H →ᶜ app H' (2W H)
  2sup⁻-d = 2supS⁻-d ◃ 2supP⁻-d

  2sup⁻ : 2W H →ᶜ app H (2W H)
  2sup⁻ = 2sup⁻-d

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

-- TODO: Another direction
