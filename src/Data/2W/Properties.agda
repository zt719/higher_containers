module Data.2W.Properties where

open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties
open ≡-Reasoning
open import Function.Base
open import Data.Cont
open import Data.2Cont
open import Data.2W.Base
open import Data.2W.Folding
open import Prelude

------------------------------------------------------------------------
-- Lambek's lemma

module _ {H : 2Cont} where

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


private
  variable
    ℓ ℓ′ ℓ″ : Level

uip : {A : Set ℓ}
  {x y : A}
  (p q : x ≡ y)
  → p ≡ q
uip refl refl = refl

subst-cast : {A : Set ℓ} {B : A → Set ℓ′} {x y : A}
             (p q : x ≡ y) (b : B x) →
             subst B p b ≡ subst B q b
subst-cast {B = B} p q b = cong (λ r → subst B r b) (uip p q)


Σ≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
  (p : a₁ ≡ a₂) → 
  subst B p b₁ ≡ b₂ → 
  (a₁ , b₁) ≡ (a₂ , b₂)
Σ≡ refl refl = refl

-- push subst under a Π
subst-Π :
  {A : Set ℓ}
  {B : Set ℓ′}
  {C : A → B → Set ℓ″}
  {x y : A}
  (f : (u : B) → C x u)
  (p : x ≡ y)
  {b : B} →
  subst (λ x → (s : B) → C x s) p f b ≡ subst (λ x → C x b) p (f b)
subst-Π f refl = refl

-- subst on the domain of a function type (contravariance ⇒ sym)
subst-dom :
  {A : Set ℓ}
  {B : A → Set ℓ′}
  {C : Set ℓ″}
  {x y : A} {u : B y}
  (f : B x → C)  
  (p : x ≡ y) → 
  subst (λ x → B x → C) p f u ≡ f (subst B (sym p) u)
subst-dom f refl = refl

→ᶜ-≡ :
  {SP TQ : Cont}
  (open Cont SP)
  (open Cont TQ renaming (S to T; P to Q))
  {f f′ : S → T}
  {g  : (s : S) → Q (f s)  → P s}
  {g′ : (s : S) → Q (f′ s) → P s}
  (hS : (s : S) → f s ≡ f′ s)
  (hP : (s : S) (q : Q (f s)) →
    g s q ≡ g′ s (subst Q (hS s) q)) → 
  _≡_ {A = SP →ᶜ TQ} (f ◃ g) (f′ ◃ g′)
→ᶜ-≡ {S ◃ P} {T ◃ Q} {f} {f′} {g} {g′} hS hP = dcong₂ _◃_ eS eP
  where
    eS : f ≡ f′
    eS = funExt hS

    eP : subst (λ f → (s : S) → Q (f s) → P s) eS g ≡ g′
    eP = funExt λ s → funExt λ q → 
      begin
        subst (λ f → (s : S) → Q (f s) → P s) eS g s q
      ≡⟨ cong (_$ q) (subst-Π {C = λ f s → Q (f s) → P s} g eS) ⟩ 
        subst (λ f → Q (f s) → P s) eS (g s) q
      ≡⟨ subst-dom (g s) eS ⟩
        g s (subst (λ f → Q (f s)) (sym eS) q)
      ≡⟨ cong (g s) (subst-∘ (sym eS)) ⟩
        g s (subst Q (cong (_$ s) (sym eS)) q)
      ≡⟨ cong (λ e → g s (subst Q e q)) (trans (sym (sym-cong (funExt hS))) (cong sym (funExt-β hS s))) ⟩
        g s (subst Q (sym (hS s)) q)
      ≡⟨ hP s (subst Q (sym (hS s)) q) ⟩
        g′ s (subst Q (hS s) (subst Q (sym (hS s)) q))
      ≡⟨ cong (g′ s) (subst-subst-sym (hS s)) ⟩
        g′ s q
      ∎

module 2sup∘ᶜ2sup⁻≡idᶜ {H : 2Cont} where

  onS :
    {H′ : 2Cont}
    (s : 2WS-d H′ H) →
    2supS-d (2supS⁻-d s) ≡ s
  onS {S ◃ PX + PF + RF} (mk s f) =
    cong (mk s) (funExt λ pF →
      let (t , g) = f pF in
        cong (t ,_) (funExt λ q →
          onS (g q)))

  subst-posX :
    {H′ : 2Cont} (open 2Cont H′)
    {ws ws′ : 2WS-d H′ H} (open 2WS-d ws)
    (eq : ws ≡ ws′)
    (pX : PX s) →
    let s-eq = cong 2WS-d.s eq in
    subst (2WP-d H′ H) eq (posX pX) ≡ posX (subst PX s-eq pX)
  subst-posX refl pX = refl

  subst-PX :
    {H′ : 2Cont} (open 2Cont H′)
    {ws ws′ : 2WS-d H′ H} (open 2WS-d ws)
    (eq : ws ≡ ws′)
    (pX : PX s) →
    subst PX {!!} pX ≡ pX    
  subst-PX refl pX = {!!}

  t-eq :
    {H′ : 2Cont} (open 2Cont H′)
    {ws ws′ : 2WS-d H′ H}
    (eqws : ws ≡ ws′)
    (pF : PF (2WS-d.s ws))
    → proj₁ (2WS-d.f ws pF)
      ≡ proj₁ (2WS-d.f ws′ (subst PF (cong 2WS-d.s eqws) pF))
  t-eq refl pF = refl

  r-transport :
    {H′ : 2Cont} (open 2Cont H′)
    {ws ws′ : 2WS-d H′ H}
    (eqws : ws ≡ ws′)
    (pF : PF (2WS-d.s ws))
    (q : 2WP-d H H (proj₁ (2WS-d.f ws pF)))
    → let pF′ = subst PF (cong 2WS-d.s eqws) pF
          q′  = subst (2WP-d H H) (t-eq eqws pF) q
      in 2WP-d (RF (2WS-d.s ws) pF) H (proj₂ (2WS-d.f ws pF) q)
       → 2WP-d (RF (2WS-d.s ws′) pF′) H (proj₂ (2WS-d.f ws′ pF′) q′)
  r-transport refl pF q r = r

  subst-posF :
    {H′ : 2Cont} (open 2Cont H′)
    {ws ws′ : 2WS-d H′ H} (open 2WS-d ws)
    (open 2WS-d ws′ renaming (s to s′ ; f to f′))
    (eq : ws ≡ ws′)
    (pF : PF s) →
    let (t , g) = f pF in
    (q  : 2WP-d H H t)
    (rp : 2WP-d (RF s pF) H (g q)) →
    let
      pF′ = subst PF (cong 2WS-d.s eq) pF
      (t′ , g′) = f′ pF′
      q′ = subst (2WP-d H H) (t-eq eq pF) q
      rp′ = r-transport eq pF q rp
    in
    subst (2WP-d H′ H) eq
    (posF (pF , q , rp))
    ≡
    posF (pF′ , q′ , rp′)
  subst-posF refl pF q rp = refl

  lem :
    {H′ : 2Cont} (open 2Cont H′)
    {ws : 2WS-d H′ H} (open 2WS-d ws)
    (eqS : {H′ : 2Cont} (ws : 2WS-d H′ H) → 2supS-d (2supS⁻-d ws) ≡ ws)
    (pF : PF s) →
    let (t , g) = f pF in
    (q : 2WP-d H H t)
    (rp : 2WP-d (RF s pF) H (2supS-d (2supS⁻-d (g q)))) →
    subst (2WP-d (S ◃ PX + PF + RF) H) (eqS (mk s f)) (posF (pF , q , rp))
      ≡ posF (pF , q , subst (2WP-d (RF s pF) H) (eqS (g q)) rp)
  lem {H′@(S ◃ PX + PF + RF)} {mk s f} eqS pF q rp =
    let (t , g) = f pF in
    begin
      subst (2WP-d (S ◃ PX + PF + RF) H) (eqS (mk s f)) (posF (pF , q , rp))
    ≡⟨ {!!} ⟩
      posF (pF , q , subst (2WP-d (RF s pF) H) (eqS (g q)) rp)
    ∎

  onP :
    {H′ : 2Cont} (open 2Cont H′)
    (s : 2WS-d H′ H)
    (q : 2WP-d H′ H (2supS-d (2supS⁻-d s)))
    → 2supP⁻-d s (2supP-d (2supS⁻-d s) q) ≡ subst (2WP-d H′ H) (onS s) q
  onP {S ◃ PX + PF + RF} (mk s f) (posX pX) = sym (trans (subst-posX (onS (mk s f)) pX) (cong posX {!!}))
  onP {H′@(S ◃ PX + PF + RF)} (mk s f) (posF (pF , q , rp)) =
    let (t , g) = f pF in 
      trans
        (cong (λ z → posF (pF , q , z)) (onP (g q) rp))
        (sym (lem {H′} {mk s f} onS pF q rp))

  2sup-d∘ᶜ2sup⁻-d : {H′ : 2Cont} → 2sup-d ∘ᶜ 2sup⁻-d ≡ idᶜ {2W-d H′ H}
  2sup-d∘ᶜ2sup⁻-d = →ᶜ-≡ onS onP

  2sup∘ᶜ2sup⁻ : 2sup ∘ᶜ 2sup⁻ ≡ idᶜ
  2sup∘ᶜ2sup⁻ = 2sup-d∘ᶜ2sup⁻-d

{-
module _
  {H : 2Cont}
  {TQ : Cont}
  (α : app H TQ →ᶜ TQ)
  where

  open Cont TQ renaming (S to T ; P to Q)
  open _→ᶜ_ α renaming (fS to αS ; fP to αP)

  mutual
  
    onS :
      {H′ : 2Cont}
      (s : appS H′ (2W H))
      → auxS α (2supS-d s) ≡ appS₁ H′ (fold2W α) s

    f′≡f :
      {H′ : 2Cont} (open 2Cont H′)
      {s : S}
      {f : (pF : PF s) →
     Σ-syntax (Cont.S (2W H))
     (λ t →
        Cont.P (2W H) t → appS (RF s pF) (Cont.S (2W H) ◃ Cont.P (2W H)))}
      → _≡_ {A = (pF : PF s) → let (t , g) = f pF in
        T × ((q : Q (fold2WS α t)) → appS (RF s pF) TQ)}
        (λ pF → let (t , g) = f pF in
           fold2WS α t , λ q → auxS α (2supS-d (g (fold2WP α t q))))
        (λ pF → let (t , g) = f pF in
        fold2WS α t , λ q → appS₁ (RF s pF) (fold2W α) (g (fold2WP α t q)))
    f′≡f {H′} {s} {f} = funExt λ pF → let (t , g) = f pF in
      cong (fold2WS α t ,_) (funExt λ q → onS (g (fold2WP α t q)))
      
    onS {S ◃ PX + PF + RF} (s , f) =
      cong (s ,_)
        (funExt λ pF → let (t , g) = f pF in
          cong (fold2WS α t ,_)
            (funExt λ q → onS (g (fold2WP α t q))))

  lem :
    {H′ : 2Cont} (open 2Cont H′)
    {s : S}
    {f f′ : (pF : PF s) → Σ-syntax T (λ t → Q t → appS (RF s pF) TQ)}
    (f′≡f : f′ ≡ f)
    (pX : PX s)    
    → subst (appP (S ◃ PX + PF + RF) TQ) (cong (s ,_) f′≡f) (inj₁ pX) ≡ inj₁ pX
  lem refl pX = refl

  onP :
    {H′ : 2Cont}
    (s : appS H′ (2W H))
    (q : appP H′ TQ (auxS α (2supS-d s)))
    → 2supP-d s (auxP α (2supS-d s) q) ≡
      appP₁ H′ (fold2W α) s (subst (appP H′ TQ) (onS s) q)
  onP {S ◃ PX + PF + RF} (s , f) (inj₁ pX) =
    sym (cong (appP₁ (S ◃ PX + PF + RF) (fold2W α) (s , f))
      (lem {S ◃ PX + PF + RF} {s} (funExt
                                    (λ pF → let (t , g) = f pF in
                                       cong (fold2WS α t ,_)
                                       (funExt (λ q → onS (g (fold2WP α t q)))))) pX))

  onP {S ◃ PX + PF + RF} (s , f) (inj₂ y) =
    sym {!!}

{-
  commuteS : (s : appS H (2W H))
    → fold2WS α (2supS s) ≡ αS (appS₁ H (fold2W α) s)
  commuteS s = cong αS (onS {H} s)

  commuteP : (s : Cont.S (app H (2W H)))
      (q : Q (fold2WS α (2supS s)))
      → 2supP s (fold2WP α (2supS s) q)
      ≡ appP₁ H (fold2W α) s (αP (appS₁ H (fold2W α) s) (subst Q (commuteS s) q))
  commuteP s q = {!cong (λ eq → ?) (onP s ?)!}
-}

  aux∘ᶜ2sup-d : {H′ : 2Cont}
    → aux α ∘ᶜ 2sup-d ≡ app₁ H′ (fold2W α)
  aux∘ᶜ2sup-d {H′} = →ᶜ-≡ onS onP
  
  commute : fold2W α ∘ᶜ 2sup ≡ α ∘ᶜ app₁ H (fold2W α)
  commute = cong (α ∘ᶜ_) aux∘ᶜ2sup-d -- →ᶜ-≡ commuteS commuteP
-}
