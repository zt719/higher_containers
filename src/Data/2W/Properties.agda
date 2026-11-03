{-# OPTIONS --cubical --guardedness #-}

module Data.2W.Properties where

open import Prelude
open import Data.Cont
open import Data.2Cont
open import Data.2W.Base

------------------------------------------------------------------------
-- Supremum is iso

module _ {H : 2Cont} where
 
  2supS∘2supS⁻-d : {H' : 2Cont} (w : 2WS-d H' H) → 2supS-d (2supS⁻-d w) ≡ w
  2supS∘2supS⁻-d {S ◃ PX + PF + RF} (mk s f) i =
    mk s (λ pF → let (t , g) = f pF in t , λ q → 2supS∘2supS⁻-d {RF s pF} (g q) i)
 
  2supP∘2supP⁻-d : {H' : 2Cont} (w : 2WS-d H' H)
    → PathP (λ i → 2WP-d H' H (2supS∘2supS⁻-d w i) → 2WP-d H' H w)
            (λ p → 2supP⁻-d w (2supP-d (2supS⁻-d w) p))
            (λ p → p)
  2supP∘2supP⁻-d {S ◃ PX + PF + RF} (mk s f) i (posX pX) =
    posX pX
  2supP∘2supP⁻-d {S ◃ PX + PF + RF} (mk s f) i (posF (pF , q , rp)) =
    let (t , g) = f pF in
      posF (pF , q , 2supP∘2supP⁻-d {RF s pF} (g q) i rp)
 
  2sup∘ᶜ2sup⁻-d : {H' : 2Cont} → 2sup-d ∘ᶜ 2sup⁻-d ≡ idᶜ {2W-d H' H}
  2sup∘ᶜ2sup⁻-d {H'} i =
    (λ w → 2supS∘2supS⁻-d {H'} w i) ◃ (λ w → 2supP∘2supP⁻-d {H'} w i)
 
  2sup∘ᶜ2sup⁻ : 2sup ∘ᶜ 2sup⁻ ≡ idᶜ {2W H}
  2sup∘ᶜ2sup⁻ = 2sup∘ᶜ2sup⁻-d {H}

------------------------------------------------------------------------
-- Folding commutes

module _ {H : 2Cont} {TQ : Cont} (α : app H TQ →ᶜ TQ) where

  aux∘ᶜ2supS-d : {H' : 2Cont} (x : appS H' (2W H))
    → auxS α (2supS-d x) ≡ appS₁ H' (fold2W α) x
  aux∘ᶜ2supS-d {S ◃ PX + PF + RF} (s , f) i =
    s , λ pF → let (t , g) = f pF in
      fold2WS α t , λ q → aux∘ᶜ2supS-d {RF s pF} (g (fold2WP α t q)) i

  aux∘ᶜ2supP-d : {H' : 2Cont} (x : appS H' (2W H))
    → PathP (λ i → appP H' TQ (aux∘ᶜ2supS-d x i) → appP H' (2W H) x)
            (λ p → 2supP-d x (auxP α (2supS-d x) p))
            (appP₁ H' (fold2W α) x)
  aux∘ᶜ2supP-d {S ◃ PX + PF + RF} (s , f) i (inl pX) =
    inl pX
  aux∘ᶜ2supP-d {S ◃ PX + PF + RF} (s , f) i (inr (pF , q , rp)) =
    let (t , g) = f pF in
      inr (pF , fold2WP α t q , aux∘ᶜ2supP-d {RF s pF} (g (fold2WP α t q)) i rp)

  aux∘ᶜ2sup-d : {H′ : 2Cont} → aux α ∘ᶜ 2sup-d ≡ app₁ H′ (fold2W α)
  aux∘ᶜ2sup-d {H′} i =
    (λ x → aux∘ᶜ2supS-d {H′} x i) ◃ (λ x → aux∘ᶜ2supP-d {H′} x i)

  aux∘ᶜ2sup : aux α ∘ᶜ 2sup-d ≡ app₁ H (fold2W α)
  aux∘ᶜ2sup = aux∘ᶜ2sup-d {H}

  comm : fold2W α ∘ᶜ 2sup ≡ α ∘ᶜ app₁ H (fold2W α)
  comm = cong (α ∘ᶜ_) aux∘ᶜ2sup

------------------------------------------------------------------------
-- Folding is unique

module _ {H : 2Cont} {TQ : Cont} (α : app H TQ →ᶜ TQ)
         (h : 2W H →ᶜ TQ) (h-comm : h ∘ᶜ 2sup ≡ α ∘ᶜ app₁ H h) where

  open Cont TQ renaming (S to T ; P to Q)
  open _→ᶜ_ α renaming (fS to αS ; fP to αP)
  open _→ᶜ_ h renaming (fS to hS ; fP to hP)

  h-unfold : h ≡ α ∘ᶜ app₁ H h ∘ᶜ 2sup⁻
  h-unfold = cong (h ∘ᶜ_) (sym (2sup∘ᶜ2sup⁻ {H})) ∙ cong (_∘ᶜ 2sup⁻ {H}) h-comm

  fold2W-uniqS : (w : 2WS H) → hS w ≡ fold2WS α w

  fold2W-uniqP : (w : 2WS H)
    → PathP (λ i → Q (fold2W-uniqS w i) → 2WP H w) (hP w) (fold2WP α w)

  app₁∘ᶜ2sup⁻S-d : {H' : 2Cont} (w : 2WS-d H' H)
    → appS₁ H' h (2supS⁻-d w) ≡ auxS α w

  app₁∘ᶜ2sup⁻P-d : {H' : 2Cont} (w : 2WS-d H' H)
    → PathP (λ i → appP H' TQ (app₁∘ᶜ2sup⁻S-d w i) → 2WP-d H' H w)
            (λ p → 2supP⁻-d w (appP₁ H' h (2supS⁻-d w) p))
            (auxP α w)

  fold2W-uniqS w = (λ i → _→ᶜ_.fS (h-unfold i) w) ∙ cong αS (app₁∘ᶜ2sup⁻S-d w)

  fold2W-uniqP w =
    compPathP' {B = λ t → Q t → 2WP H w}
               {p = λ i → _→ᶜ_.fS (h-unfold i) w}
               {q = cong αS (app₁∘ᶜ2sup⁻S-d w)}
      (λ i → _→ᶜ_.fP (h-unfold i) w)
      (λ i q → app₁∘ᶜ2sup⁻P-d w i (αP (app₁∘ᶜ2sup⁻S-d w i) q))

  app₁∘ᶜ2sup⁻S-d {S ◃ PX + PF + RF} (mk s f) i =
    s , λ pF → let (t , g) = f pF in
      fold2W-uniqS t i , λ q → app₁∘ᶜ2sup⁻S-d {RF s pF} (g (fold2W-uniqP t i q)) i

  app₁∘ᶜ2sup⁻P-d {S ◃ PX + PF + RF} (mk s f) i (inl pX) =
    posX pX
  app₁∘ᶜ2sup⁻P-d {S ◃ PX + PF + RF} (mk s f) i (inr (pF , q , rp)) =
    let (t , g) = f pF in
      posF (pF , fold2W-uniqP t i q , app₁∘ᶜ2sup⁻P-d {RF s pF} (g (fold2W-uniqP t i q)) i rp)

  fold2W-uniq : h ≡ fold2W α
  fold2W-uniq i = (λ w → fold2W-uniqS w i) ◃ (λ w → fold2W-uniqP w i)
