{-# OPTIONS --cubical --guardedness #-}

module Data.2M.Properties where

open import Prelude
open import Data.Cont
open import Data.2Cont
open import Data.2M.Base

------------------------------------------------------------------------
-- Infimum is iso

module _ {H : 2Cont} where

  2infS⁻∘2infS-d : {H′ : 2Cont} (ms : 2MS-d H′ H) → 2infS⁻-d (2infS-d ms) ≡ ms
  2infS⁻∘2infS-d {S ◃ PX + PF + RF} ms i .2MS-d.s = ms .2MS-d.s
  2infS⁻∘2infS-d {S ◃ PX + PF + RF} ms i .2MS-d.f =
    λ pF → let (t , g) = ms .2MS-d.f pF in
      t , λ q → 2infS⁻∘2infS-d {RF (ms .2MS-d.s) pF} (g q) i

  2infP⁻∘2infP-d : {H′ : 2Cont} (ms : 2MS-d H′ H)
    → PathP (λ i → 2MP-d H′ H (2infS⁻∘2infS-d ms i) → 2MP-d H′ H ms)
            (λ p → 2infP-d ms (2infP⁻-d (2infS-d ms) p))
            (λ p → p)
  2infP⁻∘2infP-d {S ◃ PX + PF + RF} ms i (posX pX) =
    posX pX
  2infP⁻∘2infP-d {S ◃ PX + PF + RF} ms i (posF (pF , q , rp)) =
    let (t , g) = ms .2MS-d.f pF in
      posF (pF , q , 2infP⁻∘2infP-d {RF (ms .2MS-d.s) pF} (g q) i rp)

  2inf⁻∘ᶜ2inf-d : {H′ : 2Cont} → 2inf⁻-d ∘ᶜ 2inf-d ≡ idᶜ {2M-d H′ H}
  2inf⁻∘ᶜ2inf-d {H′} i =
    (λ ms → 2infS⁻∘2infS-d {H′} ms i) ◃ (λ ms → 2infP⁻∘2infP-d {H′} ms i)

  2inf⁻∘ᶜ2inf : 2inf⁻ ∘ᶜ 2inf ≡ idᶜ {2M H}
  2inf⁻∘ᶜ2inf = 2inf⁻∘ᶜ2inf-d {H}

------------------------------------------------------------------------
-- Unfolding commutes

module _ {H : 2Cont} {TQ : Cont} (α : TQ →ᶜ app H TQ) where

  2inf∘ᶜauxS-d : {H′ : 2Cont} (x : appS H′ TQ)
    → 2infS-d (auxS α x) ≡ appS₁ H′ (unfold2M α) x
  2inf∘ᶜauxS-d {S ◃ PX + PF + RF} (s , f) i =
    s , λ pF → let (t , g) = f pF in
      unfold2MS α t , λ q → 2inf∘ᶜauxS-d {RF s pF} (g (unfold2MP α t q)) i

  2inf∘ᶜauxP-d : {H′ : 2Cont} (x : appS H′ TQ)
    → PathP (λ i → appP H′ (2M H) (2inf∘ᶜauxS-d x i) → appP H′ TQ x)
            (λ p → auxP α x (2infP-d (auxS α x) p))
            (appP₁ H′ (unfold2M α) x)
  2inf∘ᶜauxP-d {S ◃ PX + PF + RF} (s , f) i (inl pX) =
    inl pX
  2inf∘ᶜauxP-d {S ◃ PX + PF + RF} (s , f) i (inr (pF , q , rp)) =
    let (t , g) = f pF in
      inr (pF , unfold2MP α t q , 2inf∘ᶜauxP-d {RF s pF} (g (unfold2MP α t q)) i rp)

  2inf∘ᶜaux-d : {H′ : 2Cont} → 2inf-d ∘ᶜ aux α ≡ app₁ H′ (unfold2M α)
  2inf∘ᶜaux-d {H′} i =
    (λ x → 2inf∘ᶜauxS-d {H′} x i) ◃ (λ x → 2inf∘ᶜauxP-d {H′} x i)

  2inf∘ᶜaux : 2inf-d ∘ᶜ aux α ≡ app₁ H (unfold2M α)
  2inf∘ᶜaux = 2inf∘ᶜaux-d {H}

  comm : 2inf ∘ᶜ unfold2M α ≡ app₁ H (unfold2M α) ∘ᶜ α
  comm = cong (_∘ᶜ α) 2inf∘ᶜaux

------------------------------------------------------------------------
-- Unfolding is unique

module _ {H : 2Cont} {TQ : Cont} (α : TQ →ᶜ app H TQ)
         (h : TQ →ᶜ 2M H) (h-comm : 2inf {H} ∘ᶜ h ≡ app₁ H h ∘ᶜ α) where

  open Cont TQ renaming (S to T ; P to Q)
  open _→ᶜ_ α renaming (fS to αS ; fP to αP)
  open _→ᶜ_ h renaming (fS to hS ; fP to hP)

  h-unfold : h ≡ 2inf⁻ {H} ∘ᶜ app₁ H h ∘ᶜ α
  h-unfold = cong (_∘ᶜ h) (sym (2inf⁻∘ᶜ2inf {H})) ∙ cong (2inf⁻ {H} ∘ᶜ_) h-comm

  {-# TERMINATING #-}
  unfold2M-uniqS : (t : T) → hS t ≡ unfold2MS α t

  unfold2M-uniqP : (t : T)
    → PathP (λ i → 2MP H (unfold2M-uniqS t i) → Q t) (hP t) (unfold2MP α t)

  2inf⁻∘ᶜapp₁S-d : {H′ : 2Cont} (x : appS H′ TQ)
    → 2infS⁻-d (appS₁ H′ h x) ≡ auxS α x

  2inf⁻∘ᶜapp₁P-d : {H′ : 2Cont} (x : appS H′ TQ)
    → PathP (λ i → 2MP-d H′ H (2inf⁻∘ᶜapp₁S-d x i) → appP H′ TQ x)
            (λ p → appP₁ H′ h x (2infP⁻-d (appS₁ H′ h x) p))
            (auxP α x)

  unfold2M-uniqS t =
    (λ i → _→ᶜ_.fS (h-unfold i) t) ∙ 2inf⁻∘ᶜapp₁S-d (αS t)

  unfold2M-uniqP t =
    compPathP' {B = λ ms → 2MP H ms → Q t}
               {p = λ i → _→ᶜ_.fS (h-unfold i) t}
               {q = 2inf⁻∘ᶜapp₁S-d (αS t)}
      (λ i → _→ᶜ_.fP (h-unfold i) t)
      (λ i p → αP t (2inf⁻∘ᶜapp₁P-d (αS t) i p))

  2inf⁻∘ᶜapp₁S-d {S ◃ PX + PF + RF} (s , f) i .2MS-d.s = s
  2inf⁻∘ᶜapp₁S-d {S ◃ PX + PF + RF} (s , f) i .2MS-d.f =
    λ pF → let (t , g) = f pF in
      unfold2M-uniqS t i , λ q → 2inf⁻∘ᶜapp₁S-d {RF s pF} (g (unfold2M-uniqP t i q)) i

  2inf⁻∘ᶜapp₁P-d {S ◃ PX + PF + RF} (s , f) i (posX pX) =
    inl pX
  2inf⁻∘ᶜapp₁P-d {S ◃ PX + PF + RF} (s , f) i (posF (pF , q , rp)) =
    let (t , g) = f pF in
      inr (pF , unfold2M-uniqP t i q ,
        2inf⁻∘ᶜapp₁P-d {RF s pF} (g (unfold2M-uniqP t i q)) i rp)

  unfold2M-uniq : h ≡ unfold2M α
  unfold2M-uniq i = (λ t → unfold2M-uniqS t i) ◃ (λ t → unfold2M-uniqP t i)
