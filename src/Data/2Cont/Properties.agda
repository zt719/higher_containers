{-# OPTIONS --without-K #-}

module Data.2Cont.Properties where

open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality hiding (J)
open import Data.Cont
open import Data.2Cont.Base
open import Data.2Cont.Morphism

postulate
  funExt : ∀ {ℓ ℓ′}
           {A : Set ℓ} {B : A → Set ℓ′}
           {f g : (a : A) → B a}
           (h : (a : A) → f a ≡ g a)
           → f ≡ g

  funExt-β : ∀ {ℓ ℓ′}
           {A : Set ℓ} {B : A → Set ℓ′}
           {f g : (a : A) → B a}
           (h : (a : A) → f a ≡ g a)           
           (a : A) → cong-app (funExt h) a ≡ h a

private
  variable
    SP SP' TQ TQ' UV : Cont
    H J : 2Cont

------------------------------------------------------------------------
-- Natural transformations

-- Extensional equality of morphisms
_≈_ : ∀ {S P T Q} → (S ◃ P) →ᶜ (T ◃ Q) → (S ◃ P) →ᶜ (T ◃ Q) → Set
_≈_ {Q = Q} (f ◃ g) (f′ ◃ g′) =
  Σ[ e ∈ (f ≡ f′) ]
    (g ≡ λ s q → g′ s (subst Q (cong-app e s) q))

≈-≡ : {SP TQ : Cont} {α β : SP →ᶜ TQ}
      → α ≈ β → α ≡ β
≈-≡ (refl , refl) = refl

onS : {H J : 2Cont} 
      (α : H →²ᶜ J)
      {F G : Cont}
      (β : F →ᶜ G)
      (s : appS H F)
      → app→²ᶜS α G (appS₁ H β s) ≡ appS₁ J β (app→²ᶜS α F s)
onS {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (αS ◃ αPX + αPF + αRF)
    {F} {G} (βS ◃ βP) (s , f) =
  cong (αS s ,_) (funExt λ qF →
    let (t , g) = f (αPF s qF) in
      cong (βS t ,_) (funExt λ q →
        onS (αRF s qF) (βS ◃ βP) (g (βP t q))))

onP : {H J : 2Cont} 
      (α : H →²ᶜ J)
      {F G : Cont}
      (β : F →ᶜ G)
      (s : appS H F)
      (q : appP J G (app→²ᶜS α G (appS₁ H β s)))
      → appP₁ H β s (app→²ᶜP α G (appS₁ H β s) q)
      ≡ app→²ᶜP α F s (appP₁ J β (app→²ᶜS α F s) (subst (appP J G) (onS α β s) q))
onP {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (αS ◃ αPX + αPF + αRF) {F} {G} (fS ◃ fP) (s , f) (inj₁ x) =
  {!!}
onP {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (αS ◃ αPX + αPF + αRF) {F} {G} (fS ◃ fP) (s , f) (inj₂ y) = {!!}

app→²ᶜ-nat : {H J : 2Cont} 
             (α : H →²ᶜ J)
             {F G : Cont}
             (β : F →ᶜ G)
           → app→²ᶜ α G ∘ᶜ app₁ H β ≡ app₁ J β ∘ᶜ app→²ᶜ α F
app→²ᶜ-nat {H} {J} α {F} {G} β =
  ≈-≡ (funExt (onS α β) , funExt λ s → funExt λ q →
    trans (onP α β s q)
      (cong (λ z → app→²ᶜP α F s (appP₁ J β (app→²ᶜS α F s) (subst (appP J G) z q)))
        (sym (funExt-β (onS α β) s))))

Nat : 2Cont → 2Cont → Set₁
Nat H J =
  Σ[ α ∈ ((F : Cont) → app H F →ᶜ app J F) ]
    ({F G : Cont} (β : F →ᶜ G)
       → α G ∘ᶜ app₁ H β ≡ app₁ J β ∘ᶜ α F)

to : H →²ᶜ J → Nat H J
to m = app→²ᶜ m , app→²ᶜ-nat m
