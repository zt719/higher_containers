{-# OPTIONS --guardedness #-}
module HCont-coind where

open import Agda.Primitive
  using (Level ; lzero ; lsuc ; _⊔_)
  renaming (Set to Type ; Setω to Typeω)


record ∑ {i j} (A : Type i) (B : A → Type j) : Type (i ⊔ j) where
  constructor _,_
  field
    p₀ : A
    p₁ : B p₀
open ∑ public

infixr 10 _,_
{-# BUILTIN SIGMA ∑ #-}

_×_ : ∀ {i j} → Type i → Type j → Type (i ⊔ j)
A × B = ∑ A (λ _ → B)
infixr 4 _×_

record 𝟙 {a} : Type a where
  constructor ★
{-# BUILTIN UNIT 𝟙 #-}

data _+_ {i j} (A : Type i) (B : Type j) : Type (i ⊔ j) where
  inl : A → A + B
  inr : B → A + B
infixr 3 _+_

data _＝_ {i} {A : Type i} (a : A) : A → Type i where
  refl : a ＝ a
infix 4 _＝_

tr : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A}
   → x ＝ y → B x → B y
tr B refl b = b

data Kind : Type where
  ∗ : Kind
  _⇒_ : Kind → Kind → Kind

data Con : Type where
  • : Con
  _·_ : Con → Kind → Con

_··_ : Con → Con → Con
Γ ·· • = Γ
Γ ·· (Δ · A) = (Γ · A)  ·· Δ

Argument : Kind → Con
Argument ∗ = •
Argument (k ⇒ l) = Argument l · k

data Variable (A : Kind) : Con → Type where
  ↓       : ∀ {Γ} →                       Variable A (Γ · A)
  _·Arg_  : ∀ {Γ} → Variable A Γ → ∀ B →  Variable A (Γ · B)

splitVariable : ∀ Γ Δ k → Variable k (Γ ·· Δ) → Variable k Γ + Variable k Δ
splitVariable Γ • k x = inl x
splitVariable Γ (Δ · A) k x with splitVariable (Γ · A) Δ k x
... | inr xΔ = inr (xΔ ·Arg A)
... | inl ↓ = inr ↓
... | inl (xΓ ·Arg .A) = inl xΓ

A : Con → Kind → Type₁
A Γ ∗ = ∑ Type (λ S → (S → (k : Kind) → Variable k Γ → Type))
A Γ (k ⇒ l ) = A (Γ · k) l

B : (Γ : Con) → (k : Kind) → A Γ k → Type
B Γ ∗ (S , P) = ∑ _ (λ s
              → ∑ _ (λ k
              → ∑ _ (λ x
              → ∑ (P s k x) (λ p
              → ∑ Kind (λ l → Variable l (Argument k))))))
B Γ (k ⇒ l) a = B (Γ · k) l a

w : (Γ : Con) (k : Kind) (a : A Γ k) (b : B Γ k a) → Kind
w Γ ∗ (S , P) (s , k , x , p , l , y) = l
w Γ (k ⇒ l) a b = w (Γ · k) l a b

w₀ : (Γ : Con) (k : Kind) (a : A Γ k) (b : B Γ k a) → Con
w₀ Γ k _ _ = Γ ·· (Argument k)
--w₀ Γ ∗ (S , P) (s , k , x , p , l , y) = Γ
--w₀ Γ (k ⇒ l) a b = w₀ (Γ · k) l a b

Shape : ∀ Γ k → A Γ k → Type
Shape Γ ∗ = p₀
Shape Γ (k ⇒ l) = Shape (Γ · k) l


ConPosition : ∀ Γ k a → Shape Γ k a → ∀ l → Variable l Γ → Type
ConPosition Γ ∗ = p₁
ConPosition Γ (k ⇒ l) a s m x = ConPosition (Γ · k) l a s m (x ·Arg k)

ArgPosition : ∀ Γ k a → Shape Γ k a → ∀ l → Variable l (Argument k) → Type
ArgPosition Γ ∗ _ _ _ ()
ArgPosition Γ (k ⇒ l) a s m ↓ = ConPosition (Γ · k) l a s m ↓
ArgPosition Γ (k ⇒ l) a s m (x ·Arg .k) = ArgPosition (Γ · k) l a s m x


Bify : ∀ Γ k a s l x → ConPosition Γ k a s l x
        → ∀ m → Variable m (Argument l)
        → B Γ k a
Bify Γ ∗ a s l x p m y = (s , l , x , p , m , y)
Bify Γ (k₀ ⇒ k₁) a s l x p m y = Bify (Γ · k₀) k₁ a s l (x ·Arg k₀) p m y

w-Bify : ∀ Γ k a s l x p m y → w Γ k a (Bify Γ k a s l x p m y) ＝ m
w-Bify Γ ∗ a s l x p m y  = refl
w-Bify Γ (k₀ ⇒ k₁) a s l x p m y  = w-Bify (Γ · k₀) k₁ a s l (x ·Arg k₀) p m y

record Expression (Γ : Con) (k : Kind) : Type₁ where
  constructor expression
  coinductive
  field
    structure : A Γ k
    call : (b : B Γ k structure) → Expression (w₀ Γ k structure b) (w Γ k structure b)

open Expression


shift : ∀ Γ k l → Expression Γ (k ⇒ l) → Expression (Γ · k) l
shift Γ k l e = expression (structure e) (call e)

weaken : ∀ Γ k l → Expression Γ l → Expression (Γ · k) l
weaken Γ k l e = ren Γ (Γ · k) l (λ m x → x ·Arg k) e
  where
    liftRen : ∀ Γ Δ k
            → (∀ m → Variable m Γ → Variable m Δ)
            → ∀ m → Variable m (Γ · k) → Variable m (Δ · k)
    liftRen Γ Δ k ρ .k ↓ = ↓
    liftRen Γ Δ k ρ m (x ·Arg .k) = ρ m x ·Arg k

    ren : ∀ Γ Δ k
        → (∀ m → Variable m Γ → Variable m Δ)
        → Expression Γ k → Expression Δ k

    structure (ren Γ Δ ∗ ρ e) =
      ( p₀ (structure e)
      , λ s m y → ∑ _ λ x
                → ∑ (ρ m x ＝ y) λ _
                → p₁ (structure e) s m x
      )

    call (ren Γ Δ ∗ ρ e)
         (s , m , .(ρ m x) , (x , refl , p) , n , y) =
      ren Γ Δ n ρ (call e (s , m , x , p , n , y))

    structure (ren Γ Δ (k₀ ⇒ k₁) ρ e) =
      structure
        (ren (Γ · k₀) (Δ · k₀) k₁
             (liftRen Γ Δ k₀ ρ)
             (shift Γ k₀ k₁ e))

    call (ren Γ Δ (k₀ ⇒ k₁) ρ e) b =
      call
        (ren (Γ · k₀) (Δ · k₀) k₁
             (liftRen Γ Δ k₀ ρ)
             (shift Γ k₀ k₁ e))
        b

var : ∀ Γ k → Expression (Γ · k) k
var Γ k =
  corec Xᵛ cᵛ stepᵛ (Γ · k) k
        (k , ↓ , appendVariable (Γ · k) (Argument k))
  where
    weakenVariable : ∀ Γ Δ k → Variable k Γ → Variable k (Γ ·· Δ)
    weakenVariable Γ • k x = x
    weakenVariable Γ (Δ · A) k x =
      weakenVariable (Γ · A) Δ k (x ·Arg A)

    appendVariable : ∀ Γ Δ k → Variable k Δ → Variable k (Γ ·· Δ)
    appendVariable Γ • k ()
    appendVariable Γ (Δ · A) .A ↓ =
      weakenVariable (Γ · A) Δ A ↓
    appendVariable Γ (Δ · A) k (x ·Arg .A) =
      appendVariable (Γ · A) Δ k x

    Xᵛ : ∀ Θ l → Type
    Xᵛ Θ l =
      ∑ Kind λ K →
      Variable K Θ ×
      (∀ m → Variable m (Argument K) → Variable m (Θ ·· Argument l))

    cᵛ : ∀ Θ l → Xᵛ Θ l → A Θ l
    cᵛ Θ ∗ (K , x , α) =
      ( 𝟙
      , λ _ m y →
          ∑ (K ＝ m) λ q →
          tr (λ z → Variable z Θ) q x ＝ y
      )
    cᵛ Θ (k ⇒ l) (K , x , α) =
      cᵛ (Θ · k) l (K , x ·Arg k , α)

    stepᵛ : ∀ Θ l
          → (v : Xᵛ Θ l)
          → (b : B Θ l (cᵛ Θ l v))
          → Xᵛ (w₀ Θ l (cᵛ Θ l v) b)
                (w  Θ l (cᵛ Θ l v) b)
    stepᵛ Θ ∗ (K , x , α)
           (_ , .K , .x , (refl , refl) , m , y) =
      (m , α m y , appendVariable Θ (Argument m))
    stepᵛ Θ (k ⇒ l) (K , x , α) b =
      stepᵛ (Θ · k) l (K , x ·Arg k , α) b

    corec : ∀ {i}
          → (X : ∀ Γ k → Type i)
          → (coalg : ∀ Γ k → X Γ k → A Γ k)
          → (step : ∀ Γ k → (x : X Γ k)
                  → (b : B Γ k (coalg Γ k x))
                  → X (w₀ Γ k (coalg Γ k x) b)
                      (w  Γ k (coalg Γ k x) b))
          → ∀ Γ k → X Γ k → Expression Γ k
    structure (corec X coalg step Γ k x) =
      coalg Γ k x
    call (corec X coalg step Γ k x) b =
      corec X coalg step _ _ (step Γ k x b)

contextVar : ∀ Γ k → Variable k Γ → Expression Γ k
contextVar (Γ · l) k ↓ = var Γ k
contextVar (Γ · l) k (x ·Arg ._) = weaken _ _ _ (contextVar Γ k x)

·subst : ∀ Γ Δ l
        → (∀ k → Variable k Γ → Expression Δ k)
        → (∀ k → Variable k (Γ · l) → Expression (Δ · l) k)
·subst Γ Δ k σ l ↓ = var Δ l
·subst Γ Δ k σ l (x ·Arg ._) = weaken Δ k l (σ l x)


µ₀ : Expression (• · (∗ ⇒ ∗))  ∗
structure µ₀ = (𝟙 , λ {_ ._ ↓ → 𝟙})
call µ₀ (_ , ._ , ↓ , _ , ._ , ↓) = µ₀

λµ₀ : Expression • ((∗ ⇒ ∗) ⇒ ∗)
λµ₀ = expression (structure µ₀) (call µ₀)



Substitution : Type₁
Substitution = ∀ Γ Δ → (∀ k → Variable k Γ   → Expression Δ k)
                     → (∀ k → Expression Γ k → Expression Δ k)

-- Terminality: Expression is a final coalgebra
-- Given any coalgebra (X, coalg), there is a unique morphism into Expression
terminality : ∀ {i}
            → (X : ∀ Γ k → Type i)
            → (coalg : ∀ Γ k → X Γ k → A Γ k)
            → (step : ∀ Γ k → (x : X Γ k) → (b : B Γ k (coalg Γ k x)) → X (w₀ Γ k (coalg Γ k x) b) (w Γ k (coalg Γ k x) b))
            → ∀ Γ k → X Γ k → Expression Γ k
structure (terminality X coalg step Γ k x) = coalg Γ k x
call (terminality X coalg step Γ k x) b = terminality X coalg step _ _ (step Γ k x b)


X : ∀ Θ l → Type₁
X Θ l = ∑ _ (λ Λ → (Expression Λ l) × (∀ m → Variable m Λ → Expression Θ m))


c : (Δ₁ : Con) (k₁ : Kind) → X Δ₁ k₁ → A Δ₁ k₁
data S (Γ₁ : Con) (e₁ : Expression Γ₁ ∗) (Δ₁ : Con) (σ₁ : ∀ m → Variable m Γ₁ → Expression Δ₁ m) : Type where
  sup : (s : p₀ (structure e₁))
      → (∀ m x  → (p : p₁ (structure e₁) s m x)
                → ∑ (Shape Δ₁ m (structure (σ₁ m x)))
                    (λ s' → ∀ l y (p' : ArgPosition Δ₁ m (structure (σ₁ m x)) s' l y)
                          → Shape Δ₁ l (c Δ₁ l (Γ₁ , call e₁ (s , m , x , p , l , y) , σ₁))) )
      → S Γ₁ e₁ Δ₁ σ₁

P : ∀ Γ₁ e₁ Δ₁ σ₁ → S Γ₁ e₁ Δ₁ σ₁ → (k₁ : Kind) → Variable k₁ Δ₁ → Type
P Γ₁ e₁ Δ₁ σ₁ (sup s v) l y
    = ∑ _ (λ m
    → ∑ _ (λ x
    → ∑ (p₁ (structure e₁) s m x) (λ p
    → ConPosition Δ₁ m (structure (σ₁ m x)) (p₀ (v m x p)) l y)))

c Δ₁ ∗ (Γ₁ , e₁ , σ₁) = ( S Γ₁ e₁ Δ₁ σ₁ , P Γ₁ e₁ Δ₁ σ₁)
c Δ₁ (k ⇒ l) (Γ₁ , e₁ , σ₁)
    = c _ l (Γ₁ · k
            , shift Γ₁ k l e₁
            , ·subst Γ₁ Δ₁ k σ₁)



{-# TERMINATING #-}
substitute : Substitution
structure (substitute Γ Δ σ k e) = c Δ k (Γ , e , σ)
call (substitute Γ Δ σ ∗ e) ((sup s v) , k , x , (m , z , p , p') , l , y)
  = substitute (Δ ·· Argument m) Δ ρ l e₂
  where
    eσ : Expression Δ m
    eσ = σ m z

    sσ : Shape Δ m (structure eσ)
    sσ = p₀ (v m z p)

    bσ : B Δ m (structure eσ)
    bσ = Bify Δ m (structure eσ) sσ k x p' l y

    e₂ : Expression (Δ ·· Argument m) l
    e₂ = tr (Expression _) (w-Bify Δ m (structure eσ) sσ k x p' l y) (call eσ bσ)

    ρ : _
    ρ n u with splitVariable Δ (Argument m) n u
    ... | inl uΔ   = contextVar Δ n uΔ
    ... | inr uArg = substitute Γ Δ σ n (call e (s , m , z , p , n , uArg))

call (substitute Γ Δ σ (k ⇒ l) e) b =
  call (substitute (Γ · k) (Δ · k) (·subst Γ Δ k σ) l (shift Γ k l e)) b

{- ALTERNATIVE USING terminality:

substitute : Substitution
substitute Γ Δ σ k e = terminality X c step Δ k (Γ , e , σ)
  where
    step : ∀ Δ₁ k₁
         → (x₁ : X Δ₁ k₁)
         → (b : B Δ₁ k₁ (c Δ₁ k₁ x₁))
         → X (w₀ Δ₁ k₁ (c Δ₁ k₁ x₁) b)
             (w  Δ₁ k₁ (c Δ₁ k₁ x₁) b)

    step Δ₁ ∗ (Γ₁ , e₁ , σ₁)
         ((sup s v) , k , x , (m , z , p , p') , l , y) =
      ( Δ₁ ·· Argument m
      , e₂
      , ρ
      )
      where
        eσ : Expression Δ₁ m
        eσ = σ₁ m z

        sσ : Shape Δ₁ m (structure eσ)
        sσ = p₀ (v m z p)

        bσ : B Δ₁ m (structure eσ)
        bσ = Bify Δ₁ m (structure eσ) sσ k x p' l y

        e₂ : Expression (Δ₁ ·· Argument m) l
        e₂ =
          tr (Expression _)
             (w-Bify Δ₁ m (structure eσ) sσ k x p' l y)
             (call eσ bσ)

        ρ : ∀ n → Variable n (Δ₁ ·· Argument m) → Expression Δ₁ n
        ρ n u with splitVariable Δ₁ (Argument m) n u
        ... | inl uΔ =
          contextVar Δ₁ n uΔ
        ... | inr uArg =
          terminality X c step Δ₁ n
            ( Γ₁
            , call e₁ (s , m , z , p , n , uArg)
            , σ₁
            )

    step Δ₁ (k ⇒ l) (Γ₁ , e₁ , σ₁) b =
      step (Δ₁ · k) l
        ( Γ₁ · k
        , shift Γ₁ k l e₁
        , ·subst Γ₁ Δ₁ k σ₁
        )
        b
  -}
