\begin{code}
{-# OPTIONS --cubical #-}

open import Prelude

variable
  A B : Type

Maybe₁ : (A → B) → Maybe A → Maybe B
Maybe₁ f nothing = nothing
Maybe₁ f (just a) = just (f a)

[z,s] : Maybe ℕ → ℕ
[z,s] nothing = zero
[z,s] (just n) = suc n

foldℕ : (Maybe A → A) → ℕ → A
foldℕ α zero = α nothing
foldℕ α (suc n) = α (just (foldℕ α n))

commuteℕ : (α : Maybe A → A) → foldℕ α ∘ [z,s] ≡ α ∘ Maybe₁ (foldℕ α)
commuteℕ α i nothing = α nothing
commuteℕ α i (just n) = α (just (foldℕ α n))

uniquefoldℕ : (foldℕ' : (Maybe A → A) → ℕ → A)
  → ((α : Maybe A → A) → foldℕ' α ∘ [z,s] ≡ α ∘ Maybe₁ (foldℕ' α))
  → foldℕ' ≡ foldℕ
uniquefoldℕ foldℕ' p i α zero = p α i nothing
uniquefoldℕ foldℕ' p i α (suc n) =
  ((λ j → p α j (just n)) ∙ cong (α ∘ just) (λ j → uniquefoldℕ foldℕ' p j α n)) i

infix 0 _◃_
record Cont : Type₁ where
  constructor _◃_
  field
    S : Type
    P : S → Type

variable
  SP : Cont

⟦_⟧ : Cont → Type → Type
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

⟦_⟧₁ : (SP : Cont) → (A → B) → ⟦ SP ⟧ A → ⟦ SP ⟧ B
⟦ SP ⟧₁ g (s , f) = s , g ∘ f

data W (SP : Cont) : Type where
  sup : ⟦ SP ⟧ (W SP) → W SP

foldW : (⟦ SP ⟧ A → A) → W SP → A
foldW α (sup (s , f)) = α (s , λ p → foldW α (f p))

commuteW : (α : ⟦ SP ⟧ A → A) → foldW α ∘ sup ≡ α ∘ ⟦ SP ⟧₁ (foldW α)
commuteW α i (s , f) = α (s , foldW α ∘ f)

uniquefoldW : (foldW' : (⟦ SP ⟧ A → A) → W SP → A)
  → ((α : ⟦ SP ⟧ A → A) → foldW' α ∘ sup ≡ α ∘ ⟦ SP ⟧₁ (foldW' α))
  → foldW' ≡ foldW
uniquefoldW foldW' c i α (sup (s , f)) =
  ((λ j → c α j (s , f)) ∙ cong (λ g → α (s , g)) (λ j p → uniquefoldW foldW' c j α (f p))) i
\end{code}
