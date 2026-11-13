\begin{code}
{-# OPTIONS --type-in-type #-}

{-# NO_POSITIVITY_CHECK #-}
data Bush : Type → Type₁ where
  []  : {X : Type} → Bush X
  _∷_ : {X : Type} → X → Bush (Bush X) → Bush X
\end{code}
