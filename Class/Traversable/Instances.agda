{-# OPTIONS --without-K #-}
module Class.Traversable.Instances where

open import Class.Prelude
open import Class.Functor
open import Class.Monad
open import Class.Traversable.Core

instance
  Traversable-Maybe : Traversable Maybe
  Traversable-Maybe .sequence = λ where
    nothing  → return nothing
    (just x) → x >>= return ∘ just

  Traversable-List : Traversable List
  Traversable-List .sequence = go
    where go = λ where
      []       → return []
      (m ∷ ms) → do x ← m; xs ← go ms; return (x ∷ xs)

  Traversable-List⁺ : Traversable List⁺
  Traversable-List⁺ .sequence (m ∷ ms) = do x ← m; xs ← sequence ms; return (x ∷ xs)
