module Class.Foldable.Instances where

open import Class.Prelude
open import Class.Functor
open import Class.Semigroup
open import Class.Monoid
open import Class.Foldable.Core

instance
  Foldable-List : Foldable List
  Foldable-List .fold = go where go = λ where
    [] → ε
    (x ∷ []) → x
    (x ∷ xs@(_ ∷ _)) → x ◇ go xs
