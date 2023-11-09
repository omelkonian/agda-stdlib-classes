{-# OPTIONS --without-K #-}
module Test.Decidable where

open import Class.Prelude
open import Class.Decidable
open import Class.DecEq

open import Data.List.Membership.Propositional using (_∈_; _∉_)

private 0⋯2 = List ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []

_ = 1 ∈ 0⋯2
  ∋ auto
_ = 3 ∉ 0⋯2
  ∋ auto
f = (3 ∈ 0⋯2 → 2 ≡ 3)
  ∋ contradict
