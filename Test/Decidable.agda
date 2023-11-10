{-# OPTIONS --without-K #-}
module Test.Decidable where

open import Class.Prelude
open import Class.Decidable
open import Class.DecEq

module _ {ℓ} {A : Set ℓ} where
  open import Data.Maybe
  _ = Is-just    {A = A} ⁇¹
  _ = Is-nothing {A = A} ⁇¹

import Data.Nat as ℕ
_ = ℕ._≤_ ⁇² ∋ it
_ = ℕ._<_ ⁇² ∋ it

import Data.Integer as ℤ
_ = ℤ._≤_ ⁇² ∋ it
_ = ℤ._<_ ⁇² ∋ it

open import Data.List.Membership.Propositional using (_∈_; _∉_)

0⋯2 = List ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []

_ = 1 ∈ 0⋯2
  ∋ auto
_ = 3 ∉ 0⋯2
  ∋ auto
f = (3 ∈ 0⋯2 → 2 ≡ 3)
  ∋ contradict
