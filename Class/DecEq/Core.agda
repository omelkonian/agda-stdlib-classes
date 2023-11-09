{-# OPTIONS --without-K #-}
module Class.DecEq.Core where

open import Class.Prelude
open import Class.Core

record DecEq (A : Type ℓ) : Type ℓ where
  field _≟_ : DecidableEquality A

  _==_ _≡ᵇ_ : A → A → Bool
  x == y = ⌊ x ≟ y ⌋
  _≡ᵇ_ = _==_

  _≠_ : A → A → Bool
  x ≠ y = not (x == y)

  infix 4 _≟_ _≡ᵇ_ _==_ _≠_
open DecEq ⦃...⦄ public

DecEq¹ = DecEq ¹
DecEq² = DecEq ²
DecEq³ = DecEq ³
