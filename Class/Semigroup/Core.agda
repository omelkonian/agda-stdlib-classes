{-# OPTIONS --cubical-compatible #-}
module Class.Semigroup.Core where

open import Class.Prelude

record Semigroup (A : Type ℓ) : Type ℓ where
  infixr 5 _◇_ _<>_
  field _◇_ : A → A → A
  _<>_ = _◇_
open Semigroup ⦃...⦄ public

module _ (A : Type ℓ) ⦃ _ : Semigroup A ⦄ where
  record SemigroupLaws (_≈_ : Rel A ℓ′) : Type (ℓ ⊔ ℓ′) where
    open Alg _≈_
    field ◇-comm   : Commutative _◇_
          ◇-assocʳ : Associative _◇_
  open SemigroupLaws ⦃...⦄ public

  SemigroupLaws≡ : Type ℓ
  SemigroupLaws≡ = SemigroupLaws _≡_

module _ {A : Type ℓ} ⦃ _ : Semigroup A ⦄ ⦃ _ : SemigroupLaws≡ A ⦄ where
  ◇-assocˡ : ∀ (x y z : A) → (x ◇ (y ◇ z)) ≡ ((x ◇ y) ◇ z)
  ◇-assocˡ x y z = sym (◇-assocʳ x y z)
