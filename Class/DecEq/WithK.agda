{-# OPTIONS --with-K #-}
module Class.DecEq.WithK where

open import Class.Prelude
open import Class.DecEq.Core

module _ ⦃ _ : DecEq A ⦄ where
  ≟-refl : ∀ (x : A) → (x ≟ x) ≡ yes refl
  ≟-refl x with refl , p ← dec-yes (x ≟ x) refl = p

  DecEq-Σ : ∀ {B : A → Type ℓ′} ⦃ _ : ∀ {x} → DecEq (B x) ⦄ → DecEq (Σ A B)
  DecEq-Σ ._≟_ (x , y) (x′ , y′)
    with x ≟ x′
  ... | no ¬p    = no λ where refl → ¬p refl
  ... | yes refl
    with y ≟ y′
  ... | no ¬p    = no λ where refl → ¬p refl
  ... | yes refl = yes refl
