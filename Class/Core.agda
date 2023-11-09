module Class.Core where

open import Class.Prelude

Type[_↝_] : ∀ ℓ ℓ′ → Type (lsuc ℓ ⊔ lsuc ℓ′)
Type[ ℓ ↝ ℓ′ ] = Type ℓ → Type ℓ′

Type↑ : Typeω
Type↑ = ∀ {ℓ} → Type[ ℓ ↝ ℓ ]

module _ (M : Type↑) where
  _¹ : (A → Type ℓ) → Type _
  _¹ P = ∀ {x} → M (P x)

  _² : (A → B → Type ℓ) → Type _
  _² _~_ = ∀ {x y} → M (x ~ y)

  _³ : (A → B → C → Type ℓ) → Type _
  _³ _~_~_ = ∀ {x y z} → M (x ~ y ~ z)

variable
  M F : Type↑
