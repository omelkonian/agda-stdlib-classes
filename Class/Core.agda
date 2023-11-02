module Class.Core where

open import Class.Prelude

Type[_↝_] : ∀ ℓ ℓ′ → Type (lsuc ℓ ⊔ lsuc ℓ′)
Type[ ℓ ↝ ℓ′ ] = Type ℓ → Type ℓ′

Type↑ : Typeω
Type↑ = ∀ {ℓ} → Type[ ℓ ↝ ℓ ]

variable
  M F : Type↑
