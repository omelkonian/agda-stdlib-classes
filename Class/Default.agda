------------------------------------------------------------------------
-- Types with a default value.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}
module Class.Default where

open import Class.Prelude

record Default (A : Type ℓ) : Type ℓ where
  constructor ⌞_⌟
  field def : A
open Default ⦃...⦄ public

instance
  Default-⊤ : Default ⊤
  Default-⊤ = ⌞ tt ⌟

  Default-× : ⦃ Default A ⦄ → ⦃ Default B ⦄ → Default (A × B)
  Default-× = ⌞ def , def ⌟

  Default-⊎ : ⦃ Default A ⦄ → ⦃ Default B ⦄ → Default (A ⊎ B)
  Default-⊎ = ⌞ inj₁ def ⌟

  Default-Maybe : Default (Maybe A)
  Default-Maybe = ⌞ nothing ⌟

  Default-Bool : Default Bool
  Default-Bool = ⌞ true ⌟

  Default-ℕ : Default ℕ
  Default-ℕ = ⌞ zero ⌟

  Default-ℤ : Default ℤ
  Default-ℤ = ⌞ ℤ.pos def ⌟

  Default-Fin : ∀ {n : ℕ} → Default (Fin (suc n))
  Default-Fin = ⌞ zero ⌟

  Default-List : Default (List A)
  Default-List = ⌞ [] ⌟

  Default-→ : ⦃ Default B ⦄ → Default (A → B)
  Default-→ = ⌞ const def ⌟
