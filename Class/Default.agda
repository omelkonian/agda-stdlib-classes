------------------------------------------------------------------------
-- Types with a default value.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}
module Class.Default where

open import Class.Prelude
import Data.Vec as V

record Default (A : Type ℓ) : Type ℓ where
  constructor ⌞_⌟
  field def : A
open Default ⦃...⦄ public

private variable n : ℕ

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

  Default-Fin : Default (Fin (suc n))
  Default-Fin = ⌞ zero ⌟

  Default-List : Default (List A)
  Default-List = ⌞ [] ⌟

  Default-Vec-zero : Default (Vec A 0)
  Default-Vec-zero = ⌞ V.[] ⌟

  Default-Vec-suc : ⦃ Default A ⦄ → Default (Vec A (suc n))
  Default-Vec-suc = ⌞ V.replicate _ def ⌟

  Default-→ : ⦃ Default B ⦄ → Default (A → B)
  Default-→ = ⌞ const def ⌟
