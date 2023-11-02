{-# OPTIONS --safe --without-K #-}
module Class.Show.Core where

open import Class.Prelude

record Show (A : Type ℓ) : Type ℓ where
  constructor mkShow
  field show : A → String
open Show ⦃...⦄ public
