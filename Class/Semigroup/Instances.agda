{-# OPTIONS --without-K #-}
module Class.Semigroup.Instances where

open import Class.Prelude
open import Class.Semigroup.Core

instance
  Semigroup-List : Semigroup (List A)
  Semigroup-List ._◇_ = _++_

  Semigroup-List⁺ : Semigroup (List⁺ A)
  Semigroup-List⁺ ._◇_ = _⁺++⁺_

  Semigroup-∃Vec : Semigroup (∃ (Vec A))
  Semigroup-∃Vec ._◇_ (_ , v) (_ , v′) = _ , (v V.++ v′)
    where import Data.Vec as V

  Semigroup-String : Semigroup String
  Semigroup-String ._◇_ = Str._++_
    where import Data.String as Str

  Semigroup-Maybe : ⦃ Semigroup A ⦄ → Semigroup (Maybe A)
  Semigroup-Maybe ._◇_ = λ where
    (just x) (just y) → just (x ◇ y)
    (just x) nothing  → just x
    nothing  m        → m

  SemigroupLaws-Maybe : ⦃ _ : Semigroup A ⦄ → ⦃ SemigroupLaws≡ A ⦄
    → SemigroupLaws≡ (Maybe A)
  SemigroupLaws-Maybe {A = A} = λ where
    .◇-assocʳ → λ where
      (just _) (just _) (just _) → cong just (◇-assocʳ _ _ _)
      (just _) (just _) nothing  → refl
      (just _) nothing  _        → refl
      nothing  (just _) _        → refl
      nothing  nothing  _        → refl
    .◇-comm → λ where
      (just x) (just y) → cong just (◇-comm x y)
      (just _) nothing  → refl
      nothing  (just _) → refl
      nothing  nothing  → refl
   where open Alg≡

-- ** natural numbers
module _ where
  open import Data.Nat
  open import Data.Nat.Properties

  Semigroup-ℕ-+ = Semigroup ℕ ∋ λ where ._◇_ → _+_
  SemigroupLaws-ℕ-+ = SemigroupLaws ℕ _≡_ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℕ-+

  Semigroup-ℕ-* = Semigroup ℕ ∋ λ where ._◇_ → _*_
  SemigroupLaws-ℕ-* = SemigroupLaws ℕ _≡_ ∋
    record {◇-assocʳ = *-assoc; ◇-comm = *-comm}
    where instance _ = Semigroup-ℕ-*

-- ** integers
module _ where
  open import Data.Integer
  open import Data.Integer.Properties

  Semigroup-ℤ-+ = Semigroup ℤ ∋ λ where ._◇_ → _+_
  SemigroupLaws-ℤ-+ = SemigroupLaws ℤ _≡_ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℤ-+

  Semigroup-ℤ-* = Semigroup ℤ ∋ λ where ._◇_ → _*_
  SemigroupLaws-ℤ-* = SemigroupLaws ℤ _≡_ ∋
    record {◇-assocʳ = *-assoc; ◇-comm = *-comm}
    where instance _ = Semigroup-ℤ-*
