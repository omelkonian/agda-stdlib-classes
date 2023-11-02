module Class.Monoid.Instances where

open import Class.Prelude
open import Class.Semigroup
open import Class.Monoid.Core

instance
  Monoid-List : Monoid (List A)
  Monoid-List .ε = []

  MonoidLaws-List : MonoidLaws≡ (List A)
  MonoidLaws-List .ε-identity = L.++-identityˡ , L.++-identityʳ
    where import Data.List.Properties as L

  Monoid-Vec : Monoid (∃ (Vec A))
  Monoid-Vec .ε = 0 , []

  Monoid-String : Monoid String
  Monoid-String .ε = ""

module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ where instance
  Monoid-Maybe : Monoid (Maybe A)
  Monoid-Maybe .ε = nothing

  MonoidLaws-Maybe : ⦃ MonoidLaws≡ A ⦄ → MonoidLaws≡ (Maybe A)
  MonoidLaws-Maybe .ε-identity = p , q
    where open Alg≡
          p = LeftIdentity ε  _◇_ ∋ λ _ → refl
          q = RightIdentity ε _◇_ ∋ λ where (just _) → refl; nothing → refl

-- ** natural numbers
module _ where
  open import Data.Nat.Properties
  module _ where
    instance _ = Semigroup-ℕ-+
    Monoid-ℕ-+ = Monoid ℕ ∋ λ where .ε → 0
    instance _ = Monoid-ℕ-+
    MonoidLaws-ℕ-+ = MonoidLaws≡ ℕ ∋ record {ε-identity = +-identityˡ , +-identityʳ}
  module _ where
    instance _ = Semigroup-ℕ-*
    Monoid-ℕ-* = Monoid ℕ ∋ λ where .ε → 1
    instance _ = Monoid-ℕ-*
    MonoidLaws-ℕ-* = MonoidLaws≡ ℕ ∋ record {ε-identity = *-identityˡ , *-identityʳ}

-- ** integers
module _ where
  open import Data.Integer.Properties
  module _ where
    instance _ = Semigroup-ℤ-+
    Monoid-ℤ-+ = Monoid ℤ ∋ λ where .ε → 0ℤ
    instance _ = Monoid-ℤ-+
    MonoidLaws-ℤ-+ = MonoidLaws≡ ℤ ∋ record {ε-identity = +-identityˡ , +-identityʳ}
  module _ where
    instance _ = Semigroup-ℤ-*
    Monoid-ℤ-* = Monoid ℤ ∋ λ where .ε → 1ℤ
    instance _ = Monoid-ℤ-*
    MonoidLaws-ℤ-* = MonoidLaws≡ ℤ ∋ record {ε-identity = *-identityˡ , *-identityʳ}

-- ** maybes
module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ ⦃ _ : MonoidLaws≡ A ⦄ (x : A) where
  just-◇ˡ : ∀ (mx : Maybe A) →
    just x ◇ mx ≡ just (x ◇ fromMaybe ε mx)
  just-◇ˡ = λ where
    (just _) → refl
    nothing  → cong just $ sym $ ε-identityʳ≡ x

  just-◇ʳ : ∀ (mx : Maybe A) →
    mx ◇ just x ≡ just (fromMaybe ε mx ◇ x)
  just-◇ʳ = λ where
    (just _) → refl
    nothing  → cong just $ sym $ ε-identityˡ≡ x
