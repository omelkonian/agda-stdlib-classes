{-# OPTIONS --without-K #-}
module Class.Decidable.Instances where

open import Class.Prelude
open import Class.Decidable.Core
open import Class.DecEq.Core

private variable
  n : ℕ
  x : A
  P Q : Pred A ℓ
  R : Rel A ℓ

instance

  -- ** deriving from DecEq
  DecEq⇒Dec : ⦃ DecEq A ⦄ → _≡_ {A = A} ⁇²
  DecEq⇒Dec = ⁇² _≟_

  -- ** basic type formers

  Dec-⊥ : ⊥ ⁇
  Dec-⊥ .dec = no λ()

  Dec-⊤ : ⊤ ⁇
  Dec-⊤ .dec = yes tt

  open import Relation.Nullary.Decidable as D

  Dec-→ : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A → B) ⁇
  Dec-→ .dec = dec D.→-dec dec

  -- ** products

  Dec-× : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A × B) ⁇
  Dec-× .dec = dec D.×-dec dec

  -- ** sums

  Dec-⊎ : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A ⊎ B) ⁇
  Dec-⊎ .dec = dec D.⊎-dec dec

  import Data.Sum.Relation.Unary.All as ⊎; open ⊎ using (inj₁; inj₂)
  open import Relation.Nullary.Decidable using () renaming (map′ to mapDec)

  Dec-⊎All : ⦃ P ⁇¹ ⦄ → ⦃ Q ⁇¹ ⦄ → ⊎.All P Q ⁇¹
  Dec-⊎All {P = P} {Q = Q} {x = inj₁ x} .dec = mapDec inj₁ inj₁˘ ¿ P x ¿
    where inj₁˘ : ⊎.All P Q (inj₁ x) → P x
          inj₁˘ (inj₁ x) = x
  Dec-⊎All {P = P} {Q = Q} {x = inj₂ y} .dec = mapDec inj₂ inj₂˘ ¿ Q y ¿
    where inj₂˘ : ⊎.All P Q (inj₂ x) → Q x
          inj₂˘ (inj₂ x) = x

  import Data.Bool as 𝔹

  Dec-T : T ⁇¹
  Dec-T = ⁇¹ 𝔹.T?

  import Data.List.Relation.Unary.All as L
  import Data.List.Relation.Unary.Any as L

  Dec-All : ⦃ P ⁇¹ ⦄ → L.All P ⁇¹
  Dec-All = ⁇¹ L.all? dec¹

  Dec-Any : ⦃ P ⁇¹ ⦄ → L.Any P ⁇¹
  Dec-Any = ⁇¹ L.any? dec¹

  import Data.List.Relation.Unary.AllPairs as AP

  Dec-AllPairs : ⦃ R ⁇² ⦄ → AP.AllPairs R ⁇¹
  Dec-AllPairs = ⁇¹ AP.allPairs? dec²

  open import Data.Vec as V
  open import Data.Vec.Relation.Unary.All as V
  open import Data.Vec.Relation.Unary.Any as V

  Dec-VAll : ⦃ P ⁇¹ ⦄ → V.All P {n} ⁇¹
  Dec-VAll = ⁇¹ V.all? dec¹

  Dec-VAny : ⦃ P ⁇¹ ⦄ → V.Any P {n} ⁇¹
  Dec-VAny = ⁇¹ V.any? dec¹

  import Data.Maybe as M
  import Data.Maybe.Relation.Unary.All as M renaming (dec to all?)
  import Data.Maybe.Relation.Unary.Any as M renaming (dec to any?)

  Dec-MAll : ⦃ P ⁇¹ ⦄ → M.All P ⁇¹
  Dec-MAll = ⁇¹ M.all? dec¹

  Dec-MAny : ⦃ P ⁇¹ ⦄ → M.Any P ⁇¹
  Dec-MAny = ⁇¹ M.any? dec¹

  -- ** inequalities

  import Data.Nat.Properties as ℕ

  ℕ-Dec-≤ = ⁇² ℕ._≤?_
  ℕ-Dec-< = ⁇² ℕ._<?_

  import Data.Integer.Properties as ℤ

  ℤ-Dec-≤ = ⁇² ℤ._≤?_
  ℤ-Dec-< = ⁇² ℤ._<?_

  import Data.Rational.Properties as Rat

  ℚ-Dec-≤ = ⁇² Rat._≤?_
  ℚ-Dec-< = ⁇² Rat._<?_
