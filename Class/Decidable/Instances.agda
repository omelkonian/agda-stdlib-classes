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
  Dec-⊥ : ⊥ ⁇
  Dec-⊥ .dec = no λ()

  Dec-⊤ : ⊤ ⁇
  Dec-⊤ .dec = yes tt

  open import Relation.Nullary.Decidable as D

  Dec-→ : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A → B) ⁇
  Dec-→ .dec = dec D.→-dec dec

  Dec-× : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A × B) ⁇
  Dec-× .dec = dec D.×-dec dec

  Dec-⊎ : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A ⊎ B) ⁇
  Dec-⊎ .dec = dec D.⊎-dec dec

  DecEq⇒Dec : ⦃ DecEq A ⦄ → _≡_ {A = A} ⁇²
  DecEq⇒Dec .dec = _ ≟ _

  import Data.Bool as 𝔹

  Dec-T : T ⁇¹
  Dec-T .dec = 𝔹.T? _

  import Data.List.Relation.Unary.All as L
  import Data.List.Relation.Unary.Any as L

  Dec-All : ⦃ P ⁇¹ ⦄ → L.All P ⁇¹
  Dec-All .dec = L.all? dec¹ _

  Dec-Any : ⦃ P ⁇¹ ⦄ → L.Any P ⁇¹
  Dec-Any .dec = L.any? dec¹ _

  import Data.List.Relation.Unary.AllPairs as AP

  Dec-AllPairs : ⦃ R ⁇² ⦄ → AP.AllPairs R ⁇¹
  Dec-AllPairs .dec = AP.allPairs? dec² _

  open import Data.Vec as V
  open import Data.Vec.Relation.Unary.All as V
  open import Data.Vec.Relation.Unary.Any as V

  Dec-VAll : ⦃ P ⁇¹ ⦄ → V.All P {n} ⁇¹
  Dec-VAll .dec = V.all? dec¹ _

  Dec-VAny : ⦃ P ⁇¹ ⦄ → V.Any P {n} ⁇¹
  Dec-VAny .dec = V.any? dec¹ _

  import Data.Maybe as M
  import Data.Maybe.Relation.Unary.All as M renaming (dec to all?)
  import Data.Maybe.Relation.Unary.Any as M renaming (dec to any?)

  Dec-MAll : ⦃ P ⁇¹ ⦄ → M.All P ⁇¹
  Dec-MAll .dec = M.all? dec¹ _

  Dec-MAny : ⦃ P ⁇¹ ⦄ → M.Any P ⁇¹
  Dec-MAny .dec = M.any? dec¹ _

  Dec-Is-just : M.Is-just {A = A} ⁇¹
  Dec-Is-just {x = x} .dec with x
  ... | just _  = yes $ M.just _
  ... | nothing = no λ ()

  Dec-Is-nothing : M.Is-nothing {A = A} ⁇¹
  Dec-Is-nothing {x = x} .dec with x
  ... | just _  = no λ where (M.just ())
  ... | nothing = yes M.nothing

  import Data.Sum.Relation.Unary.All as ⊎; open ⊎ using (inj₁; inj₂)
  open import Relation.Nullary.Decidable using () renaming (map′ to mapDec)

  Dec-⊎All : ⦃ P ⁇¹ ⦄ → ⦃ Q ⁇¹ ⦄ → ⊎.All P Q ⁇¹
  Dec-⊎All {P = P} {Q = Q} {x = inj₁ x} .dec = mapDec inj₁ inj₁˘ ¿ P x ¿
    where inj₁˘ : ⊎.All P Q (inj₁ x) → P x
          inj₁˘ (inj₁ x) = x
  Dec-⊎All {P = P} {Q = Q} {x = inj₂ y} .dec = mapDec inj₂ inj₂˘ ¿ Q y ¿
    where inj₂˘ : ⊎.All P Q (inj₂ x) → Q x
          inj₂˘ (inj₂ x) = x
