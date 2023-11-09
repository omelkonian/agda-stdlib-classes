module Class.Decidable.Instances where

open import Class.Prelude
open import Class.Decidable.Core
open import Class.DecEq.Core

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

  private variable n : ℕ; P¹ : Pred A ℓ; P² : Rel A ℓ

  Dec-All : ⦃ P¹ ⁇¹ ⦄ → L.All P¹ ⁇¹
  Dec-All .dec = L.all? dec¹ _

  Dec-Any : ⦃ P¹ ⁇¹ ⦄ → L.Any P¹ ⁇¹
  Dec-Any .dec = L.any? dec¹ _

  import Data.List.Relation.Unary.AllPairs as AP

  Dec-AllPairs : ⦃ P² ⁇² ⦄ → AP.AllPairs P² ⁇¹
  Dec-AllPairs .dec = AP.allPairs? dec² _

  open import Data.Vec as V
  open import Data.Vec.Relation.Unary.All as V
  open import Data.Vec.Relation.Unary.Any as V

  Dec-VAll : ⦃ P¹ ⁇¹ ⦄ → V.All P¹ {n} ⁇¹
  Dec-VAll .dec = V.all? dec¹ _

  Dec-VAny : ⦃ P¹ ⁇¹ ⦄ → V.Any P¹ {n} ⁇¹
  Dec-VAny .dec = V.any? dec¹ _

  import Data.Maybe as M
  import Data.Maybe.Relation.Unary.All as M renaming (dec to all?)
  import Data.Maybe.Relation.Unary.Any as M renaming (dec to any?)

  Dec-MAll : ⦃ P¹ ⁇¹ ⦄ → M.All P¹ ⁇¹
  Dec-MAll .dec = M.all? dec¹ _

  Dec-MAny : ⦃ P¹ ⁇¹ ⦄ → M.Any P¹ ⁇¹
  Dec-MAny .dec = M.any? dec¹ _
