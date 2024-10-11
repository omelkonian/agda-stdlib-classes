module Class.Anyable.Instance where

open import Class.Prelude
open import Class.Anyable.Core

import Data.List.Relation.Unary.Any as L
import Data.Vec.Relation.Unary.Any as V
import Data.Maybe.Relation.Unary.Any as M

instance
  Anyable-List : Anyable {ℓ} List
  Anyable-List .Any = L.Any

  Anyable-Vec : ∀ {n} → Anyable {ℓ} (flip Vec n)
  Anyable-Vec .Any P = V.Any P

  Anyable-Maybe : Anyable {ℓ} Maybe
  Anyable-Maybe .Any = M.Any

private
  open import Class.Decidable
  open import Class.HasOrder

  _ : ∃[ x ∈ List ℕ ∋ 1 ∷ 2 ∷ 3 ∷ [] ] x > 0
  _ = auto

  _ : ∃[ x ∈ just 42 ] x > 0
  _ = auto

  _ : ∄[ x ∈ nothing ] x > 0
  _ = auto
