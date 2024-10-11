module Class.Allable.Instance where

open import Class.Prelude
open import Class.Allable.Core

import Data.List.Relation.Unary.All as L
import Data.Vec.Relation.Unary.All as V
import Data.Maybe.Relation.Unary.All as M

instance
  Allable-List : Allable {ℓ} List
  Allable-List .All = L.All

  Allable-Vec : ∀ {n} → Allable {ℓ} (flip Vec n)
  Allable-Vec .All P = V.All P

  Allable-Maybe : Allable {ℓ} Maybe
  Allable-Maybe .All = M.All

private
  open import Class.Decidable
  open import Class.HasOrder

  _ : ∀[ x ∈ List ℕ ∋ 1 ∷ 2 ∷ 3 ∷ [] ] x > 0
  _ = auto

  _ : ∀[ x ∈ just 42 ] x > 0
  _ = auto

  _ : ∀[ x ∈ nothing ] x > 0
  _ = auto

  _ : ¬∀[ x ∈ just 0 ] x > 0
  _ = auto
