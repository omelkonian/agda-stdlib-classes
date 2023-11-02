module Class.Functor.Instances where

open import Class.Prelude
open import Class.Functor.Core

instance
  Functor-Maybe : Functor Maybe
  Functor-Maybe = record {M}
    where import Data.Maybe as M renaming (map to _<$>_)

  FunctorLaws-Maybe : FunctorLaws Maybe
  FunctorLaws-Maybe = λ where
    .fmap-id → λ where (just _) → refl; nothing → refl
    .fmap-∘  → λ where (just _) → refl; nothing → refl

  Functor-List : Functor List
  Functor-List ._<$>_ = map

  FunctorLaws-List : FunctorLaws List
  FunctorLaws-List = record {fmap-id = p; fmap-∘ = q}
    where
      p : ∀ {A : Type ℓ} (x : List A) → fmap id x ≡ x
      p = λ where
        [] → refl
        (x ∷ xs) → cong (x ∷_) (p xs)

      q : ∀ {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {f : B → C} {g : A → B} (x : List A) →
        fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
      q {f = f}{g} = λ where
        [] → refl
        (x ∷ xs) → cong (f (g x) ∷_) (q xs)

  Functor-List⁺ : Functor List⁺
  Functor-List⁺ = record {L}
    where import Data.List.NonEmpty as L renaming (map to _<$>_)

  Functor-Vec : ∀ {n} → Functor (flip Vec n)
  Functor-Vec = record {V}
    where import Data.Vec as V renaming (map to _<$>_)

  open import Reflection
  open import Reflection.Meta

  Functor-TC : Functor TC
  Functor-TC = record {R}
    where import Reflection.TypeChecking.Monad.Syntax as R

  Functor-Abs : Functor Abs
  Functor-Abs = record {R}
    where import Reflection.Abstraction as R renaming (map to _<$>_)

  Functor-Arg : Functor Arg
  Functor-Arg = record {R}
    where import Reflection.Argument as R renaming (map to _<$>_)

  Functor-∃Vec : Functor (∃ ∘ Vec)
  Functor-∃Vec ._<$>_ f (_ , xs) = -, (f <$> xs)

_ = fmap suc (just 0) ≡ just 1
  ∋ refl
_ = fmap suc (List ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  ∋ refl
_ = fmap suc (List⁺ ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  ∋ refl
_ = fmap suc (Vec ℕ 3 ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  ∋ refl
_ = fmap suc (∃ (Vec ℕ) ∋ -, 0 ∷ 1 ∷ 2 ∷ []) ≡ (-, 1 ∷ 2 ∷ 3 ∷ [])
  ∋ refl
