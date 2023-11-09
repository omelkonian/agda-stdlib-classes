module Class.Decidable.Core where

open import Class.Prelude
open import Class.Core

open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

record _⁇ (P : Type ℓ) : Type ℓ where
  constructor ⁇_
  field dec : Dec P

  auto : ⦃ True dec ⦄ → P
  auto ⦃ pr ⦄ = toWitness pr

  contradict : ∀ {X : Type} {pr : False dec} → P → X
  contradict {pr = pr} = ⊥-elim ∘ toWitnessFalse pr

open _⁇ ⦃ ... ⦄ public

¿_¿ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Dec X
¿ _ ¿ = dec

_⁇¹ = _⁇ ¹
_⁇² = _⁇ ²
_⁇³ = _⁇ ³

module _ {A : Type ℓ} where

  dec¹ : {P : Pred A ℓ′} → ⦃ P ⁇¹ ⦄ → Decidable¹ P
  dec¹ _ = dec

  ¿_¿¹ : (P : Pred A ℓ′) → ⦃ P ⁇¹ ⦄ → Decidable¹ P
  ¿ _ ¿¹ = dec¹

module _ {A B : Type ℓ} where

  dec² : {_~_ : REL A B ℓ′} → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
  dec² _ _ = dec

  ¿_¿² : (_~_ : REL A B ℓ′) → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
  ¿ _ ¿² = dec²

module _ {A B C : Type ℓ} where

  dec³ : {_~_~_ : 3REL A B C ℓ′} → ⦃ _~_~_ ⁇³ ⦄ → Decidable³ _~_~_
  dec³ _ _ _ = dec

  ¿_¿³ : (_~_~_ : 3REL A B C ℓ′) → ⦃ _~_~_ ⁇³ ⦄ → Decidable³ _~_~_
  ¿ _ ¿³ = dec³

infix -100 auto∶_
auto∶_ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Type
auto∶_ A = True ¿ A ¿
