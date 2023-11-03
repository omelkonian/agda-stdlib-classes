module Class.Decidable.Core where

open import Class.Prelude

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

module _ {A : Type ℓ} where

  _⁇¹ : Pred A ℓ′ → Type (ℓ ⊔ ℓ′)
  P ⁇¹ = ∀ {x} → P x ⁇

  dec¹ : {P : Pred A ℓ′} → ⦃ P ⁇¹ ⦄ → Decidable¹ P
  dec¹ _ = dec

  ¿_¿¹ : (P : Pred A ℓ′) → ⦃ P ⁇¹ ⦄ → Decidable¹ P
  ¿ _ ¿¹ = dec¹

module _ {A B : Type ℓ} where

  _⁇² : REL A B ℓ′ → Type (ℓ ⊔ ℓ′)
  _~_ ⁇² = ∀ {x y} → (x ~ y) ⁇

  dec² : {_~_ : REL A B ℓ′} → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
  dec² _ _ = dec

  ¿_¿² : (_~_ : REL A B ℓ′) → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
  ¿ _ ¿² = dec²

module _ {A B C : Type ℓ} where

  _⁇³ : (P : 3REL A B C ℓ′) → Type (ℓ ⊔ ℓ′)
  _~_~_ ⁇³ = ∀ {x y z} → (x ~ y ~ z) ⁇

  dec³ : {_~_~_ : 3REL A B C ℓ′} → ⦃ _~_~_ ⁇³ ⦄ → Decidable³ _~_~_
  dec³ _ _ _ = dec

  ¿_¿³ : (_~_~_ : 3REL A B C ℓ′) → ⦃ _~_~_ ⁇³ ⦄ → Decidable³ _~_~_
  ¿ _ ¿³ = dec³

infix -100 auto∶_
auto∶_ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Type
auto∶_ A = True ¿ A ¿
