module Class.Anyable.Core where

open import Class.Prelude

record Anyable (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field Any : ∀ {A} → (A → Set) → F A → Set ℓ

  ∃∈-syntax  = Any
  ∃∈-syntax′ = Any
  ∄∈-syntax  = λ {A} P → ¬_ ∘ Any {A} P
  ∄∈-syntax′ = ∄∈-syntax
  infix 2 ∃∈-syntax ∃∈-syntax′ ∄∈-syntax ∄∈-syntax′
  syntax ∃∈-syntax  P         xs = ∃[∈    xs ] P
  syntax ∃∈-syntax′ (λ x → P) xs = ∃[ x ∈ xs ] P
  syntax ∄∈-syntax  P         xs = ∄[∈    xs ] P
  syntax ∄∈-syntax′ (λ x → P) xs = ∄[ x ∈ xs ] P

open Anyable ⦃...⦄ public
