module Class.Allable.Core where

open import Class.Prelude

record Allable (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field All : ∀ {A} → (A → Set) → F A → Set ℓ

  ∀∈-syntax   = All
  ∀∈-syntax′  = All
  ¬∀∈-syntax  = λ {A} P → ¬_ ∘ All {A} P
  ¬∀∈-syntax′ = ¬∀∈-syntax
  infix 2 ∀∈-syntax ∀∈-syntax′ ¬∀∈-syntax ¬∀∈-syntax′
  syntax ∀∈-syntax   P         xs = ∀[∈     xs ] P
  syntax ∀∈-syntax′  (λ x → P) xs = ∀[  x ∈ xs ] P
  syntax ¬∀∈-syntax  P         xs = ¬∀[∈    xs ] P
  syntax ¬∀∈-syntax′ (λ x → P) xs = ¬∀[ x ∈ xs ] P

open Allable ⦃...⦄ public
