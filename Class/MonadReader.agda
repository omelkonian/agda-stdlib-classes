module Class.MonadReader where

open import Class.Prelude
open import Class.Core
open import Class.Monad
open import Class.Functor
open import Class.MonadError

record MonadReader (R : Type ℓ) (M : Type↑) ⦃ _ : Monad M ⦄ : Typeω where
  field
    ask : M R
    local : ∀ {a} {A : Type a} → (R → R) → M A → M A

  reader : ∀ {a} {A : Type a} → (R → A) → M A
  reader f = f <$> ask
    where instance _ = Functor-M
open MonadReader ⦃...⦄ public

ReaderT : (R : Type) (M : Type↑) → Type↑
ReaderT R M A = R → M A

module _ {R : Type} {M : Type↑} ⦃ _ : Monad M ⦄ where

  Monad-ReaderT : Monad (ReaderT R M)
  Monad-ReaderT = λ where
    .return a → λ r → return a
    ._>>=_ x f r → x r >>= λ a → f a r

  MonadReader-ReaderT : MonadReader R (ReaderT R M) ⦃ Monad-ReaderT ⦄
  MonadReader-ReaderT = λ where
    .ask → return
    .local f x → x ∘ f

  MonadError-ReaderT : ∀ {E : Type ℓ} → ⦃ MonadError E M ⦄ → MonadError E (ReaderT R M)
  MonadError-ReaderT = λ where
    .error e _ → error e
    .catch x h r → catch (x r) (λ e → h e r)
