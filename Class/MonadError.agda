module Class.MonadError where

open import Class.Prelude
open import Class.Core
open import Class.Monad

record MonadError (E : Type ℓ) (M : Type↑) : Typeω where
  field
    error : E → M A
    catch : M A → (E → M A) → M A
open MonadError ⦃...⦄ public

open import Reflection using (ErrorPart; typeError; catchTC; strErr)

MonadError-TC : MonadError (List ErrorPart) TC
MonadError-TC = λ where
  .error → typeError
  .catch x h → catchTC x (h [ strErr "TC doesn't provide which error to catch" ])

ErrorT : (E : Type) → (M : Type↑) → Type↑
ErrorT E M A = M (E ⊎ A)

module _ {E : Type} {M : Type↑} ⦃ _ : Monad M ⦄ where

  Monad-ErrorT : Monad (ErrorT E M)
  Monad-ErrorT .return a = return (inj₂ a)
  Monad-ErrorT ._>>=_ x f = x >>= λ where
    (inj₁ e) → return (inj₁ e)
    (inj₂ a) → f a

  MonadError-ErrorT : MonadError E (ErrorT E M)
  MonadError-ErrorT .error e = return (inj₁ e)
  MonadError-ErrorT .catch x h = x >>= λ where
    (inj₁ e) → h e
    (inj₂ a) → return (inj₂ a)
