module Class.Monad.Instances where

open import Class.Prelude
open import Class.Monad.Core

instance
  Monad-TC : Monad TC
  Monad-TC = record {R}
    where import Reflection as R

  Monad-List : Monad List
  Monad-List = λ where
    .return → _∷ []
    ._>>=_  → flip concatMap

  Monad-Maybe : Monad Maybe
  Monad-Maybe = λ where
    .return → just
    ._>>=_  → Maybe._>>=_
   where import Data.Maybe as Maybe
