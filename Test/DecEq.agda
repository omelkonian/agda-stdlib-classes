{-# OPTIONS --without-K #-}
module Test.DecEq where

open import Class.Prelude
open import Class.DecEq

_ = DecEq ⊤ ∋ it
_ = DecEq Bool ∋ it
_ = DecEq ℕ ∋ it
_ = DecEq ℤ ∋ it
_ = DecEq ℚ ∋ it
_ = DecEq Char ∋ it
_ = DecEq String ∋ it
_ : DecEq¹ Fin; _ = it
_ = DecEq Name ∋ it where open import Reflection.AST.Name
_ = DecEq Literal ∋ it where open import Reflection.AST.Literal
_ = DecEq Meta ∋ it where open import Reflection.AST.Meta
_ = DecEq Term ∋ it where open import Reflection.AST.Term
_ = DecEq Visibility ∋ it where open import Reflection.AST.Argument.Visibility
_ = DecEq Modality ∋ it where open import Reflection.AST.Argument.Modality
_ = DecEq ArgInfo ∋ it where open import Reflection.AST.Argument.Information
