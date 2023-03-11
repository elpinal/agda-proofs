module Playground.Data.Sum where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types

private variable
  ℓ ℓ′ : Level

data _+_ (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  inl : A → A + B
  inr : B → A + B
