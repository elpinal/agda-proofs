module Playground.Neg where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Data.Empty

private variable
  ℓ : Level

¬_ : (A : Type ℓ) → Type ℓ
¬ A = A → ⊥
