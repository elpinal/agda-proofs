module Playground.Data.Empty where

open import Agda.Primitive
open import Playground.Types

private variable
  ℓ : Level
  A : Type ℓ

data ⊥ : Type lzero where

⊥-rec : ⊥ → A
⊥-rec ()
