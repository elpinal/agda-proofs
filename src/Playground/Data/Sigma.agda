module Playground.Data.Sigma where

open import Agda.Primitive
open import Playground.Types

private variable
  ℓ ℓ′ : Level

record Σ (A : Type ℓ) (B : A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  eta-equality

  constructor _,_

  field
    fst : A
    snd : B fst

open Σ public
