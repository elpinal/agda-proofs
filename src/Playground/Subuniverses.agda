module Playground.Subuniverses where

open import Agda.Primitive
open import Playground.Types
open import Playground.Data.Sigma
open import Playground.HLevels

hProp : ∀ ℓ → Type (lsuc ℓ)
hProp ℓ = Σ (Type ℓ) isProp

hSet : ∀ ℓ → Type (lsuc ℓ)
hSet ℓ = Σ (Type ℓ) isSet
