module Playground.Types where

open import Agda.Primitive

Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ

Typeω : Setω1
Typeω = Setω

of : ∀ {ℓ : Level} → Type ℓ → Level
of {ℓ} _ = ℓ
