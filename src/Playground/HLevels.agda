module Playground.HLevels where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Data.Sigma

private variable
  ℓ : Level

isContr : ∀ (A : Type ℓ) → Type ℓ
isContr A = Σ A λ x → ∀ (y : A) → x ≡ y

isProp : ∀ (A : Type ℓ) → Type ℓ
isProp A = ∀ (x y : A) → x ≡ y

isSet : ∀ (A : Type ℓ) → Type ℓ
isSet A = ∀ (x y : A) → isProp (x ≡ y)

isGroupoid : ∀ (A : Type ℓ) → Type ℓ
isGroupoid A = ∀ (x y : A) → isSet (x ≡ y)
