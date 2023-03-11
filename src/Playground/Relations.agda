module Playground.Relations where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Neg
open import Playground.Data.Sum
open import Playground.Data.Sigma

private variable
  ℓ : Level
  A B : Type ℓ

Decidable : (A : Type ℓ) → Type ℓ
Decidable A = A + (¬ A)

isDiscrete : (A : Type ℓ) → Type ℓ
isDiscrete A = ∀ (x y : A) → Decidable (x ≡ y)

WeakConst : (f : A → B) → Type (of A ⊔ of B)
WeakConst {A = A} f = ∀ (x y : A) → f x ≡ f y

ConstOn : (A : Type ℓ) → Type ℓ
ConstOn A = Σ (A → A) WeakConst

PathConstOn : (A : Type ℓ) → Type ℓ
PathConstOn A = ∀ (x y : A) → ConstOn (x ≡ y)
