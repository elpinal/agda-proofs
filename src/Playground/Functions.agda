module Playground.Functions where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Data.Sigma

private variable
  ℓ : Level
  A B : Type ℓ
  C : A → Type ℓ

fiber : (f : A → B) → (y : B) → Type (of A ⊔ of B)
fiber {A = A} f y = Σ A λ x → f x ≡ y

happly : (f g : (x : A) → C x) → f ≡ g → ∀ (x : A) → f x ≡ g x
happly {A = A} f .f refl x = refl
