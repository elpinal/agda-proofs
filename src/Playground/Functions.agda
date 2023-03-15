module Playground.Functions where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Data.Sigma

private variable
  ℓ ℓ′ : Level
  A B C : Type ℓ
  P : A → Type ℓ

fiber : (f : A → B) → (y : B) → Type (of A ⊔ of B)
fiber {A = A} f y = Σ A λ x → f x ≡ y

happly : (f g : (x : A) → P x) → f ≡ g → ∀ (x : A) → f x ≡ g x
happly {A = A} f .f refl x = refl

_∘_ : (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

id : A → A
id x = x

HasSection : (r : B → A) → Type (of A ⊔ of B)
HasSection {B = B} {A = A} r =
  Σ (A → B) λ s → ∀ (x : A) → r (s x) ≡ x

HasRetraction : (s : A → B) → Type (of A ⊔ of B)
HasRetraction {A = A} {B = B} s =
  Σ (B → A) λ r → ∀ (x : A) → r (s x) ≡ x

-- "A is a retract of B."
--
-- I like this notation, taken from Escardo's lecture notes, because
-- it expresses an intuition that the left hand side is "smaller" than
-- the right hand side.
_◁_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
A ◁ B = Σ (B → A) HasSection

-- "B is a section of A."
_▷_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
B ▷ A = Σ (A → B) HasRetraction

retraction : A ◁ B → B → A
retraction (r , _) = r

section : A ◁ B → A → B
section (_ , (s , _)) = s
