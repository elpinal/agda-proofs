module Playground.Homotopy where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Identity

private variable
  ℓ : Level
  A B : Type ℓ
  P : A → Type ℓ

_~_ : ∀ {P : A → Type ℓ} → (f g : (x : A) → P x) → Type (of A ⊔ ℓ)
_~_ {A = A} f g = ∀ (x : A) → f x ≡ g x

~-refl : {f : (x : A) → P x} → f ~ f
~-refl x = refl

~-sym : {f g : (x : A) → P x} → f ~ g → g ~ f
~-sym H x = sym (H x)

~-trans : {f g h : (x : A) → P x} → f ~ g → g ~ h → f ~ h
~-trans H H′ x = trans (H x) (H′ x)

naturality : ∀ {x y : A} {f g : A → B} → (H : f ~ g) → (p : x ≡ y) → H x ∙ ap g p ≡ ap f p ∙ H y
naturality H refl = rUnit _ ∙ sym (lUnit _)

naturalityDep : ∀ {x y : A} {f g : (x : A) → P x} → (H : f ~ g) → (p : x ≡ y)
  → H x ∙ transportFlip p (apd g p) ≡ transportFlip p (apd f p ∙ H y)
naturalityDep H refl = rUnit _ ∙ sym (lUnit _)
