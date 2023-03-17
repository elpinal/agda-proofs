module Playground.FunExt where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Functions
open import Playground.Equivalence

private variable
  ℓ ℓ′ : Level
  A B : Type ℓ
  C : A → Type ℓ

FunExtForSpecificTypes : ∀ (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
FunExtForSpecificTypes A B = ∀ (f g : (x : A) → B x) → isEquiv (happly f g)

FunExtForAllSmallTypes : ∀ ℓ ℓ′ → Type (lsuc (ℓ ⊔ ℓ′))
FunExtForAllSmallTypes ℓ ℓ′ = ∀ {A : Type ℓ} (B : A → Type ℓ′) → FunExtForSpecificTypes A B

FunExtForAllTypes : Typeω
FunExtForAllTypes = ∀ {ℓ ℓ′ : Level} → FunExtForAllSmallTypes ℓ ℓ′

module _ (e : FunExtForSpecificTypes A C) where
  funExt : (f g : (x : A) → C x) → (∀ (x : A) → f x ≡ g x) → f ≡ g
  funExt f g = invFun (e f g)

module _ (e : FunExtForAllSmallTypes ℓ ℓ) where
  -- This definition requires A, B, and C to live in the same universe.
  funExt2′ :
    ∀ {A : Type ℓ} (B : A → Type ℓ) (C : (x : A) → B x → Type ℓ)
      (f g : (x : A) → (y : B x) → C x y)
    → (∀ (x : A) (y : B x) → f x y ≡ g x y)
    → f ≡ g
  funExt2′ {A = A} B C f g k =
    funExt (e (λ x → ∀ y → C x y)) f g
      λ x → funExt (e (λ y → C x y)) (f x) (g x)
        λ y → k x y

module _ (e : FunExtForAllTypes) where
  funExt2 :
    ∀ (B : A → Type ℓ) (C : (x : A) → B x → Type ℓ′)
      (f g : (x : A) → (y : B x) → C x y)
    → (∀ (x : A) (y : B x) → f x y ≡ g x y)
    → f ≡ g
  funExt2 B C f g k =
    funExt (e (λ x → ∀ y → C x y)) f g
      λ x → funExt (e (λ y → C x y)) (f x) (g x)
        λ y → k x y
