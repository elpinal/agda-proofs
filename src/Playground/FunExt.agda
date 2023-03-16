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

FunExt : Typeω
FunExt = ∀ {ℓ ℓ′ : Level} {A : Type ℓ} (B : A → Type ℓ′) (f g : (x : A) → B x) → isEquiv (happly f g)

FunExt′ : ∀ ℓ ℓ′ → Type (lsuc (ℓ ⊔ ℓ′))
FunExt′ ℓ ℓ′ = ∀ {A : Type ℓ} (P : A → Type ℓ′) (f g : (x : A) → P x) → isEquiv (happly f g)

module _ (e : FunExt) where
  funExt : ∀ (B : A → Type ℓ) (f g : (x : A) → B x) → (∀ (x : A) → f x ≡ g x) → f ≡ g
  funExt B f g = invFun (e B f g)

  funExt2 :
    ∀ (B : A → Type ℓ) (C : (x : A) → B x → Type ℓ′)
      (f g : (x : A) → (y : B x) → C x y)
    → (∀ (x : A) (y : B x) → f x y ≡ g x y)
    → f ≡ g
  funExt2 B C f g k =
    funExt (λ x → ∀ y → C x y) f g
      λ x → funExt (λ y → C x y) (f x) (g x)
        λ y → k x y
