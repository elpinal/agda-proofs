module Playground.Identity where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types

private variable
  ℓ : Level
  A B : Type ℓ
  P : A → Type ℓ

  x y z : A

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

infixl 6 _∙_
_∙_ = trans

assoc : x ∙ y ∙ z ≡ x ∙ (y ∙ z)
assoc {x = refl} {y = refl} {z = refl} = refl

transport : (P : A → Type ℓ) → x ≡ y → P x → P y
transport _ refl Px = Px

lUnit : (p : x ≡ y) → trans refl p ≡ p
lUnit refl = refl

rUnit : (p : x ≡ y) → trans p refl ≡ p
rUnit refl = refl

symInvolutive : (p : x ≡ y) → sym (sym p) ≡ p
symInvolutive refl = refl

lInv : (p : x ≡ y) → trans (sym p) p ≡ refl
lInv refl = refl

rInv : (p : x ≡ y) → trans p (sym p) ≡ refl
rInv refl = refl

-- Judgmental computation rule.
transportRefl : (a : P x) → transport P refl a ≡ a
transportRefl _ = refl

ap : (f : A → B) → (p : x ≡ y) → f x ≡ f y
ap _ refl = refl

apd : (f : (x : A) → P x) → (p : x ≡ y) → transport P p (f x) ≡ f y
apd _ refl = refl

transportPathCodomain :
  ∀ {a : A} (p : x ≡ y) (q : a ≡ x)
  → transport (λ x → a ≡ x) p q ≡ trans q p
transportPathCodomain refl q = sym (rUnit q)

infix 4 _∎
_∎ : (x : A) → x ≡ x
x ∎ = refl

infixr 3 _≡⟨⟩_
_≡⟨⟩_ : (x : A) → x ≡ y → x ≡ y
x ≡⟨⟩ p = p

infixr 3 _≡⟨_⟩_
_≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

infixr 3 _≡˘⟨_⟩_
_≡˘⟨_⟩_ : (x : A) → y ≡ x → y ≡ z → x ≡ z
x ≡˘⟨ p ⟩ q = sym p ∙ q

infix 2 begin_
begin_ : x ≡ y → x ≡ y
begin p = p
