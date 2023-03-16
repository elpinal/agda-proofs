module Playground.Equivalence where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Functions
open import Playground.HLevels
open import Playground.Data.Sigma

private variable
  ℓ : Level
  A B : Type ℓ
  f : A → B

isEquiv : (f : A → B) → Type (of A ⊔ of B)
isEquiv {B = B} f = ∀ (y : B) → isContr (fiber f y)

invFun : ∀ {f : A → B} (e : isEquiv f) → B → A
invFun e y = e y .fst .fst
