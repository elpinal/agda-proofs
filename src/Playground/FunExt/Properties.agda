module Playground.FunExt.Properties where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Data.Sigma
open import Playground.Data.Sigma.Properties
open import Playground.Data.Empty
open import Playground.Neg
open import Playground.HLevels
open import Playground.HLevels.Properties
open import Playground.FunExt
open import Playground.Identity
open import Playground.Functions
open import Playground.Equivalence
open import Playground.Equivalence.Properties
open import Playground.Fibration
open import Playground.Homotopy

private variable
  ℓ ℓ′ : Level
  A B : Type ℓ
  P : A → Type ℓ

IsContrΠ→FunExt′ : IsContrΠ ℓ ℓ′ → FunExt′ ℓ ℓ′
IsContrΠ→FunExt′ c P f = isEquivTotal→isFiberwiseEquiv (happly f) e
  where
    isContrDom : isContr (Σ (∀ x → P x) λ g → f ≡ g)
    isContrDom = isContrΣ≡ f

    isContrCod : isContr (Σ (∀ x → P x) λ g → f ~ g)
    isContrCod = isContrRetract (c (λ x → isContrΣ≡ (f x))) (ΠΣ→ΣΠ {C = λ x Px → f x ≡ Px} , isEquiv→HasSection Π-distrib-Σ)

    e : isEquiv {A = Σ (∀ x → P x) λ g → f ≡ g} {B = Σ (∀ x → P x) λ g → f ~ g} (totalMap (happly f))
    e y = isContr→isEquiv isContrDom isContrCod (totalMap (happly f)) y
