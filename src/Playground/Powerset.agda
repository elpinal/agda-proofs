module Playground.Powerset where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Functions
open import Playground.HLevels
open import Playground.Subuniverses
open import Playground.Data.Sigma
open import Playground.FunExt
open import Playground.FunExt.Properties
open import Playground.Subuniverses.Properties
open import Playground.PropUnivalence

private
  variable
    ℓ ℓ′ : Level
    A : Type ℓ

-- A powerset. Its elements are called subsets.
𝒫 : ∀ (A : Type ℓ) ℓ′ → Type (ℓ ⊔ lsuc ℓ′)
𝒫 A ℓ′ = A → hProp ℓ′

_∈_ : ∀ (x : A) (S : 𝒫 A ℓ) → Type ℓ
x ∈ S = S x .fst

isProp∈ : ∀ x (S : 𝒫 A ℓ) → isProp (x ∈ S)
isProp∈ x S = S x .snd

module _
  (e : FunExtForAllSmallTypes ℓ ℓ)
  (e′ : FunExtForAllSmallTypes (of A) (lsuc ℓ))
  (pu : PropUnivalenceForAllSmallTypes ℓ)
  where
  isSet𝒫 : isSet (𝒫 A ℓ)
  isSet𝒫 = FunExt→IsSetΠ e′ λ _ → isSetHProp pu e
