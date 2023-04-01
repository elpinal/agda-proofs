module Playground.PropUnivalence where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Data.Sigma
open import Playground.Data.Sigma.Properties using (PathΣ)
open import Playground.HLevels
open import Playground.HLevels.Properties
open import Playground.Identity
open import Playground.Equivalence

private variable
  ℓ : Level
  P Q : Type ℓ

logicallyEquivProps→equiv : isProp P → isProp Q
  → (f : P → Q) → (g : Q → P)
  → isEquiv f
logicallyEquivProps→equiv isPropP isPropQ f g y .fst = g y , isPropQ (f (g y)) y
logicallyEquivProps→equiv isPropP isPropQ f g y .snd (x , p) =
  PathΣ (isPropP (g y) x) (isProp→isSet isPropQ (f x) y (transport (λ x₁ → f x₁ ≡ y) (isPropP (g y) x) (isPropQ (f (g y)) y)) p)

PropUnivalenceForSpecificTypes : ∀ (P Q : Type ℓ) → Type (lsuc ℓ)
PropUnivalenceForSpecificTypes P Q = isProp P → isProp Q → (P → Q) → (Q → P) → P ≡ Q

PropUnivalenceForAllSmallTypes : ∀ ℓ → Type (lsuc ℓ)
PropUnivalenceForAllSmallTypes ℓ = ∀ {P Q : Type ℓ} → PropUnivalenceForSpecificTypes P Q

PropUnivalenceForAllTypes : Typeω
PropUnivalenceForAllTypes = ∀ {ℓ} → PropUnivalenceForAllSmallTypes ℓ
