module Playground.Subuniverses.Properties where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Functions
open import Playground.Data.Sigma
open import Playground.Data.Sigma.Properties
open import Playground.HLevels
open import Playground.HLevels.Properties
open import Playground.Identity
open import Playground.FunExt
open import Playground.Relations
open import Playground.Hedberg
open import Playground.Subuniverses
open import Playground.PropUnivalence
open import Playground.Equivalence
open import Playground.Equivalence.Properties

module M {ℓ} {P Q : Type ℓ} (pu : PropUnivalenceForSpecificTypes P Q) (e : FunExtForAllSmallTypes ℓ ℓ)
  (isPropP : isProp P) (isPropQ : isProp Q)
  where
  toLogicalEquiv : P ≡ Q → Σ (P → Q) λ _ → (Q → P)
  toLogicalEquiv refl = id , id

  propPathEndo : P ≡ Q → P ≡ Q
  propPathEndo p = pu isPropP isPropQ (toLogicalEquiv p .fst) (toLogicalEquiv p .snd)

  hPropPathEndo : (P , isPropP) ≡ (Q , isPropQ) → (P , isPropP) ≡ (Q , isPropQ)
  hPropPathEndo p = PathΣ (propPathEndo (ΣPaths p .fst)) (isPropIsProp e _ isPropQ)

  weakConstToLogicalEquiv : WeakConst toLogicalEquiv
  weakConstToLogicalEquiv p q =
    isPropΣ
      (FunExt→IsPropΠ e λ _ → isPropQ)
      (λ _ → FunExt→IsPropΠ e (λ _ → isPropP))
      (toLogicalEquiv p)
      (toLogicalEquiv q)

  weakConstPropPathEndo : WeakConst propPathEndo
  weakConstPropPathEndo p q =
    ap
      (λ (f , g) → pu isPropP isPropQ f g)
      (weakConstToLogicalEquiv p q)

  weakConstHPropPathEndo : WeakConst hPropPathEndo
  weakConstHPropPathEndo p q =
    ap
      (λ r → PathΣ r (isPropIsProp e _ isPropQ))
      (weakConstPropPathEndo (ΣPaths p .fst) (ΣPaths q .fst))

module _ {ℓ} (pu : PropUnivalenceForAllSmallTypes ℓ) (e : FunExtForAllSmallTypes ℓ ℓ) where
  pathConstOnHProp : PathConstOn (hProp ℓ)
  pathConstOnHProp (_ , isPropP) (_ , isPropQ) = hPropPathEndo , weakConstHPropPathEndo
    where open M pu e isPropP isPropQ

  isSetHProp : isSet (hProp ℓ)
  isSetHProp = PathConstOn→isSet pathConstOnHProp
