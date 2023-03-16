module Playground.Equivalence.Properties where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Functions
open import Playground.HLevels
open import Playground.Data.Sigma
open import Playground.Data.Sigma.Properties
open import Playground.Equivalence

private variable
  ℓ : Level
  A B : Type ℓ
  f : A → B

isEquiv→HasSection : isEquiv f → HasSection f
isEquiv→HasSection e = invFun e , λ y → e y .fst .snd

isEquiv→HasSectionInvFun : (e : isEquiv f) → HasSection (invFun e)
isEquiv→HasSectionInvFun {f = f} e = f , k
  where
    k : ∀ x → invFun e (f x) ≡ x
    k x = ΣPaths (e (f x) .snd (x , refl)) .fst
