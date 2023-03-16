module Playground.Equivalence.Properties where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Identity
open import Playground.Functions
open import Playground.HLevels
open import Playground.HLevels.Properties
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

isContr→isEquiv : isContr A → isContr B → (f : A → B) → isEquiv f
isContr→isEquiv isContrA isContrB f y .fst .fst = fst isContrA
isContr→isEquiv isContrA isContrB f y .fst .snd = isContr→isProp isContrB _ y
isContr→isEquiv isContrA isContrB f y .snd (a , p) = PathΣ (snd isContrA a) (isProp→isSet (isContr→isProp isContrB) (f a) y _ p)
