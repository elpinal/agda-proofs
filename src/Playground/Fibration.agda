module Playground.Fibration where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Identity
open import Playground.HLevels
open import Playground.HLevels.Properties using (isContrRetract)
open import Playground.Functions
open import Playground.Equivalence
open import Playground.Equivalence.Properties
open import Playground.Data.Sigma
open import Playground.Data.Sigma.Properties

private variable
  ℓ ℓ′ : Level
  A B : Type ℓ
  P Q : A → Type ℓ

-- A fiberwise map, or a fiberwise transformation from P to Q.
FiberwiseMap : (P : A → Type ℓ) (Q : A → Type ℓ′) → Type (of A ⊔ ℓ ⊔ ℓ′)
FiberwiseMap P Q = ∀ x → P x → Q x

isFiberwiseEquiv : ∀ {P : A → Type ℓ} {Q : A → Type ℓ′} → (f : FiberwiseMap P Q) → Type (of A ⊔ ℓ ⊔ ℓ′)
isFiberwiseEquiv f = ∀ x → isEquiv (f x)

totalMap : FiberwiseMap P Q → Σ A P → Σ A Q
totalMap m ( x , y ) = x , m x y

fiberOfFiberwiseMap : ∀ (x : A) (v : Q x) → (f : FiberwiseMap P Q) → fiber (totalMap f) (x , v) → fiber (f x) v
fiberOfFiberwiseMap _ _ f ((a , b) , refl) = b , refl

isEquivFiberOfFiberwiseMap : ∀ {x : A} {v : Q x} (f : FiberwiseMap P Q) → isEquiv (fiberOfFiberwiseMap x v f)
isEquivFiberOfFiberwiseMap {x = x} f (Px , b) .fst .fst = ((x , Px) , ap (x ,_) b)
isEquivFiberOfFiberwiseMap {x = x} f (Px , refl) .fst .snd = refl
isEquivFiberOfFiberwiseMap {x = .a} f (_ , _) .snd (((a , Pa) , refl) , refl) = refl

fiberOfTotalMap : ∀ (x : A) (v : Q x) → (f : FiberwiseMap P Q) → fiber (f x) v → fiber (totalMap f) (x , v)
fiberOfTotalMap _ _ f = invFun (isEquivFiberOfFiberwiseMap f)

module _ {P : A → Type ℓ} {Q : A → Type ℓ′} (f : FiberwiseMap P Q) where
  isFiberwiseEquiv→isEquivTotal : isFiberwiseEquiv f → isEquiv (totalMap f)
  isFiberwiseEquiv→isEquivTotal fe (x , v) = isContrRetract (fe x v) r
    where
      r : fiber (totalMap f) (x , v) ◁ fiber (f x) v
      r = fiberOfTotalMap _ _ f , isEquiv→HasSectionInvFun (isEquivFiberOfFiberwiseMap f)

  isEquivTotal→isFiberwiseEquiv : isEquiv (totalMap f) → isFiberwiseEquiv f
  isEquivTotal→isFiberwiseEquiv e x v = isContrRetract (e (x , v)) r
    where
      r : fiber (f x) v ◁ fiber (totalMap f) (x , v)
      r = fiberOfFiberwiseMap _ _ f , isEquiv→HasSection (isEquivFiberOfFiberwiseMap f)

