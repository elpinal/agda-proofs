module Playground.Data.Sigma.Properties where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Identity
open import Playground.Equivalence
open import Playground.HLevels
open import Playground.Functions
open import Playground.Data.Sigma

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : A → Type ℓ

module _ {w w′ : Σ A B} where
  ΣPaths : w ≡ w′ → Σ (fst w ≡ fst w′) (λ p → transport B p (snd w) ≡ snd w′)
  ΣPaths refl = refl , refl

  isEquivΣPaths : isEquiv ΣPaths
  isEquivΣPaths (refl , refl) .fst .fst = refl
  isEquivΣPaths (refl , refl) .fst .snd = refl
  isEquivΣPaths _             .snd (refl , refl) = refl

  PathΣ : (p : fst w ≡ fst w′) → transport B p (snd w) ≡ snd w′ → w ≡ w′
  PathΣ p q = invFun isEquivΣPaths (p , q)

  PathΣisPropSnd : (∀ x → isProp (B x)) → fst w ≡ fst w′ → w ≡ w′
  PathΣisPropSnd isPropB p = PathΣ p (isPropB (fst w′) (transport B p (snd w)) (snd w′))
