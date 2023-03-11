-- See "Notions of Anonymous Existence in Martin-Löf Type Theory" by Kraus et al.
--   https://doi.org/10.23638/LMCS-13(1:15)2017
module Playground.Hedberg where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Playground.Types
open import Playground.Neg
open import Playground.Data.Empty
open import Playground.Data.Sigma
open import Playground.Data.Sum
open import Playground.HLevels
open import Playground.Relations
open import Playground.Identity

private variable
  ℓ : Level
  A : Type ℓ

isDiscrete→PathConstOn : isDiscrete A → PathConstOn A
isDiscrete→PathConstOn disc x y with disc x y
... | inl p = (λ _ → p) , λ _ _ → refl
... | inr k = (λ p → ⊥-rec (k p)) , λ p _ → ⊥-rec (k p)

PathConstOn→isSet : PathConstOn A → isSet A
PathConstOn→isSet c x y p q = trans (transport (P p) (c x y .snd p q) (f p)) (sym (f q))
  where
    P : x ≡ y → x ≡ y → Type _
    P r s = r ≡ trans (sym (c x x .fst refl)) s

    f : ∀ (r : x ≡ y) → P r (c x y .fst r)
    f r with r
    ... | refl = sym (lInv (c x x .fst refl))

isDiscrete→isSet : isDiscrete A → isSet A
isDiscrete→isSet disc = PathConstOn→isSet (isDiscrete→PathConstOn disc)

--------------------------------------------------------------------------------

isSet→PathConstOn : isSet A → PathConstOn A
isSet→PathConstOn _ _ _ .fst p = p
isSet→PathConstOn isSetA x y .snd p q = isSetA x y p q
