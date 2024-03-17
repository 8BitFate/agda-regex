module Main where

open import Finite
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.AllPairs
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any

open import Function.Injection

data AB : Set where
 a : AB
 b : AB

_≟_ : (n m : AB) → Dec (n ≡ m)
a ≟ a = yes refl
a ≟ b = no (λ ())
b ≟ a = no (λ ())
b ≟ b = yes refl

every : (x : AB) → Any (_≡_ x) (a ∷ b ∷ [])
every a = here refl
every b = there (here refl)

FiniteAB : Finite AB
FiniteAB = record { eq = _≟_ ; list = a ∷ b ∷ [] ; noDups = ((λ ()) ∷ []) ∷ [] ∷ [] ; every = every }

open import RegEx FiniteAB
open import SmartConstructor FiniteAB
open import Complement FiniteAB
open import Match FiniteAB

test = ⟦ a ⟧ ∙ ⟦ b ⟧

test2 = complement test
