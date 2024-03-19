open import Relation.Nullary using (Dec)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.DecPropositional using (Unique)

module Finite where

AllElements : {A : Set} → List A → Set
AllElements {A} xs = (x : A) → x ∈ xs

record Finite (A : Set) : Set where
  field
    _≟_ : (a : A) → (b : A) → Dec (a ≡ b) 
    list : List A
    noDups : Unique _≟_ list
    every : AllElements list
