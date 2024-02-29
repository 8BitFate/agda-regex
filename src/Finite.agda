open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Setoid using (Unique)

module Finite where

AllElements : (A : Set) → List A → Set
AllElements A xs = (x : A) → x ∈ xs

record Finite (A : Set) : Set where
  field
    list : List A
    noDups : Unique (record
                      { Carrier = A
                      ; _≈_ = λ _ _ → A
                      ; isEquivalence =
                          record { refl = λ {x} → x ; sym = λ z → z ; trans = λ _ z → z }
                      }) list
    every : AllElements A list
