open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module RegEx {Σ : Set} (Φ : Finite Σ) where

infixl 5 _+_
infixl 6 _&_
infixl 7 _∙_
infixl 8 _*

data RegEx : Set where
  ∅   : RegEx
  ε   : RegEx
  ⟦_⟧  : Σ → RegEx
  _*  : RegEx → RegEx
  _+_ : RegEx → RegEx → RegEx
  _∙_ : RegEx → RegEx → RegEx
  _&_ : RegEx → RegEx → RegEx
