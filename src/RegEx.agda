open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module RegEx {Σ : Set} (Φ : Finite Σ) (_≟_ : (a : Σ) → (b : Σ) →  Dec ( a ≡ b)) where

infixl 5 _+_
infixl 6 _&_
infixl 7 _∙_
infixl 8 _*
infixl 9 ¬_

data RegEx : Set where
  ∅   : RegEx
  ε   : RegEx
  ⟦_⟧  : Σ → RegEx
  _*  : RegEx → RegEx
  ¬_  : RegEx → RegEx
  _∙_ : RegEx → RegEx → RegEx
  _+_ : RegEx → RegEx → RegEx
  _&_ : RegEx → RegEx → RegEx

