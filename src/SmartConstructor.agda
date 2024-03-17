open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module SmartConstructor {Σ : Set} (Φ : Finite Σ) where

open import RegEx Φ

infixl 5 _+ˢ_
infixl 6 _&ˢ_
infixl 7 _∙ˢ_
infixl 8 _*ˢ

_*ˢ :  RegEx → RegEx
∅ *ˢ = ε
ε *ˢ = ε
r *ˢ = r *

_∙ˢ_ : RegEx → RegEx → RegEx
∅ ∙ˢ _ = ∅
_ ∙ˢ ∅ = ∅
ε ∙ˢ r = r
r ∙ˢ ε = r
l ∙ˢ r = l ∙ r

_+ˢ_ : RegEx → RegEx → RegEx
∅ +ˢ r = r
r +ˢ ∅ = r
l +ˢ r = l + r

_&ˢ_ : RegEx → RegEx → RegEx
∅ &ˢ _ = ∅
_ &ˢ ∅ = ∅
l &ˢ r = l & r

