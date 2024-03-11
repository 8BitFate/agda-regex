open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module SmartConstructor {Σ : Set} (Φ : Finite Σ) (_≟_ : (a : Σ) → (b : Σ) →  Dec ( a ≡ b)) where

open import RegEx Φ _≟_

infixl 5 _+ˢ_
infixl 6 _&ˢ_
infixl 7 _∙ˢ_
infixl 8 _*ˢ

_*ˢ :  RegEx → RegEx
∅ *ˢ = ε
ε *ˢ = ε
r *ˢ = r *

¬ˢ_ : RegEx → RegEx
¬ˢ (¬ r) = r
¬ˢ r = ¬ r

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


open import Data.List using (List;_∷_;[];foldr;dropWhile)

accept : List Σ → RegEx
accept = foldr (λ char reg → ⟦ char ⟧ +ˢ reg) ∅

σ : RegEx
σ = accept (Finite.list Φ)

Ι : RegEx -- Universal Set (Accepts every string)
Ι = σ *

infixl 8 _⁺

_⁺ : RegEx → RegEx 
_⁺ r = r ∙ r *

complement : RegEx → RegEx
complement ∅ = Ι
complement ε = σ ⁺
complement ⟦ c ⟧ = ε + (accept (dropWhile (_≟_ c) (Finite.list Φ))) ∙ˢ Ι
complement (r *) = (r *ˢ ∙ˢ(complement r))
complement (¬ r) = r
complement (l ∙ r) = (complement l) +ˢ (l ∙ˢ complement r)
complement (l + r) = (complement l) &ˢ (complement r)
complement (l & r) = (complement l) +ˢ (complement r)
