open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module Match {Σ : Set} (Φ : Finite Σ)  where

open import RegEx Φ 
open import SmartConstructor Φ

open import Data.List using (List;[];_∷_;[_];_++_)

infix 1 _~_

data _~_ : RegEx → List Σ → Set where
  eps  : ε ~ []
  chr  : {c : Σ} → ⟦ c ⟧ ~ [ c ]
  star : {s : List Σ}{r : RegEx} → (ε + r ∙ r *) ~ s → r * ~ s
  con  : {s t u : List Σ}{l r : RegEx} → l ~ s → r ~ t → s ++ t ≡ u → l ∙ r ~ u
  altl : {s : List Σ}{l r : RegEx} → l ~ s → l + r ~ s
  altr : {s : List Σ}{l r : RegEx} → r ~ s → l + r ~ s
  and  : {s : List Σ}{l r : RegEx} → l ~ s → r ~ s → l & r ~ s

open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_×_;_,_;∃;-,_) renaming (Σ to Sigma)

-- Probably not needed with this con definition
-- Based on this question: https://stackoverflow.com/questions/29260874/problems-on-data-type-indices-that-uses-list-concatenation
~++ : {r : RegEx}{s : List Σ} → r ~ s → Sigma (List Σ) (λ t → (t ≡ s) × (r ~ t))
~++ m = _ , refl , m
