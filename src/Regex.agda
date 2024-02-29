open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module Regex {Σ : Set} (Φ : Finite Σ) (_≟_ : (a : Σ) → (b : Σ) →  Dec ( a ≡ b)) where

infixl 5 _&_
infixl 6 _+_
infixl 7 _∙_
infixl 8 _*

data RegEx : Set where
  ∅   : RegEx
  ε   : RegEx
  ⟦_⟧  : Σ → RegEx  
  _∙_ : RegEx → RegEx → RegEx
  _*  : RegEx → RegEx
  _+_ : RegEx → RegEx → RegEx
  _&_ : RegEx → RegEx → RegEx
  ¬_  : RegEx → RegEx

-- open Φ

open import Data.List using (List; []; [_]; _++_;foldl;dropWhile)

accept : List Σ → RegEx
accept = foldl (λ reg char → reg + ⟦ char ⟧) ∅

φ : RegEx
φ = accept (Finite.list Φ)

I : RegEx -- Universal Set (Accepts every string)-
I = φ *

infixl 8 _⁺

_⁺ : RegEx → RegEx 
_⁺ r = r ∙ r *

open import Relation.Nullary renaming (¬_ to neg)
open import Relation.Nullary.Negation using (¬?)

complement : RegEx → RegEx
complement ∅ = I
complement ε = I ⁺
complement ⟦ c ⟧ = ε + accept ( dropWhile different (Finite.list Φ)) ∙ I where
    different : (x : Σ) → Dec (neg (c ≡ x))
    different x with c ≟ x
    ... | p = ¬? p
complement (l ∙ r) = (complement l) + (l ∙ complement r)
complement (r *) = (complement r) + (r * ∙ (complement r))
complement (l + r) = (complement l) & (complement r)
complement (l & r) = (complement l) + (complement r)
complement (¬ r) = r

infix 1 _~_

data _~_ : RegEx → List Σ → Set where
  eps  : ε ~ []
  chr  : {a : Σ} → ⟦ a ⟧ ~ [ a ]  
  con  : {l r : RegEx}{s t : List Σ} → l ~ s → r ~ t  → l ∙ r ~ s ++ t
  star : {r : RegEx}{s : List Σ} → (ε + r ⁺) ~ s → r * ~ s  
  altl : {l r : RegEx}{s : List Σ} → l ~ s → l + r ~ s
  altr : {l r : RegEx}{s : List Σ} → r ~ s → l + r ~ s
  and  : {l r : RegEx}{s : List Σ} → l ~ s → r ~ s → l & r ~ s
  comp : {r : RegEx}{s : List Σ} → complement r ~ s → ¬ r ~ s




-- ν : (r : RegEx) → RegEx
