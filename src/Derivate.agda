open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_)

open import Finite using (Finite)

module Derivate {Σ : Set} (Φ : Finite Σ) where

open Finite.Finite Φ 

open import RegEx Φ
open import SmartConstructor Φ
open import SmartConstructor.Properties Φ
open import Match Φ
open import Match.Properties Φ

open import Relation.Binary.PropositionalEquality using (refl)
open import Data.List using (List;[];_∷_;[_])
open import Data.Sum using (reduce) renaming (map to sumMap)
open import Relation.Nullary using (yes;no)
open import Function using (_∘_)
open import Data.Product using () renaming (proj₁ to fst;proj₂ to snd)


nullable : (r : RegEx) → Dec( r ~ [])
nullable ∅ = no (λ ())
nullable ε = yes eps
nullable ⟦ x ⟧ = no (λ ())
nullable (r *) = yes (star (altl eps))
nullable (l ∙ r) with nullable l | nullable r
... | yes lp | yes rp = yes (con lp rp refl)
... | yes lp | no ¬rp = no (¬rp ∘ snd ∘ ∙~[])
... | no ¬lp | rp = no (¬lp ∘ fst ∘ ∙~[])
nullable (l + r) with nullable l | nullable r
... | yes lp | rp = yes (altl lp)
... | no ¬lp | yes rp = yes (altr rp)
... | no ¬lp | no ¬rp = no (reduce ∘ sumMap ¬lp ¬rp ∘ +~[])
nullable (l & r) with nullable l | nullable r
... | yes lp | yes rp = yes (and lp rp)
... | yes lp | no ¬rp = no (¬rp ∘ snd ∘ &~[])
... | no ¬lp | rp = no (¬lp ∘ fst ∘ &~[])

derivate : Σ → RegEx → RegEx
derivate c ∅ = ∅
derivate c ε = ∅
derivate c ⟦ x ⟧ with c ≟ x
... | yes _ = ε
... | no  _ = ∅
derivate c (r *) = (derivate c r) ∙ˢ (r *ˢ)
derivate c (l + r) = (derivate c l) +ˢ (derivate c r)
derivate c (l ∙ r) with nullable l
... | yes _ = ((derivate c l) ∙ˢ r) +ˢ (derivate c r)
... | no  _ = (derivate c l) ∙ˢ r
derivate c (l & r) = (derivate c l) &ˢ (derivate c r)
