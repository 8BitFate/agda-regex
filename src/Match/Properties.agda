{-# OPTIONS --sized-types #-}

open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module Match.Properties {Σ : Set} (Φ : Finite Σ)  where

open import Data.List using (List;[];_++_)
open import Relation.Nullary
open import Data.Sum using (_⊎_) renaming (inj₁ to left;inj₂ to right)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_×_;_,_;∃;-,_) renaming (Σ to Sigma)


open import RegEx Φ 
open import Match Φ

∅~ : {s : List Σ} → ¬(∅ ~ s)
∅~ ()

ε~ : {s : List Σ} → ε ~ s → s ≡ []
ε~ eps = refl

⟦_⟧~[] : {c : Σ} → ¬(⟦ c ⟧ ~ [])
⟦_⟧~[] ()

∙~[] : {l r : RegEx} → _∙_ l r ~ [] → ((l ~ []) × (r ~ []))
∙~[] {l}{r} m with ~++ m
... | _ , _ , con {[]} {[]} ml mr = ml , mr

+~[] : {l r : RegEx} → l + r ~ [] → (l ~ []) ⊎ (r ~ [])
+~[] (altl m) = left m
+~[] (altr m) = right m

&~[] : {l r : RegEx} → l & r ~ [] → ((l ~ []) × (r ~ []))
&~[] (and l r) = l , r
