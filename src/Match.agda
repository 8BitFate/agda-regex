{-# OPTIONS --sized-types #-}
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module Match {Σ : Set} (Φ : Finite Σ)  where

open import RegEx Φ 
open import SmartConstructor Φ

open import Data.List using (List;[];_∷_;[_];_++_)
-- https://ionathan.ch/2021/08/26/using-sized-types.html
open import Size

infix 1 _~_

data _~_ {i : Size} :  RegEx → List Σ → Set where
  eps  : {j : Size< i} → _~_ {i} ε []
  chr  : {c : Σ}{j : Size< i} → _~_ {i}⟦ c ⟧ [ c ]
  star : {s : List Σ}{r : RegEx}{j : Size< i} → _~_ {j} (ε + r ∙ r *) s → _~_ {i} (r *) s
  con  : {s t : List Σ}{l r : RegEx}{j k : Size< i} → _~_ {j} l s → _~_ {k} r t → _~_ {i} (l ∙ r) (s ++ t)
  altl : {s : List Σ}{l r : RegEx}{j : Size< i} → _~_ {j} l s → _~_ {i} (l + r) s
  altr : {s : List Σ}{l r : RegEx}{j : Size< i} → _~_ {j} r s → _~_ {i} (l + r) s
  and  : {s : List Σ}{l r : RegEx}{j k : Size< i} → _~_ {j} l s → _~_ {k} r s → _~_ {i} (l & r) s

open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_×_;_,_;∃;-,_) renaming (Σ to Sigma)

-- Based on this question: https://stackoverflow.com/questions/29260874/problems-on-data-type-indices-that-uses-list-concatenation
~++ : {r : RegEx}{s : List Σ}{i : Size} → _~_{i} r s → Sigma (List Σ) (λ t → (t ≡ s) × (_~_{i} r t))
~++ m = _ , refl , m
