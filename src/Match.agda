open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module Match {Σ : Set} (Φ : Finite Σ) (_≟_ : (a : Σ) → (b : Σ) →  Dec ( a ≡ b)) where

open import RegEx Φ _≟_
open import SmartConstructor Φ _≟_ 

open import Data.List using (List;[];_∷_;[_];_++_)

infix 1 _~_

data _~_ : RegEx → List Σ → Set where
  eps  : ε ~ []
  chr  : {c : Σ} → ⟦ c ⟧ ~ [ c ]  
  star : {s : List Σ}{r : RegEx} → (ε + r ∙ r *) ~ s → r * ~ s
  comp : {s : List Σ}{r : RegEx} → complement r ~ s → ¬ r ~ s
  con  : {s t : List Σ}{l r : RegEx} → l ~ s → r ~ t → l ∙ r ~ s ++ t
  altl : {s : List Σ}{l r : RegEx} → l ~ s → l + r ~ s
  altr : {s : List Σ}{l r : RegEx} → r ~ s → l + r ~ s
  and  : {s : List Σ}{l r : RegEx} → l ~ s → r ~ s → l & r ~ s 

open import Relation.Nullary renaming (¬_ to ¬ᵗ_) 

∅~ : {s : List Σ} → ¬ᵗ(∅ ~ s)
∅~ = λ ()

open import Relation.Binary.PropositionalEquality using (refl)

ε~ : {s : List Σ} → ε ~ s → s ≡ []
ε~ eps = refl

⟦_⟧~[] : {c : Σ} → ¬ᵗ(⟦ c ⟧ ~ [])
⟦_⟧~[] = λ ()

open import Data.Product using (_×_;_,_;∃;-,_) renaming (Σ to DP)

generalize : {A : Set} (B : A -> Set) {x : A} -> B x -> DP A (λ a → (a ≡ x) × B a) 
generalize B y = -, (refl , y)

∙~[] : {l r : RegEx} → _∙_ l r ~ [] → ((l ~ []) × (r ~ []))
∙~[] {l}{r} m with generalize {List Σ} (_~_ (l ∙ r)) {[]}  m 
... | .([] ++ []) , p , con {[]} {[]} ml mr = ml , mr

open import Data.Sum using (_⊎_) renaming (inj₁ to left;inj₂ to right)

+~[] : {l r : RegEx} → l + r ~ [] → (l ~ []) ⊎ (r ~ [])
+~[] (altl m) = left m
+~[] (altr m) = right m

&~[] : {l r : RegEx} → l & r ~ [] → ((l ~ []) × (r ~ []))
&~[] (and l r) = l , r

¬-involutileʳ : {r : RegEx}{s : List Σ} → r ~ s → ¬ ¬ r ~ s
¬-involutileʳ m = comp m

¬-involutileˡ : {r : RegEx}{s : List Σ} → ¬ ¬ r ~ s → r ~ s
¬-involutileˡ (comp m) = m
