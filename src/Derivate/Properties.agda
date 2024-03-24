open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_)

open import Finite using (Finite)

module Derivate.Properties {Σ : Set} (Φ : Finite Σ) where

open Finite.Finite Φ

open import Data.List using (List;_∷_;[];_++_;tail)
open import Data.List.Properties using (∷-injective)
open import Relation.Nullary using (yes;no)
open import Relation.Binary.PropositionalEquality using (refl;subst;cong)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_;_,_;∃;-,_) renaming (Σ to Sigma;proj₁ to fst;proj₂ to snd)

open import RegEx Φ
open import SmartConstructor Φ
open import SmartConstructor.Properties Φ
open import Match Φ
open import Match.Properties Φ
open import Derivate Φ

derivate-sound : {r : RegEx}{c : Σ}{s : List Σ} → (derivate c r) ~ s → r ~ (c ∷ s)
derivate-sound {⟦ x ⟧} {c}  {s}  m with c ≟ x
derivate-sound {⟦ x ⟧} {.x} {[]} m | yes refl = chr
derivate-sound {⟦ x ⟧} {c}   () | no ¬p
derivate-sound {r *}   {c}   m with ∙ˢ-sound m
... | con ln rn refl = star (altr (con (derivate-sound ln) (*ˢ-sound rn) refl))
derivate-sound {l + r} {c}   m with +ˢ-sound m
... | altl n = altl (derivate-sound n)
... | altr n = altr (derivate-sound n)
derivate-sound {l ∙ r} {c} m with nullable l
... | yes p with +ˢ-sound  m
... | altl n with ∙ˢ-sound n
... | con lo ro refl = con (derivate-sound lo) ro refl
derivate-sound {l ∙ r} {c} m | yes p | altr n = con p (derivate-sound n) refl
derivate-sound {l ∙ r} {c} m | no ¬p with ∙ˢ-sound {derivate c l} m
... | con ln rn refl = con (derivate-sound ln) rn refl
derivate-sound {l & r} {c} m with &ˢ-sound m
... | and ln rn = and (derivate-sound ln) (derivate-sound rn)

derivate-complete : {r : RegEx}{c : Σ}{s : List Σ} → r ~ (c ∷ s) → (derivate c r) ~ s
derivate-complete {⟦ x ⟧} {c} {[]} m with c ≟ x
... | yes refl = eps
derivate-complete {⟦ x ⟧} {.x} {[]} chr | no ¬p = ⊥-elim (¬p refl)
derivate-complete {r *}   {c}  {s} (star (altr (con{[]}{d ∷ u} ln rn refl))) = derivate-complete rn
derivate-complete {r *}   {c}  {s} (star (altr (con{d ∷ t} ln rn refl))) = ∙ˢ-comp (con (derivate-complete ln) (*ˢ-comp rn) refl)
derivate-complete {l + r} (altl m) = +ˢ-comp (altl (derivate-complete m))
derivate-complete {l + r} {c} (altr m) = +ˢ-comp{derivate c l} (altr (derivate-complete m))
derivate-complete {l ∙ r} {c} {s} m with nullable l
derivate-complete {l ∙ r} {c} {s} (con{[]}       ln rn refl) | yes q = +ˢ-comp{(derivate c l) ∙ˢ r} (altr (derivate-complete rn))
derivate-complete {l ∙ r} {c} {s} (con{d ∷ t}{u} ln rn refl) | yes q = +ˢ-comp (altl (∙ˢ-comp (con (derivate-complete ln) rn refl)))
derivate-complete {l ∙ r} {c} {s} (con {[]} ln rn refl) | no ¬q = ⊥-elim (¬q ln)
derivate-complete {l ∙ r} {c} {s} (con {d ∷ t} {u} ln rn refl) | no ¬q = ∙ˢ-comp (con (derivate-complete ln) rn refl)
derivate-complete {l & r} {c} (and lm rm) = &ˢ-comp (and (derivate-complete lm) (derivate-complete rm))
