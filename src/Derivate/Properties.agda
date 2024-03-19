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
... | con ln rn = star (altr (con (derivate-sound ln) (*ˢ-sound rn)))
derivate-sound {l + r} {c}   m with +ˢ-sound m
... | altl n = altl (derivate-sound n)
... | altr n = altr (derivate-sound n)
derivate-sound {l ∙ r} {c} m with nullable l
... | yes p with +ˢ-sound  m
... | altl n with ∙ˢ-sound n
... | con lo ro = con (derivate-sound lo) ro
derivate-sound {l ∙ r} {c} m | yes p | altr n = con p (derivate-sound n)
derivate-sound {l ∙ r} {c} m | no ¬p with ∙ˢ-sound {derivate c l} m
... | con ln rn = con (derivate-sound ln) rn
derivate-sound {l & r} {c} m with &ˢ-sound m
... | and ln rn = and (derivate-sound ln) (derivate-sound rn)

derivate-complete : {r : RegEx}{c : Σ}{s : List Σ} → r ~ (c ∷ s) → (derivate c r) ~ s
derivate-complete {⟦ x ⟧} {c} {[]} m with c ≟ x
... | yes refl = eps
derivate-complete {⟦ x ⟧} {.x} {[]} chr | no ¬p = ⊥-elim (¬p refl)
derivate-complete {r *}   {c}  {s} (star (altr m)) with ~++ m
... | _ , p , con{[]}{d ∷ u} ln rn = subst (_~_ ((derivate c r ) ∙ˢ (r *ˢ))) p2 (subst (λ x → (derivate x r) ∙ˢ (r *ˢ) ~ u) p1 (derivate-complete rn))
 where
  p1 = fst (∷-injective p)
  p2 = snd (∷-injective p)
... | _ , p , con{d ∷ t} ln rn = ∙ˢ-comp (subst (_~_ ((derivate c r) ∙ (r *ˢ))) p2 (con (subst (λ x → (derivate x r) ~ t) p1 (derivate-complete ln)) (*ˢ-comp rn)))
 where
  p1 = fst (∷-injective p)
  p2 = snd (∷-injective p)
derivate-complete {l + r} (altl m) = +ˢ-comp (altl (derivate-complete m))
derivate-complete {l + r} {c} (altr m) = +ˢ-comp{derivate c l} (altr (derivate-complete m))
derivate-complete {l ∙ r} {c} {s} m  with ~++ m | nullable l
... | _ , p , con{[]}       ln rn | yes q = +ˢ-comp{(derivate c l) ∙ˢ r} (altr (derivate-complete (subst (_~_ r) p rn)))
... | _ , p , con{d ∷ t}{u} ln rn | yes q = +ˢ-comp (altl (∙ˢ-comp (subst (_~_ ((derivate c l) ∙ r)) p2 (con ((subst (λ x → derivate x l ~ t)  p1 (derivate-complete ln))) rn))))
 where
  p1 = fst (∷-injective p)
  p2 = snd (∷-injective p)
... | _ , p , con {[]} ln rn | no ¬q = ⊥-elim (¬q ln)
... | _ , p , con {d ∷ t} {u} ln rn | no ¬q = ∙ˢ-comp (subst (_~_ ((derivate c l) ∙ r)) p2 (con ((subst (λ x → derivate x l ~ t)  p1 (derivate-complete ln))) rn))
 where
  p1 = fst (∷-injective p)
  p2 = snd (∷-injective p)
derivate-complete {l & r} {c} (and lm rm) = &ˢ-comp (and (derivate-complete lm) (derivate-complete rm))
