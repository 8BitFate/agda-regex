open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module SmartConstructor.Properties {Σ : Set} (Φ : Finite Σ) (_≟_ : (a : Σ) → (b : Σ) →  Dec ( a ≡ b)) where

open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (subst;sym)
open import Data.List using (List;_∷_;[];foldr;dropWhile)

open import RegEx Φ _≟_
open import SmartConstructor Φ _≟_
open import Match Φ _≟_ as M

-- Smart Constructor proofs

*ˢ-sound : {r : RegEx}{s : List Σ} → r *ˢ ~ s → r * ~ s
*ˢ-sound {ε}     eps = star (altl eps)
*ˢ-sound {∅}     eps = star (altl eps)
*ˢ-sound {⟦ _ ⟧} m = m
*ˢ-sound {_ *}   m = m
*ˢ-sound {¬ _}   m = m
*ˢ-sound {_ ∙ _} m = m
*ˢ-sound {_ + _} m = m
*ˢ-sound {_ & _} m = m

*ˢ-comp : {r : RegEx}{s : List Σ} → r * ~ s → r *ˢ ~ s
*ˢ-comp {∅}     (star (altl m)) = m
*ˢ-comp {∅}     (star (altr (con () m)))
*ˢ-comp {ε}     (star (altl m)) = m
*ˢ-comp {ε}     (star (altr (con eps m))) = *ˢ-comp m
*ˢ-comp {⟦ _ ⟧} m = m
*ˢ-comp {_ *}   m = m
*ˢ-comp {¬ _}   m = m
*ˢ-comp {_ ∙ _} m = m
*ˢ-comp {_ + _} m = m
*ˢ-comp {_ & _} m = m

¬ˢ-sound : {r : RegEx}{s : List Σ} → ¬ˢ r ~ s → ¬ r ~ s
¬ˢ-sound {∅} m = m
¬ˢ-sound {ε} m = m
¬ˢ-sound {⟦ _ ⟧} m = m
¬ˢ-sound {_ *} m = m
¬ˢ-sound {¬ r} m = ¬-involutileʳ m
¬ˢ-sound {_ ∙ _} m = m
¬ˢ-sound {_ + _} m = m
¬ˢ-sound {_ & _} m = m

¬ˢ-comp : {r : RegEx}{s : List Σ}→ ¬ r ~ s → ¬ˢ r ~ s
¬ˢ-comp {∅} m = m
¬ˢ-comp {ε} m = m
¬ˢ-comp {⟦ _ ⟧} m = m
¬ˢ-comp {_ *} m = m
¬ˢ-comp {¬ r} m = ¬-involutileˡ m
¬ˢ-comp {_ ∙ _} m = m
¬ˢ-comp {_ + _} m = m
¬ˢ-comp {_ & _} m = m

∙ˢ-sound : {l r : RegEx}{s : List Σ} → l ∙ˢ r ~ s → l ∙ r ~ s
∙ˢ-sound {ε}       {ε}     m = con eps m
∙ˢ-sound {ε}       {⟦ _ ⟧} m = con eps m
∙ˢ-sound {ε}       {_ *}   m = con eps m
∙ˢ-sound {ε}       {¬ _}   m = con eps m
∙ˢ-sound {ε}       {_ ∙ _} m = con eps m
∙ˢ-sound {ε}       {_ + _} m = con eps m
∙ˢ-sound {ε}       {_ & _} m = con eps m
∙ˢ-sound {⟦ c ⟧}   {ε} {s} m = subst (_~_ (⟦ c ⟧ ∙ ε)) (++-identityʳ s) (con m eps)
∙ˢ-sound {⟦ _ ⟧}   {⟦ _ ⟧} m = m
∙ˢ-sound {⟦ _ ⟧}   {_ *}   m = m
∙ˢ-sound {⟦ _ ⟧}   {¬ _}   m = m
∙ˢ-sound {⟦ _ ⟧}   {_ ∙ _} m = m
∙ˢ-sound {⟦ _ ⟧}   {_ + _} m = m
∙ˢ-sound {⟦ _ ⟧}   {_ & _} m = m
∙ˢ-sound {l1 ∙ l2} {ε} {s} m = subst (_~_ (l1 ∙ l2 ∙ ε)) (++-identityʳ s) (con m eps)
∙ˢ-sound {_ ∙ _}   {⟦ _ ⟧} m = m
∙ˢ-sound {_ ∙ _}   {_ *}   m = m
∙ˢ-sound {_ ∙ _}   {¬ _}   m = m
∙ˢ-sound {_ ∙ _}   {_ ∙ _} m = m
∙ˢ-sound {_ ∙ _}   {_ + _} m = m
∙ˢ-sound {_ ∙ _}   {_ & _} m = m
∙ˢ-sound {l *}     {ε} {s} m = subst (_~_ (l * ∙ ε)) (++-identityʳ s) (con m eps)
∙ˢ-sound {_ *}     {⟦ _ ⟧} m = m
∙ˢ-sound {_ *}     {_ *}   m = m
∙ˢ-sound {_ *}     {¬ _}   m = m
∙ˢ-sound {_ *}     {_ ∙ _} m = m
∙ˢ-sound {_ *}     {_ + _} m = m
∙ˢ-sound {_ *}     {_ & _} m = m
∙ˢ-sound {l1 + l2} {ε} {s} m = subst (_~_ ((l1 + l2) ∙ ε)) (++-identityʳ s) (con m eps)
∙ˢ-sound {_ + _}   {⟦ _ ⟧} m = m
∙ˢ-sound {_ + _}   {_ *}   m = m
∙ˢ-sound {_ + _}   {¬ _}   m = m
∙ˢ-sound {_ + _}   {_ ∙ _} m = m
∙ˢ-sound {_ + _}   {_ + _} m = m
∙ˢ-sound {_ + _}   {_ & _} m = m
∙ˢ-sound {l1 & l2} {ε} {s} m = subst (_~_ ((l1 & l2) ∙ ε)) (++-identityʳ s) (con m eps)
∙ˢ-sound {_ & _}   {⟦ _ ⟧} m = m
∙ˢ-sound {_ & _}   {_ *}   m = m
∙ˢ-sound {_ & _}   {¬ _}   m = m
∙ˢ-sound {_ & _}   {_ ∙ _} m = m
∙ˢ-sound {_ & _}   {_ + _} m = m
∙ˢ-sound {_ & _}   {_ & _} m = m
∙ˢ-sound {¬ r}     {ε} {s} m = subst (_~_ (¬ r ∙ ε)) (++-identityʳ s) (con m eps)
∙ˢ-sound {¬ _}     {⟦ _ ⟧} m = m
∙ˢ-sound {¬ _}     {_ *}   m = m
∙ˢ-sound {¬ _}     {¬ _}   m = m
∙ˢ-sound {¬ _}     {_ ∙ _} m = m
∙ˢ-sound {¬ _}     {_ + _} m = m
∙ˢ-sound {¬ _}     {_ & _} m = m

∙ˢ-comp : {l r : RegEx}{s : List Σ} → l ∙ r ~ s → l ∙ˢ r ~ s
∙ˢ-comp {∅}       {_}     (con () _)
∙ˢ-comp {ε}       {ε}     (con eps m) = m
∙ˢ-comp {ε}       {⟦ _ ⟧} (con eps m) = m
∙ˢ-comp {ε}       {_ *}   (con eps m) = m
∙ˢ-comp {ε}       {¬ _}   (con eps m) = m
∙ˢ-comp {ε}       {_ ∙ _} (con eps m) = m
∙ˢ-comp {ε}       {_ + _} (con eps m) = m
∙ˢ-comp {ε}       {_ & _} (con eps m) = m
∙ˢ-comp {⟦ _ ⟧}   {∅}     (con m ()) 
∙ˢ-comp {⟦ c ⟧}   {ε}     (con {s} m eps) = subst (_~_ ⟦ c ⟧) (sym (++-identityʳ s))  m
∙ˢ-comp {⟦ _ ⟧}   {⟦ _ ⟧} m = m
∙ˢ-comp {⟦ _ ⟧}   {_ *}   m = m
∙ˢ-comp {⟦ _ ⟧}   {¬ _}   m = m
∙ˢ-comp {⟦ _ ⟧}   {_ ∙ _} m = m
∙ˢ-comp {⟦ _ ⟧}   {_ + _} m = m
∙ˢ-comp {⟦ _ ⟧}   {_ & _} m = m
∙ˢ-comp {_ *}     {∅}     (con m ())
∙ˢ-comp {r *}     {ε}     (con {s} m eps) = subst (_~_ (r *)) (sym (++-identityʳ s)) m
∙ˢ-comp {_ *}     {⟦ _ ⟧} m = m
∙ˢ-comp {_ *}     {_ *}   m = m
∙ˢ-comp {_ *}     {¬ _}   m = m
∙ˢ-comp {_ *}     {_ ∙ _} m = m
∙ˢ-comp {_ *}     {_ + _} m = m
∙ˢ-comp {_ *}     {_ & _} m = m
∙ˢ-comp {¬ _}     {∅}     (con m ())
∙ˢ-comp {¬ r}     {ε}     (con {s} m eps) = subst (_~_ (¬ r)) (sym (++-identityʳ s)) m
∙ˢ-comp {¬ _}     {⟦ _ ⟧} m = m
∙ˢ-comp {¬ _}     {_ *}   m = m
∙ˢ-comp {¬ _}     {¬ _}   m = m
∙ˢ-comp {¬ _}     {_ ∙ _} m = m
∙ˢ-comp {¬ _}     {_ + _} m = m
∙ˢ-comp {¬ _}     {_ & _} m = m
∙ˢ-comp {_ ∙ _}   {∅}     (con m ())
∙ˢ-comp {l1 ∙ l2} {ε}     (con {s} m eps) = subst (_~_ (l1 ∙ l2)) (sym (++-identityʳ s)) m
∙ˢ-comp {_ ∙ _}   {⟦ x ⟧} m = m
∙ˢ-comp {_ ∙ _}   {_ *}   m = m
∙ˢ-comp {_ ∙ _}   {¬ _}   m = m
∙ˢ-comp {_ ∙ _}   {_ ∙ _} m = m
∙ˢ-comp {_ ∙ _}   {_ + _} m = m
∙ˢ-comp {_ ∙ _}   {_ & _} m = m
∙ˢ-comp {_ + _}   {∅}     (con m ())
∙ˢ-comp {l1 + l2} {ε}     (con {s} m eps) = subst (_~_ (l1 + l2)) (sym (++-identityʳ s)) m
∙ˢ-comp {_ + _}   {⟦ _ ⟧} m = m
∙ˢ-comp {_ + _}   {_ *}   m = m
∙ˢ-comp {_ + _}   {¬ _}   m = m
∙ˢ-comp {_ + _}   {_ ∙ _} m = m
∙ˢ-comp {_ + _}   {_ + _} m = m
∙ˢ-comp {_ + _}   {_ & _} m = m
∙ˢ-comp {_ & _}   {∅}     (con m ())
∙ˢ-comp {l1 & l2} {ε}     (con {s} m eps) = subst (_~_ (l1 & l2)) (sym (++-identityʳ s)) m
∙ˢ-comp {_ & _}   {⟦ _ ⟧} m = m
∙ˢ-comp {_ & _}   {_ *}   m = m
∙ˢ-comp {_ & _}   {¬ _}   m = m
∙ˢ-comp {_ & _}   {_ ∙ _} m = m
∙ˢ-comp {_ & _}   {_ + _} m = m
∙ˢ-comp {_ & _}   {_ & _} m = m

+ˢ-sound : {l r : RegEx}{s : List Σ} → l +ˢ r ~ s → l + r ~ s
+ˢ-sound {∅}     {_}     m = altr m
+ˢ-sound {ε}     {∅}     m = altl m
+ˢ-sound {ε}     {ε}     m = m
+ˢ-sound {ε}     {⟦ _ ⟧} m = m
+ˢ-sound {ε}     {_ *}   m = m
+ˢ-sound {ε}     {¬ _}   m = m
+ˢ-sound {ε}     {_ ∙ _} m = m
+ˢ-sound {ε}     {_ + _} m = m
+ˢ-sound {ε}     {_ & _} m = m
+ˢ-sound {⟦ _ ⟧} {∅}     m = altl m
+ˢ-sound {⟦ _ ⟧} {ε}     m = m
+ˢ-sound {⟦ _ ⟧} {⟦ _ ⟧} m = m
+ˢ-sound {⟦ _ ⟧} {_ *}   m = m
+ˢ-sound {⟦ _ ⟧} {¬ _}   m = m
+ˢ-sound {⟦ _ ⟧} {_ ∙ _} m = m
+ˢ-sound {⟦ _ ⟧} {_ + _} m = m
+ˢ-sound {⟦ _ ⟧} {_ & _} m = m
+ˢ-sound {_ *}   {∅}     m = altl m
+ˢ-sound {_ *}   {ε}     m = m
+ˢ-sound {_ *}   {⟦ _ ⟧} m = m
+ˢ-sound {_ *}   {_ *}   m = m
+ˢ-sound {_ *}   {¬ _}   m = m
+ˢ-sound {_ *}   {_ ∙ _} m = m
+ˢ-sound {_ *}   {_ + _} m = m
+ˢ-sound {_ *}   {_ & _} m = m
+ˢ-sound {¬ _}   {∅}     m = altl m
+ˢ-sound {¬ _}   {ε}     m = m
+ˢ-sound {¬ _}   {⟦ _ ⟧} m = m
+ˢ-sound {¬ _}   {_ *}   m = m
+ˢ-sound {¬ _}   {¬ _}   m = m
+ˢ-sound {¬ _}   {_ ∙ _} m = m
+ˢ-sound {¬ _}   {_ + _} m = m
+ˢ-sound {¬ _}   {_ & _} m = m
+ˢ-sound {_ ∙ _} {∅}     m = altl m
+ˢ-sound {_ ∙ _} {ε}     m = m
+ˢ-sound {_ ∙ _} {⟦ _ ⟧} m = m
+ˢ-sound {_ ∙ _} {_ *}   m = m
+ˢ-sound {_ ∙ _} {¬ _}   m = m
+ˢ-sound {_ ∙ _} {_ ∙ _} m = m
+ˢ-sound {_ ∙ _} {_ + _} m = m
+ˢ-sound {_ ∙ _} {_ & _} m = m
+ˢ-sound {_ + _} {∅}     m = altl m
+ˢ-sound {_ + _} {ε}     m = m
+ˢ-sound {_ + _} {⟦ _ ⟧} m = m
+ˢ-sound {_ + _} {_ *}   m = m
+ˢ-sound {_ + _} {¬ _}   m = m
+ˢ-sound {_ + _} {_ ∙ _} m = m
+ˢ-sound {_ + _} {_ + _} m = m
+ˢ-sound {_ + _} {_ & _} m = m
+ˢ-sound {_ & _} {∅}     m = altl m
+ˢ-sound {_ & _} {ε}     m = m
+ˢ-sound {_ & _} {⟦ _ ⟧} m = m
+ˢ-sound {_ & _} {_ *}   m = m
+ˢ-sound {_ & _} {¬ _}   m = m
+ˢ-sound {_ & _} {_ ∙ _} m = m
+ˢ-sound {_ & _} {_ + _} m = m
+ˢ-sound {_ & _} {_ & _} m = m

+ˢ-comp : {l r : RegEx}{s : List Σ} → l + r ~ s → l +ˢ r ~ s
+ˢ-comp {∅}     {_}     (altr m) = m
+ˢ-comp {ε}     {∅}     (altl m) = m
+ˢ-comp {ε}     {ε}     m = m
+ˢ-comp {ε}     {⟦ _ ⟧} m = m
+ˢ-comp {ε}     {_ *}   m = m
+ˢ-comp {ε}     {¬ _}   m = m
+ˢ-comp {ε}     {_ ∙ _} m = m
+ˢ-comp {ε}     {_ + _} m = m
+ˢ-comp {ε}     {_ & _} m = m
+ˢ-comp {⟦ _ ⟧} {∅}     (altl m) = m
+ˢ-comp {⟦ _ ⟧} {ε}     m = m
+ˢ-comp {⟦ _ ⟧} {⟦ _ ⟧} m = m
+ˢ-comp {⟦ _ ⟧} {_ *}   m = m
+ˢ-comp {⟦ _ ⟧} {¬ _}   m = m
+ˢ-comp {⟦ _ ⟧} {_ ∙ _} m = m
+ˢ-comp {⟦ _ ⟧} {_ + _} m = m
+ˢ-comp {⟦ _ ⟧} {_ & _} m = m
+ˢ-comp {_ *}   {∅}     (altl m) = m
+ˢ-comp {_ *}   {ε}     m = m
+ˢ-comp {_ *}   {⟦ _ ⟧} m = m
+ˢ-comp {_ *}   {_ *}   m = m
+ˢ-comp {_ *}   {¬ _}   m = m
+ˢ-comp {_ *}   {_ ∙ _} m = m
+ˢ-comp {_ *}   {_ + _} m = m
+ˢ-comp {_ *}   {_ & _} m = m
+ˢ-comp {¬ _}   {∅}     (altl m) = m
+ˢ-comp {¬ _}   {ε}     m = m
+ˢ-comp {¬ _}   {⟦ _ ⟧} m = m
+ˢ-comp {¬ _}   {_ *}   m = m
+ˢ-comp {¬ _}   {¬ _}   m = m
+ˢ-comp {¬ _}   {_ ∙ _} m = m
+ˢ-comp {¬ _}   {_ + _} m = m
+ˢ-comp {¬ _}   {_ & _} m = m
+ˢ-comp {_ ∙ _} {∅}     (altl m) = m
+ˢ-comp {_ ∙ _} {ε}     m = m
+ˢ-comp {_ ∙ _} {⟦ _ ⟧} m = m
+ˢ-comp {_ ∙ _} {_ *}   m = m
+ˢ-comp {_ ∙ _} {¬ _}   m = m
+ˢ-comp {_ ∙ _} {_ ∙ _} m = m
+ˢ-comp {_ ∙ _} {_ + _} m = m
+ˢ-comp {_ ∙ _} {_ & _} m = m
+ˢ-comp {_ + _} {∅}     (altl m) = m
+ˢ-comp {_ + _} {ε}     m = m
+ˢ-comp {_ + _} {⟦ _ ⟧} m = m
+ˢ-comp {_ + _} {_ *}   m = m
+ˢ-comp {_ + _} {¬ _}   m = m
+ˢ-comp {_ + _} {_ ∙ _} m = m
+ˢ-comp {_ + _} {_ + _} m = m
+ˢ-comp {_ + _} {_ & _} m = m
+ˢ-comp {_ & _} {∅}     (altl m) = m
+ˢ-comp {_ & _} {ε}     m = m
+ˢ-comp {_ & _} {⟦ _ ⟧} m = m
+ˢ-comp {_ & _} {_ *}   m = m
+ˢ-comp {_ & _} {¬ _}   m = m
+ˢ-comp {_ & _} {_ ∙ _} m = m
+ˢ-comp {_ & _} {_ + _} m = m
+ˢ-comp {_ & _} {_ & _} m = m

&ˢ-sound : {l r : RegEx}{s : List Σ} → l &ˢ r ~ s → l & r ~ s
&ˢ-sound {∅}     {_}     ()
&ˢ-sound {ε}     {ε}     m = m
&ˢ-sound {ε}     {⟦ _ ⟧} m = m
&ˢ-sound {ε}     {_ *}   m = m
&ˢ-sound {ε}     {¬ _}   m = m
&ˢ-sound {ε}     {_ ∙ _} m = m
&ˢ-sound {ε}     {_ + _} m = m
&ˢ-sound {ε}     {_ & _} m = m
&ˢ-sound {⟦ _ ⟧} {ε}     m = m
&ˢ-sound {⟦ _ ⟧} {⟦ _ ⟧} m = m
&ˢ-sound {⟦ _ ⟧} {_ *}   m = m
&ˢ-sound {⟦ _ ⟧} {¬ _}   m = m
&ˢ-sound {⟦ _ ⟧} {_ ∙ _} m = m
&ˢ-sound {⟦ _ ⟧} {_ + _} m = m
&ˢ-sound {⟦ _ ⟧} {_ & _} m = m
&ˢ-sound {_ *}   {ε}     m = m
&ˢ-sound {_ *}   {⟦ _ ⟧} m = m
&ˢ-sound {_ *}   {_ *}   m = m
&ˢ-sound {_ *}   {¬ _}   m = m
&ˢ-sound {_ *}   {_ ∙ _} m = m
&ˢ-sound {_ *}   {_ + _} m = m
&ˢ-sound {_ *}   {_ & _} m = m
&ˢ-sound {¬ _}   {ε}     m = m
&ˢ-sound {¬ _}   {⟦ _ ⟧} m = m
&ˢ-sound {¬ _}   {_ *}   m = m
&ˢ-sound {¬ _}   {¬ _}   m = m
&ˢ-sound {¬ _}   {_ ∙ _} m = m
&ˢ-sound {¬ _}   {_ + _} m = m
&ˢ-sound {¬ _}   {_ & _} m = m
&ˢ-sound {_ ∙ _} {ε}     m = m
&ˢ-sound {_ ∙ _} {⟦ _ ⟧} m = m
&ˢ-sound {_ ∙ _} {_ *}   m = m
&ˢ-sound {_ ∙ _} {¬ _}   m = m
&ˢ-sound {_ ∙ _} {_ ∙ _} m = m
&ˢ-sound {_ ∙ _} {_ + _} m = m
&ˢ-sound {_ ∙ _} {_ & _} m = m
&ˢ-sound {_ + _} {ε}     m = m
&ˢ-sound {_ + _} {⟦ _ ⟧} m = m
&ˢ-sound {_ + _} {_ *}   m = m
&ˢ-sound {_ + _} {¬ _}   m = m
&ˢ-sound {_ + _} {_ ∙ _} m = m
&ˢ-sound {_ + _} {_ + _} m = m
&ˢ-sound {_ + _} {_ & _} m = m
&ˢ-sound {_ & _} {ε}     m = m
&ˢ-sound {_ & _} {⟦ _ ⟧} m = m
&ˢ-sound {_ & _} {_ *}   m = m
&ˢ-sound {_ & _} {¬ _}   m = m
&ˢ-sound {_ & _} {_ ∙ _} m = m
&ˢ-sound {_ & _} {_ + _} m = m
&ˢ-sound {_ & _} {_ & _} m = m

&ˢ-comp : {l r : RegEx}{s : List Σ} → l & r ~ s → l &ˢ r ~ s
&ˢ-comp {∅}     {_}     (and () _)
&ˢ-comp {ε}     {∅}     (and m ())
&ˢ-comp {ε}     {ε}     m = m
&ˢ-comp {ε}     {⟦ _ ⟧} m = m
&ˢ-comp {ε}     {_ *}   m = m
&ˢ-comp {ε}     {¬ _}   m = m
&ˢ-comp {ε}     {_ ∙ _} m = m
&ˢ-comp {ε}     {_ + _} m = m
&ˢ-comp {ε}     {_ & _} m = m
&ˢ-comp {⟦ _ ⟧} {∅}     (and _ ())
&ˢ-comp {⟦ _ ⟧} {ε}     m = m
&ˢ-comp {⟦ _ ⟧} {⟦ _ ⟧} m = m
&ˢ-comp {⟦ _ ⟧} {_ *}   m = m
&ˢ-comp {⟦ _ ⟧} {¬ _}   m = m
&ˢ-comp {⟦ _ ⟧} {_ ∙ _} m = m
&ˢ-comp {⟦ _ ⟧} {_ + _} m = m
&ˢ-comp {⟦ _ ⟧} {_ & _} m = m
&ˢ-comp {_ *}   {∅}     (and m ())
&ˢ-comp {_ *}   {ε}     m = m
&ˢ-comp {_ *}   {⟦ _ ⟧} m = m
&ˢ-comp {_ *}   {_ *}   m = m
&ˢ-comp {_ *}   {¬ _}   m = m
&ˢ-comp {_ *}   {_ ∙ _} m = m
&ˢ-comp {_ *}   {_ + _} m = m
&ˢ-comp {_ *}   {_ & _} m = m
&ˢ-comp {¬ _}   {∅}     (and m ())
&ˢ-comp {¬ _}   {ε}     m = m
&ˢ-comp {¬ _}   {⟦ _ ⟧} m = m
&ˢ-comp {¬ _}   {_ *}   m = m
&ˢ-comp {¬ _}   {¬ _}   m = m
&ˢ-comp {¬ _}   {_ ∙ _} m = m
&ˢ-comp {¬ _}   {_ + _} m = m
&ˢ-comp {¬ _}   {_ & _} m = m
&ˢ-comp {_ ∙ _} {∅}     (and m ())
&ˢ-comp {_ ∙ _} {ε}     m = m
&ˢ-comp {_ ∙ _} {⟦ _ ⟧} m = m
&ˢ-comp {_ ∙ _} {_ *}   m = m
&ˢ-comp {_ ∙ _} {¬ _}   m = m
&ˢ-comp {_ ∙ _} {_ ∙ _} m = m
&ˢ-comp {_ ∙ _} {_ + _} m = m
&ˢ-comp {_ ∙ _} {_ & _} m = m
&ˢ-comp {_ + _} {∅}     (and m ())
&ˢ-comp {_ + _} {ε}     m = m
&ˢ-comp {_ + _} {⟦ _ ⟧} m = m
&ˢ-comp {_ + _} {_ *}   m = m
&ˢ-comp {_ + _} {¬ _}   m = m
&ˢ-comp {_ + _} {_ ∙ _} m = m
&ˢ-comp {_ + _} {_ + _} m = m
&ˢ-comp {_ + _} {_ & _} m = m
&ˢ-comp {_ & _} {∅}     (and m ())
&ˢ-comp {_ & _} {ε}     m = m
&ˢ-comp {_ & _} {⟦ _ ⟧} m = m
&ˢ-comp {_ & _} {_ *}   m = m
&ˢ-comp {_ & _} {¬ _}   m = m
&ˢ-comp {_ & _} {_ ∙ _} m = m
&ˢ-comp {_ & _} {_ + _} m = m
&ˢ-comp {_ & _} {_ & _} m = m

-- Helper functions proofs

open import Relation.Nullary using () renaming (¬_ to ¬ᵗ_)
open import Data.List using ([_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here;there)
open import Relation.Binary.PropositionalEquality using (_≡_;refl)

accept-comp : {l : List Σ}{c : Σ} → (c ∈ l) → (accept l) ~ [ c ]
accept-comp {c ∷ l} (here refl) = +ˢ-comp {⟦ c ⟧}{accept l} (altl chr)
accept-comp {c ∷ l} (there p) = +ˢ-comp{⟦ c ⟧}{accept l} (altr (accept-comp p))

accept-sound : {s : List Σ}{c : Σ} →  (accept s) ~ [ c ] → c ∈ s
accept-sound {c ∷ s} m with +ˢ-sound {⟦ c  ⟧}{r = accept s} m
... | altl chr = here refl
... | altr n = there (accept-sound n)

accept≁[] : {l : List Σ} → ¬ᵗ((accept l) ~ [])
accept≁[] {c ∷ l} m with +ˢ-sound {⟦ c ⟧}{accept l} m 
... | altr n = accept≁[] {l} n

accept≁l2+ : {l s : List Σ}{a b : Σ} → ¬ᵗ((accept l) ~ a ∷ b ∷ s)
accept≁l2+ {c ∷ l} m with +ˢ-sound {⟦ c ⟧}{accept l} m
... | altr n = accept≁l2+ {l} n

σ~* : {c : Σ} → σ ~ [ c ]
σ~* {c} = accept-comp (Finite.every Φ c)

σ≁[] : ¬ᵗ(σ ~ [])
σ≁[] = accept≁[] {Finite.list Φ} 

Ι~** : {s : List Σ} → Ι ~ s
Ι~** {[]} = star (altl eps)
Ι~** {c ∷ s} = star (altr (con {[ c ]} σ~* Ι~**))

complement-involutileʳ : {r : RegEx}{s : List Σ} → r ~ s →  complement (complement r) ~ s
complement-involutileʳ m = {!!}

complement-involutileˡ : {r : RegEx}{s : List Σ} → complement (complement r) ~ s → r ~ s 
complement-involutileˡ m = {!!}

open import Relation.Nullary using (yes;no)
open import Data.Empty using (⊥;⊥-elim)
open import Data.Product using () renaming (proj₁ to fst)
open import Function using (_∘_)

complement-inverse : {r : RegEx}{s : List Σ} → r ~ s → (complement r) ~ s → ⊥
complement-inverse {ε} eps = σ≁[] ∘ fst ∘ ∙~[]
complement-inverse {⟦ x ⟧} chr (altr n) = {!n!}
complement-inverse {r *} (star m) n = {!!}
complement-inverse {¬ r} m n = {!!}
complement-inverse {l ∙ r} m n = {!!}
complement-inverse {l + r} m n = {!!}
complement-inverse {l & r} (and lm rm) = {!!}
