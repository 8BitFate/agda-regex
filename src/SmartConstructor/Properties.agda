open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Finite using (Finite)

module SmartConstructor.Properties {Σ : Set} (Φ : Finite Σ) where

open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (refl;subst;sym)
open import Data.List using (List;_∷_;[];foldr;dropWhile)

open import RegEx Φ
open import SmartConstructor Φ
open import Match Φ

-- Smart Constructor proofs

*ˢ-sound : {r : RegEx}{s : List Σ} → r *ˢ ~ s → r * ~ s
*ˢ-sound {ε}     eps = star (altl eps)
*ˢ-sound {∅}     eps = star (altl eps)
*ˢ-sound {⟦ _ ⟧} m = m
*ˢ-sound {_ *}   m = m
*ˢ-sound {_ + _} m = m
*ˢ-sound {_ ∙ _} m = m
*ˢ-sound {_ & _} m = m

*ˢ-comp : {r : RegEx}{s : List Σ} → r * ~ s → r *ˢ ~ s
*ˢ-comp {∅}     (star (altl m))           = m
*ˢ-comp {∅}     (star (altr (con () _ _)))
*ˢ-comp {ε}     (star (altl m))           = m
*ˢ-comp {ε}     (star (altr (con eps m refl))) = *ˢ-comp m
*ˢ-comp {⟦ _ ⟧} m                         = m
*ˢ-comp {_ *}   m                         = m
*ˢ-comp {_ + _} m                         = m
*ˢ-comp {_ ∙ _} m                         = m
*ˢ-comp {_ & _} m                         = m

∙ˢ-sound : {l r : RegEx}{s : List Σ} → l ∙ˢ r ~ s → l ∙ r ~ s
∙ˢ-sound {ε}       {ε}     m = con eps m refl
∙ˢ-sound {ε}       {⟦ _ ⟧} m = con eps m refl
∙ˢ-sound {ε}       {_ *}   m = con eps m refl
∙ˢ-sound {ε}       {_ + _} m = con eps m refl
∙ˢ-sound {ε}       {_ ∙ _} m = con eps m refl
∙ˢ-sound {ε}       {_ & _} m = con eps m refl
∙ˢ-sound {⟦ c ⟧}   {ε} {s} m = subst (_~_ (⟦ c ⟧ ∙ ε)) (++-identityʳ s) (con m eps refl)
∙ˢ-sound {⟦ _ ⟧}   {⟦ _ ⟧} m = m
∙ˢ-sound {⟦ _ ⟧}   {_ *}   m = m
∙ˢ-sound {⟦ _ ⟧}   {_ + _} m = m
∙ˢ-sound {⟦ _ ⟧}   {_ ∙ _} m = m
∙ˢ-sound {⟦ _ ⟧}   {_ & _} m = m 
∙ˢ-sound {l *}     {ε} {s} m = subst (_~_ (l * ∙ ε)) (++-identityʳ s) (con m eps refl )
∙ˢ-sound {_ *}     {⟦ _ ⟧} m = m
∙ˢ-sound {_ *}     {_ *}   m = m
∙ˢ-sound {_ *}     {_ + _} m = m
∙ˢ-sound {_ *}     {_ ∙ _} m = m
∙ˢ-sound {_ *}     {_ & _} m = m
∙ˢ-sound {l1 + l2} {ε} {s} m = subst (_~_ ((l1 + l2) ∙ ε)) (++-identityʳ s) (con m eps refl)
∙ˢ-sound {_ + _}   {⟦ _ ⟧} m = m
∙ˢ-sound {_ + _}   {_ *}   m = m
∙ˢ-sound {_ + _}   {_ + _} m = m
∙ˢ-sound {_ + _}   {_ ∙ _} m = m
∙ˢ-sound {_ + _}   {_ & _} m = m
∙ˢ-sound {l1 ∙ l2} {ε} {s} m = subst (_~_ (l1 ∙ l2 ∙ ε)) (++-identityʳ s) (con m eps refl)
∙ˢ-sound {_ ∙ _}   {⟦ _ ⟧} m = m
∙ˢ-sound {_ ∙ _}   {_ *}   m = m
∙ˢ-sound {_ ∙ _}   {_ + _} m = m
∙ˢ-sound {_ ∙ _}   {_ ∙ _} m = m
∙ˢ-sound {_ ∙ _}   {_ & _} m = m
∙ˢ-sound {l1 & l2} {ε} {s} m = subst (_~_ ((l1 & l2) ∙ ε)) (++-identityʳ s) (con m eps refl)
∙ˢ-sound {_ & _}   {⟦ _ ⟧} m = m
∙ˢ-sound {_ & _}   {_ *}   m = m
∙ˢ-sound {_ & _}   {_ ∙ _} m = m
∙ˢ-sound {_ & _}   {_ + _} m = m
∙ˢ-sound {_ & _}   {_ & _} m = m

∙ˢ-comp : {l r : RegEx}{s : List Σ} → l ∙ r ~ s → l ∙ˢ r ~ s
∙ˢ-comp {∅}       {_}     (con () _ _)
∙ˢ-comp {ε}       {ε}     (con eps m refl) = m
∙ˢ-comp {ε}       {⟦ _ ⟧} (con eps m refl) = m
∙ˢ-comp {ε}       {_ *}   (con eps m refl) = m
∙ˢ-comp {ε}       {_ + _} (con eps m refl) = m
∙ˢ-comp {ε}       {_ ∙ _} (con eps m refl) = m
∙ˢ-comp {ε}       {_ & _} (con eps m refl) = m
∙ˢ-comp {⟦ _ ⟧}   {∅}     (con m () _) 
∙ˢ-comp {⟦ c ⟧}   {ε}     (con {s} m eps refl) = subst (_~_ ⟦ c ⟧) (sym (++-identityʳ s))  m
∙ˢ-comp {⟦ _ ⟧}   {⟦ _ ⟧} m = m
∙ˢ-comp {⟦ _ ⟧}   {_ *}   m = m
∙ˢ-comp {⟦ _ ⟧}   {_ + _} m = m
∙ˢ-comp {⟦ _ ⟧}   {_ ∙ _} m = m
∙ˢ-comp {⟦ _ ⟧}   {_ & _} m = m
∙ˢ-comp {_ *}     {∅}     (con m () _)
∙ˢ-comp {r *}     {ε}     (con {s} m eps refl) = subst ((_~_ (r *))) (sym (++-identityʳ s)) m
∙ˢ-comp {_ *}     {⟦ _ ⟧} m = m
∙ˢ-comp {_ *}     {_ *}   m = m
∙ˢ-comp {_ *}     {_ + _} m = m
∙ˢ-comp {_ *}     {_ ∙ _} m = m
∙ˢ-comp {_ *}     {_ & _} m = m
∙ˢ-comp {_ + _}   {∅}     (con m () _)
∙ˢ-comp {l1 + l2} {ε}     (con {s} m eps refl) = subst (_~_ (l1 + l2)) (sym (++-identityʳ s)) m
∙ˢ-comp {_ + _}   {⟦ _ ⟧} m = m
∙ˢ-comp {_ + _}   {_ *}   m = m
∙ˢ-comp {_ + _}   {_ + _} m = m
∙ˢ-comp {_ + _}   {_ ∙ _} m = m
∙ˢ-comp {_ + _}   {_ & _} m = m
∙ˢ-comp {_ ∙ _}   {∅}     (con m () _)
∙ˢ-comp {l1 ∙ l2} {ε}     (con {s} m eps refl) = subst (_~_ (l1 ∙ l2)) (sym (++-identityʳ s)) m
∙ˢ-comp {_ ∙ _}   {⟦ x ⟧} m = m
∙ˢ-comp {_ ∙ _}   {_ *}   m = m
∙ˢ-comp {_ ∙ _}   {_ + _} m = m
∙ˢ-comp {_ ∙ _}   {_ ∙ _} m = m
∙ˢ-comp {_ ∙ _}   {_ & _} m = m
∙ˢ-comp {_ & _}   {∅}     (con m () _)
∙ˢ-comp {l1 & l2} {ε}     (con {s} m eps refl) = subst (_~_ (l1 & l2)) (sym (++-identityʳ s)) m
∙ˢ-comp {_ & _}   {⟦ _ ⟧} m = m
∙ˢ-comp {_ & _}   {_ *}   m = m
∙ˢ-comp {_ & _}   {_ + _} m = m
∙ˢ-comp {_ & _}   {_ ∙ _} m = m
∙ˢ-comp {_ & _}   {_ & _} m = m

+ˢ-sound : {l r : RegEx}{s : List Σ} → l +ˢ r ~ s → l + r ~ s
+ˢ-sound {∅}     {_}     m = altr m
+ˢ-sound {ε}     {∅}     m = altl m
+ˢ-sound {ε}     {ε}     m = m
+ˢ-sound {ε}     {⟦ _ ⟧} m = m
+ˢ-sound {ε}     {_ *}   m = m
+ˢ-sound {ε}     {_ + _} m = m
+ˢ-sound {ε}     {_ ∙ _} m = m
+ˢ-sound {ε}     {_ & _} m = m
+ˢ-sound {⟦ _ ⟧} {∅}     m = altl m
+ˢ-sound {⟦ _ ⟧} {ε}     m = m
+ˢ-sound {⟦ _ ⟧} {⟦ _ ⟧} m = m
+ˢ-sound {⟦ _ ⟧} {_ *}   m = m
+ˢ-sound {⟦ _ ⟧} {_ + _} m = m
+ˢ-sound {⟦ _ ⟧} {_ ∙ _} m = m
+ˢ-sound {⟦ _ ⟧} {_ & _} m = m
+ˢ-sound {_ *}   {∅}     m = altl m
+ˢ-sound {_ *}   {ε}     m = m
+ˢ-sound {_ *}   {⟦ _ ⟧} m = m
+ˢ-sound {_ *}   {_ *}   m = m
+ˢ-sound {_ *}   {_ + _} m = m
+ˢ-sound {_ *}   {_ ∙ _} m = m
+ˢ-sound {_ *}   {_ & _} m = m
+ˢ-sound {_ + _} {∅}     m = altl m
+ˢ-sound {_ + _} {ε}     m = m
+ˢ-sound {_ + _} {⟦ _ ⟧} m = m
+ˢ-sound {_ + _} {_ *}   m = m
+ˢ-sound {_ + _} {_ + _} m = m
+ˢ-sound {_ + _} {_ ∙ _} m = m
+ˢ-sound {_ + _} {_ & _} m = m
+ˢ-sound {_ ∙ _} {∅}     m = altl m
+ˢ-sound {_ ∙ _} {ε}     m = m
+ˢ-sound {_ ∙ _} {⟦ _ ⟧} m = m
+ˢ-sound {_ ∙ _} {_ *}   m = m
+ˢ-sound {_ ∙ _} {_ + _} m = m
+ˢ-sound {_ ∙ _} {_ ∙ _} m = m
+ˢ-sound {_ ∙ _} {_ & _} m = m
+ˢ-sound {_ & _} {∅}     m = altl m
+ˢ-sound {_ & _} {ε}     m = m
+ˢ-sound {_ & _} {⟦ _ ⟧} m = m
+ˢ-sound {_ & _} {_ *}   m = m
+ˢ-sound {_ & _} {_ + _} m = m
+ˢ-sound {_ & _} {_ ∙ _} m = m
+ˢ-sound {_ & _} {_ & _} m = m

+ˢ-comp : {l r : RegEx}{s : List Σ} → l + r ~ s → l +ˢ r ~ s
+ˢ-comp {∅}     {_}     (altr m) = m
+ˢ-comp {ε}     {∅}     (altl m) = m
+ˢ-comp {ε}     {ε}     m = m
+ˢ-comp {ε}     {⟦ _ ⟧} m = m
+ˢ-comp {ε}     {_ *}   m = m
+ˢ-comp {ε}     {_ + _} m = m
+ˢ-comp {ε}     {_ ∙ _} m = m
+ˢ-comp {ε}     {_ & _} m = m
+ˢ-comp {⟦ _ ⟧} {∅}     (altl m) = m
+ˢ-comp {⟦ _ ⟧} {ε}     m = m
+ˢ-comp {⟦ _ ⟧} {⟦ _ ⟧} m = m
+ˢ-comp {⟦ _ ⟧} {_ *}   m = m
+ˢ-comp {⟦ _ ⟧} {_ + _} m = m
+ˢ-comp {⟦ _ ⟧} {_ ∙ _} m = m
+ˢ-comp {⟦ _ ⟧} {_ & _} m = m
+ˢ-comp {_ *}   {∅}     (altl m) = m
+ˢ-comp {_ *}   {ε}     m = m
+ˢ-comp {_ *}   {⟦ _ ⟧} m = m
+ˢ-comp {_ *}   {_ *}   m = m
+ˢ-comp {_ *}   {_ + _} m = m
+ˢ-comp {_ *}   {_ ∙ _} m = m
+ˢ-comp {_ *}   {_ & _} m = m
+ˢ-comp {_ + _} {∅}     (altl m) = m
+ˢ-comp {_ + _} {ε}     m = m
+ˢ-comp {_ + _} {⟦ _ ⟧} m = m
+ˢ-comp {_ + _} {_ *}   m = m
+ˢ-comp {_ + _} {_ + _} m = m
+ˢ-comp {_ + _} {_ ∙ _} m = m
+ˢ-comp {_ + _} {_ & _} m = m
+ˢ-comp {_ ∙ _} {∅}     (altl m) = m
+ˢ-comp {_ ∙ _} {ε}     m = m
+ˢ-comp {_ ∙ _} {⟦ _ ⟧} m = m
+ˢ-comp {_ ∙ _} {_ *}   m = m
+ˢ-comp {_ ∙ _} {_ + _} m = m
+ˢ-comp {_ ∙ _} {_ ∙ _} m = m
+ˢ-comp {_ ∙ _} {_ & _} m = m
+ˢ-comp {_ & _} {∅}     (altl m) = m
+ˢ-comp {_ & _} {ε}     m = m
+ˢ-comp {_ & _} {⟦ _ ⟧} m = m
+ˢ-comp {_ & _} {_ *}   m = m
+ˢ-comp {_ & _} {_ + _} m = m
+ˢ-comp {_ & _} {_ ∙ _} m = m
+ˢ-comp {_ & _} {_ & _} m = m

&ˢ-sound : {l r : RegEx}{s : List Σ} → l &ˢ r ~ s → l & r ~ s
&ˢ-sound {∅}     {_}     ()
&ˢ-sound {ε}     {ε}     m = m
&ˢ-sound {ε}     {⟦ _ ⟧} m = m
&ˢ-sound {ε}     {_ *}   m = m
&ˢ-sound {ε}     {_ + _} m = m
&ˢ-sound {ε}     {_ ∙ _} m = m
&ˢ-sound {ε}     {_ & _} m = m
&ˢ-sound {⟦ _ ⟧} {ε}     m = m
&ˢ-sound {⟦ _ ⟧} {⟦ _ ⟧} m = m
&ˢ-sound {⟦ _ ⟧} {_ *}   m = m
&ˢ-sound {⟦ _ ⟧} {_ + _} m = m
&ˢ-sound {⟦ _ ⟧} {_ ∙ _} m = m
&ˢ-sound {⟦ _ ⟧} {_ & _} m = m
&ˢ-sound {_ *}   {ε}     m = m
&ˢ-sound {_ *}   {⟦ _ ⟧} m = m
&ˢ-sound {_ *}   {_ *}   m = m
&ˢ-sound {_ *}   {_ + _} m = m
&ˢ-sound {_ *}   {_ ∙ _} m = m
&ˢ-sound {_ *}   {_ & _} m = m
&ˢ-sound {_ + _} {ε}     m = m
&ˢ-sound {_ + _} {⟦ _ ⟧} m = m
&ˢ-sound {_ + _} {_ *}   m = m
&ˢ-sound {_ + _} {_ + _} m = m
&ˢ-sound {_ + _} {_ ∙ _} m = m
&ˢ-sound {_ + _} {_ & _} m = m
&ˢ-sound {_ ∙ _} {ε}     m = m
&ˢ-sound {_ ∙ _} {⟦ _ ⟧} m = m
&ˢ-sound {_ ∙ _} {_ *}   m = m
&ˢ-sound {_ ∙ _} {_ + _} m = m
&ˢ-sound {_ ∙ _} {_ ∙ _} m = m
&ˢ-sound {_ ∙ _} {_ & _} m = m
&ˢ-sound {_ & _} {ε}     m = m
&ˢ-sound {_ & _} {⟦ _ ⟧} m = m
&ˢ-sound {_ & _} {_ *}   m = m
&ˢ-sound {_ & _} {_ + _} m = m
&ˢ-sound {_ & _} {_ ∙ _} m = m
&ˢ-sound {_ & _} {_ & _} m = m

&ˢ-comp : {l r : RegEx}{s : List Σ} → l & r ~ s → l &ˢ r ~ s
&ˢ-comp {∅}     {_}     (and () _)
&ˢ-comp {ε}     {∅}     (and m ())
&ˢ-comp {ε}     {ε}     m = m
&ˢ-comp {ε}     {⟦ _ ⟧} m = m
&ˢ-comp {ε}     {_ *}   m = m
&ˢ-comp {ε}     {_ + _} m = m
&ˢ-comp {ε}     {_ ∙ _} m = m
&ˢ-comp {ε}     {_ & _} m = m
&ˢ-comp {⟦ _ ⟧} {∅}     (and _ ())
&ˢ-comp {⟦ _ ⟧} {ε}     m = m
&ˢ-comp {⟦ _ ⟧} {⟦ _ ⟧} m = m
&ˢ-comp {⟦ _ ⟧} {_ *}   m = m
&ˢ-comp {⟦ _ ⟧} {_ + _} m = m
&ˢ-comp {⟦ _ ⟧} {_ ∙ _} m = m
&ˢ-comp {⟦ _ ⟧} {_ & _} m = m
&ˢ-comp {_ *}   {∅}     (and m ())
&ˢ-comp {_ *}   {ε}     m = m
&ˢ-comp {_ *}   {⟦ _ ⟧} m = m
&ˢ-comp {_ *}   {_ *}   m = m
&ˢ-comp {_ *}   {_ + _} m = m
&ˢ-comp {_ *}   {_ ∙ _} m = m
&ˢ-comp {_ *}   {_ & _} m = m
&ˢ-comp {_ + _} {∅}     (and m ())
&ˢ-comp {_ + _} {ε}     m = m
&ˢ-comp {_ + _} {⟦ _ ⟧} m = m
&ˢ-comp {_ + _} {_ *}   m = m
&ˢ-comp {_ + _} {_ + _} m = m
&ˢ-comp {_ + _} {_ ∙ _} m = m
&ˢ-comp {_ + _} {_ & _} m = m
&ˢ-comp {_ ∙ _} {∅}     (and m ())
&ˢ-comp {_ ∙ _} {ε}     m = m
&ˢ-comp {_ ∙ _} {⟦ _ ⟧} m = m
&ˢ-comp {_ ∙ _} {_ *}   m = m
&ˢ-comp {_ ∙ _} {_ + _} m = m
&ˢ-comp {_ ∙ _} {_ ∙ _} m = m
&ˢ-comp {_ ∙ _} {_ & _} m = m
&ˢ-comp {_ & _} {∅}     (and m ())
&ˢ-comp {_ & _} {ε}     m = m
&ˢ-comp {_ & _} {⟦ _ ⟧} m = m
&ˢ-comp {_ & _} {_ *}   m = m
&ˢ-comp {_ & _} {_ + _} m = m
&ˢ-comp {_ & _} {_ ∙ _} m = m
&ˢ-comp {_ & _} {_ & _} m = m
