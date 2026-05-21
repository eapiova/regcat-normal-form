{-# OPTIONS --safe #-}

-- Tait-style rebuild prototype (Phase K). Top + Sigma fragment.
-- Verbatim fork of TReg.Prelude.

module Tait.Prelude where

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

Type : Set₁
Type = Set

infixl 30 _∙_

_∙_ : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
_∙_ = trans

cong₃ :
  {A B C D : Set} (f : A -> B -> C -> D)
  {a a' : A} {b b' : B} {c c' : C}
  -> a ≡ a' -> b ≡ b' -> c ≡ c'
  -> f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

transport : {A B : Type} -> A ≡ B -> A -> B
transport p = subst (λ X -> X) p
