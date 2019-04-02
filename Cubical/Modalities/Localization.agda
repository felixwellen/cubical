{-
  The goal (far from achieved yet...) of this file is to implement the
  construction of localizations from the modalities paper:

    https://arxiv.org/abs/1706.07526

  A technical part (Lemma 2.7) is in the module 'LocalizationTechnicality',
  since it takes a long time to check.
-}

{-# OPTIONS --cubical #-}
module Cubical.Modalities.Localization where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Modalities.LocalizationTechnicality

{-
  Localization at a family of functions, from the modalities paper.

  The goal is to construct a HIT, that localizes at a family of maps

    F : (a : A) → B a → C a

  A type X is local wrt F, if all maps f:B(a)->X can be uniquely
  extended along F(a):

    B(a) ─f─→ X
     |       ↗
    F(a)   ∃!
     ↓   /
    C(a)

  In the 'first-approximation' a HIT 'ℐ X' is constructed, that such
  that '(ℐ X → Y) ≃ (X → Y)'. 'ℐ X' is not the localization.
-}

{-
  Goal: Show that ap having a section is the same as Δ_f having a section
-}

record pullback {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″}
                (f : A → C) (g : B → C) : Set (ℓ-max ℓ (ℓ-max ℓ′ ℓ″)) where
  field
    a : A
    b : B
    p : f a ≡ g b

open pullback

private
  Δ : ∀ {ℓ} {A B : Set ℓ} → (f : A → B) → (A → pullback f f)
  a (Δ f x) = x
  b (Δ f x) = x
  (p (Δ f x)) _ = f x
  
