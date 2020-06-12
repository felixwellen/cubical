{-# OPTIONS --cubical --safe #-}

module Cubical.Algebra.ZeroRing where


open import Cubical.Foundations.Everything
open import Cubical.Foundations.HLevels
open import Cubical.HITs.S1

open import Cubical.Structures.Ring
open import Cubical.Structures.QuotientRing
open import Cubical.Data.Unit
open import Cubical.Data.Bool

ZeroRing : Ring {ℓ-zero}
ZeroRing = createRing
             Unit
             (isProp→isOfHLevelSuc 1 isPropUnit)
             (record
                { 0r = tt
                ; 1r = tt
                ; _+_ = λ _ _ → tt
                ; -_ = λ _ → tt
                ; _·_ = λ _ _ → tt
                ; +-assoc = λ _ _ _ → refl
                ; +-rid = λ _ → refl
                ; +-comm = λ _ _  → refl
                ; +-rinv = λ _  → refl
                ; ·-assoc = λ _ _ _ → refl
                ; ·-lid = λ _ → refl
                ; ·-rid = λ _ → refl
                ; ldist = λ _ _ _ → refl
                ; rdist = λ _ _ _ → refl
                })
