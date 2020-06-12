{-# OPTIONS --cubical --safe #-}

module Cubical.Algebra.F2 where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.HLevels
open import Cubical.HITs.S1

open import Cubical.Structures.Ring
open import Cubical.Structures.QuotientRing
open import Cubical.Data.Unit
open import Cubical.Data.Bool

module _ where
  xor : Bool → Bool → Bool
  xor false false = false
  xor false true = true
  xor true false = true
  xor true true = false

  xor-assoc : ∀ x y z → xor x (xor y z) ≡ xor (xor x y) z
  xor-assoc false false false = refl
  xor-assoc false false true = refl
  xor-assoc false true false = refl
  xor-assoc false true true = refl
  xor-assoc true false false = refl
  xor-assoc true false true = refl
  xor-assoc true true false = refl
  xor-assoc true true true = refl

  xor-rid : ∀ x → xor x false ≡ x
  xor-rid false = refl
  xor-rid true = refl

  xor-comm : ∀ x y → xor x y ≡ xor y x
  xor-comm false false = refl
  xor-comm false true = refl
  xor-comm true false = refl
  xor-comm true true = refl

  xor-rinv : ∀ x → xor x x ≡ false
  xor-rinv false = refl
  xor-rinv true = refl

  and : Bool → Bool → Bool
  and false false = false
  and false true = false
  and true false = false
  and true true = true

  and-assoc : ∀ x y z → and x (and y z) ≡ and (and x y) z
  and-assoc false false false = refl
  and-assoc false false true = refl
  and-assoc false true false = refl
  and-assoc false true true = refl
  and-assoc true false false = refl
  and-assoc true false true = refl
  and-assoc true true false = refl
  and-assoc true true true = refl

  and-rid : ∀ x → and x true ≡ x
  and-rid false = refl
  and-rid true = refl

  and-lid : ∀ x → and true x ≡ x
  and-lid false = refl
  and-lid true = refl

  and-comm : ∀ x y → and x y ≡ and y x
  and-comm false false = refl
  and-comm false true = refl
  and-comm true false = refl
  and-comm true true = refl

  xor-ldist : ∀ x y z → and (xor x y) z ≡ xor (and x z) (and y z)
  xor-ldist false false false = refl
  xor-ldist false false true = refl
  xor-ldist false true false = refl
  xor-ldist false true true = refl
  xor-ldist true false false = refl
  xor-ldist true false true = refl
  xor-ldist true true false = refl
  xor-ldist true true true = refl

  xor-rdist : ∀ x y z → and x (xor y z) ≡ xor (and x y) (and x z)
  xor-rdist false false false = refl
  xor-rdist false false true = refl
  xor-rdist false true false = refl
  xor-rdist false true true = refl
  xor-rdist true false false = refl
  xor-rdist true false true = refl
  xor-rdist true true false = refl
  xor-rdist true true true = refl

𝔽₂ : Ring {ℓ-zero}
𝔽₂ = createRing
       Bool
       isSetBool
       (record
          { 0r = false
          ; 1r = true
          ; _+_ = xor
          ; -_ = λ x → x
          ; _·_ = and
          ; +-assoc = xor-assoc
          ; +-rid = xor-rid
          ; +-comm = xor-comm
          ; +-rinv = xor-rinv
          ; ·-assoc = and-assoc
          ; ·-lid = and-lid
          ; ·-rid = and-rid
          ; ldist = xor-ldist
          ; rdist = xor-rdist
          })
