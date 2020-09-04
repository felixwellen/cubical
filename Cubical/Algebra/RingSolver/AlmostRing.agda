{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.AlmostRing where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.Semigroup    hiding (⟨_⟩)
open import Cubical.Algebra.Monoid    hiding (⟨_⟩)
open import Cubical.Algebra.AbGroup   hiding (⟨_⟩)

private
  variable
    ℓ : Level

record IsAlmostRing {R : Type ℓ}
                  (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor isalmostring

  field
    +IsMonoid : IsMonoid 0r _+_
    ·IsMonoid : IsMonoid 1r _·_
    +Comm : (x y : R) → x + y ≡ y + x
    ·Comm : (x y : R) → x · y ≡ y · x
    ·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
    ·DistL+ :  (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
    -Comm· : (x y : R) → - (x · y) ≡ (- x) · y
    -Dist+ : (x y : R) → - (x + y) ≡ (- x) + (- y)
    0LeftAnnihilates : (x : R) → 0r · x ≡ 0r
    0RightAnnihilates : (x : R) → x · 0r ≡ 0r

  open IsMonoid +IsMonoid public
    renaming
      ( assoc       to +Assoc
      ; identity    to +Identity
      ; lid         to +Lid
      ; rid         to +Rid
      ; isSemigroup to +IsSemigroup)

  open IsMonoid ·IsMonoid public
    renaming
      ( assoc       to ·Assoc
      ; identity    to ·Identity
      ; lid         to ·Lid
      ; rid         to ·Rid
      ; isSemigroup to ·IsSemigroup )
    hiding
      ( is-set ) -- We only want to export one proof of this

record AlmostRing : Type (ℓ-suc ℓ) where

  constructor almostring

  field
    Carrier : Type ℓ
    0r      : Carrier
    1r      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    isAlmostRing  : IsAlmostRing 0r 1r _+_ _·_ -_

  infixl 8 _·_
  infixl 7 -_
  infixl 6 _+_

  open IsAlmostRing isAlmostRing public

  _^_ : Carrier → ℕ → Carrier
  x ^ 0 = 1r
  x ^ 1 = x
  x ^ ℕ.suc k = x · (x ^ k)

-- Extractor for the carrier type
⟨_⟩ : AlmostRing → Type ℓ
⟨_⟩ = AlmostRing.Carrier

isSetAlmostRing : (R : AlmostRing {ℓ}) → isSet ⟨ R ⟩
isSetAlmostRing R = R .AlmostRing.isAlmostRing .IsAlmostRing.·IsMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set
