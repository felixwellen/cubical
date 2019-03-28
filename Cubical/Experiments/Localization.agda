{-
  The goal (far from achieved yet...) of this file is to implement the
construction of
  localizations from the modalities paper https://arxiv.org/abs/1706.07526
-}


{-# OPTIONS --cubical #-}
module Cubical.Experiments.Localization where

open import Cubical.Core.Everything

open import Cubical.Foundations.Everything


{-
  Localization at a family of functions, from the modalities paper.
  The goal is to construct a HIT, that localizes at a family of maps

    F : (a : A) → B a → C a

  A type X is local wrt F, if all maps f:B(a)->X can be uniquely
extended along
  F(a):

    B(a) ─f─→ X
     |       ↗
    F(a)   ∃!
     ↓   /
    C(a)

-}

module first-approximation {ℓ} {A : Set ℓ} {B C : A → Set ℓ} (F : (a : A) → B a → C a) where
  data ℐ (X : Set ℓ) : Set ℓ where
    α : X → ℐ X
    ext : (a : A) → (B a → ℐ X) → (C a → ℐ X)
    is-ext : (a : A) (f : B a → ℐ X) (b : B a) → ext a f (F a b) ≡ f b

  ℐ-unit-at : (X : Set ℓ) → X → ℐ X
  ℐ-unit-at X x = α x

  isF-Local : ∀ (X : Set ℓ) → Set ℓ
  isF-Local X = (a : A) → isEquiv (λ (f : C a → X) → f ∘ (F a))

  {-
    Lemma 2.7
  -}
  HomIntoF-localWorks : ∀ (X Y : Set ℓ) → (isF-Local Y)
    → isEquiv (λ (f : ℐ X → Y) → f ∘ α)
  HomIntoF-localWorks X Y YisLocal = snd (pathSplitToEquiv ((λ (f : ℐ X → Y) → f ∘ α) ,
    (record {
      s = rightInverse ;
      sec = λ f → refl ;
      secCong = λ g h → {!!} , {!!}})))
    where rightInverse : (X → Y) → (ℐ X → Y)
          rightInverse g (α x) = g x
          rightInverse g (ext a f cₐ) = fst
            (sectionOfEquiv _ (YisLocal a)) (λ bₐ → rightInverse g (f bₐ)) cₐ
          rightInverse g (is-ext a f bₐ i) = snd
            (sectionOfEquiv _ (YisLocal a)) (λ bₐ → rightInverse g (f bₐ)) i bₐ

          equivCong : ∀ (a : A) → (f₁ f₂ : C a → Y)
            → isEquiv (λ (p : f₁ ≡ f₂) → cong (λ (f : C a → Y) → f ∘ (F a)) p)
          equivCong a g h = isEquivCong (_ , (YisLocal a))

          rightInverseCong : (g h : ℐ X → Y) → g ∘ α ≡ h ∘ α → g ≡ h
          rightInverseCong _ _ q i (α x) = q i x
          rightInverseCong g h q i (ext a f cₐ) = H i
            where
              H : g (ext a f cₐ) ≡ h (ext a f cₐ)
              H j =
                fst
                  (sectionOfEquiv _
                    (equivCong a
                      (g ∘ (ext a f)) (h ∘ (ext a f))))
                 (λ j b → ((λ i → g (is-ext a f b i))
                         ∙ (λ i → rightInverseCong g h q i (f b))
                         ∙ (λ i → h (is-ext a f b i)) ⁻¹) j)
                 j cₐ 
          rightInverseCong g h q i (is-ext a f bₐ j) = H j i
            where
              γ : ext a f (F a bₐ) ≡ f bₐ
              γ = is-ext a f bₐ

              H : (i : I) → g (γ i) ≡ h (γ i)
              H = {!fst
                  (sectionOfEquiv _
                    (equivCong a
                      (g ∘ (ext a f)) (h ∘ (ext a f))))!}

