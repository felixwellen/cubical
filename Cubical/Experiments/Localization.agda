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
            
          {-
            In the following module, a right inverse on the path spaces is constructed.
            One square will be central:

                g(ext a f (F a b)) ≡ h(ext a f (F a b))
                      ≡                     ≡
                     g(f b)        ≡       h(f b)

            We construct the upper equality ('H0') as a transport of the lower one ('H1').
            This will make all the necessary degenrations fit in the induction below.
            The last step deviates from the proof in the article. 
          -}
          module _ (g h : ℐ X → Y) (q : g ∘ α ≡ h ∘ α) where
            module _ (a : A) (f : B a → ℐ X) where 
              equivCong : isEquiv (λ (p : (g ∘ (ext a f)) ≡ (h ∘ (ext a f)))
                             → cong (λ (f : C a → Y) → f ∘ (F a)) p)
              equivCong = isEquivCong (_ , (YisLocal a))

              module _ (bₐ : B a) where
                γ : ext a f (F a bₐ) ≡ f bₐ
                γ = is-ext a f bₐ
                
                H0 : (H1 : g (f bₐ) ≡ h (f bₐ))
                     → g(ext a f (F a bₐ)) ≡ h(ext a f (F a bₐ))
                H0 H1 = transport (cong (λ z → g z ≡ h z) (sym γ)) H1
              
            rightInverseCong : g ≡ h
            rightInverseCong i (α x) = q i x
            rightInverseCong i (ext a f cₐ) = H i
              where
                Ylocal : g ∘ (ext a f) ∘ F a ≡ h ∘ (ext a f) ∘ F a
                         → g ∘ (ext a f) ≡ h ∘ (ext a f)
                Ylocal = fst (sectionOfEquiv _ (equivCong a f))
              
                H : g (ext a f cₐ) ≡ h (ext a f cₐ)
                H j = Ylocal (λ i bₐ → H0 a f bₐ (λ j → rightInverseCong j (f bₐ)) i) j cₐ
                
            rightInverseCong i (is-ext a f bₐ j) = {!!} -- H j i
              -- some degenerations still don't match up
              where
                p = γ a f bₐ
                
                H : (j : I) → g (p j) ≡ h (p j)
                H j = transport
                        (λ k → g (p (k ∧ j)) ≡ h (p (k ∧ j)))
                        (H0 a f bₐ (λ k → rightInverseCong k (f bₐ)))
