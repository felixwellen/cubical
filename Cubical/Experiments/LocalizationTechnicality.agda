{-
  The goal of this file is to implement the Lemma 2.7 of the modalities paper:
  
    https://arxiv.org/abs/1706.07526
-}

{-# OPTIONS --cubical #-}
module Cubical.Experiments.LocalizationTechnicality where

open import Cubical.Core.Everything

open import Cubical.Foundations.Everything

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
      secCong = λ g h → rightInverseCong g h , λ p _ → p})))
    where rightInverse : (X → Y) → (ℐ X → Y)
          rightInverse g (α x) = g x
          rightInverse g (ext a f cₐ) = fst
            (sectionOfEquiv _ (YisLocal a)) (λ bₐ → rightInverse g (f bₐ)) cₐ
          rightInverse g (is-ext a f bₐ i) = snd
            (sectionOfEquiv _ (YisLocal a)) (λ bₐ → rightInverse g (f bₐ)) i bₐ
            
          {-
            In the following module, a right inverse on the path spaces is constructed.
            One square will be central:          

                g(ext a f (F a bₐ)) ──H0──  h(ext a f (F a bₐ))
                        |                          |
       g(is-ext a f _)  |                          |  h(is-ext a f _)
                        |                          |
                     g(f bₐ) ───────H1────────── h(f bₐ)

            When we fill the square in the last case of the inductive definition
            of 'rightInverseCong', the upper and lower path will already be fixed
            by the induction hypothesis (H1) and another case (H0).
          -}
          module _ (g h : ℐ X → Y) (q : g ∘ α ≡ h ∘ α) where
            module _ (a : A) (f : B a → ℐ X) where 
              equivCong : isEquiv (λ (p : (g ∘ (ext a f)) ≡ (h ∘ (ext a f)))
                             → cong (λ (f : C a → Y) → f ∘ (F a)) p)
              equivCong = isEquivCong (_ , (YisLocal a))
              
              Ylocal : g ∘ (ext a f) ∘ F a ≡ h ∘ (ext a f) ∘ F a
                       → g ∘ (ext a f) ≡ h ∘ (ext a f)
              Ylocal = fst (sectionOfEquiv _ equivCong)

              module _ (bₐ : B a) where
                γ : ext a f (F a bₐ) ≡ f bₐ
                γ = is-ext a f bₐ
                
                H0 : (H1 : g (f bₐ) ≡ h (f bₐ))
                     → g(ext a f (F a bₐ)) ≡ h(ext a f (F a bₐ))
                H0 H1 = transport (λ i → g (γ (~ i)) ≡ h (γ (~ i))) H1
              
              
            rightInverseCong : g ≡ h
            rightInverseCong i (α x) = q i x
            rightInverseCong i (ext a f cₐ) = H i
              where
                H1 : g ∘ f ≡ h ∘ f
                H1 j bₐ = rightInverseCong j (f bₐ)

                H : g (ext a f cₐ) ≡ h (ext a f cₐ)
                H j = Ylocal a f (λ k bₐ → H0 a f bₐ (λ l → H1 l bₐ) k) j cₐ
                
            rightInverseCong i (is-ext a f bₐ j) = H'' i1 i j
              where
                H1 : g ∘ f ≡ h ∘ f
                H1 j bₐ = rightInverseCong j (f bₐ)

                H0' : g ∘ (ext a f) ∘ (F a) ≡ h ∘ (ext a f) ∘ (F a)
                H0' = λ k bₐ → H0 a f bₐ (λ l → H1 l bₐ) k
                Ylocal' : (λ k (bₐ : B a) → Ylocal a f H0' k (F a bₐ))
                          ≡ H0'
                Ylocal' = (snd (sectionOfEquiv _ (equivCong a f))) H0'
                
                p = γ a f bₐ

                H' : (j : I) → g (p j) ≡ h (p j)
                H' j = transp
                        (λ k → g (p ((~ k) ∨ j)) ≡ h (p ((~ k) ∨ j)))
                        j (λ l → H1 l bₐ)
                
                H'' : I → I → I → Y
                H'' i j k = hcomp (λ i → λ { (k = i0) → Ylocal' (~ i) j bₐ;
                                             (k = i1) → H1 j bₐ;
                                             (j = i0) → g (p k);
                                             (j = i1) → h (p k)})
                                  (H' k j) 
