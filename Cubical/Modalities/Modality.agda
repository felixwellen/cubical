{-# OPTIONS --cubical --safe #-}
module Cubical.Modalities.Modality where

{- 
  translated from 
  https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/types/Modality.agda
-}

open import Cubical.Core.Everything

record Modality ℓ : Set (ℓ-suc ℓ) where
  field
    isModal : Set ℓ → Set ℓ
    isModalIsProp : {A : Set ℓ} → isProp (isModal A)

    ◯ : Set ℓ → Set ℓ
    ◯-isModal : {A : Set ℓ} → isModal (◯ A)
                                         
    η : {A : Set ℓ} → A → ◯ A

    ◯-elim : {A : Set ℓ} {B : ◯ A → Set ℓ}
      (B-modal : (x : ◯ A) → isModal (B x))
      → ((x : A) → (B (η x))) → ((x : ◯ A) → B x)
                                               
    ◯-elim-β : {A : Set ℓ} {B : ◯ A → Set ℓ}
      (B-modal : (x : ◯ A) → isModal (B x)) (f : (x : A) → (B (η x)))
      → (a : A) → ◯-elim B-modal f (η a) ≡ f a

    ◯-=-isModal : {A : Set ℓ} (x y : ◯ A) → isModal (x ≡ y)
    
  ○-Types : Set (ℓ-suc ℓ)
  ○-Types = Σ[ A ∈ Set ℓ ] isModal A
  
  
  
