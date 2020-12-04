{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.AlgebraEvaluationHomomorphism where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Vec

open import Cubical.Algebra.RingSolver.RawAlgebra
open import Cubical.Algebra.RingSolver.AlgebraHornerForms
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

private
  variable
    ℓ : Level

module HomomorphismProperties (R : CommRing {ℓ}) where
  private
    νR = CommRing→RawℤAlgebra R
  open CommRingStr (snd R)
  open Theory (CommRing→Ring R)
  open IteratedHornerOperations νR

  EvalHom+0 : (n : ℕ) (P : IteratedHornerForms νR n) (xs : Vec ⟨ νR ⟩ n)
      → eval n (0ₕ +ₕ P) xs ≡ eval n P xs
  EvalHom+0 ℕ.zero (const x) [] = cong (scalar R) (+Ridℤ x)
  EvalHom+0 (ℕ.suc n) P xs = refl

  Eval0H : (n : ℕ) (xs : Vec ⟨ νR ⟩ n)
         → eval {A = νR} n 0ₕ xs ≡ 0r
  Eval0H .ℕ.zero [] = refl
  Eval0H .(ℕ.suc _) (x ∷ xs) = refl

  Eval1ₕ : (n : ℕ) (xs : Vec ⟨ νR ⟩ n)
         → eval {A = νR} n 1ₕ xs ≡ 1r
  Eval1ₕ .ℕ.zero [] = refl
  Eval1ₕ (ℕ.suc n) (x ∷ xs) =
    eval (ℕ.suc n) 1ₕ (x ∷ xs)                             ≡⟨ refl ⟩
    eval (ℕ.suc n) (0H ·X+ 1ₕ) (x ∷ xs)                    ≡⟨ refl ⟩
    eval {A = νR} (ℕ.suc n) 0H (x ∷ xs) · x + eval n 1ₕ xs ≡⟨ cong (λ u → u · x + eval n 1ₕ xs)
                                                                   (Eval0H _ (x ∷ xs)) ⟩
    0r · x + eval n 1ₕ xs                                   ≡⟨ cong (λ u → 0r · x + u)
                                                                    (Eval1ₕ _ xs) ⟩
    0r · x + 1r                                            ≡⟨ cong (λ u → u + 1r)
                                                                   (0LeftAnnihilates _) ⟩
    0r + 1r                                                ≡⟨ +Lid _ ⟩
    1r ∎

  -EvalDist :
    (n : ℕ) (P : IteratedHornerForms νR n) (xs : Vec ⟨ νR ⟩ n)
    → eval n (-ₕ P) xs ≡ - eval n P xs
  -EvalDist .ℕ.zero (const x) []   = -DistScalar R x
  -EvalDist          n       0H  xs =
    eval n (-ₕ 0H) xs  ≡⟨ Eval0H n xs ⟩
    0r                        ≡⟨ sym 0Selfinverse ⟩
    - 0r                      ≡⟨ cong -_ (sym (Eval0H n xs)) ⟩
    - eval n 0H xs     ∎
  -EvalDist .(ℕ.suc _) (P ·X+ Q) (x ∷ xs) =
      eval (ℕ.suc _) (-ₕ (P ·X+ Q)) (x ∷ xs)
    ≡⟨ refl ⟩
      eval (ℕ.suc _) ((-ₕ P) ·X+ (-ₕ Q)) (x ∷ xs)
    ≡⟨ refl ⟩
      (eval (ℕ.suc _) (-ₕ P) (x ∷ xs)) · x + eval _ (-ₕ Q) xs
    ≡⟨ cong (λ u → u · x + eval _ (-ₕ Q) xs) (-EvalDist _ P _) ⟩
      (- eval (ℕ.suc _) P (x ∷ xs)) · x + eval _ (-ₕ Q) xs
    ≡⟨ cong (λ u → (- eval (ℕ.suc _) P (x ∷ xs)) · x + u) (-EvalDist _ Q _) ⟩
      (- eval (ℕ.suc _) P (x ∷ xs)) · x + - eval _ Q xs
    ≡[ i ]⟨ -DistL· (eval (ℕ.suc _) P (x ∷ xs)) x i +  - eval _ Q xs ⟩
      - ((eval (ℕ.suc _) P (x ∷ xs)) · x) + (- eval _ Q xs)
    ≡⟨ -Dist _ _ ⟩
      - ((eval (ℕ.suc _) P (x ∷ xs)) · x + eval _ Q xs)
    ≡⟨ refl ⟩
      - eval (ℕ.suc _) (P ·X+ Q) (x ∷ xs) ∎

  +Homeval :
    (n : ℕ) (P Q : IteratedHornerForms νR n) (xs : Vec ⟨ νR ⟩ n)
    → eval n (P +ₕ Q) xs ≡ (eval n P xs) + (eval n Q xs)
  +Homeval .ℕ.zero (const x) (const y) [] = +HomScalar R x y
  +Homeval n 0H Q xs =
    eval n (0H +ₕ Q) xs            ≡⟨ refl ⟩
    eval n Q xs                    ≡⟨ sym (+Lid _) ⟩
    0r + eval n Q xs               ≡⟨ cong (λ u → u + eval n Q xs) (sym (Eval0H n xs)) ⟩
    eval n 0H xs + eval n Q xs ∎
  +Homeval .(ℕ.suc _) (P ·X+ Q) 0H xs =
    eval (ℕ.suc _) ((P ·X+ Q) +ₕ 0H) xs                    ≡⟨ refl ⟩
    eval (ℕ.suc _) (P ·X+ Q) xs                            ≡⟨ sym (+Rid _) ⟩
    eval (ℕ.suc _) (P ·X+ Q) xs + 0r
   ≡⟨ cong (λ u → eval (ℕ.suc _) (P ·X+ Q) xs + u) (sym (Eval0H _ xs)) ⟩
    eval (ℕ.suc _) (P ·X+ Q) xs + eval (ℕ.suc _) 0H xs ∎
  +Homeval .(ℕ.suc _) (P ·X+ Q) (S ·X+ T) (x ∷ xs) =
    eval (ℕ.suc _) ((P ·X+ Q) +ₕ (S ·X+ T)) (x ∷ xs)
   ≡⟨ refl ⟩
    eval (ℕ.suc _) ((P +ₕ S) ·X+ (Q +ₕ T)) (x ∷ xs)
   ≡⟨ refl ⟩
    (eval (ℕ.suc _) (P +ₕ S) (x ∷ xs)) · x + eval _ (Q +ₕ T) xs
   ≡⟨ cong (λ u → (eval (ℕ.suc _) (P +ₕ S) (x ∷ xs)) · x + u) (+Homeval _ Q T xs) ⟩
    (eval (ℕ.suc _) (P +ₕ S) (x ∷ xs)) · x + (eval _ Q xs + eval _ T xs)
   ≡⟨ cong (λ u → u · x + (eval _ Q xs + eval _ T xs)) (+Homeval (ℕ.suc _) P S (x ∷ xs)) ⟩
    (eval (ℕ.suc _) P (x ∷ xs) + eval (ℕ.suc _) S (x ∷ xs)) · x
    + (eval _ Q xs + eval _ T xs)
   ≡⟨ cong (λ u → u + (eval _ Q xs + eval _ T xs)) (·Ldist+ _ _ _) ⟩
    (eval (ℕ.suc _) P (x ∷ xs)) · x + (eval (ℕ.suc _) S (x ∷ xs)) · x
    + (eval _ Q xs + eval _ T xs)
   ≡⟨ +ShufflePairs _ _ _ _ ⟩
    ((eval (ℕ.suc _) P (x ∷ xs)) · x + eval _ Q xs)
    + ((eval (ℕ.suc _) S (x ∷ xs)) · x + eval _ T xs)
   ≡⟨ refl ⟩
    eval (ℕ.suc _) (P ·X+ Q) (x ∷ xs)
    + eval (ℕ.suc _) (S ·X+ T) (x ∷ xs) ∎

  ⋆Homeval : (n : ℕ)
             (r : IteratedHornerForms νR n)
             (P : IteratedHornerForms νR (ℕ.suc n)) (x : ⟨ νR ⟩) (xs : Vec ⟨ νR ⟩ n)
           → eval (ℕ.suc n) (r ⋆ P) (x ∷ xs) ≡ eval n r xs · eval (ℕ.suc n) P (x ∷ xs)


  ⋆0LeftAnnihilates :
    (n : ℕ) (P : IteratedHornerForms νR (ℕ.suc n)) (xs : Vec ⟨ νR ⟩ (ℕ.suc n))
    → eval (ℕ.suc n) (0ₕ ⋆ P) xs ≡ 0r

  ·Homeval : (n : ℕ) (P Q : IteratedHornerForms νR n) (xs : Vec ⟨ νR ⟩ n)
    → eval n (P ·ₕ Q) xs ≡ (eval n P xs) · (eval n Q xs)

  ⋆0LeftAnnihilates n 0H xs = Eval0H (ℕ.suc n) xs
  ⋆0LeftAnnihilates n (P ·X+ Q) (x ∷ xs) =
      eval (ℕ.suc n) (0ₕ ⋆ (P ·X+ Q)) (x ∷ xs)                    ≡⟨ refl ⟩
      eval (ℕ.suc n) ((0ₕ ⋆ P) ·X+ (0ₕ ·ₕ Q)) (x ∷ xs)             ≡⟨ refl ⟩
      (eval (ℕ.suc n) (0ₕ ⋆ P) (x ∷ xs)) · x + eval n (0ₕ ·ₕ Q) xs
    ≡⟨ cong (λ u → (u · x) + eval _ (0ₕ ·ₕ Q) _) (⋆0LeftAnnihilates n P (x ∷ xs)) ⟩
      0r · x + eval n (0ₕ ·ₕ Q) xs
    ≡⟨ cong (λ u → u + eval _ (0ₕ ·ₕ Q) _) (0LeftAnnihilates _) ⟩
      0r + eval n (0ₕ ·ₕ Q) xs
    ≡⟨ +Lid _ ⟩
      eval n (0ₕ ·ₕ Q) xs
    ≡⟨ ·Homeval n 0ₕ Q _ ⟩
      eval n 0ₕ xs · eval n Q xs
    ≡⟨ cong (λ u → u · eval n Q xs) (Eval0H _ xs) ⟩
      0r · eval n Q xs
    ≡⟨ 0LeftAnnihilates _ ⟩
      0r ∎

  ⋆Homeval n r 0H x xs =
    eval (ℕ.suc n) (r ⋆ 0H) (x ∷ xs)         ≡⟨ refl ⟩
    0r                                       ≡⟨ sym (0RightAnnihilates _) ⟩
    eval n r xs · 0r                         ≡⟨ refl ⟩
    eval n r xs · eval {A = νR} (ℕ.suc n) 0H (x ∷ xs) ∎
  ⋆Homeval n r (P ·X+ Q) x xs =
      eval (ℕ.suc n) (r ⋆ (P ·X+ Q)) (x ∷ xs)                    ≡⟨ refl ⟩
      eval (ℕ.suc n) ((r ⋆ P) ·X+ (r ·ₕ Q)) (x ∷ xs)              ≡⟨ refl ⟩
      (eval (ℕ.suc n) (r ⋆ P) (x ∷ xs)) · x + eval n (r ·ₕ Q) xs
    ≡⟨ cong (λ u → u · x + eval n (r ·ₕ Q) xs) (⋆Homeval n r P x xs) ⟩
      (eval n r xs · eval (ℕ.suc n) P (x ∷ xs)) · x + eval n (r ·ₕ Q) xs
    ≡⟨ cong (λ u → (eval n r xs · eval (ℕ.suc n) P (x ∷ xs)) · x + u) (·Homeval n r Q xs) ⟩
      (eval n r xs · eval (ℕ.suc n) P (x ∷ xs)) · x + eval n r xs · eval n Q xs
    ≡⟨ cong (λ u → u  + eval n r xs · eval n Q xs) (sym (·Assoc _ _ _)) ⟩
      eval n r xs · (eval (ℕ.suc n) P (x ∷ xs) · x) + eval n r xs · eval n Q xs
    ≡⟨ sym (·Rdist+ _ _ _) ⟩
      eval n r xs · ((eval (ℕ.suc n) P (x ∷ xs) · x) + eval n Q xs)
    ≡⟨ refl ⟩
      eval n r xs · eval (ℕ.suc n) (P ·X+ Q) (x ∷ xs) ∎

  combineCases :
    (n : ℕ) (Q : IteratedHornerForms νR n) (P S : IteratedHornerForms νR (ℕ.suc n))
    (xs : Vec ⟨ νR ⟩ (ℕ.suc n))
    → eval (ℕ.suc n) ((P ·X+ Q) ·ₕ S) xs ≡ eval (ℕ.suc n) (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) xs
  combineCases n Q P S (x ∷ xs) with (P ·ₕ S)
  ... | 0H =
    eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)                ≡⟨ sym (+Lid _) ⟩
    0r + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)           ≡⟨ cong (λ u → u + eval _ (Q ⋆ S) (x ∷ xs)) lemma ⟩
    eval (ℕ.suc n) (0H ·X+ 0ₕ) (x ∷ xs)
    + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)              ≡⟨ sym (+Homeval (ℕ.suc n)
                                                      (0H ·X+ 0ₕ) (Q ⋆ S) (x ∷ xs)) ⟩
    eval (ℕ.suc n) ((0H ·X+ 0ₕ) +ₕ (Q ⋆ S)) (x ∷ xs) ∎
    where lemma : 0r ≡ eval (ℕ.suc n) (0H ·X+ 0ₕ) (x ∷ xs)
          lemma = 0r
                ≡⟨ sym (+Rid _) ⟩
                  0r + 0r
                ≡⟨ cong (λ u → u + 0r) (sym (0LeftAnnihilates _)) ⟩
                  0r · x + 0r
                ≡⟨ cong (λ u → 0r · x + u) (sym (Eval0H _ xs)) ⟩
                  0r · x + eval n 0ₕ xs
                ≡⟨ cong (λ u → u · x + eval n 0ₕ xs) (sym (Eval0H _ (x ∷ xs))) ⟩
                  eval {A = νR} (ℕ.suc n) 0H (x ∷ xs) · x + eval n 0ₕ xs
                ≡⟨ refl ⟩
                  eval (ℕ.suc n) (0H ·X+ 0ₕ) (x ∷ xs) ∎
  ... | (_ ·X+ _) = refl

  ·Homeval .ℕ.zero (const x) (const y) [] = ·HomScalar R x y
  ·Homeval (ℕ.suc n) 0H Q xs =
    eval (ℕ.suc n) (0H ·ₕ Q) xs        ≡⟨ Eval0H _ xs ⟩
    0r                                 ≡⟨ sym (0LeftAnnihilates _) ⟩
    0r · eval (ℕ.suc n) Q xs          ≡⟨ cong (λ u → u · eval _ Q xs) (sym (Eval0H _ xs)) ⟩
    eval (ℕ.suc n) 0H xs · eval (ℕ.suc n) Q xs ∎
  ·Homeval (ℕ.suc n) (P ·X+ Q) S (x ∷ xs) =
      eval (ℕ.suc n) ((P ·X+ Q) ·ₕ S) (x ∷ xs)
    ≡⟨ combineCases n Q P S (x ∷ xs) ⟩
      eval (ℕ.suc n) (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) (x ∷ xs)
    ≡⟨ +Homeval (ℕ.suc n) ((P ·ₕ S) ·X+ 0ₕ) (Q ⋆ S) (x ∷ xs) ⟩
      eval (ℕ.suc n) ((P ·ₕ S) ·X+ 0ₕ) (x ∷ xs) + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)
    ≡⟨ refl ⟩
      (eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + eval n 0ₕ xs)
      + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)
    ≡⟨ cong (λ u → u + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs))
          ((eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + eval n 0ₕ xs)
         ≡⟨ cong (λ u → eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + u) (Eval0H _ xs) ⟩
           (eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + 0r)
         ≡⟨ +Rid _ ⟩
           (eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x)
         ≡⟨ cong (λ u → u · x) (·Homeval (ℕ.suc n) P S (x ∷ xs)) ⟩
           ((eval (ℕ.suc n) P (x ∷ xs) · eval (ℕ.suc n) S (x ∷ xs)) · x)
         ≡⟨ sym (·Assoc _ _ _) ⟩
           (eval (ℕ.suc n) P (x ∷ xs) · (eval (ℕ.suc n) S (x ∷ xs) · x))
         ≡⟨ cong (λ u → eval (ℕ.suc n) P (x ∷ xs) · u) (·-comm _ _) ⟩
           (eval (ℕ.suc n) P (x ∷ xs) · (x · eval (ℕ.suc n) S (x ∷ xs)))
         ≡⟨ ·Assoc _ _ _ ⟩
           (eval (ℕ.suc n) P (x ∷ xs) · x) · eval (ℕ.suc n) S (x ∷ xs)
          ∎) ⟩
      (eval (ℕ.suc n) P (x ∷ xs) · x) · eval (ℕ.suc n) S (x ∷ xs)
      + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)
    ≡⟨ cong (λ u → (eval (ℕ.suc n) P (x ∷ xs) · x) · eval (ℕ.suc n) S (x ∷ xs) + u)
            (⋆Homeval n Q S x xs) ⟩
      (eval (ℕ.suc n) P (x ∷ xs) · x) · eval (ℕ.suc n) S (x ∷ xs)
      + eval n Q xs · eval (ℕ.suc n) S (x ∷ xs)
    ≡⟨ sym (·Ldist+ _ _ _) ⟩
      ((eval (ℕ.suc n) P (x ∷ xs) · x) + eval n Q xs) · eval (ℕ.suc n) S (x ∷ xs)
    ≡⟨ refl ⟩
      eval (ℕ.suc n) (P ·X+ Q) (x ∷ xs) · eval (ℕ.suc n) S (x ∷ xs) ∎

