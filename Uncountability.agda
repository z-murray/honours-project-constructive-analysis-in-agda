-- Proof that the reals are uncountable

{-# OPTIONS --without-K --safe #-}

module Uncountability where

open import Algebra
open import Data.Bool.Base using (Bool; if_then_else_)
open import Function.Base using (_∘_)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Integer.DivMod as ℤD
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕP using (≤-step)
import Data.Nat.DivMod as ℕD
open import Level using (0ℓ)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Decidable
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong; sym; subst; trans; ≢-sym)
open import Relation.Binary
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; mkℚᵘ; _≢0; _/_; 0ℚᵘ; 1ℚᵘ; ↥_; ↧_; ↧ₙ_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Algebra.Bundles
open import Algebra.Structures
open import Data.Empty
open import Data.Sum
open import Data.Maybe.Base
import NonReflectiveQ as ℚ-Solver
import NonReflectiveZ as ℤ-Solver
open import Data.List

open import ExtraProperties
open import Real
open import RealProperties

uncountability : ∀ (a : ℕ -> ℝ) -> ∀ (x₀ y₀ : ℝ) -> x₀ < y₀ ->
                 ∃ λ (x : ℝ) -> (x₀ ≤ x ≤ y₀) × (∀ (n : ℕ) -> {n≢0 : n ≢0} -> x ≄ a n)
uncountability a x₀ y₀ x₀<y₀ = x , ((≤-trans (x₀≤xₙ 1) (xₙ≤x 1)) , (≤-respˡ-≃ (≃-symm x≃y) (≤-trans (yₙ≥y 1) (yₙ≤y₀ 1)))) , x≄aₙ
  where
    generator : (n : ℕ) -> {n≢0 : n ≢0} -> (xₙ₋₁ yₙ₋₁ : ℝ) -> xₙ₋₁ < yₙ₋₁ -> x₀ ≤ xₙ₋₁ -> yₙ₋₁ ≤ y₀ ->
                ∃ λ (xₙ : ℚᵘ) -> ∃ λ (yₙ : ℚᵘ) ->
                ((x₀ ≤ xₙ₋₁ ≤ (xₙ ⋆)) × (xₙ ℚ.< yₙ) × ((yₙ ⋆) ≤ yₙ₋₁ ≤ y₀)) ×
                ((xₙ ⋆ > a n) ⊎ yₙ ⋆ < a n) ×
                yₙ ℚ.- xₙ ℚ.< (+ 1 / n) {n≢0}
    generator (suc n-1) xₙ₋₁ yₙ₋₁ xₙ₋₁<yₙ₋₁ x₀≤xₙ₋₁ yₙ₋₁≤y₀ = func (fast-corollary-2-17 (a n) xₙ₋₁ yₙ₋₁ xₙ₋₁<yₙ₋₁)
      where
        n = suc n-1
        func : a n < yₙ₋₁ ⊎ a n > xₙ₋₁ ->
               ∃ λ (xₙ : ℚᵘ) -> ∃ λ (yₙ : ℚᵘ) ->
                ((x₀ ≤ xₙ₋₁ ≤ (xₙ ⋆)) × (xₙ ℚ.< yₙ) × ((yₙ ⋆) ≤ yₙ₋₁ ≤ y₀)) ×
                ((xₙ ⋆ > a n) ⊎ yₙ ⋆ < a n) ×
                yₙ ℚ.- xₙ ℚ.< + 1 / n
        func (inj₁ aₙ<yₙ₋₁) = xₙ , yₙ , prop1 , prop2 , prop3
          where
            open ℚP.≤-Reasoning
            open ℚ-Solver
            yₙp = fast-density-of-ℚ (a n ⊔ xₙ₋₁) yₙ₋₁ (x<z∧y<z⇒x⊔y<z (a n) xₙ₋₁ yₙ₋₁ aₙ<yₙ₋₁ xₙ₋₁<yₙ₋₁)
            yₙ = proj₁ yₙp
            xₙp = fast-density-of-ℚ (a n ⊔ xₙ₋₁ ⊔ ((yₙ ℚ.- + 1 / n) ⋆)) (yₙ ⋆)
                  (x<z∧y<z⇒x⊔y<z (a n ⊔ xₙ₋₁) ((yₙ ℚ.- + 1 / n) ⋆) (yₙ ⋆) (proj₁ (proj₂ yₙp))
                  (p<q⇒p⋆<q⋆ (yₙ ℚ.- + 1 / n) yₙ (begin-strict
              yₙ ℚ.- + 1 / n <⟨ ℚP.+-monoʳ-< yₙ {ℚ.- (+ 1 / n)} {0ℚᵘ} (ℚP.negative⁻¹ _) ⟩
              yₙ ℚ.+ 0ℚᵘ     ≈⟨ ℚP.+-identityʳ yₙ ⟩
              yₙ              ∎)))
            xₙ = proj₁ xₙp

            prop1 : (x₀ ≤ xₙ₋₁ ≤ (xₙ ⋆)) × (xₙ ℚ.< yₙ) × ((yₙ ⋆) ≤ yₙ₋₁ ≤ y₀)
            prop1 = (x₀≤xₙ₋₁ , helper) , p⋆<q⋆⇒p<q xₙ yₙ (proj₂ (proj₂ xₙp)) , (<⇒≤ (proj₂ (proj₂ yₙp)) , yₙ₋₁≤y₀)
              where
                helper : xₙ₋₁ ≤ (xₙ ⋆)
                helper = ≤-trans (≤-trans (x≤y⊔x xₙ₋₁ (a n)) (x≤x⊔y (a n ⊔ xₙ₋₁) ((yₙ ℚ.- + 1 / n) ⋆)))
                                 (<⇒≤ (proj₁ (proj₂ xₙp)))

            prop2 : (xₙ ⋆ > a n) ⊎ yₙ ⋆ < a n
            prop2 = inj₁ (≤-<-trans (≤-trans (x≤x⊔y (a n) xₙ₋₁) (x≤x⊔y (a n ⊔ xₙ₋₁) ((yₙ ℚ.- + 1 / n) ⋆))) (proj₁ (proj₂ xₙp)))

            prop3 : yₙ ℚ.- xₙ ℚ.< + 1 / n
            prop3 = begin-strict
              yₙ ℚ.- xₙ                           ≈⟨ solve 3 (λ xₙ yₙ n⁻¹ ->
                                                     (yₙ ⊖ xₙ) ⊜ ((yₙ ⊖ n⁻¹) ⊕ (n⁻¹ ⊖ xₙ)))
                                                     ℚP.≃-refl xₙ yₙ (+ 1 / n) ⟩
              yₙ ℚ.- + 1 / n ℚ.+ (+ 1 / n ℚ.- xₙ) <⟨ ℚP.+-monoˡ-< (+ 1 / n ℚ.- xₙ)
                                                     (p⋆<q⋆⇒p<q (yₙ ℚ.- + 1 / n) xₙ
                                                     (≤-<-trans (x≤y⊔x ((yₙ ℚ.- + 1 / n) ⋆) (a n ⊔ xₙ₋₁)) (proj₁ (proj₂ xₙp)))) ⟩
              xₙ ℚ.+ (+ 1 / n ℚ.- xₙ)             ≈⟨ solve 2 (λ xₙ n⁻¹ -> (xₙ ⊕ (n⁻¹ ⊖ xₙ)) ⊜ n⁻¹) ℚP.≃-refl xₙ (+ 1 / n) ⟩
              + 1 / n                              ∎
        func (inj₂ aₙ>xₙ₋₁) = xₙ , yₙ , prop1 , prop2 , prop3
          where
            open ℚP.≤-Reasoning
            open ℚ-Solver
            xₙp = fast-density-of-ℚ xₙ₋₁ (a n ⊓ yₙ₋₁) (x<y∧x<z⇒x<y⊓z xₙ₋₁ (a n) yₙ₋₁ aₙ>xₙ₋₁ xₙ₋₁<yₙ₋₁)
            xₙ = proj₁ xₙp
            yₙp = fast-density-of-ℚ (xₙ ⋆) (a n ⊓ yₙ₋₁ ⊓ ((xₙ ℚ.+ + 1 / n) ⋆))
                  (x<y∧x<z⇒x<y⊓z (xₙ ⋆) (a n ⊓ yₙ₋₁) ((xₙ ℚ.+ + 1 / n) ⋆) (proj₂ (proj₂ xₙp))
                  (p<q⇒p⋆<q⋆ xₙ (xₙ ℚ.+ + 1 / n) (begin-strict
              xₙ             ≈⟨ ℚP.≃-sym (ℚP.+-identityʳ xₙ) ⟩
              xₙ ℚ.+ 0ℚᵘ     <⟨ ℚP.+-monoʳ-< xₙ {0ℚᵘ} {+ 1 / n} (ℚP.positive⁻¹ _) ⟩
              xₙ ℚ.+ + 1 / n  ∎)))
            yₙ = proj₁ yₙp

            prop1 : (x₀ ≤ xₙ₋₁ ≤ (xₙ ⋆)) × (xₙ ℚ.< yₙ) × ((yₙ ⋆) ≤ yₙ₋₁ ≤ y₀)
            prop1 = (x₀≤xₙ₋₁ , <⇒≤ (proj₁ (proj₂ xₙp))) , p⋆<q⋆⇒p<q xₙ yₙ (proj₁ (proj₂ yₙp)) , helper , yₙ₋₁≤y₀
              where
                helper : yₙ ⋆ ≤ yₙ₋₁
                helper = ≤-trans (<⇒≤ (proj₂ (proj₂ yₙp)))
                                 (≤-trans (x⊓y≤x (a n ⊓ yₙ₋₁) ((xₙ ℚ.+ + 1 / n) ⋆)) (x⊓y≤y (a n) yₙ₋₁))

            prop2 : (xₙ ⋆ > a n) ⊎ yₙ ⋆ < a n
            prop2 = inj₂ (<-≤-trans (proj₂ (proj₂ yₙp))
                         (≤-trans (x⊓y≤x (a n ⊓ yₙ₋₁) ((xₙ ℚ.+ + 1 / n) ⋆)) (x⊓y≤x (a n) yₙ₋₁)))

            prop3 : yₙ ℚ.- xₙ ℚ.< + 1 / n
            prop3 = begin-strict
              yₙ ℚ.- xₙ             <⟨ ℚP.+-monoˡ-< (ℚ.- xₙ)
                                       (p⋆<q⋆⇒p<q yₙ (xₙ ℚ.+ + 1 / n)
                                       (<-≤-trans (proj₂ (proj₂ yₙp))
                                       (x⊓y≤y (a n ⊓ yₙ₋₁) ((xₙ ℚ.+ + 1 / n) ⋆)))) ⟩
              xₙ ℚ.+ + 1 / n ℚ.- xₙ ≈⟨ solve 2 (λ xₙ n⁻¹ -> (xₙ ⊕ n⁻¹ ⊖ xₙ) ⊜ n⁻¹) ℚP.≃-refl xₙ (+ 1 / n) ⟩
              + 1 / n                ∎
            
            
    xs : ℕ -> ℚᵘ
    ys : ℕ -> ℚᵘ
    xs-increasing : ∀ (n : ℕ) -> {n ≢0} -> xs n ℚ.≤ xs (suc n)
    ys-decreasing : ∀ (n : ℕ) -> {n ≢0} -> ys (suc n) ℚ.≤ ys n
    xₙ<yₙ : ∀ (n : ℕ) -> {n ≢0} -> xs n ⋆ < ys n ⋆
    x₀≤xₙ : ∀ (n : ℕ) -> {n ≢0} -> x₀ ≤ xs n ⋆
    yₙ≤y₀ : ∀ (n : ℕ) -> {n ≢0} -> ys n ⋆ ≤ y₀

    xs 0 = 0ℚᵘ
    xs 1 = proj₁ (generator 1 x₀ y₀ x₀<y₀ ≤-refl ≤-refl)
    xs (suc (suc n-2)) = proj₁ (generator (suc (suc n-2)) (xs (suc n-2) ⋆) (ys (suc n-2) ⋆) (xₙ<yₙ (suc n-2)) (x₀≤xₙ (suc n-2)) (yₙ≤y₀ (suc n-2)))

    ys 0 = 0ℚᵘ
    ys 1 = proj₁ (proj₂ (generator 1 x₀ y₀ x₀<y₀ ≤-refl ≤-refl))
    ys (suc (suc n-2)) = proj₁ (proj₂ ((generator (suc (suc n-2)) (xs (suc n-2) ⋆) (ys (suc n-2) ⋆) (xₙ<yₙ (suc n-2)) (x₀≤xₙ (suc n-2)) (yₙ≤y₀ (suc n-2)))))

    xs-increasing 1 = p⋆≤q⋆⇒p≤q (xs 1) (xs 2)
                      (proj₂ (proj₁ (proj₁ (proj₂ (proj₂ (generator 2 (xs 1 ⋆) (ys 1 ⋆) (xₙ<yₙ 1) (x₀≤xₙ 1) (yₙ≤y₀ 1)))))))
    xs-increasing (suc (suc n-2)) = let n-1 = suc (suc n-2); n = suc n-1 in
                                    p⋆≤q⋆⇒p≤q (xs n-1) (xs n)
                                    (proj₂ (proj₁ (proj₁ (proj₂ (proj₂ (generator n (xs n-1 ⋆) (ys n-1 ⋆) (xₙ<yₙ n-1) (x₀≤xₙ n-1) (yₙ≤y₀ n-1)))))))
    
    ys-decreasing 1 = p⋆≤q⋆⇒p≤q (ys 2) (ys 1)
                      (proj₁ (proj₂ (proj₂ (proj₁ (proj₂ (proj₂ (generator 2 (xs 1 ⋆) (ys 1 ⋆) (xₙ<yₙ 1) (x₀≤xₙ 1) (yₙ≤y₀ 1))))))))
    ys-decreasing (suc (suc n-2)) = let n-1 = suc (suc n-2); n = suc n-1 in
                                    p⋆≤q⋆⇒p≤q (ys n) (ys n-1)
                                    (proj₁ (proj₂ (proj₂ (proj₁ (proj₂ (proj₂ (generator n (xs n-1 ⋆) (ys n-1 ⋆) (xₙ<yₙ n-1) (x₀≤xₙ n-1) (yₙ≤y₀ n-1))))))))

    xₙ<yₙ 1 = p<q⇒p⋆<q⋆ (xs 1) (ys 1) (proj₁ (proj₂ (proj₁ (proj₂ (proj₂ (generator 1 x₀ y₀ x₀<y₀ ≤-refl ≤-refl))))))
    xₙ<yₙ (suc (suc n-2)) = let n-1 = suc n-2; n = suc n-1 in
                            p<q⇒p⋆<q⋆ (xs n) (ys n) (proj₁ (proj₂ (proj₁ (proj₂ (proj₂ (generator n (xs n-1 ⋆) (ys n-1 ⋆) (xₙ<yₙ n-1) (x₀≤xₙ n-1) (yₙ≤y₀ n-1)))))))

    x₀≤xₙ 1 = proj₂ (proj₁ (proj₁ (proj₂ (proj₂ (generator 1 x₀ y₀ x₀<y₀ ≤-refl ≤-refl)))))
    x₀≤xₙ (suc (suc n-2)) = let n-1 = suc n-2; n = suc n-1; get = generator n (xs n-1 ⋆) (ys n-1 ⋆) (xₙ<yₙ n-1) (x₀≤xₙ n-1) (yₙ≤y₀ n-1) in
                            ≤-trans {x₀} {xs n-1 ⋆} {xs n ⋆} (x₀≤xₙ n-1) (proj₂ (proj₁ (proj₁ (proj₂ (proj₂ get)))))
    
    yₙ≤y₀ 1 = proj₁ (proj₂ (proj₂ (proj₁ (proj₂ (proj₂ (generator 1 x₀ y₀ x₀<y₀ ≤-refl ≤-refl))))))
    yₙ≤y₀ (suc (suc n-2)) = let n-1 = suc n-2; n = suc n-1; get = generator n (xs n-1 ⋆) (ys n-1 ⋆) (xₙ<yₙ n-1) (x₀≤xₙ n-1) (yₙ≤y₀ n-1) in
                            ≤-trans {ys n ⋆} {ys n-1 ⋆} {y₀} (proj₁ (proj₂ (proj₂ (proj₁ (proj₂ (proj₂ get)))))) (yₙ≤y₀ n-1)

    n≤m⇒xₙ≤xₘ : ∀ (m n : ℕ) -> {n ≢0} -> n ℕ.≤ m -> xs n ⋆ ≤ xs m ⋆
    n≤m⇒xₙ≤xₘ (suc m-1) (suc n-1) n≤m = let m = suc m-1; n = suc n-1 in
                                        [ (λ {refl -> ≤-refl}) ,
                                        (λ {n<m -> ≤-trans (n≤m⇒xₙ≤xₘ m-1 n (m<1+n⇒m≤n n m-1 n<m))
                                                           (p≤q⇒p⋆≤q⋆ (xs m-1) (xs m) (xs-increasing m-1
                                                                      {0<n⇒n≢0 m-1 (ℕP.<-transˡ ℕP.0<1+n (m<1+n⇒m≤n n m-1 n<m))}))}) ]′
                                        (≤⇒≡∨< n m n≤m)

    n≤m⇒yₘ≤yₙ : ∀ (m n : ℕ) -> {n ≢0} -> n ℕ.≤ m -> ys m ⋆ ≤ ys n ⋆
    n≤m⇒yₘ≤yₙ (suc m-1) (suc n-1) n≤m = let m = suc m-1; n = suc n-1 in
                                        [ (λ {refl -> ≤-refl}) ,
                                        (λ {n<m -> ≤-trans (p≤q⇒p⋆≤q⋆ (ys m) (ys m-1) (ys-decreasing m-1
                                                                      {0<n⇒n≢0 m-1 (ℕP.<-transˡ ℕP.0<1+n (m<1+n⇒m≤n n m-1 n<m))}))
                                                           (n≤m⇒yₘ≤yₙ m-1 n (m<1+n⇒m≤n n m-1 n<m))}) ]′
                                        (≤⇒≡∨< n m n≤m)

    xₙ>aₙ∨yₙ<aₙ : ∀ (n : ℕ) -> {n ≢0} -> xs n ⋆ > a n ⊎ ys n ⋆ < a n
    xₙ>aₙ∨yₙ<aₙ 1 = proj₁ (proj₂ (proj₂ (proj₂ (generator 1 x₀ y₀ x₀<y₀ ≤-refl ≤-refl))))
    xₙ>aₙ∨yₙ<aₙ (suc (suc n-2)) = let n-1 = suc n-2; n = suc n-1 in
                                  proj₁ (proj₂ (proj₂ (proj₂ (generator n (xs n-1 ⋆) (ys n-1 ⋆) (xₙ<yₙ n-1) (x₀≤xₙ n-1) (yₙ≤y₀ n-1)))))

    yₙ-xₙ<n⁻¹ : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ys n ℚ.- xs n ℚ.< (+ 1 / n) {n≢0}
    yₙ-xₙ<n⁻¹ 1 = proj₂ (proj₂ (proj₂ (proj₂ (generator 1 x₀ y₀ x₀<y₀ ≤-refl ≤-refl))))
    yₙ-xₙ<n⁻¹ (suc (suc n-2)) = let n-1 = suc n-2; n = suc n-1 in
                                proj₂ (proj₂ (proj₂ (proj₂ (generator n (xs n-1 ⋆) (ys n-1 ⋆) (xₙ<yₙ n-1) (x₀≤xₙ n-1) (yₙ≤y₀ n-1)))))

    x : ℝ
    seq x = xs
    reg x = regular-n≤m xs (λ {(suc m-1) (suc n-1) m≥n → let m = suc m-1; n = suc n-1 in begin
      ℚ.∣ xs m ℚ.- xs n ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p (p⋆≤q⋆⇒p≤q (xs n) (xs m) (n≤m⇒xₙ≤xₘ m n m≥n))) ⟩
      xs m ℚ.- xs n       <⟨ ℚP.+-monoˡ-< (ℚ.- xs n) (p⋆<q⋆⇒p<q (xs m) (ys n)
                             (<-≤-trans (xₙ<yₙ m) (n≤m⇒yₘ≤yₙ m n m≥n))) ⟩
      ys n ℚ.- xs n       <⟨ yₙ-xₙ<n⁻¹ n ⟩
      + 1 / n             ≈⟨ ℚP.≃-sym (ℚP.+-identityˡ (+ 1 / n)) ⟩
      0ℚᵘ ℚ.+ + 1 / n     <⟨ ℚP.+-monoˡ-< (+ 1 / n) {0ℚᵘ} {+ 1 / m} (ℚP.positive⁻¹ _) ⟩
      + 1 / m ℚ.+ + 1 / n  ∎})
      where open ℚP.≤-Reasoning

    y : ℝ
    seq y = ys
    reg y = regular-n≤m ys (λ {(suc m-1) (suc n-1) m≥n -> let m = suc m-1; n = suc n-1 in begin
      ℚ.∣ ys m ℚ.- ys n ∣ ≈⟨ ∣p-q∣≃∣q-p∣ (ys m) (ys n) ⟩
      ℚ.∣ ys n ℚ.- ys m ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p (p⋆≤q⋆⇒p≤q (ys m) (ys n) (n≤m⇒yₘ≤yₙ m n m≥n))) ⟩
      ys n ℚ.- ys m       <⟨ ℚP.+-monoʳ-< (ys n) (ℚP.neg-mono-< (p⋆<q⋆⇒p<q (xs n) (ys m)
                             (≤-<-trans (n≤m⇒xₙ≤xₘ m n m≥n) (xₙ<yₙ m)))) ⟩
      ys n ℚ.- xs n       <⟨ yₙ-xₙ<n⁻¹ n ⟩
      + 1 / n             ≈⟨ ℚP.≃-sym (ℚP.+-identityˡ (+ 1 / n)) ⟩
      0ℚᵘ ℚ.+ + 1 / n     <⟨ ℚP.+-monoˡ-< (+ 1 / n) {0ℚᵘ} {+ 1 / m} (ℚP.positive⁻¹ _) ⟩
      + 1 / m ℚ.+ + 1 / n  ∎})
      where open ℚP.≤-Reasoning

    x≃y : x ≃ y
    x≃y = *≃* (λ {(suc n-1) -> let n = suc n-1 in begin
      ℚ.∣ xs n ℚ.- ys n ∣ ≈⟨ ∣p-q∣≃∣q-p∣ (xs n) (ys n) ⟩
      ℚ.∣ ys n ℚ.- xs n ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.<⇒≤ (p<q⇒0<q-p (xs n) (ys n)
                             (p⋆<q⋆⇒p<q (xs n) (ys n) (xₙ<yₙ n)))) ⟩
      ys n ℚ.- xs n       <⟨ yₙ-xₙ<n⁻¹ n ⟩
      + 1 / n             ≤⟨ ℚ.*≤* (ℤP.*-monoʳ-≤-nonNeg n {+ 1} {+ 2} (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n))) ⟩
      + 2 / n              ∎})
      where open ℚP.≤-Reasoning

    xₙ≤x : ∀ (n : ℕ) -> {n ≢0} -> xs n ⋆ ≤ x
    xₙ≤x (suc n-1) = let n = suc n-1 in
                     lemma-2-8-2-onlyif (λ {(suc k-1) -> n , _ , λ {(suc m-1) m≥n -> let k = suc k-1; m = suc m-1 in
                     begin
     ℚ.- (+ 1 / k)         <⟨ ℚP.negative⁻¹ _ ⟩
     0ℚᵘ                   ≤⟨ ℚP.p≤q⇒0≤q-p (p⋆≤q⋆⇒p≤q (xs n) (xs (2 ℕ.* m))
                              (n≤m⇒xₙ≤xₘ (2 ℕ.* m) n (ℕP.≤-trans m≥n (ℕP.m≤n*m m {2} ℕP.0<1+n)))) ⟩
     xs (2 ℕ.* m) ℚ.- xs n  ∎}})
      where open ℚP.≤-Reasoning

    yₙ≥y : ∀ (n : ℕ) -> {n ≢0} -> ys n ⋆ ≥ y
    yₙ≥y (suc n-1) = let n = suc n-1 in
                     lemma-2-8-2-onlyif (λ {(suc k-1) -> n , _ , λ {(suc m-1) m≥n -> let k = suc k-1; m = suc m-1 in
                     begin
      ℚ.- (+ 1 / k)         <⟨ ℚP.negative⁻¹ _ ⟩
      0ℚᵘ                   ≤⟨ ℚP.p≤q⇒0≤q-p (p⋆≤q⋆⇒p≤q (ys (2 ℕ.* m)) (ys n)
                               (n≤m⇒yₘ≤yₙ (2 ℕ.* m) n (ℕP.≤-trans m≥n (ℕP.m≤n*m m {2} ℕP.0<1+n)))) ⟩
      ys n ℚ.- ys (2 ℕ.* m)  ∎}})
      where open ℚP.≤-Reasoning

    x≄aₙ : ∀ (n : ℕ) -> {n ≢0} -> x ≄ (a n)
    x≄aₙ (suc n-1) = let n = suc n-1 in
                     [ (λ xₙ>aₙ -> inj₂ (<-≤-trans xₙ>aₙ (xₙ≤x n))) ,
                     (λ yₙ<aₙ -> inj₁ (<-respˡ-≃ (≃-symm x≃y) (≤-<-trans (yₙ≥y n) yₙ<aₙ))) ]′
                     (xₙ>aₙ∨yₙ<aₙ n)
