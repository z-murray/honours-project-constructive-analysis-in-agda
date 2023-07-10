{-# OPTIONS --without-K #-}

-- A module for testing what does run successfully and what does not.

module Test where

open import Agda.Builtin.Unit
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
open import Inverse
open import Sequence
-- open import FastPow

-- A function which creates a real number equal to p⋆, but with a more complex definition than the original one.
-- Needed because when using _⋆, Agda can sometimes simplify calculations and things can terminate that otherwise cannot.
strangify : ℚᵘ → ℝ
seq (strangify _) zero = 0ℚᵘ
seq (strangify p) (suc n) = p ℚ.+ (+ 1 / (suc n))
reg (strangify p) (suc m) (suc n) = begin
           ℚ.∣ p ℚ.+ (+ 1 / (suc m)) ℚ.- (p ℚ.+ (+ 1 / (suc n))) ∣    ≈⟨ ℚP.∣-∣-cong (solve 3 (λ p q r → p ⊕ q ⊖ (p ⊕ r) ⊜ (q ⊖ r)) ℚP.≃-refl p (+ 1 / (suc m)) (+ 1 / (suc n))) ⟩
           ℚ.∣ (+ 1 / (suc m)) ℚ.- (+ 1 / (suc n)) ∣                   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (+ 1 / (suc m)) (ℚ.- (+ 1 / (suc n))) ⟩
           ℚ.∣ (+ 1 / (suc m)) ∣ ℚ.+ ℚ.∣ (+ 1 / (suc n)) ∣              ≈⟨ ℚP.+-cong {ℚ.∣ (+ 1 / (suc m)) ∣} {+ 1 / (suc m)} {ℚ.∣ (+ 1 / (suc n)) ∣} {+ 1 / (suc n)}
                                                                         (ℚP.0≤p⇒∣p∣≃p (ℚ.*≤* (ℤ.+≤+ ℕ.z≤n))) ((ℚP.0≤p⇒∣p∣≃p (ℚ.*≤* (ℤ.+≤+ ℕ.z≤n)))) ⟩
           (+ 1 / (suc m)) ℚ.+ (+ 1 / (suc n))                        ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

strangifyp≃p : ∀ (p : ℚᵘ) → strangify p ≃ p ⋆
strangifyp≃p p = *≃* λ {(suc n) → begin
             ℚ.∣ p ℚ.+ (+ 1 / (suc n)) ℚ.- p ∣    ≈⟨ ℚP.∣-∣-cong (solve 2 (λ a b → a ⊕ b ⊖ a ⊜ b) ℚP.≃-refl p (+ 1 / (suc n))) ⟩
             ℚ.∣ (+ 1 / (suc n)) ∣                                            ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚ.*≤* (ℤ.+≤+ ℕ.z≤n)) ⟩
                 (+ 1 / (suc n))                                             ≤⟨ ℚ.*≤* (ℤ.+≤+ (ℕ.s≤s (ℕP.+-monoʳ-≤ n ℕ.z≤n))) ⟩
                 (+ 2 / (suc n))                                             ∎}
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

strange1 : ℝ
strange1 = strangify 1ℚᵘ

pos-strange1 : Positive strange1
pos-strange1 = pos* (1 , ℚ.*<* (ℤ.+<+ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))))

strange1≄0 : strange1 ≄ 0ℝ
strange1≄0 = inj₂ (posx⇒0<x pos-strange1)

-- must evaluate with C-u C-c C-n! (ignore abstract)
test-inverse-on-strange1 : ℕ
test-inverse-on-strange1 = ↧ₙ (seq (_⁻¹ strange1 strange1≄0) 100)
-- successfully evaluates with C-u C-c C-n; returns 1665

test-e : ℕ
test-e = ↧ₙ (seq e 100)
-- gets stuck

archimedean-ℝ₃-on-strange1 : ℕ
archimedean-ℝ₃-on-strange1 = proj₁ (archimedean-ℝ₃ {strange1} strange1 pos-strange1)
-- successfully evaluates with C-u C-c C-n; returns 4

test-geometric-series-isConvergent : ℕ
test-geometric-series-isConvergent = ↧ₙ (seq (proj₁ (geometric-series-isConvergent {strangify (+ 1 / 2)} lem)) 100)
  where
    open ≤-Reasoning
    lem : ∣ strangify (+ 1 / 2) ∣ < 1ℝ
    lem = begin-strict
             ∣ strangify (+ 1 / 2) ∣     ≈⟨ ∣-∣-cong (strangifyp≃p (+ 1 / 2)) ⟩
             ∣ (+ 1 / 2)⋆ ∣                 ≈⟨ 0≤x⇒∣x∣≃x {(+ 1 / 2)⋆} (p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 / 2) (ℚ.*≤* (ℤ.+≤+ ℕ.z≤n))) ⟩
              (+ 1 / 2)⋆                   <⟨ p<q⇒p⋆<q⋆ (+ 1 / 2) 1ℚᵘ (ℚ.*<* (ℤ.+<+ (ℕ.s≤s ℕP.≤-refl))) ⟩
              1ℝ                          ∎
-- successfully evaluates with C-u C-c C-n; returns 7630

test-proposition-3-6-1 : ℕ
test-proposition-3-6-1 = ↧ₙ (seq (proj₁ (proposition-3-6-1 {series} {(+ 1 / 2)⋆} (p<q⇒p⋆<q⋆ 0ℚᵘ (+ 1 / 2) (ℚ.*<* (ℤ.+<+ ℕP.≤-refl)) ,
                                                                                 p<q⇒p⋆<q⋆ (+ 1 / 2) 1ℚᵘ (ℚ.*<* (ℤ.+<+ ℕP.≤-refl)))
                                                                                 (0 , λ n _ → begin
                                                                                          ∣ mkℚᵘ (+ 1) 2 ⋆ * series n ∣  ≈⟨ ∣x*y∣≃∣x∣*∣y∣ ((+ 1 / 3)⋆) (series n) ⟩
                                                                                        ∣  mkℚᵘ (+ 1) 2 ⋆ ∣ * ∣ series n ∣ ≈⟨ *-congʳ {∣ series n ∣} (0≤x⇒∣x∣≃x (p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 / 3) (ℚ.*≤* (ℤ.+≤+ ℕ.z≤n)))) ⟩
                                                                                          mkℚᵘ (+ 1) 2 ⋆ * ∣ series n ∣  ≤⟨ *-mono-≤ {(+ 1 / 3)⋆} {(+ 1 / 2)⋆} {∣ series n ∣} {∣ series n ∣}
                                                                                                                                   (nonNegp⇒nonNegp⋆ (+ 1 / 3) tt) (nonNeg∣x∣ (series n))
                                                                                                                                   (p≤q⇒p⋆≤q⋆ (+ 1 / 3) (+ 1 / 2) (ℚ.*≤* (ℤ.+≤+ (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))))) ≤-refl ⟩
                                                                                          mkℚᵘ (+ 1) 1 ⋆ * ∣ series n ∣  ∎))) 100)
  where
  open ≤-Reasoning
  series : ℕ → ℝ
  series zero = 1ℝ
  series (suc n) = (+ 1 / 3)⋆ * series n
-- gets stuck

pow-test : ℕ
pow-test = ↧ₙ (seq (pow (strangify (+ 1 / 2)) 10) 100)
-- gets stuck

-- fast-pow-test : ℕ
-- fast-pow-test = ↧ₙ (seq (fast-pow (strangify (+ 1 / 2)) 10) 100)
