{-# OPTIONS --without-K #-}

-- A module for testing what does run successfully and what does not.

module Test where

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

postulate cheat : ∀ {i}{A : Set i} → A

strange1 : ℝ
seq strange1 zero = 0ℚᵘ
seq strange1 (suc n) = 1ℚᵘ ℚ.+ (+ 1 / (suc n))
reg strange1 (suc m) (suc n) = cheat

strange1≄0 : strange1 ≄ 0ℝ
strange1≄0 = inj₂ (pos* (0 , ℚ.*<* (ℤ.+<+ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))))))

strange1≃1 : strange1 ≃ 1ℝ
strange1≃1 = *≃* λ {(suc n) → cheat}

-- must evaluate with C-u C-c C-n! (ignore abstract)
testInverseOnStrange1 : ℕ
testInverseOnStrange1 = ↧ₙ (seq (_⁻¹ strange1 strange1≄0) 100)
-- successfully evaluates with C-u C-c C-n; returns 1665

testEuler : ℕ
testEuler = ↧ₙ (seq e 100)
-- runs out of memory
