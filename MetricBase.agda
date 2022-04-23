-- Metric spaces definitions and results.
-- Work on this file was discontinued when I realized I would need square roots to define the
-- Cauchy-Schwarz inequality, which would, in turn, require calculus to define.

{-# OPTIONS --without-K --safe #-}

module MetricBase where

open import Algebra
open import Data.Bool.Base using (Bool; if_then_else_)
open import Function.Base using (_∘_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; +0; +[1+_]; -[1+_])
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
open import Data.List
open import Function.Structures {_} {_} {_} {_} {ℕ} _≡_ {ℕ} _≡_

{-
The solvers are used and renamed often enough to warrant them being opened up here
for the sake of consistency and cleanliness.
-}
open import NonReflectiveZ as ℤ-Solver using ()
  renaming
    ( solve to ℤsolve
    ; _⊕_   to _:+_
    ; _⊗_   to _:*_
    ; _⊖_   to _:-_
    ; ⊝_    to :-_
    ; _⊜_   to _:=_
    ; Κ     to ℤΚ
    )
open import NonReflectiveQ as ℚ-Solver using ()
  renaming
    ( solve to ℚsolve
    ; _⊕_   to _+:_
    ; _⊗_   to _*:_
    ; _⊖_   to _-:_
    ; ⊝_    to -:_
    ; _⊜_   to _=:_
    ; Κ     to ℚΚ
    )

open import ExtraProperties
open import Real
open import RealProperties
open import Inverse
open ℝ-Solver

{-
(M,ρ) is a metric space if:
(i) x = y ⇒ ρ x y = 0
(ii) ρ x y ≤ ρ x z + ρ z y
(iii) ρ x y = ρ y x
(iv) ρ x y ≥ 0 

-}
record PseudoMetricSpace (M : Set) (ρ : M → M → ℝ) (_≈_ : Rel M 0ℓ) : Set where
  constructor mkPseudo
  field
    ≈-isEquivalence     : IsEquivalence _≈_
    positivity          : {x y : M} → ρ x y ≥ 0ℝ
    nondegen-if         : {x y : M} → x ≈ y → ρ x y ≃ 0ℝ
    symmetry            : {x y : M} → ρ x y ≃ ρ y x
    triangle-inequality : {x y z : M} → ρ x y ≤ ρ x z + ρ z y

open PseudoMetricSpace public

record MetricSpace (M : Set) (ρ : M → M → ℝ) (_≈_ : Rel M 0ℓ) : Set where
  constructor mkMetric
  field
    pseudo : PseudoMetricSpace M ρ _≈_
    nondegen-onlyif : {x y : M} → ρ x y ≃ 0ℝ → x ≈ y

open MetricSpace public

productFunction : {M₁ M₂ : Set} (ρ₁ : M₁ → M₁ → ℝ) (ρ₂ : M₂ → M₂ → ℝ) →
            M₁ × M₂ → M₁ × M₂ → ℝ
productFunction ρ₁ ρ₂ x y = ρ₁ (proj₁ x) (proj₁ y) + ρ₂ (proj₂ x) (proj₂ y)

productEquality : {M₁ M₂ : Set} (_≈₁_ : Rel M₁ 0ℓ) (_≈₂ : Rel M₂ 0ℓ) →
                  Rel (M₁ × M₂) 0ℓ
productEquality _≈₁_ _≈₂_ x y = (proj₁ x ≈₁ proj₁ y) × (proj₂ x ≈₂ proj₂ y)

productPseudoMetric : {M₁ M₂ : Set} {ρ₁ : M₁ → M₁ → ℝ} {ρ₂ : M₂ → M₂ → ℝ} 
                      {_≈₁_ : Rel M₁ 0ℓ} {_≈₂_ : Rel M₂ 0ℓ}               → 
                      PseudoMetricSpace M₁ ρ₁ _≈₁_                        →
                      PseudoMetricSpace M₂ ρ₂ _≈₂_                        →
                      PseudoMetricSpace (M₁ × M₂) (productFunction ρ₁ ρ₂) (productEquality _≈₁_ _≈₂_)
productPseudoMetric {M₁} {M₂} {ρ₁} {ρ₂} {_≈₁_} {_≈₂_} spaceM₁ spaceM₂ = mkPseudo {!!} {!!} {!!} {!!} {!!}
  where
   ρ : (x y : M₁ × M₂) → ℝ
   ρ = productFunction ρ₁ ρ₂

   _≈_ : Rel (M₁ × M₂) 0ℓ
   _≈_ = productEquality _≈₁_ _≈₂_

   ≈-isEq : IsEquivalence _≈_
   ≈-isEq = {!!}
