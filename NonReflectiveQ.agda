-- The nonreflective ring solver instantiated for the rational numbers.

{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Bool
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Nullary
open import Data.Rational.Unnormalised.Base using (ℚᵘ; 0ℚᵘ; _≃_)
open import Data.Rational.Unnormalised.Properties using (+-*-commutativeRing; _≃?_)

isZero? : ∀ (p : ℚᵘ) -> Maybe (0ℚᵘ ≃ p)
isZero? p with 0ℚᵘ ≃? p
... | .true because ofʸ p₁ = just p₁
... | .false because ofⁿ ¬p = nothing

open import Tactic.RingSolver.Core.AlmostCommutativeRing using (fromCommutativeRing)
open import Tactic.RingSolver.NonReflective (fromCommutativeRing +-*-commutativeRing isZero?) public
