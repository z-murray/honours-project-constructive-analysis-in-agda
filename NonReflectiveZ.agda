-- The nonreflective ring solver instantiated for integers.
-- (could not find on the repository)

{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Nullary
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
open import Data.Integer.Properties as ℤP
open import Relation.Binary.Definitions

isZero? : ∀ (p : ℤ) -> Maybe (ℤ.0ℤ ≡ p)
isZero? p with ℤ.0ℤ ℤP.≟ p
... | .true because ofʸ p₁ = just p₁
... | .false because ofⁿ ¬p = nothing

open import Tactic.RingSolver.Core.AlmostCommutativeRing using (fromCommutativeRing)
open import Tactic.RingSolver.NonReflective (fromCommutativeRing +-*-commutativeRing isZero?) public

import Tactic.RingSolver.NonReflective
import Data.Nat.Base as ℕ
_⊖_ : {A : Set} → {n : ℕ.ℕ} → Tactic.RingSolver.NonReflective.Expr A n → Tactic.RingSolver.NonReflective.Expr A n → Tactic.RingSolver.NonReflective.Expr A n
ex1 ⊖ ex2 = ex1 ⊕ (⊝ ex2)
infixl 6 _⊖_

