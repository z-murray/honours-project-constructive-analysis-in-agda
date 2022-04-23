{-
This module is almost exactly the same as the Tactic.RingSolver.NonReflective in
the Agda Standard Library as of commit 84dcc85. The key difference is that this
version allows the user to use a coefficient ring other than the carrier ring
(given via homomorphism), while that version does not.
Without this change, the solver does not function well with real numbers since
we are forced to use the reals as the coefficient ring and the carrier ring.
Using the rationals for coefficients fixes our problems. The main change comes from
the ring solver's original documentation at
https://oisdk.github.io/agda-ring-solver/Polynomial.Solver.html,
where Raw.Carrier is used instead of Carrier.
-}

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.AlmostCommutativeRing
open import Tactic.RingSolver.Core.Polynomial.Parameters

module NonReflective
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  (homo : Homomorphism ℓ₁ ℓ₂ ℓ₃ ℓ₄)
  (let open Homomorphism homo)
  where

open import Algebra.Morphism
open import Function
open import Data.Bool.Base using (Bool; true; false; T; if_then_else_)
open import Data.Maybe.Base
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Vec hiding (_⊛_)
open import Data.Vec.N-ary

open import Tactic.RingSolver.Core.Expression
open import Algebra.Properties.Semiring.Exp.TCOptimised semiring

myMorphism : _
myMorphism = _-Raw-AlmostCommutative⟶_.⟦_⟧ morphism 

open Eval (AlmostCommutativeRing.rawRing to) myMorphism
open import Tactic.RingSolver.Core.Polynomial.Base from

norm : ∀ {n} -> Expr Raw.Carrier n -> Poly n
norm (Κ x)   = κ x
norm (Ι x)   = ι x
norm (x ⊕ y) = norm x ⊞ norm y
norm (x ⊗ y) = norm x ⊠ norm y
norm (x ⊛ i) = norm x ⊡ i
norm (⊝ x)   = ⊟ norm x

⟦_⇓⟧ : ∀ {n} → Expr Raw.Carrier n → Vec Carrier n → Carrier
⟦ expr ⇓⟧ = ⟦ norm expr ⟧ₚ where

  open import Tactic.RingSolver.Core.Polynomial.Semantics homo
    renaming (⟦_⟧ to ⟦_⟧ₚ)

correct : ∀ {n} -> (e : Expr Raw.Carrier n) -> (ρ : Vec Carrier n) -> ⟦ e ⇓⟧ ρ ≈ ⟦ e ⟧ ρ
correct {n} = go
  where
  open import Tactic.RingSolver.Core.Polynomial.Homomorphism homo

  go : ∀ (expr : Expr Raw.Carrier n) ρ → ⟦ expr ⇓⟧ ρ ≈ ⟦ expr ⟧ ρ
  go (Κ x) ρ = κ-hom x ρ
  go (Ι x) ρ = ι-hom x ρ
  go (x ⊕ y) ρ = ⊞-hom (norm x) (norm y) ρ ⟨ trans ⟩ (go x ρ ⟨ +-cong ⟩ go y ρ)
  go (x ⊗ y) ρ = ⊠-hom (norm x) (norm y) ρ ⟨ trans ⟩ (go x ρ ⟨ *-cong ⟩ go y ρ)
  go (x ⊛ i) ρ = ⊡-hom (norm x) i ρ ⟨ trans ⟩ ^-congˡ i (go x ρ)
  go (⊝ x) ρ = ⊟-hom (norm x) ρ   ⟨ trans ⟩ -‿cong (go x ρ)

open import Relation.Binary.Reflection setoid Ι ⟦_⟧ ⟦_⇓⟧ correct public
{-
We are using the ⊖ notation instead of ⊝ (notice the former has a longer line) because
of a parsing error when using the latter.
-}
infixl 6 _⊖_
_⊖_ : ∀ {n : ℕ} ->
      Expr Raw.Carrier n ->
      Expr Raw.Carrier n ->
      Expr Raw.Carrier n
x ⊖ y = x ⊕ (⊝ y)
