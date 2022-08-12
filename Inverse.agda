-- Definitions and properties regarding multiplicative inverses.
-- Inverses require a number of results that rightfully belong in RealProperties.agda,
-- hence this new file.

{-# OPTIONS --without-K --safe #-}

module Inverse where

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


-- Helper results for defining inverses

Nₐ : (x : ℝ) -> (x≄0 : x ≄0) ->  ℕ
Nₐ x x≄0 = suc (proj₁ (fast-lemma-2-8-1-if {∣ x ∣} (x≄0⇒pos∣x∣ {x} x≄0)))

abstract
  not0-helper : ∀ (x : ℝ) -> (x≄0 : x ≄0) -> ∀ (n : ℕ) ->
                ℤ.∣ ↥ (seq x ((n ℕ.+ (Nₐ x x≄0)) ℕ.* ((Nₐ x x≄0) ℕ.* (Nₐ x x≄0)))) ∣ ≢0
  not0-helper x x≄0 n = ℚP.p≄0⇒∣↥p∣≢0 xₛ (ℚ≠-helper xₛ ([ left , right ]′ (ℚP.∣p∣≡p∨∣p∣≡-p xₛ)))
    where
      open ℚP.≤-Reasoning

      N : ℕ
      N = Nₐ x x≄0

      xₛ : ℚᵘ
      xₛ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))

      0<∣xₛ∣ : 0ℚᵘ ℚ.< ℚ.∣ xₛ ∣
      0<∣xₛ∣ = begin-strict
        0ℚᵘ     <⟨ ℚP.positive⁻¹ _ ⟩
        + 1 / N ≤⟨ proj₂ (fast-lemma-2-8-1-if {∣ x ∣} (x≄0⇒pos∣x∣ {x} x≄0)) ((n ℕ.+ N) ℕ.* (N ℕ.* N))
                 (ℕP.≤-trans (ℕP.m≤n*m N {N} ℕP.0<1+n) (ℕP.m≤n*m (N ℕ.* N) {n ℕ.+ N} (subst (0 ℕ.<_) (ℕP.+-comm N n) ℕP.0<1+n))) ⟩
        ℚ.∣ xₛ ∣  ∎

      left : ℚ.∣ xₛ ∣ ≡ xₛ -> xₛ ℚ.> 0ℚᵘ ⊎ xₛ ℚ.< 0ℚᵘ
      left hyp = inj₁ (begin-strict
        0ℚᵘ      <⟨ 0<∣xₛ∣ ⟩
        ℚ.∣ xₛ ∣ ≡⟨ hyp ⟩
        xₛ        ∎)

      right : ℚ.∣ xₛ ∣ ≡ ℚ.- xₛ -> xₛ ℚ.> 0ℚᵘ ⊎ xₛ ℚ.< 0ℚᵘ
      right hyp = inj₂ (begin-strict
        xₛ            ≈⟨ ℚP.≃-sym (ℚP.neg-involutive xₛ) ⟩
        ℚ.- (ℚ.- xₛ)  ≡⟨ cong ℚ.-_ (sym hyp) ⟩
        ℚ.- ℚ.∣ xₛ ∣  <⟨ ℚP.neg-mono-< 0<∣xₛ∣ ⟩
        0ℚᵘ            ∎)


--Had to declare separately as abstract in order to typecheck fast enough.
--TODO: see whether it could be hidden from global scope.
abstract
  lesser-helper-2 : ∀ (x : ℝ) -> (x≄0 : x ≄0) -> ∀ (n : ℕ) -> (+ 1 / (Nₐ x x≄0)) ℚ.≤ ℚ.∣ seq x ((n ℕ.+ (Nₐ x x≄0)) ℕ.* ((Nₐ x x≄0) ℕ.* (Nₐ x x≄0))) ∣
  lesser-helper-2 x x≄0 n = proj₂ (fast-lemma-2-8-1-if {∣ x ∣} (x≄0⇒pos∣x∣ {x} x≄0)) ((n ℕ.+ N) ℕ.* (N ℕ.* N)) lesser-helper
    where
    N : ℕ
    N = Nₐ x x≄0
    lesser-helper : (Nₐ x x≄0) ℕ.≤ (n ℕ.+ (Nₐ x x≄0)) ℕ.* ((Nₐ x x≄0) ℕ.* (Nₐ x x≄0))
    lesser-helper = ℕP.≤-trans (ℕP.m≤n+m N n) (ℕP.m≤m*n (n ℕ.+ N) {N ℕ.* N} ℕP.0<1+n)


abstract
  inverse-helper : ∀ (x : ℝ) -> (x≄0 : x ≄0) -> ∀ (n : ℕ) ->
                   ℚ.∣ (ℚ.1/ seq x ((n ℕ.+ (Nₐ x x≄0)) ℕ.* (Nₐ x x≄0 ℕ.* Nₐ x x≄0))) {not0-helper x x≄0 n} ∣ ℚ.≤ + (Nₐ x x≄0) / 1
  inverse-helper x x≄0 n = begin
    ℚ.∣ xₛ⁻¹ ∣                             ≈⟨ ℚP.≃-sym (ℚP.*-identityʳ ℚ.∣ xₛ⁻¹ ∣) ⟩
    ℚ.∣ xₛ⁻¹ ∣ ℚ.* 1ℚᵘ                     ≈⟨ ℚP.*-congˡ {ℚ.∣ xₛ⁻¹ ∣} (ℚP.≃-sym (ℚP.*-inverseˡ (+ N / 1))) ⟩
    ℚ.∣ xₛ⁻¹ ∣ ℚ.* (+ 1 / N ℚ.* (+ N / 1)) ≈⟨ ℚP.≃-sym (ℚP.*-assoc ℚ.∣ xₛ⁻¹ ∣ (+ 1 / N) (+ N / 1)) ⟩
    ℚ.∣ xₛ⁻¹ ∣ ℚ.* (+ 1 / N) ℚ.* (+ N / 1) ≤⟨ ℚP.*-monoˡ-≤-nonNeg {+ N / 1} _ (ℚP.*-monoʳ-≤-nonNeg {ℚ.∣ xₛ⁻¹ ∣} (ℚ.nonNegative (ℚP.0≤∣p∣ (xₛ⁻¹))) (lesser-helper-2 x x≄0 n)) ⟩
    ℚ.∣ xₛ⁻¹ ∣ ℚ.* ℚ.∣ xₛ ∣ ℚ.* (+ N / 1)  ≈⟨ ℚP.*-congʳ {+ N / 1} helper ⟩
    1ℚᵘ ℚ.* (+ N / 1)                     ≈⟨ ℚP.*-identityˡ (+ N / 1) ⟩
    + N / 1                                 ∎
    where
      open ℚP.≤-Reasoning

      N : ℕ
      N = Nₐ x x≄0

      xₛ : ℚᵘ
      xₛ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))

      xₛ≢0 : ℤ.∣ ↥ xₛ ∣ ≢0
      xₛ≢0 = not0-helper x x≄0 n
  
      
      xₛ⁻¹ : ℚᵘ
      xₛ⁻¹ = (ℚ.1/ xₛ) {xₛ≢0}
      

      helper : ℚ.∣ xₛ⁻¹ ∣ ℚ.* ℚ.∣ xₛ ∣ ℚ.≃ ℚ.1ℚᵘ
      helper = begin-equality
        ℚ.∣ xₛ⁻¹ ∣ ℚ.* ℚ.∣ xₛ ∣ ≈⟨ ℚP.≃-sym (ℚP.∣p*q∣≃∣p∣*∣q∣ xₛ⁻¹ xₛ) ⟩
        ℚ.∣ xₛ⁻¹ ℚ.* xₛ ∣       ≈⟨ ℚP.∣-∣-cong (ℚP.*-inverseˡ xₛ {xₛ≢0}) ⟩
        ℚ.1ℚᵘ                    ∎
{-
      lesser-helper : N ℕ.≤ (n ℕ.+ N) ℕ.* (N ℕ.* N)
      lesser-helper = ℕP.≤-trans (ℕP.m≤n+m N n) (ℕP.m≤m*n (n ℕ.+ N) {N ℕ.* N} ℕP.0<1+n)

      lesser-helper-2 : (+ 1 / N) ℚ.≤ ℚ.∣ xₛ ∣
      lesser-helper-2 = proj₂ (fast-lemma-2-8-1-if {∣ x ∣} (x≄0⇒pos∣x∣ {x} x≄0)) ((n ℕ.+ N) ℕ.* (N ℕ.* N)) lesser-helper
-}

-- Definition of the multiplicative inverse function _⁻¹
_⁻¹ : (x : ℝ) -> (x≄0 : x ≄ 0ℝ) -> ℝ
seq ((x ⁻¹) x≄0) n = (ℚ.1/ xₛ) {not0-helper x x≄0 n}
  where
    open ℚP.≤-Reasoning
    N = Nₐ x x≄0
    xₛ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))
reg ((x ⁻¹) x≄0) (suc k₁) (suc k₂) = begin
  ℚ.∣ yₘ ℚ.- yₙ ∣                                 ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                     (ℚP.≃-trans (ℚP.≃-sym (ℚP.*-identityʳ yₘ)) (ℚP.*-congˡ {yₘ} (ℚP.≃-sym (ℚP.*-inverseˡ xₙ {xₖ≢0 n}))))
                                                     (ℚP.-‿cong (ℚP.≃-trans (ℚP.≃-sym (ℚP.*-identityʳ yₙ)) (ℚP.*-congˡ {yₙ} (ℚP.≃-sym (ℚP.*-inverseˡ xₘ {xₖ≢0 m})))))) ⟩
  ℚ.∣ yₘ ℚ.* (yₙ ℚ.* xₙ) ℚ.- yₙ ℚ.* (yₘ ℚ.* xₘ) ∣ ≈⟨ ℚP.∣-∣-cong (solve 4 (λ xₘ xₙ yₘ yₙ ->
                                                     (yₘ ⊗ (yₙ ⊗ xₙ) ⊖ yₙ ⊗ (yₘ ⊗ xₘ)) ⊜ (yₘ ⊗ yₙ ⊗ (xₙ ⊖ xₘ)))
                                                     ℚP.≃-refl xₘ xₙ yₘ yₙ) ⟩
  ℚ.∣ yₘ ℚ.* yₙ ℚ.* (xₙ ℚ.- xₘ) ∣                 ≈⟨ ℚP.∣p*q∣≃∣p∣*∣q∣ (yₘ ℚ.* yₙ) (xₙ ℚ.- xₘ) ⟩
  ℚ.∣ yₘ ℚ.* yₙ ∣ ℚ.* ℚ.∣ xₙ ℚ.- xₘ ∣             ≤⟨ ℚP.≤-trans
                                                     (ℚP.*-monoʳ-≤-nonNeg {ℚ.∣ yₘ ℚ.* yₙ ∣} _ (reg x ((n ℕ.+ N) ℕ.* (N ℕ.* N)) ((m ℕ.+ N) ℕ.* (N ℕ.* N))))
                                                     (ℚP.*-monoˡ-≤-nonNeg {+ 1 / ((n ℕ.+ N) ℕ.* (N ℕ.* N)) ℚ.+ + 1 / ((m ℕ.+ N) ℕ.* (N ℕ.* N))} _ ∣yₘ*yₙ∣≤N²) ⟩
  (+ N / 1) ℚ.* (+ N / 1) ℚ.*
  ((+ 1 / ((n ℕ.+ N) ℕ.* (N ℕ.* N))) ℚ.+
   (+ 1 / ((m ℕ.+ N) ℕ.* (N ℕ.* N))))             ≈⟨ ℚ.*≡* (ℤsolve 3 (λ m n N ->
                                                     ((N :* N) :* ((κ (+ 1) :* ((m :+ N) :* (N :* N))) :+
                                                     (κ (+ 1) :* ((n :+ N) :* (N :* N))))) :* ((m :+ N) :* (n :+ N)) :=
                                                     (κ (+ 1) :* (n :+ N) :+ κ (+ 1) :* (m :+ N)) :* (κ (+ 1) :* κ (+ 1) :*
                                                     (((n :+ N) :* (N :* N)) :* ((m :+ N) :* (N :* N)))))
                                                     refl (+ m) (+ n) (+ N)) ⟩

  (+ 1 / (m ℕ.+ N)) ℚ.+ (+ 1 / (n ℕ.+ N))         ≤⟨ ℚP.+-mono-≤
                                                     (q≤r⇒+p/r≤+p/q 1 m (m ℕ.+ N) (ℕP.m≤m+n m N))
                                                     (q≤r⇒+p/r≤+p/q 1 n (n ℕ.+ N) (ℕP.m≤m+n n N)) ⟩
  (+ 1 / m) ℚ.+ (+ 1 / n)                          ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver
    open ℤ-Solver using ()
      renaming
        ( solve to ℤsolve
        ; _⊕_   to _:+_
        ; _⊗_   to _:*_
        ; _⊜_   to _:=_
        ; Κ     to κ
        )

    N = Nₐ x x≄0
    m = suc k₁
    n = suc k₂

    xₘ = seq x ((m ℕ.+ N) ℕ.* (N ℕ.* N))
    xₙ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))

    xₖ≢0 : ∀ (k : ℕ) -> ℤ.∣ ↥ seq x ((k ℕ.+ N) ℕ.* (N ℕ.* N)) ∣ ≢0
    xₖ≢0 k = not0-helper x x≄0 k

    yₘ = (ℚ.1/ xₘ) {xₖ≢0 m}
    yₙ = (ℚ.1/ xₙ) {xₖ≢0 n}

    ∣yₘ*yₙ∣≤N² : ℚ.∣ yₘ ℚ.* yₙ ∣ ℚ.≤ (+ N / 1) ℚ.* (+ N / 1)
    ∣yₘ*yₙ∣≤N² = begin
      ℚ.∣ yₘ ℚ.* yₙ ∣          ≈⟨ ℚP.∣p*q∣≃∣p∣*∣q∣ yₘ yₙ ⟩
      ℚ.∣ yₘ ∣ ℚ.* ℚ.∣ yₙ ∣    ≤⟨ ℚ-*-mono-≤ {ℚ.∣ yₘ ∣} {+ N / 1} {ℚ.∣ yₙ ∣} {+ N / 1} _ _
                                 (inverse-helper x x≄0 m) (inverse-helper x x≄0 n) ⟩
      (+ N / 1) ℚ.* (+ N / 1)   ∎

+p≤+q⇒1/q≤1/p : ∀ {p q} -> (posp : ℚ.Positive p) -> (posq : ℚ.Positive q) -> p ℚ.≤ q ->
                (ℚ.1/ q) {ℚP.p≄0⇒∣↥p∣≢0 q (ℚ≠-helper q (inj₁ (ℚP.positive⁻¹ posq)))} ℚ.≤ (ℚ.1/ p) {ℚP.p≄0⇒∣↥p∣≢0 p (ℚ≠-helper p (inj₁ (ℚP.positive⁻¹ posp)))}
+p≤+q⇒1/q≤1/p {mkℚᵘ (+ suc p-1) q-1} {mkℚᵘ (+ suc u-1) v-1} posp/q posu/v p/q≤u/v = let p = + suc p-1; q = + suc q-1; u = + suc u-1; v = + suc v-1 in
                                                                                    ℚ.*≤* (begin
  v ℤ.* p ≡⟨ ℤP.*-comm v p ⟩
  p ℤ.* v ≤⟨ ℚP.drop-*≤* p/q≤u/v ⟩
  u ℤ.* q ≡⟨ ℤP.*-comm u q ⟩
  q ℤ.* u  ∎)
  where open ℤP.≤-Reasoning

-- Properties of _⁻¹

*-inverseʳ : ∀ x -> (x≄0 : x ≄0) -> x * ((x ⁻¹) x≄0) ≃ 1ℝ
*-inverseʳ x x≄0 = *≃* λ {(suc k₁) ->
                     let n = suc k₁; x⁻¹ = (x ⁻¹) x≄0; k = K x ℕ.⊔ K x⁻¹
                            ; N = Nₐ x x≄0; x₂ₖₙ = seq x (2 ℕ.* k ℕ.* n)
                            ; xₛ = seq x ((2 ℕ.* k ℕ.* n ℕ.+ N) ℕ.* (N ℕ.* N))
                            ; y₂ₖₙ = (ℚ.1/ xₛ) {not0-helper x x≄0 (2 ℕ.* k ℕ.* n)} in begin
  ℚ.∣ x₂ₖₙ ℚ.* y₂ₖₙ ℚ.- 1ℚᵘ ∣                                   ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (x₂ₖₙ ℚ.* y₂ₖₙ) (ℚP.-‿cong
                                                                   (ℚP.≃-sym (ℚP.*-inverseʳ xₛ {not0-helper x x≄0 (2 ℕ.* k ℕ.* n)})))) ⟩
  ℚ.∣ x₂ₖₙ ℚ.* y₂ₖₙ ℚ.- xₛ ℚ.* y₂ₖₙ ∣                           ≈⟨ ℚP.≃-trans
                                                                   (ℚP.∣-∣-cong (solve 3 (λ x₂ₖₙ xₛ y₂ₖₙ ->
                                                                   (x₂ₖₙ ⊗ y₂ₖₙ ⊖ xₛ ⊗ y₂ₖₙ) ⊜ (y₂ₖₙ ⊗ (x₂ₖₙ ⊖ xₛ)))
                                                                   ℚP.≃-refl x₂ₖₙ xₛ y₂ₖₙ))
                                                                   (ℚP.∣p*q∣≃∣p∣*∣q∣ y₂ₖₙ (x₂ₖₙ ℚ.- xₛ))⟩
  ℚ.∣ y₂ₖₙ ∣  ℚ.* ℚ.∣ x₂ₖₙ ℚ.- xₛ ∣                             ≤⟨ ℚ-*-mono-≤ _ _
                                                                   (ℚP.≤-trans (ℚP.<⇒≤ (canonical-strict-upper-bound x⁻¹ (2 ℕ.* k ℕ.* n)))
                                                                               (p≤q⇒p/r≤q/r (+ K x⁻¹) (+ k) 1 (ℤ.+≤+ (ℕP.m≤n⊔m (K x) (K x⁻¹)))))
                                                                   (reg x (2 ℕ.* k ℕ.* n) ((2 ℕ.* k ℕ.* n ℕ.+ N) ℕ.* (N ℕ.* N))) ⟩
  + k / 1 ℚ.* (+ 1 / (2 ℕ.* k ℕ.* n) ℚ.+
  + 1 / ((2 ℕ.* k ℕ.* n ℕ.+ N) ℕ.* (N ℕ.* N)))                  ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ k / 1} _ (ℚP.+-monoʳ-≤ (+ 1 / (2 ℕ.* k ℕ.* n))
                                                                   (q≤r⇒+p/r≤+p/q 1 (2 ℕ.* k ℕ.* n) ((2 ℕ.* k ℕ.* n ℕ.+ N) ℕ.* (N ℕ.* N))
                                                                   (ℕP.≤-trans (ℕP.m≤m+n (2 ℕ.* k ℕ.* n) N) (ℕP.m≤m*n (2 ℕ.* k ℕ.* n ℕ.+ N) {N ℕ.* N} ℕP.0<1+n)))) ⟩
  + k / 1 ℚ.* (+ 1 / (2 ℕ.* k ℕ.* n) ℚ.+ + 1 / (2 ℕ.* k ℕ.* n)) ≈⟨ ℚ.*≡* (ℤsolve 2 (λ k n ->
                                                                   (k :* (κ (+ 1) :* (κ (+ 2) :* k :* n) :+ κ (+ 1) :* (κ (+ 2) :* k :* n))) :* n :=
                                                                   κ (+ 1) :* (κ (+ 1) :* (κ (+ 2) :* k :* n :* (κ (+ 2) :* k :* n))))
                                                                   refl (+ k) (+ n)) ⟩
  + 1 / n                                                       ≤⟨ p≤q⇒p/r≤q/r (+ 1) (+ 2) n (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n)) ⟩
  + 2 / n                                                                                    ∎}
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver
    open ℤ-Solver using ()
      renaming
        ( solve to ℤsolve
        ; _⊕_   to _:+_
        ; _⊗_   to _:*_
        ; _⊜_   to _:=_
        ; Κ     to κ
        )

*-inverseˡ : ∀ x -> (x≄0 : x ≄0) -> ((x ⁻¹) x≄0) * x ≃ 1ℝ
*-inverseˡ x x≄0 = let x⁻¹ = (x ⁻¹) x≄0 in begin
  x⁻¹ * x ≈⟨ *-comm x⁻¹ x ⟩
  x * x⁻¹ ≈⟨ *-inverseʳ x x≄0 ⟩
  1ℝ       ∎
  where open ≃-Reasoning

abstract
  ⁻¹-unique : ∀ t x -> (x≄0 : x ≄0) -> t * x ≃ 1ℝ -> t ≃ (x ⁻¹) x≄0
  ⁻¹-unique t x x≄0 tx=1 = let x⁻¹ = (x ⁻¹) x≄0 in begin 
    t             ≈⟨ ≃-symm (*-identityʳ t) ⟩
    t * 1ℝ        ≈⟨ *-congˡ (≃-symm (*-inverseʳ x x≄0)) ⟩
    t * (x * x⁻¹) ≈⟨ ≃-symm (*-assoc t x x⁻¹) ⟩
    (t * x) * x⁻¹ ≈⟨ *-congʳ tx=1 ⟩
    1ℝ * x⁻¹      ≈⟨ *-identityˡ x⁻¹ ⟩
    x⁻¹            ∎
    where open ≃-Reasoning

⁻¹-cong : ∀ {x y} -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) -> x ≃ y -> (x ⁻¹) x≄0 ≃ (y ⁻¹) y≄0
⁻¹-cong {x} {y} x≄0 y≄0 x≃y = ⁻¹-unique x⁻¹ y y≄0 lem 
  where
    open ≃-Reasoning
    x⁻¹ = (x ⁻¹) x≄0
    y⁻¹ = (y ⁻¹) y≄0
    lem : x⁻¹ * y ≃ 1ℝ
    lem = begin
      x⁻¹ * y ≈⟨ *-congˡ (≃-symm x≃y) ⟩
      x⁻¹ * x ≈⟨ *-inverseˡ x x≄0 ⟩
      1ℝ       ∎

posx⇒posx⁻¹ : ∀ {x} -> (x≄0 : x ≄0) -> Positive x -> Positive ((x ⁻¹) x≄0)
posx⇒posx⁻¹ {x} x≄0 posx = let fromPosx = fast-lemma-2-8-1-if posx; M = suc (proj₁ fromPosx) in
                           lemma-2-8-1-onlyif (ℕ.pred (K x ℕ.⊔ M) , λ {(suc k₁) m≥Kₓ⊔M ->
                           let m = suc k₁; N = Nₐ x x≄0; xₛ = seq x ((m ℕ.+ N) ℕ.* (N ℕ.* N)); yₘ = (ℚ.1/ xₛ) {not0-helper x x≄0 m} in begin
 + 1 / (K x ℕ.⊔ M) ≤⟨ q≤r⇒+p/r≤+p/q 1 (K x) (K x ℕ.⊔ M) (ℕP.m≤m⊔n (K x) M) ⟩
 + 1 / (K x)       ≤⟨ +p≤+q⇒1/q≤1/p {xₛ} {+ K x / 1}
                      (ℚ.positive (ℚP.<-≤-trans (ℚP.positive⁻¹ {+ 1 / M} _) (proj₂ fromPosx ((m ℕ.+ N) ℕ.* (N ℕ.* N))
                                  (ℕP.≤-trans (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (K x) M) m≥Kₓ⊔M) (ℕP.m≤m+n m N)) (ℕP.m≤m*n (m ℕ.+ N) {N ℕ.* N} ℕP.0<1+n))))) _
                      (ℚP.≤-trans (p≤∣p∣ xₛ) (ℚP.<⇒≤ (canonical-strict-upper-bound x ((m ℕ.+ N) ℕ.* (N ℕ.* N))))) ⟩
 yₘ                  ∎})
  where open ℚP.≤-Reasoning

neg-distrib-⁻¹ : ∀ {x} -> (x≄0 : x ≄0) -> - ((x ⁻¹) x≄0) ≃ ((- x) ⁻¹) (x≄0⇒-x≄0 x x≄0)
neg-distrib-⁻¹ {x} x≄0 = let x⁻¹ = (x ⁻¹) x≄0 in ⁻¹-unique (- x⁻¹) (- x) (x≄0⇒-x≄0 x x≄0) (begin
  (- x⁻¹) * (- x) ≈⟨ ≃-symm (neg-distribˡ-* x⁻¹ (- x)) ⟩
  - (x⁻¹ * (- x)) ≈⟨ -‿cong (≃-symm (neg-distribʳ-* x⁻¹ x)) ⟩
  - - (x⁻¹ * x)   ≈⟨ neg-involutive (x⁻¹ * x) ⟩
  x⁻¹ * x         ≈⟨ *-inverseˡ x x≄0 ⟩
  1ℝ               ∎)
  where open ≃-Reasoning

negx⇒negx⁻¹ : ∀ {x} -> (x≄0 : x ≄0) -> Negative x -> Negative ((x ⁻¹) x≄0)
negx⇒negx⁻¹ {x} x≄0 negx = let x⁻¹ = (x ⁻¹) x≄0; -x⁻¹ = ((- x) ⁻¹) (x≄0⇒-x≄0 x x≄0) in
                           pos-cong { -x⁻¹} { - x⁻¹} (≃-symm (neg-distrib-⁻¹ {x} x≄0)) (posx⇒posx⁻¹ { - x} (x≄0⇒-x≄0 x x≄0) negx)

x<0⇒x⁻¹<0 : ∀ {x} -> (x≄0 : x ≄0) -> x < 0ℝ -> (x ⁻¹) x≄0 < 0ℝ
x<0⇒x⁻¹<0 {x} x≄0 x<0 = let x⁻¹ = (x ⁻¹) x≄0 in
                        negx⇒x<0 {x⁻¹} (negx⇒negx⁻¹ {x} x≄0 (x<0⇒negx {x} x<0))

x<y∧posx,y⇒y⁻¹<x⁻¹ : ∀ {x y} -> x < y -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) -> Positive x -> Positive y ->
                     (y ⁻¹) y≄0 < (x ⁻¹) x≄0
x<y∧posx,y⇒y⁻¹<x⁻¹ {x} {y} x<y x≄0 y≄0 posx posy = let x⁻¹ = (x ⁻¹) x≄0; y⁻¹ = (y ⁻¹) y≄0 in
                   begin-strict
  y⁻¹             ≈⟨ ≃-symm (≃-trans (*-congʳ (*-inverseʳ x x≄0)) (*-identityˡ y⁻¹)) ⟩
  x * x⁻¹ * y⁻¹   <⟨ *-monoˡ-<-pos {y⁻¹} (posx⇒posx⁻¹ {y} y≄0 posy)
                     (*-monoˡ-<-pos {x⁻¹} (posx⇒posx⁻¹ {x} x≄0 posx) x<y) ⟩
  y * x⁻¹ * y⁻¹   ≈⟨ ≃-trans (*-congʳ (*-comm y x⁻¹)) (*-assoc x⁻¹ y y⁻¹) ⟩
  x⁻¹ * (y * y⁻¹) ≈⟨ ≃-trans (*-congˡ (*-inverseʳ y y≄0)) (*-identityʳ x⁻¹) ⟩
  x⁻¹              ∎
  where open ≤-Reasoning

⁻¹-involutive : ∀ {x} -> (x≄0 : x ≄0) -> (x⁻¹≄0 : (x ⁻¹) x≄0 ≄0) ->
                (((x ⁻¹) x≄0) ⁻¹) x⁻¹≄0 ≃ x
⁻¹-involutive {x} x≄0 x⁻¹≄0 = let x⁻¹ = (x ⁻¹) x≄0 in ≃-symm (⁻¹-unique x x⁻¹ x⁻¹≄0 (*-inverseʳ x x≄0))

0<x⇒0<x⁻¹ : ∀ {x} -> (x≄0 : x ≄0) -> 0ℝ < x -> 0ℝ < (x ⁻¹) x≄0
0<x⇒0<x⁻¹ {x} x≄0 0<x = posx⇒0<x {(x ⁻¹) x≄0} (posx⇒posx⁻¹ {x} x≄0 (0<x⇒posx 0<x))

⁻¹-involutive-default : ∀ {x} -> (x≄0 : x ≄0) ->
                (((x ⁻¹) x≄0) ⁻¹) ([ (λ x<0 -> inj₁ (x<0⇒x⁻¹<0 {x} x≄0 x<0)) , (λ 0<x -> inj₂ (0<x⇒0<x⁻¹ {x} x≄0 0<x))]′ x≄0) ≃ x
⁻¹-involutive-default {x} x≄0 = ⁻¹-involutive {x} x≄0 ([ (λ x<0 -> inj₁ (x<0⇒x⁻¹<0 {x} x≄0 x<0)) , (λ 0<x -> inj₂ (0<x⇒0<x⁻¹ {x} x≄0 0<x))]′ x≄0)

