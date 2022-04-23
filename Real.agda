-- Definition of the real numbers with arithmetic operations and ordering

{-# OPTIONS --without-K --safe #-}

module Real where

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

open ℚᵘ public

record ℝ : Set where
  constructor mkℝ
  field
    -- No n≢0 condition for seq
    seq : ℕ → ℚᵘ
    reg : (m n : ℕ) {m≢0 : m ≢0} {n≢0 : n ≢0} →
          ℚ.∣ seq m ℚ.- seq n ∣ ℚ.≤
          (+ 1 / m) {m≢0} ℚ.+ (+ 1 / n) {n≢0}

open ℝ public

infix 4 _≃_
infixl 6 _+_ _-_ _⊔_ _⊓_ _⊓₂_
infixl 7 _*_
infix 8 -_ _⋆

data _≃_ : Rel ℝ Level.zero where
  *≃* : {x y : ℝ} → ((n : ℕ) {n≢0 : n ≢0} →
        ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0}) →
        x ≃ y

-- Before defining the arithmetic operations, we will need something called
-- a canonical bound of a real number x ≡ (xₙ). The canonical bound is just the least
-- least integer than or equal to ∣x₁∣ + 2.
-- We will also need a couple of small technical results about it.

K : ℝ -> ℕ
K x = let p = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ); q = ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in suc ℤ.∣ p divℕ q ∣

private
  abstract
    Kx=1+t : ∀ x -> + K x ≡ + 1 ℤ.+ ((↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ)))
    Kx=1+t x = let t = (↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ)) in begin-equality
      + K x             ≡⟨ _≡_.refl ⟩
      + 1 ℤ.+ + ℤ.∣ t ∣ ≡⟨ cong (λ x -> + 1 ℤ.+ x) (ℤP.0≤n⇒+∣n∣≡n (0≤n⇒0≤n/ℕd (↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ)) (↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))
                                (ℚP.≥0⇒↥≥0 (ℚP.≤-trans (ℚP.0≤∣p∣ (seq x 1)) (ℚP.p≤p+q {ℚ.∣ seq x 1 ∣} {2ℚᵘ} _))))) ⟩
      + 1 ℤ.+ t          ∎
      where
        open ℤP.≤-Reasoning

abstract
  canonical-well-defined : ∀ (x : ℝ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< + K x / 1 ×
                           ∀ (n : ℤ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< n / 1 -> + K x ℤ.≤ n
  canonical-well-defined x = left , right
    where
      left : ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< + K x / 1
      left = let t = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in begin-strict
        ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ <⟨ proj₁ (proj₂ (least-ℤ>ℚ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))) ⟩
        (+ 1 ℤ.+ t) / 1       ≈⟨ ℚP.≃-reflexive (ℚP./-cong (sym (Kx=1+t x)) _≡_.refl _ _) ⟩
        + K x / 1              ∎
        where open ℚP.≤-Reasoning

      right : ∀ (n : ℤ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< n / 1 -> + K x ℤ.≤ n
      right n hyp = let t = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in begin
        + K x     ≡⟨ Kx=1+t x ⟩
        + 1 ℤ.+ t ≤⟨ proj₂ (proj₂ (least-ℤ>ℚ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))) n hyp ⟩
        n          ∎
      
        where open ℤP.≤-Reasoning

canonical-strict-upper-bound : ∀ (x : ℝ) -> ∀ (n : ℕ) -> {n ≢0} -> ℚ.∣ seq x n ∣ ℚ.< + K x / 1
canonical-strict-upper-bound x (suc k₁) = let n = suc k₁ in begin-strict
  ℚ.∣ seq x n ∣                               ≈⟨ ℚP.∣-∣-cong (solve 2 (λ xₙ x₁ ->
                                                 xₙ ⊜ (x₁ ⊕ (xₙ ⊖ x₁))) ℚP.≃-refl (seq x n) (seq x 1)) ⟩
  ℚ.∣ seq x 1 ℚ.+ (seq x n ℚ.- seq x 1)∣      ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x 1) (seq x n ℚ.- seq x 1) ⟩
  ℚ.∣ seq x 1 ∣ ℚ.+ ℚ.∣ seq x n ℚ.- seq x 1 ∣ ≤⟨ ℚP.+-monoʳ-≤ ℚ.∣ seq x 1 ∣ (reg x n 1) ⟩
  ℚ.∣ seq x 1 ∣ ℚ.+ (+ 1 / n ℚ.+ ℚ.1ℚᵘ)       ≤⟨ ℚP.+-monoʳ-≤ ℚ.∣ seq x 1 ∣ (ℚP.+-monoˡ-≤ ℚ.1ℚᵘ {+ 1 / n} {1ℚᵘ} (1/n≤1 n)) ⟩
  ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ                       <⟨ proj₁ (canonical-well-defined x) ⟩
  + K x / 1                                    ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

-- Arithmetic operations
_+_ : ℝ -> ℝ -> ℝ
seq (x + y) n = seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)
reg (x + y) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m) ℚ.-
     (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ∣    ≈⟨ ℚP.∣-∣-cong (solve 4 (λ xₘ yₘ xₙ yₙ ->
                                                   xₘ ⊕ yₘ ⊖ (xₙ ⊕ yₙ) ⊜ (xₘ ⊖ xₙ ⊕ (yₘ ⊖ yₙ)))
                                                   ℚP.≃-refl (seq x (2 ℕ.* m)) (seq y (2 ℕ.* m)) (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  ℚ.∣ seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n) ℚ.+
      (seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n)) ∣   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n)) (seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n)) ⟩
  ℚ.∣ seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n) ∣ ℚ.+
  ℚ.∣ seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n) ∣     ≤⟨ ℚP.+-mono-≤ (reg x (2 ℕ.* m) (2 ℕ.* n)) (reg y (2 ℕ.* m) (2 ℕ.* n)) ⟩
  + 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n) ℚ.+
  (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n))         ≈⟨ ℚ.*≡* (ℤsolve 2 (λ m n ->
                                                   (((κ (+ 1) :* (κ (+ 2) :* n) :+ κ (+ 1) :* (κ (+ 2) :* m))
                                                   :* ((κ (+ 2) :* m) :* (κ (+ 2) :* n))) :+
                                                   (κ (+ 1) :* (κ (+ 2) :* n) :+ κ (+ 1) :* (κ (+ 2) :* m))
                                                   :* ((κ (+ 2) :* m) :* (κ (+ 2) :* n))) :* (m :* n) :=
                                                   (κ (+ 1) :* n :+ κ (+ 1) :* m) :*
                                                   (((κ (+ 2) :* m) :* (κ (+ 2) :* n)) :*
                                                   (((κ (+ 2) :* m) :* (κ (+ 2) :* n)))))
                                                   _≡_.refl (+ m) (+ n)) ⟩
  + 1 / m ℚ.+ + 1 / n                            ∎
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
        
-_ : ℝ -> ℝ
seq (- x) n = ℚ.- seq x n
reg (- x) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ ℚ.- seq x m ℚ.- ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.≃-sym (ℚP.≃-reflexive (ℚP.neg-distrib-+ (seq x m) (ℚ.- seq x n)))) ⟩
  ℚ.∣ ℚ.- (seq x m ℚ.- seq x n) ∣   ≤⟨ ℚP.≤-respˡ-≃ (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x m ℚ.- seq x n))) (reg x m n) ⟩
  + 1 / m ℚ.+ + 1 / n                ∎
  where open ℚP.≤-Reasoning

_-_ : ℝ -> ℝ -> ℝ
x - y = x + (- y)

-- x ⊔ y is the maximum of x and y.
_⊔_ : ℝ -> ℝ -> ℝ
seq (x ⊔ y) n = (seq x n) ℚ.⊔ (seq y n)
reg (x ⊔ y) (suc k₁) (suc k₂) = [ left , right ]′ (ℚP.≤-total (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver
    m = suc k₁
    n = suc k₂

    lem : ∀ (a b c d : ℚᵘ) -> a ℚ.≤ b -> ∀ (r s : ℕ) -> {r≢0 : r ≢0} -> {s≢0 : s ≢0} ->
                               ℚ.∣ b ℚ.- d ∣ ℚ.≤ ((+ 1) / r) {r≢0} ℚ.+ ((+ 1) / s) {s≢0} ->
                               (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d) ℚ.≤ ((+ 1) / r) {r≢0} ℚ.+ ((+ 1) / s) {s≢0} 
    lem a b c d a≤b r s hyp = begin
      (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d)     ≤⟨ ℚP.+-monoʳ-≤ (a ℚ.⊔ b) (ℚP.neg-mono-≤ (ℚP.p≤q⊔p c d)) ⟩
      (a ℚ.⊔ b) ℚ.- d             ≈⟨ ℚP.+-congˡ (ℚ.- d) (ℚP.p≤q⇒p⊔q≃q a≤b) ⟩
      b ℚ.- d                     ≤⟨ p≤∣p∣ (b ℚ.- d) ⟩
      ℚ.∣ b ℚ.- d ∣               ≤⟨ hyp ⟩
      ((+ 1) / r) ℚ.+ ((+ 1) / s)  ∎

    left : seq x m ℚ.⊔ seq y m ℚ.≤ seq x n ℚ.⊔ seq y n ->
           ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
    left hyp1 = [ xn≤yn , yn≤xn ]′ (ℚP.≤-total (seq x n) (seq y n))
      where
        xn≤yn : seq x n ℚ.≤ seq y n -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        xn≤yn hyp2 = begin
          ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ ((seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n))))
                                                                  (ℚP.∣-∣-cong (solve 2 (λ a b -> (⊝ (a ⊖ b)) ⊜ (b ⊖ a))
                                                                  ℚP.≃-refl (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))) ⟩
          ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
          (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m)       ≤⟨ lem (seq x n) (seq y n) (seq x m) (seq y m) hyp2 m n
                                                                   (ℚP.≤-respʳ-≃ (ℚP.+-comm (+ 1 / n) (+ 1 / m)) (reg y n m)) ⟩
          (+ 1 / m) ℚ.+ (+ 1 / n)                                ∎ 

        yn≤xn : seq y n ℚ.≤ seq x n -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        yn≤xn hyp2 = begin
          ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ ((seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n))))
                                                                  (ℚP.∣-∣-cong (solve 2 (λ a b -> (⊝ (a ⊖ b)) ⊜ (b ⊖ a))
                                                                  ℚP.≃-refl (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))) ⟩
          ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
          (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m)       ≈⟨ ℚP.≃-trans (ℚP.+-congʳ (seq x n ℚ.⊔ seq y n)
                                                                   (ℚP.-‿cong {seq x m ℚ.⊔ seq y m} {seq y m ℚ.⊔ seq x m} (ℚP.⊔-comm (seq x m) (seq y m))))
                                                                   (ℚP.+-congˡ (ℚ.- (seq y m ℚ.⊔ seq x m)) (ℚP.⊔-comm (seq x n) (seq y n))) ⟩
          (seq y n ℚ.⊔ seq x n) ℚ.- (seq y m ℚ.⊔ seq x m) 
                                                                ≤⟨ lem (seq y n) (seq x n) (seq y m) (seq x m) hyp2 m n
                                                                   (ℚP.≤-respʳ-≃ (ℚP.+-comm (+ 1 / n) (+ 1 / m)) (reg x n m)) ⟩
          (+ 1 / m) ℚ.+ (+ 1 / n)                                ∎

    right : seq x n ℚ.⊔ seq y n ℚ.≤ seq x m ℚ.⊔ seq y m ->
            ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
    right hyp1 = [ xm≤ym , ym≤xm ]′ (ℚP.≤-total (seq x m) (seq y m))
      where
        xm≤ym : seq x m ℚ.≤ seq y m -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        xm≤ym hyp2 = ℚP.≤-respˡ-≃ (ℚP.≃-sym (ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1))) (lem (seq x m) (seq y m) (seq x n) (seq y n) hyp2 m n (reg y m n)) 

        ym≤xm : seq y m ℚ.≤ seq x m -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        ym≤xm hyp2 = begin
           ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
           (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n)       ≈⟨ ℚP.≃-trans (ℚP.+-congˡ (ℚ.- (seq x n ℚ.⊔ seq y n)) (ℚP.⊔-comm (seq x m) (seq y m)))
                                                                    (ℚP.+-congʳ (seq y m ℚ.⊔ seq x m)
                                                                    (ℚP.-‿cong {seq x n ℚ.⊔ seq y n} {seq y n ℚ.⊔ seq x n} (ℚP.⊔-comm (seq x n) (seq y n)))) ⟩
           (seq y m ℚ.⊔ seq x m) ℚ.- (seq y n ℚ.⊔ seq x n)       ≤⟨ lem (seq y m) (seq x m) (seq y n) (seq x n) hyp2 m n (reg x m n) ⟩
           (+ 1 / m) ℚ.+ (+ 1 / n)                                                      ∎

-- x ⊓ y is the minimum of x and y.
_⊓_ : ℝ -> ℝ -> ℝ
seq (x ⊓ y) n = seq x n ℚ.⊓ seq y n
reg (x ⊓ y) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂; xₘ = seq x m; yₘ = seq y m; xₙ = seq x n; yₙ = seq y n in begin
  ℚ.∣ xₘ ℚ.⊓ yₘ ℚ.- xₙ ℚ.⊓ yₙ ∣               ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                 (ℚP.⊓-cong (ℚP.≃-sym (ℚP.neg-involutive xₘ)) (ℚP.≃-sym (ℚP.neg-involutive yₘ)))
                                                 (ℚP.-‿cong (ℚP.⊓-cong (ℚP.≃-sym (ℚP.neg-involutive xₙ)) (ℚP.≃-sym (ℚP.neg-involutive yₙ))))) ⟩
  ℚ.∣ ((ℚ.- (ℚ.- xₘ)) ℚ.⊓ (ℚ.- (ℚ.- yₘ))) ℚ.-
      ((ℚ.- (ℚ.- xₙ)) ℚ.⊓ (ℚ.- (ℚ.- yₙ))) ∣   ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                 (ℚP.≃-sym (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₘ) (ℚ.- yₘ)))
                                                 (ℚP.-‿cong (ℚP.≃-sym (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₙ) (ℚ.- yₙ))))) ⟩
  ℚ.∣ ℚ.- ((ℚ.- xₘ) ℚ.⊔ (ℚ.- yₘ)) ℚ.-
     (ℚ.- ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ))) ∣          ≈⟨ ℚP.∣-∣-cong (solve 2 (λ m n -> ((⊝ m) ⊖ (⊝ n)) ⊜ (n ⊖ m)) ℚP.≃-refl ((ℚ.- xₘ) ℚ.⊔ (ℚ.- yₘ)) ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ))) ⟩
  ℚ.∣ ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ)) ℚ.-
      ((ℚ.- xₘ) ℚ.⊔ (ℚ.- yₘ)) ∣               ≤⟨ reg (- x ⊔ - y) n m ⟩
  + 1 / n ℚ.+ + 1 / m                         ≈⟨ ℚP.+-comm (+ 1 / n) (+ 1 / m) ⟩
  + 1 / m ℚ.+ + 1 / n                          ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

-- An alternative (but equivalent) definition of minimum for convenience.
_⊓₂_ : ℝ -> ℝ -> ℝ
x ⊓₂ y = - ((- x) ⊔ (- y))

_*_ : ℝ -> ℝ -> ℝ
seq (x * y) n = seq x (2 ℕ.* (K x ℕ.⊔ K y) ℕ.* n) ℚ.* seq y (2 ℕ.* (K x ℕ.⊔ K y) ℕ.* n)
reg (x * y) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂; k = K x ℕ.⊔ K y; 2km = 2 ℕ.* k ℕ.* m; 2kn = 2 ℕ.* k ℕ.* n
                                      ; x₂ₖₘ = seq x 2km; y₂ₖₘ = seq y 2km; x₂ₖₙ = seq x 2kn; y₂ₖₙ = seq y 2kn
                                      ; ∣x₂ₖₘ∣≤k = ℚP.≤-trans (ℚP.<⇒≤ (canonical-strict-upper-bound x 2km)) (p≤r⇒p/q≤r/q (+ K x) (+ k) 1 (ℤP.i≤i⊔j (+ K x) (+ K y)))
                                      ; ∣y₂ₖₙ∣≤k = ℚP.≤-trans (ℚP.<⇒≤ (canonical-strict-upper-bound y 2kn)) (p≤r⇒p/q≤r/q (+ K y) (+ k) 1 (ℤP.i≤j⊔i (+ K x) (+ K y))) in
                                      begin
  ℚ.∣ x₂ₖₘ ℚ.* y₂ₖₘ ℚ.- x₂ₖₙ ℚ.* y₂ₖₙ ∣        ≈⟨ ℚP.∣-∣-cong (solve 4 (λ xm ym xn yn ->
                                                  (xm ⊗ ym ⊖ xn ⊗ yn) ⊜
                                                  (xm ⊗ (ym ⊖ yn) ⊕ yn ⊗ (xm ⊖ xn)))
                                                  ℚP.≃-refl x₂ₖₘ y₂ₖₘ x₂ₖₙ y₂ₖₙ) ⟩
  ℚ.∣ x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ) ℚ.+
      y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ) ∣              ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ))
                                                                (y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ)) ⟩
  ℚ.∣ x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ) ∣ ℚ.+
  ℚ.∣ y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ) ∣              ≈⟨ ℚP.+-cong (ℚP.∣p*q∣≃∣p∣*∣q∣ x₂ₖₘ (y₂ₖₘ ℚ.- y₂ₖₙ)) (ℚP.∣p*q∣≃∣p∣*∣q∣ y₂ₖₙ (x₂ₖₘ ℚ.- x₂ₖₙ)) ⟩
  ℚ.∣ x₂ₖₘ ∣ ℚ.* ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣ ℚ.+
  ℚ.∣ y₂ₖₙ ∣ ℚ.* ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣           ≤⟨ ℚP.+-mono-≤
                                                  (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣} _ ∣x₂ₖₘ∣≤k)
                                                  (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣} _ ∣y₂ₖₙ∣≤k) ⟩
  (+ k / 1) ℚ.* ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣ ℚ.+
  (+ k / 1) ℚ.* ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣           ≤⟨ ℚP.+-mono-≤
                                                 (ℚP.*-monoʳ-≤-nonNeg {+ k / 1} _ (reg y 2km 2kn))
                                                 (ℚP.*-monoʳ-≤-nonNeg {+ k / 1} _ (reg x 2km 2kn)) ⟩
  (+ k / 1) ℚ.* ((+ 1 / 2km) ℚ.+
  (+ 1 / 2kn)) ℚ.+
  (+ k / 1) ℚ.* ((+ 1 / 2km) ℚ.+
  (+ 1 / 2kn))                               ≈⟨ ℚP.≃-sym (ℚP.*-distribˡ-+ (+ k / 1) ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn)) ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn))) ⟩

  (+ k / 1) ℚ.* ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn)
  ℚ.+ ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn)))         ≈⟨ ℚ.*≡* (ℤsolve 3 (λ k m n ->

  {- Function for the solver -}
  ((k :* ((((κ (+ 1) :* (κ (+ 2) :* k :* n)) :+ (κ (+ 1) :* (κ (+ 2) :* k :* m))) :* ((κ (+ 2) :* k :* m) :* (κ (+ 2) :* k :* n))) :+
  (((κ (+ 1) :* (κ (+ 2) :* k :* n)) :+ (κ (+ 1) :* (κ (+ 2) :* k :* m))) :* ((κ (+ 2) :* k :* m) :* (κ (+ 2) :* k :* n)))))
  :* (m :* n)) :=
  ((κ (+ 1) :* n :+ κ (+ 1) :* m) :*
  (κ (+ 1) :* (((κ (+ 2) :* k :* m) :* (κ (+ 2) :* k :* n)):* ((κ (+ 2) :* k :* m) :* (κ (+ 2) :* k :* n))))))
  -- Other solver inputs
  refl (+ k) (+ m) (+ n)) ⟩
  
  (+ 1 / m) ℚ.+ (+ 1 / n)                     ∎
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

-- The _⋆ function lifts a rational number into its real representation.
-- The sequence of p ⋆ is just the constant sequence (p).
_⋆ : ℚᵘ -> ℝ
seq (p ⋆) n = p
reg (p ⋆) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ p ℚ.- p ∣       ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ p) ⟩
  0ℚᵘ                 ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 1 / m ℚ.+ + 1 / n  ∎
  where
    open ℚP.≤-Reasoning

∣_∣ : ℝ -> ℝ
seq ∣ x ∣ n = ℚ.∣ seq x n ∣
reg ∣ x ∣ (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ ℚ.∣ seq x m ∣ ℚ.- ℚ.∣ seq x n ∣ ∣ ≤⟨ ∣∣p∣-∣q∣∣≤∣p-q∣ (seq x m) (seq x n) ⟩
  ℚ.∣ seq x m ℚ.- seq x n ∣            ≤⟨ reg x m n ⟩
  + 1 / m ℚ.+ + 1 / n                   ∎
  where open ℚP.≤-Reasoning

-- Identities
0ℝ : ℝ
0ℝ = 0ℚᵘ ⋆

1ℝ : ℝ
1ℝ = 1ℚᵘ ⋆

-- Exponentiation for natural powers
pow : ℝ -> ℕ -> ℝ
pow x 0 = 1ℝ
pow x (suc n) = pow x n * x

-- Maximum over a sequence
{-
Taking the max over a sequence instead of over a list for convenience.
It seems to make it easier to take the max over a list of a variable length n, since I don't
think we can write x₁ :: x₂ :: ... :: xₙ :: nil in Agda. 
For an example of this, see the convergent⇒bounded proof, particularly the part where M is defined.
-}
max : (ℕ → ℝ) → (n : ℕ) → ℝ
max f 0 = f 0
max f (suc n) = max f n ⊔ f (suc n)

-- Sign predicates
data Positive : Pred ℝ 0ℓ where
  pos* : ∀ {x} -> (∃ λ (n-1 : ℕ) -> seq x (suc n-1) ℚ.> + 1 / (suc n-1)) -> Positive x

data NonNegative : Pred ℝ 0ℓ where
  nonNeg* : ∀ {x} -> (∀ (n : ℕ) -> {n≢0 : n ≢0} -> seq x n ℚ.≥ ℚ.- ((+ 1 / n) {n≢0})) -> NonNegative x

Negative : Pred ℝ 0ℓ
Negative x = Positive (- x)

-- Ordering of ℝ
infix 4 _<_ _>_ _≤_ _≥_

_<_ : Rel ℝ 0ℓ
x < y = Positive (y - x)

_>_ : Rel ℝ 0ℓ
x > y = y < x

_≤_ : Rel ℝ 0ℓ
x ≤ y = NonNegative (y - x)

_≥_ : Rel ℝ 0ℓ
x ≥ y = y ≤ x

_≄_ : Rel ℝ 0ℓ
x ≄ y = x < y ⊎ y < x

_≄0 : ℝ -> Set
x ≄0 = x ≄ 0ℝ

_<_<_ : (x y z : ℝ) -> Set
x < y < z = (x < y) × (y < z)

_<_≤_ : (x y z : ℝ) -> Set
x < y ≤ z = (x < y) × (y ≤ z)

_≤_<_ : (x y z : ℝ) -> Set
x ≤ y < z = (x ≤ y) × (y < z)

_≤_≤_ : (x y z : ℝ) -> Set
x ≤ y ≤ z = (x ≤ y) × (y ≤ z)

_≮_ : Rel ℝ 0ℓ
x ≮ y = ¬ (x < y)

_≰_ : Rel ℝ 0ℓ
x ≰ y = ¬ (x ≤ y)

_≱_ : Rel ℝ 0ℓ
x ≱ y = y ≰ x

-- Summations
∑₀ : (ℕ -> ℝ) -> ℕ -> ℝ
∑₀ a 0 = 0ℝ
∑₀ a (suc n) = ∑₀ a n + a n

∑ : (ℕ -> ℝ) -> ℕ -> ℕ -> ℝ
∑ a 0 n = ∑₀ a n
∑ a (suc i) n = ∑₀ a n - ∑₀ a (suc i)
