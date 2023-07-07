-- Here, Σ ℕ (λ k → k ℕ.≤ n) is used instead of Fin as an index type.
-- It's uglier but much easier to handle.

{-# OPTIONS --without-K --safe #-}
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
open import Relation.Unary
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
open import Agda.Builtin.Unit
open import Level using (Level)

open import ExtraProperties
open import Real
open import RealProperties

module FiniteSequences.SigmaIndices where

SigInd : ℕ → Set
SigInd n = Σ ℕ (λ k → k ℕ.≤ n)

-- A maximum for finite sequences given by sigma indices.
-- For easier proofs, f₀ is ⊔-ed to the rest.
maxΣ : {n-1 : ℕ} → (SigInd n-1 → ℝ) → ℝ
maxΣ {zero} f = f (0 , ℕ.z≤n)
maxΣ {suc n-2} f = f (0 , ℕ.z≤n) ⊔ maxΣ {n-2} λ (k , k≤n-2) → f (suc k , ℕ.s≤s k≤n-2)

m≤n-1⇒fm≤maxΣf : {n-1 : ℕ} → (f : SigInd n-1 → ℝ) →
         (m : Σ ℕ (λ m → m ℕ.≤ n-1)) → f m ≤ maxΣ f
m≤n-1⇒fm≤maxΣf {zero} f (.zero , ℕ.z≤n) = ≤-refl
m≤n-1⇒fm≤maxΣf {suc n-2} f (zero , ℕ.z≤n) = x≤x⊔y (f (zero , ℕ.z≤n)) (maxΣ {n-2} λ (k , k≤n-2) → f (suc k , ℕ.s≤s k≤n-2))
m≤n-1⇒fm≤maxΣf {suc n-2} f (suc m-1 , ℕ.s≤s m-1≤n-2) = let ftail = λ (k , k≤n-2) → f (suc k , ℕ.s≤s k≤n-2) in
                                           ≤-trans (m≤n-1⇒fm≤maxΣf {n-2} ftail (m-1 , m-1≤n-2)) (x≤y⊔x ((maxΣ {n-2} ftail)) (f (zero , ℕ.z≤n)))

-- A version of maxSelect for sigma indices.
maxΣSelect : ∀ {n-1 : ℕ} (f : (SigInd n-1 → ℝ)) (ε : ℝ) → ε > 0ℝ → ∃ (λ i → maxΣ f - ε < f i)
maxΣSelect {zero}    f ε ε>0 = (zero , ℕ.z≤n) , 0<ε⇒x-ε<x {ε} (f (0 , ℕ.z≤n)) ε>0
maxΣSelect {suc n-1} f ε ε>0 = [ case₁ , case₂ ]′ eitheror
  where
  n : ℕ
  n = suc n-1
  prevf : SigInd n-1 → ℝ
  prevf = λ (k , k≤n-1) → f (suc k , ℕ.s≤s k≤n-1)
  v : ℝ
  v = maxΣ prevf
  prevproof : ∃ (λ i-1 → v - ε < prevf i-1)       --the index from the induction hypothesis
  prevproof = maxΣSelect prevf ε ε>0

  i : ℕ
  i = suc (proj₁ (proj₁ prevproof))
  iΣ : SigInd n
  iΣ = i , ℕ.s≤s (proj₂ (proj₁ prevproof))

  -- Agda deduces this by itself
  -- fiΣ≃prevf[i-1Σ] : f iΣ ≃ prevf (proj₁ prevproof)
  -- fiΣ≃prevf[i-1Σ] = ≃-refl

  --here we have to take the first element separately, not the last one
  0Σ : SigInd n
  0Σ = 0 , ℕ.z≤n

  eitheror : f 0Σ - f iΣ < ε ⊎ f 0Σ - f iΣ > 0ℝ
  eitheror = fast-corollary-2-17 (f 0Σ - f iΣ) 0ℝ ε ε>0

  case₁ : f 0Σ - f iΣ < ε →
      ∃ (λ i₁ → f 0Σ ⊔ v - ε < f i₁)
  case₁ hyp = iΣ , (begin-strict
         f 0Σ ⊔ v - ε            <⟨ +-monoˡ-< (- ε) (x<z∧y<z⇒x⊔y<z (f 0Σ) v (f iΣ + ε) ((a-b<c⇒a<b+c hyp)) ((a-b<c⇒a<c+b (proj₂ prevproof)))) ⟩
         f iΣ + ε - ε            ≈⟨ solve 2 (λ a b → a ⊕ b ⊖ b ⊜ a) ≃-refl (f iΣ) ε ⟩
         f iΣ                    ∎ )
    where
      open ≤-Reasoning
      open ℝ-Solver

  case₂ : f 0Σ - f iΣ > 0ℝ →
      ∃ (λ i₁ → f 0Σ ⊔ v - ε < f i₁)
  case₂ hyp = 0Σ , (begin-strict
         f 0Σ ⊔ v - ε      <⟨ +-monoˡ-< (- ε) (x<z∧y<z⇒x⊔y<z (f 0Σ) v (f 0Σ + ε) ((0<ε⇒x<x+ε (f 0Σ) ε>0)) lem) ⟩
         f 0Σ + ε - ε      ≈⟨ solve 2 (λ a b → a ⊕ b ⊖ b ⊜ a) ≃-refl (f 0Σ) ε ⟩
         f 0Σ              ∎)
    where
      open ≤-Reasoning
      open ℝ-Solver
      lem : v < f 0Σ + ε
      lem = begin-strict
          v              <⟨ a-b<c⇒a<c+b (proj₂ prevproof) ⟩
          f iΣ + ε        <⟨ +-monoˡ-< ε (0<y-x⇒x<y (f iΣ) (f 0Σ) hyp) ⟩
          f 0Σ + ε  ∎
