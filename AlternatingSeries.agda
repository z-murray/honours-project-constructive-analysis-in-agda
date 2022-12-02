-- Proof of the alternating series test

{-# OPTIONS --without-K --safe #-}

module AlternatingSeries where

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

open import ExtraProperties
open import Real
open import RealProperties
open import Sequence

open ℝ-Solver

private
  {-
  Let n∈ℕ and suppose, towards contradiction, that xₙ < 0. Then ∣xₙ∣ > 0.
  Since (xₙ)→0, there is N ≥ n such that ∣xₘ∣ < ∣xₙ∣ for m ≥ N ≥ n.
  As (xₙ) is decreasing and m ≥ n, we have xₘ ≤ xₙ < 0. Thus ∣xₙ∣ ≤ ∣xₘ∣,
  contradicting ∣xₘ∣ < ∣xₙ∣. Hence 0 ≤ xₙ.
  -}
    xₙ≥0 : {xs : ℕ → ℝ} → xs isDecreasing → xs ConvergesTo 0ℝ → (n : ℕ) → xs n ≥ 0ℝ
    xₙ≥0 {xs} dec xₙ→0 n = ≮⇒≥ (λ xₙ<0 → let get = fast-ε-from-convergence (0ℝ , xₙ→0) ∣ xs n ∣ (0<x⇒posx (x<0⇒0<∣x∣ xₙ<0)); N = suc (proj₁ get); M = N ℕ.⊔ n; dec₂ = fast-isDecreasing⇒isDecreasing₂ dec in
                           <-irrefl ≃-refl (begin-strict
      ∣ xs n ∣      ≤⟨ x≤y≤0⇒∣y∣≤∣x∣ {xs M} {xs n} (dec₂ M n (ℕP.m≤n⊔m N n) , <⇒≤ xₙ<0) ⟩
      ∣ xs M ∣      ≈⟨ ∣-∣-cong (solve 1 (λ x → x ⊜ x ⊖ Κ 0ℚᵘ) ≃-refl (xs M)) ⟩
      ∣ xs M - 0ℝ ∣ <⟨ proj₂ get M (ℕP.m≤m⊔n N n) ⟩
      ∣ xs n ∣       ∎))
      where
        open ≤-Reasoning

    alt : (ℕ → ℝ) → (ℕ → ℝ)
    alt xs k = pow (- 1ℝ) k * xs k

    partial≥0 : {xs : ℕ → ℝ} → xs isDecreasing → xs ConvergesTo 0ℝ →
                   (n : ℕ) → ∑₀ (alt xs) n ≥ 0ℝ
    partial≥0 {xs} dec xₙ→0            zero       = ≤-refl
    partial≥0 {xs} dec xₙ→0       (suc zero)      = let [-1]ᵏxₖ = alt xs in begin
              0ℝ            ≤⟨ xₙ≥0 {xs} dec xₙ→0 0 ⟩
              xs 0          ≈⟨ ≃-symm (*-identityˡ (xs 0)) ⟩
              [-1]ᵏxₖ 0     ≈⟨ ≃-symm (+-identityˡ ([-1]ᵏxₖ 0)) ⟩
         0ℝ + [-1]ᵏxₖ 0      ∎
         where
           open ≤-Reasoning
    
    partial≥0 {xs} dec xₙ→0    m = [ foreven m , forodd m ]′ ([-1]ᵏ≃1∨[-1]ᵏ≃[-1] m)
      where
        open ≤-Reasoning

        -1<1 : - 1ℝ < 1ℝ
        -1<1 = pos* (0 , ℚ.*<* (ℤ.+<+ (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))))

        1*-1<1 : 1ℝ * - 1ℝ < 1ℝ
        1*-1<1 = begin-strict
               1ℝ * - 1ℝ   ≈⟨ *-identityˡ (- 1ℝ) ⟩
                    - 1ℝ   <⟨ -1<1 ⟩
                      1ℝ  ∎

        --had to split it like this so that the termination checker accepts it

        foreven : (m : ℕ) → pow (- 1ℝ) m ≃ 1ℝ → ∑₀ (alt xs) m ≥ 0ℝ
        foreven zero _ = ≤-refl
        foreven (suc zero) -1≃1 = ⊥-elim (<-irrefl -1≃1 1*-1<1)
        foreven (suc (suc m-2)) pow≃1 = let [-1]ᵏxₖ = alt xs; m-1 = suc m-2 in begin --the m'th one is _not_ included!
              0ℝ                                    ≤⟨ nonNegx⇒0≤x (dec m-2) ⟩
              xs m-2 - xs m-1                        ≈⟨ solve 2 (λ x y → x ⊖ y ⊜ Κ 1ℚᵘ ⊗ x ⊕ Κ 1ℚᵘ ⊗ (⊝ Κ 1ℚᵘ) ⊗ y) ≃-refl (xs m-2) (xs m-1) ⟩
              1ℝ * xs m-2 + (1ℝ * - 1ℝ) * xs m-1    ≈⟨ +-cong
                                                           ((*-congʳ {xs m-2} {_} {_} (≃-trans (≃-symm pow≃1) (≃-symm ([-1]ⁿ≃[-1]ⁿ⁺² m-2)))))
                                                           ((*-congʳ {xs m-1} {_} {_} (*-congʳ { - 1ℝ} {_} {_} (≃-trans (≃-symm pow≃1) (≃-symm ([-1]ⁿ≃[-1]ⁿ⁺² m-2)))))) ⟩
              [-1]ᵏxₖ m-2 + [-1]ᵏxₖ m-1              ≈⟨ solve 2 (λ x y → x ⊕ y ⊜ Κ 0ℚᵘ ⊕ x ⊕ y) ≃-refl ([-1]ᵏxₖ m-2) ([-1]ᵏxₖ m-1) ⟩
              0ℝ + [-1]ᵏxₖ m-2 + [-1]ᵏxₖ m-1        ≤⟨ +-monoˡ-≤ ([-1]ᵏxₖ m-1) (+-monoˡ-≤ ([-1]ᵏxₖ m-2) (foreven m-2 (≃-trans ([-1]ⁿ≃[-1]ⁿ⁺² m-2) pow≃1))) ⟩
              ∑₀ [-1]ᵏxₖ (suc m-1)                   ∎

        forodd : (m : ℕ) → pow (- 1ℝ) m ≃ (- 1ℝ) → ∑₀ (alt xs) m ≥ 0ℝ
        forodd zero 1≃-1 = ⊥-elim (<-irrefl (≃-symm 1≃-1) -1<1)
        forodd (suc zero) _ = begin
               0ℝ    ≤⟨ xₙ≥0 dec xₙ→0 0 ⟩
               xs 0    ≈⟨ ≃-symm (*-identityˡ (xs 0)) ⟩
               alt xs 0 ≈⟨ ≃-symm (+-identityˡ (alt xs 0)) ⟩
               0ℝ + alt xs 0 ∎
        forodd (suc (suc m-2)) pow≃-1 = let [-1]ᵏxₖ = alt xs; m-1 = suc m-2; powm-2≃-1 = ≃-trans ([-1]ⁿ≃[-1]ⁿ⁺² m-2) pow≃-1 in begin  --the m'th one is _not_ included!
              0ℝ          ≤⟨ xₙ≥0 {xs} dec xₙ→0 m-1 ⟩
              xs m-1 ≈⟨ ≃-symm (*-identityˡ (xs m-1)) ⟩
              1ℝ * xs m-1 ≈⟨ *-congʳ {xs m-1} {_} {_} (solve 0 (Κ 1ℚᵘ ⊜ (⊝ Κ 1ℚᵘ) ⊗ (⊝ Κ 1ℚᵘ)) ≃-refl)  ⟩
              - 1ℝ * (- 1ℝ) * xs m-1 ≈⟨ *-congʳ {xs m-1} {_} {_} (*-congʳ { - 1ℝ} {_} {_} (≃-symm lpow≃-1) ) ⟩
              [-1]ᵏxₖ m-1     ≈⟨ ≃-symm (+-identityˡ ([-1]ᵏxₖ m-1)) ⟩
              0ℝ + [-1]ᵏxₖ m-1 ≤⟨ +-monoˡ-≤ ([-1]ᵏxₖ m-1) (foreven m-1 (≃-trans (*-congʳ {x = - 1ℝ} lpow≃-1) (solve 0 (⊝ Κ 1ℚᵘ ⊗ ⊝ Κ 1ℚᵘ ⊜ Κ 1ℚᵘ) ≃-refl))) ⟩
              ∑₀ [-1]ᵏxₖ (suc m-1) ∎
          where
          lpow≃-1 : pow (- 1ℝ) m-2 ≃ - 1ℝ
          lpow≃-1 = ≃-trans (solve 1 (λ x → x ⊜ x ⊗ ⊝ Κ 1ℚᵘ ⊗ ⊝ Κ 1ℚᵘ) ≃-refl (pow (- 1ℝ) m-2)) pow≃-1

    alt-shift≃[-1]ⁿ*shift-alt : {xs : ℕ → ℝ} → xs isDecreasing → xs ConvergesTo 0ℝ → ∀ (n i : ℕ) → alt (shift xs n) i ≃ pow (- 1ℝ) n * shift (alt xs) n i
    alt-shift≃[-1]ⁿ*shift-alt {xs} dec xₙ→0 n i = let n+i = n ℕ.+ i in begin
      pow (- 1ℝ) i * xs n+i    ≈⟨ ≃-symm (*-identityˡ (pow (- 1ℝ) i * xs n+i)) ⟩
      1ℝ * (pow (- 1ℝ) i * xs n+i) ≈⟨ *-congʳ (≃-symm ([-1]ⁿ*[-1]ⁿ≃1 n)) ⟩
      pow (- 1ℝ) n * pow (- 1ℝ) n * (pow (- 1ℝ) i * xs n+i)  ≈⟨ solve 4 (λ a b c d → a ⊗ b ⊗ (c ⊗ d) ⊜ a ⊗ ((b ⊗ c) ⊗ d)) ≃-refl (pow (- 1ℝ) n) (pow (- 1ℝ) n) (pow (- 1ℝ) i) (xs n+i) ⟩
      pow (- 1ℝ) n * ((pow (- 1ℝ) n * pow (- 1ℝ) i) * xs n+i)  ≈⟨ *-congˡ {x = pow (- 1ℝ) n} (*-congʳ {x = xs n+i} (xⁿxᵐ≃xⁿ⁺ᵐ (- 1ℝ) n i)) ⟩
      pow (- 1ℝ) n * (pow (- 1ℝ) n+i * xs n+i) ∎
      where
        open ≃-Reasoning

    slice≥0 : {xs : ℕ → ℝ} → xs isDecreasing → xs ConvergesTo 0ℝ → (n k : ℕ) → pow (- 1ℝ) n * ∑ (alt xs) n (n ℕ.+ k) ≥ 0ℝ
    slice≥0 {xs} dec xₙ→0 n k = let xsfromn = shift xs n; m = n ℕ.+ k; [-1]ᵏxₖ = alt xs in begin
       0ℝ                                    ≤⟨ partial≥0 {xsfromn} (shift-isDecreasing dec n) (fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y {xsfromn} {xs} (shift-is-subsequence xs n) (0ℝ , xₙ→0)) k ⟩
       ∑₀ (alt xsfromn) k                    ≈⟨ ∑₀-cong (alt-shift≃[-1]ⁿ*shift-alt {xs} dec xₙ→0 n) k ⟩
       ∑₀ (λ i → pow (- 1ℝ) n * shift [-1]ᵏxₖ n i) k   ≈⟨ ∑cxₙ≃c∑xₙ (shift [-1]ᵏxₖ n) (pow (- 1ℝ) n) zero k ⟩
       pow (- 1ℝ) n * ∑₀ (shift [-1]ᵏxₖ n) k ≈⟨ *-congˡ (shift-sum ([-1]ᵏxₖ) n k ) ⟩
       pow (- 1ℝ) n * ∑ [-1]ᵏxₖ n m          ∎
       where
         open ≤-Reasoning

    abstract
      fast-slice≥0 : {xs : ℕ → ℝ} → xs isDecreasing → xs ConvergesTo 0ℝ → (n k : ℕ) → pow (- 1ℝ) n * ∑ (alt xs) n (n ℕ.+ k) ≥ 0ℝ
      fast-slice≥0 = slice≥0

    partial≤x₀ : {xs : ℕ → ℝ} → xs isDecreasing → xs ConvergesTo 0ℝ → (n : ℕ) → ∑₀ (alt xs) n ≤ xs 0
    partial≤x₀ {xs} dec xₙ→0 0 = xₙ≥0 dec xₙ→0 0
    partial≤x₀ {xs} dec xₙ→0 (suc n-1) = let n = suc n-1; x₀ = xs 0; [-1]ᵏxₖ = alt xs in begin
      ∑₀ [-1]ᵏxₖ n                            ≈⟨  solve 2 (λ s x → s ⊜ x ⊖ (Κ 1ℚᵘ ⊗ ⊝ Κ 1ℚᵘ) ⊗ (s ⊖ (Κ 0ℚᵘ ⊕ Κ 1ℚᵘ ⊗ x))) ≃-refl (∑₀ [-1]ᵏxₖ n) x₀ ⟩
      x₀ - (pow (- 1ℝ) 1) * ∑ [-1]ᵏxₖ 1 n    ≤⟨ +-monoʳ-≤ x₀ (neg-mono-≤ (fast-slice≥0 {xs} dec xₙ→0 1 n-1)) ⟩ --it needs the hidden parameter!
      x₀ - 0ℝ                                ≈⟨ +-congʳ x₀ (≃-symm 0≃-0) ⟩
      x₀ + 0ℝ                                ≈⟨ +-identityʳ x₀ ⟩
      x₀ ∎
      where
        open ≤-Reasoning

    slice≤xₙ : {xs : ℕ → ℝ} → xs isDecreasing → xs ConvergesTo 0ℝ → (n k : ℕ) → pow (- 1ℝ) n * ∑ (alt xs) n (n ℕ.+ k) ≤ xs n
    slice≤xₙ {xs} dec xₙ→0 n k = let xsfromn = shift xs n; m = n ℕ.+ k; [-1]ᵏxₖ = alt xs in begin
      pow (- 1ℝ) n * ∑ [-1]ᵏxₖ n m           ≈⟨ ≃-symm (*-congˡ (shift-sum ([-1]ᵏxₖ) n k )) ⟩
      pow (- 1ℝ) n * ∑₀ (shift [-1]ᵏxₖ n) k ≈⟨ ≃-symm (∑cxₙ≃c∑xₙ (shift [-1]ᵏxₖ n) (pow (- 1ℝ) n) zero k) ⟩
      ∑₀ (λ i → pow (- 1ℝ) n * shift [-1]ᵏxₖ n i) k   ≈⟨ ≃-symm (∑₀-cong (alt-shift≃[-1]ⁿ*shift-alt {xs} dec xₙ→0 n) k) ⟩
      ∑₀ (alt xsfromn) k                    ≤⟨ partial≤x₀ {xsfromn} (shift-isDecreasing dec n) (fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y {xsfromn} {xs} (shift-is-subsequence xs n) (0ℝ , xₙ→0)) k ⟩
      xsfromn 0                             ≈⟨ ≃-refl₂ (cong xs (ℕP.+-identityʳ n)) ⟩
      xs n ∎
      where
        open ≤-Reasoning

    abstract
      fast-slice≤xₙ : {xs : ℕ → ℝ} → xs isDecreasing → xs ConvergesTo 0ℝ → (n k : ℕ) → pow (- 1ℝ) n * ∑ (alt xs) n (n ℕ.+ k) ≤ xs n
      fast-slice≤xₙ = slice≤xₙ

alternating-series-test : {xs : ℕ → ℝ} → xs isDecreasing → xs ConvergesTo 0ℝ →
                          SeriesOf (λ n → pow (- 1ℝ) n * xs n) isConvergent
alternating-series-test {xs} dec (con* hyp) = fast-cauchy⇒convergent (cauchy* (λ k {k≢0} → (proj₁ (hyp k {k≢0}), ineq k {k≢0})))
  where
    open ≤-Reasoning

    [-1]ᵏxₖ : ℕ → ℝ
    [-1]ᵏxₖ = alt xs

    dec₂ : xs isDecreasing₂
    dec₂ = fast-isDecreasing⇒isDecreasing₂ dec

    knowing-n≤m : (k : ℕ) → {k≢0 : k ≢0} → (m n : ℕ) → n ℕ.≥ suc (proj₁ (hyp k {k≢0})) →
                  n ℕ.≤ m →  ∣ SeriesOf (alt xs) m - SeriesOf (alt xs) n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
    knowing-n≤m k {k≢0} m n n≥M n≤m = let m-n = m ℕ.∸ n in begin
        ∣ SeriesOf [-1]ᵏxₖ m - SeriesOf [-1]ᵏxₖ n ∣    ≈⟨ ∣-∣-cong (≃-symm (∑ₙᵐ≃∑₀ᵐ-∑₀ⁿ [-1]ᵏxₖ n m)) ⟩
        ∣ ∑ [-1]ᵏxₖ n m ∣                             ≈⟨ [ (λ [-1]ⁿ≃1 → ∣-∣-cong (≃-trans (≃-symm (*-identityˡ (∑ [-1]ᵏxₖ n m))) (*-congʳ (≃-symm [-1]ⁿ≃1)))) ,
                                                         helper ]′
                                                         ([-1]ᵏ≃1∨[-1]ᵏ≃[-1] n) ⟩
        ∣ pow (- 1ℝ) n * ∑ [-1]ᵏxₖ n m ∣              ≈⟨ ≃-refl₂ (sym (cong (λ x → ∣ pow (- 1ℝ) n * ∑ [-1]ᵏxₖ n x ∣) (ℕP.m+[n∸m]≡n n≤m))) ⟩ --with ≃-refl₂, cong and ℕP.m+[n∸m]≡n n≤m
        ∣ pow (- 1ℝ) n * ∑ [-1]ᵏxₖ n (n ℕ.+ m-n) ∣     ≈⟨ 0≤x⇒∣x∣≃x (fast-slice≥0 dec (con* hyp) n m-n) ⟩
         pow (- 1ℝ) n * ∑ [-1]ᵏxₖ n (n ℕ.+ m-n)      ≤⟨ fast-slice≤xₙ dec (con* hyp) n m-n ⟩
         xs n                                        ≈⟨ ≃-trans (≃-symm (0≤x⇒∣x∣≃x (xₙ≥0 dec (con* hyp) n))) (∣-∣-cong (≃-trans (≃-symm (+-identityʳ (xs n)))  (+-congʳ (xs n) 0≃-0))) ⟩
         ∣ xs n - 0ℝ ∣                                ≤⟨ proj₂ (hyp k {k≢0}) n n≥M ⟩
         (+ 1 / k) ⋆ ∎
      where
        helper : (pow (- 1ℝ) n) ≃ - 1ℝ → ∣ ∑ [-1]ᵏxₖ n m ∣ ≃ ∣ pow (- 1ℝ) n * ∑ [-1]ᵏxₖ n m ∣
        helper [-1]ⁿ≃-1 = ≃-Reasoning.begin
             ∣ ∑ [-1]ᵏxₖ n m ∣   ≃-Reasoning.≈⟨ ≃-symm ∣-x∣≃∣x∣ ⟩
             ∣ - ∑ [-1]ᵏxₖ n m ∣  ≃-Reasoning.≈⟨ ∣-∣-cong (solve 1 (λ x → ⊝ x ⊜ ⊝ Κ 1ℚᵘ ⊗ x) ≃-refl (∑ [-1]ᵏxₖ n m)) ⟩
             ∣ - 1ℝ * ∑ [-1]ᵏxₖ n m ∣  ≃-Reasoning.≈⟨ ∣-∣-cong (*-congʳ (≃-symm [-1]ⁿ≃-1) ) ⟩
             ∣ pow (- 1ℝ) n * ∑ [-1]ᵏxₖ n m ∣ ≃-Reasoning.∎

    ineq : (k : ℕ) → {k≢0 : k ≢0} → (m n : ℕ) → m ℕ.≥ suc (proj₁ (hyp k {k≢0})) → n ℕ.≥ suc (proj₁ (hyp k {k≢0})) →
                      ∣ SeriesOf (alt xs) m - SeriesOf (alt xs) n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
    ineq k {k≢0} m n m≥M n≥M    with ℕP.≤-total n m
    ineq k {k≢0} m n _   n≥M    | inj₁ n≤m             = knowing-n≤m k {k≢0} m n n≥M n≤m    
    ineq k {k≢0} m n m≥M _      | inj₂ n≥m = begin
          ∣ SeriesOf [-1]ᵏxₖ m - SeriesOf [-1]ᵏxₖ n ∣         ≈⟨ ≃-symm ∣-x∣≃∣x∣ ⟩
          ∣ - (SeriesOf [-1]ᵏxₖ m - SeriesOf [-1]ᵏxₖ n) ∣     ≈⟨ ∣-∣-cong (solve 2 (λ x y → ⊝ (x ⊖ y) ⊜ y ⊖ x) ≃-refl (SeriesOf [-1]ᵏxₖ m) (SeriesOf [-1]ᵏxₖ n)) ⟩
          ∣ SeriesOf [-1]ᵏxₖ n - SeriesOf [-1]ᵏxₖ m ∣         ≤⟨ knowing-n≤m k {k≢0} n m m≥M n≥m ⟩
          (+ 1 / k) ⋆ ∎


abstract
  fast-alternating-series-test : {xs : ℕ → ℝ} → xs isDecreasing → xs ConvergesTo 0ℝ →
                                 SeriesOf (λ n → pow (- 1ℝ) n * xs n) isConvergent
  fast-alternating-series-test = alternating-series-test

π : ℝ
π = (+ 4 / 1) ⋆ * proj₁ (fast-alternating-series-test {λ n → (+ 1 / (1 ℕ.+ 2 ℕ.* n)) ⋆}
                        dec [1+2k]⁻¹→0)
  where
    open ≤-Reasoning
    [1+2k]⁻¹ : ℕ → ℝ
    [1+2k]⁻¹ n = (+ 1 / (1 ℕ.+ 2 ℕ.* n)) ⋆
    
    dec : [1+2k]⁻¹ isDecreasing
    dec n = p≤q⇒p⋆≤q⋆ (+ 1 / (1 ℕ.+ 2 ℕ.* (suc n))) (+ 1 / (1 ℕ.+ 2 ℕ.* n))
            (q≤r⇒+p/r≤+p/q 1 (1 ℕ.+ 2 ℕ.* n) (1 ℕ.+ 2 ℕ.* (suc n))
            (ℕP.+-monoʳ-≤ 1 (ℕP.*-monoʳ-≤ 2 (ℕP.n≤1+n n))))

    [1+2k]⁻¹→0 : [1+2k]⁻¹ ConvergesTo 0ℝ
    [1+2k]⁻¹→0 = con* (λ {(suc k-1) → let k = suc k-1 in
                 k-1 , λ n n≥k → begin
      ∣ [1+2k]⁻¹ n - 0ℝ ∣ ≈⟨ ∣-∣-cong (solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) ≃-refl ([1+2k]⁻¹ n)) ⟩
      ∣ [1+2k]⁻¹ n ∣      ≈⟨ nonNegx⇒∣x∣≃x (nonNegp⇒nonNegp⋆ (+ 1 / (1 ℕ.+ 2 ℕ.* n)) _) ⟩
      [1+2k]⁻¹ n         ≤⟨ p≤q⇒p⋆≤q⋆ (+ 1 / (1 ℕ.+ 2 ℕ.* n)) (+ 1 / (1 ℕ.+ 2 ℕ.* k))
                            (q≤r⇒+p/r≤+p/q 1 (1 ℕ.+ 2 ℕ.* k) (1 ℕ.+ 2 ℕ.* n)
                            (ℕ.s≤s (ℕP.*-monoʳ-≤ 2 n≥k))) ⟩
      [1+2k]⁻¹ k         ≤⟨ p≤q⇒p⋆≤q⋆ (+ 1 / (1 ℕ.+ 2 ℕ.* k)) (+ 1 / k)
                            (q≤r⇒+p/r≤+p/q 1 k (1 ℕ.+ 2 ℕ.* k)
                            (ℕP.≤-trans 
                            (ℕP.m≤n*m k {2} (ℕ.s≤s ℕ.z≤n)) (ℕP.n≤1+n (2 ℕ.* k)))) ⟩
      (+ 1 / k) ⋆         ∎})


