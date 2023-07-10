-- Representation of real compact intervals; of an equal partition of a real compact interval and some results about them.

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
open import Sequence
open import FiniteSequences.SigmaIndices
open ℝ-Solver

-- Syntax I like better for product type representations of subsets
-- Not a fan of the normal syntax and ∃ is pretty irrelevant for this usage
𝕊 : {A : Set} (P : Pred A 0ℓ) → Set
𝕊 {A} P = Σ A P

data IntervalKind : Set where
  ⦅_,_⦆  : (a b : ℝ) → IntervalKind
  ⦅_,_⟧  : (a b : ℝ) → IntervalKind
  ⟦_,_⦆  : (a b : ℝ) → IntervalKind
  ⟦_,_⟧  : (a b : ℝ) → IntervalKind
  ⦅-∞,_⦆ : (b : ℝ)   → IntervalKind
  ⦅-∞,_⟧ : (b : ℝ)   → IntervalKind
  ⦅_,∞⦆  : (a : ℝ)   → IntervalKind
  ⟦_,∞⦆  : (a : ℝ)   → IntervalKind

-- Interval semantics
IntervalPred : IntervalKind → Pred ℝ 0ℓ
IntervalPred ⦅ a , b ⦆ x = a < x < b
IntervalPred ⦅ a , b ⟧ x = a < x ≤ b
IntervalPred ⟦ a , b ⦆ x = a ≤ x < b
IntervalPred ⟦ a , b ⟧ x = a ≤ x ≤ b
IntervalPred ⦅-∞, b ⦆  x = x < b
IntervalPred ⦅-∞, b ⟧  x = x ≤ b
IntervalPred ⦅ a ,∞⦆   x = a < x
IntervalPred ⟦ a ,∞⦆   x = a ≤ x

-- Syntactic sugar for intervals as sets
-- So now each interval is a record type (as was originally desired) but induction on the kinds of intervals
-- is still possible via IntervalKind.
-- It's kind of annoying to specify the IntervalKind all of the time, and have to write an interval as Interval ⦅ a , b ⦆.
-- It would be much better if I could refer to intervals without the Interval word constructing the set.
-- Also, wouldn't it be useful if, when constructing some type (like this one), we could choose a default "piece" of the
-- type to perform induction on? I'm going to be doing induction on IntervalKind whenever I need to prove some basic
-- property about intervals, but it's annoying to specify IntervalKind all of the time. It would be cool if I could specify,
-- in this definition below, the default type to perform induction on for Interval.
Interval : (IK : IntervalKind) → Set
Interval IK = 𝕊 (IntervalPred IK)

{-
How about this definition:

data IntervalKind : Set where
  open-open     : (a b : ℝ) → IntervalKind
  open-closed   : (a b : ℝ) → IntervalKind
  closed-open   : (a b : ℝ) → IntervalKind
  closed-closed : (a b : ℝ) → IntervalKind

IntervalPred : (IK : IntervalKind) → Pred ℝ 0ℓ
IntervalPred (open-open a b)     = (x : ℝ) → a < x < b 
IntervalPred (open-closed a b)   = (x : ℝ) → a < x ≤ b
IntervalPred (closed-open a b)   = (x : ℝ) → a ≤ x < b
IntervalPred (closed-closed a b) = (x : ℝ) → a ≤ x ≤ b

⦅_,_⦆ : (a b : ℝ) → Set
⦅ a , b ⦆ = 𝕊 (IntervalPred open-open a b)

⦅_,_⟧ : (a b : ℝ) → Set
⦅ a , b ⟧ = 𝕊 (IntervalPred open-closed a b)

⟦_,_⦆ : (a b : ℝ) → Set
⟦ a , b ⦆ = 𝕊 (IntervalPred closed-open a b)

⟦_,_⟧ : (a b : ℝ) → Set
⟦ a , b ⟧ = 𝕊 (IntervalPred closed-closed a b)



-}

record CompactInterval : Set where
  field
    CIlower            : ℝ
    CIupper            : ℝ
    CIlower≤upper      : CIlower ≤ CIupper
open CompactInterval public

_↓ : CompactInterval → Set
_↓ D = Interval ⟦ CIlower D , CIupper D ⟧

CINonempty : (D : CompactInterval) → D ↓
CINonempty D = CIlower D , ≤-refl {CIlower D} , CIlower≤upper D

{-
CompactInterval : ℝ → ℝ → Set
CompactInterval = _≤_

lower upper : {x y : ℝ} → CompactInterval x y → ℝ
lower {x} {_} _ = x
upper {_} {y} _ = y

_↓ : {x y : ℝ} → CompactInterval x y → Set
_↓ {x} {y} _ = Interval ⟦ x , y ⟧

CINonempty : {x y : ℝ} (CI : CompactInterval x y) → CI ↓
CINonempty {x} {y} CI = x , {!!}
-}

--Simply the numbers, without the proofs that they are in the interval. We also do not take the interval itself here. Just the pure recursion.
--The recursive form is important because it makes it easier to make inductive proofs.
fullPartition-base : (a b : ℝ) (n : ℕ) .{n≢0 : n ≢0} → ℕ → ℝ
fullPartition-base a b n zero = a
fullPartition-base a b n {n≢0} (suc i) = fullPartition-base a b n {n≢0} i + ((+ 1 / n) {n≢0}) ⋆ * (b - a)

--(These for the next one, but is also useful otherwise.)
ℚ≃-refl₂ : {a b : ℚᵘ} → a ≡ b → a ℚ.≃ b
ℚ≃-refl₂ {a} .{a} refl = ℚP.≃-refl

a/n+b/n≃[a+b]/n : (a b : ℤ) (n : ℕ) .{n≢0 : n ≢0} → (a / n) {n≢0} ℚ.+ (b / n) {n≢0} ℚ.≃ ((a ℤ.+ b) / n) {n≢0}
a/n+b/n≃[a+b]/n a b (suc n-1) = let n = (suc n-1) in begin-equality
                  a / n ℚ.+ b / n   ≈⟨ ℚP.+-cong {a / n} {a / 1 ℚ.* (+ 1 / n)} {b / n} {b / 1 ℚ.* (+ 1 / n)} (ℚ≃-refl₂ (ℚP.↥↧≡⇒≡ (sym (ℤP.*-identityʳ a)) (cong suc (sym (ℕP.+-identityʳ n-1)))))
                                                                                                              ((ℚ≃-refl₂ (ℚP.↥↧≡⇒≡ (sym (ℤP.*-identityʳ b)) (cong suc (sym (ℕP.+-identityʳ n-1)))))) ⟩
                  a / 1 ℚ.* (+ 1 / n) ℚ.+ b / 1 ℚ.* (+ 1 / n) ≈⟨ ℚP.≃-sym (ℚP.*-distribʳ-+ (+ 1 / n) (a / 1) (b / 1)) ⟩
                  (a / 1 ℚ.+ b / 1) ℚ.* (+ 1 / n) ≈⟨ ℚP.*-congʳ {+ 1 / n} {a / 1 ℚ.+ b / 1} {(a ℤ.+ b) / 1} (ℚ≃-refl₂ (cong (λ d → mkℚᵘ d 0)
                                                                                                      (trans (cong (λ d → (a ℤ.* d ℤ.+ b ℤ.* (↧ mkℚᵘ a 0))) (ℚP.↧[p/q]≡q b 1))
                                                                                                      (trans (cong (λ d → a ℤ.* + 1 ℤ.+ b ℤ.* d) (ℚP.↧[p/q]≡q a 1))
                                                                                                      (ℤsolve 2 (λ a b → (a :* ℤΚ (+ 1)) :+ (b :* ℤΚ (+ 1)) := (a :+ b)) refl a b))
                                                                                                      {-begin
                                                                                                      a ℤ.* (↧ mkℚᵘ b 0) ℤ.+ b ℤ.* (↧ mkℚᵘ a 0) ≡⟨ {!ℚP.↧[p/q]≡q!} ⟩
                                                                                                      a ℤ.* (+ 1) ℤ.+ b ℤ.* (↧ mkℚᵘ a 0)         ≡⟨ ? ⟩
                                                                                                      a ℤ.* (+ 1) ℤ.+ b ℤ.* (+ 1)                ≡⟨ ? ⟩
                                                                                                      a ℤ.+ b                                    ∎-}))) ⟩
                  (a ℤ.+ b) / 1 ℚ.* (+ 1 / n) ≈⟨ ℚ≃-refl₂ (ℚP.↥↧≡⇒≡ (ℤP.*-identityʳ (a ℤ.+ b)) (cong suc (ℕP.+-identityʳ n-1))) ⟩
                  (a ℤ.+ b) / n ∎
  where
  open ℚP.≤-Reasoning
  

--Now a proof that this is equal to a+(i/n)*(b-a).
fullPartition-base-aᵢ≃a+i/n*[b-a] : (a b : ℝ) (n : ℕ) .{n≢0 : n ≢0} (i : ℕ) → fullPartition-base a b n {n≢0} i ≃ a + ((+ i / n) {n≢0})⋆ * (b - a)
fullPartition-base-aᵢ≃a+i/n*[b-a] a b (suc n-1) zero = let n = suc n-1 in begin
                                             a          ≈⟨ ≃-symm (+-identityʳ a) ⟩
                                             a + 0ℝ     ≈⟨ +-congʳ a {0ℝ} {(+ zero / n) ⋆ * (b - a)}
                                                                (≃-trans (≃-symm (*-zeroˡ (b - a)))
                                                                         (*-congʳ {b - a} (⋆-cong {0ℚᵘ} {+ zero / n} (ℚ.*≡* refl)))) ⟩
                                             a + (+ zero / n) ⋆ * (b - a) ∎
  where open ≃-Reasoning
fullPartition-base-aᵢ≃a+i/n*[b-a] a b (suc n-1) {_} (suc i) = let n = suc n-1 in begin
             fullPartition-base a b n i + (+ 1 / n) ⋆ * (b - a) ≈⟨ +-congˡ ((+ 1 / n) ⋆ * (b - a)) (fullPartition-base-aᵢ≃a+i/n*[b-a] a b n i) ⟩
                               a + (+ i / n)⋆ * (b - a) + (+ 1 / n) ⋆ * (b - a) ≈⟨ +-assoc a ((+ i / n)⋆ * (b - a)) ((+ 1 / n)⋆ * (b - a)) ⟩
                               a + ((+ i / n)⋆ * (b - a) + (+ 1 / n) ⋆ * (b - a)) ≈⟨ +-congʳ a {(+ i / n)⋆ * (b - a) + (+ 1 / n) ⋆ * (b - a)} {(+ (suc i) / n)⋆ * (b - a)}
                                                                      (≃-trans (≃-symm (*-distribʳ-+ (b - a) ((+ i / n)⋆) ((+ 1 / n)⋆)))
                                                                               (*-congʳ {b - a} {(+ i / n) ⋆ + (+ 1 / n) ⋆} {(+ (suc i) / n)⋆}
                                                                               (≃-trans (≃-symm (⋆-distrib-+ (+ i / n) (+ 1 / n)))
                                                                                        (⋆-cong {+ i / n ℚ.+ + 1 / n} {+ (suc i) / n}
                                                                                        (ℚP.≃-trans (a/n+b/n≃[a+b]/n (+ i) (+ 1) n)
                                                                                                    (ℚ≃-refl₂ (ℚP.↥↧≡⇒≡ (cong +_ (ℕP.+-comm i 1)) refl))))))) ⟩
                               a + (+ (suc i) / n)⋆ * (b - a) ∎
  where open ≃-Reasoning


--Some results based on this that will be needed for the final definition.
private
  -- Just something that was needed here.
  ℤn≡m⇒n≤m : {n m : ℤ} → n ≡ m → n ℤ.≤ m
  ℤn≡m⇒n≤m {n} .{n} refl = ℤP.≤-refl
  
  a≤b⇒a≤aᵢ : (a b : ℝ) (n : ℕ) .{n≢0 : n ≢0} (i : ℕ) → a ≤ b → a ≤ fullPartition-base a b n {n≢0} i
  a≤b⇒a≤aᵢ a b (suc n-1) i a≤b = let n = suc n-1 in begin
                           a           ≤⟨ 0≤x⇒y≤y+x {(+ i / n)⋆ * (b - a)} a (0≤x,y⇒0≤x*y {(+ i / n)⋆} {b - a} (p≤q⇒p⋆≤q⋆ (0ℚᵘ) (+ i / n) (ℚ.*≤* (ℤP.≤-trans (ℤ.+≤+ (ℕ.z≤n {i}))
                                                                                                                                                                (ℤn≡m⇒n≤m {+ i} {+ i ℤ.* + 1} (sym (ℤP.*-identityʳ (+ i)))))))
                                                                                                                (x≤y⇒0≤y-x a≤b)) ⟩
                           a + (+ i / n)⋆ * (b - a) ≈⟨ ≃-symm (fullPartition-base-aᵢ≃a+i/n*[b-a] a b n i) ⟩
                  fullPartition-base a b n i ∎
    where
    open ≤-Reasoning

  i≤n∧a≤b⇒aᵢ≤b : (a b : ℝ) (n : ℕ) .{n≢0 : n ≢0} {i : ℕ} → i ℕ.≤ n → a ≤ b → fullPartition-base a b n {n≢0} i ≤ b
  i≤n∧a≤b⇒aᵢ≤b a b (suc n-1) {_} {i} i≤n a≤b = let n = suc n-1 in begin
                                  fullPartition-base a b (suc n-1) i    ≈⟨ fullPartition-base-aᵢ≃a+i/n*[b-a] a b n i ⟩
                                  a + (+ i / n)⋆ * (b - a)                ≤⟨ +-monoʳ-≤ a (*-monoʳ-≤-nonNeg {(+ i / n)⋆} {b - a} {1ℝ}
                                                                                           (p≤q⇒p⋆≤q⋆ (+ i / n) (1ℚᵘ)
                                                                                             (ℚ.*≤* (ℤP.≤-trans (ℤn≡m⇒n≤m {+ i ℤ.* + 1} {+ i} (ℤP.*-identityʳ (+ i)))
                                                                                                    (ℤP.≤-trans (ℤ.+≤+ i≤n)
                                                                                                                (ℤn≡m⇒n≤m {+ n} {+ (n ℕ.+ 0)} (cong +[1+_] (sym (ℕP.+-identityʳ n-1))))))))
                                                                                           (0≤x⇒nonNegx {b - a} (x≤y⇒0≤y-x a≤b))) ⟩
                          --via   a + (+ n / n)⋆ * (b - a)
                                  a + 1ℝ * (b - a)                       ≈⟨ solve 2 (λ a b → a ⊕ Κ 1ℚᵘ ⊗ (b ⊖ a) ⊜ b) ≃-refl a b ⟩
                                  b                                       ∎
    where open ≤-Reasoning


--A partition of a compact interval to n equally sized subintervals. Returns the (suc n) separators.
--Maybe we should change the parameter to a sigma index for the sake of consistency.

fullPartition : (D : CompactInterval) (n : ℕ) {n≢0 : n ≢0} → {i : ℕ} → i ℕ.≤ n → D ↓
fullPartition D (suc n-1) {_} {i} i≤n = let n = suc n-1 ; a = CIlower D ; b = CIupper D in
                                                          fullPartition-base a b n i ,
                                                          a≤b⇒a≤aᵢ a b n i (CIlower≤upper D) ,
                                                          i≤n∧a≤b⇒aᵢ≤b a b n {_} {i} i≤n (CIlower≤upper D)
{-
fullPartition D (suc n-1) {_} {zero} _ = CIlower D , ≤-refl {CIlower D} , CIlower≤upper D
fullPartition D (suc n-1) {_} {suc i-1} i<sucn = newOne , ≤-trans {CIlower D} {proj₁ rec} {newOne} (proj₁ (proj₂ rec))
        (begin
            proj₁ rec     ≈⟨ ≃-symm (+-identityʳ (proj₁ rec)) ⟩
            proj₁ rec + 0ℝ ≤⟨ +-monoʳ-≤ (proj₁ rec) {0ℝ} {1/n * (b - a)} (0≤x,y⇒0≤x*y {1/n} {b - a} (nonNegx⇒0≤x {1/n} (nonNegp⇒nonNegp⋆ (+ 1 / n) tt)) (x≤y⇒0≤y-x {a} {b} (CIlower≤upper D))) ⟩
            proj₁ rec + (+ 1 / n) ⋆ * (b - a) ∎) ,
        {!begin
            proj₁ rec + 1/n * (b - a)  ≈⟨ ? ⟩
            !}
  where
  open ≤-Reasoning
  n : ℕ
  n = suc n-1
  a b 1/n : ℝ
  a = CIlower D
  b = CIupper D
  1/n = (+ 1 / n) ⋆
  rec : D ↓
  rec = fullPartition D n {_} {i-1} (ℕP.<-trans (ℕP.≤-refl {suc i-1}) i<sucn)
  newOne : ℝ
  newOne = proj₁ rec + (+ 1 / n) ⋆ * (b - a)
-}

fullPartition-a₀≃a : ∀ (D : CompactInterval) (n : ℕ) {n≢0 : n ≢0} → proj₁ (fullPartition D n {n≢0} {zero} ℕ.z≤n) ≃ CIlower D
fullPartition-a₀≃a D (suc n-1) = ≃-refl

fullPartition-aₙ≃b : ∀ (D : CompactInterval) (n : ℕ) {n≢0 : n ≢0} → proj₁ (fullPartition D n {n≢0} {n} (ℕP.≤-refl)) ≃ CIupper D
fullPartition-aₙ≃b D (suc n-1) = let n = suc n-1 ; a = CIlower D ; b = CIupper D in begin
        proj₁ (fullPartition D n (ℕP.≤-refl))                ≈⟨ fullPartition-base-aᵢ≃a+i/n*[b-a] a b n n ⟩
        a + (+ n / n)⋆ * (b - a)                               ≈⟨ +-congʳ a {(+ n / n)⋆ * (b - a)} {b - a} (≃-trans (*-congʳ {b - a} {(+ n / n)⋆} {1ℝ} (⋆-cong (ℚ.*≡* (cong +[1+_] (trans (ℕP.*-identityʳ n-1)
                                                                                                                                                                                         (sym (ℕP.+-identityʳ n-1)))))))
                                                                                                                   (*-identityˡ (b - a))) ⟩
        a + (b - a)                                            ≈⟨ solve 2 (λ a b → a ⊕ (b ⊖ a) ⊜ b) ≃-refl a b ⟩
        b                                                      ∎
  where open ≃-Reasoning

{-
TODO
New idea: with corollary-2-17
Let d:=(b-a)/n and assume that a < b. Then we can show an at most 2*d long interval that contains x.
- Since we know that aₙ₋₁ < b, either aₙ₋₁ < x or x < b. In the former case, we know that a₀ = a ≤ x < a₁, and can finish the proof accordingly.
- If we already know that x < aₖ:
  - If k > 1, either aₖ₋₂ < x or x < aₖ₋₁ (because aₖ₋₂ < aₖ₋₁). In the latter case, we step forward; in the former, we can finish the proof from aₖ₋₂ < x < aₖ.
  - If k = 1, we know that a = a₀ ≤ x < a₁, and finish the proof accordingly.
We step backwards because that's how it is easier to handle Fins.

This only works, however, if we know that a < b. Of course, if a = b, the proof is trivial;
but if we only know that a ≤ b, we cannot decide.
What about working in (a - ε, b + ε) for some arbitrary ε > 0?
-}

fullPartition-pointNear :  ∀ (D : CompactInterval) (a<b : CIlower D < CIupper D) (n : ℕ) {n≢0 : n ≢0} (xd : D ↓) →
          ∃ λ (sk : SigInd n) →
            ∣ proj₁ (fullPartition D n {n≢0} (proj₂ sk)) - proj₁ xd ∣ < ((+ 1 / n) {n≢0}) ⋆ * (CIupper D - CIlower D)
fullPartition-pointNear D a<b (suc n-1) (x , prx) = [ rec {n} {ℕP.≤-refl} , rightEnd ]′ (corollary-2-17 x aₙ₋₁ aₙ
                                                                                                         (begin-strict
                                                                                                                aₙ₋₁        ≈⟨ ≃-symm (+-identityʳ aₙ₋₁) ⟩
                                                                                                                aₙ₋₁ + 0ℝ   <⟨ +-monoʳ-< aₙ₋₁ {0ℝ} {d} 0<d ⟩
                                                                                                                aₙ₋₁ + d    ∎))
  where
  open ≤-Reasoning
  n : ℕ
  n = suc n-1
  asdℕ : {i : ℕ} → i ℕ.≤ n  → D ↓
  asdℕ = fullPartition D n
  asℕ : {i : ℕ} → i ℕ.≤ n  → ℝ
  asℕ i≤n = proj₁ (asdℕ i≤n)
  a b d aₙ₋₁ aₙ : ℝ
  a = CIlower D
  b = CIupper D
  d = (+ 1 / n) ⋆ * (b - a)
  aₙ₋₁ = asℕ {n-1} (≤-step ℕP.≤-refl)
  aₙ = asℕ {n} ℕP.≤-refl   -- this is actually equal to b

  0<d : 0ℝ < d
  0<d = posx⇒0<x (posx,y⇒posx*y {(+ 1 / n) ⋆} {b - a} (0<p⇒0<p⋆ (+ 1 / n) tt) a<b) -- here we need a < b

  --if it's already greater than aₙ₋₁:
  rightEnd : aₙ₋₁ < x → ∃ λ (sk : SigInd n) →
            ∣ asℕ (proj₂ sk) - x ∣ < d
  rightEnd aₙ₋₁<x = (n , ℕP.≤-refl) , -y<x<y⇒∣x∣<y (aₙ - x) d ((begin-strict
                                                                  - d        <⟨ neg-mono-< {0ℝ} {d} 0<d ⟩
                                                                  - 0ℝ       ≈⟨ ≃-symm 0≃-0 ⟩
                                                                    0ℝ       ≈⟨ ≃-symm (+-inverseʳ b) ⟩
                                                               b  - b        ≈⟨ +-congˡ (- b) {b} {aₙ} (≃-symm (fullPartition-aₙ≃b D n)) ⟩
                                                               aₙ - b        ≤⟨ +-monoʳ-≤ aₙ { - b} { - x} (neg-mono-≤ {x} {b} (proj₂ prx)) ⟩
                                                               aₙ - x        ∎) ,
                                                               (begin-strict
                                                               aₙ - x        <⟨ +-monoʳ-< aₙ { - x} { - aₙ₋₁} (neg-mono-< {aₙ₋₁} {x} aₙ₋₁<x) ⟩
                                                               aₙ - aₙ₋₁     ≈⟨ solve 2 (λ d a → (a ⊕ d) ⊖ a ⊜ d) ≃-refl d aₙ₋₁ ⟩
                                                               d              ∎))

  rec : {l : ℕ} {l≤n : l ℕ.≤ n} → x < asℕ l≤n → ∃ λ (sk : Σ ℕ (λ k → k ℕ.≤ n)) →
            ∣ asℕ (proj₂ sk) - x ∣ < d
  rec {zero} x<a = ⊥-elim (<⇒≱ x<a (proj₁ prx)) --a contradiction
  rec {suc zero} x<a₁ = (zero , ℕ.z≤n) , -y<x<y⇒∣x∣<y (a - x) d ((begin-strict
                                                                              - d                         ≈⟨ solve 2 (λ d a → ⊝ d ⊜ a ⊖ (a ⊕ d)) ≃-refl d a ⟩
                                                                              a - a₁                      <⟨ +-monoʳ-< a { - a₁} { - x} (neg-mono-< {x} {a₁} x<a₁) ⟩
                                                                              a - x                       ∎) ,
                                                                       (begin-strict
                                                                              a - x                       ≤⟨ x≤y⇒x-y≤0 (proj₁ prx) ⟩
                                                                              0ℝ                          <⟨ 0<d ⟩ -- here we need a<b
                                                                              d                           ∎))
    where
    a₁ : ℝ
    a₁ = asℕ {suc zero} (ℕ.s≤s ℕ.z≤n)
  rec {suc (suc l-2)} {hyp} x<aₗ = [ (rec {suc l-2} {ℕP.<-trans ℕP.≤-refl hyp}) , case₂ ]′ (corollary-2-17 x aₗ₋₂ aₗ₋₁ (0<x⇒posx ((begin-strict
                                                                                      0ℝ   <⟨ 0<d ⟩ -- here we need a<b
                                                                                      d    ≈⟨ solve 2 (λ x y → x ⊜ y ⊕ x ⊖ y) ≃-refl d aₗ₋₂ ⟩
                                                                                      aₗ₋₂ + d - aₗ₋₂ ∎) {tt})))
    where
    aₗ₋₂ aₗ₋₁ : ℝ
    aₗ₋₂ = asℕ {l-2} (ℕP.≤-trans (ℕP.≤-step (ℕP.≤-step ℕP.≤-refl)) hyp)
    aₗ₋₁ = asℕ {suc l-2} (ℕP.≤-trans (ℕ.s≤s (ℕP.≤-step ℕP.≤-refl)) hyp)
    aₗ = asℕ {suc (suc l-2)} hyp

    case₂ : aₗ₋₂ < x → ∃ λ (sk : Σ ℕ (λ k → k ℕ.≤ n)) →
            ∣ asℕ (proj₂ sk) - x ∣ < d
    case₂ aₗ₋₂<x = let l-1≤n = (ℕP.≤-trans (ℕ.s≤s (ℕP.≤-step ℕP.≤-refl)) hyp) in (suc l-2 , l-1≤n) , -y<x<y⇒∣x∣<y (asℕ {suc l-2} l-1≤n - x) d ((begin-strict
                                                                                - d                        ≈⟨ solve 2 (λ d a → ⊝ d ⊜ a ⊕ d ⊖ (a ⊕ d ⊕ d)) ≃-refl d aₗ₋₂ ⟩
                                                                                aₗ₋₁ - aₗ                  <⟨ +-monoʳ-< aₗ₋₁ { - aₗ} { - x} (neg-mono-< {x} {aₗ} x<aₗ) ⟩
                                                                                aₗ₋₁ - x                   ∎) ,
                                                                         (begin-strict
                                                                                aₗ₋₁ - x                   <⟨ +-monoʳ-< aₗ₋₁ { - x} { - aₗ₋₂} (neg-mono-< {aₗ₋₂} {x} aₗ₋₂<x) ⟩
                                                                                aₗ₋₁ - aₗ₋₂               ≈⟨ solve 2 (λ d a → (a ⊕ d) ⊖ a ⊜ d) ≃-refl d aₗ₋₂ ⟩
                                                                                d                          ∎))
