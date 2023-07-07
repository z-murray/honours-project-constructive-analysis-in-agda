-- Here Fin is used as an index type.
-- More has been done here (conversions etc.); still it's less used in the library because of the many inconveniences Fin brings.

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

import Data.Fin.Base as Fin
open import Data.Fin.Base using (Fin; fromℕ; fromℕ<; fromℕ≤; toℕ; inject₁)
import Data.Fin.Properties as FinP

open import ExtraProperties
open import Real
open import RealProperties

module FiniteSequences.Fin where

maxFin : {n-1 : ℕ} → (f : Fin (suc n-1) → ℝ) → ℝ
maxFin {zero} f    = f (fromℕ 0)
maxFin {suc n-1} f = maxFin (λ (x : Fin (suc n-1)) → f (inject₁ x)) ⊔ f (fromℕ (suc n-1))

maxFin≃f0⊔rest : {k : ℕ} (g : Fin (suc (suc k)) → ℝ) → maxFin g ≃ g Fin.zero ⊔ maxFin (λ x → g (Fin.suc x))
maxFin≃f0⊔rest {zero} g = ≃-refl
maxFin≃f0⊔rest {suc k} g = begin
    maxFin (λ x → g (inject₁ (inject₁ x))) ⊔
      g (Fin.suc (inject₁ (fromℕ k)))
      ⊔ g (Fin.suc (Fin.suc (fromℕ k)))          ≈⟨ ⊔-congʳ {g (Fin.suc (Fin.suc (fromℕ k)))} (maxFin≃f0⊔rest (λ x → g (inject₁ x))) ⟩
    g Fin.zero ⊔
      maxFin (λ x → g (Fin.suc (inject₁ x))) ⊔
       g (Fin.suc (Fin.suc (fromℕ k)))           ≈⟨ ⊔-assoc (g Fin.zero) (maxFin (λ x → g (Fin.suc (inject₁ x)))) (g (Fin.suc (Fin.suc (fromℕ k)))) ⟩
    g Fin.zero ⊔
      (maxFin (λ x → g (Fin.suc (inject₁ x))) ⊔
       g (Fin.suc (Fin.suc (fromℕ k))))          ∎
  where open ≃-Reasoning

m≤n⇒fm≤maxFinf : {m n : ℕ} (f : Fin (suc n) → ℝ) → (m<sucn : m ℕ.< (suc n)) → f (fromℕ< m<sucn) ≤ maxFin f  
m≤n⇒fm≤maxFinf {zero} {zero} f m<sucn = ≤-refl
m≤n⇒fm≤maxFinf {zero} {suc n} f m<sucn = ≤-trans (m≤n⇒fm≤maxFinf (λ x → f (inject₁ x)) (ℕ.s≤s ℕ.z≤n)) (x≤x⊔y _ _)
m≤n⇒fm≤maxFinf {suc zero} {zero} f (ℕ.s≤s ())
m≤n⇒fm≤maxFinf {suc m} {suc n} f (ℕ.s≤s m<sucn) = begin
           f (Fin.suc (fromℕ< m<sucn))             ≤⟨ m≤n⇒fm≤maxFinf (λ x → f (Fin.suc x)) m<sucn ⟩
           maxFin (λ x → f (Fin.suc x))                 ≤⟨ x≤y⊔x (maxFin (λ x → f (Fin.suc x))) (f Fin.zero)  ⟩
           f Fin.zero ⊔ maxFin (λ x → f (Fin.suc x))    ≈⟨ ≃-symm (maxFin≃f0⊔rest f) ⟩
           maxFin f                                      ∎
  where open ≤-Reasoning

mFinsn⇒fm≤maxFinf : {n : ℕ} (f : Fin (suc n) → ℝ) (m : Fin (suc n)) → f m ≤ maxFin f
mFinsn⇒fm≤maxFinf {zero} f Fin.zero = ≤-refl
mFinsn⇒fm≤maxFinf {suc n} f m = begin
    f m                                   ≈⟨ ≃-refl₂ (cong f (sym (FinP.fromℕ<-toℕ m (FinP.toℕ<n m)))) ⟩
    f (fromℕ< {toℕ m} (FinP.toℕ<n m))    ≤⟨ m≤n⇒fm≤maxFinf {toℕ m} {suc n} f (FinP.toℕ<n m) ⟩
    maxFin f                 ∎
  where open ≤-Reasoning

finTrunc : ∀ {i} {A : Set i} {n : ℕ} → (Fin (suc n) → A) → (Fin n → A)
finTrunc f i = f (inject₁ i)

toℕseq : ∀ {i} {A : Set i} {n : ℕ} (f : Fin n → A) (def : A) → (ℕ → A)
toℕseq {n = zero}  f def k = def
toℕseq {n = suc n} f def zero = f Fin.zero
toℕseq {n = suc n} f def (suc k) = toℕseq {n = n} (λ j → f (Fin.suc j)) def k
{-with k ℕP.≤? n
...          | Bool.true  because ofʸ  k≤n = f (fromℕ< {k} (ℕ.s≤s k≤n))
...          | Bool.false because ofⁿ k≮n = def-}

toℕseqEq : ∀ {i} {A : Set i} {n : ℕ} (f : Fin n → A) → {k : ℕ} → (k<n : k ℕ.< n) → (def : A) → toℕseq {n = n} f def k ≡ f (fromℕ< k<n)
toℕseqEq {n = zero} f {k} () def
toℕseqEq {n = suc n} f {zero} k<sucn def = refl
toℕseqEq {n = suc n} f {suc k} k<sucn def = toℕseqEq {n = n} (λ j → f (Fin.suc j)) {k} (ℕ.≤-pred k<sucn) def
{-with k ℕP.≤? n
...          | Bool.true  because ofʸ  k≤n = cong (λ p → f (fromℕ< p)) (ℕP.≤-irrelevant (ℕ.s≤s k≤n) k<sucn) 
...          | Bool.false because ofⁿ k≮n = ⊥-elim (k≮n (ℕ.≤-pred k<sucn))-}

toℕseqEqDef : ∀ {i} {A : Set i} {n : ℕ} (f : Fin n → A) → {k : ℕ} → (k<n : k ℕ.≥ n) → (def : A) → toℕseq {n = n} f def k ≡ def
toℕseqEqDef {n = zero} _ {_} _ _ = refl
toℕseqEqDef {n = suc n} f {suc k} sk≥sn def = toℕseqEqDef (λ j → f (Fin.suc j)) {k} (ℕ.≤-pred sk≥sn) def

-- for steppings:
toℕseqInjectEq : ∀ {i} {A : Set i} {m n : ℕ} → (a : Fin (suc n) → A) →  m ℕ.< n → (defAft : A) → toℕseq {n = n} (λ i₁ → a (inject₁ i₁)) defAft m ≡ toℕseq a defAft m
toℕseqInjectEq {m = zero} {n = suc n} a m<n defAft = refl
toℕseqInjectEq {m = suc m} {n = suc n} a m<n defAft = toℕseqInjectEq (λ j → a (Fin.suc j)) (ℕP.≤-pred m<n) defAft

--here n<sucn is provided in order for it to work for any proof
fromℕ-fromℕ< : ∀ (n : ℕ) → fromℕ n ≡ fromℕ< {n} (ℕP.n<1+n n)
fromℕ-fromℕ< zero = refl
fromℕ-fromℕ< (suc n) = cong Fin.suc (fromℕ-fromℕ< n)

ℕize : ∀ {i j} {A : Set i} {B : Set j} {n : ℕ} → ((Fin n → B) → A) → ((ℕ → B) → A)
ℕize {n = n} f a = f (λ i → a (toℕ i))

foldlSeq : ∀ {i j} {A : Set i} {B : Set j} → (A → B → A) → A → (ℕ → B) → ℕ → A
foldlSeq op def f zero = def
foldlSeq op def f (suc n) = op (foldlSeq op def f n) (f n)

foldlFin : ∀ {i j} {A : Set i} {B : Set j} {n : ℕ} → (A → B → A) → A → (Fin n → B) → A
foldlFin {n = zero} op def a = def
foldlFin {n = suc n} op def a = op (foldlFin {n = n} op def (λ i → a (inject₁ i))) (a (fromℕ n))

foldlFinSeqEq : ∀ {i j} {A : Set i} {B : Set j} {n : ℕ} (op : A → B → A) (def : A) (a : Fin n → B) (defAft : B) →
          foldlFin op def a ≡ foldlSeq op def (toℕseq a defAft) n
foldlFinSeqEq {n = zero} op def a _ = refl
foldlFinSeqEq {n = suc n} op def a defAft = trans (cong (λ x → op x (a (fromℕ n))) (trans (foldlFinSeqEq op def (λ i₁ → a (inject₁ i₁)) defAft) (lem₁ n ℕP.≤-refl)))
                                                (cong (λ x → op (foldlSeq op def (λ k → toℕseq a defAft k) n) x)
                                                 (trans (cong a (fromℕ-fromℕ< n)) (sym (toℕseqEq a (ℕP.n<1+n n) defAft))))
  where
  lem₁ : ∀ (m : ℕ) → m ℕ.≤ n → foldlSeq op def (toℕseq (λ i₁ → a (inject₁ i₁)) defAft) m ≡ foldlSeq op def (λ k → toℕseq a defAft k) m
  lem₁ zero    _ = refl
  lem₁ (suc m) sucm≤n = trans (cong (λ x → op (foldlSeq op def (toℕseq (λ i₁ → a (inject₁ i₁)) defAft) m) x) (toℕseqInjectEq a sucm≤n defAft))
                            (cong (λ x → op x (toℕseq a defAft m)) (lem₁ m
                                                                    (ℕP.≤-trans (ℕP.n≤1+n m) sucm≤n)))

--to ExtraProperties?
ℚx⊔x≃x : ∀ (x : ℚᵘ) → x ℚ.⊔ x ≡ x
ℚx⊔x≃x x with x ℚ.≤ᵇ x
ℚx⊔x≃x x | Bool.true = refl
ℚx⊔x≃x x | Bool.false = refl

--to RealProperties?
x⊔x≃x : ∀ (x : ℝ) → x ⊔ x ≃ x
x⊔x≃x x = *≃* λ {(suc n) → begin
      ℚ.∣ seq x (suc n) ℚ.⊔ seq x (suc n) ℚ.- seq x (suc n) ∣   ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- seq x (suc n)) (ℚP.≃-reflexive (ℚx⊔x≃x (seq x (suc n))))) ⟩
      ℚ.∣ seq x (suc n) ℚ.- seq x (suc n) ∣                      ≈⟨ ℚP.∣-∣-cong (ℚP.p≃q⇒p-q≃0 (seq x (suc n)) (seq x (suc n)) ℚP.≃-refl) ⟩
      0ℚᵘ                                                       ≤⟨ ℚ.*≤* (ℤ.+≤+ ℕ.z≤n) ⟩
      + 2 / (suc n)                                            ∎}
  where
  open ℚP.≤-Reasoning

max≃foldl⊔ : ∀ (f : ℕ → ℝ) (n : ℕ) → max f n ≃ foldlSeq _⊔_ (f zero) f (suc n)
max≃foldl⊔ f zero = ≃-symm (x⊔x≃x (f 0))
max≃foldl⊔ f (suc n) = ⊔-congʳ {f (suc n)} (max≃foldl⊔ f n)

maxFin≃foldl⊔ : ∀ {n : ℕ} (f : Fin (suc n) → ℝ) → maxFin f ≃ foldlFin _⊔_ (f Fin.zero) f
maxFin≃foldl⊔ {zero} f = ≃-symm (x⊔x≃x (f Fin.zero))
maxFin≃foldl⊔ {suc n} f = ⊔-congʳ {f (Fin.suc (fromℕ n))} (maxFin≃foldl⊔ (λ x → f (inject₁ x)))

minFin : {n : ℕ} → (Fin (suc n) → ℝ) → ℝ
minFin f = foldlFin _⊓_ (f Fin.zero) f

toℕseqmax : ∀ {n : ℕ} (f : Fin (suc n) → ℝ) (defAft : ℝ) → max (toℕseq {n = suc n} f defAft) n ≃ maxFin f
toℕseqmax {n} f defAft = begin
        max (toℕseq {n = suc n} f defAft) n    ≈⟨ max≃foldl⊔ (toℕseq {n = suc n} f defAft) n ⟩
        foldlSeq _⊔_ (f Fin.zero) (toℕseq {n = suc n} f defAft) (suc n)  ≈⟨ ≃-refl₂ (sym (foldlFinSeqEq _⊔_ (f Fin.zero) f defAft)) ⟩
        foldlFin _⊔_ (f Fin.zero) f                                                 ≈⟨ ≃-symm (maxFin≃foldl⊔ f) ⟩
        maxFin f ∎
  where open ≃-Reasoning
{-
this also proved _≡_, but used old definition of toℕseq and was _very_ dirty
toℕseqmax {zero} f = refl
toℕseqmax {suc n} f = trans (cong (max (toℕseq f (f Fin.zero - 1ℝ)) n ⊔_) part₁) (cong (_⊔ f (Fin.suc (fromℕ n))) part₂)
  where
  part₁ : toℕseq f (f Fin.zero - 1ℝ) (suc n) ≡ f (Fin.suc (fromℕ n))
  part₁ = trans (toℕseqEq f ℕP.≤-refl (f Fin.zero - 1ℝ)) (cong (λ x → f (Fin.suc x)) (sym (fromℕ-fromℕ< n)))
  part₂ : max (toℕseq f (f Fin.zero - 1ℝ)) n ≡ maxFin (λ x → f (inject₁ x))
  part₂ = trans (lem (ℕP.≤-refl {suc n})) (toℕseqmax (λ x → f (inject₁ x)))
    where
    lem : ∀ {k : ℕ} (k<sucn : k ℕ.< suc n) → max (toℕseq f (f Fin.zero - 1ℝ)) k ≡ max (toℕseq (λ x → f (inject₁ x)) (f Fin.zero - 1ℝ)) k
    lem {zero} k<sucn = refl
    lem {suc k-1} k<sucn = trans (cong (_⊔ toℕseq f (f Fin.zero - 1ℝ) (suc k-1)) (lem {k-1} {!!})) (cong (max (toℕseq (λ x → f (inject₁ x)) (f Fin.zero - 1ℝ)) k-1 ⊔_) lem₂)
      where
      lem₂ : toℕseq f (f Fin.zero - 1ℝ) (suc k-1) ≡ toℕseq (λ x → f (inject₁ x)) (f Fin.zero - 1ℝ) (suc k-1)
      lem₂ = {!toℕseqInjectEq!} {-with (suc k-1) ℕP.≤? n               | k-1 ℕP.<? (suc n)
      ...          | Bool.true  because ofʸ  k≤n | Bool.true  because ofʸ  k≤sucn = cong (λ i → f (Fin.suc i)) {!yetAnotherLem k n!}
      ...          | Bool.true  because ofʸ  k≤n | Bool.false because ofⁿ  k≮sucn = ⊥-elim (k≮sucn (≤-step k≤n))
      ...          | Bool.false because ofⁿ k≮n |  _                             = ⊥-elim (k≮n (ℕ.≤-pred k<sucn))-}
-}

maxFinSelect : ∀ {n : ℕ} (f : Fin (suc n) → ℝ) (ε : ℝ) → ε > 0ℝ → ∃ (λ i → maxFin f - ε < f i)
maxFinSelect {n} f ε ε>0 = iFin , (begin-strict
          maxFin f - ε       ≈⟨ lem ⟩
          max fℕ n - ε       <⟨ proj₂ other ⟩
          fℕ i              ≈⟨ ≃-refl₂ (toℕseqEq f i<sucn def) ⟩
          f iFin            ∎)
  where
  open ≤-Reasoning
  def : ℝ
  def = maxFin f - ε - ε
  fℕ : ℕ → ℝ
  fℕ = toℕseq {n = suc n} f def
  lem : maxFin f - ε ≃ max fℕ n - ε
  lem = +-congˡ (- ε) (≃-symm (toℕseqmax {n} f def))
  other : ∃ (λ i → max fℕ n - ε < fℕ i)
  other = maxSelect fℕ n ε ε>0
  i : ℕ
  i = proj₁ other
  i<sucn : i ℕ.< suc n
  i<sucn = ℕP.≰⇒> (λ sucn≤i → <⇒≱ (proj₂ other) (begin
     toℕseq f def i             ≈⟨ ≃-refl₂ (toℕseqEqDef f sucn≤i def) ⟩
     maxFin f - ε - ε {-def-}   ≤⟨ <⇒≤ (0<ε⇒x-ε<x (maxFin f - ε) ε>0) ⟩
     maxFin f - ε               ≈⟨ lem ⟩
     max fℕ n - ε               ∎))
     where open ≤-Reasoning
  iFin : Fin (suc n)
  iFin = fromℕ< {i} i<sucn

-- minFinSelect : ∀ {n : ℕ} (f : Fin (suc n) → ℝ) (ε : ℝ) → ε > 0ℝ → ∃ (λ i → minFin f + ε > f i)
-- minFinSelect = {!!}

{-
-- A Fin version of fullPartition.
fullPartition : (D : CompactInterval) (n : ℕ) {n≢0 : n ≢0} → (Fin (suc n) → D ↓)
fullPartition D (suc n-1) i = fullPartitionℕ D (suc n-1) {tt} {toℕ i} (FinP.toℕ<n {suc (suc n-1)} i)
{-
fullPartition D (suc n-1) i = CIlower D + (+ (toℕ i) / n) ⋆ * (CIupper D - CIlower D) ,
                                                  0≤x⇒y≤y+x a (0≤x,y⇒0≤x*y (nonNegx⇒0≤x (nonNegp⇒nonNegp⋆ (+ (toℕ i) / n) tt)) d≥0) ,
                                                  (begin
                                                  a + (+ (toℕ i) / n) ⋆ * d     ≤⟨ +-monoʳ-≤ a (*-monoʳ-≤-nonNeg {(+ (toℕ i) / n) ⋆} {d} {(+ n / n) ⋆}
                                                                                               (p≤q⇒p⋆≤q⋆ (+ (toℕ i) / n) (+ n / n) (p≤q⇒p/r≤q/r (+ (toℕ i)) (+ n) n (ℤ.+≤+ (ℕ.≤-pred (FinP.toℕ<n i)))))
                                                                                               (0≤x⇒nonNegx d≥0)) ⟩
                                                  a + (+ n       / n) ⋆ * d     ≈⟨ +-congʳ a (*-congʳ {d} (⋆-cong (ℚ.*≡* (cong +[1+_] (trans (ℕP.*-identityʳ n-1) (sym (ℕP.+-identityʳ n-1))))))) ⟩
                                                  a +                1ℝ * d     ≈⟨ solve 2 (λ a b → a ⊕ Κ 1ℚᵘ ⊗ (b ⊖ a) ⊜ b) ≃-refl a b ⟩
                                                  b                             ∎)
  where
  open ≤-Reasoning
  n : ℕ
  n = suc n-1
  a b d : ℝ
  a = CIlower D ; b = CIupper D ; d = b - a

  d≥0 : d ≥ 0ℝ
  d≥0 = begin
     0ℝ     ≈⟨ solve 1 (λ a → Κ 0ℚᵘ ⊜ a ⊖ a) ≃-refl a ⟩
     a - a  ≤⟨ +-monoˡ-≤ (- a) (CIlower≤upper D) ⟩
     b - a  ∎
-}
-}
