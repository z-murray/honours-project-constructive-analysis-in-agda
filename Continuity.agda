-- Some definitions and results on continuity.

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
open import Data.Fin.Base using (Fin; fromℕ; fromℕ<; fromℕ≤; toℕ; inject₁)

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
open import Sequence
open ℝ-Solver

-- Syntax I like better for product type representations of subsets
-- Not a fan of the normal syntax and ∃ is pretty irrelevant for this usage
𝕊 : {A : Set} (P : Pred A 0ℓ) → Set
𝕊 {A} P = Σ A P

-- Should I be using this I wonder? Instead of stuff like (ε : ℝ) → ε > 0ℝ → ⋯
ℝ⁺ : Set
ℝ⁺ = 𝕊 (λ x → x > 0ℝ)

_isNonvoid : {A : Set} (P : Pred A 0ℓ) → Set
P isNonvoid = ∃ λ x → P x

_isBoundedAboveBy_ : Pred ℝ 0ℓ → Pred ℝ 0ℓ
P isBoundedAboveBy b = (x : 𝕊 P ) → proj₁ x ≤ b

_isBoundedAbove : Pred ℝ 0ℓ → Set
P isBoundedAbove = ∃ λ (b : ℝ) → P isBoundedAboveBy b 

_isBoundedBelowBy_ : Pred ℝ 0ℓ → Pred ℝ 0ℓ
P isBoundedBelowBy l = (x : 𝕊 P) → l ≤ proj₁ x

_isBoundedBelow : Pred ℝ 0ℓ → Set
P isBoundedBelow = ∃ λ l → P isBoundedBelowBy l

_isStrictlyBoundedAboveBy_ : Pred ℝ 0ℓ → Pred ℝ 0ℓ
P isStrictlyBoundedAboveBy b = (x : 𝕊 P) → proj₁ x < b

_isStrictlyBoundedAbove : Pred ℝ 0ℓ → Set
P isStrictlyBoundedAbove = ∃ λ b → P isStrictlyBoundedAboveBy b

_isStrictlyBoundedBelowBy_ : Pred ℝ 0ℓ → Pred ℝ 0ℓ
P isStrictlyBoundedBelowBy b = (x : 𝕊 P) → b < proj₁ x

_isStrictlyBoundedBelow : Pred ℝ 0ℓ → Set
P isStrictlyBoundedBelow = ∃ λ b → P isStrictlyBoundedBelowBy b

_hasSupremum_ : (P : Pred ℝ 0ℓ) (s : ℝ) → Set
P hasSupremum s = P isBoundedAboveBy s × ((ε : ℝ) → ε > 0ℝ → ∃ λ (x : 𝕊 P) → proj₁ x > s - ε)

_hasSupremum : Pred ℝ 0ℓ → Set
P hasSupremum = ∃ λ s → P hasSupremum s

_hasInfimum_ : (P : Pred ℝ 0ℓ) (l : ℝ) → Set
P hasInfimum l = P isBoundedBelowBy l × ((ε : ℝ) → ε > 0ℝ → ∃ λ (x : 𝕊 P) → proj₁ x < l + ε)

_hasInfimum : (P : Pred ℝ 0ℓ) → Set
P hasInfimum = ∃ λ l → P hasInfimum l

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

proposition-4-3-onlyif : {P : Pred ℝ 0ℓ} → P hasSupremum →
                         {x y : ℝ} → x < y → P isBoundedAboveBy y ⊎ ∃ λ a → P a × x < a
proposition-4-3-onlyif {P} (supP , P≤supP , supHyp) {x} {y} x<y = [ left , right ]′ (corollary-2-17 supP x y x<y)
  where
    open ≤-Reasoning
    left : supP < y → P isBoundedAboveBy y ⊎ ∃ λ a → P a × x < a
    left supP<y = inj₁ (λ A → let a = proj₁ A in begin
      a    ≤⟨ P≤supP A ⟩
      supP <⟨ supP<y ⟩
      y     ∎)

    right : supP > x → P isBoundedAboveBy y ⊎ ∃ λ a → P a × x < a
    right supP>x = let aget = supHyp (supP - x) (x<y⇒0<y-x x supP supP>x); a = proj₁ (proj₁ aget) in
                   inj₂ (a , proj₂ (proj₁ aget) , (begin-strict
      x                 ≈⟨ solve 2 (λ x supP → x ⊜ supP ⊖ (supP ⊖ x)) ≃-refl x supP ⟩
      supP - (supP - x) <⟨ proj₂ aget ⟩
      a                  ∎))

abstract
  fast-proposition-4-3-onlyif : {P : Pred ℝ 0ℓ} → P hasSupremum →
                                {x y : ℝ} → x < y → P isBoundedAboveBy y ⊎ ∃ λ a → P a × x < a
  fast-proposition-4-3-onlyif = proposition-4-3-onlyif
  

{-
Supremum of defined by:
For all ε > 0, there is a∈A such that a > supA - ε

∅ ⊂ P ⊆ ℝ
P is bounded above
The supremum of P exists if for every x < y in ℝ, P is bounded above by y or there is a∈P such that x < a.
 
·Construct (aₙ)∈P, increasing
(bₙ) upper bounds, decreasing

aₙ ≤ ℓ ≤ bₙ ⇒ ℓ upper bound

∀ε>0 ∃a∈P a > ℓ - ε

aₙ→ℓ
aₙ∈P

a∈P
b strict upper bound of P

(i)  aₙ ≤ aₙ₊₁ < bₙ₊₁ ≤ bₙ
(ii) bₙ₊₁ - aₙ₊₁ ≤ (3/4) * (bₙ - aₙ)

aₙ + (1/4)(bₙ - aₙ) < aₙ + (3/4)(bₙ - aₙ)


-}

proposition-4-3-if : {P : Pred ℝ 0ℓ} → P isNonvoid → P isBoundedAbove →
                     ({x y : ℝ} → x < y → P isBoundedAboveBy y ⊎ ∃ λ a → P a × x < a) →
                     P hasSupremum
proposition-4-3-if {P} (a , a∈P) (b-1 , P≤b-1) hyp = supP≃ℓ --supP≃ℓ
  where
    open ≤-Reasoning
    b = b-1 + 1ℝ
    
    a<b : a < b
    a<b = begin-strict
      a   ≤⟨ P≤b-1 (a , a∈P) ⟩
      b-1 <⟨ <-respˡ-≃ (+-identityʳ b-1) (+-monoʳ-< b-1
             (p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _))) ⟩
      b    ∎

    {-
    Want to construct sequences (aₙ),(bₙ) such that for n∈ℕ:
    (i)  aₙ ≤ aₙ₊₁ < bₙ₊₁ ≤ bₙ    and
    (ii) bₙ₊₁ - aₙ₊₁ ≤ ¾(bₙ - aₙ).
    
    We have ¼(bₙ - aₙ) < ¾(bₙ - aₙ). By our hypothesis, either
    ¾(bₙ - aₙ) is an upper bound of P or there exists a∈P such that aₙ + ¼(bₙ - aₙ) < a.

    In the first case, we set bₙ₊₁ = aₙ + ¾(bₙ - aₙ) and aₙ₊₁ = aₙ. 

    In the second case, we set aₙ₊₁ = a and bₙ₊₁ = bₙ. Then bₙ₊₁ ≤ bₙ trivially holds, and
    bₙ₊₁ - aₙ₊₁ = bₙ - a 
                < bₙ - (¼bₙ + ¾aₙ)
                = ¾(bₙ - aₙ),
    so bₙ₊₁ - aₙ₊₁ ≤ ¾(bₙ - aₙ). 

    We have
    aₙ₊₁ = a 
         > aₙ + ¼(bₙ - aₙ)
         ≥ aₙ              since aₙ < bₙ,
    so aₙ ≤ aₙ₊₁.
      
    
    a₁
    aₙ₊₁
    -}
    generator : (aₙ bₙ : ℝ) → aₙ < bₙ → P aₙ → P isStrictlyBoundedAboveBy bₙ →
                ∃ λ aₙ₊₁ → ∃ λ bₙ₊₁ → P aₙ₊₁ × (aₙ ≤ aₙ₊₁ < bₙ₊₁) × bₙ₊₁ ≤ bₙ ×
                                      (bₙ₊₁ - aₙ₊₁ ≤ (+ 3 / 4) ⋆ * (bₙ - aₙ)) ×
                                      P isStrictlyBoundedAboveBy bₙ₊₁
    generator aₙ bₙ aₙ<bₙ aₙ∈P P<bₙ = [ left , right ]′ (hyp (proj₁ helper)) --[ left , right ]′ (hyp (proj₁ helper)) --[ left , right ]′ (hyp helper)
      where
        aₙ+¾[bₙ-aₙ] = aₙ + (+ 3 / 4) ⋆ * (bₙ - aₙ)
        aₙ+¼[bₙ-aₙ] = aₙ + (+ 1 / 4) ⋆ * (bₙ - aₙ)
        

        {-
          aₙ + ¼(bₙ - aₙ) = ¼bₙ + ¾aₙ
                          < ½bₙ + ¾aₙ

        ½bₙ + ¾aₙ
        aₙ + ¾(bₙ - aₙ) = ¾bₙ + ¼aₙ
                        
        aₙ + ¼(bₙ - aₙ) < aₙ + ¾(bₙ - aₙ)

        aₙ + ½(bₙ - aₙ) = ½bₙ + ½aₙ

        We really need bₙ to be a strict upper bound, which is easy
      aₙ + ¼(bₙ - aⱼn) < (2/4)bₙ + 2/4aₙ < aₙ + 3/4(bₙ - aₙ)

      WTS aₙ + (1/4)(bₙ - aₙ) < (2/4)bₙ + (2/4)aₙ < aₙ + (3/4)(bₙ - aₙ)
      aₙ + (1/4)bₙ - (1/4)aₙ = (1/4)bₙ + (3/4)aₙ
                          
        
        -}
        helper : (aₙ + (+ 1 / 4) ⋆ * (bₙ - aₙ)) < ((+ 2 / 4) ⋆ * bₙ + (+ 2 / 4) ⋆ * aₙ) < (aₙ + (+ 3 / 4) ⋆ * (bₙ - aₙ))
        helper = <-respʳ-≃ helperLem (+-monoʳ-< aₙ (*-monoˡ-<-pos aₙ<bₙ (p<q⇒p⋆<q⋆ (+ 1 / 4) (+ 2 / 4) (p<q⇒p/r<q/r (+ 1) (+ 2) 4 (ℤ.+<+ ℕP.≤-refl))))) ,
                 <-respˡ-≃ helperLem (+-monoʳ-< aₙ (*-monoˡ-<-pos aₙ<bₙ (p<q⇒p⋆<q⋆ (+ 2 / 4) (+ 3 / 4) (p<q⇒p/r<q/r (+ 2) (+ 3) 4 (ℤ.+<+ ℕP.≤-refl)))))
        --<-respʳ-≃ helperLem (+-monoʳ-< aₙ (*-monoˡ-<-pos aₙ<bₙ (0<y-x⇒x<y ((+ 1 / 4) ⋆) ((+ 2 / 4) ⋆) (<-respʳ-≃ {!!} {!!})))) , {!!}
          where
            helperLem : aₙ + (+ 2 / 4) ⋆ * (bₙ - aₙ) ≃ (+ 2 / 4) ⋆ * bₙ + (+ 2 / 4) ⋆ * aₙ
            helperLem = begin-equality
              aₙ + (+ 2 / 4) ⋆ * (bₙ - aₙ)                  ≈⟨ solve 2 (λ aₙ bₙ →
                                                               aₙ ⊕ Κ (+ 2 / 4) ⊗ (bₙ ⊖ aₙ) ⊜
                                                               Κ (+ 2 / 4) ⊗ bₙ ⊕ Κ (1ℚᵘ ℚ.- (+ 2 / 4)) ⊗ aₙ)
                                                               ≃-refl aₙ bₙ ⟩
              (+ 2 / 4) ⋆ * bₙ + (1ℚᵘ ℚ.- (+ 2 / 4)) ⋆ * aₙ ≈⟨ ≃-refl ⟩
              (+ 2 / 4) ⋆ * bₙ + (+ 2 / 4) ⋆ * aₙ            ∎

        {-
          Suppose P is strictly bounded above by aₙ + ¾(bₙ - aₙ). Set aₙ₊₁ = aₙ and bₙ₊₁ = aₙ + ¾(bₙ - aₙ). Then:
          
          aₙ ≤ aₙ₊₁ trivially holds

          aₙ₊₁ = aₙ < aₙ + ¾(bₙ - aₙ) = bₙ₊₁ holds since bₙ > aₙ

          bₙ₊₁ = ¾bₙ + ¼aₙ
               ≤ ¾bₙ + ¼bₙ = bₙ,
          so bₙ₊₁ ≤ bₙ.

          bₙ₊₁ - aₙ₊₁ = aₙ + ¾(bₙ - aₙ) - aₙ
                      = ¾(bₙ - aₙ),
          so bₙ₊₁ - aₙ₊₁ ≥ ¾(bₙ - aₙ).
        -}
        left : P isBoundedAboveBy ((+ 2 / 4) ⋆ * bₙ + (+ 2 / 4) ⋆ * aₙ) →
               ∃ λ aₙ₊₁ → ∃ λ bₙ₊₁ → P aₙ₊₁ × (aₙ ≤ aₙ₊₁ < bₙ₊₁) ×
                                     bₙ₊₁ ≤ bₙ × (bₙ₊₁ - aₙ₊₁ ≤ (+ 3 / 4) ⋆ * (bₙ - aₙ)) ×
                                     P isStrictlyBoundedAboveBy bₙ₊₁
        left hyp2 = aₙ , aₙ + (+ 3 / 4) ⋆ * (bₙ - aₙ) , aₙ∈P , (≤-refl , lemA) , lemB , lemC , lemD
          where
            lemA : aₙ < aₙ + (+ 3 / 4) ⋆ * (bₙ - aₙ)
            lemA = begin-strict
              aₙ                           ≈⟨ solve 1 (λ aₙ → aₙ ⊜ aₙ ⊕ Κ (+ 3 / 4) ⊗ Κ 0ℚᵘ) ≃-refl aₙ ⟩
              aₙ + (+ 3 / 4) ⋆ * 0ℝ        <⟨ +-monoʳ-< aₙ (*-monoʳ-<-pos (posp⇒posp⋆ (+ 3 / 4) _) (x<y⇒0<y-x aₙ bₙ aₙ<bₙ)) ⟩
              aₙ + (+ 3 / 4) ⋆ * (bₙ - aₙ)  ∎

            lemB : aₙ + (+ 3 / 4) ⋆ * (bₙ - aₙ) ≤ bₙ
            lemB = begin
              aₙ + (+ 3 / 4) ⋆ * (bₙ - aₙ)        ≈⟨ solve 2 (λ aₙ bₙ →
                                                     aₙ ⊕ Κ (+ 3 / 4) ⊗ (bₙ ⊖ aₙ) ⊜
                                                     Κ (+ 3 / 4) ⊗ bₙ ⊕ Κ (1ℚᵘ ℚ.- (+ 3 / 4)) ⊗ aₙ)
                                                     ≃-refl aₙ bₙ ⟩
              (+ 3 / 4) ⋆ * bₙ + (+ 1 / 4) ⋆ * aₙ ≤⟨ +-monoʳ-≤ ((+ 3 / 4) ⋆ * bₙ) (*-monoˡ-≤-nonNeg (<⇒≤ aₙ<bₙ) (nonNegp⇒nonNegp⋆ (+ 1 / 4) _)) ⟩
              (+ 3 / 4) ⋆ * bₙ + (+ 1 / 4) ⋆ * bₙ ≈⟨ ≃-trans (≃-trans
                                                     (solve 1 (λ bₙ → Κ (+ 3 / 4) ⊗ bₙ ⊕ Κ (+ 1 / 4) ⊗ bₙ ⊜ Κ (+ 16 / 16) ⊗ bₙ) ≃-refl bₙ)
                                                     (*-congʳ (⋆-cong (ℚ.*≡* refl)))) (*-identityˡ bₙ) ⟩
              bₙ                                   ∎

            lemC : aₙ + (+ 3 / 4) ⋆ * (bₙ - aₙ) - aₙ ≤ (+ 3 / 4) ⋆ * (bₙ - aₙ)
            lemC = ≤-reflexive (solve 2 (λ aₙ bₙ → aₙ ⊕ Κ (+ 3 / 4) ⊗ (bₙ ⊖ aₙ) ⊖ aₙ ⊜ Κ (+ 3 / 4) ⊗ (bₙ ⊖ aₙ)) ≃-refl aₙ bₙ)

            -- removed x∈P arg
            lemD : P isStrictlyBoundedAboveBy (aₙ + (+ 3 / 4) ⋆ * (bₙ - aₙ))
            lemD (x , x∈P) = begin-strict
              x                                   ≤⟨ hyp2 (x , x∈P) ⟩
              (+ 2 / 4) ⋆ * bₙ + (+ 2 / 4) ⋆ * aₙ <⟨ proj₂ helper ⟩
              aₙ + (+ 3 / 4) ⋆ * (bₙ - aₙ)         ∎ 

        right : (∃ λ z → P z × (aₙ + (+ 1 / 4) ⋆ * (bₙ - aₙ)) < z) →
                ∃ λ aₙ₊₁ → ∃ λ bₙ₊₁ → P aₙ₊₁ × (aₙ ≤ aₙ₊₁ < bₙ₊₁) × bₙ₊₁ ≤ bₙ ×
                                      (bₙ₊₁ - aₙ₊₁ ≤ (+ 3 / 4) ⋆ * (bₙ - aₙ)) ×
                                      P isStrictlyBoundedAboveBy bₙ₊₁
        right (z , hyp2a , hyp2b) = z , bₙ , hyp2a , (lemA , P<bₙ (z , hyp2a)) , ≤-refl , lemB , P<bₙ
          where
            lemA : z ≥ aₙ
            lemA = begin
              aₙ                           ≈⟨ solve 1 (λ aₙ → aₙ ⊜ aₙ ⊕ Κ (+ 1 / 4) ⊗ (aₙ ⊖ aₙ)) ≃-refl aₙ ⟩
              aₙ + (+ 1 / 4) ⋆ * (aₙ - aₙ) ≤⟨ +-monoʳ-≤ aₙ (*-monoˡ-≤-nonNeg (+-monoˡ-≤ (- aₙ) (<⇒≤ aₙ<bₙ)) (nonNegp⇒nonNegp⋆ (+ 1 / 4) _)) ⟩
              aₙ + (+ 1 / 4) ⋆ * (bₙ - aₙ) <⟨ hyp2b ⟩
              z                             ∎

            lemB : bₙ - z ≤ (+ 3 / 4) ⋆ * (bₙ - aₙ)
            lemB = begin
              bₙ - z                                                <⟨ +-monoʳ-< bₙ (neg-mono-< hyp2b) ⟩
              bₙ - (aₙ + (+ 1 / 4) ⋆ * (bₙ - aₙ))                   ≈⟨ solve 2 (λ aₙ bₙ →
                                                                       bₙ ⊖ (aₙ ⊕ Κ (+ 1 / 4) ⊗ (bₙ ⊖ aₙ)) ⊜
                                                                       Κ (1ℚᵘ ℚ.- (+ 1 / 4)) ⊗ bₙ ⊖ Κ (1ℚᵘ ℚ.- (+ 1 / 4)) ⊗ aₙ) ≃-refl aₙ bₙ ⟩
              (1ℚᵘ ℚ.- (+ 1 / 4)) ⋆ * bₙ - (1ℚᵘ ℚ.- (+ 1 / 4)) ⋆ * aₙ ≈⟨ +-cong (*-congʳ ≃-refl) (-‿cong (*-congʳ ≃-refl)) ⟩
              (+ 3 / 4) ⋆ * bₙ - (+ 3 / 4) ⋆ * aₙ                     ≈⟨ solve 3 (λ a b c → a ⊗ b ⊖ a ⊗ c ⊜ a ⊗ (b ⊖ c)) ≃-refl
                                                                         ((+ 3 / 4) ⋆) bₙ aₙ ⟩
              (+ 3 / 4) ⋆ * (bₙ - aₙ)                                  ∎


    as : ℕ → ℝ
    bs : ℕ → ℝ
    aₙ<bₙ : (n : ℕ) → as n < bs n
    aₙ∈P : (n : ℕ) → P (as n)
    aₙ≤aₙ₊₁ : as isIncreasing
    bₙ₊₁≤bₙ : bs isDecreasing
    bₙ₊₁-aₙ₊₁≤[3/4][bₙ-aₙ] : (n : ℕ) → bs (suc n) - as (suc n) ≤ (+ 3 / 4) ⋆ * (bs n - as n)
    P<bₙ : (n : ℕ) → P isStrictlyBoundedAboveBy bs n

    gen-get : (n : ℕ) → _
    gen-get n = generator (as n) (bs n) (aₙ<bₙ n) (aₙ∈P n) (P<bₙ n)

    as zero    = a
    as (suc n) = proj₁ (gen-get n)

    bs zero    = b
    bs (suc n) = proj₁ (proj₂ (gen-get n))

    aₙ<bₙ zero    = a<b
    aₙ<bₙ (suc n) = proj₂ (proj₁ (proj₂ (proj₂ (proj₂ (gen-get n))))) 

    aₙ∈P zero    = a∈P
    aₙ∈P (suc n) = proj₁ (proj₂ (proj₂ (gen-get n)))

    aₙ≤aₙ₊₁ n = proj₁ (proj₁ (proj₂ (proj₂ (proj₂ (gen-get n)))))

    bₙ₊₁≤bₙ n = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (gen-get n)))))

    bₙ₊₁-aₙ₊₁≤[3/4][bₙ-aₙ] n = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (gen-get n))))))

    -- removed x∈P arg
    P<bₙ zero (x , x∈P) = begin-strict
      x   ≤⟨ P≤b-1 (x , x∈P) ⟩
      b-1 <⟨ <-respˡ-≃ (+-identityʳ b-1) (+-monoʳ-< b-1 (p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _))) ⟩
      b    ∎
    P<bₙ (suc n)    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (gen-get n)))))) 

    lem : (n : ℕ) → {n≢0 : n ≢0} → bs n - as n ≤ (pow ((+ 3 / 4) ⋆) (ℕ.pred n) * (b - a))
    lem (suc zero)    = begin
      bs 1 - as 1 ≤⟨ +-mono-≤ (bₙ₊₁≤bₙ 0) (neg-mono-≤ (aₙ≤aₙ₊₁ 0)) ⟩
      b - a       ≈⟨ ≃-symm (*-identityˡ (b - a)) ⟩
      1ℝ * (b - a) ∎
    lem (suc (suc n)) = begin
      bs (suc (suc n)) - as (suc (suc n))           ≤⟨ bₙ₊₁-aₙ₊₁≤[3/4][bₙ-aₙ] (suc n) ⟩
      (+ 3 / 4) ⋆ * (bs (suc n) - as (suc n))       ≤⟨ *-monoˡ-≤-nonNeg {bs (suc n) - as (suc n)} {(+ 3 / 4) ⋆}
                                                       {pow ((+ 3 / 4) ⋆) n * (b - a)}
                                                       (lem (suc n)) (0≤x⇒nonNegx (p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 3 / 4) (ℚP.nonNegative⁻¹ _))) ⟩
      (+ 3 / 4) ⋆ * (pow ((+ 3 / 4) ⋆) n * (b - a)) ≈⟨ solve 3 (λ a b c → a ⊗ (b ⊗ c) ⊜ b ⊗ a ⊗ c)
                                                       ≃-refl ((+ 3 / 4) ⋆) (pow ((+ 3 / 4) ⋆) n) (b - a) ⟩
      pow ((+ 3 / 4) ⋆) (suc n) * (b - a)    ∎

    zs : ℕ → ℝ
    zs 0       = b - a
    zs (suc n) = pow ((+ 3 / 4) ⋆) n * (b - a)

    bₙ-aₙ≤zₙ : (n : ℕ) → bs n - as n ≤ zs n
    bₙ-aₙ≤zₙ zero    = ≤-refl
    bₙ-aₙ≤zₙ (suc zero)    = begin
      bs 1 - as 1 ≤⟨ +-mono-≤ (bₙ₊₁≤bₙ 0) (neg-mono-≤ (aₙ≤aₙ₊₁ 0)) ⟩
      b - a       ≈⟨ ≃-symm (*-identityˡ (b - a)) ⟩
      1ℝ * (b - a) ∎
    bₙ-aₙ≤zₙ (suc (suc n)) = begin
      bs (suc (suc n)) - as (suc (suc n))           ≤⟨ bₙ₊₁-aₙ₊₁≤[3/4][bₙ-aₙ] (suc n) ⟩
      (+ 3 / 4) ⋆ * (bs (suc n) - as (suc n))       ≤⟨ *-monoˡ-≤-nonNeg {bs (suc n) - as (suc n)} {(+ 3 / 4) ⋆}
                                                       {pow ((+ 3 / 4) ⋆) n * (b - a)}
                                                       (bₙ-aₙ≤zₙ (suc n)) (0≤x⇒nonNegx (p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 3 / 4) (ℚP.nonNegative⁻¹ _))) ⟩
      (+ 3 / 4) ⋆ * (pow ((+ 3 / 4) ⋆) n * (b - a)) ≈⟨ solve 3 (λ a b c → a ⊗ (b ⊗ c) ⊜ b ⊗ a ⊗ c)
                                                       ≃-refl ((+ 3 / 4) ⋆) (pow ((+ 3 / 4) ⋆) n) (b - a) ⟩
      pow ((+ 3 / 4) ⋆) (suc n) * (b - a)    ∎

    zₙ₊₁→0 : (λ n → zs (suc n)) ConvergesTo 0ℝ
    zₙ₊₁→0 = xₙ→x∧x≃y⇒xₙ→y (xₙyₙ→x₀y₀ (0ℝ , ∣r∣<1⇒rⁿ→0 (begin-strict
      (∣ (+ 3 / 4) ⋆ ∣ ≈⟨ 0≤x⇒∣x∣≃x (p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 3 / 4) (ℚP.nonNegative⁻¹ _)) ⟩
      (+ 3 / 4) ⋆     <⟨ p<q⇒p⋆<q⋆ (+ 3 / 4) 1ℚᵘ (0<q-p⇒p<q (+ 3 / 4) 1ℚᵘ (ℚP.positive⁻¹ _)) ⟩
      1ℝ               ∎))) (b - a , xₙ≃c⇒xₙ→c (λ n → ≃-refl))) (*-zeroˡ (b - a))

    zₙ→0 : zs ConvergesTo 0ℝ
    zₙ→0 = con* λ {(suc k-1) → let k = suc k-1; N-get = fast-convergence-getter (0ℝ , zₙ₊₁→0) k; N = suc (proj₁ N-get) in
           N , λ {(suc n-1) (ℕ.s≤s n-1≥N) → proj₂ N-get n-1 n-1≥N}}

    bₙ-aₙ→0 : (λ n → bs n - as n) ConvergesTo 0ℝ
    bₙ-aₙ→0 = con* (λ {(suc k-1) → let k = suc k-1; N-get = fast-convergence-getter (0ℝ , zₙ→0) k; N = suc (proj₁ N-get) in
              ℕ.pred N , λ n n≥N → begin
      ∣ bs n - as n - 0ℝ ∣ ≈⟨ ≃-trans (∣-∣-cong (solve 2 (λ aₙ bₙ → bₙ ⊖ aₙ ⊖ Κ 0ℚᵘ ⊜ bₙ ⊖ aₙ) ≃-refl (as n) (bs n)))
                             (0≤x⇒∣x∣≃x (x≤y⇒0≤y-x (<⇒≤ (aₙ<bₙ n)))) ⟩
      bs n - as n         ≤⟨ bₙ-aₙ≤zₙ n ⟩
      zs n                ≤⟨ ≤-trans x≤∣x∣ (≤-respˡ-≃ (∣-∣-cong (solve 1 (λ zₙ → zₙ ⊖ Κ 0ℚᵘ ⊜ zₙ) ≃-refl (zs n)))
                             (proj₂ N-get n n≥N)) ⟩
      (+ 1 / k) ⋆          ∎})

    aₙ,bₙ→ℓ : ∃ λ (aₙ→ℓ : as isConvergent) → ∃ λ (bₙ→ℓ : bs isConvergent) → lim aₙ→ℓ ≃ lim bₙ→ℓ × ((n : ℕ) → as n ≤ lim aₙ→ℓ ≤ bs n)
    aₙ,bₙ→ℓ = fast-common-limit-lemma (λ n → <⇒≤ (aₙ<bₙ n))
              (xₙ→x∧x≃y⇒xₙ→y (xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ n {n≢0} → neg-involutive (as n - bs n))
              (- 0ℝ , -xₙ→-x₀ (0ℝ , xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ n {n≢0} → solve 2 (λ aₙ bₙ → bₙ ⊖ aₙ ⊜ (⊝ (aₙ ⊖ bₙ))) ≃-refl (as n) (bs n)) (0ℝ , bₙ-aₙ→0))))
              (≃-symm 0≃-0)) aₙ≤aₙ₊₁ bₙ₊₁≤bₙ

    ℓ : ℝ
    ℓ = proj₁ (proj₁ aₙ,bₙ→ℓ)

  {-
    To show that ℓ = supP, we need to show that ℓ is an upper bound of P and that, for each ε > 0, there exists a∈P such that a > ℓ - ε.
    
    Since bₙ→ℓ and each bₙ is an upper bound of P, it follows, from the Order Limit Theorem, that ℓ is an upper bound of P.

    Let ε > 0. Then ℓ - aₙ < ε for sufficiently large n since aₙ→ℓ. But then ℓ - ε < aₙ, and so we are done.
-}
    supP≃ℓ : P hasSupremum
    supP≃ℓ = ℓ ,
             (λ { (x , x∈P) → xₙ≤yₙ⇒x₀≤y₀ (xₙ≃c⇒xₙ→c {λ n → x} {x} λ n {n≢0} → ≃-refl)
               (xₙ→x∧x≃y⇒xₙ→y (proj₂ (proj₁ (proj₂ aₙ,bₙ→ℓ))) (≃-symm (proj₁ (proj₂ (proj₂ aₙ,bₙ→ℓ))))) (λ n {n≢0} → <⇒≤ (P<bₙ n (x , x∈P)))}) ,
             λ ε ε>0 → let aₙ→ℓ = proj₁ aₙ,bₙ→ℓ; aₙ-get = fast-ε-from-convergence aₙ→ℓ ε (0<x⇒posx ε>0); n = suc (proj₁ aₙ-get); aₙ = as n in
               (aₙ , aₙ∈P n) , (begin-strict
                 ℓ - ε             ≈⟨ solve 3 (λ ℓ aₙ ε → ℓ ⊖ ε ⊜ ℓ ⊖ aₙ ⊕ (aₙ ⊖ ε)) ≃-refl ℓ aₙ ε ⟩
                 ℓ - aₙ + (aₙ - ε) <⟨ +-monoˡ-< (aₙ - ε) (≤-<-trans x≤∣x∣ (<-respˡ-≃ (∣x-y∣≃∣y-x∣ aₙ ℓ) (proj₂ aₙ-get n ℕP.≤-refl))) ⟩
                 ε + (aₙ - ε)      ≈⟨ solve 2 (λ aₙ ε → ε ⊕ (aₙ ⊖ ε) ⊜ aₙ) ≃-refl aₙ ε ⟩
                 aₙ                 ∎)

abstract
  fast-proposition-4-3-if : {P : Pred ℝ 0ℓ} → P isNonvoid → P isBoundedAbove →
                            ({x y : ℝ} → x < y → P isBoundedAboveBy y ⊎ ∃ λ a → P a × x < a) →
                            P hasSupremum
  fast-proposition-4-3-if = proposition-4-3-if


{-
A subset A⊆ℝ is totally bounded if, for each ε>0, there exists a subfinite subset {y₁,...,yₙ} of A such that, for all x∈A, at least one of
∣x - y₁∣, ..., ∣x - yₙ∣ is less than ε.

Change to n instead of suc n-1


-}

_isTotallyBounded : Pred ℝ 0ℓ → Set
P isTotallyBounded = (ε : ℝ) → ε > 0ℝ → ∃ λ (n-1 : ℕ) → ∃ λ (f : Fin (suc n-1) → 𝕊 P) →
                     (X : 𝕊 P) → ∃ λ (k : Σ ℕ λ m → m ℕ.< suc n-1) → ∣ proj₁ X - proj₁ (f (fromℕ< (proj₂ k))) ∣ < ε

z<x⊔y⇒z<x∨z<y : {x y z : ℝ} → z < x ⊔ y → (z < x) ⊎ (z < y)
z<x⊔y⇒z<x∨z<y {x} {y} {z} (pos* (n-1 , hyp)) = [ left , right ]′ (ℚP.≤-total x₂ₙ y₂ₙ)
  where
    open ℚP.≤-Reasoning
    n = suc n-1
    x₂ₙ = seq x (2 ℕ.* n)
    y₂ₙ = seq y (2 ℕ.* n)
    z₂ₙ = seq z (2 ℕ.* n)

    left : x₂ₙ ℚ.≤ y₂ₙ → (z < x) ⊎ (z < y)
    left hyp2 = inj₂ (pos* (n-1 , (begin-strict
      + 1 / n             <⟨ hyp ⟩
      x₂ₙ ℚ.⊔ y₂ₙ ℚ.- z₂ₙ ≈⟨ ℚP.+-congˡ (ℚ.- z₂ₙ) (ℚP.p≤q⇒p⊔q≃q hyp2) ⟩
      y₂ₙ ℚ.- z₂ₙ          ∎)))

    right : y₂ₙ ℚ.≤ x₂ₙ → (z < x) ⊎ (z < y)
    right hyp2 = inj₁ (pos* (n-1 , (begin-strict
      + 1 / n             <⟨ hyp ⟩
      x₂ₙ ℚ.⊔ y₂ₙ ℚ.- z₂ₙ ≈⟨ ℚP.+-congˡ (ℚ.- z₂ₙ) (ℚP.p≥q⇒p⊔q≃p hyp2) ⟩
      x₂ₙ ℚ.- z₂ₙ          ∎)))

z<max⦅xᵢ⦆⇒z<xⱼ : {z : ℝ} {f : ℕ → ℝ} {n : ℕ} → z < max f n →
                 ∃ λ k → k ℕ.≤ n × z < f k
z<max⦅xᵢ⦆⇒z<xⱼ {z} {f} {zero} hyp    = 0 , ℕP.≤-refl , hyp
z<max⦅xᵢ⦆⇒z<xⱼ {z} {f} {suc n-1} hyp = [ left , right ]′ (z<x⊔y⇒z<x∨z<y hyp)
  where
    n = suc n-1

    left : z < max f n-1 → ∃ λ k → k ℕ.≤ n × z < f k
    left hyp2 = let rec = z<max⦅xᵢ⦆⇒z<xⱼ hyp2 in
                proj₁ rec , ℕP.≤-trans (proj₁ (proj₂ rec)) (ℕP.n≤1+n n-1) , proj₂ (proj₂ rec)

    right : z < f n → ∃ λ k → k ℕ.≤ n × z < f k
    right hyp2 = n , ℕP.≤-refl , hyp2
{-
{y₁,...,yₙ}
Max over first m elements
m = 1: y₁
m = k + 1: 

f : Fin (suc (suc n-1)) → ℝ
g : Fin (suc n-1) → ℝ

Probably don't need this
-}
maxFin : {n-1 : ℕ} → (f : Fin (suc n-1) → ℝ) → ℝ
maxFin {zero} f    = f (fromℕ 0)
maxFin {suc n-1} f = maxFin (λ (x : Fin (suc n-1)) → f (inject₁ x)) ⊔ f (fromℕ (suc n-1))

{-

-}
m≤n⇒fm≤maxFinf : {m n : ℕ} (f : Fin (suc n) → ℝ) → (m≤n : m ℕ.≤ n) → f (fromℕ< (ℕ.s≤s m≤n)) ≤ maxFin f  
m≤n⇒fm≤maxFinf {zero} {zero} f m≤n = ≤-refl
m≤n⇒fm≤maxFinf {zero} {suc n} f m≤n = ≤-trans (m≤n⇒fm≤maxFinf (λ x → f (inject₁ x)) ℕ.z≤n) (x≤x⊔y _ _)
m≤n⇒fm≤maxFinf {suc m} {zero} f ()
m≤n⇒fm≤maxFinf {suc m} {suc n} f (ℕ.s≤s m≤n) = {!m≤n⇒fm≤maxFinf (λ x → f (inject₁ x)) m≤n!}

{-
F : Fin 3 → ℝ
F Fin.zero = 0ℝ
F (Fin.suc Fin.zero) = 1ℝ
F (Fin.suc (Fin.suc Fin.zero)) = (+ 2 / 1) ⋆

G : Fin 2 → ℝ
G Fin.zero = 0ℝ
G (Fin.suc Fin.zero) = 1ℝ

H : Fin 1 → ℝ
H Fin.zero = 0ℝ

{-
maxFin {2} F = maxFin () ⊔ F 2
-}

test : {!!}
test = {!!}
-}

abstract
  _fast-≤?_ : Relation.Binary.Decidable ℕ._≤_
  _fast-≤?_ = ℕP._≤?_

  -- The non-abstract version tends to slow down computations significantly, for instance
  -- in totallyBounded⇒boundedAbove below.
  fast-p<q⇒p⋆<q⋆ : (p q : ℚᵘ) → p ℚ.< q → p ⋆ < q ⋆
  fast-p<q⇒p⋆<q⋆ = p<q⇒p⋆<q⋆

{-
max : (ℕ → ℝ) → (n : ℕ) → ?
max f n = ?

Proposition:
  A totally bounded subset A of ℝ is bounded above.
Proof:
  Let {y₁,...,yₙ} ⊆ A be subfinite such that, for every x∈A, we have ∣x - yₖ∣ < 1 for some yₖ.
Set M = max{y₁,...,yₙ}. Let x∈P and choose yₖ such that ∣x - yₖ∣ < 1. Then
x = x - yₖ + yₖ
  ≤ 1 + M,
so 1 + M is an upper bound of A.                                                            □
-}
totallyBounded⇒boundedAbove : {P : Pred ℝ 0ℓ} → P isTotallyBounded → P isBoundedAbove
totallyBounded⇒boundedAbove {P} PT = 1ℝ + M , λ x∈P → let x = proj₁ x∈P; k<n = proj₁ (proj₂ (proj₂ PT-get) x∈P); k = proj₁ k<n
                                                            ; yₖ = proj₁ (proj₁ (proj₂ PT-get) (fromℕ< (proj₂ k<n))) in
  begin
  x           ≈⟨ solve 2 (λ x yₖ → x ⊜ x ⊖ yₖ ⊕ yₖ) ≃-refl x yₖ ⟩
  x - yₖ + yₖ ≤⟨ +-mono-≤ (<⇒≤ (≤-<-trans x≤∣x∣ (proj₂ (proj₂ (proj₂ PT-get) x∈P))))
                 {!!} ⟩
  --+-mono-≤ (<⇒≤ (≤-<-trans x≤∣x∣ (proj₂ (proj₂ (proj₂ PT-get) x∈P))))
                        --  (m≤n⇒fm≤maxfn y {!!} {!!} {!!}) ⟩
  1ℝ + M       ∎
  where
    open ≤-Reasoning
    PT-get = PT 1ℝ (fast-p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _))
    n = suc (proj₁ PT-get)
    f : Fin n → 𝕊 P
    f = proj₁ (proj₂ PT-get)

    --y k with p : m < n ≡ f (fromℕ m<n)
    

    y : ℕ → ℝ
    y m with m ℕP.<? n
    ... | .Bool.true because ofʸ m<n  = proj₁ (f (fromℕ< m<n))
    ... | .Bool.false because ofⁿ m≥n = 0ℝ

    {-
    
    -}

    z : ℕ → ℝ
    z m = t m (m ℕP.<? n)
      where
        t : (m : ℕ) → Dec (m ℕ.< n) → ℝ
        t m (.Bool.true because ofʸ m<n)  = proj₁ (f (fromℕ< m<n))
        t m (.Bool.false because ofⁿ m≥n) = 0ℝ

    zₖ-wellDef : (m : ℕ) → (m<n : m ℕ.< n) → z m ≃ proj₁ (f (fromℕ< m<n))
    zₖ-wellDef m m<n with m ℕ.<? n
    ... | .Bool.true because ofʸ p   = {!!}
    ... | .Bool.false because ofⁿ ¬p = {!!}

    M : ℝ
    M = max y (ℕ.pred n)

    {-lem : P isBoundedAboveBy (1ℝ + M)
    lem x∈P = {!!}
      where
        x = proj₁ x∈P
        k<n = proj₁ (proj₂ (proj₂ PT-get) x∈P)
        k = proj₁ k<n
        yₖ = proj₁ (proj₁ (proj₂ PT-get) (fromℕ< (proj₂ k<n)))-}

        {-yₖ-wellDef : yₖ ≡ y k
        yₖ-wellDef with k ℕP.<? n
        ... | .Bool.true because ofʸ p = {!!}
        ... | .Bool.false because ofⁿ ¬p = {!!}-}

{-
Choose a₁,...,aₙ∈A such that for each a∈A at least
one of ∣a - a₁∣,...,∣a - aₙ∣ is less than 1/4. For some 1 ≤ k ≤ n
we have
                      aₖ > max{a₁,...,aₙ} - 1/4.
Either 0 < aₙ or aₙ < 1/2. 

Let M = max{a₁,...,aₙ}.
aₖ = aₖ - M + M
   ≥ M - ∣M - aₖ∣
   
M - 1/4 ≤ M - ∣a - aₖ∣
        ≤ M - a + aₖ
        
M < aₖ + 1/4?

M ≥ aₖ + 1/4

M - aₖ < 1/4
-1/4 < aₖ - M

M - aₖ = M - aₖ + a - a
       ≤ ∣a - M∣ + ∣a - aₖ∣
       < ∣a - M∣ + 1/4

aₖ = M - M + aₖ
   ≥ M - ∣aₖ - M∣
   
     c∣aₖ - M∣ ≤ ∣aₖ - a∣ + ∣M - a∣
        < 1/4 + ∣M - a∣


   ·
        ·     □
   ·        ·  
  ·                ·

Let x < y and set α = ¼(y - x). Choose a₁,...,aₙ∈A such that at
least one ∣a - aᵢ∣ < α. 

aₖ = a - (a - aₖ)
   ≥ a - ∣a - aₖ∣
   > a - α

aₖ > M - α ⇔ aₖ - M + α > 0

aₖ ≤ M ⇒ -M ≤ - 

Let x < y and set α = ¼(y - x). Choose a₁,...,aₙ∈A such that for each a∈A, we have ∣a - aᵢ∣ < ε for some 1 ≤ i ≤ n.
Let M = max{a₁,...,aₙ}. Then there is aₖ such that aₖ > M - α. Either x < aₖ or aₖ < x + 2α. In the latter case, we have
              a ≤ aᵢ + ∣a - aᵢ∣ < aₖ + α + α < x + 4α = y,
so y is an upper bound of A. Thus supA exists by Proposition 4.3                                                       □
-}
corollary-4-4-supremum : {P : Pred ℝ 0ℓ} (PT : P isTotallyBounded) → (P hasSupremum)
corollary-4-4-supremum {P} PT = fast-proposition-4-3-if {!!} {!!} {!!}
  where
    

corollary-4-4-infimum : {P : Pred ℝ 0ℓ} (PT : P isTotallyBounded) → P hasInfimum
corollary-4-4-infimum {P} PT = {!!}

{-
A finite closed interval is compact if it is nonempty.
Let I be a closed interval.
-}

_≃ₛ_ : {P : Pred ℝ 0ℓ} → Rel (𝕊 P) 0ℓ
x ≃ₛ y = proj₁ x ≃ proj₁ y

≃ₛ-isEquivalence : (P : Pred ℝ 0ℓ) → IsEquivalence (_≃ₛ_ {P})
≃ₛ-isEquivalence P = record
  { refl  = ≃-refl
  ; sym   = ≃-symm
  ; trans = ≃-trans
  }

-- Setoid conversion function
-- Convert a subset into a setoid
𝕊[_] : Pred ℝ 0ℓ → Setoid 0ℓ 0ℓ
𝕊[ P ] = record
  { Carrier       = 𝕊 P
  ; _≈_           = _≃ₛ_
  ; isEquivalence = ≃ₛ-isEquivalence P
  }

record CompactInterval : Set where
  field
    lower    : ℝ
    upper    : ℝ
    nonempty : Interval ⟦ lower , upper ⟧

open import Function.Bundles using (Func)

_⟶_ : Pred ℝ 0ℓ → Pred ℝ 0ℓ → Set
P ⟶ Q = Func 𝕊[ P ] 𝕊[ Q ]

_⟶ℝ : Pred ℝ 0ℓ → Set
P ⟶ℝ = Func 𝕊[ P ] ≃-setoid

testing : {!!}
testing = (x : ℝ) → let T = x in {!!}

{-
f : [a , b] → ℝ

f : Func (𝕊[ P ]) ≃-setoid
      P → ℝ

∣ ⟦ x ⟧ + ⟦ y ⟧ ∣ < ⟦ δ ⟧


-}
data _isContinuousAt_ {P : Pred ℝ 0ℓ} (F : P ⟶ℝ) (x : 𝕊 P) : Set where
  cont* : ((ε : ℝ⁺) → ∃ λ (δ : ℝ⁺) → (y : 𝕊 P) → ∣ {!!} ∣ < (proj₁ δ) → {!!}) → F isContinuousAt x

{-data _isContinuousAt_ {P : Pred ℝ 0ℓ} (F : Func (𝕊[ P ]) ≃-setoid) (xP : 𝕊 P) : Set where
  cont* : ((ε>0 : ℝ⁺) → ∃ λ (δ>0 : ℝ⁺) → (yP : 𝕊 P) → let ε = proj₁ ε>0; δ = proj₁ δ>0; x = proj₁ xP; y = proj₁ yP; f = Func.f F in
          {!∣ x - y ∣ < δ → ∣ f x - f y ∣ < ε!}) → F isContinuousAt xP
-}    
  --cont* : ((ε : ℝ⁺) → ∃ λ (δ : ℝ⁺) → (y : 𝕊 P) → ∣ proj₁ x - proj₁ y ∣ < proj₁ δ → ∣ {!!} ∣ < proj₁ ε) → F isContinuousAt x

{-


A function f : [a,b] → ℝ is continuous if for each ε > 0 there exists ω(ε) > 0 such that
∣f(x) - f(y)∣ ≤ ε whenever ∣x - y∣ ≤ ω(ε).




Why not make a function continuous at a point and then extend that to continuity on subsets of ℝ
instead of focusing on intervals? We can use intervals for differentiation later on instead.
-}
data _isContinuousOn_ : Set where
  --cont* :


