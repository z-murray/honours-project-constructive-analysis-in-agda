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
import Data.Fin.Properties as FinP

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

--into RealProperties?
a-b<c⇒a<c+b : ∀ {a b c : ℝ} → a - b < c → a < c + b
a-b<c⇒a<c+b {a} {b} {c} hyp = begin-strict
     a           ≈⟨ solve 2 (λ a b → a ⊜ a ⊖ b ⊕ b) ≃-refl a b ⟩
     a - b + b   <⟨ +-monoˡ-< b hyp ⟩
     c + b ∎
  where open ≤-Reasoning

a-b<c⇒a<b+c : ∀ {a b c : ℝ} → a - b < c → a < b + c
a-b<c⇒a<b+c {a} {b} {c} hyp = begin-strict
     a           <⟨ a-b<c⇒a<c+b hyp ⟩
     c + b       ≈⟨ +-comm c b ⟩
     b + c       ∎
  where open ≤-Reasoning

0<ε⇒x<x+ε : ∀ {ε : ℝ} (x : ℝ) → 0ℝ < ε → x < x + ε
0<ε⇒x<x+ε {ε} x ε>0 = begin-strict
    x        ≈⟨ ≃-symm (+-identityʳ x) ⟩
    x + 0ℝ   <⟨ +-monoʳ-< x ε>0 ⟩
    x + ε    ∎
  where open ≤-Reasoning

0<ε⇒x-ε<x : ∀ {ε : ℝ} (x : ℝ) → 0ℝ < ε → x - ε < x
0<ε⇒x-ε<x {ε} x ε>0 = begin-strict
    x - ε     <⟨ +-monoʳ-< x { - ε} { - 0ℝ} (neg-mono-< {0ℝ} {ε} ε>0) ⟩
    x - 0ℝ   ≈⟨ solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) ≃-refl x ⟩
    x        ∎
  where open ≤-Reasoning

--based on Nuprl proof at https://www.nuprl.org/LibrarySnapshots/Published/Version1/Mathematics/reals/rmaximum-select_proof_1_2_1_1.html
maxSelect : ∀ (f : ℕ → ℝ) (n : ℕ) (ε : ℝ) → ε > 0ℝ → ∃ (λ i → max f n - ε < f i)
maxSelect f zero ε ε>0 = zero , (begin-strict
    f 0 - ε       <⟨ 0<ε⇒x<x+ε (f 0 - ε) ε>0 ⟩
    f 0 - ε + ε   ≈⟨ solve 2 (λ x y → x ⊖ y ⊕ y ⊜ x) ≃-refl (f 0) ε ⟩
    f 0           ∎)
  where open ≤-Reasoning
maxSelect f (suc n) ε ε>0 = [ case₁ , case₂ ]′ eitheror
  where
  v : ℝ
  v = max f n
  prevproof : ∃ (λ i → v - ε < f i)
  prevproof = maxSelect f n ε ε>0
  i : ℕ
  i = proj₁ prevproof

  eitheror : f (suc n) - f i < ε ⊎ f (suc n) - f i > 0ℝ
  eitheror = fast-corollary-2-17 (f (suc n) - f i) 0ℝ ε ε>0

  case₁ : f (suc n) - f i < ε →
      ∃ (λ i₁ → v ⊔ f (suc n) - ε < f i₁)
  case₁ hyp = i , (begin-strict
         v ⊔ f (suc n) - ε      <⟨ +-monoˡ-< (- ε) (x<z∧y<z⇒x⊔y<z v (f (suc n)) (f i + ε) (a-b<c⇒a<c+b (proj₂ prevproof)) (a-b<c⇒a<b+c hyp)) ⟩
         f i + ε - ε            ≈⟨ solve 2 (λ a b → a ⊕ b ⊖ b ⊜ a) ≃-refl (f i) ε ⟩
         f i                    ∎ )
    where open ≤-Reasoning
  case₂ : f (suc n) - f i > 0ℝ →
      ∃ (λ i₁ → v ⊔ f (suc n) - ε < f i₁)
  case₂ hyp = suc n , (begin-strict
         v ⊔ f (suc n) - ε      <⟨ +-monoˡ-< (- ε) (x<z∧y<z⇒x⊔y<z v (f (suc n)) (f (suc n) + ε) lem (0<ε⇒x<x+ε (f (suc n)) ε>0)) ⟩
         f (suc n) + ε - ε      ≈⟨ solve 2 (λ a b → a ⊕ b ⊖ b ⊜ a) ≃-refl (f (suc n)) ε ⟩
         f (suc n)              ∎)
    where
      open ≤-Reasoning
      lem : v < f (suc n) + ε
      lem = begin-strict
          v              <⟨ a-b<c⇒a<c+b (proj₂ prevproof) ⟩
          f i + ε        <⟨ +-monoˡ-< ε (0<y-x⇒x<y (f i) (f (suc n)) hyp) ⟩
          f (suc n) + ε  ∎

--to ExtraProperties?

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
                                                            ; fₖ = proj₁ (f (fromℕ< (proj₂ k<n))) ; zₖ = z k in
  begin
  x           ≈⟨ solve 2 (λ x fₖ → x ⊜ x ⊖ fₖ ⊕ fₖ) ≃-refl x fₖ ⟩
  x - fₖ + fₖ ≈⟨ +-congʳ (x - fₖ) (≃-symm (zₖ-wellDef k (proj₂ k<n))) ⟩ --writing zₖ instead of fₖ; it is easier to prove zₖ≤M than fₖ≤M
  x - fₖ + zₖ ≤⟨ +-mono-≤ (<⇒≤ (≤-<-trans x≤∣x∣ (proj₂ (proj₂ (proj₂ PT-get) x∈P))))
                 (m≤n⇒fm≤maxfn z k n-1 (k<n⇒k≤n-1 (proj₂ k<n))) ⟩
  1ℝ + M       ∎
  where
    open ≤-Reasoning
    PT-get = PT 1ℝ (fast-p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _))
    n-1 = proj₁ PT-get
    n = suc n-1
    f : Fin n → 𝕊 P
    f = proj₁ (proj₂ PT-get)

    z : ℕ → ℝ
    z m = t m (m ℕP.<? n)
      where
        t : (m : ℕ) → Dec (m ℕ.< n) → ℝ
        t m (.Bool.true because ofʸ m<n)  = proj₁ (f (fromℕ< m<n))
        t m (.Bool.false because ofⁿ m≥n) = 0ℝ

    ≤-same : {m m' : ℕ} → (p p' : m ℕ.≤ m') → p ≡ p'
    ≤-same {.zero} {_} ℕ.z≤n ℕ.z≤n = refl
    ≤-same {.suc _} {.suc _} (ℕ.s≤s p) (ℕ.s≤s p') = cong ℕ.s≤s (≤-same p p')

    zₖ-wellDef : (m : ℕ) → (m<n : m ℕ.< n) → z m ≃ proj₁ (f (fromℕ< m<n))
    zₖ-wellDef m m<n with m ℕ.<? n
    zₖ-wellDef m m<n | .Bool.true because ofʸ p with ≤-same m<n p
    ...                                        | refl = ≃-refl₂ refl
    zₖ-wellDef m m<n | .Bool.false because ofⁿ ¬p = ⊥-elim (¬p m<n)

    M : ℝ
    M = max z n-1

    k<n⇒k≤n-1 : ∀ {k : ℕ} → k ℕ.< n → k ℕ.≤ n-1
    k<n⇒k≤n-1 (ℕ.s≤s uneq) = uneq

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

--to RealProperties?
0<1 : 0ℝ < 1ℝ
0<1 = pos* (2 , ℚ.*<* (ℤ.+<+ (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))))

isTotallyBounded⇒isNonvoid : {P : Pred ℝ 0ℓ} → P isTotallyBounded → P isNonvoid
isTotallyBounded⇒isNonvoid {P} PT = (proj₁ (proj₂ (PT 1ℝ 0<1))) Fin.zero

corollary-4-4-supremum : {P : Pred ℝ 0ℓ} (PT : P isTotallyBounded) → P hasSupremum
corollary-4-4-supremum {P} PT = fast-proposition-4-3-if (isTotallyBounded⇒isNonvoid PT) (totallyBounded⇒boundedAbove PT) mainPart
  where
  mainPart : {x y : ℝ} → x < y → (P isBoundedAboveBy y) ⊎ ∃ (λ a → P a × x < a)
  mainPart {x} {y} x<y = [ part1 , part2 ]′ eitheror
    where
    α x+2α : ℝ
    α = ((+ 1 ℚ./ 4) ⋆) * (y - x)
    x+2α = (x + α + α)
    α>0 : α > 0ℝ
    α>0 = posx⇒0<x (posx,y⇒posx*y {(+ 1 ℚ./ 4) ⋆} {y - x} (0<p⇒0<p⋆ (+ 1 ℚ./ 4) tt) (0<x⇒posx (x<y⇒0<y-x x y x<y)))

    pack = PT α (0<x,y⇒0<x*y {(+ 1 ℚ./ 4) ⋆} {y - x} (fast-p<q⇒p⋆<q⋆ 0ℚᵘ (+ 1 ℚ./ 4) (ℚ.*<* (ℤ.+<+ (ℕ.s≤s ℕ.z≤n)))) (x<y⇒0<y-x x y x<y))
    N-1 N : ℕ
    N-1 = proj₁ pack
    N = suc N-1
    as : Fin N → 𝕊 P
    as = proj₁ (proj₂ pack)
    proofforas : (X : 𝕊 P) → ∃ (λ (k : Σ ℕ (λ k → k ℕ.< N)) →  ∣ proj₁ X - proj₁ (as (fromℕ< (proj₂ k))) ∣ < α)
    proofforas = proj₂ (proj₂ pack)
    asFin : Fin N → ℝ
    asFin = (λ k → proj₁ (as k))

    --here we need the maximum as 𝕊 P
    ∃n : ∃ (λ n → proj₁ (as n) > maxFin asFin - α)
    ∃n = maxFinSelect asFin α α>0
    n : Fin (suc N-1)
    n = proj₁ ∃n
    an : ℝ
    an = proj₁ (as n)

    eitheror : an < x+2α ⊎ an > x
    eitheror = fast-corollary-2-17 an x x+2α (begin-strict
              x         <⟨ 0<ε⇒x<x+ε x α>0 ⟩
              x + α     <⟨ 0<ε⇒x<x+ε (x + α) α>0 ⟩
              x + α + α ∎)
      where open ≤-Reasoning

    part1 : an < x+2α → (P isBoundedAboveBy y) ⊎ ∃ (λ a → P a × x < a)
    part1 an<x+2α = inj₁ lem
      where
      lem : P isBoundedAboveBy y
      lem sa = <⇒≤ (begin-strict
          a                          ≈⟨ solve 2 (λ ak a → a ⊜ ak ⊕ (a ⊖ ak)) ≃-refl ak a ⟩
          ak + (a - ak)              ≤⟨ +-monoʳ-≤ ak (x≤∣x∣ {a - ak}) ⟩
          ak + ∣ a - ak ∣             <⟨ +-monoʳ-< ak (proj₂ kp) ⟩
          ak + α                     ≈⟨ solve 2 (λ ak α → ak ⊕ α ⊜ ak ⊖ α ⊕ α ⊕ α) ≃-refl ak α ⟩
          ak - α + α + α             <⟨ +-monoˡ-< α {ak - α + α} {an + α}
                                       (+-monoˡ-< α {ak - α} {an} (begin-strict
                                                                  ak - α           ≤⟨ +-monoˡ-≤ (- α) {ak} {maxFin asFin} (mFinsn⇒fm≤maxFinf asFin k) ⟩
                                                                  maxFin asFin - α <⟨ proj₂ ∃n ⟩
                                                                  an               ∎)) ⟩
          an + α + α                 <⟨ +-monoˡ-< α (+-monoˡ-< α an<x+2α) ⟩ 
          x + α + α + α + α          ≈⟨ solve 2 (λ x y → x ⊕ y ⊕ y ⊕ y ⊕ y ⊜ x ⊕ (y ⊕ y ⊕ y ⊕ y)) ≃-refl x α ⟩
          x + (α + α + α + α)        ≈⟨ +-congʳ x {α + α + α + α} {(+ 4 / 1) ⋆ * (((+ 1 / 4) ⋆) * (y - x))} (solve 1 (λ w → w ⊕ w ⊕ w ⊕ w ⊜ Κ (+ 4 / 1) ⊗ w) ≃-refl α) ⟩
          x + (+ 4 / 1) ⋆ * (((+ 1 / 4) ⋆) * (y - x))    ≈⟨ +-congʳ x {(+ 4 / 1) ⋆ * (((+ 1 / 4) ⋆) * (y - x))} {((+ 4 / 1) ⋆ * (+ 1 / 4) ⋆) * (y - x)}
                                                            (≃-symm (*-assoc ((+ 4 / 1) ⋆) ((+ 1 / 4) ⋆) (y - x))) ⟩
          x + ((+ 4 / 1) ⋆ * (+ 1 / 4) ⋆) * (y - x)      ≈⟨ +-congʳ x {((+ 4 / 1) ⋆ * (+ 1 / 4) ⋆) * (y - x)} {1ℝ * (y - x)}
                                                           (*-congʳ {y - x} (≃-trans (≃-symm (⋆-distrib-* (+ 4 / 1) (+ 1 / 4))) (⋆-cong (ℚ.*≡* refl)) )) ⟩
          x + 1ℝ * (y - x)           ≈⟨ solve 2 (λ x y → x ⊕ (Κ 1ℚᵘ) ⊗ (y ⊖ x) ⊜ y) ≃-refl x y  ⟩
          y                          ∎)
        where
        open ≤-Reasoning
        a : ℝ
        a = proj₁ sa
        kp : ∃ (λ (k : Σ ℕ (λ k → k ℕ.< N)) → ∣ a - proj₁ (as (fromℕ< (proj₂ k))) ∣ < α)
        kp = proofforas sa
        k : Fin N
        k = fromℕ< (proj₂ (proj₁ kp))
        ak : ℝ
        ak = proj₁ (as k)
    part2 : an > x → (P isBoundedAboveBy y) ⊎ ∃ (λ a → P a × x < a)
    part2 an>x = inj₂ (an , proj₂ (as n) , an>x)

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
