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
open import Interval
open import FiniteSequences.SigmaIndices
open ℝ-Solver

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
P isTotallyBounded = (ε : ℝ) → ε > 0ℝ → ∃ λ (n-1 : ℕ) → ∃ λ (f : SigInd n-1 → 𝕊 P) →
                     (X : 𝕊 P) → ∃ λ (k : SigInd n-1) → ∣ proj₁ X - proj₁ (f k) ∣ < ε

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

abstract
  _fast-≤?_ : Relation.Binary.Decidable ℕ._≤_
  _fast-≤?_ = ℕP._≤?_

  -- The non-abstract version tends to slow down computations significantly, for instance
  -- in totallyBounded⇒boundedAbove below.
  fast-p<q⇒p⋆<q⋆ : (p q : ℚᵘ) → p ℚ.< q → p ⋆ < q ⋆
  fast-p<q⇒p⋆<q⋆ = p<q⇒p⋆<q⋆

{-
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
totallyBounded⇒boundedAbove {P} PT = 1ℝ + M , λ x∈P → let x = proj₁ x∈P; k≤n-1 = proj₁ (proj₂ (proj₂ PT-get) x∈P); k = proj₁ k≤n-1 ; fₖ = f k≤n-1 in
  begin
  x           ≈⟨ solve 2 (λ x fₖ → x ⊜ x ⊖ fₖ ⊕ fₖ) ≃-refl x fₖ ⟩
  x - fₖ + fₖ ≤⟨ +-mono-≤ (<⇒≤ (≤-<-trans x≤∣x∣ (proj₂ (proj₂ (proj₂ PT-get) x∈P))))
                 (m≤n-1⇒fm≤maxΣf {n-1} f k≤n-1) ⟩
  1ℝ + M       ∎
  where
    open ≤-Reasoning
    PT-get = PT 1ℝ (fast-p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _))
    n-1 = proj₁ PT-get
    f𝕊 : SigInd n-1 → 𝕊 P
    f𝕊 = proj₁ (proj₂ PT-get)
    f : SigInd n-1 → ℝ
    f k = proj₁ (f𝕊 k)

    ≤-same : {m m' : ℕ} → (p p' : m ℕ.≤ m') → p ≡ p'
    ≤-same {.zero} {_} ℕ.z≤n ℕ.z≤n = refl
    ≤-same {.suc _} {.suc _} (ℕ.s≤s p) (ℕ.s≤s p') = cong ℕ.s≤s (≤-same p p')

    M : ℝ
    M = maxΣ f

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
isTotallyBounded⇒isNonvoid {P} PT = (proj₁ (proj₂ (PT 1ℝ 0<1))) (zero , ℕ.z≤n)

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
    as𝕊 : SigInd N-1 → 𝕊 P
    as𝕊 = proj₁ (proj₂ pack)
    as : SigInd N-1 → ℝ
    as k = proj₁ (as𝕊 k)
    proofforas : (X : 𝕊 P) → ∃ (λ (k : SigInd N-1) →  ∣ proj₁ X - as k ∣ < α)
    proofforas = proj₂ (proj₂ pack)

    --here we need the maximum as 𝕊 P
    ∃n : ∃ (λ n → as n > maxΣ as - α)
    ∃n = maxΣSelect {N-1} as α α>0
    n : SigInd N-1
    n = proj₁ ∃n
    an : ℝ
    an = as n

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
                                                                  ak - α           ≤⟨ +-monoˡ-≤ (- α) {ak} (m≤n-1⇒fm≤maxΣf as k) ⟩
                                                                  maxΣ as - α      <⟨ proj₂ ∃n ⟩
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
        kp : ∃ (λ (k : SigInd N-1) → ∣ a - as k ∣ < α)
        kp = proofforas sa
        k : SigInd N-1
        k = proj₁ kp
        ak : ℝ
        ak = as k
    part2 : an > x → (P isBoundedAboveBy y) ⊎ ∃ (λ a → P a × x < a)
    part2 an>x = inj₂ (an , proj₂ (as𝕊 n) , an>x)

-- Is similarly provable. Or maybe a (-_) ∘ f would shorten it.
-- corollary-4-4-infimum : {P : Pred ℝ 0ℓ} (PT : P isTotallyBounded) → P hasInfimum
-- corollary-4-4-infimum {P} PT = ?

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

open import Function.Bundles using (Func)

_⟶_ : Pred ℝ 0ℓ → Pred ℝ 0ℓ → Set
P ⟶ Q = Func 𝕊[ P ] 𝕊[ Q ]

_⟶ℝ : Pred ℝ 0ℓ → Set
P ⟶ℝ = Func 𝕊[ P ] ≃-setoid

-- The interval has to be an explicit parameter; otherwise it cannot figure out
-- from the function what the interval was.
data continuousOnCI : (D : CompactInterval) (f : D ↓ → ℝ) → Set where
  contOn* : {D : CompactInterval} {f : D ↓ → ℝ} →
            (∃ λ (ω : ℝ⁺ → ℝ⁺) → ∀ (ε : ℝ⁺) (x y : D ↓) → ∣ proj₁ x - proj₁ y ∣ ≤ proj₁ (ω ε) → ∣ f x - f y ∣ ≤ proj₁ ε)
              → continuousOnCI D f
-- Unfortunately, the syntax becomes a bit inconvenient.

{-
-- this would also need D as an explicit parameter
_isContinuousOnCI : {D : CompactInterval} (f : D ↓ → ℝ) → Set
_isContinuousOnCI {D} f = continuousOnCI D f
-}

modCon : {D : CompactInterval} {f : D ↓ → ℝ} → continuousOnCI D f → (ℝ⁺ → ℝ⁺)
modCon (contOn* (ω , _)) = ω 

constIsContinuous : ∀ (c : ℝ) (D : CompactInterval) → continuousOnCI D (λ (x : D ↓) → c)
constIsContinuous c D = contOn* ((λ ε → 1ℝ , 0<1) , λ ε x y ∣x-y∣≤1 → begin
    ∣ c - c ∣ ≈⟨ ∣-∣-cong {c - c} {0ℝ} (solve 1 (λ c → c ⊖ c ⊜ Κ 0ℚᵘ) ≃-refl c) ⟩
    ∣ 0ℝ ∣    ≈⟨ 0≤x⇒∣x∣≃x ≤-refl ⟩
    0ℝ      ≤⟨ <⇒≤ (proj₂ ε) ⟩
    proj₁ ε ∎)
  where open ≤-Reasoning

idIsContinuous : ∀ (D : CompactInterval) → continuousOnCI D (λ (x : D ↓) → proj₁ x)
idIsContinuous D = contOn* ((λ ε → ε) , λ ε x y ∣x-y∣≤ε → ∣x-y∣≤ε)

inRangeOf : {A : Set} (f : A → ℝ) → (ℝ → Set)
inRangeOf f = λ y → ∃ λ x → f x ≃ y

contOnD⇒totallyBounded : {D : CompactInterval} {f : D ↓ → ℝ} → continuousOnCI D f → (a<b : CIlower D < CIupper D) →
    inRangeOf f isTotallyBounded
contOnD⇒totallyBounded {D} {f} (contOn* (ω , hyp)) a<b 2ε 2ε>0 = n , fas𝕊 , mainPart
  where
  ε : ℝ --have to take 2ε because isTotallyBounded expects strict <
  ε = 2ε * (+ 1 / 2) ⋆
  ε>0 : ε > 0ℝ
  ε>0 = 0<x,y⇒0<x*y {2ε} {(+ 1 / 2)⋆} 2ε>0 (posx⇒0<x (0<p⇒0<p⋆ (+ 1 / 2) tt))
  ε⁺ ωε : ℝ⁺
  ε⁺ = ε , ε>0
  ωε = ω ε⁺
  a b : ℝ
  a = CIlower D
  b = CIupper D
  arch : ∃ (λ n-1 → (+[1+ n-1 ] / 1) ⋆ > (b - a) * (proj₁ ωε ⁻¹) (inj₂ (proj₂ ωε)))
  arch = fast-archimedean-ℝ ((b - a) * (proj₁ ωε ⁻¹) (inj₂ (proj₂ ωε)))
  n-1 n : ℕ
  n-1 = proj₁ arch
  n = suc n-1

  d : ℝ
  d = (b - a) * (+ 1 / n) ⋆
  d>0 : d > 0ℝ
  d>0 = 0<x,y⇒0<x*y {b - a} {(+ 1 / n)⋆} (x<y⇒0<y-x a b a<b) (posx⇒0<x (0<p⇒0<p⋆ (+ 1 / n) tt))
  asd : SigInd n  → D ↓
  asd (k , k≤n) = fullPartition D n {tt} {k} k≤n
  as : SigInd n → ℝ
  as k = proj₁ (asd k)
  fas𝕊 : SigInd n → 𝕊 (inRangeOf f)
  fas𝕊 k = f (asd k) , asd k , ≃-refl

  mainPart : ∀ (y : 𝕊 (inRangeOf f)) → ∃ (λ (i : SigInd n) → ∣ proj₁ y - proj₁ (fas𝕊 i) ∣ < 2ε)
  mainPart (y , x , fx≃y) = i , (begin-strict
           ∣ y - proj₁ (fas𝕊 i) ∣        ≈⟨ ∣-∣-cong (+-congˡ (- f (asd i)) {y} {f x} (≃-symm fx≃y)) ⟩
          ∣ f x - f (asd i) ∣            ≤⟨ hyp ε⁺ x (asd i) (<⇒≤ {∣ proj₁ x - proj₁ (asd i) ∣} {proj₁ (ω ε⁺)} iInRadius) ⟩
          ε                             <⟨ *-monoʳ-<-pos {2ε} (0<x⇒posx 2ε>0) {(+ 1 / 2)⋆} {1ℝ} (p<q⇒p⋆<q⋆ (+ 1 / 2) 1ℚᵘ (ℚ.*<* (ℤ.+<+ ℕP.≤-refl))) ⟩      -- ε was 2ε * (+ 1 / 2)⋆
          2ε * 1ℝ                      ≈⟨ *-identityʳ 2ε ⟩
          2ε                                    ∎)
    where
    open ≤-Reasoning
    {-
      aᵢ > x
      a + (i+1) * d > x
      (i+1) * d > x - a
      (i+1) > (x - a) / d
    -}

    --this should rather be solved with fullPartition-[x-aᵢ]<d/n
    pointNearApp : ∃ λ (i : SigInd n) →
            ∣ as i - proj₁ x ∣ < ((+ 1 / n)) ⋆ * (b - a)
    pointNearApp = fullPartition-pointNear D a<b n x
    i : SigInd n
    i = proj₁ pointNearApp
    iInRadius : ∣ proj₁ x - as i ∣ < proj₁ (ω ε⁺)
    iInRadius = begin-strict
                ∣ proj₁ x - as i ∣        ≈⟨ ≃-trans (≃-symm (∣-x∣≃∣x∣ {proj₁ x - as i})) (∣-∣-cong { - (proj₁ x - as i)} {as i - proj₁ x}
                                                                                               (solve 2 (λ t t' → ⊝ (t ⊖ t') ⊜ t' ⊖ t) ≃-refl (proj₁ x) (as i)) ) ⟩
                ∣ as i - proj₁ x ∣        <⟨ proj₂ pointNearApp ⟩
                (+ 1 / n)⋆ * (b - a)    ≈⟨ ≃-symm (*-identityʳ ((+ 1 / n)⋆ * (b - a))) ⟩
                (+ 1 / n)⋆ * (b - a) * 1ℝ ≈⟨ *-congˡ {(+ 1 / n)⋆ * (b - a)} {1ℝ} {(proj₁ ωε ⁻¹) (inj₂ (proj₂ ωε)) * (proj₁ ωε)}
                                               (≃-symm (*-inverseˡ (proj₁ ωε) (inj₂ (proj₂ ωε)))) ⟩
                (+ 1 / n)⋆ * (b - a) * ((proj₁ ωε ⁻¹) (inj₂ (proj₂ ωε)) * (proj₁ ωε)) ≈⟨ solve 4 (λ t₁ t₂ t₃ t₄ → (t₁ ⊗ t₂) ⊗ (t₃ ⊗ t₄) ⊜ t₁ ⊗ ((t₂ ⊗ t₃) ⊗ t₄))
                                                                                           ≃-refl ((+ 1 / n)⋆) (b - a) ((proj₁ ωε ⁻¹) (inj₂ (proj₂ ωε))) (proj₁ ωε) ⟩
                (+ 1 / n)⋆ * ((b - a) * (proj₁ ωε ⁻¹) (inj₂ (proj₂ ωε)) * (proj₁ ωε)) <⟨ archApp ⟩
                (+ 1 / n)⋆ * ((+ n / 1)⋆ * (proj₁ ωε)) ≈⟨ ≃-symm (*-assoc ((+ 1 / n)⋆) ((+ n / 1)⋆) (proj₁ ωε)) ⟩
                (+ 1 / n)⋆ * (+ n / 1)⋆ * (proj₁ ωε) ≈⟨ *-congʳ {proj₁ ωε} {((+ 1 / n)⋆) * (+ n / 1)⋆} {1ℝ}
                                                         (≃-trans (≃-symm (⋆-distrib-* (+ 1 / n) (+ n / 1))) (⋆-cong {(+ 1 / n) ℚ.* (+ n / 1)} {1ℚᵘ}
                                                           (ℚ.*≡* (cong +[1+_] (trans (ℕP.*-identityʳ (n-1 ℕ.+ 0))
                                                                                (trans (ℕP.+-identityʳ n-1)
                                                                                (trans (sym (ℕP.*-identityʳ n-1))
                                                                                       (sym (ℕP.+-identityʳ (n-1 ℕ.* 1)))))))))) ⟩
                1ℝ * (proj₁ ωε)                     ≈⟨ *-identityˡ (proj₁ ωε) ⟩
                proj₁ (ωε)             ∎
      where
      -- proj₂ arch : (+ n / 1)⋆ > (b-a) * (proj₁ ωε ⁻¹) (inj₂ (proj₂ ωε))
      archApp : (+ 1 / n)⋆ * ((b - a) * (proj₁ ωε ⁻¹) (inj₂ (proj₂ ωε)) * (proj₁ ωε)) < (+ 1 / n)⋆ * ((+ n / 1)⋆ * (proj₁ ωε))
      archApp = *-monoʳ-<-pos {(+ 1 / n)⋆} (0<p⇒0<p⋆ (+ 1 / n) tt) {(b - a) * (proj₁ ωε ⁻¹) (inj₂ (proj₂ ωε)) * (proj₁ ωε)} {(+ n / 1)⋆ * (proj₁ ωε)}
                  (*-monoˡ-<-pos {proj₁ ωε} (0<x⇒posx (proj₂ ωε)) {(b - a) * (proj₁ ωε ⁻¹) (inj₂ (proj₂ ωε))} {(+ n / 1)⋆}
                    (proj₂ arch))
      
    
weakWeierstrass-sup : {D : CompactInterval} {f : D ↓ → ℝ} → continuousOnCI D f → (a<b : CIlower D < CIupper D) →
    inRangeOf f hasSupremum
weakWeierstrass-sup {D} {f} fcont a<b = corollary-4-4-supremum (contOnD⇒totallyBounded {D} {f} fcont a<b)
