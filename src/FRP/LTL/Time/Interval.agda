open import FRP.LTL.Time using ( Time ; _,_ )
open import FRP.LTL.Time.Bound using 
  ( Time∞ ; _≼_ ; _≺_ ; fin ; +∞ ; +∞-top ; t≺+∞ ; ≼-refl ; _≼-trans_ 
  ; ≡-impl-≼ ; ≺-impl-≼ ; _≺-trans_ ; _≺-transʳ_ ; ≺-impl-⋡ ; t≺t+1 )
open import FRP.LTL.Util using ( irrelevant ; ⊥-elim )
open import Relation.Unary using ( _∈_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym )

module FRP.LTL.Time.Interval where

infixr 2 _⊑_ _~_
infixr 4 _,_ _⌢_∵_

-- Semi-open intervals, with possibly infinite bounds

-- Previous versions of Interval used ≼ rather than ≺ 
-- (that is, empty intervals were supported) but
-- MSet has been written to avoid requiring empty intervals.

data Interval : Set where
  [_⟩ : ∀ {s t} → .(s ≺ t) → Interval

lb : Interval → Time∞
lb ([_⟩ {s} {t} s≺t) = s

ub : Interval → Time∞
ub ([_⟩ {s} {t} s≺t) = t

.lb≺ub : ∀ i → (lb i ≺ ub i)
lb≺ub [ s≺t ⟩ = irrelevant s≺t

-- Semantics of intervals

data Int∞ (i : Interval) (t : Time∞) : Set where
  _,_ : .(lb i ≼ t) → .(t ≺ ub i) → (t ∈ Int∞ i)

Int : Interval → Time → Set
Int i t = fin t ∈ Int∞ i

.lb≼ : ∀ {t i} → (t ∈ Int i) → (lb i ≼ fin t)
lb≼ (s≼t , t≺u) = irrelevant s≼t

.≺ub : ∀ {t i} → (t ∈ Int i) → (fin t ≺ ub i)
≺ub (s≼t , t≺u) = irrelevant t≺u

-- Ordering on intervals

data _⊑_ (i j : Interval) : Set where
  _,_ : .(lb j ≼ lb i) → .(ub i ≼ ub j) → (i ⊑ j)

⊑-refl : ∀ {i} → (i ⊑ i)
⊑-refl = (≼-refl , ≼-refl)

_⊑-trans_ : ∀ {i j k} → (i ⊑ j) → (j ⊑ k) → (i ⊑ k)
(sj≼si , ui≼uj) ⊑-trans (sk≼sj , uj≼uk) =
  (sk≼sj ≼-trans sj≼si , ui≼uj ≼-trans uj≼uk)

.⊑-impl-≼ : ∀ {i j} → (i ⊑ j) → (ub i ≼ ub j)
⊑-impl-≼ (lj≼li , ui≼uj) = irrelevant ui≼uj

.⊑-impl-≽ : ∀ {i j} → (i ⊑ j) → (lb j ≼ lb i)
⊑-impl-≽ (lj≼li , ui≼uj) = irrelevant lj≼li

-- When do two intervals abut?

_~_ : Interval → Interval → Set
i ~ j = ub i ≡ lb j

-- Concatenation of intervals

_⌢_∵_ : ∀ i j → (i ~ j) → Interval
i ⌢ j ∵ i~j = [ lb≺ub i ≺-trans ≡-impl-≼ i~j ≺-transʳ lb≺ub j ⟩

⌢-inj₁ : ∀ i j i~j → (i ⊑ (i ⌢ j ∵ i~j))
⌢-inj₁ [ s≺t ⟩ [ t≺u ⟩ refl = (≼-refl , ≺-impl-≼ t≺u)

⌢-inj₂ : ∀ i j i~j → (j ⊑ (i ⌢ j ∵ i~j))
⌢-inj₂ [ s≺t ⟩ [ t≺u ⟩ refl = (≺-impl-≼ s≺t , ≼-refl)

-- Up-closure of a time

↑ : Time → Interval
↑ t = [ t≺+∞ {t} ⟩

-- Singleton interval

sing : Time → Interval
sing t = [ t≺t+1 {t} ⟩