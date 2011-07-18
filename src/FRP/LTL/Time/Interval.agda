open import FRP.LTL.Time using ( Time )
open import FRP.LTL.Time.Bound using ( Time∞ ; _≼_ ; _≺_ ; fin ; ≼-refl ; _≼-trans_ ; ≡-impl-≼ )
open import FRP.LTL.Util using ( irrelevant )
open import Relation.Unary using ( _∈_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

module FRP.LTL.Time.Interval where

infixr 2 _⊑_ _⇝_
infixr 4 _,_ _++_∵_

-- Semi-open intervals, with possibly infinite bounds

data Interval : Set where
  [_⟩ : ∀ {s t} → .(s ≼ t) → Interval

lb : Interval → Time∞
lb ([_⟩ {s} {t} s≼t) = s

ub : Interval → Time∞
ub ([_⟩ {s} {t} s≼t) = t

.int-≼ : ∀ i → (lb i ≼ ub i)
int-≼ [ s≼t ⟩ = irrelevant s≼t

-- Semantics of intervals

data Int∞ (i : Interval) (t : Time∞) : Set where
  _,_ : (lb i ≼ t) → (t ≺ ub i) → (t ∈ Int∞ i)

Int : Interval → Time → Set
Int i t = fin t ∈ Int∞ i

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

_⇝_ : Interval → Interval → Set
i ⇝ j = ub i ≡ lb j

-- Concatenation of intervals

_++_∵_ : ∀ i j → .(i ⇝ j) → Interval
i ++ j ∵ i⇝j = [ int-≼ i ≼-trans ≡-impl-≼ i⇝j ≼-trans int-≼ j ⟩
