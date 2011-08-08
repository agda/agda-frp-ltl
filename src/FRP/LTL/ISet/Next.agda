open import Data.Product using ( _×_ ; _,_ )
open import FRP.LTL.ISet.Core using ( ISet ; MSet ; [_] ; _⇛_ ; _,_ )
open import FRP.LTL.Time using ( _+_ ; +-resp-≤ ; +-resp-< )
open import FRP.LTL.Time.Bound using
  ( Time∞ ; +∞ ; fin ; _≼_ ; _≺_ ; +∞-top ; ≤-impl-≼ ; t≺+∞ ; ≺-impl-⋡ ; ≺-impl-< ; <-impl-≺ )
open import FRP.LTL.Time.Interval using ( Interval ; [_⟩ ; _⊑_ ; _~_ ; _⌢_∵_ ; _,_ )
open import FRP.LTL.Util using ( ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( refl )

module FRP.LTL.ISet.Next where

-- ○ A is "A holds at the next point in time"

next : Time∞ → Time∞
next +∞      = +∞
next (fin t) = fin (t + 1)

next-resp-≼ : ∀ {t u} → (t ≼ u) → (next t ≼ next u)
next-resp-≼ +∞-top         = +∞-top
next-resp-≼ (≤-impl-≼ t≤u) = ≤-impl-≼ (+-resp-≤ t≤u 1)

next-resp-≺ : ∀ {t u} → (t ≺ u) → (next t ≺ next u)
next-resp-≺ {+∞}            t≺u = ⊥-elim (≺-impl-⋡ t≺u +∞-top)
next-resp-≺ {fin t} {+∞}    t≺u = t≺+∞
next-resp-≺ {fin t} {fin u} t≺u = <-impl-≺ (+-resp-< (≺-impl-< t≺u) 1)

Next : MSet → MSet
Next (A , split , subsum) = (○A , ○split , ○subsum) where

  ○A : Interval → Set
  ○A [ s≺t ⟩ = A [ next-resp-≺ s≺t ⟩

  ○split : ∀ i j i~j → ○A (i ⌢ j ∵ i~j) → (○A i × ○A j)
  ○split [ s≺t ⟩ [ t≺u ⟩ refl = 
    split [ next-resp-≺ s≺t ⟩ [ next-resp-≺ t≺u ⟩ refl

  ○subsum : ∀ i j → (i ⊑ j) → ○A j → ○A i
  ○subsum [ s≺t ⟩ [ r≺u ⟩ (r≼s , t≼u) = 
    subsum [ next-resp-≺ s≺t ⟩ [ next-resp-≺ r≺u ⟩ (next-resp-≼ r≼s , next-resp-≼ t≼u)

○ : ISet → ISet
○ ([ A ]) = [ Next A ]
○ (A ⇛ B) = Next A ⇛ ○ B
