open import Data.Product using ( _×_ ; _,_ )
open import FRP.LTL.ISet.Core using ( ISet ; MSet ; [_] ; _⇛_ ; _,_ )
open import FRP.LTL.Time using ( _+_ ; +-resp-≤ )
open import FRP.LTL.Time.Bound using ( Time∞ ; +∞ ; fin ; _≼_ ; +∞-top ; ≤-impl-≼ ; ≼-refl )
open import FRP.LTL.Time.Interval using ( Interval ; [_⟩ ; _~_ ; _⌢_∵_ )
open import Relation.Binary.PropositionalEquality using ( refl )

module FRP.LTL.ISet.Next where

-- ○ A is "A holds at the next point in time"

next : Time∞ → Time∞
next +∞      = +∞
next (fin t) = fin (t + 1)

next-resp-≼ : ∀ {t u} → (t ≼ u) → (next t ≼ next u)
next-resp-≼ +∞-top         = +∞-top
next-resp-≼ (≤-impl-≼ t≤u) = ≤-impl-≼ (+-resp-≤ t≤u 1)

Next : MSet → MSet
Next (A , id , comp , split) = (○A , ○id , ○comp , ○split) where

  ○A : Interval → Set
  ○A [ s≼t ⟩ = A [ next-resp-≼ s≼t ⟩

  ○id : ∀ i → (i ~ i) → ○A i
  ○id [ s≼t ⟩ refl = id [ ≼-refl ⟩ refl

  ○comp : ∀ i j i~j → (○A i × ○A j) → ○A (i ⌢ j ∵ i~j)
  ○comp [ s≼t ⟩ [ t≼u ⟩ refl = comp [ next-resp-≼ s≼t ⟩ [ next-resp-≼ t≼u ⟩ refl

  ○split : ∀ i j i~j → ○A (i ⌢ j ∵ i~j) → (○A i × ○A j)
  ○split [ s≼t ⟩ [ t≼u ⟩ refl = split [ next-resp-≼ s≼t ⟩ [ next-resp-≼ t≼u ⟩ refl

○ : ISet → ISet
○ ([ A ]) = [ Next A ]
○ (A ⇛ B) = Next A ⇛ ○ B
