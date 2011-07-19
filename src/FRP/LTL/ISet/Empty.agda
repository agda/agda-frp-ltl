open import Data.Product using ( _×_ ; _,_ )
open import Data.Empty using ( ⊥ )
open import FRP.LTL.ISet.Core using ( ISet ; [_] ; _,_ )
open import FRP.LTL.Time.Bound using ( _≼-asym_ )
open import FRP.LTL.Time.Interval using ( [_⟩ ; _~_ )
open import FRP.LTL.Util using ( ≡-relevant )
open import Relation.Binary.PropositionalEquality using ( refl )

module FRP.LTL.ISet.Empty where

F : ISet
F = [ (λ i → i ~ i) , id , comp , split ] where

  id : ∀ i → (i ~ i) → (i ~ i)
  id i i~i = i~i

  comp : ∀ i j → (i ~ j) → ((i ~ i) × (j ~ j)) → (j ~ i)
  comp [ s≼t ⟩ [ t≼u ⟩ refl (refl , refl) = refl

  split : ∀ i j → (i ~ j) → (j ~ i) → ((i ~ i) × (j ~ j))
  split [ s≼t ⟩ [ t≼s ⟩ refl refl = (≡-relevant (t≼s ≼-asym s≼t) , ≡-relevant (s≼t ≼-asym t≼s))


