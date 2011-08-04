open import Data.Product using ( _×_ )
open import FRP.LTL.ISet.Core using ( ISet ; ⌈_⌉ ; M⟦_⟧ )
open import FRP.LTL.Time using ( Time ; _≤_ )
open import FRP.LTL.Time.Bound using ( ≤-impl-≼ )
open import FRP.LTL.Time.Interval using ( [_⟩ ; sing )

module FRP.LTL.ISet.Until where

data _Until_ (A B : ISet) (t : Time) : Set where
  _,_ : ∀ {u} .(t≤u : t ≤ u) → (M⟦ A ⟧ [ ≤-impl-≼ t≤u ⟩ × M⟦ B ⟧ (sing u)) → (A Until B) t

_U_ : ISet → ISet → ISet
A U B = ⌈ A Until B ⌉