open import Data.Product using ( _×_ )
open import FRP.LTL.ISet.Core using ( ISet ; ⌈_⌉ ; M⟦_⟧ )
open import FRP.LTL.Time using ( Time )
open import FRP.LTL.Time.Bound using ( fin ; _≺_ )
open import FRP.LTL.Time.Interval using ( [_⟩ ; sing )

module FRP.LTL.ISet.Until where

data _Until_ (A B : ISet) (t : Time) : Set where
  now : M⟦ B ⟧ (sing t) → (A Until B) t
  later : ∀ {u} → .(t≺u : fin t ≺ fin u) → M⟦ A ⟧ [ t≺u ⟩ → M⟦ B ⟧ (sing u) → (A Until B) t

_U_ : ISet → ISet → ISet
A U B = ⌈ A Until B ⌉