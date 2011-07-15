open import Data.Product using ( ∃ ; _×_ )
open import FRP.LTL.RSet.Core using ( RSet ; _[_,_⟩ )
open import FRP.LTL.Time using ( _≤_ )

module FRP.LTL.RSet.Until where

infixr 2 _U_

_U_ : RSet → RSet → RSet
(A U B) t = ∃ λ u → (t ≤ u) × (A [ t , u ⟩) × B u

