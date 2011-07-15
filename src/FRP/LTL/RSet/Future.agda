open import Data.Product using ( ∃ ; _×_ )
open import FRP.LTL.RSet.Core using ( RSet )
open import FRP.LTL.Time using ( _≤_ )

module FRP.LTL.RSet.Future where

◇ : RSet → RSet
◇ A t = ∃ λ u → (t ≤ u) × A u

