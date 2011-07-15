open import Data.Sum using ( _⊎_ )
open import FRP.LTL.RSet.Core using ( RSet )

module FRP.LTL.RSet.Sum where

infixr 2 _∨_

_∨_ : RSet → RSet → RSet
(A ∨ B) t = A t ⊎ B t

