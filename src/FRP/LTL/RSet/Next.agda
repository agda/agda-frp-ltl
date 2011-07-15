open import FRP.LTL.RSet.Core using ( RSet )
open import FRP.LTL.Time using ( _+_ )

module FRP.LTL.RSet.Next where

○ : RSet → RSet
○ A t = A (t + 1)

