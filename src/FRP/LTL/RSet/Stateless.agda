open import FRP.LTL.RSet.Core using ( RSet )

module FRP.LTL.RSet.Stateless where

infixr 1 _⇒_

_⇒_ : RSet → RSet → RSet
(A ⇒ B) t = A t → B t

