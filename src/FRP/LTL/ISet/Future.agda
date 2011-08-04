open import FRP.LTL.ISet.Core using ( ISet ; ⌈_⌉ ; ⌊_⌋ )
open import FRP.LTL.RSet using ( RSet )
open import FRP.LTL.Time using ( Time ; _≤_ )

module FRP.LTL.ISet.Future where

data Future (A : RSet) (t : Time) : Set where
  _,_ : ∀ {u} .(t≤u : t ≤ u) → A u → Future A t

◇ : ISet → ISet
◇ A = ⌈ Future ⌊ A ⌋ ⌉