open import Data.Product using ( _,_ )
open import Data.Unit using ( ⊤ ; tt )
open import FRP.LTL.ISet.Core using ( ISet ; [_] ; _,_ )

module FRP.LTL.ISet.Unit where

T : ISet
T = [ (λ i → ⊤) , (λ i j i~j t → (tt , tt)) , (λ i j i⊑j t → tt) ]

