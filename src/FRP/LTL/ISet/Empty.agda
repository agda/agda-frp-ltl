open import Data.Product using ( _,_ )
open import Data.Empty using ( ⊥ )
open import FRP.LTL.ISet.Core using ( ISet ; [_] ; _,_ )

module FRP.LTL.ISet.Empty where

F : ISet
F = [ (λ i → ⊥) , (λ i j i~j → λ ()) , (λ i j i⊑j → λ ()) ]
