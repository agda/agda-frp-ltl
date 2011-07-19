open import Data.Product using ( _,_ )
open import FRP.LTL.ISet.Core using ( ISet ; _⇛_ ; mset )

module FRP.LTL.ISet.Stateless where

_⇒_ : ISet → ISet → ISet
A ⇒ B = mset A ⇛ B