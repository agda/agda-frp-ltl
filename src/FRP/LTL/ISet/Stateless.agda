open import Data.Product using ( _,_ )
open import FRP.LTL.ISet.Core using ( ISet ; _⇛_ ; mset ; M⟦_⟧ ; ⟦_⟧ ; [_] ; i→m ; ⊑-subsum )

module FRP.LTL.ISet.Stateless where

infixr 2 _⇒_

_⇒_ : ISet → ISet → ISet
A ⇒ B = mset A ⇛ B

_$_ : ∀ {A B i} → M⟦ A ⇒ B ⟧ i → M⟦ A ⟧ i → M⟦ B ⟧ i
f $ σ = i→m (λ j j⊑i → f j j⊑i [ ⊑-subsum j⊑i σ ])
