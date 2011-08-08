open import Data.Product using ( _,_ )
open import FRP.LTL.ISet.Core using ( ISet ; _⇛_ ; mset ; M⟦_⟧ ; ⟦_⟧ ; [_] ; subsumM⟦_⟧ )
open import FRP.LTL.Time.Interval using ( ⊑-refl )

module FRP.LTL.ISet.Stateless where

infixr 2 _⇒_

_⇒_ : ISet → ISet → ISet
A ⇒ B = mset A ⇛ B

-- We could define $ as
-- f $ σ = i→m (λ j j⊑i → f j j⊑i [ subsumM⟦ A ⟧ j i j⊑i σ ])
-- but we inline i→m for efficiency

_$_ : ∀ {A B i} → M⟦ A ⇒ B ⟧ i → M⟦ A ⟧ i → M⟦ B ⟧ i
_$_ {A} {[ B ]} {i} f σ = f i ⊑-refl [ σ ]
_$_ {A} {B ⇛ C} {i} f σ = λ j j⊑i → f j j⊑i [ subsumM⟦ A ⟧ j i j⊑i σ ]