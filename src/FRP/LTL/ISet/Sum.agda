open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂  )
open import FRP.LTL.Time.Interval using ( _~_ ; _⌢_∵_ )
open import FRP.LTL.ISet.Core using 
  ( ISet ; IList ; [_] ; _,_ ; M⟦_⟧ ; idList ; compList ; splitList ; splitM⟦_⟧ )

module FRP.LTL.ISet.Sum where

_∨_ : ISet → ISet → ISet
A ∨ B = [ IList (λ i → M⟦ A ⟧ i ⊎ M⟦ B ⟧ i) , idList , compList , splitList split ] where

  split : ∀ i j i~j → 
    (M⟦ A ⟧ (i ⌢ j ∵ i~j) ⊎ M⟦ B ⟧ (i ⌢ j ∵ i~j)) → 
      ((M⟦ A ⟧ i ⊎ M⟦ B ⟧ i) × (M⟦ A ⟧ j ⊎ M⟦ B ⟧ j)) 
  split i j i~j (inj₁ σ) with splitM⟦ A ⟧ i j i~j σ
  split i j i~j (inj₁ σ) | (σ₁ , σ₂) = (inj₁ σ₁ , inj₁ σ₂)
  split i j i~j (inj₂ τ) with splitM⟦ B ⟧ i j i~j τ
  split i j i~j (inj₂ τ) | (τ₁ , τ₂) = (inj₂ τ₁ , inj₂ τ₂)
   
