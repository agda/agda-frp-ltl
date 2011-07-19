open import Data.Product using ( _×_ ; _,_ )
open import FRP.LTL.Time.Interval using ( _~_ ; _⌢_∵_ )
open import FRP.LTL.ISet.Core using ( ISet ; [_] ; _,_ ; M⟦_⟧ ; idM⟦_⟧ ; compM⟦_⟧ ; splitM⟦_⟧ )

module FRP.LTL.ISet.Product where

_∧_ : ISet → ISet → ISet
A ∧ B = [ (λ i → M⟦ A ⟧ i × M⟦ B ⟧ i) , id , comp , split ] where

  id : ∀ i → (i ~ i) → (M⟦ A ⟧ i × M⟦ B ⟧ i)
  id i i~i = (idM⟦ A ⟧ i i~i , idM⟦ B ⟧ i i~i)

  comp : ∀ i j i~j → 
    ((M⟦ A ⟧ i × M⟦ B ⟧ i) × (M⟦ A ⟧ j × M⟦ B ⟧ j)) → 
      (M⟦ A ⟧ (i ⌢ j ∵ i~j) × M⟦ B ⟧ (i ⌢ j ∵ i~j))
  comp i j i~j ((σ₁ , τ₁) , (σ₂ , τ₂)) = 
    (compM⟦ A ⟧ i j i~j (σ₁ , σ₂) , compM⟦ B ⟧ i j i~j (τ₁ , τ₂))

  split : ∀ i j i~j → 
    (M⟦ A ⟧ (i ⌢ j ∵ i~j) × M⟦ B ⟧ (i ⌢ j ∵ i~j)) → 
      ((M⟦ A ⟧ i × M⟦ B ⟧ i) × (M⟦ A ⟧ j × M⟦ B ⟧ j)) 
  split i j i~j (σ , τ) with splitM⟦ A ⟧ i j i~j σ | splitM⟦ B ⟧ i j i~j τ
  split i j i~j (σ , τ) | (σ₁ , σ₂) | (τ₁ , τ₂) = ((σ₁ , τ₁) , (σ₂ , τ₂))
   
