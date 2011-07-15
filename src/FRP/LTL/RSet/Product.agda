open import Data.Product using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import FRP.LTL.RSet.Core using ( RSet ; ⟦_⟧ )
open import FRP.LTL.RSet.Globally using ( [_] )
open import FRP.LTL.RSet.Causal using ( _⊵_ ; arr )
open import FRP.LTL.RSet.Stateless using ( _⇒_ )

module FRP.LTL.RSet.Product where

infixr 2 _∧_

-- Conjunction of LTL formulae

_∧_ : RSet → RSet → RSet
(A ∧ B) t = A t × B t

-- Product structure

fst : ∀ {A B} → ⟦ (A ∧ B) ⊵ A ⟧
fst {A} {B} = arr [ (λ {u} (ab : A u × B u) → proj₁ ab) ]

snd : ∀ {A B} → ⟦ (A ∧ B) ⊵ B ⟧
snd {A} {B} = arr [ (λ {u} (ab : A u × B u) → proj₂ ab) ]

_&&&_ :  ∀ {A B C} → ⟦ (A ⊵ B) ⇒ (A ⊵ C) ⇒ (A ⊵ (B ∧ C)) ⟧
(f &&& g) s≤t σ = (f s≤t σ , g s≤t σ)