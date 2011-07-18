open import Data.Product using ( ∃ ; _×_ )
open import FRP.LTL.RSet.Core using ( RSet ; _[_,_] ; ⟦_⟧ )
open import FRP.LTL.RSet.Stateless using ( _⇒_ )
open import FRP.LTL.RSet.Globally using ( □ ; [_] )
open import FRP.LTL.Time using ( _≤_ ; ≤-refl ; _≤-trans_ )

module FRP.LTL.RSet.Causal where

infixr 2 _⊵_
infixr 3 _⋙_

-- A ⊵ B is the causal function space from A to B

_⊵_ : RSet → RSet → RSet
(A ⊵ B) t = ∀ {u} → (t ≤ u) → (A [ t , u ]) → B u

-- Categorical structure

arr : ∀ {A B} → ⟦ □ (A ⇒ B) ⇒ (A ⊵ B) ⟧
arr f s≤t σ = f s≤t (σ s≤t ≤-refl)

identity : ∀ {A} → ⟦ A ⊵ A ⟧
identity {A} = arr [( λ {u} (a : A u) → a )]

_before_ : ∀ {A s u v} → (A [ s , v ]) → (u ≤ v) → (A [ s , u ])
(σ before u≤v) s≤t t≤u = σ s≤t (t≤u ≤-trans u≤v)

_after_ : ∀ {A s t v} → (A [ s , v ]) → (s ≤ t) → (A [ t , v ])
(σ after s≤t) t≤u u≤v = σ (s≤t ≤-trans t≤u) u≤v

_$_ : ∀ {A B s u} → (A ⊵ B) s → (A [ s , u ]) → (B [ s , u ])
(f $ σ) s≤t t≤u = f s≤t (σ before t≤u)

_⋙_ : ∀ {A B C} → ⟦ (A ⊵ B) ⇒ (B ⊵ C) ⇒ (A ⊵ C) ⟧
(f ⋙ g) s≤t σ = g s≤t (f $ σ) 
