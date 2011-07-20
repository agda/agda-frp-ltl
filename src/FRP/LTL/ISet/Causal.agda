open import Coinduction using ( ∞ ; ♯_ ; ♭ )
open import Data.Product using ( _×_ ; _,_ ; proj₂ )
open import FRP.LTL.ISet.Core using ( ISet ; M⟦_⟧ ; ⟦_⟧ ; ⌈_⌉ ; _,_ ; splitM⟦_⟧ ) renaming ( [_] to ⟪_⟫ )
open import FRP.LTL.ISet.Globally using ( □ ; [_] )
open import FRP.LTL.ISet.Stateless using ( _⇒_ ; _$_  )
open import FRP.LTL.RSet.Core using ( RSet )
open import FRP.LTL.Time.Bound using 
  ( Time∞ ; fin ; +∞ ; _≺_ ; _≼_ ; +∞-top ; ≺-impl-≼ ; ≼-refl ; _≼-trans_ ; ≺-impl-≢ ; ≡-impl-≽ ; ∞≼-impl-≡∞ ; t≺+∞ )
open import FRP.LTL.Time.Interval using ( [_⟩ ; Int ; ↑ )
open import FRP.LTL.Util using ( ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Unary using ( _∈_ )

module FRP.LTL.ISet.Causal where

infixr 2 _⊵_
infixr 3 _⋙_ _≫_

-- A ⊵ B is the causal function space from A to B

data _∙_⊸_∙_ (A : ISet) (s : Time∞) (B : ISet) (u : Time∞) : Set where
  inp : .(s ≼ u) → .(u ≺ +∞) → 
    (∀ {t} .(s≺t : s ≺ t) → M⟦ A ⟧ [ ≺-impl-≼ s≺t ⟩ → ∞ (A ∙ t ⊸ B ∙ u)) → 
      (A ∙ s ⊸ B ∙ u)
  out : ∀ {v} .(u≺v : u ≺ v) → 
    M⟦ B ⟧ [ ≺-impl-≼ u≺v ⟩ → ∞ (A ∙ s ⊸ B ∙ v) → 
      (A ∙ s ⊸ B ∙ u)
  done : .(u ≡ +∞) → 
    (A ∙ s ⊸ B ∙ u)

_⊵_ : ISet → ISet → ISet
A ⊵ B = ⌈ (λ t → A ∙ fin t ⊸ B ∙ fin t) ⌉

-- Categorical structure

ar : ∀ {A B} t → M⟦ A ⇒ B ⟧ (↑ t) → (A ∙ t ⊸ B ∙ t)
ar {A} {B} +∞      f = done refl
ar {A} {B} (fin t) f = inp ≼-refl t≺+∞ P where

  P : ∀ {u} .t≺u → M⟦ A ⟧ [ ≺-impl-≼ t≺u ⟩ → ∞ (A ∙ u ⊸ B ∙ fin t)
  P {u} t≺u σ with splitM⟦ A ⇒ B ⟧ [ ≺-impl-≼ t≺u ⟩ (↑ u) refl f
  P {u} t≺u σ | (f₁ , f₂) = ♯ out t≺u (f₁ $ σ) (♯ ar u f₂)

arr : ∀ {A B} → ⟦ □ (A ⇒ B) ⇒ (A ⊵ B) ⟧
arr ⟪ ⟪ f ⟫ ⟫ = ⟪ (λ t t∈i → ar (fin t) (f t t∈i) ) ⟫

-- We could define id in terms of arr, but we define it explictly for efficiency.

id : ∀ {A} t → (A ∙ t ⊸ A ∙ t)
id +∞      = done refl
id (fin t) = inp ≼-refl t≺+∞ (λ {u} t≺u σ → ♯ out t≺u σ (♯ id u))

identity : ∀ {A} → ⟦ A ⊵ A ⟧
identity {A} = ⟪ (λ t t∈i → id (fin t)) ⟫

-- Composition requires a well-ordering proof in the case of output
-- from the LHS being fed as intput to the RHS, to ensure there isn't
-- an infinite amount of chatter.

_≫_ : ∀ {A B C s t u} → (A ∙ s ⊸ B ∙ t) → (B ∙ t ⊸ C ∙ u) → (A ∙ s ⊸ C ∙ u)
inp s≼t t≺∞ P ≫ inp t≼u u≺∞ Q = inp (s≼t ≼-trans t≼u) u≺∞ (λ s≺v σ → ♯ (♭ (P s≺v σ) ≫ inp t≼u u≺∞ Q))
inp s≼t t≺∞ P ≫ out u≺w τ Q   = out u≺w τ (♯(inp s≼t t≺∞ P ≫ ♭ Q))
inp s≼t t≺∞ P ≫ done u≡∞      = done u≡∞
out t≺v σ P   ≫ inp t≼u u≺∞ Q = ♭ P ≫ ♭ (Q t≺v σ) -- need to use well-ordering here
out t≺v σ P   ≫ out u≺w τ Q   = out u≺w τ (♯ (out t≺v σ P ≫ ♭ Q))
out t≺v σ P   ≫ done u≡∞      = done u≡∞
done t≡∞      ≫ inp t≼u u≺∞ Q = ⊥-elim (≺-impl-≢ u≺∞ (∞≼-impl-≡∞ (≡-impl-≽ t≡∞ ≼-trans t≼u)))
done t≡∞      ≫ out u≺w τ Q   = out u≺w τ (♯ (done t≡∞ ≫ ♭ Q))
done t≡∞      ≫ done u≡∞      = done u≡∞

_⋙_ : ∀ {A B C} → ⟦ (A ⊵ B) ⇒ (B ⊵ C) ⇒ (A ⊵ C) ⟧
(⟪ ⟪ f ⟫ ⟫ ⋙ ⟪ ⟪ g ⟫ ⟫) = ⟪ (λ t t∈i → f t t∈i ≫ g t t∈i) ⟫
