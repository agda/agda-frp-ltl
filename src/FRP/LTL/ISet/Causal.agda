open import Coinduction using ( ∞ ; ♯_ ; ♭ )
open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₂ )
open import Data.Nat using ( ℕ ; zero ; suc )
open import Data.Empty using ( ⊥ )
open import FRP.LTL.ISet.Core using ( ISet ; M⟦_⟧ ; ⟦_⟧ ; ⌈_⌉ ; _,_ ; splitM⟦_⟧ ) renaming ( [_] to ⟪_⟫ )
open import FRP.LTL.ISet.Globally using ( □ ; [_] )
open import FRP.LTL.ISet.Stateless using ( _⇒_ ; _$_  )
open import FRP.LTL.RSet.Core using ( RSet )
open import FRP.LTL.Time.Bound using 
  ( Time∞ ; fin ; +∞ ; _≺_ ; _≼_ ; _⋠_ ; ≺-Indn ; _,_
  ; ≺-impl-≼ ; ≼-refl ; _≼-trans_ ; ≡-impl-≽ ; ≺-impl-≢ ; ≺-impl-⋡ ; t≺+∞ ; ∞≼-impl-≡∞ ; ≺-indn )
open import FRP.LTL.Time.Interval using ( [_⟩ ; Int ; ↑ )
open import FRP.LTL.Util using ( ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Unary using ( _∈_ )

module FRP.LTL.ISet.Causal where

infixr 2 _⊵_ 
infixr 3 _⋙_ _≫_ _⊨_≫_

-- A ⊵ B is the causal function space from A to B

data _∙_⊸_∙_ (A : ISet) (s : Time∞) (B : ISet) (u : Time∞) : Set where
  inp : .(s ≼ u) → .(u ≺ +∞) → 
    (∀ {t} .(s≺t : s ≺ t) → M⟦ A ⟧ [ s≺t ⟩ → ∞ (A ∙ t ⊸ B ∙ u)) → 
      (A ∙ s ⊸ B ∙ u)
  out : ∀ {v} .(u≺v : u ≺ v) → 
    M⟦ B ⟧ [ u≺v ⟩ → ∞ (A ∙ s ⊸ B ∙ v) → 
      (A ∙ s ⊸ B ∙ u)
  done : .(u ≡ +∞) → 
    (A ∙ s ⊸ B ∙ u)

_⊵_ : ISet → ISet → ISet
A ⊵ B = ⌈ (λ t → A ∙ fin t ⊸ B ∙ fin t) ⌉

-- Categorical structure

ar : ∀ {A B} t → M⟦ A ⇒ B ⟧ (↑ t) → (A ∙ fin t ⊸ B ∙ fin t)
ar {A} {B} t f = inp ≼-refl t≺+∞ P where

  P : ∀ {u} .(t≺u : fin t ≺ u) → M⟦ A ⟧ [ t≺u ⟩ → ∞ (A ∙ u ⊸ B ∙ fin t)
  P {+∞}    t≺u σ = ♯ out t≺u (f $ σ) (♯ done refl)
  P {fin u} t≺u σ with splitM⟦ A ⇒ B ⟧ [ t≺u ⟩ (↑ u) refl f
  P {fin u} t≺u σ | (f₁ , f₂) = ♯ out t≺u (f₁ $ σ) (♯ ar u f₂)

arr : ∀ {A B} → ⟦ □ (A ⇒ B) ⇒ (A ⊵ B) ⟧
arr ⟪ ⟪ f ⟫ ⟫ = ⟪ (λ t t∈i → ar t (f t t∈i) ) ⟫

-- We could define id in terms of arr, but we define it explictly for efficiency.

id : ∀ {A} t → (A ∙ t ⊸ A ∙ t)
id +∞      = done refl
id (fin t) = inp ≼-refl t≺+∞ (λ {u} t≺u σ → ♯ out t≺u σ (♯ id u))

identity : ∀ {A} → ⟦ A ⊵ A ⟧
identity = ⟪ (λ t t∈i → id (fin t)) ⟫

-- The following typechecks but does not pass the termination checker,
-- due to the possibility of infinite left-to-right chatter:

-- _≫_ : ∀ {A B C s t u} → (A ∙ s ⊸ B ∙ t) → (B ∙ t ⊸ C ∙ u) → (A ∙ s ⊸ C ∙ u)
-- P             ≫ out u≺w τ Q   = out u≺w τ (♯ (P ≫ ♭ Q))
-- P             ≫ done u≡∞      = done u≡∞
-- inp s≼t t≺∞ P ≫ inp t≼u u≺∞ Q = inp (s≼t ≼-trans t≼u) u≺∞ (λ s≺v σ → ♯ (♭ (P s≺v σ) ≫ inp t≼u u≺∞ Q))
-- done t≡∞      ≫ inp t≼u u≺∞ Q = ⊥-elim (≺-impl-≢ u≺∞ (∞≼-impl-≡∞ (≡-impl-≽ t≡∞ ≼-trans t≼u)))
-- out t≺v σ P   ≫ inp t≼u u≺∞ Q = out t≺v σ P ≫ inp t≼u u≺∞ Q

-- We have to be explicit about the induction scheme in the case of left-to-right
-- communication, which is because, for any t and u ≺ ∞, there is a bound
-- on the length of any ≺-chain between t and u.

mutual

  _⊨_≫_ : ∀ {A B C s t u} → (≺-Indn t u) → (A ∙ s ⊸ B ∙ t) → (B ∙ t ⊸ C ∙ u) → (A ∙ s ⊸ C ∙ u)
  n     , t+n≻u   ⊨ P             ≫ out u≺w τ Q   = out u≺w τ (♯ (P ≫ ♭ Q))
  n     , t+n≻u   ⊨ P             ≫ done u≡∞      = done u≡∞
  n     , t+n≻u   ⊨ inp s≼t t≺∞ P ≫ inp t≼u u≺∞ Q = inp (s≼t ≼-trans t≼u) u≺∞ (λ s≺v σ → ♯ (♭ (P s≺v σ) ≫ inp t≼u u≺∞ Q))
  n     , t+n≻u   ⊨ done t≡∞      ≫ inp t≼u u≺∞ Q = ⊥-elim (≺-impl-≢ u≺∞ (∞≼-impl-≡∞ (≡-impl-≽ t≡∞ ≼-trans t≼u)))
  zero  , u≺t     ⊨ out t≺v σ P   ≫ inp t≼u u≺∞ Q = ⊥-elim (≺-impl-⋡ u≺t t≼u)
  suc n , t+1+n≻u ⊨ out t≺v σ P   ≫ inp t≼u u≺∞ Q = n , t+1+n≻u t≺v ⊨ ♭ P ≫ ♭ (Q t≺v σ)

  _≫_ : ∀ {A B C s t u} → (A ∙ s ⊸ B ∙ t) → (B ∙ t ⊸ C ∙ u) → (A ∙ s ⊸ C ∙ u)
  P             ≫ out u≺w τ Q   = out u≺w τ (♯ (P ≫ ♭ Q))
  P             ≫ done u≡∞      = done u≡∞
  inp s≼t t≺∞ P ≫ inp t≼u u≺∞ Q = inp (s≼t ≼-trans t≼u) u≺∞ (λ s≺v σ → ♯ (♭ (P s≺v σ) ≫ inp t≼u u≺∞ Q))
  done t≡∞      ≫ inp t≼u u≺∞ Q = ⊥-elim (≺-impl-≢ u≺∞ (∞≼-impl-≡∞ (≡-impl-≽ t≡∞ ≼-trans t≼u)))
  out t≺v σ P   ≫ inp t≼u u≺∞ Q = ≺-indn u≺∞ ⊨ out t≺v σ P ≫ inp t≼u u≺∞ Q

_⋙_ : ∀ {A B C} → ⟦ (A ⊵ B) ⇒ (B ⊵ C) ⇒ (A ⊵ C) ⟧
(⟪ ⟪ f ⟫ ⟫ ⋙ ⟪ ⟪ g ⟫ ⟫) = ⟪ (λ t t∈i → f t t∈i ≫ g t t∈i) ⟫

-- Apply a process to some of its output

_/_/_ : ∀ {A B s t u} → (A ∙ s ⊸ B ∙ u) → .(s≺t : s ≺ t) → M⟦ A ⟧ [ s≺t ⟩ → (A ∙ t ⊸ B ∙ u)
inp s≼u u≺∞ P / s≺t / σ = ♭ (P s≺t σ)
out u≺v τ P   / s≺t / σ = out u≺v τ (♯ (♭ P / s≺t / σ))
done u≡∞      / s≺t / σ = done u≡∞
