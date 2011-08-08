open import Data.Product using ( _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import FRP.LTL.ISet.Core using 
  ( ISet ; I⟦_⟧ ; M⟦_⟧ ; ⟦_⟧ ; ⌈_⌉ ; splitM⟦_⟧ ; subsumM⟦_⟧ ; i→m ; m→i ) renaming 
  ( [_] to [_]′ )
open import FRP.LTL.ISet.Stateless using ( _⇒_ ; _$_ )
open import FRP.LTL.Time.Bound using ( fin ; +∞ ; +∞-top ; ≼-refl ; _≼-trans_ ; _≼-total_ ; _≼-asym_ ; ≺-impl-⋡ )
open import FRP.LTL.Time.Interval using ( ↑ ; [_⟩; _⊑_ ; lb≺ub ; lb≼ ; _,_ ; Int )
open import FRP.LTL.Util using ( ≡-relevant ; ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ )

module FRP.LTL.ISet.Globally where

-- □ A is "A holds globally in the future"

□ : ISet → ISet
□ A = ⌈( λ t → M⟦ A ⟧ (↑ t) )⌉

-- Comonad structure of □

extend : ∀ {A B} → ⟦ A ⇒ B ⟧ → ⟦ □ A ⇒ □ B ⟧
extend {A} {B} f [ [ σ ]′ ]′ =
  [ (λ t t∈i → i→m (λ j j⊑↑t → f [ subsumM⟦ A ⟧ j (↑ t) j⊑↑t (σ t t∈i) ]′)) ]′

extract : ∀ {A} → ⟦ □ A ⇒ A ⟧
extract {A} {[_⟩ {fin s} {t} s≺t} [ [ σ ]′ ]′ = 
  m→i (subsumM⟦ A ⟧ [ s≺t ⟩ (↑ s) (≼-refl , +∞-top) (σ s (≼-refl , s≺t)))
extract {A} {[_⟩ {+∞}    {t} ∞≺t} [ [ σ ]′ ]′ = 
  ⊥-elim (≺-impl-⋡ ∞≺t +∞-top)

duplicate : ∀ {A} → ⟦ □ A ⇒ □ (□ A) ⟧
duplicate {A} [ [ σ ]′ ]′ =
  [ (λ t t∈i → [ (λ u u∈↑t → subsumM⟦ A ⟧ (↑ u) (↑ t) (lb≼ u∈↑t , ≼-refl) (σ t t∈i)) ]′) ]′

-- Applicative structure of □

[_] : ∀ {A} → ⟦ A ⟧ → ⟦ □ A ⟧
[ σ ] = [ (λ t t∈i → i→m (λ j j⊑↑t → σ)) ]′

_⟨*⟩_ : ∀ {A B} → ⟦ □ (A ⇒ B) ⇒ □ A ⇒ □ B ⟧
[ [ f ]′ ]′ ⟨*⟩ [ [ σ ]′ ]′ =
  [ (λ t t∈i → (f t t∈i) $ (σ t t∈i)) ]′
