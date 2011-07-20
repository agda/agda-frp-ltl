open import Data.Product using ( _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import FRP.LTL.ISet.Core using 
  ( ISet ; I⟦_⟧ ; M⟦_⟧ ; ⟦_⟧ ; ⌈_⌉ ; idI⟦_⟧ ; splitM⟦_⟧ ; i→m ; m→i ; ⊑-subsum ) renaming 
  ( [_] to [_]′ )
open import FRP.LTL.ISet.Stateless using ( _⇒_ ; _$_ )
open import FRP.LTL.Time.Bound using ( fin ; +∞ ; +∞-top ; ≼-refl ; _≼-trans_ ; _≼-total_ ; _≼-asym_ ; ≺-impl-⋡ )
open import FRP.LTL.Time.Interval using ( ↑ ; [_⟩; _⊑_ ; lb ; ub ; lb≼ub ; lb≼ ; _,_ ; Int )
open import FRP.LTL.Util using ( ≡-relevant ; ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ )

module FRP.LTL.ISet.Globally where

-- □ A is "A holds globally in the future"

□ : ISet → ISet
□ A = ⌈( λ t → M⟦ A ⟧ (↑ (fin t)) )⌉

-- Comonad structure of □

extend : ∀ {A B} → ⟦ A ⇒ B ⟧ → ⟦ □ A ⇒ □ B ⟧
extend f [ [ σ ]′ ]′ =
  [ (λ t t∈i → i→m (λ j j⊑↑t → f [ ⊑-subsum j⊑↑t (σ t t∈i) ]′)) ]′

extract : ∀ {A} → ⟦ □ A ⇒ A ⟧
extract {A} {[ s≼t ⟩} [ [ σ ]′ ]′ 
  with lb [ s≼t ⟩ | ub [ s≼t ⟩ 
extract {A} {[ s≼t ⟩} [ [ σ ]′ ]′ | +∞ | t =
  idI⟦ A ⟧ [ s≼t ⟩ (≡-relevant (+∞-top ≼-asym s≼t))
extract {A} {[ s≼t ⟩} [ [ σ ]′ ]′ | fin s | t
  with t ≼-total fin s
extract {A} {[ s≼t ⟩} [ [ σ ]′ ]′ | fin s | t | inj₁ t≼s =
  idI⟦ A ⟧ [ s≼t ⟩ (≡-relevant (t≼s ≼-asym s≼t))
extract {A} {[ s≼t ⟩} [ [ σ ]′ ]′ | fin s | t | inj₂ s≺t
  with splitM⟦ A ⟧ [ s≼t ⟩ (↑ t) refl (σ s (≼-refl , s≺t))
extract {A} {[ s≼t ⟩} [ [ σ ]′ ]′ | fin s | t | inj₂ s≺t | (σ₁ , σ₂) =
  m→i σ₁

duplicate : ∀ {A} → ⟦ □ A ⇒ □ (□ A) ⟧
duplicate [ [ σ ]′ ]′ =
  [ (λ t t∈i → [ (λ u u∈↑t → ⊑-subsum (lb≼ u∈↑t , ≼-refl) (σ t t∈i)) ]′) ]′

-- Applicative structure of □

[_] : ∀ {A} → ⟦ A ⟧ → ⟦ □ A ⟧
[ σ ] = [ (λ t t∈i → i→m (λ j j⊑↑t → σ)) ]′

_⟨*⟩_ : ∀ {A B} → ⟦ □ (A ⇒ B) ⇒ □ A ⇒ □ B ⟧
[ [ f ]′ ]′ ⟨*⟩ [ [ σ ]′ ]′ =
  [ (λ t t∈i → (f t t∈i) $ (σ t t∈i)) ]′
