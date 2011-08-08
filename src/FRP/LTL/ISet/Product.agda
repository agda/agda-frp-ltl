open import Coinduction using ( ∞ ; ♯_ ; ♭ )
open import Data.Product using ( _×_ ; _,_ ; proj₁ )
open import FRP.LTL.Time.Bound using 
  ( Time∞ ; _≼_ ; _≺_ ; fin ; +∞ ; +∞-top
  ; ≼-refl ; _≼-trans_ ; ≡-impl-≽ ; ≺-impl-≼ ; ≺-impl-⋡ ; t≺+∞ 
  ; _≼-case_ ; lt ; eq ; gt )
open import FRP.LTL.Time.Interval using ( [_⟩ ; _⊑_ ; _~_ ; _⌢_∵_ )
open import FRP.LTL.ISet.Causal using ( _⊵_ ; _∙_⊸_∙_ ; done ; inp ; out ; _/_/_ )
open import FRP.LTL.ISet.Core using ( ISet ; [_] ; _,_ ; ⟦_⟧ ; M⟦_⟧ ; splitM⟦_⟧ ; subsumM⟦_⟧ )
open import FRP.LTL.ISet.Stateless using ( _⇒_ )
open import FRP.LTL.Util using ( ⊥-elim ; ≡-relevant )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

module FRP.LTL.ISet.Product where

_∧_ : ISet → ISet → ISet
A ∧ B = [ (λ i → M⟦ A ⟧ i × M⟦ B ⟧ i) , split , subsum ] where

  split : ∀ i j i~j → 
    (M⟦ A ⟧ (i ⌢ j ∵ i~j) × M⟦ B ⟧ (i ⌢ j ∵ i~j)) → 
      ((M⟦ A ⟧ i × M⟦ B ⟧ i) × (M⟦ A ⟧ j × M⟦ B ⟧ j)) 
  split i j i~j (σ , τ) with splitM⟦ A ⟧ i j i~j σ | splitM⟦ B ⟧ i j i~j τ
  split i j i~j (σ , τ) | (σ₁ , σ₂) | (τ₁ , τ₂) = ((σ₁ , τ₁) , (σ₂ , τ₂))

  subsum : ∀ i j → (i ⊑ j) → (M⟦ A ⟧ j × M⟦ B ⟧ j) → (M⟦ A ⟧ i × M⟦ B ⟧ i)
  subsum i j i⊑j (σ , τ) = (subsumM⟦ A ⟧ i j i⊑j σ , subsumM⟦ B ⟧ i j i⊑j τ)
   
-- We could define fst and snd in terms of arr, but we define them explictly for efficiency.

π₁ : ∀ {A B} t → ((A ∧ B) ∙ t ⊸ A ∙ t)
π₁ {A} {B} +∞      = done refl
π₁ {A} {B} (fin t) = inp ≼-refl t≺+∞ P where

  P : ∀ {u} .(t≺u : fin t ≺ u) → M⟦ A ∧ B ⟧ [ t≺u ⟩ → ∞ ((A ∧ B) ∙ u ⊸ A ∙ fin t)
  P {u} t≺u [ σ , τ ] = ♯ out t≺u σ (♯ π₁ u)

fst : ∀ {A B} → ⟦ A ∧ B ⊵ A ⟧
fst = [ (λ t t∈i → π₁ (fin t)) ]

π₂ : ∀ {A B} t → ((A ∧ B) ∙ t ⊸ B ∙ t)
π₂ {A} {B} +∞      = done refl
π₂ {A} {B} (fin t) = inp ≼-refl t≺+∞ Q where

  Q : ∀ {u} .(t≺u : fin t ≺ u) → M⟦ A ∧ B ⟧ [ t≺u ⟩ → ∞ ((A ∧ B) ∙ u ⊸ B ∙ fin t)
  Q {u} t≺u [ σ , τ ] = ♯ out t≺u τ (♯ π₂ u)

snd : ∀ {A B} → ⟦ A ∧ B ⊵ B ⟧
snd = [ (λ t t∈i → π₂ (fin t)) ]

-- Mediating morphism

_&&_ : ∀ {A B C s t} → (A ∙ s ⊸ B ∙ t) → (A ∙ s ⊸ C ∙ t) → (A ∙ s ⊸ (B ∧ C) ∙ t)
inp s≼t t≺∞ P   && Q               = inp s≼t t≺∞ (λ s≺u σ → ♯ (♭ (P s≺u σ)   && (Q / s≺u / σ)))
P               && inp s≼t t≺∞ Q   = inp s≼t t≺∞ (λ s≺u σ → ♯ ((P / s≺u / σ) && ♭ (Q s≺u σ)))
P               && done t≡∞        = done t≡∞
done t≡∞        && Q               = done t≡∞
out {u} t≺u σ P && out {v} t≺v τ Q with u ≼-case v
out t≺u σ P     && out t≺v τ Q | lt u≺v with splitM⟦ _ ⟧ [ t≺u ⟩ [ u≺v ⟩ refl τ 
out t≺u σ P     && out t≺v τ Q | lt u≺v | (τ₁ , τ₂) = out t≺u [ σ , τ₁ ] (♯ (♭ P && out u≺v τ₂ Q))
out t≺u σ P     && out t≺v τ Q | eq u≡v with ≡-relevant u≡v
out t≺u σ P     && out t≺v τ Q | eq u≡v | refl      = out t≺u [ σ , τ ] (♯ (♭ P && ♭ Q))
out t≺u σ P     && out t≺v τ Q | gt v≺u with splitM⟦ _ ⟧ [ t≺v ⟩ [ v≺u ⟩ refl σ
out t≺u σ P     && out t≺v τ Q | gt v≺u | (σ₁ , σ₂) = out t≺v [ σ₁ , τ ] (♯ (out v≺u σ₂ P && ♭ Q))

_&&&_ : ∀ {A B C} → ⟦ (A ⊵ B) ⇒ (A ⊵ C) ⇒ (A ⊵ (B ∧ C)) ⟧
[ [ f ] ] &&& [ [ g ] ] = [ (λ t t∈i → f t t∈i && g t t∈i) ]