open import Coinduction using ( ∞ ; ♯_ ; ♭ )
open import Data.Product using ( _,_ )
open import FRP.LTL.ISet.Core using ( ISet ; M⟦_⟧ ; compM⟦_⟧ ; splitM⟦_⟧ ; ⟦_⟧ ; ⌈_⌉ ; [_] )
open import FRP.LTL.ISet.Product using ( _∧_ )
open import FRP.LTL.ISet.Stateless using ( _⇒_ )
open import FRP.LTL.Time.Bound using ( Time∞ ; fin ; +∞ ; _≼_ ; _≺_ ; ≼-refl ; ≺-impl-≼ ; ≺-impl-⋡ ; _≺-trans_ ; _≼-case_ ; lt ; eq ; gt ; t≺+∞ )
open import FRP.LTL.Time.Interval using ( [_⟩ )
open import FRP.LTL.Util using ( ⊥-elim ; ≡-relevant )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

module FRP.LTL.ISet.Decoupled where

data _∙_⊷_∙_ (A : ISet) (s : Time∞) (B : ISet) (u : Time∞) : Set where
  inp : .(s ≺ u) → .(u ≺ +∞) → 
    (∀ {t} .(s≺t : s ≺ t) → M⟦ A ⟧ [ ≺-impl-≼ s≺t ⟩ → ∞ (A ∙ t ⊷ B ∙ u)) → 
      (A ∙ s ⊷ B ∙ u)
  out : ∀ {v} .(u≺v : u ≺ v) → 
    M⟦ B ⟧ [ ≺-impl-≼ u≺v ⟩ → ∞ (A ∙ s ⊷ B ∙ v) → 
      (A ∙ s ⊷ B ∙ u)
  done : .(u ≡ +∞) → 
    (A ∙ s ⊷ B ∙ u)

_▹_ : ISet → ISet → ISet
A ▹ B = ⌈ (λ t → A ∙ fin t ⊷ B ∙ fin t) ⌉

_/_/_ : ∀ {A B s t u} → (A ∙ s ⊷ B ∙ u) → .(s≺t : s ≺ t) → M⟦ A ⟧ [ ≺-impl-≼ s≺t ⟩ → (A ∙ t ⊷ B ∙ u)
inp s≺u u≺∞ P / s≺t / σ = ♭ (P s≺t σ)
out u≺v τ P   / s≺t / σ = out u≺v τ (♯ (♭ P / s≺t / σ))
done u≡∞      / s≺t / σ = done u≡∞

mutual

  ≻-tr : ∀ {A B C s u} .(s≻u : u ≺ s) → M⟦ B ⟧ [ ≺-impl-≼ s≻u ⟩ → 
    ((A ∧ B) ∙ u ⊷ (A ∧ C) ∙ u) → (B ∙ s ⊷ C ∙ u)
  ≻-tr s≻u σ (inp u≺u u≺∞ P) = ⊥-elim (≺-impl-⋡ u≺u ≼-refl)
  ≻-tr {A} {B} {C} {s} {u} s≻u σ (out {v} u≺v [ ρ , τ ] P) 
    with s ≼-case v
  ≻-tr {A} {B} {C} s≻u σ (out u≺v [ ρ , τ ] P) | lt s≺v 
    with splitM⟦ A ⟧ [ ≺-impl-≼ s≻u ⟩ [ ≺-impl-≼ s≺v ⟩ refl ρ 
  ≻-tr {A} {B} {C} s≻u σ (out u≺v [ ρ , τ ] P) | lt s≺v | (ρ₁ , ρ₂) = 
    out u≺v τ (♯ ≺-tr s≺v ρ₂ (♭ P / s≻u / [ ρ₁ , σ ]))
  ≻-tr {A} {B} {C} s≻u σ (out u≺v [ ρ , τ ] P) | eq s≡v 
    with ≡-relevant s≡v
  ≻-tr {A} {B} {C} s≻u σ (out u≺v [ ρ , τ ] P) | eq s≡v | refl =
    out u≺v τ (♯ tr (♭ P / s≻u / [ ρ , σ ]))
  ≻-tr {A} {B} {C} s≻u σ (out u≺v [ ρ , τ ] P) | gt s≻v 
    with splitM⟦ B ⟧ [ ≺-impl-≼ u≺v ⟩ [ ≺-impl-≼ s≻v ⟩ refl σ
  ≻-tr {A} {B} {C} s≻u σ (out u≺v [ ρ , τ ] P) | gt s≻v | (σ₁ , σ₂) = 
    out u≺v τ (♯ ≻-tr s≻v σ₂ (♭ P / u≺v / [ ρ , σ₁ ]))
  ≻-tr s≻u σ (done u≡∞) = done u≡∞

  ≺-tr : ∀ {A B C s u} .(s≺u : s ≺ u) → M⟦ A ⟧ [ ≺-impl-≼ s≺u ⟩ → 
    ((A ∧ B) ∙ s ⊷ (A ∧ C) ∙ u) → (B ∙ s ⊷ C ∙ u)
  ≺-tr {A} {B} {C} {s} {+∞}    s≺u ρ P = done refl
  ≺-tr {A} {B} {C} {s} {fin u} s≺u ρ P = inp s≺u t≺+∞ Q where

    Q : ∀ {t} .(s≺t : s ≺ t) → M⟦ B ⟧ [ ≺-impl-≼ s≺t ⟩ → ∞ (B ∙ t ⊷ C ∙ fin u)
    Q {t} s≺t σ  with t ≼-case (fin u)
    Q s≺t σ | lt t≺u with splitM⟦ _ ⟧ [ ≺-impl-≼ s≺t ⟩ [ ≺-impl-≼ t≺u ⟩ refl ρ
    Q s≺t σ | lt t≺u | (ρ₁ , ρ₂) = ♯ ≺-tr t≺u ρ₂ (P / s≺t / [ ρ₁ , σ ])
    Q s≺t σ | eq t≡u with ≡-relevant t≡u
    Q s≺t σ | eq t≡u | refl = ♯ tr (P / s≺u / [ ρ , σ ])
    Q s≺t σ | gt t≻u with splitM⟦ _ ⟧ [ ≺-impl-≼ s≺u ⟩ [ ≺-impl-≼ t≻u ⟩ refl σ
    Q s≺t σ | gt t≻u | (σ₁ , σ₂) = ♯ (≻-tr t≻u σ₂ (P / s≺u / [ ρ , σ₁ ]))

  tr : ∀ {A B C s} → ((A ∧ B) ∙ s ⊷ (A ∧ C) ∙ s) → (B ∙ s ⊷ C ∙ s)
  tr (inp s≺s s≺∞ P)       = ⊥-elim (≺-impl-⋡ s≺s ≼-refl)
  tr (out s≺u [ ρ , τ ] P) = out s≺u τ (♯ ≺-tr s≺u ρ (♭ P))
  tr (done s≡∞)            = done s≡∞

loop : ∀ {A B C} → ⟦ ((A ∧ B) ▹ (A ∧ C)) ⇒ (B ▹ C) ⟧
loop [ [ f ] ] = [ (λ t t∈i → tr (f t t∈i)) ]