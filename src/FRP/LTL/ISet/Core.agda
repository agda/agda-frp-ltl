open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import FRP.LTL.Time.Bound using ( _≼_ ; ≼-refl ; _≼-trans_ ; _≼-asym_ ; _≼-total_ ; ≼-proof-irrel )
open import FRP.LTL.Time.Interval using ( Interval ; [_⟩ ; _⊑_ ; _,_ ; lb ; ub )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym )

module FRP.LTL.ISet.Core where

infixr 4 _,_

-- Monotone interval types

≡-impl-≼ : ∀ {s t} → (s ≡ t) → (s ≼ t)
≡-impl-≼ refl = ≼-refl

data MSet : Set₁ where
  _,_ : 
    (A : Interval → Set) →
    ( (∀ {s} → A [ ≼-refl {s} ⟩)
    × (∀ {s t u} {s≼t : s ≼ t} {t≼u : t ≼ u} → (A [ s≼t ⟩ × A [ t≼u ⟩) → A [ s≼t ≼-trans t≼u ⟩)
    × (∀ {s t u} {s≼t : s ≼ t} {t≼u : t ≼ u} → A [ s≼t ≼-trans t≼u ⟩ → (A [ s≼t ⟩ × A [ t≼u ⟩))
    ) → MSet

-- The underlying "unboxed" elements of an MSet

U⟦_⟧ : MSet → Interval → Set
U⟦ A , _ ⟧ = A

-- A "boxed" element of an MSet. This is used rather than the unboxed
-- representation because it's invertable, and so plays much better
-- with the type inference algorithm.

data B⟦_⟧ (A : MSet) (i : Interval) : Set where
  [_] : U⟦ A ⟧ i → B⟦ A ⟧ i

unbox : ∀ {A i} → B⟦ A ⟧ i → U⟦ A ⟧ i
unbox [ a ] = a

idB⟦_⟧ : ∀ A {s} → 
  B⟦ A ⟧ [ ≼-refl {s} ⟩
idB⟦ A , id , comp , split ⟧ = 
  [ id ]

compB⟦_⟧ : ∀ A {s t u} {s≼t : s ≼ t} {t≼u : t ≼ u} → 
  (B⟦ A ⟧ [ s≼t ⟩ × B⟦ A ⟧ [ t≼u ⟩) → B⟦ A ⟧ [ s≼t ≼-trans t≼u ⟩
compB⟦ A , id , comp , split ⟧ ([ σ₁ ] , [ σ₂ ]) =
  [ comp (σ₁ , σ₂) ]

splitB⟦_⟧ : ∀ A {s t u} {s≼t : s ≼ t} {t≼u : t ≼ u} → 
  B⟦ A ⟧ [ s≼t ≼-trans t≼u ⟩ → (B⟦ A ⟧ [ s≼t ⟩ × B⟦ A ⟧ [ t≼u ⟩)
splitB⟦ A , id , comp , split ⟧ [ σ ] =
  ([ proj₁ σ₁₂ ] , [ proj₂ σ₁₂ ]) where σ₁₂ = split σ

-- Interval types

data ISet : Set₁ where
  [_] : MSet → ISet
  _⇛_ : MSet → ISet → ISet

-- Non-monotone semantics of ISets

I⟦_⟧ : ISet → Interval → Set
I⟦ [ A ] ⟧ i = B⟦ A ⟧ i
I⟦ A ⇛ B ⟧ i = B⟦ A ⟧ i → I⟦ B ⟧ i

-- Monotone semantics of ISets

M⟦_⟧ : ISet → Interval → Set
M⟦ [ A ] ⟧ i = I⟦ [ A ] ⟧ i
M⟦ A ⇛ B ⟧ i = ∀ j → (j ⊑ i) → I⟦ A ⇛ B ⟧ j

-- User-level semantics

⟦_⟧ : ISet → Set
⟦ A ⟧ = ∀ {i} → I⟦ A ⟧ i

-- Translation of ISet into MSet

idI⟦_⟧ : ∀ A {s} → I⟦ A ⟧ [ ≼-refl {s} ⟩
idI⟦ [ A ] ⟧ = idB⟦ A ⟧
idI⟦ A ⇛ B ⟧ = λ σ → idI⟦ B ⟧

idM⟦_⟧ : ∀ A {s} → M⟦ A ⟧ [ ≼-refl {s} ⟩
idM⟦ [ A ] ⟧ = idI⟦ [ A ] ⟧
idM⟦ A ⇛ B ⟧ = lemma where

  lemma : ∀ {s} → M⟦ A ⇛ B ⟧ [ ≼-refl {s} ⟩
  lemma [ t≼u ⟩ (s≼t , u≼s) with s≼t ≼-asym (t≼u ≼-trans u≼s)
  lemma [ t≼u ⟩ (s≼t , u≼s) | refl with t≼u ≼-asym u≼s
  lemma [ t≼u ⟩ (s≼t , u≼s) | refl | refl with ≼-proof-irrel t≼u ≼-refl
  lemma [ .≼-refl ⟩ (s≼t , u≼s) | refl | refl | refl = idI⟦ A ⇛ B ⟧

compI⟦_⟧ : ∀ A {s t u} {s≼t : s ≼ t} {t≼u : t ≼ u} → 
  (I⟦ A ⟧ [ s≼t ⟩ × I⟦ A ⟧ [ t≼u ⟩) → I⟦ A ⟧ [ s≼t ≼-trans t≼u ⟩
compI⟦ [ A ] ⟧ (σ₁ , σ₂) = compB⟦ A ⟧ (σ₁ , σ₂)
compI⟦ A ⇛ B ⟧ {s} {t} {u} {s≼t} {t≼u} (f₁ , f₂) = lemma where

  lemma : B⟦ A ⟧ [ s≼t ≼-trans t≼u ⟩ → I⟦ B ⟧ [ s≼t ≼-trans t≼u ⟩
  lemma σ = compI⟦ B ⟧ (f₁ (proj₁ σ₁₂) , f₂ (proj₂ σ₁₂)) where σ₁₂ = splitB⟦ A ⟧ σ

compM⟦_⟧ : ∀ A {s t u} {s≼t : s ≼ t} {t≼u : t ≼ u} → 
  (M⟦ A ⟧ [ s≼t ⟩ × M⟦ A ⟧ [ t≼u ⟩) → M⟦ A ⟧ [ s≼t ≼-trans t≼u ⟩
compM⟦ [ A ] ⟧ (σ₁ , σ₂) = compI⟦ [ A ] ⟧ (σ₁ , σ₂)
compM⟦ A ⇛ B ⟧ {s} {t} {u} {s≼t} {t≼u} (f₁ , f₂) = lemma where

  lemma : ∀ j → (j ⊑ [ s≼t ≼-trans t≼u ⟩) → B⟦ A ⟧ j → I⟦ B ⟧ j
  lemma [ r≼v ⟩ (s≼r , v≼u) with lb [ r≼v ⟩ | ub [ r≼v ⟩
  lemma [ r≼v ⟩ (s≼r , v≼u) | r | v with r ≼-total t | t ≼-total v
  lemma [ r≼v ⟩ (s≼r , v≼u) | r | v | inj₁ r≼t | inj₁ t≼v with ≼-proof-irrel r≼v (r≼t ≼-trans t≼v)
  lemma [ ._  ⟩ (s≼r , v≼u) | r | v | inj₁ r≼t | inj₁ t≼v | refl = 
    compI⟦ A ⇛ B ⟧ (f₁ [ r≼t ⟩ (s≼r , ≼-refl) , f₂ [ t≼v ⟩ (≼-refl , v≼u))
  lemma [ r≼v ⟩ (s≼r , v≼u) | r | v | inj₁ r≼t | inj₂ v≼t = 
    f₁ [ r≼v ⟩ (s≼r , v≼t) 
  lemma [ r≼v ⟩ (s≼r , v≼u) | r | v | inj₂ t≼r | inj₁ t≼v = 
    f₂ [ r≼v ⟩ (t≼r , v≼u) 
  lemma [ r≼v ⟩ (s≼r , v≼u) | r | v | inj₂ t≼r | inj₂ v≼t with r≼v ≼-asym (v≼t ≼-trans t≼r)
  lemma [ r≼v ⟩ (s≼r , v≼u) | r | .r | inj₂ t≼r | inj₂ v≼t | refl with ≼-proof-irrel r≼v ≼-refl
  lemma [ ._  ⟩ (s≼r , v≼u) | r | .r | inj₂ t≼r | inj₂ v≼t | refl | refl = 
    idI⟦ A ⇛ B ⟧ 

splitM⟦_⟧ : ∀ A {s t u} {s≼t : s ≼ t} {t≼u : t ≼ u} → 
  M⟦ A ⟧ [ s≼t ≼-trans t≼u ⟩ → (M⟦ A ⟧ [ s≼t ⟩ × M⟦ A ⟧ [ t≼u ⟩)
splitM⟦ [ A ] ⟧ σ = splitB⟦ A ⟧ σ
splitM⟦ A ⇛ B ⟧ {s} {t} {u} {s≼t} {t≼u} f = (f₁ , f₂) where

  f₁ : ∀ j → (j ⊑ [ s≼t ⟩) → B⟦ A ⟧ j → I⟦ B ⟧ j
  f₁ [ r≼v ⟩ (s≼r , v≼t) σ = f [ r≼v ⟩ (s≼r , v≼t ≼-trans t≼u) σ

  f₂ : ∀ j → (j ⊑ [ t≼u ⟩) → B⟦ A ⟧ j → I⟦ B ⟧ j
  f₂ [ r≼v ⟩ (t≼r , v≼u) σ = f [ r≼v ⟩ (s≼t ≼-trans t≼r , v≼u) σ

mset : ISet → MSet
mset A = 
  ( M⟦ A ⟧
  , (λ {s} → idM⟦ A ⟧ {s})
  , (λ {s} → compM⟦ A ⟧ {s})
  , (λ {s} → splitM⟦ A ⟧ {s}) )
