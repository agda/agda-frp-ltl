open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ ; uncurry )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import FRP.LTL.Time.Bound using ( Time∞ ; _≼_ ; _≺_ ; ≼-refl ; _≼-trans_ ; _≼-asym_ ; _≼-total_ ; ≺-impl-≼ ; ≼-proof-irrel ; ≡-impl-≼ )
open import FRP.LTL.Time.Interval using ( Interval ; [_⟩ ; _⊑_ ; _⇝_ ; _,_ ; lb ; ub ; Int ; _++_∵_ ; ⊑-impl-≼ ; ⊑-impl-≽ ; int-≼ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym )
open import Relation.Unary using ( _∈_ )

module FRP.LTL.ISet.Core where

infixr 4 _,_

-- Monotone interval types
-- There's a bit of hoop-jumping here to avoid mentioning time bounds explicitly,
-- in order to allow interval orders to be irrelevant.

data MSet : Set₁ where
  _,_ : 
    (A : Interval → Set) →
    ( (∀ {i} → .(i ⇝ i) → A i)
    × (∀ {i j} .i⇝j → (A i × A j) → (A (i ++ j ∵ i⇝j))) 
    × (∀ {i j} .i⇝j → A (i ++ j ∵ i⇝j) → (A i × A j))
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

idB⟦_⟧ : ∀ A {i} → .(i ⇝ i) → B⟦ A ⟧ i
idB⟦ A , id , comp , split ⟧ i⇝i = [ id i⇝i ]

compB⟦_⟧ : ∀ A {i j} .i⇝j → (B⟦ A ⟧ i × B⟦ A ⟧ j) → (B⟦ A ⟧ (i ++ j ∵ i⇝j))
compB⟦ A , id , comp , split ⟧ i⇝j ([ σ₁ ] , [ σ₂ ]) =
  [ comp i⇝j (σ₁ , σ₂) ]

splitB⟦_⟧ : ∀ A {i j} .i⇝j → B⟦ A ⟧ (i ++ j ∵ i⇝j) → (B⟦ A ⟧ i × B⟦ A ⟧ j)
splitB⟦ A , id , comp , split ⟧ i⇝j [ σ ] =
  ([ proj₁ σ₁₂ ] , [ proj₂ σ₁₂ ]) where σ₁₂ = split i⇝j σ

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

idI⟦_⟧ : ∀ A {i} → .(i ⇝ i) → I⟦ A ⟧ i
idI⟦ [ A ] ⟧ i⇝i = idB⟦ A ⟧ i⇝i
idI⟦ A ⇛ B ⟧ i⇝i = λ σ → idI⟦ B ⟧ i⇝i

idM⟦_⟧ : ∀ A {i} → .(i ⇝ i) → M⟦ A ⟧ i
idM⟦ [ A ] ⟧ i⇝i = idI⟦ [ A ] ⟧ i⇝i
idM⟦ A ⇛ B ⟧ i⇝i = λ j j⊑i → 
  idI⟦ A ⇛ B ⟧ ((⊑-impl-≼ j⊑i ≼-trans ≡-impl-≼ i⇝i ≼-trans ⊑-impl-≽ j⊑i) ≼-asym (int-≼ j))

compI⟦_⟧ : ∀ A {i j} .i⇝j → (I⟦ A ⟧ i × I⟦ A ⟧ j) → (I⟦ A ⟧ (i ++ j ∵ i⇝j))
compI⟦ [ A ] ⟧ i⇝j (σ₁ , σ₂) = compB⟦ A ⟧ i⇝j (σ₁ , σ₂)
compI⟦ A ⇛ B ⟧ {i} {j} i⇝j (f₁ , f₂) = lemma where

  lemma : B⟦ A ⟧ (i ++ j ∵ i⇝j) → I⟦ B ⟧ (i ++ j ∵ i⇝j)
  lemma σ = compI⟦ B ⟧ i⇝j (f₁ (proj₁ σ₁₂) , f₂ (proj₂ σ₁₂)) where σ₁₂ = splitB⟦ A ⟧ i⇝j σ

compM⟦_⟧ : ∀ A {i j} .i⇝j → (M⟦ A ⟧ i × M⟦ A ⟧ j) → (M⟦ A ⟧ (i ++ j ∵ i⇝j))
compM⟦ [ A ] ⟧ i⇝j (σ₁ , σ₂) = compI⟦ [ A ] ⟧ i⇝j (σ₁ , σ₂)
compM⟦ A ⇛ B ⟧ {i} {j} i⇝j (f₁ , f₂) = lemma where

  lemma : ∀ k → k ⊑ (i ++ j ∵ i⇝j) → B⟦ A ⟧ k → I⟦ B ⟧ k
  lemma k k⊑i++j with lb k ≼-total ub i | lb j ≼-total ub k
  lemma [ s≼t ⟩ (li≼s , t≼uj) | inj₁ s≼ui | inj₁ lj≼t = 
    compI⟦ A ⇛ B ⟧ i⇝j (f₁ [ s≼ui ⟩ (li≼s , ≼-refl) , f₂ [ lj≼t ⟩ (≼-refl , t≼uj))
  lemma [ s≼t ⟩ (li≼s , t≼uj) | inj₁ s≼ui | inj₂ t≼lj = 
    f₁ [ s≼t ⟩ (li≼s , t≼lj ≼-trans ≡-impl-≼ (sym i⇝j))
  lemma [ s≼t ⟩ (li≼s , t≼uj) | inj₂ ui≼s | inj₁ lj≼t = 
    f₂ [ s≼t ⟩ (≡-impl-≼ (sym i⇝j) ≼-trans ui≼s , t≼uj)
  lemma [ s≼t ⟩ (li≼s , t≼uj) | inj₂ ui≼s | inj₂ t≼lj = 
    idI⟦ A ⇛ B ⟧ ((t≼lj ≼-trans ≡-impl-≼ (sym i⇝j) ≼-trans ui≼s) ≼-asym s≼t)

splitM⟦_⟧ : ∀ A {i j} .i⇝j → M⟦ A ⟧ (i ++ j ∵ i⇝j) → (M⟦ A ⟧ i × M⟦ A ⟧ j)
splitM⟦ [ A ] ⟧ i⇝j σ = splitB⟦ A ⟧ i⇝j σ
splitM⟦ A ⇛ B ⟧ {i} {j} i⇝j f = (f₁ , f₂) where

  f₁ : ∀ k → (k ⊑ i) → B⟦ A ⟧ k → I⟦ B ⟧ k 
  f₁ k k⊑i = f k (⊑-impl-≽ k⊑i , ⊑-impl-≼ k⊑i ≼-trans ≡-impl-≼ i⇝j ≼-trans int-≼ j)

  f₂ : ∀ k → (k ⊑ j) → B⟦ A ⟧ k → I⟦ B ⟧ k
  f₂ k k⊑j = f k (int-≼ i ≼-trans ≡-impl-≼ i⇝j ≼-trans ⊑-impl-≽ k⊑j , ⊑-impl-≼ k⊑j) 

mset : ISet → MSet
mset A = 
  ( M⟦ A ⟧
  , (λ {i} → idM⟦ A ⟧ {i})
  , (λ {i j} → compM⟦ A ⟧ {i} {j})
  , (λ {i j} → splitM⟦ A ⟧ {i} {j}) )
