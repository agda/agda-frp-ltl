open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import FRP.LTL.RSet.Core using ( RSet )
open import FRP.LTL.Time.Bound using 
  ( Time∞ ; fin ; _≼_ ; _≺_ ; ≼-refl ; _≼-trans_ ; _≼-asym_ ; _≼-total_ ; _≺-transˡ_
  ; ≺-impl-≼ ; ≡-impl-≼ ; ≡-impl-≽ ; ≺-impl-⋡ ; src )
open import FRP.LTL.Time.Interval using 
  ( Interval ; [_⟩ ; _⊑_ ; _~_ ; _,_ ; lb ; ub ; lb≼ ; ≺ub ; Int ; _⌢_∵_ 
  ; ⊑-impl-≼ ; ⊑-impl-≽ ; lb≺ub ; ⊑-refl ; _⊑-trans_ ; ⌢-inj₁ ; ⌢-inj₂ ; sing )
open import FRP.LTL.Util using ( ≡-relevant ; ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Unary using ( _∈_ )

module FRP.LTL.ISet.Core where

infixr 4 _,_

-- Monotone interval types

-- An MSet is a pair (A , split , subsum) where 
-- A : Interval → Set
-- if σ : A [ s≼t≼u ⟩ then (split s≼t t≼u σ) : (A [ s≼t ⟩ × A [ t≼u ⟩)
-- if i ⊑ j and σ : A j then subsum i⊑j σ : A i

-- Note that subsum and split are interderivable, but
-- we provide both for efficiency.

-- In previous versions of MSet, we also included comp (an inverse of split)
-- and id (a unit for comp) but &&& and loop have been rewritten to avoid needing comp.

data MSet : Set₁ where
  _,_ : (A : Interval → Set) → 
    ((∀ i j i~j → A (i ⌢ j ∵ i~j) → (A i × A j)) × (∀ i j → (i ⊑ j) → A j → A i)) → 
    MSet

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

splitB⟦_⟧ : ∀ A i j i~j → B⟦ A ⟧ (i ⌢ j ∵ i~j) → (B⟦ A ⟧ i × B⟦ A ⟧ j)
splitB⟦ A , split , subsum ⟧ i j i~j [ σ ] with split i j i~j σ
... | (σ₁ , σ₂) = ([ σ₁ ] , [ σ₂ ])

subsumB⟦_⟧ : ∀ A i j → (i ⊑ j) → B⟦ A ⟧ j → B⟦ A ⟧ i
subsumB⟦ A , split , subsum ⟧ i j i⊑j [ σ ] = [ subsum i j i⊑j σ ]

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
M⟦ [ A ] ⟧ i = B⟦ A ⟧ i
M⟦ A ⇛ B ⟧ i = ∀ j → (j ⊑ i) → I⟦ A ⇛ B ⟧ j

-- User-level semantics

⟦_⟧ : ISet → Set
⟦ A ⟧ = ∀ {i} → I⟦ A ⟧ i

-- Translation of ISet into MSet

splitM⟦_⟧ : ∀ A i j i~j → M⟦ A ⟧ (i ⌢ j ∵ i~j) → (M⟦ A ⟧ i × M⟦ A ⟧ j)
splitM⟦ [ A ] ⟧ i j i~j σ = splitB⟦ A ⟧ i j i~j σ
splitM⟦ A ⇛ B ⟧ i j i~j f = (f₁ , f₂) where

  f₁ : ∀ k → (k ⊑ i) → B⟦ A ⟧ k → I⟦ B ⟧ k 
  f₁ k k⊑i = f k (⊑-impl-≽ k⊑i , ⊑-impl-≼ k⊑i ≼-trans ≡-impl-≼ i~j ≼-trans ≺-impl-≼ (lb≺ub j))

  f₂ : ∀ k → (k ⊑ j) → B⟦ A ⟧ k → I⟦ B ⟧ k
  f₂ k k⊑j = f k (≺-impl-≼ (lb≺ub i) ≼-trans ≡-impl-≼ i~j ≼-trans ⊑-impl-≽ k⊑j , ⊑-impl-≼ k⊑j) 

subsumM⟦_⟧ : ∀ A i j → (i ⊑ j) → M⟦ A ⟧ j → M⟦ A ⟧ i
subsumM⟦ [ A ] ⟧ i j i⊑j σ = subsumB⟦ A ⟧ i j i⊑j σ
subsumM⟦ A ⇛ B ⟧ i j i⊑j f = λ h h⊑i → f h (h⊑i ⊑-trans i⊑j)

mset : ISet → MSet
mset A =  ( M⟦ A ⟧ , splitM⟦ A ⟧ , subsumM⟦ A ⟧ )

-- Translations back and forth between M⟦ A ⟧ and I⟦ A ⟧

m→i : ∀ {A i} → M⟦ A ⟧ i → I⟦ A ⟧ i
m→i {[ A ]} {i} σ = σ
m→i {A ⇛ B} {i} f = f i ⊑-refl

i→m : ∀ {A i} → (∀ j → (j ⊑ i) → I⟦ A ⟧ j) → M⟦ A ⟧ i
i→m {[ A ]} {i} σ = σ i ⊑-refl
i→m {A ⇛ B} {i} f = f

-- Embedding of RSet into ISet

⌈_⌉ : RSet → ISet
⌈ A ⌉ = [ (λ i → ∀ t → .(t ∈ Int i) → A t) , split , subsum ] where

  split : ∀ i j i~j → (∀ t → .(t ∈ Int (i ⌢ j ∵ i~j)) → A t) → 
    ((∀ t → .(t ∈ Int i) → A t) × (∀ t → .(t ∈ Int j) → A t))
  split i j i~j σ = 
    ( (λ t t∈i → σ t (lb≼ t∈i , ≺ub t∈i ≺-transˡ ≡-impl-≼ i~j ≼-trans ≺-impl-≼ (lb≺ub j)))
    , (λ t t∈j → σ t (≺-impl-≼ (lb≺ub i) ≼-trans ≡-impl-≼ i~j ≼-trans lb≼ t∈j , ≺ub t∈j)) )

  subsum : ∀ i j → (i ⊑ j) → (∀ t → .(t ∈ Int j) → A t) → (∀ t → .(t ∈ Int i) → A t)
  subsum i j i⊑j σ t t∈i = σ t (⊑-impl-≽ i⊑j ≼-trans lb≼ t∈i , ≺ub t∈i ≺-transˡ ⊑-impl-≼ i⊑j)

-- Embedding of ISet into RSet

⌊_⌋ : ISet → RSet
⌊ A ⌋ t = M⟦ A ⟧ (sing t)

-- Embedding of Set into ISet

data Always (A : Set) (i : Interval) : Set where
  const : A → Always A i
  var : ∀ j → .(i ⊑ j) → (∀ t → .(t ∈ Int j) → A) → Always A i

⟨_⟩ : Set → ISet
⟨ A ⟩ =  [ Always A , split , subsum ] where

  split : ∀ i j i~j → Always A (i ⌢ j ∵ i~j) → (Always A i × Always A j)
  split i j i~j (const a) = (const a , const a)
  split i j i~j (var k i⌢j⊑k f) = 
    ( var k (⌢-inj₁ i j i~j ⊑-trans i⌢j⊑k) f
    , var k (⌢-inj₂ i j i~j ⊑-trans i⌢j⊑k) f )

  subsum : ∀ i j → (i ⊑ j) → Always A j → Always A i
  subsum i j i⊑j (const a)     = const a
  subsum i j i⊑j (var k j⊑k f) = var k (i⊑j ⊑-trans j⊑k) f
