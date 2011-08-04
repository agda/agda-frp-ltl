open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import FRP.LTL.RSet.Core using ( RSet )
open import FRP.LTL.Time.Bound using 
  ( Time∞ ; fin ; _≼_ ; _≺_ ; ≼-refl ; _≼-trans_ ; _≼-asym_ ; _≼-total_ ; _≺-transˡ_
  ; ≺-impl-≼ ; ≡-impl-≼ ; ≡-impl-≽ ; ≺-impl-⋡ ; src )
open import FRP.LTL.Time.Interval using 
  ( Interval ; [_⟩ ; _⊑_ ; _~_ ; _,_ ; lb ; ub ; lb≼ ; ≺ub ; Int ; _⌢_∵_ 
  ; ⊑-impl-≼ ; ⊑-impl-≽ ; lb≼ub ; ⊑-refl ; _⊑-trans_ ; ⌢-inj₁ ; ⌢-inj₂ ; sing )
open import FRP.LTL.Util using ( ≡-relevant ; ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Unary using ( _∈_ )

module FRP.LTL.ISet.Core where

infixr 4 _,_

-- Monotone interval types
-- There's a bit of hoop-jumping here to avoid mentioning time bounds explicitly,
-- in order to allow interval orders to be irrelevant.

data MSet : Set₁ where
  _,_ : 
    (A : Interval → Set) →
    ( (∀ i → (i ~ i) → A i)
    × (∀ i j i~j → (A i × A j) → (A (i ⌢ j ∵ i~j))) 
    × (∀ i j i~j → A (i ⌢ j ∵ i~j) → (A i × A j))
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

idB⟦_⟧ : ∀ A i → (i ~ i) → B⟦ A ⟧ i
idB⟦ A , id , comp , split ⟧ i i~i = [ id i i~i ]

compB⟦_⟧ : ∀ A i j i~j → (B⟦ A ⟧ i × B⟦ A ⟧ j) → (B⟦ A ⟧ (i ⌢ j ∵ i~j))
compB⟦ A , id , comp , split ⟧ i j i~j ([ σ₁ ] , [ σ₂ ]) =
  [ comp i j i~j (σ₁ , σ₂) ]

splitB⟦_⟧ : ∀ A i j i~j → B⟦ A ⟧ (i ⌢ j ∵ i~j) → (B⟦ A ⟧ i × B⟦ A ⟧ j)
splitB⟦ A , id , comp , split ⟧ i j i~j [ σ ] with split i j i~j σ
... | (σ₁ , σ₂) = ([ σ₁ ] , [ σ₂ ])

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

idI⟦_⟧ : ∀ A i → (i ~ i) → I⟦ A ⟧ i
idI⟦ [ A ] ⟧ i i~i = idB⟦ A ⟧ i i~i
idI⟦ A ⇛ B ⟧ i i~i = λ σ → idI⟦ B ⟧ i i~i

idM⟦_⟧ : ∀ A i → (i ~ i) → M⟦ A ⟧ i
idM⟦ [ A ] ⟧ i i~i = idI⟦ [ A ] ⟧ i i~i
idM⟦ A ⇛ B ⟧ i i~i = λ j j⊑i → idI⟦ A ⇛ B ⟧ j
  (≡-relevant ((⊑-impl-≼ j⊑i ≼-trans ≡-impl-≼ i~i ≼-trans ⊑-impl-≽ j⊑i) ≼-asym lb≼ub j))

compI⟦_⟧ : ∀ A i j i~j → (I⟦ A ⟧ i × I⟦ A ⟧ j) → (I⟦ A ⟧ (i ⌢ j ∵ i~j))
compI⟦ [ A ] ⟧ i j i~j (σ₁ , σ₂) = compB⟦ A ⟧ i j i~j (σ₁ , σ₂)
compI⟦ A ⇛ B ⟧ i j i~j (f₁ , f₂) = lemma where

  lemma : B⟦ A ⟧ (i ⌢ j ∵ i~j) → I⟦ B ⟧ (i ⌢ j ∵ i~j)
  lemma σ with splitB⟦ A ⟧ i j i~j σ
  lemma σ | (σ₁ , σ₂) = compI⟦ B ⟧ i j i~j (f₁ σ₁ , f₂ σ₂)

compM⟦_⟧ : ∀ A i j i~j → (M⟦ A ⟧ i × M⟦ A ⟧ j) → (M⟦ A ⟧ (i ⌢ j ∵ i~j))
compM⟦ [ A ] ⟧ i j i~j (σ₁ , σ₂) = compI⟦ [ A ] ⟧ i j i~j (σ₁ , σ₂)
compM⟦ A ⇛ B ⟧ i j i~j (f₁ , f₂) = lemma where

  lemma : ∀ k → k ⊑ (i ⌢ j ∵ i~j) → B⟦ A ⟧ k → I⟦ B ⟧ k
  lemma k k⊑i⌢j with lb k ≼-total ub i | lb j ≼-total ub k
  lemma [ s≼t ⟩ (li≼s , t≼uj) | inj₁ s≼ui | inj₁ lj≼t = 
    compI⟦ A ⇛ B ⟧ [ s≼ui ⟩ [ lj≼t ⟩ i~j (f₁ [ s≼ui ⟩ (li≼s , ≼-refl) , f₂ [ lj≼t ⟩ (≼-refl , t≼uj))
  lemma [ s≼t ⟩ (li≼s , t≼uj) | inj₁ s≼ui | inj₂ t≺lj = 
    f₁ [ s≼t ⟩ (li≼s , ≺-impl-≼ t≺lj ≼-trans ≡-impl-≽ i~j)
  lemma [ s≼t ⟩ (li≼s , t≼uj) | inj₂ ui≺s | inj₁ lj≼t = 
    f₂ [ s≼t ⟩ (≡-impl-≽ i~j ≼-trans ≺-impl-≼ ui≺s , t≼uj)
  lemma [ s≼t ⟩ (li≼s , t≼uj) | inj₂ ui≺s | inj₂ t≺lj = 
    ⊥-elim (≺-impl-⋡ ui≺s (s≼t ≼-trans ≺-impl-≼ t≺lj ≼-trans ≡-impl-≽ i~j))

splitM⟦_⟧ : ∀ A i j i~j → M⟦ A ⟧ (i ⌢ j ∵ i~j) → (M⟦ A ⟧ i × M⟦ A ⟧ j)
splitM⟦ [ A ] ⟧ i j i~j σ = splitB⟦ A ⟧ i j i~j σ
splitM⟦ A ⇛ B ⟧ i j i~j f = (f₁ , f₂) where

  f₁ : ∀ k → (k ⊑ i) → B⟦ A ⟧ k → I⟦ B ⟧ k 
  f₁ k k⊑i = f k (⊑-impl-≽ k⊑i , ⊑-impl-≼ k⊑i ≼-trans ≡-impl-≼ i~j ≼-trans lb≼ub j)

  f₂ : ∀ k → (k ⊑ j) → B⟦ A ⟧ k → I⟦ B ⟧ k
  f₂ k k⊑j = f k (lb≼ub i ≼-trans ≡-impl-≼ i~j ≼-trans ⊑-impl-≽ k⊑j , ⊑-impl-≼ k⊑j) 

mset : ISet → MSet
mset A =  ( M⟦ A ⟧ , idM⟦ A ⟧ , compM⟦ A ⟧ , splitM⟦ A ⟧ )

-- Translations back and forth between M⟦ A ⟧ and I⟦ A ⟧

m→i : ∀ {A i} → M⟦ A ⟧ i → I⟦ A ⟧ i
m→i {[ A ]} {i} σ = σ
m→i {A ⇛ B} {i} f = f i ⊑-refl

i→m : ∀ {A i} → (∀ j → (j ⊑ i) → I⟦ A ⟧ j) → M⟦ A ⟧ i
i→m {[ A ]} {i} σ = σ i ⊑-refl
i→m {A ⇛ B} {i} f = f

-- M⟦ A ⟧ respects ⊑

⊑-subsum : ∀ {A i j} → (i ⊑ j) → (M⟦ A ⟧ j) → (M⟦ A ⟧ i)
⊑-subsum {A} {[ t≼u ⟩} {[ s≼v ⟩} (s≼t , u≼v) σ with splitM⟦ A ⟧ [ s≼t ⟩ [ t≼u ≼-trans u≼v ⟩ refl σ
⊑-subsum {A} {[ t≼u ⟩} {[ s≼v ⟩} (s≼t , u≼v) σ | (σ₁ , σ₂₃) with splitM⟦ A ⟧ [ t≼u ⟩ [ u≼v ⟩ refl σ₂₃
⊑-subsum {A} {[ t≼u ⟩} {[ s≼v ⟩} (s≼t , u≼v) σ | (σ₁ , σ₂₃) | (σ₂ , σ₃) = σ₂

-- Embedding of RSet into ISet

⌈_⌉ : RSet → ISet
⌈ A ⌉ = [ (λ i → ∀ t → .(t ∈ Int i) → A t) , id , comp , split ] where

  id : ∀ i i~i t → .(t ∈ Int i) → A t
  id i i~i t t∈i = ⊥-elim (≺-impl-⋡ (≺ub t∈i) (≡-impl-≼ i~i ≼-trans lb≼ t∈i))

  comp : ∀ i j i~j → ((∀ t → .(t ∈ Int i) → A t) × (∀ t → .(t ∈ Int j) → A t)) → 
    (∀ t → .(t ∈ Int (i ⌢ j ∵ i~j)) → A t)
  comp i j i~j (σ₁ , σ₂) t t∈i⌢j with ub i ≼-total fin t
  comp i j i~j (σ₁ , σ₂) t t∈i⌢j | inj₁ u≼t = σ₂ t (≡-impl-≽ i~j ≼-trans u≼t , ≺ub t∈i⌢j)
  comp i j i~j (σ₁ , σ₂) t t∈i⌢j | inj₂ t≺u = σ₁ t (lb≼ t∈i⌢j , t≺u)

  split : ∀ i j i~j → (∀ t → .(t ∈ Int (i ⌢ j ∵ i~j)) → A t) → 
    ((∀ t → .(t ∈ Int i) → A t) × (∀ t → .(t ∈ Int j) → A t))
  split i j i~j σ = 
    ( (λ t t∈i → σ t (lb≼ t∈i , ≺ub t∈i ≺-transˡ ≡-impl-≼ i~j ≼-trans lb≼ub j))
    , (λ t t∈j → σ t (lb≼ub i ≼-trans ≡-impl-≼ i~j ≼-trans lb≼ t∈j , ≺ub t∈j)) )

-- Embedding of ISet into RSet

⌊_⌋ : ISet → RSet
⌊ A ⌋ t = M⟦ A ⟧ (sing t)

-- Embedding of Set into ISet

-- We could just embed Set into RSet and then into ISet, but it's a bit
-- more efficient to optimize for constant signals.

data IList (A : Interval → Set) : Interval → Set where
  nil : ∀ {i} → (i ~ i) → IList A i
  cons : ∀ {i j} i~j → A i → IList A j → IList A (i ⌢ j ∵ i~j)

idList : ∀ {A} i → (i ~ i) → IList A i
idList i = nil

compList : ∀ {A} i j i~j → (IList A i × IList A j) → (IList A (i ⌢ j ∵ i~j))
compList [ s≼s ⟩ [ s≼t ⟩ refl (nil refl , τs) = 
  τs
compList .(i ⌢ j ∵ i~j) k j~k (cons {i} {j} i~j σ σs , τs) = 
  cons i~j σ (compList j k j~k (σs , τs))

splitList :  ∀ {A} → (∀ i j i~j → A (i ⌢ j ∵ i~j) → (A i × A j)) →
  ∀ i j i~j → IList A (i ⌢ j ∵ i~j) → (IList A i × IList A j)
splitList split [ s≼t ⟩ [ t≼s ⟩ refl (nil refl) = 
  (nil (≡-relevant (t≼s ≼-asym s≼t)) , nil (≡-relevant (s≼t ≼-asym t≼s)))
splitList split [ s≼t ⟩ [ t≼u ⟩ refl (cons {[ s≼v ⟩} {[ v≼u ⟩} refl σ σs) 
  with (src t≼u) ≼-total (src v≼u)
splitList split [ s≼t ⟩ [ t≼u ⟩ refl (cons {[ s≼v ⟩} {[ v≼u ⟩} refl σ σs) 
  | inj₁ t≼v with split [ s≼t ⟩ [ t≼v ⟩ refl σ
splitList split [ s≼t ⟩ [ t≼u ⟩ refl (cons {[ s≼v ⟩} {[ v≼u ⟩} refl σ σs)
  | inj₁ t≼v | (σ₁ , σ₂) = (cons {i = [ s≼t ⟩} {j = [ ≼-refl ⟩} refl σ₁ (nil refl) , cons refl σ₂ σs)
splitList split [ s≼t ⟩ [ t≼u ⟩ refl (cons {[ s≼v ⟩} {[ v≼u ⟩} refl σ σs) 
  | inj₂ v≺t with splitList split [ ≺-impl-≼ v≺t ⟩ [ t≼u ⟩ refl σs
splitList split [ s≼t ⟩ [ t≼u ⟩ refl (cons {[ s≼v ⟩} {[ v≼u ⟩} refl σ σs) 
  | inj₂ v≺t | (σs₁ , σs₂) = (cons refl σ σs₁ , σs₂)

data Always (A : Set) (i : Interval) : Set where
  const : A → Always A i
  var : ∀ j → .(i ⊑ j) → (∀ t → .(t ∈ Int j) → A) → Always A i

splitAlways : ∀ {A} i j i~j → Always A (i ⌢ j ∵ i~j) → (Always A i × Always A j)
splitAlways i j i~j (const a) = (const a , const a)
splitAlways i j i~j (var k i⌢j⊑k f) = 
  ( var k (⌢-inj₁ i j i~j ⊑-trans i⌢j⊑k) f
  , var k (⌢-inj₂ i j i~j ⊑-trans i⌢j⊑k) f )

⟨_⟩ : Set → ISet
⟨ A ⟩ =  [ IList (Always A) , idList , compList , splitList splitAlways ]
