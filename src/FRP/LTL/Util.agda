open import Data.Empty using ( ⊥ )
open import Data.Nat using ( ℕ ; zero ; suc ; _+_ ; _≤_ ; z≤n ; s≤s )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong )
open import Relation.Binary.PropositionalEquality.TrustMe using ( trustMe )
open import Relation.Nullary using ( ¬_ )

module FRP.LTL.Util where

infixr 5 _trans_ _∋_

-- Irrelevant projections

postulate
  .irrelevant : ∀ {A : Set} → .A → A

-- Irrelevant ≡ can be promoted to relevant ≡

≡-relevant : ∀ {A : Set} {a b : A} → .(a ≡ b) → (a ≡ b)
≡-relevant a≡b = trustMe

-- A version of ⊥-elim which takes an irrelevant argument

⊥-elim : {A : Set} → .⊥ → A
⊥-elim ()

-- An infix variant of trans

_trans_ : ∀ {X : Set} {x y z : X} → (x ≡ y) → (y ≡ z) → (x ≡ z)
refl trans refl = refl

-- Help the type inference engine out by being explicit about X.

_∋_ : (X : Set) → X → X
X ∋ x = x

-- Lemmas about addition on ℕ
-- These are from Data.Nat.Properties,
-- included here to avoid having to load all of Data.Nat.Properties' dependencies.

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero    n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

+-comm : ∀ m n → (m + n ≡ n + m)
+-comm zero    zero    = refl
+-comm zero    (suc n) = cong suc (+-comm zero n)
+-comm (suc m) n       = (cong suc (+-comm m n)) trans (sym (m+1+n≡1+m+n n m))

+-assoc : ∀ l m n → ((l + m) + n ≡ l + (m + n))
+-assoc zero    m n = refl
+-assoc (suc l) m n = cong suc (+-assoc l m n)

m+n≡0-impl-m≡0 : ∀ m n → (m + n ≡ 0) → (m ≡ 0)
m+n≡0-impl-m≡0 zero    n m+n≡0 = refl
m+n≡0-impl-m≡0 (suc m) n ()

1+n≰n : ∀ n → ¬(suc n ≤ n)
1+n≰n zero    ()
1+n≰n (suc n) (s≤s m≤n) = 1+n≰n n m≤n

≤0-impl-≡0 : ∀ {n} → (n ≤ 0) → (n ≡ 0)
≤0-impl-≡0 z≤n = refl
