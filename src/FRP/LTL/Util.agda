open import Data.Nat using ( ℕ ; zero ; suc ; _+_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong )

module FRP.LTL.Util where

infixr 5 _trans_

-- An infix variant of trans

_trans_ : ∀ {X : Set} {x y z : X} → (x ≡ y) → (y ≡ z) → (x ≡ z)
refl trans refl = refl

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
