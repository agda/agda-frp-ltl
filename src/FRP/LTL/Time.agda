open import Function using ( _∘_ )
open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Nat using ( ℕ ; zero ; suc ) renaming ( _+_ to _+ℕ_ ; _≤_ to _≤ℕ_ )
open import Relation.Binary.PropositionalEquality using 
  ( _≡_ ; _≢_ ; refl ; sym ; cong ; cong₂ ; subst₂ ; inspect ; [_] )
open import Relation.Nullary using ( ¬_ ; Dec ; yes ; no )
open import FRP.LTL.Util using ( _trans_ ; _∋_ ; m+n≡0-impl-m≡0 ; ≤0-impl-≡0 ; 1+n≰n ) 
  renaming ( +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc )

open Relation.Binary.PropositionalEquality.≡-Reasoning using ( begin_ ; _≡⟨_⟩_ ; _∎ )

module FRP.LTL.Time where

infix 2 _≤_ _≥_ _≰_ _≱_ _<_ _>_
infixr 4 _,_
infixr 5 _≤-trans_ _<-transˡ_ _<-transʳ_ _≤-asym_ _≤-total_ 
infixl 6 _+_ _∸_

-- Time has a cancellative action _+_ which respects the monoid structure of ℕ

postulate

  Time : Set
  _+_ : Time → ℕ → Time

  +-unit : ∀ t → (t + 0 ≡ t)
  +-assoc : ∀ t m n → ((t + m) + n ≡ t + (m +ℕ n))
  +-cancelˡ : ∀ t {m n} → (t + m ≡ t + n) → (m ≡ n)
  +-cancelʳ : ∀ {s t} n → (s + n ≡ t + n) → (s ≡ t)

-- The order on time is derived from +

data _≤_ (t u : Time) : Set where
  _,_ : ∀ n → (t + n ≡ u) → (t ≤ u)

-- Floored subtraction t ∸ u is the smallest n such that t ≤ u + n

postulate

  _∸_ : Time → Time → ℕ
  t≤u+t∸u : ∀ {t u} → (t ≤ u + (t ∸ u))
  ∸-min : ∀ {t u n} → (t ≤ u + n) → (t ∸ u ≤ℕ n)

-- End of postulates.

suc-cancelʳ : ∀ {t u m n} → (t + suc m ≡ u + suc n) → (t + m ≡ u + n)
suc-cancelʳ {t} {u} {m} {n} t+1+m≡u+1+n = 
  +-cancelʳ 1 
    (+-assoc t m 1 trans 
      cong₂ _+_ refl (+ℕ-comm m 1) trans 
        t+1+m≡u+1+n trans 
          cong₂ _+_ refl (+ℕ-comm 1 n) trans 
            sym (+-assoc u n 1))

-- Syntax sugar for ≤

_≥_ : Time → Time → Set
t ≥ u = u ≤ t

_≰_ :  Time → Time → Set
t ≰ u = ¬(t ≤ u)

_≱_ :  Time → Time → Set
t ≱ u = u ≰ t

_<_ : Time → Time → Set
t < u = (t ≤ u) × (u ≰ t)

_>_ : Time → Time → Set
t > u = u < t

-- ≤ is a decidable total order

≤-refl : ∀ {t} → (t ≤ t)
≤-refl {t} = (0 , +-unit t)

_≤-trans_ : ∀ {t u v} → (t ≤ u) → (u ≤ v) → (t ≤ v)
_≤-trans_ {t} {u} {v} (m , t+m≡u) (n , u+n≡v) =
  (m +ℕ n , (sym (+-assoc t m n)) trans (cong₂ _+_ t+m≡u refl) trans u+n≡v)

≡-impl-≤ : ∀ {t u} → (t ≡ u) → (t ≤ u)
≡-impl-≤ refl = ≤-refl

≡-impl-≥ : ∀ {t u} → (t ≡ u) → (t ≥ u)
≡-impl-≥ refl = ≤-refl

_≤-asym_ : ∀ {t u} → (t ≤ u) → (u ≤ t) → (t ≡ u)
(m , t+m≡u) ≤-asym (n , u+n≡t) = 
  sym (+-unit _) trans cong₂ _+_ refl (sym m≡0) trans t+m≡u where

  m≡0 : m ≡ 0
  m≡0 = m+n≡0-impl-m≡0 m n (+-cancelˡ _ 
    (sym (+-assoc _ m n) trans 
      cong₂ _+_ t+m≡u refl trans 
        u+n≡t trans sym (+-unit _)))

≤-impl-∸≡0 : ∀ {t u} → (t ≤ u) → (t ∸ u ≡ 0)
≤-impl-∸≡0 t≤u with (∸-min (t≤u ≤-trans ≡-impl-≤ (sym (+-unit _))))
≤-impl-∸≡0 t≤u | t∸u≤0 = ≤0-impl-≡0 t∸u≤0

∸≡0-impl-≤ : ∀ {t u} → (t ∸ u ≡ 0) → (t ≤ u)
∸≡0-impl-≤ t∸u≡0 = t≤u+t∸u ≤-trans ≡-impl-≤ (cong₂ _+_ refl t∸u≡0 trans +-unit _)

∸≢0-impl-≰ : ∀ {t u n} → (t ∸ u ≡ suc n) → (t ≰ u)
∸≢0-impl-≰ t∸u≡1+n t≤u 
  with sym t∸u≡1+n trans ≤0-impl-≡0 (∸-min (t≤u ≤-trans ≡-impl-≤ (sym (+-unit _))))
∸≢0-impl-≰ t∸u≡1+n t≤u 
  | ()

t∸u≢0-impl-u∸t≡0 : ∀ t u {n} → (t ∸ u ≡ suc n) → (u ∸ t ≡ 0)
t∸u≢0-impl-u∸t≡0 t u {n} t∸u≡1+n with t≤u+t∸u {t} {u}
t∸u≢0-impl-u∸t≡0 t u {n} t∸u≡1+n | (zero , t+0≡u+t∸u) =
  ≤-impl-∸≡0 (t ∸ u , sym t+0≡u+t∸u trans +-unit t)
t∸u≢0-impl-u∸t≡0 t u {n} t∸u≡1+n | (suc m , t+1+m≡u+t∸u) = 
  ⊥-elim (1+n≰n n (subst₂ _≤ℕ_ t∸u≡1+n refl 
    (∸-min (m , suc-cancelʳ (t+1+m≡u+t∸u trans cong₂ _+_ refl t∸u≡1+n)))))

_≤-total_ : ∀ t u → (t ≤ u) ⊎ (u < t)
t ≤-total u with t ∸ u | inspect (_∸_ t) u
... | zero | [ t∸u≡0 ] = inj₁ (∸≡0-impl-≤ t∸u≡0)
... | suc n | [ t∸u≡1+n ] with t∸u≢0-impl-u∸t≡0 t u t∸u≡1+n
... | u∸t≡0 = inj₂ (∸≡0-impl-≤ u∸t≡0 , ∸≢0-impl-≰ t∸u≡1+n)

-- Case analysis on ≤

data _≤-Case_ (t u : Time) : Set where
  lt : .(t < u) → (t ≤-Case u)
  eq : .(t ≡ u) → (t ≤-Case u)
  gt : .(u < t) → (t ≤-Case u)

_≤-case_ : ∀ t u → (t ≤-Case u)
t ≤-case u with (t ∸ u) | inspect (_∸_ t) u | u ∸ t | inspect (_∸_ u) t
... | zero | [ t∸u≡0 ] | zero | [ u∸t≡0 ] = eq (∸≡0-impl-≤ t∸u≡0 ≤-asym ∸≡0-impl-≤ u∸t≡0)
... | suc n | [ t∸u≡1+n ] | zero | [ u∸t≡0 ] = gt (∸≡0-impl-≤ u∸t≡0 , ∸≢0-impl-≰ t∸u≡1+n)
... | zero | [ t∸u≡0 ] | suc w₁ | [ u∸t≡1+n ] = lt (∸≡0-impl-≤ t∸u≡0 , ∸≢0-impl-≰ u∸t≡1+n)
... | suc m | [ t∸u≡1+m ] | suc n | [ u∸t≡1+n ] with sym u∸t≡1+n trans t∸u≢0-impl-u∸t≡0 t u t∸u≡1+m
... | ()

-- + is monotone

+-resp-≤ : ∀ {t u} → (t ≤ u) → ∀ n → (t + n ≤ u + n)
+-resp-≤ (m , t+m≡u) n =
  ( m 
  , +-assoc _ n m trans 
      cong₂ _+_ refl (+ℕ-comm n m) trans 
        sym (+-assoc _ m n) trans 
          cong₂ _+_ t+m≡u refl )

+-refl-≤ : ∀ {t u} n → (t + n ≤ u + n) → (t ≤ u)
+-refl-≤ n (m , t+n+m≡u+n) = 
  ( m 
  , +-cancelʳ n 
    (+-assoc _ m n trans 
      cong₂ _+_ refl (+ℕ-comm m n) trans 
        sym (+-assoc _ n m) trans 
          t+n+m≡u+n) )

-- Lemmas about <

<-impl-≤ : ∀ {t u} → (t < u) → (t ≤ u)
<-impl-≤ (t≤u , u≰t) = t≤u

<-impl-≱ : ∀ {t u} → (t < u) → (u ≰ t)
<-impl-≱ (t≤u , u≰t) = u≰t

_<-transˡ_ : ∀ {t u v} → (t < u) → (u ≤ v) → (t < v)
_<-transˡ_ (t≤u , u≰t) u≤v = (t≤u ≤-trans u≤v , λ v≤t → u≰t (u≤v ≤-trans v≤t))

_<-transʳ_ : ∀ {t u v} → (t ≤ u) → (u < v) → (t < v)
_<-transʳ_ t≤u (u≤v , v≰u) = (t≤u ≤-trans u≤v , λ v≤t → v≰u (v≤t ≤-trans t≤u))

≤-proof-irrel′ : ∀ {t u m n} → (m ≡ n) → (t+m≡u : t + m ≡ u) → (t+n≡u : t + n ≡ u) → 
  (t ≤ u) ∋ (m , t+m≡u) ≡ (n , t+n≡u)
≤-proof-irrel′ refl refl refl = refl

t≤t+1 : ∀ {t} → (t ≤ t + 1)
t≤t+1 = (1 , refl)

t≱t+1 : ∀ {t} → (t ≱ t + 1)
t≱t+1 {t} (m , t+1+m≡t) with +-cancelˡ t (sym (+-assoc t 1 m) trans t+1+m≡t trans sym (+-unit t))
t≱t+1 (m , t+1+m≡t) | ()

t<t+1 : ∀ {t} → (t < t + 1)
t<t+1 = (t≤t+1 , t≱t+1)

<-impl-+1≤ : ∀ {t u} → (t < u) → (t + 1 ≤ u)
<-impl-+1≤ {t} ((zero  , t+0≡u)   , u≰t) = ⊥-elim (u≰t (≡-impl-≥ (sym (+-unit t) trans t+0≡u)))
<-impl-+1≤ {t} ((suc n , t+1+n≡u) , u≰t) = (n , +-assoc t 1 n trans t+1+n≡u)

+-resp-< : ∀ {t u} → (t < u) → ∀ n → (t + n < u + n)
+-resp-< (t≤u , t≱u) n = (+-resp-≤ t≤u n , λ u+n≤t+n → t≱u (+-refl-≤ n u+n≤t+n))

-- Proof irrelevance for ≤

≤-proof-irrel : ∀ {t u} → (p q : t ≤ u) → (p ≡ q)
≤-proof-irrel {t} (m , t+m≡u) (n , t+n≡u) =
  ≤-proof-irrel′ (+-cancelˡ t (t+m≡u trans (sym t+n≡u))) t+m≡u t+n≡u

-- Well ordering of < on an interval

_≮[_]_ : Time → ℕ → Time → Set
s ≮[ zero  ] u = ⊥
s ≮[ suc n ] u = ∀ {t} → (s ≤ t) → (t < u) → (s ≮[ n ] t)

<-wo′ : ∀ n {s u} → (s ≤ u) → (u ≤ s + n) → (s ≮[ suc n ] u)
<-wo′ zero {s} s≤u u≤s+0 s≤t t<u = 
  <-impl-≱ t<u (u≤s+0 ≤-trans ≡-impl-≤ (+-unit s) ≤-trans s≤t)
<-wo′ (suc n) s≤u u≤s+1+n {t} s≤t ((zero , t+0≡u) , t≱u) = 
  ⊥-elim (t≱u (≡-impl-≤ ((sym t+0≡u) trans (+-unit t))))
<-wo′ (suc n) {s} {u} s≤u (l , u+l≡s+1+n) {t} s≤t ((suc m , t+1+m≡u) , t≱u) = 
  <-wo′ n s≤t (l +ℕ m , suc-cancelʳ t+1+l+m≡s+1+n) where
    t+1+l+m≡s+1+n : t + suc (l +ℕ m) ≡ s + suc n
    t+1+l+m≡s+1+n = 
      cong₂ _+_ refl (cong suc (+ℕ-comm l m)) trans 
        sym (+-assoc t (1 +ℕ m) l) trans 
          cong₂ _+_ t+1+m≡u refl trans 
            u+l≡s+1+n

<-wo : ∀ {s u} → (s ≤ u) → ∃ λ n → (s ≮[ n ] u)
<-wo (n , s+n≡u) = (suc n , λ {t} → <-wo′ n (n , s+n≡u) (≡-impl-≤ (sym s+n≡u)) {t})
