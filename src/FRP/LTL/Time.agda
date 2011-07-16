open import Function using ( _∘_ )
open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Nat using ( ℕ ; zero ; suc ) renaming ( _+_ to _+ℕ_ ; _≤_ to _≤ℕ_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; _≢_ ; refl ; sym ; cong ; cong₂ )
open import Relation.Nullary using ( ¬_ ; Dec ; yes ; no )
open import FRP.LTL.Util using ( _trans_ ) renaming ( +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc )

open Relation.Binary.PropositionalEquality.≡-Reasoning using ( begin_ ; _≡⟨_⟩_ ; _∎ )

module FRP.LTL.Time where

infix 2 _≤_ _≥_ _≰_ _≱_ _<_ _>_
infixr 4 _,_
infixr 5 _≤-trans_ _<-transˡ_ _<-transʳ_ _≤-asym_ _≤-total_ 
infixl 6 _+_ _∸_

postulate

  Time : Set
  _+_ : Time → ℕ → Time

  +-unit : ∀ t → (t + 0 ≡ t)
  +-assoc : ∀ t m n → ((t + m) + n ≡ t + (m +ℕ n))
  +-cancel : ∀ {s t} n → (s + n ≡ t + n) → (s ≡ t)

data _≤_ (t u : Time) : Set where
  _,_ : ∀ n → (t + n ≡ u) → (t ≤ u)

postulate

  _≤-asym_ : ∀ {t u} → (t ≤ u) → (u ≤ t) → (t ≡ u)
  _≤-total_ : ∀ t u → (t ≤ u) ⊎ (u ≤ t)
  _∸_ : Time → Time → ℕ
  t≤u+t∸u : ∀ {t u} → (t ≤ u + (t ∸ u))
  ∸-min : ∀ {t u n} → (t ≤ u + n) → (t ∸ u ≤ℕ n)

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

≤-refl : ∀ {t} → (t ≤ t)
≤-refl {t} = (0 , +-unit t)

_≤-trans_ : ∀ {t u v} → (t ≤ u) → (u ≤ v) → (t ≤ v)
_≤-trans_ {t} {u} {v} (m , t+m≡u) (n , u+n≡v) =
  (m +ℕ n , (sym (+-assoc t m n)) trans (cong₂ _+_ t+m≡u refl) trans u+n≡v)

≡-impl-≤ : ∀ {t u} → (t ≡ u) → (t ≤ u)
≡-impl-≤ refl = ≤-refl

<-impl-≤ : ∀ {t u} → (t < u) → (t ≤ u)
<-impl-≤ (t≤u , u≰t) = t≤u

<-impl-≱ : ∀ {t u} → (t < u) → (u ≰ t)
<-impl-≱ (t≤u , u≰t) = u≰t

_<-transˡ_ : ∀ {t u v} → (t < u) → (u ≤ v) → (t < v)
_<-transˡ_ (t≤u , u≰t) u≤v = (t≤u ≤-trans u≤v , λ v≤t → u≰t (u≤v ≤-trans v≤t))

_<-transʳ_ : ∀ {t u v} → (t ≤ u) → (u < v) → (t < v)
_<-transʳ_ t≤u (u≤v , v≰u) = (t≤u ≤-trans u≤v , λ v≤t → v≰u (v≤t ≤-trans t≤u))

_≮[_]_ : Time → ℕ → Time → Set
s ≮[ zero  ] u = ⊥
s ≮[ suc n ] u = ∀ {t} → (s ≤ t) → (t < u) → (s ≮[ n ] t)

<-wo′ : ∀ n {s u} → (s ≤ u) → (u ≤ s + n) → (s ≮[ suc n ] u)
<-wo′ zero {s} s≤u u≤s+0 s≤t t<u = 
  <-impl-≱ t<u (u≤s+0 ≤-trans ≡-impl-≤ (+-unit s) ≤-trans s≤t)
<-wo′ (suc n) s≤u u≤s+1+n {t} s≤t ((zero , t+0≡u) , t≱u) = 
  ⊥-elim (t≱u (≡-impl-≤ ((sym t+0≡u) trans (+-unit t))))
<-wo′ (suc n) {s} {u} s≤u (l , u+l≡s+1+n) {t} s≤t ((suc m , t+1+m≡u) , t≱u) = 
  <-wo′ n s≤t (l +ℕ m , +-cancel 1 t+l+m+1≡s+n+1) where
    t+l+m+1≡s+n+1 : t + (l +ℕ m) + 1 ≡ s + n + 1
    t+l+m+1≡s+n+1 = 
      begin
        (t + (l +ℕ m)) + 1
      ≡⟨ +-assoc t (l +ℕ m) 1 ⟩
        t + ((l +ℕ m) +ℕ 1)
      ≡⟨ cong₂ _+_ refl (+ℕ-comm (l +ℕ m) 1) ⟩
        t + (1 +ℕ (l +ℕ m))
      ≡⟨ cong₂ _+_ refl (cong suc (+ℕ-comm l m)) ⟩
        t + (1 +ℕ (m +ℕ l))
      ≡⟨ sym (+-assoc t (1 +ℕ m) l) ⟩
        (t + (1 +ℕ m)) + l
      ≡⟨ cong₂ _+_ t+1+m≡u refl ⟩
        u + l
      ≡⟨ u+l≡s+1+n ⟩
        s + (1 +ℕ n)
      ≡⟨ cong₂ _+_ refl (+ℕ-comm 1 n) ⟩
        s + (n +ℕ 1)
      ≡⟨ sym (+-assoc s n 1) ⟩
        (s + n) + 1
      ∎

<-wo : ∀ {s u} → (s ≤ u) → ∃ λ n → (s ≮[ n ] u)
<-wo (n , s+n≡u) = (suc n , λ {t} → <-wo′ n (n , s+n≡u) (≡-impl-≤ (sym s+n≡u)) {t})
