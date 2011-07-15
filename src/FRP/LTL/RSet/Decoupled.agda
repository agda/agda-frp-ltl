open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Nat using ( ℕ ; zero ; suc )
open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import FRP.LTL.RSet.Core using ( RSet ; _[_,_⟩ ; _[_,_] ; ⟦_⟧ )
open import FRP.LTL.RSet.Causal using ( _⊵_ ; identity )
open import FRP.LTL.RSet.Stateless using ( _⇒_ )
open import FRP.LTL.RSet.Globally using ( □ )
open import FRP.LTL.RSet.Product using ( _∧_ ; _&&&_ ; fst ; snd )
open import FRP.LTL.Time using 
  ( Time ; _+_ ; _∸_ ; _≤_ ; _<_ 
  ; ≤-refl ; ≤-trans ; <-impl-≤ ; <-impl-≱ ; <-transˡ ; <-transʳ
  ; ≡-impl-≤ ; +-unit ; _≮[_]_ ; <-wo )

module FRP.LTL.RSet.Decoupled where

infixr 2 _▹_
infixr 3 _⋙ˡ_ _⋙ʳ_ _⋙ˡʳ_

-- Decoupled function space

_▹_ : RSet → RSet → RSet
(A ▹ B) t = ∀ {u} → (t ≤ u) → (A [ t , u ⟩) → B u

-- Upcast a decoupled function to a causal function

couple : ∀ {A B} → ⟦ (A ▹ B) ⇒ (A ⊵ B) ⟧
couple {A} {B} {s} f {u} s≤u σ = f s≤u σ′ where

  σ′ : A [ s , u ⟩
  σ′ s≤t t<u = σ s≤t (<-impl-≤ t<u)

-- Variants on composition which produce decoupled functions

_beforeˡ_ : ∀ {A s u v} → (A [ s , v ⟩) → (u ≤ v) → (A [ s , u ⟩)
(σ beforeˡ u≤v) s≤t t<u = σ s≤t (<-transˡ t<u u≤v)

_$ˡ_ : ∀ {A B s u} → (A ▹ B) s → (A [ s , u ⟩) → (B [ s , u ])
(f $ˡ σ) s≤t t≤u = f s≤t (σ beforeˡ t≤u)

_⋙ˡ_ : ∀ {A B C} → ⟦ (A ▹ B) ⇒ (B ⊵ C) ⇒ (A ▹ C) ⟧
(f ⋙ˡ g) s≤t σ = g s≤t (f $ˡ σ)

_beforeʳ_ : ∀ {A s u v} → (A [ s , v ⟩) → (u < v) → (A [ s , u ])
(σ beforeʳ u<v) s≤t t≤u = σ s≤t (<-transʳ t≤u u<v)

_$ʳ_ : ∀ {A B s u} → (A ⊵ B) s → (A [ s , u ⟩) → (B [ s , u ⟩)
(f $ʳ σ) s≤t t<u = f s≤t (σ beforeʳ t<u)

_⋙ʳ_ : ∀ {A B C} → ⟦ (A ⊵ B) ⇒ (B ▹ C) ⇒ (A ▹ C) ⟧
(f ⋙ʳ g) s≤t σ = g s≤t (f $ʳ σ)

_⋙ˡʳ_ : ∀ {A B C} → ⟦ (A ▹ B) ⇒ (B ▹ C) ⇒ (A ▹ C) ⟧
(f ⋙ˡʳ g) = (f ⋙ˡ couple g)

-- Fixed points

-- The following type-checks, but fails to pass the termination
-- checker, as the well-ordering on time is not made explicit:
--
-- fix : ∀ {A} → ⟦ (A ▹ A) ⇒ □ A ⟧ 
-- fix {A} {s} f {u} s≤u = f s≤u (σ u) where
--
--   σ : (u : Time) → A [ s , u ⟩
--   σ u {t} s≤t t<u = f s≤t (σ t)
--
-- To get this to pass the termination checker, we have to
-- be explicit about the induction scheme, which is
-- over < being a well-ordering on an interval.

fix : ∀ {A} → ⟦ (A ▹ A) ⇒ □ A ⟧ 
fix {A} {s} f {u} s≤u = f s≤u (σ (<-wo s≤u)) where

  σ : ∀ {u} → (∃ λ n → (s ≮[ n ] u)) → A [ s , u ⟩
  σ (zero , ())      s≤t t<u
  σ (suc n , s≮ⁿ⁺¹u) s≤t t<u = f s≤t (σ (n , s≮ⁿ⁺¹u s≤t t<u))

-- Indexed fixed points are derivable from fixed points

ifix : ∀ {A B} → ⟦ ((A ∧ B) ▹ A) ⇒ (B ▹ A) ⟧
ifix {A} {B} {s} f {v} s≤v τ = fix g s≤v ≤-refl where

  A′ : RSet
  A′ t = (t ≤ v) → A t

  g : (A′ ▹ A′) s
  g {u} s≤u σ u≤v = f s≤u ρ where

    ρ : (A ∧ B) [ s , u ⟩
    ρ s≤t t<u = (σ s≤t t<u (≤-trans (<-impl-≤ t<u) u≤v) , τ s≤t (<-transˡ t<u u≤v))

-- Loops are derivable from indexed fixed points

loop : ∀ {A B C} → ⟦ ((A ∧ B) ▹ (A ∧ C)) ⇒ (B ▹ C) ⟧
loop f = (couple (ifix (f ⋙ˡ fst)) &&& identity) ⋙ʳ f ⋙ˡ snd
