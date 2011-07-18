open import FRP.LTL.RSet.Core using ( RSet ; ⟦_⟧ )
open import FRP.LTL.RSet.Stateless using ( _⇒_ )
open import FRP.LTL.Time using ( _≤_ ; ≤-refl ; _≤-trans_ )

module FRP.LTL.RSet.Globally where

-- □ A is "A holds globally in the future"

□ : RSet → RSet
□ A t = ∀ {u} → (t ≤ u) → A u

-- Comonad structure of □

extend : ∀ {A B} → ⟦ A ⇒ B ⟧ → ⟦ □ A ⇒ □ B ⟧
extend f a s≤t = f (a s≤t)

extract : ∀ {A} → ⟦ □ A ⇒ A ⟧
extract a = a ≤-refl

duplicate : ∀ {A} → ⟦ □ A ⇒ □ (□ A) ⟧
duplicate a s≤t t≤u = a (s≤t ≤-trans t≤u)

-- Applicative structure of □

[_] : ∀ {A} → ⟦ A ⟧ → ⟦ □ A ⟧
[ a ] s≤t = a

_⟨*⟩_ : ∀ {A B} → ⟦ □ (A ⇒ B) ⇒ □ A ⇒ □ B ⟧
(f ⟨*⟩ a) s≤t = f s≤t (a s≤t)