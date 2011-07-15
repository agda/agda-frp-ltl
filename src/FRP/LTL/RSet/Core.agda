open import FRP.LTL.Time using ( Time ; _≤_ ; _<_ )

module FRP.LTL.RSet.Core where

-- Reactive types

RSet : Set₁
RSet = Time → Set

⟨_⟩ : Set → RSet
⟨ A ⟩ t = A

⟦_⟧ : RSet → Set
⟦ A ⟧ = ∀ {t} → (A t)

-- Reactive sets over an interval

_[_,_] : RSet → Time → Time → Set
A [ s , u ] = ∀ {t} → s ≤ t → t ≤ u → A t

_[_,_⟩ : RSet → Time → Time → Set
A [ s , u ⟩ = ∀ {t} → s ≤ t → t < u → A t
