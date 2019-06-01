module IPC (Base : Set) where

open import Data.List using (List; _∷_)

open import IPL     Base
open import Context IntProp

infix 3 _⊢ⱼ_

data _⊢ⱼ_ : Context → IntProp → Set where
  `_  : ∀ {Γ φ}   → Γ ∋ φ → Γ ⊢ⱼ φ
  `λ  : ∀ {Γ φ ψ} → (φ ∷ Γ) ⊢ⱼ ψ → Γ ⊢ⱼ φ ⇒ ψ
  _$_ : ∀ {Γ φ ψ} → Γ ⊢ⱼ φ ⇒ ψ → Γ ⊢ⱼ φ → Γ ⊢ⱼ ψ
