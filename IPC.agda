module IPC (Base : Set) where

open import Data.List using (List; _∷_)

data IntProp : Set where
  IntBase : Base → IntProp
  _⇒_    : IntProp → IntProp → IntProp

open import Context IntProp

infix 4  _⇒_

infix 3 _⊢ⱼ_

data _⊢ⱼ_ : Context → IntProp → Set where
  `_  : ∀ {Γ φ}   → Γ ∋ φ → Γ ⊢ⱼ φ
  `λ  : ∀ {Γ φ ψ} → (φ ∷ Γ) ⊢ⱼ ψ → Γ ⊢ⱼ φ ⇒ ψ
  _$_ : ∀ {Γ φ ψ} → Γ ⊢ⱼ φ ⇒ ψ → Γ ⊢ⱼ φ → Γ ⊢ⱼ ψ
