module Context (Proposition : Set) where

open import Data.List using (List; _∷_)

Context = List Proposition

data _∋_ : Context → Proposition → Set where
  Z  : ∀ {Γ φ}   → (φ ∷ Γ) ∋ φ
  S_ : ∀ {Γ φ ψ} → Γ ∋ φ → (ψ ∷ Γ) ∋ φ
