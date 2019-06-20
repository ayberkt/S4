module Context where

open import Data.List using (List; _∷_)

Context : Set → Set
Context = List

data _∋_ {A : Set} : List A → A → Set where
  Z  : ∀ {Γ} {φ   : A} → (φ ∷ Γ) ∋ φ
  S_ : ∀ {Γ} {φ ψ : A} → Γ ∋ φ → (ψ ∷ Γ) ∋ φ
