module S4Terms (Base : Set) where

import Relation.Binary.PropositionalEquality as Eq

open        Eq        using (_≡_; refl)
open import Data.List using (List; []; _∷_; [_])
open import Data.Nat  using (ℕ; suc; zero)

open import S4 Base

infix  3 _,_⊢_
infix  9 `_
infixl 7 _$_
infix  5 `λ

open import Context Proposition

data _,_⊢_ : Context → Context → Proposition → Set where
  `_          : ∀ {Δ Γ φ}   → Γ ∋ φ → Δ , Γ ⊢ φ
  _⋆          : ∀ {Δ Γ φ}   → Δ ∋ φ → Δ , Γ ⊢ φ
  `λ          : ∀ {Δ Γ φ ψ} → Δ , (φ ∷ Γ) ⊢ ψ → Δ , Γ ⊢ φ ⊃ ψ
  _$_         : ∀ {Δ Γ φ ψ} → Δ , Γ ⊢ φ ⊃ ψ → Δ , Γ ⊢ φ → Δ , Γ ⊢ ψ
  box         : ∀ {Δ Γ φ}   → Δ , [] ⊢ φ → Δ , Γ ⊢ □ φ
  let-box_𝒾𝓃_ : ∀ {Δ Γ φ ψ} → Δ , Γ ⊢ □ φ → (φ ∷ Δ) , Γ ⊢ ψ → Δ , Γ ⊢ ψ

MP : ∀ φ ψ → [] , [] ⊢ φ ⊃ (φ ⊃ ψ) ⊃ ψ
MP φ ψ = `λ (`λ (` Z $ ` S Z))

ax-4′ : ∀ φ → [] , [] ⊢ (□ φ) ⊃ (□ □ φ)
ax-4′ φ = `λ (let-box (` Z) 𝒾𝓃 box (box (Z ⋆)))

reflexivity′ : ∀ φ → [] , [] ⊢ □ φ ⊃ φ
reflexivity′ φ = `λ (let-box (` Z) 𝒾𝓃 (Z ⋆))
