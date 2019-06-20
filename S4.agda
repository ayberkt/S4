module S4 (Base : Set) where

import Relation.Binary.PropositionalEquality as Eq

open        Eq        using (_≡_; refl)
open import Data.List using (List; []; _∷_; [_])
open import Data.Nat  using (ℕ; suc; zero)

data S4Prop : Set where
  S4Base : Base → S4Prop
  □_     : S4Prop → S4Prop
  _⊃_    : S4Prop → S4Prop → S4Prop

open import Context

infix  7 □_
infixr 6 _⊃_

infix  3 _,_⊢_
infix  9 `_
infixl 7 _$_
infix  5 `λ

data _,_⊢_ : Context S4Prop → Context S4Prop → S4Prop → Set where
  `_          : ∀ {Δ Γ φ}   → Γ ∋ φ → Δ , Γ ⊢ φ
  _⋆          : ∀ {Δ Γ φ}   → Δ ∋ φ → Δ , Γ ⊢ φ
  `λ          : ∀ {Δ Γ φ ψ} → Δ , (φ ∷ Γ) ⊢ ψ → Δ , Γ ⊢ φ ⊃ ψ
  _$_         : ∀ {Δ Γ φ ψ} → Δ , Γ ⊢ φ ⊃ ψ → Δ , Γ ⊢ φ → Δ , Γ ⊢ ψ
  quot        : ∀ {Δ Γ φ}   → Δ , [] ⊢ φ → Δ , Γ ⊢ □ φ
  let-box_𝒾𝓃_ : ∀ {Δ Γ φ ψ} → Δ , Γ ⊢ □ φ → (φ ∷ Δ) , Γ ⊢ ψ → Δ , Γ ⊢ ψ

-- Some example theorems in modal logic.

MP : ∀ φ ψ → [] , [] ⊢ φ ⊃ (φ ⊃ ψ) ⊃ ψ
MP φ ψ = `λ (`λ (` Z $ ` S Z))

ax-4 : ∀ φ → [] , [] ⊢ □ φ ⊃ □ □ φ
ax-4 _ = `λ (let-box ` Z 𝒾𝓃 quot (quot (Z ⋆)))

reflexivity′ : ∀ φ → [] , [] ⊢ □ φ ⊃ φ
reflexivity′ φ = `λ (let-box (` Z) 𝒾𝓃 (Z ⋆))
