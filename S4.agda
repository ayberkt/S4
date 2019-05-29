module S4 (Base : Set) where

import Relation.Binary.PropositionalEquality as Eq

open        Eq        using (_≡_; refl)
open import Data.List using (List; []; _∷_; [_])
open import Data.Nat  using (ℕ; suc; zero)

data Proposition : Set where
  `M_   : Base → Proposition
  □_    : Proposition → Proposition
  _⊃_   : Proposition → Proposition → Proposition

infix  8 `M_
infix  7 □_
infixr 6 _⊃_

data IntProp : Set where
  `I_   : Base → IntProp
  _⇒_  : IntProp → IntProp → IntProp

infix 6 `I_
infix 4  _⇒_

Context = List Proposition

data _∋_ : Context → Proposition → Set where
  hd : ∀ {φ Γ}   → (φ ∷ Γ) ∋ φ
  tl : ∀ {φ ψ Γ} → Γ ∋ φ → (ψ ∷ Γ) ∋ φ

data _,_⊢_true : Context → Context → Proposition → Set where
  hyp  : ∀ {φ Δ Γ} → Γ ∋ φ → Δ , Γ ⊢ φ true
  hyp* : ∀ {ψ Δ Γ} → Δ ∋ ψ → Δ , Γ ⊢ ψ true
  ⊃I : ∀ {φ ψ Γ Δ} → Δ , (φ ∷ Γ) ⊢ ψ true → Δ , Γ ⊢ φ ⊃ ψ true
  ⊃E : ∀ {φ ψ Δ Γ} → Δ , Γ ⊢ φ ⊃ ψ true → Δ , Γ ⊢ φ true → Δ , Γ ⊢ ψ true
  □I : ∀ {φ Δ Γ} → Δ , [] ⊢ φ true → Δ , Γ ⊢ □ φ true
  □E : ∀ {φ ψ Δ Γ} → Δ , Γ ⊢ □ φ true → (φ ∷ Δ) , Γ ⊢ ψ true → Δ , Γ ⊢ ψ true

⊢_valid : Proposition → Set
⊢ φ valid = [] , [] ⊢ φ true

reflexivity : ∀ φ → ⊢ □ φ ⊃ φ valid
reflexivity φ = ⊃I (□E (hyp hd) (hyp* hd))

-- Positive introspection.
-- I read this epistemically: if the subject knows φ then they know that they
-- know φ.
ax-4 : ∀ φ → ⊢ □ φ ⊃ □ □ φ valid
ax-4 φ = ⊃I (□E (hyp hd) (□I (□I (hyp* hd))))

dist : ∀ φ ψ → ⊢ □ (φ ⊃ ψ) ⊃ □ φ ⊃ □ ψ valid
dist φ ψ =
  let
    𝒜 : (φ ∷ φ ⊃ ψ ∷ []) , [] ⊢ ψ true
    𝒜 = ⊃E (hyp* (tl hd)) (hyp* hd)
    ℬ : [] , (□ φ ∷ □ (φ ⊃ ψ) ∷ []) ⊢ □ ψ true
    ℬ = □E (hyp (tl hd)) (□E (hyp hd) (□I 𝒜))
  in
    ⊃I (⊃I ℬ)
