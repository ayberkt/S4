module Translation (Base : Set) where

open import Data.List using ([]; _∷_) renaming (map to _⟨$⟩_)
open import Data.Product using (_×_)

open import IPC Base    renaming (`_ to `I_)
open import S4  Base    renaming (`_ to `M_)
open import Context

⟦_⟧ : IntProp → S4Prop
⟦ IntBase b ⟧ = □ S4Base b
⟦ φ ⇒ ψ    ⟧ = □ (⟦ φ ⟧ ⊃ ⟦ ψ ⟧)

⟦_⟧V : ∀ {Γ φ} → Γ ∋ φ → (⟦_⟧ ⟨$⟩ Γ) ∋ ⟦ φ ⟧
⟦ Z   ⟧V = Z
⟦ S i ⟧V = S ⟦ i ⟧V

⟦_⟧T : ∀ {Γ} {φ : IntProp} →  Γ ⊢ⱼ φ →  [] , (⟦_⟧ ⟨$⟩ Γ) ⊢ ⟦ φ ⟧
⟦ `I i ⟧T                    = `M ⟦ i ⟧V
⟦ M $ N ⟧T                   = let-box ⟦ M ⟧T 𝒾𝓃 (Z ⋆) $ ⟦ N ⟧T
⟦_⟧T {[]}    {φ ⇒ ψ} (`λ M) = quot (`λ ⟦ M ⟧T)
⟦_⟧T {_ ∷ Γ} {φ ⇒ ψ} (`λ M) = quot (`λ {!!})

⟦_⟧M : ∀ {φ : IntProp} → [] ⊢ⱼ φ → [] , [] ⊢ ⟦ φ ⟧
⟦_⟧M = ⟦_⟧T
