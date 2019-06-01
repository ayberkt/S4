module Translation (Base : Set) where

open import Data.List using ([]; _∷_; map)

open import IPL     Base
open import IPC     Base
open import S4      Base
open import S4Terms Base
open import Context IntProp     renaming (Z to Zⱼ; S_ to Sⱼ_)
open import Context Proposition renaming (Z to Zₘ; S_ to Sₘ_)

⟦_⟧ : IntProp → Proposition
⟦ `I x   ⟧ = □ `M x
⟦ φ ⇒ ψ ⟧ = □ (⟦ φ ⟧ ⊃ ⟦ ψ ⟧)

⟦_⟧T : ∀ {Δ Γ} {φ : IntProp} →  Γ ⊢ⱼ φ → Δ , (map ⟦_⟧ Γ) ⊢ ⟦ φ ⟧
⟦_⟧T (` Zⱼ) = ` Zₘ
⟦ ` (Sⱼ n) ⟧T = {!!}
⟦_⟧T {Δ} {[]} (`λ M) = box (`λ ⟦ M ⟧T)
⟦_⟧T {Δ} {x ∷ Γ} (`λ M) = {!` x!}
⟦_⟧T {Δ} {Γ} (_$_ {φ = φ} {ψ = ψ} M N) = (let-box foo 𝒾𝓃 (Zₘ ⋆)) $ ⟦ N ⟧T
  where
    foo : Δ , (map ⟦_⟧ Γ) ⊢ □ (⟦ φ ⟧ ⊃ ⟦ ψ ⟧)
    foo = {!? ⟦ M ⟧T!}
