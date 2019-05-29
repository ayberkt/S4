module Translation (Base : Set) where

open import S4 Base

⟦_⟧ : IntProp → Proposition
⟦ `I x   ⟧ = □ `M x
⟦ φ ⇒ ψ ⟧ = □ (⟦ φ ⟧ ⊃ ⟦ ψ ⟧)
