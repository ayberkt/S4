module Examples where

open import Data.Nat using (ℕ; suc; zero)

data Name : Set where
  A B C D E : Name

open import S4          Name
open import Translation Name

MP : IntProp
MP = (`I A ⇒ (`I A ⇒ `I B)) ⇒ `I B

MP□ : Proposition
MP□ = ⟦ MP ⟧
