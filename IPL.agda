module IPL (Base : Set) where

data IntProp : Set where
  `I_   : Base → IntProp
  _⇒_  : IntProp → IntProp → IntProp

infix 6 `I_
infix 4  _⇒_
