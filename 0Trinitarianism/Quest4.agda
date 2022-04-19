module 0Trinitarianism.Quest4 where

open import 0Trinitarianism.Preambles.P4

data Id {A : Type} : (x y : A) → Type where

  rfl : {x : A} → Id x x

idSym : (A : Type) (x y : A) → Id x y → Id y x
idSym A x .x rfl = rfl

_*_ : {A : Type} {x y z : A} → Id x y → Id y z → Id x z
rfl * q = q
