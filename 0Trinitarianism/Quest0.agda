module 0Trinitarianism.Quest0 where
open import 0Trinitarianism.Preambles.P0

data ⊤ : Type where
  tt : ⊤

TrueToTrue : ⊤ → ⊤
TrueToTrue = λ x → x

TrueToTrue' : ⊤ → ⊤
TrueToTrue' tt = tt

data ⊥ : Type where

explosion : ⊥ → ⊤
explosion ()

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ
