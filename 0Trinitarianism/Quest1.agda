module 0Trinitarianism.Quest1 where

open import 0Trinitarianism.Preambles.P1

isEven : ℕ → Type
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n

{-
This is a comment block.
Remove this comment block and formulate
'there exists an even natural' here.
-}

_×_ : Type → Type → Type
A × C = Σ A (λ a → C)

div2 : Σ ℕ isEven → ℕ
div2 x = {!!}
