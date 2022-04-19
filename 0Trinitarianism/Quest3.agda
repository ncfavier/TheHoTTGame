module 0Trinitarianism.Quest3 where

open import 0Trinitarianism.Preambles.P3

_+_ : ℕ → ℕ → ℕ
n + zero = n
n + suc m = suc (n + m)

even+even-isEven : (n m : Σ ℕ isEven) → isEven (n .fst + m .fst)
even+even-isEven (n , ne) (zero , me) = ne
even+even-isEven (n , ne) (suc (suc m) , me) = even+even-isEven (n , ne) (m , me)
