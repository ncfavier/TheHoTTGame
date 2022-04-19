module 0Trinitarianism.Quest2 where

open import 0Trinitarianism.Preambles.P2

isEven : ℕ → Type
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n

existsEven : Σ ℕ isEven
existsEven = 0 , tt

_×_ : Type → Type → Type
A × C = Σ A (λ a → C)

div2 : Σ ℕ isEven → ℕ
div2 (zero , snd₁) = zero
div2 (suc (suc fst₁) , snd₁) = suc (div2 (fst₁ , snd₁))

private
  postulate
    A B C : Type

uncurry : (A → B → C) → (A × B → C)
uncurry f (a , b) = f a b

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b)
