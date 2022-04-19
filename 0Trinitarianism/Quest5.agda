module 0Trinitarianism.Quest5 where

open import 0Trinitarianism.Preambles.P5

PathD : {A0 A1 : Type} (A : A0 ≡ A1) (x : A0) (y : A1) → Type
PathD A x y = transport A x ≡ y

syntax PathD A x y = x ≡ y along A

example : (x : S¹) → doubleCover x → doubleCover x
example base = Flip
example (loop i) = p i where
  lemma : (a : Bool) → transport (λ i₁ → flipPath i₁ → flipPath i₁) Flip a ≡ Flip a
  lemma false = refl
  lemma true = refl
  p : PathP (λ i → flipPath i → flipPath i) Flip Flip
  p = _≅_.inv (PathPIsoPath (λ i → flipPath i → flipPath i) Flip Flip)
              (funExt lemma)

outOfS¹P : (B : S¹ → Type) → (b : B base) → PathP (λ i → B (loop i)) b b → (x : S¹) → B x
outOfS¹P B b p base = b
outOfS¹P B b p (loop i) = p i

outOfS¹D : (B : S¹ → Type) → (b : B base) → b ≡ b along (λ i → B (loop i))
   → (x : S¹) → B x
outOfS¹D B b p x = outOfS¹P B b p' x where
  p' : PathP (λ i → B (loop i)) b b
  p' = _≅_.inv (PathPIsoPath (λ i → B (loop i)) b b) p

-- lemma : {a0 a1 b0 b1 : type} {a : a0 ≡ a1} {b : b0 ≡ b1} → (a : a1) → pathtofun (λ i → a i → b i) f a ≡ pathtofun b (f (pathtofun (sym a) a))
-- lemma = ?

pathToFun→ : {A0 A1 B0 B1 : Type} {A : A0 ≡ A1} {B : B0 ≡ B1} → (f : A0 → B0) →
  pathToFun (λ i → A i → B i) f ≡ λ a1 → pathToFun B (f (pathToFun (sym A) a1))
pathToFun→ {A0} {A1} {B0} {B1} {A} {B} f = funExt {!   !}  where
  lemma : (a : A1) → pathToFun (λ i → A i → B i) f a ≡ pathToFun B (f (pathToFun (sym A) a))
  lemma a = {!   !}
