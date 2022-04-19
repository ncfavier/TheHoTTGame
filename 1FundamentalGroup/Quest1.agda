-- ignore
module 1FundamentalGroup.Quest1 where
open import 1FundamentalGroup.Preambles.P1


loopSpace : (A : Type) (a : A) → Type
loopSpace A a = a ≡ a

loop_times : ℤ → loopSpace S¹ base
loop pos zero times = Refl
loop pos (suc n) times = loop pos n times ∙ loop
loop negsuc zero times = sym loop
loop negsuc (suc n) times = loop negsuc n times ∙ sym loop

sucℤ : ℤ → ℤ
sucℤ (pos n) = pos (suc n)
sucℤ (negsuc zero) = pos zero
sucℤ (negsuc (suc n)) = negsuc n

predℤ : ℤ → ℤ
predℤ (pos zero) = negsuc zero
predℤ (pos (suc n)) = pos n
predℤ (negsuc n) = negsuc (suc n)

sucℤIso : ℤ ≅ ℤ
sucℤIso = iso sucℤ predℤ sec ret where
  sec : (n : ℤ) → sucℤ (predℤ n) ≡ n
  sec (pos zero) = refl
  sec (pos (suc n)) = refl
  sec (negsuc n) = refl
  ret : (n : ℤ) → predℤ (sucℤ n) ≡ n
  ret (pos n) = refl
  ret (negsuc zero) = refl
  ret (negsuc (suc n)) = refl

sucℤPath : ℤ ≡ ℤ
sucℤPath = isoToPath sucℤIso

helix : S¹ → Type
helix base = ℤ
helix (loop i) = sucℤPath i

windingNumberBase : base ≡ base → ℤ
windingNumberBase p = endPt helix p (pos zero)

windingNumber : (x : S¹) → base ≡ x → helix x
windingNumber x p = endPt helix p (pos zero)

-- foo : (n : ℤ) → windingNumberBase (loop n times) ≡ n
-- foo n = {!   !}
