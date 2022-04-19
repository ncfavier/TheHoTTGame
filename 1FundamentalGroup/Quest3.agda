module 1FundamentalGroup.Quest3 where

open import 1FundamentalGroup.Preambles.P3

loopSucℤtimes : (n : ℤ) → loop n times ∙ loop ≡ loop sucℤ n times
loopSucℤtimes (pos n) = refl
loopSucℤtimes (negsuc zero) = sym∙ loop
loopSucℤtimes (negsuc (suc n)) =
    (loop (negsuc n) times ∙ sym loop) ∙ loop
  ≡⟨ sym (assoc _ _ _) ⟩
    loop (negsuc n) times ∙ (sym loop ∙ loop)
  ≡⟨ cong (λ p → loop (negsuc n) times ∙ p) (sym∙ _) ⟩
    loop (negsuc n) times ∙ refl
  ≡⟨ sym (∙Refl _) ⟩
    loop (negsuc n) times ∎

sucℤPredℤ : (n : ℤ) → sucℤ (predℤ n) ≡ n
sucℤPredℤ (pos zero) = refl
sucℤPredℤ (pos (suc n)) = refl
sucℤPredℤ (negsuc n) = refl

pathToFun→ : {A0 A1 B0 B1 : Type} {A : A0 ≡ A1} {B : B0 ≡ B1} → (f : A0 → B0) →
  pathToFun (λ i → A i → B i) f ≡ λ a1 → pathToFun B (f (pathToFun (sym A) a1))
pathToFun→ f = refl

pathToFunPathFibration : {A : Type} {x y z : A} (q : x ≡ y) (p : y ≡ z) →
  pathToFun (λ i → x ≡ p i) q ≡ q ∙ p
pathToFunPathFibration {A} {x} {y} q = J (λ z p → pathToFun (λ i → x ≡ p i) q ≡ q ∙ p)
  (
    pathToFun refl q
  ≡⟨ pathToFunRefl q ⟩
    q
  ≡⟨ ∙Refl q ⟩
    q ∙ refl ∎
  )

rewind : (x : S¹) → helix x → base ≡ x
rewind = outOfS¹D (λ x → helix x → base ≡ x) loop_times
  (
    pathToFun (λ i → sucℤPath i → base ≡ loop i) loop_times
  ≡⟨ refl ⟩
    (λ n → pathToFun (λ i → base ≡ loop i) (loop_times (pathToFun (λ i → sucℤPath (~ i)) n)))
  ≡⟨ refl ⟩
    (λ n → pathToFun (λ i → base ≡ loop i) (loop predℤ n times))
  ≡⟨ (λ i n → pathToFunPathFibration (loop predℤ n times) loop i) ⟩
    (λ n → loop predℤ n times ∙ loop)
  ≡⟨ (λ i n → loopSucℤtimes (predℤ n) i) ⟩
    (λ n → loop sucℤ (predℤ n) times)
  ≡⟨ (λ i n → loop sucℤPredℤ n i times) ⟩
    loop_times ∎
  )

windingNumberRewindBase : (n : ℤ) → windingNumberBase (loop n times) ≡ n
windingNumberRewindBase (pos zero) = refl
windingNumberRewindBase (pos (suc n)) = cong sucℤ (windingNumberRewindBase (pos n))
windingNumberRewindBase (negsuc zero) = refl
windingNumberRewindBase (negsuc (suc n)) = cong predℤ (windingNumberRewindBase (negsuc n))

windingNumberRewind : (x : S¹) (n : helix x) → windingNumber x (rewind x n) ≡ n
windingNumberRewind = outOfS¹D _ windingNumberRewindBase
  (
    pathToFun (λ i → (n : sucℤPath i) → windingNumber (loop i) (rewind (loop i) n) ≡ n) windingNumberRewindBase
  ≡⟨ funExt (λ n → isSetℤ _ _ _ _) ⟩
    windingNumberRewindBase ∎
  )

rewindWindingNumber : (x : S¹) (p : base ≡ x) → rewind x (windingNumber x p) ≡ p
rewindWindingNumber x = J (λ x p → rewind x (windingNumber x p) ≡ p) refl

loopSpaceS¹≡ℤ : loopSpace S¹ base ≡ ℤ
loopSpaceS¹≡ℤ = isoToPath (iso windingNumberBase (rewind base) windingNumberRewindBase (rewindWindingNumber base))
