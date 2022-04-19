-- ignore
module 1FundamentalGroup.Quest0 where
open import 1FundamentalGroup.Preambles.P0

Refl : base ≡ base
Refl = λ i → base

Flip : Bool → Bool
Flip false = true
Flip true = false

Flip-involutive : (b : Bool) → Flip (Flip b) ≡ b
Flip-involutive false = refl
Flip-involutive true = refl

flipIso : Bool ≅ Bool
flipIso = iso Flip Flip Flip-involutive Flip-involutive

flipPath : Bool ≡ Bool
flipPath = isoToPath flipIso

doubleCover : S¹ → Type
doubleCover base = Bool
doubleCover (loop i) = flipPath i

true-loop-false : PathP (λ i → flipPath i) true false
true-loop-false = transport-filler flipPath true

endPtOfTrue : base ≡ base → doubleCover base
endPtOfTrue p = endPt doubleCover p true

Refl≢loop : Refl ≡ loop → ⊥
Refl≢loop p = true≢false λ i → endPtOfTrue (p i)

------------------- Side Quest - Empty -------------------------

toEmpty : (A : Type) → Type
toEmpty A = A → ⊥

pathEmpty : (A : Type) → Type₁
pathEmpty A = A ≡ ⊥

isoEmpty : (A : Type) → Type
isoEmpty A = A ≅ ⊥

outOf⊥ : (A : Type) → ⊥ → A
outOf⊥ A ()

toEmpty→isoEmpty : (A : Type) → toEmpty A → isoEmpty A
toEmpty→isoEmpty A e = iso e (outOf⊥ A) sec ret where
  sec : (b : ⊥) → e (outOf⊥ A b) ≡ b
  sec ()
  ret : (a : A) → outOf⊥ A (e a) ≡ a
  ret a = outOf⊥ _ (e a)

isoEmpty→pathEmpty : (A : Type) → isoEmpty A → pathEmpty A
isoEmpty→pathEmpty A = isoToPath

pathEmpty→toEmpty : (A : Type) → pathEmpty A → toEmpty A
pathEmpty→toEmpty A = pathToFun

------------------- Side Quests - true≢false --------------------

boolBundle : Bool -> Type
boolBundle false = ⊥
boolBundle true = ⊤

true≢false' : true ≡ false → ⊥
true≢false' p = endPt boolBundle p tt
