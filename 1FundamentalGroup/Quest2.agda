-- ignore
module 1FundamentalGroup.Quest2 where
open import 1FundamentalGroup.Preambles.P2

private
  variable
    A B : Type

isSet→LoopSpace≡⊤ : {A : Type} (x : A) → isSet A → (x ≡ x) ≡ ⊤
isSet→LoopSpace≡⊤ x s = isoToPath (iso fun inv sec ret) where
     fun : x ≡ x → ⊤
     fun p = tt
     inv : ⊤ → x ≡ x
     inv tt = refl
     sec : (t : ⊤) → fun (inv t) ≡ t
     sec t = refl
     ret : (p : x ≡ x) → inv (fun p) ≡ p
     ret p = s x x refl p

data _⊔_ (A B : Type) : Type where

     inl : A → A ⊔ B
     inr : B → A ⊔ B

ℤ→ℕ⊔ℕ : ℤ → ℕ ⊔ ℕ
ℤ→ℕ⊔ℕ (pos n) = inl n
ℤ→ℕ⊔ℕ (negsuc n) = inr n
ℤ←ℕ⊔ℕ : ℕ ⊔ ℕ → ℤ
ℤ←ℕ⊔ℕ (inl n) = pos n
ℤ←ℕ⊔ℕ (inr n) = negsuc n

ℤ≡ℕ⊔ℕ : ℤ ≡ ℕ ⊔ ℕ
ℤ≡ℕ⊔ℕ = isoToPath (iso ℤ→ℕ⊔ℕ ℤ←ℕ⊔ℕ sec ret) where
     sec : (n : ℕ ⊔ ℕ) → ℤ→ℕ⊔ℕ (ℤ←ℕ⊔ℕ n) ≡ n
     sec (inl n) = refl
     sec (inr n) = refl
     ret : (z : ℤ) → ℤ←ℕ⊔ℕ (ℤ→ℕ⊔ℕ z) ≡ z
     ret (pos n) = refl
     ret (negsuc n) = refl

⊔NoConfusion : (x y : A ⊔ B) → Type
⊔NoConfusion (inl x) (inl y) = x ≡ y
⊔NoConfusion (inl x) (inr y) = ⊥
⊔NoConfusion (inr x) (inl y) = ⊥
⊔NoConfusion (inr x) (inr y) = x ≡ y

⊔NoConfusion-refl : (x : A ⊔ B) → ⊔NoConfusion x x
⊔NoConfusion-refl (inl x) = refl
⊔NoConfusion-refl (inr x) = refl

Path≡⊔NoConfusion : (x y : A ⊔ B) → (x ≡ y) ≡ ⊔NoConfusion x y
Path≡⊔NoConfusion x y = isoToPath (iso (to x y) (from x y) (sec x y) (ret x y)) where
     from : (x y : A ⊔ B) → ⊔NoConfusion x y → x ≡ y
     from (inl x) (inl y) p = cong inl p
     from (inr x) (inr y) p = cong inr p
     to : (x y : A ⊔ B) → x ≡ y → ⊔NoConfusion x y
     to x y = J (λ y _ → ⊔NoConfusion x y) (⊔NoConfusion-refl x)
     sec : (x y : A ⊔ B) → (p : ⊔NoConfusion x y) → to x y (from x y p) ≡ p
     sec (inl x) (inl y) p = {!   !}
     sec (inr x) (inr y) p = {!   !}
     ret : (x y : A ⊔ B) → (p : x ≡ y) → from x y (to x y p) ≡ p
     ret = {!   !}

isSet⊔NoConfusion : isSet A → isSet B → (x y : A ⊔ B) → isProp (⊔NoConfusion x y)
isSet⊔NoConfusion a b (inl x) (inl y) = a x y
isSet⊔NoConfusion a b (inl x) (inr y) ()
isSet⊔NoConfusion a b (inr x) (inl y) ()
isSet⊔NoConfusion a b (inr x) (inr y) = b x y

isSet⊔ : isSet A → isSet B → isSet (A ⊔ B)
isSet⊔ a b x y = endPt isProp (sym (Path≡⊔NoConfusion x y)) (isSet⊔NoConfusion a b x y)

isSetℕ⊔ℕ : isSet (ℕ ⊔ ℕ)
isSetℕ⊔ℕ = isSet⊔ isSetℕ isSetℕ

isSetℤ : isSet ℤ
isSetℤ = endPt isSet (sym ℤ≡ℕ⊔ℕ) isSetℕ⊔ℕ
