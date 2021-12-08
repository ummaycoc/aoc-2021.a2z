# Agda

```agda
import Data.Nat as ℕ
import Data.Fin
import Data.Vec
```

```agda
{- φ n A B
   The type of a function that consumes n A values to produce a B.
   That is, it is the function of an n-way fold of A's into B.
 -}
φ : ℕ → (A : Set) → (B : Set) → Set
φ 0 _ r = r
φ (ℕ.suc n) i r = i → (φ n i r)
```

```agda
{- f ↑ v
   Apply the n-wise reduction f to the length-n vector to get a reduced value.
 -}
_ ↑ _ : {A B : Set}{n : ℕ} (φ n A B) → Vec A n → B
c ↑ [] = c
f ↑ (x :: xs) = (f x) ↑ xs
```

```agda
{- f ↓ vec
   The n way reduction of a vector using the function f.
 -}
_ ↓ _ : {m : ℕ}{n : Fin (ℕ.suc m)}{A B : Set} (f : φ (toℕ n) A B) → Vec A m → Vec C (1 + m - (Fin.toℕ n))
f ↓ v with (Fin.toℕ n) ≟ m
... | Dec.yes = (f ↑ v) :: []
... | Dec.no  = (f ↑ (Vec.take (Fin.toℕ n) v)) :: (f ↓ (Vec.tail v))
``` 

---- Getting it going ----
```agda
module d1 where

open import Data.Nat as ℕ using (ℕ; suc; _+_; _∸_)
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (Vec; _∷_; take; tail)

{- φ n A B
   The type of a function that consumes n A values to produce a B.
   That is, it is the function of an n-way fold of A's into B.
 -}
φ : ℕ → (A : Set) → (B : Set) → Set
φ 0 _ b = b
φ (suc n) a b = a → (φ n a b)

{- f ↑ v
   Apply the n-wise reduction f to the length-n vector to get a reduced value.
 -}
_↑_ : {A B : Set} → {n : ℕ} → (φ n A B) → Vec A n → B
c ↑ Vec.[] = c
f ↑ (x ∷ xs) = (f x) ↑ xs

{- f ↓ vec
   The n way reduction of a vector using the function f.
 -}
_↓_ : {m : ℕ}{n : Fin (suc m)}{A B : Set} (f : φ (toℕ n) A B) → Vec A m → Vec B (1 + m ∸ (toℕ n))
f ↓ v with (toℕ n) ≟ m
... | Dec.yes = (f ↑ v) :: []
... | Dec.no  = (f ↑ (take (toℕ n) v)) :: (f ↓ (tail v))
```
