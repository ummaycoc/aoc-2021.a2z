# Agda

```agda
import Data.Nat as ℕ
import Data.Fin
import Data.Vec
```

```agda
{- n A φ B
   The type of a function that consumes n A values to produce a B.
   That is, it is the function of an n-way fold of A's into B.
 -}
_ _ φ _ :  ℕ → (A : Set) → (B : Set) → Set
0 _ φ r = r
(ℕ.suc n) i φ r = i → (n i φ r)
```

```agda
{- f ↑ v
   Apply the n-wise reduction f to the length-n vector to get a reduced value.
 -}
_ ↑ _ : {A B : Set}{n : ℕ} (n A φ B) → Vec A n → B
c ↑ [] = c
f ↑ (x :: xs) = (f x) ↑ xs
```

```agda
{- f ↓ vec
   The n way reduction of a vector using the function f.
 -}
_ ↓ _ : {m : ℕ}{n : Fin (ℕ.suc m)}{A B : Set} (f : (toℕ n) A φ B) → Vec A m → Vec C (1 + m - (Fin.toℕ n))
f ↓ v with (Fin.toℕ n) ≟ m
... | Dec.yes = (f ↑ v) :: []
... | Dec.no  = (f ↑ (Vec.take (Fin.toℕ n) v)) :: (f ↓ (Vec.tail v))
``` 
