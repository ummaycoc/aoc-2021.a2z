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

```agda
data InvalidChar where
  char : Char → InvalidChar

data ValidChar where
  digit : Fin 10 → ValidChar
  space : ValidChar

data Token where
  number : ℕ → Token
  space : Token

scanChar : Char → Either InvalidChar ValidChar
scanChar c with isDigit c | isSpace c
... | false | false = left $ char c
... | true  | false = right $ digit ((Fin ∘ toℕ) c)
... | false | true  = right space

collectScans : List (Either InvalidChar ValidChar) → Either InvalidChar (List ValidChar)
collectScans [] = right []
collectScans s:ss with s | collectScans ss
... | (left ic) _ = left ic
... | _ (left ic) = left ic
... | (right v) (right vs) = right (v :: vs)

tokenize : List ValidChar → List Token
tokenize = tokenize' []
  where
    tokenize' : List Token → List ValidChar → List Token
    tokenize' ts [] = reverse ts
    tokenize' ts (space :: cs) = tokenize' (space :: ts) cs
    tokenize' ts ((digit d) :: cs) = tokenize' (append d ts) cs

    append : Fin 10 → List Token → List Token
    append d [] = (shift 0 d) :: []
    append d (space :: ts) = (shift 0 d) :: space :: ts
    append d ((number n) :: ts) = (shift n d) :: ts

    shift : ℕ → Fin 10 → Token
    shift n d = n * 10 + (toℕ d)

parseTokens : List Token → List ℕ
parseTokens (t :: ts) with t
... | number n  = n :: parse ts
... | space     = parse ts

parse :: String → Either InvalidChar (List ℕ)
parse data = with collectScans ∘ map scanChar ∘ toList $ data
... | (left ic) = left ic
... | (right vcs) = parseTokens ∘ tokenize $ vcs
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
