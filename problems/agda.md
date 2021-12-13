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
odule d1 where

open import Data.Bool using (false; true)
open import Data.Char using (Char; isDigit; isSpace) renaming (toℕ to toDigit)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; map; reverse)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_)
open import Data.String using (String; toList)
open import Data.Vec using (Vec; _∷_; take; tail)
open import Function using (_$_; _∘_)

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

data InvalidChar : Set where
  char : Char → InvalidChar

data ValidChar : Set where
  digit : ℕ → ValidChar
  space : ValidChar

data Token : Set where
  number : ℕ → Token
  space  : Token

scanChar : Char → Either InvalidChar ValidChar
scanChar c with isDigit c | isSpace c
... | true  | false = right ∘ digit ∘ toDigit $ c
... | false | true  = right space
... | _     | _     = left (char c)

collectScans : List (Either InvalidChar ValidChar) → Either InvalidChar (List ValidChar)
collectScans [] = right []
collectScans (s ∷ ss) with s | collectScans ss
... | left ic | _        = left ic
... | _       | left ic  = left ic
... | right v | right vs = right (v ∷ vs)

tokenize : List ValidChar → List Token
tokenize = tokenize' []
  where
    shift : ℕ → ℕ → Token
    shift n d = number (n * 10 + d)

    append : ℕ → List Token → List Token
    append d [] = (shift 0 d) ∷ []
    append d (space ∷ ts) = (shift 0 d) ∷ space ∷ ts
    append d ((number n) ∷ ts) = (shift n d) ∷ ts

    tokenize' : List Token → List ValidChar → List Token
    tokenize' ts [] = reverse ts
    tokenize' ts (space ∷ cs) = tokenize' (space ∷ ts) cs
    tokenize' ts ((digit d) ∷ cs) = tokenize' (append d ts) cs

parseTokens : List Token → List ℕ
parseTokens [] = []
parseTokens (t ∷ ts) with t
... | number n  = n ∷ parseTokens ts
... | space     = parseTokens ts

parse : String → Either InvalidChar (List ℕ)
parse = parse' ∘ collectScans ∘ map scanChar ∘ toList
  where
    parse' : Either InvalidChar (List ValidChar) → Either InvalidChar (List ℕ)
    parse' (left ic) = left ic
    parse' (right vcs) = right ∘ parseTokens ∘ tokenize $ vcs
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
