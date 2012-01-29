{-
Proof of a compiler from arithmetic expressions to 
stack machine. Swiped from "Hutton: Programming in Haskell."

Notes:
- Tried to use infinite stacks but the coinduction got messy.
- Now use finite stack of known size.
-}
module Hutton where

open import Data.Nat using (ℕ; _+_; suc)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; _∷_)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Abstract syntax for source language
data Expr : Set where
  val : (n : ℕ) → Expr
  add : (x y : Expr) → Expr

-- Evaluated for source language
eval : Expr → ℕ
eval (val n) = n
eval (add x y) = eval x + eval y

-- Stack machine instructions
-- Note: Parameterised by changes in stack size.
data Instr : (σ σ' : ℕ) → Set where
  push : ∀{σ} (n : ℕ) 
       → Instr σ (suc σ)
  sum2 : ∀{σ'}
       → Instr (2 + σ') (1 + σ')
  _⋆_  : ∀{σ σ' σ''}
       → (i : Instr σ σ')
       → (j : Instr σ' σ'')
       → Instr σ σ''

-- Semantics on sized stack machine
State : ℕ → Set
State σ = Vec ℕ σ

exec : ∀ {σ σ'} → Instr σ σ' → State σ → State σ'
exec (push n) s           = n ∷ s
exec sum2     (n ∷ m ∷ s) = m + n ∷ s
exec (i ⋆ j)  s           = exec j (exec i s)

-- Compiler in CPS style
compile : ∀{σ σ'} → Expr → Instr (suc σ) σ' → Instr σ σ'
compile (val n)   is = push n ⋆ is
compile (add x y) is = compile x (compile y (sum2 ⋆ is))

-- Correctness property
thm-correct : ∀ {σ σ'} x (is : Instr (suc σ) σ') s 
            → exec (compile x is) s ≡ exec is (eval x ∷ s)
thm-correct (val n) is s   = refl
thm-correct (add x y) is s
  rewrite thm-correct x (compile y (sum2 ⋆ is)) s
        | thm-correct y (sum2 ⋆ is) (eval x ∷ s) 
  = refl