\begingroup

\paragraph{Proof of McCarthy-Painter}

This is an encoding of the seminal compiler correctness problem
from \citet{mccarthy1967} using the accumulating compile function trick from
\citet{Hutton2007}.

\paragraph{Interface}
Agda is interfaced through a custom emacs mode which provides many useful
features such as unicode character entry, on-the-fly type checking and
highlighting of compilation errors.

An interesting feature is the ability to introduce \emph{``holes''} into
function and type definitions. These \emph{holes} represent incomplete 
definitions and can only be filled by expressions satisfying the relevant type
constraints. In many cases, Agda can complete the expressions automatically.

These \emph{holes}, when used in the context of \emph{types as propositions}
represent unresolved proof obligations.

\paragraph{Standard library}
Agda focuses on being a programming language first and a theorem prover second.
Therefore, many of its idioms are derived from the programming world. For
example standard library of data structures and lemmas is highly modularised.

%\snugshade
\rule{\textwidth}{0.1pt}%
\nopagebreak
\begin{code}
module McCarthy where

open import Data.Empty
  using (⊥-elim)
open import Data.Fin
  using (Fin; zero; suc; toℕ)
open import Data.Integer
  using (ℤ)
  renaming (_+_ to _ℤ+_)
open import Data.List
  using (List; []; _∷_)
open import Data.Nat
  using (ℕ; _+_; zero; suc; _≟_; _<_; decTotalOrder
        ; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-step; ≤-steps; 1+n≰n)
open import Data.Product
  using (_×_; _,_; ∃)
open import Data.Vec
  using (Vec; lookup)
open import Relation.Nullary
  using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; module ≡-Reasoning; cong; trans)
open ≡-Reasoning
  using (begin_; _∎; _≡⟨_⟩_)
open import Relation.Binary 
  using (module DecTotalOrder)
open DecTotalOrder decTotalOrder 
  using () renaming (refl to ≤-refl)
\end{code}
\nopagebreak
\rule{\textwidth}{0.1pt}%
%\endsnugshade

\paragraph{Proof scripts}
Programs look very similar to those written in Haskell. Data structures are
written in the generalised algebraic data structure style. One very visible
feature of Agda is the availability of unicode characters as identifiers.

%\snugshade
\rule{\textwidth}{0.1pt}%
\nopagebreak
\begin{code}
-- Source syntax and semantics

data Expr (novs : ℕ) : Set where
  Lit   : (n : ℤ)            → Expr novs
  Var   : (v : Fin novs)     → Expr novs
  _:+_  : (x y : Expr novs)  → Expr novs

Source : ℕ → Set
Source novs = Vec ℤ novs

eval : ∀{novs} → Expr novs → Source novs → ℤ
eval (Lit n)   s = n
eval (Var v)   s = lookup v s
eval (x :+ y)  s = eval x s ℤ+ eval y s

-- Target language and semantics

data Inst : Set where
-- Load immediate value @n@ into accumulator
  LI    : (n : ℤ)  → Inst
-- Load from register @r@ into accumulator
  LOAD  : (r : ℕ)  → Inst
-- Store accumulator value to register @r@
  STOR  : (r : ℕ)  → Inst
-- Add the value of register @r@ to the accumulator
  ADD   : (r : ℕ)  → Inst

Insts = List Inst
\end{code}
\nopagebreak

\nopagebreak
\begin{code}
Target : Set
Target = (ℤ × (ℕ → ℤ))
\end{code}
\nopagebreak

\nopagebreak
\begin{code}
update : (ℕ → ℤ) → ℕ → ℤ → ℕ → ℤ
update f k v k' with k ≟ k'
update f k v .k | yes refl  = v
update f k v k' | no  k≠k'  = f k'
\end{code}
\nopagebreak

\nopagebreak
\begin{code}
exec : Insts → Target → Target
exec []             s = s
exec (LI n    ∷ is) (a , rs) = exec is (n , rs)
exec (LOAD r  ∷ is) (a , rs) = exec is (rs r , rs)
exec (STOR r  ∷ is) (a , rs) = exec is (a , update rs r a)
exec (ADD r   ∷ is) (a , rs) = exec is (a ℤ+ rs r , rs)
\end{code}
\nopagebreak
\rule{\textwidth}{0.1pt}%
%\endsnugshade

The compiler is written in a continuation passing style,
as described in \citet[section 13.7]{Hutton2007}. It
assumes that variables are mapped to the first @novs@
registers.

The argument @r@ represents the next register (offset by @novs@)
that can be safely used as a temporary store. The argument @is@
contains instructions to be appended on to the end of the 
expression's compiled form.

%\snugshade
\rule{\textwidth}{0.1pt}%
\nopagebreak
\begin{code}
compile : ∀{novs} → ℕ → Expr novs → Insts → Insts
compile         r (Lit n)   is  = LI n ∷ is
compile         r (Var v)   is  = LOAD (toℕ v) ∷ is
compile {novs}  r (x :+ y)  is  = compile r y (STOR (r + novs)
                                ∷ compile (suc r) x (ADD (r + novs) ∷ is))
\end{code}
\nopagebreak
\rule{\textwidth}{0.1pt}%
%\endsnugshade

\paragraph{Proof style}
The proof style in Agda is to write terms, representing proofs, that inhabit 
types, representing propositions. This has two benefits. It comes very naturally
to someone from a statically-typed functional programming background and it
is very close to the underlying logic, Martin-Löf's 
\citeyearpar{martin1971theory} type theory.

The proof steps are natural structures and there is no basic vocabulary to 
learn, in contrast with the other three tools.

\paragraph{Lemmas}
Three lemmas are required. The lemma identified @Lemma-Readwrite@ states
that if a register is written to and then immediately read back, the
resulting value is that which has just been stored.

$⊥-elim$ is a function that uses a contradiction, such as $k ≡ k'$ and $k ≢ k'$,
to inhabit any type.

%\snugshade
\rule{\textwidth}{0.1pt}%
\nopagebreak
\begin{code}
Lemma-ReadWrite : ∀ {rs} k {v} → update rs k v k ≡ v
Lemma-ReadWrite k with k ≟ k
... | yes  refl  = refl
... | no   k≢k'  = ⊥-elim (k≢k' refl)
\end{code}
\nopagebreak
\rule{\textwidth}{0.1pt}%
%\endsnugshade

Another lemma, @Lemma-Read<Write@, states that if the register being
accessed, @k'@, is less than the register most recently updated, @k@,
then the update may be bypassed.

%\snugshade
\rule{\textwidth}{0.1pt}%
\nopagebreak
\begin{code}
Lemma-Read<Write : ∀ {rs} k {v} j → j < k → update rs k v j ≡ rs j
Lemma-Read<Write  k  j   j<k  with k ≟ j
Lemma-Read<Write  k  .k  j<k  | yes  refl  = ⊥-elim ((1+n≰n) (j<k))
Lemma-Read<Write  k  j   j<k  | no   k≢j   = refl
\end{code}
\nopagebreak
\rule{\textwidth}{0.1pt}%
%\endsnugshade

The final lemma states that if a number @m@ exists in the set of integers
bounded by @n@, then the integer form of @m@ must be less than @n@.

%\snugshade
\rule{\textwidth}{0.1pt}%
\nopagebreak
\begin{code}
Fin⇒< : ∀{n} (m : Fin n) → toℕ m < n
Fin⇒< zero     = s≤s z≤n
Fin⇒< (suc m)  = s≤s (Fin⇒< m)
\end{code}
\nopagebreak
\rule{\textwidth}{0.1pt}%
%\endsnugshade

\paragraph{Theorem}

The correctness theorem states that;
\begin{enumerate}
  \item \label{forallvars}
  \emph{for all} numbers of source variables, @novs@, 
  source states @s@, next available registers @r + novs@,
  source expressions @e@, target instructions 
  @is@ and target states @(acc, rs)@, 
  \item \label{mapsts}
  \emph{if, for all} source variable reference @v@, the
  value in the equivalent register is the same that in the source
  state,
  \item \emph{then} there \emph{exists} a new register state
  @rs'@ such that;
  \begin{enumerate}
    \item \label{mapsts'}
    \emph{for all} source variable reference @v@, the
    value in the equivalent register is the same that in the
    source state,
    \item \label{nochg}
    \emph{for all} registers @q@ such that they are less
    than the next available register @r + novs@, the value in
    new target state is that same as the old one,
    \item \label{corr}
    \emph{and} expression @e@ is compiled into @is@
    at register offset @r + novs@ and executed in starting
    state @(acc , rs)@ \emph{is equivalent to} the execution
    of the additional instructions @is@ with the value of
    evaluating the expression in the accumulator.
  \end{enumerate}
\end{enumerate}

%\snugshade
\rule{\textwidth}{0.1pt}%
\nopagebreak
\begin{code}
Correctness  : ∀ novs s r (e : Expr novs) is acc rs               -- \emph{\autoref{forallvars}}
             → (∀ v → rs (toℕ v) ≡ lookup v s)                    -- \emph{\autoref{mapsts}}
             → ∃ λ rs'  →  (∀ v → rs' (toℕ v) ≡ lookup v s)       -- \emph{\autoref{mapsts'}}
                        ×  (∀ q → q < (r + novs) → rs' q ≡ rs q)  -- \emph{\autoref{nochg}}
                        ×  (exec (compile r e is) (acc , rs)      -- \emph{\autoref{corr}}
                           ≡ exec is (eval e s , rs'))
\end{code}
\nopagebreak
\rule{\textwidth}{0.1pt}%
%\endsnugshade

This is proved by structural induction over the expressions. The @Lit@
case is trivial as only the accumulator is updated and the executions
normalise to the same result.

%\snugshade
\rule{\textwidth}{0.1pt}%
\nopagebreak
\begin{code}
Correctness novs s r (Lit n) is acc rs Arss 
  = (rs , Arss , (λ _ _ → refl) , refl)
\end{code}
\nopagebreak
\rule{\textwidth}{0.1pt}%
%\endsnugshade

The @Var@ case only updates the accumulator but requires the use
of the initial assumption, \autoref{mapsts} above, and @Arss@ in the code. This
is introduced using the congruence principle of equality.

%\snugshade
\rule{\textwidth}{0.1pt}%
\nopagebreak
\begin{code}
Correctness novs s r (Var v) is acc rs Arss
  = (rs , Arss , (λ _ _ → refl) , cong (λ n → exec is (n , rs)) (Arss v))
\end{code}
\nopagebreak
\rule{\textwidth}{0.1pt}%
%\endsnugshade

Finally, the inductive case over addition.

\begin{description}
  \item[Inductive assumptions] \label{inductassump}
    The inductive assumptions are generated for the compilation of the @y@ expression into
    the tail of the instructions and the compilation of the @x@ expression with a higher
    available register and the updated (eval y s , @rsy@) state.
  \item[Register and laws] \label{reglaws}
    The result of the inductive assumption applied to @x@ gives the new register state
    required for @3@ and the required law for @3a@. The law required for @3b@ can be
    constructed using the transitivity principle of equality and the inductive assumptions
    of @x@ and @y@ connected with @Lemma-Read<Write@.
  \item[Correctness] \label{corrs}
    The 3c condition is now proved using a more verbose reasoning syntax, starting
    with the left-hand side of the 3c condition.
    \begin{enumerate}[I.]
      \item \label{corrsI} Applying an inductive assumption over $y$ and allowing the execution to
      continue through the @STOR@ instruction.
      \item \label{corrsII} Applying an inductive assumption over $x$ and allowing the execution to
      continue through the @ADD@ instruction.
      \item \label{corrsIII} The @rsx (r + novs)@ term is replaced by its equivalent through it being
      less than the next available register used when compiling @r@ and through the
      @Lemma-ReadWrite@.
    \end{enumerate}
\end{description}

%\snugshade
\rule{\textwidth}{0.1pt}%
\nopagebreak
\begin{code}
Correctness novs s r (x :+ y) is acc rs Arss

-- \emph{Note: \hyperref[inductassump]{Inductive assumptions}}
  with Correctness novs s r y
         (STOR (r + novs) ∷ compile (suc r) x (ADD (r + novs) ∷ is)) 
         acc rs Arss
... | (rsy , Irssy , Iltry , Icorrecty)
    with Correctness novs s (suc r) x (ADD (r + novs) ∷ is) 
           (eval y s) (update rsy (r + novs) (eval y s)) 
           (λ v → trans 
             (Lemma-Read<Write (r + novs) (toℕ v) (≤-steps r (Fin⇒< v))) 
             (Irssy v))
...   | (rsx , Irssx , Iltrx , Icorrectx)

-- \emph{Note: \hyperref[reglaws]{Register and laws}}
  = (rsx , Irssx 
  , (λ q sq≤r → trans 
       (Iltrx q (≤-step sq≤r)) 
       (trans 
         (Lemma-Read<Write (r + novs) q sq≤r) 
         (Iltry q sq≤r)))

-- \emph{Note: \hyperref[corrs]{Correctness}}
  , (begin 
      exec
        (compile r y
         (STOR (r + novs) ∷ compile (suc r) x (ADD (r + novs) ∷ is)))
        (acc , rs)

-- \emph{Note: \hyperref[corrsI]{Correctness I}}
    ≡⟨ Icorrecty ⟩
      exec
        (STOR (r + novs) ∷ compile (suc r) x (ADD (r + novs) ∷ is))
        (eval y s , rsy)

-- \emph{Note: \hyperref[corrsII]{Correctness II}}
    ≡⟨ Icorrectx ⟩
      exec is (eval x s ℤ+ rsx (r + novs) , rsx)

-- \emph{Note: \hyperref[corrsIII]{Correctness III}}
    ≡⟨ cong  (λ y → exec is (eval x s ℤ+ y , rsx)) 
             (trans (Iltrx (r + novs) ≤-refl) (Lemma-ReadWrite (r + novs))) ⟩
      exec is (eval x s ℤ+ eval y s , rsx) 
    ∎))

\end{code}
\nopagebreak
\rule{\textwidth}{0.1pt}%
%\endsnugshade

\paragraph{Documentation}
Like Coq, plenty of tutorial and course material exists for learning to 
use Agda. The documentation of the standard library is very extensive and the
language's concise style helps to make it very understandable.

\paragraph{Code extraction}
The Agda to Haskell code extractor always produces code which is very likely
to maintain the laws proved on it. However, it is almost unreadable by
humans due the mechanical, unoptimised process used to extract it. The code 
produced also hinders many of GHC's compiler optimisations.
\endgroup
