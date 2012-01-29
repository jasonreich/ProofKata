Require Import List Streams.

Inductive expr : Set :=
  | Val : nat -> expr
  | Add : expr -> expr -> expr.

Fixpoint eval (x : expr) : nat := 
  match x with
  | Val n => n
  | Add y0 y1 => eval y0 + eval y1 
  end.

Inductive instr : Set :=
 | Push : nat -> instr
 | Sum : instr.

Definition instrs : Set := list instr.
Definition stack : Set := Stream nat.

Definition step (i : instr) (s : stack) : stack :=
 match i with
 | Push n => Cons n s
 | Sum => Cons (hd (tl s) + hd s) (tl (tl s))
 end.
Fixpoint exec (is : instrs) (s : stack) : stack :=
 match is with
 | nil => s
 | i' :: is' => exec is' (step i' s)
 end.

Fixpoint compile (x : expr) (is : instrs) : instrs :=
 match x with
 | Val n => Push n :: is
 | Add y0 y1 => compile y0 (compile y1 (Sum :: is))
 end.

Theorem correct : forall x is s, exec (compile x is) s = exec is (Cons (eval x) s).
intro. induction x. auto. intros. simpl. rewrite IHx1. rewrite IHx2. auto.
Qed.


Extraction Language Haskell.
Recursive Extraction eval exec.