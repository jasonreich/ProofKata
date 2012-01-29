Require Import Arith Bool BoolEq List Omega.

(* Source Language *)
Inductive expr : Set :=
  | Con : nat -> expr
  | Var : nat -> expr
  | Add : expr -> expr -> expr.

Fixpoint eval e s := match e with
  | Con n   => n
  | Var v   => s v
  | Add x y => eval x s + eval y s
end.

(* Target Language *)
Inductive inst : Set :=
  | Li    : nat -> inst
  | Load  : nat -> inst
  | Store : nat -> inst
  | Sum   : nat -> inst.

Definition update (rs : nat -> nat) (k v k' : nat) := match beq_nat k' k with
  | true  => v
  | false => rs k'
end.

Fixpoint step (i : inst) (s' : nat * (nat -> nat)) := match i with
  | Li    n => (n, snd s')
  | Load  r => (snd s' r, snd s')
  | Store r => (fst s', update (snd s') r (fst s'))
  | Sum   r => (fst s' + snd s' r, snd s')
end.

Fixpoint exec is s' := match is with
  | nil     => s'
  | i :: is => exec is (step i s')
end.

(* Compiler *)
Fixpoint compile (m : nat -> nat) (r : nat) (e : expr) (is : list inst) := match e with
  | Con n   => Li n :: is
  | Var v   => Load (m v) :: is
  | Add x y => compile m r y (Store r :: compile m (S r) x (Sum r :: is))
end.

(* Lemmas *)
Lemma update_same :
  forall rs key value,
    update rs key value key = value.
intros. unfold update. rewrite <- beq_nat_refl. auto.
Qed.

Lemma lt_is_ne : 
  forall q r : nat, q < r -> q <> r.
intros. assert ({q = r} + {q <> r}).
apply eq_nat_dec. destruct H0. omega. auto.
Qed.

Lemma n_nlt_n :
  forall n, (n < n) -> False.
intros. omega.
Qed.

Lemma update_less :
  forall rs hi value lo,
    lo < hi -> update rs hi value lo = rs lo.
intros. unfold update. case_eq (beq_nat lo hi).
intros. assert (lo = hi). apply beq_nat_eq. auto. rewrite H1 in H. apply n_nlt_n in H. elim H.
auto.
Qed.

(* Correctness *)
Theorem correctness :
  forall m s e r is acc rs,
    (forall v, m v < r) -> (forall v, rs (m v) = s v) ->
    exists rs', (forall v, rs' (m v) = s v)
               /\ (forall q, q < r -> rs' q = rs q)
               /\ exec (compile m r e is) (acc, rs) = exec is (eval e s, rs').
intros until s. induction e.
intros. exists rs.  repeat (split; auto).
intros r is acc rs Hltr Heqs. exists rs.  repeat (split; auto). simpl. rewrite Heqs. auto.
intros r is acc rs Hltr Heqs.
destruct IHe2 with (r := r) (acc := acc) (rs := rs) (is := (Store r :: compile m (S r) e1 (Sum r :: is))).
auto. auto. destruct H as [Hyltr H].  destruct H as [Hyeqs Hycor].
destruct IHe1 with (r := S r) (acc := eval e2 s) (rs := (update x r (eval e2 s))) (is := (Sum r :: is)).
intros. apply lt_S. auto.
intros. rewrite update_less. auto. auto. destruct H as [Hxltr H]. destruct H as [Hxeqs Hxcor].
exists x0. split. auto. split. intros. rewrite Hxeqs. auto. rewrite update_less. rewrite Hyeqs.
auto. auto. auto. auto.
simpl. rewrite Hycor. simpl. rewrite Hxcor. simpl. rewrite Hxeqs. rewrite update_same. auto. auto.
Qed.

Extraction Language Haskell.
Recursive Extraction compile eval exec.