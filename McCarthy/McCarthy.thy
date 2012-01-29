theory McCarthy
imports HOL List
begin

types string = "char list"

(* Source arithmetic expressions *)
datatype exp = Lit nat
             | Var string
             | Plus exp exp

(* Source semantics *)
primrec E :: "exp => (string => nat) => nat" where
    "E(Lit n)      s = n"
  | "E(Var v)      s = s v"
  | "E(Plus e1 e2) s = E e1 s + E e2 s"
   
(* Target machine memory addresses *)
datatype cell = Acc
              | Reg nat

(* Target machine instructions *)
datatype inst = Li nat
              | Load nat
              | Sto nat
              | Add nat

(* Target memory storage operation *)
definition update :: "cell => nat => (cell => nat) => (cell => nat)" where
  "update x z s y = (if y = x then z else s y)"

(* Target instruction semantics *)
primrec S :: "inst => (cell => nat) => (cell => nat)" where
    "S (Li n)   s = update Acc n s"
  | "S (Load r) s = update Acc (s (Reg r)) s"
  | "S (Sto r)  s = update (Reg r) (s Acc) s"
  | "S (Add r)  s = update Acc (s (Reg r) + s Acc) s"

(* Target semantics for lists of instructions *)
primrec S' :: "inst list => (cell => nat) => (cell => nat)" where
    "S' []          s = s"
  | "S' (inst#rest) s = S' rest (S inst s)"

(* Source to Target compilation *)
primrec C :: "exp => (string => nat) => nat => inst list" where
    "C (Lit n)      m r = [Li n]"
  | "C (Var v)      m r = [Load (m v)]"
  | "C (Plus e1 e2) m r = C e1 m r
                        @ [Sto r]
                        @ C e2 m (r + 1)
                        @ [Add r]"

(* Lemma to handle appended instructions *)
lemma s'_append: "\<forall>p1 p2 s. S' (p1 @ p2) s = S' p2 (S' p1 s)"
apply (rule allI)
apply (induct_tac p1)
apply auto
done

(* Ignore an update to a different cell *)
lemma update_different: "\<forall>x y z s. ~(x = y) --> (update x z s y = s y)"
apply (auto simp add: update_def)
done

(* Retrieve an update to the same cell *)
lemma update_same: "\<forall>x z s. update x z s x = z"
apply (auto simp add: update_def)
done

(* Ignore updates below the register being retrieved *)
lemma update_below: "\<forall>q r z s. q < r \<longrightarrow> update (Reg r) z s (Reg q) = s (Reg q)"
apply (auto simp add: update_def)
done

(*
  Assumptions;
  * For all variables, the register it is mapped to is less than r.
  * For all variables, the value of the variable in source state "s" is
    equal to that of the mapped register in target state "s'".

  Theorem;
  * The evaluation of the compiled form of "e", in mapping "m", starting
    at register "r" is equal to that of the evaluation of "e".
  and
  * All registers below "r" are unchanged after the evaluation of "e".
*)
theorem Correctness:
  "\<forall>e m s s' r.
     (\<forall>v. m v < r) \<longrightarrow>
     (\<forall>v. s v = s' (Reg (m v))) \<longrightarrow>
         (S' (C e m r) s' Acc = E e s) \<and>
         (\<forall>x < r. (S' (C e m r) s' (Reg x) = s' (Reg x)))"
apply (rule allI)
apply (induct_tac e)
apply (simp_all add: update_def)
apply (simp add: update_same update_different update_below Nat.less_SucI s'_append)
done

export_code S' C in Haskell
  module_name MP file "/tmp"