Require Import Extraction.
Require Import ZArith Psatz.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => (S n') * fact n'
  end.

Fixpoint fact_acc (n : nat) (acc : nat) :=
    match n with
    | 0 => acc
    | S k => fact_acc k (n * acc)
    end.

  Definition fact' (n : nat) :=
    fact_acc n 1.

Inductive factorial : nat -> nat -> Prop :=
| FactZero : factorial 0 1
| FactSucc : forall n m, factorial n m -> factorial (S n) ((S n)*m). 

Theorem fact_correct : forall n, factorial n (fact n).
  Proof.
    induction n.
    - eapply FactZero.
    - simpl.
      eapply FactSucc.
      assumption.
  Qed.

Lemma fact_tr_acc_mult : forall (n m : nat),
  fact_acc n m = m * fact_acc n 1.
Proof.
  induction n as [ | k IH]; intro p.
  - simpl. nia.
  - replace (fact_acc (S k) p) with (fact_acc k ((S k) * p)).
    -- 
       rewrite IH. simpl. rewrite mult_1_r.
       rewrite IH with (m := S k).
       nia.
    -- simpl. trivial.
Qed.

Theorem fact'_correct : forall (n : nat), 
  factorial n (fact' n).
Proof.
  intros n. unfold fact'.
  induction n as [ | k IH].
  - simpl. econstructor.
  - simpl. rewrite mult_1_r.
    destruct k as [ | m].
    -- simpl. rewrite <- mult_1_r. 
       econstructor.
       econstructor.
    -- rewrite fact_tr_acc_mult.
       econstructor.
       assumption.
Qed.

Recursive Extraction fact.
Recursive Extraction fact'.

(* Definition of plus *)
Print Nat.add.

Theorem plus_2_3 : (S (S O)) + (S (S (S O))) = (S (S (S (S (S O))))).
Proof.
  simpl.
  reflexivity.
Qed.


Theorem plus_O_n : forall n, O + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

(* Resulting term *)
Print plus_O_n.
(* plus_O_n = fun n : nat => eq_refl
     : forall n : nat, 0 + n = n *)

Theorem plus_n_O : forall n, n + O = n.
Proof.
  induction n; simpl.
  (* base case *)
  - reflexivity.
  (* inductive step *)
  - rewrite IHn.
    reflexivity.
Qed.

(* A more complex proof: commutativity of addition *)
Theorem plus_commut : forall m n : nat, n + m = m + n.
Proof.
  induction m.
  - simpl.
    apply plus_n_O.
  - induction n.
    -- rewrite plus_n_O.
       rewrite plus_O_n.
       reflexivity.
    -- simpl.
       f_equal.
       rewrite IHn.
       pose proof (IHm (S n)).
       rewrite <- H.
       simpl.
       f_equal.
       symmetry.
       apply IHm.
Qed.

(* A simple example of "programming with dependent types"  *)

(* We declaratively define m minus n : z s.t. m = n + z. We prove that for each m and n such z exists  *)

Definition minus (m n : nat) {H:n <= m}: { z | m = n + z }.
Proof.
  revert m n H.
  induction m.
  - exists 0. omega. (* omega is the tactic that can solve simple arithmetic goals *)
  - intros.
    induction n.
    -- exists (S m). omega.
    -- destruct (IHm n) as [z Hz].
       omega.
       exists z.
       omega.
Defined.

(* By Curry-Howard we have a term corresponding to this proof *)
Print minus.

(* Which can be converted into OCaml program that perfors substraction *)
Extraction minus.
(*
(** val minus : nat -> nat -> nat **)

 let rec minus n y =
 match n with
 | O -> O
 | S n0 ->
 (match y with
 | O -> S n0
 | S y0 -> minus n0 y0)
 *)
       

      
    
