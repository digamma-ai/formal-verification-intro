(* Recall the following structures: *)

Inductive Nat : Set :=
  | O : Nat
  | S : Nat -> Nat.

Inductive Bool : Set :=
  | true : Bool
  | false : Bool.

Fixpoint eqb (n m : Nat) : Bool :=
  match n with
  | O =>
    match m with
    | O => true
    | S l => false
    end
  | S k =>
    match m with
    | O => false
    | S l => eqb k l
    end
end.

Lemma eqb_decidable : forall (n m : Nat), {eqb n m = true} + {eqb n m = false}.
Proof.
  intros n.
  induction n.
    (* n = O *)
    intro m.
    case m.
      (* m = O *)
      left.
      simpl.
      reflexivity.
      (* S m *)
      intro n.
      right.
      simpl.
      reflexivity.
    (* S n *)
    intro m.
    case m.
      (* m = O *)
      right.
      simpl.
      reflexivity.
      (* S m *)
      simpl.
      exact IHn.
Qed.

Fixpoint leqb (n m : Nat) : Bool :=
  match n with
  | O => true
  | S k =>
    match m with
    | O => false
    | S l => leqb k l
    end
  end.

Lemma leqb_decidable : forall (n m : Nat), {leqb n m = true} + {leqb n m = false}.
Proof.
  intros n.
  induction n.
    (* n = O *)
    simpl.
    intro n.
    left.
    reflexivity.
    (* S n *)
    intro m.
    case m.
      (* m = O *)
      simpl.
      right.
      reflexivity.
      (* S m *)
      simpl.
      exact IHn.
Qed.

Lemma leqb_quasi_antisymm : forall (n m : Nat), leqb n m = false -> leqb m n = true.
Proof.
  intros n.
  induction n.
    (* n = O *)
    simpl.
    intro m.
    intro H.
    discriminate H.
    (* S n *)
    intro m.
    simpl.
    case m.
      (* m = O *)
      intro H.
      simpl.
      reflexivity.
      (* S m *)
      intro k.
      intro H.
      simpl.
      exact (IHn k H).
Qed.

Inductive List : Set :=
  | nil : List
  | cons : Nat -> List -> List.
Notation "n :: w" := (cons n w).

Check (O :: (S O) :: (S (S O)) :: nil).

(* We can define a type 'sorted' for lists which are sorted *)

Inductive sorted : List -> Prop :=
  | sorted_nil : sorted nil
  | sorted_singleton : forall n : Nat, sorted (n :: nil)
  | sorted_full :
    forall (n m : Nat) (w : List),
      (leqb n m = true) ->
      sorted (m :: w) ->
      sorted (n :: m :: w).

Lemma sortedO123 : sorted (O :: S O :: S (S O) :: S (S (S O)) :: nil).
Proof.
  apply (sorted_full O (S O)).
    simpl.
    reflexivity.
  apply (sorted_full (S O) (S (S O))).
    simpl.
    reflexivity.
  apply (sorted_full (S (S O)) (S (S (S O)))).
    simpl.
    reflexivity.
  apply (sorted_singleton (S (S (S O)))).
Qed.

Lemma sorted_sublists : forall (n : Nat) (w : List), sorted (n :: w) -> sorted w.
Proof.
  intros n w H.
  inversion H as [ | n' n_is_n' | n' m w'].
  (* inversion H looks at the type of H and, for each possible constructur c of that type, lists the conditions necessary for c to prove H.
  Since H : sorted (n :: w) we could use two of the constructors:
    either w = nil and (sorted_singleton n) proves (n :: w), or
    w = (m :: w'), H0 : (leq n m), H1 : (sorted m w'), and (sorted_full n m H0 H1) proves (n :: m :: w0)
   *)
    (* w = nil *)
    apply sorted_nil.
    (* w = m :: w0 *)
    exact H1.
Qed.

(* Number of occurences of a number in a list *)
Fixpoint numb_occ (n : Nat) (w : List) : Nat :=
  match w with
    | nil => O
    | m :: w' =>
      match (eqb m n) with
      | true => (S (numb_occ n w'))
      | false => (numb_occ n w')
      end
  end.

Compute numb_occ O (O :: S O :: O :: nil).
Compute numb_occ (S O) (O :: S O :: O :: nil).
Compute numb_occ (S (S O)) (O :: S O :: O :: nil).

(* Two lists are a permutation of each other *)
Definition perm (w w' : List) :=
  forall n : Nat, (numb_occ n w) = (numb_occ n w').

(* We can check that perm is an equivalence relation, ie, that it is
  reflexive
  symmetric
  transitive
*)

Lemma perm_reflexive : forall w : List, perm w w.
Proof.
  intro w.
  induction w.
    (* nil *)
    unfold perm.
    intro n.
    reflexivity.
    (* n :: w *)
    unfold perm.
    intro m.
    reflexivity.
Qed.

Lemma perm_symmetric : forall (w w' : List), perm w w' -> perm w' w.
Proof.
  intros w w' H.
  unfold perm.
  intro n.
  rewrite (H n).
  reflexivity.
Qed.

Lemma perm_transitive : forall (w w' w'' : List), perm w w' -> perm w' w'' -> perm w w''.
Proof.
  intros w w' w'' H1 H2.
  unfold perm.
  intro n.
  rewrite (H1 n).
  exact (H2 n).
Qed.

(* We can also see that, if two lists are permutations of each other, appending something to both won't change that *)
Theorem perm_cons : forall (n : Nat) (w w' : List), perm w w' -> perm (n :: w) (n :: w').
Proof.
  intros n w w' H.
  unfold perm.
  intro m.
  simpl.
  case (eqb n m).
    (* eqb n m = true *)
    rewrite (H m).
    reflexivity.
    (* eqb n m = false *)
    rewrite (H m).
    reflexivity.
Qed.

Theorem perm_switched_cons : forall (n m : Nat) (w w' : List), perm w w' -> perm (n :: m :: w) (m :: n :: w').
Proof.
  intros n m w w' H.
  unfold perm.
  intro k.
  simpl.
  case (eqb n k).
    (* eqb n k = true *)
    case (eqb m k).
      (* eqb m k = true *)
      rewrite (H k).
      reflexivity.
      (* eqb m k = false *)
      rewrite (H k).
      reflexivity.
    (* eqb n k = false *)
    case (eqb m k).
      (* eqb m k = true *)
      rewrite (H k).
      reflexivity.
      (* eqb m k = false *)
      rewrite (H k).
      reflexivity.
Qed.

(* This concludes the properties we will need of perm *)

(* Now we define a funcion to insert a number in a list at the biggest position such that every element before it is smaller *)
Fixpoint insert (n : Nat) (w : List) : List :=
  match w with
  | nil => n :: nil
  | m :: w' =>
    match (leqb n m) with
    | true => n :: m :: w'
    | false => m :: (insert n w')
    end
  end.

Compute insert O (S O :: nil).
Compute insert (S O) (O :: nil).
Compute insert (S (S O)) (S O :: O :: S (S (S O)) :: nil).

Lemma insert_perm : forall (n : Nat) (w : List), perm (n :: w) (insert n w).
Proof.
  intros n w.
  induction w as [ | k].
    (* nil *)
    simpl.
    exact (perm_reflexive (n :: nil)).
    (* k :: w *)
    simpl.
    case (leqb_decidable n k).
      (* leqb n k = true *)
      intro n_leq_k.
      rewrite n_leq_k.
      exact (perm_reflexive (n :: k :: w)).
      (* leqb n k = false *)
      intro n_nleq_k.
      rewrite n_nleq_k.
      cut (perm (n :: k :: w) (k :: n :: w)).
        (* use it *)
        intro H.
        apply (perm_transitive (n :: k :: w) (k :: n :: w) (k :: insert n w) H).
        apply (perm_cons k (n :: w) (insert n w)).
        exact IHw.
        (* prove it *)
        exact (perm_switched_cons n k w w (perm_reflexive w)).
Qed.

Theorem insert_sorted : forall (n : Nat) (w : List), sorted w -> sorted (insert n w).
Proof.
  intros n w H.
  elim H.
    (* w = nil *)
    simpl.
    exact (sorted_singleton n).
    (* w = n0 :: nil *)
    intro n0.
    simpl.
    case (leqb_decidable n n0).
      (* leqb n n0 = true *)
      intro n_leq_n0.
      rewrite n_leq_n0.
      exact (sorted_full n n0 nil n_leq_n0 (sorted_singleton n0)).
      (* leqb n n0 = false *)
      intro n_nleq_n0.
      rewrite n_nleq_n0.
      apply (sorted_full n0 n nil).
        exact (leqb_quasi_antisymm n n0 n_nleq_n0).
        exact (sorted_singleton n).
    (* w = n0 :: m :: w0 *)
    intros n0 m w0 n0_leq_m H1 H2.
    simpl.
    case (leqb_decidable n n0).
      (* leqb n n0 = true *)
      intro n_leq_n0.
      rewrite n_leq_n0.
      apply (sorted_full n n0 (m :: w0) n_leq_n0).
      apply (sorted_full n0 m w0 n0_leq_m).
      exact H1.
      (* leqb n n0 = false *)
      intro n_nleq_n0.
      rewrite n_nleq_n0.
      case (leqb_decidable n m).
        (* leqb n m = true *)
        intro n_leq_m.
        rewrite n_leq_m.
        apply (sorted_full n0 n (m :: w0)).
          exact (leqb_quasi_antisymm n n0 n_nleq_n0).
        exact (sorted_full n m w0 n_leq_m H1).
        (* leqb n m = false *)
        intro n_nleq_m.
        rewrite n_nleq_m.
        apply (sorted_full n0 m (insert n w0) n0_leq_m).
        simpl in H2.
        rewrite n_nleq_m in H2.
        exact H2.
Qed.

Definition sort (w : List) : {s : List | sorted s /\ perm w s}.
Proof.
  induction w.
    (* w = nil *)
    exists nil.
    split.
    exact sorted_nil.
    exact (perm_reflexive nil).
    (* n :: w *)
    destruct IHw as [s H].
    destruct H as [H1 H2].
    exists (insert n s).
    split.
      (* it is sorted *)
      exact (insert_sorted n s H1).
      (* it is a permutation *)
      apply (perm_transitive (n :: w) (n :: s) (insert n s)).
        exact (perm_cons n w s H2).
        exact (insert_perm n s).
Defined.

Extraction sort.
Extraction insert.
Extraction leqb.
