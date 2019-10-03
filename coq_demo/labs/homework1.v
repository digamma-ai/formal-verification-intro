(* Lab #1 ( Homework ) *)

(* After completing these exercices you will know how to define simple recursive functions on inductive types and do some basic proofs in Coq. 

Note: in all of the proofs below you just need 5 tactics: induction _, simpl, reflexivity, rewrite _ and apply _. If you are not sure what they are, please consult the Coq reference manual: https://coq.inria.fr/distrib/current/refman/. Use your search engine and ask us if you are lost! *)

(* There are 4 tasks, divided in two groups: *)

(* Tasks I-II. Please each of you do them alone. You just have to repeat what we did in class, nothing new appears there. If you have any question ask Nika or Ana. *)

(* Tasks III-IV. Here some variations on what we did in class appear. You can and should cooperate on these tasks. Use github! *) 


(*********************************** INTRO **************************************)
(* This is what we did in class: *)

Inductive (* Definition *) Nat : Set :=
  | O : Nat
  | S : Nat -> Nat.

Print Nat. (* Outputs the definition of Nat *)
Check Nat. (* Outputs the type of Nat *)
Check S ( S O ). 

Fixpoint plus ( n m : Nat ) : Nat := 
  match n with 
  | O => m 
  | S l => S ( plus l m )
  end.

Lemma hyper_trivial : plus O O = O. (* This is the statement of what we are going to prove. Below follows the proof, which consists of keywords called "tactics". *)
Proof.
simpl. (* this tactic applies the definition of plus, that is, reduces the term plus O O, according to the definition *) 
reflexivity. (* applies the definition of equality, x = x *) 
Qed.

(* Coq is a proof assistant: it helps you to create proofs and verifies if they are correct. It means that you have to come up with general proof strategy on your own. In simple cases, the proof in Coq and on paper would be pretty much the same. So, the above proof would go like this:

Lemma ( Hyper Trivial ) : 0 + 0 = 0.
Proof. By the first clause of definition of plus (+), we have that 0 + n = n for any n, thus, in particular 0 + 0 = 0. 
Qed. 

Note that on paper usually it is assumed that " = " obeys the rules of equality and people don't mention it explicitly. *)
 

(********************************** Task I **************************************)
(* write the proofs of the below theorems "on paper" (type them here), as in the example above. *) 

Theorem very_trivial : forall n : Nat, plus O n = n.
Proof.
simpl.
reflexivity.
Qed.


Theorem somewhat_trivial :  forall n : Nat, plus n O = n. 
Proof.
induction n. (* Proving by induction on n *) 
apply hyper_trivial.
simpl.
rewrite IHn. (* rewrites the goal using Induction hypothesis *)
reflexivity.
Qed.


(********************************** Task II *************************************)
(*  Below you will see some incomplete definitions and proofs, please fill in the gaps so that Coq accepts your completions.  *)

(* The  "Compute BLA" command can be helpful: it prints the result of applying simpl to BLA *) 

Compute plus ( S O ) ( S O ).  (* So here it outputs S ( S O ) *)

(* Define multiplication: *)

Fixpoint times ( n m : Nat ) : Nat := 
  match n with 


(* Write the proofs of the following theorems on paper and then complete the formal proofs here: *)

Proposition (* This is a synonym for Theorem *) times_OO : times O O = O.  
Proof.


Proposition times_nO : forall n : Nat, times O n = O.
Proof.



Proposition times_On : forall n : Nat, times n O = O.
Proof.

(* Define predecessor function *)


(* minus: *)


(* factorial: *)


(* Formulate and prove some statement using any functions above, they can be even super-hyper-trivial, don't worry. *) 

Proposition again_trivial : 

(********************************** Task III ************************************)
(* Define Booleans. *)

Inductive Bool := true | false. (* we just have two simple constructors, remember lambda-calculus! *)

(* Now define conjunction, disjunction, implication and negation *)

Definition AndB ( b1 b2 : Bool ) :=
  match b1, b2 with 

(* Now we can create function from Nat to Bool, define less than or equal. Hint: one can nest match ... with expressions. *)

Fixpoint lq ( n m : Nat ) : Bool := 
  match n with
      
     => match m with



Proposition l : forall n, lq O n = true.
Proof.

Proposition ln : forall n, lq n ( S n ) = true.
Proof.


(********************************** Task IV ************************************)
(* Define functions on lists of natural numbers *) 

Inductive Nat_List : Set :=
  | nil_N : Nat_List
  | cons_N : Nat -> Nat_List ->  Nat_List.

(* For instance, an alternative Cons that appends one element at the end: *) 

Fixpoint back_cons_N  ( L : Nat_List ) ( a : Nat) : Nat_List := 
  match L with
    | nil_N => cons_N a nil_N 
    | cons_N Head Tail => cons_N Head ( back_cons_N Tail a )
  end.

(* Reverse a list using back_cons_N *)

Fixpoint reverse ( L : Nat_List ) : Nat_List :=

(* Append two lists together *)

Fixpoint append ( L1 L2 : Nat_List ) : Nat_List :=

(* Define reverse with append *)

Fixpoint reverse2

(* Filter a list such that it contains only numbers smaller or equal to n. Hint: match ... with can be nested. *)

Fixpoint filter ( L : Nat_List ) ( n : Nat )

(* Define a length function for lists: *)


(* Now state and prove a propostion that the length ( append L1 L2 ) is length L1 + length L2. Remember to first write your proof down in English: *)

 






