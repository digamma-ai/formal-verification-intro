(* Coq'a specification language Gallina consists of declarations. Declaration associates a name with a specification; both have to be valid expresions of Gallina. There are three kind of specifications: logical propositions (Prop, as A -> A), mathematical collections (Set, as Nat) and abstract types (Type, as Set and Prop, and Type!). Before we have talked about natural numbers and lists, that is, objects of type Set; today we will talk about Prop and see the Curry-Howard isomorphism you proved in action. *)

Section Propositions.   (* Sections are useful to structure the code, variables introduced here belong to the section and will be reset after the end of the section. Read about this here: https://coq.inria.fr/refman/Reference-Manual004.html#Section *)

  Check Prop. (* logical propositions *) 
  Check Set. (* collections *)
  Check Type. (* types *) 

(* Propositions are objects that can have proofs *) 
(* There are two special propositions False and True, defined as follows: *)

  Inductive False : Prop := . (* unprovable *)

  (* False is the proposition that has no proofs *)


  Inductive True : Prop := (* provable *)
  | I : True. 

  (* True is the proposition that has the single proof I. Practically, whenever you have goal True, you can just provide I as it's proof: *)

  Theorem True_is_true : True.
  Proof.
    apply I.
  Qed.

  (* It is not the same as boolean true and false though! Recall: *)

  Inductive bool : Set :=
  | true : bool
  | false : bool.

  (* Every boolean reduces to true or false, however, not every proposition is either provable or unprovable, you agree? To show that some proposition is provable you construct a proof, how do you show that it is unprovable? Prove A -> False: then the proof A would be a proof of False, but by definition False has no proofs. BHK interpretation in action!*)

  Theorem False_unprovable : False -> False.
  Proof.
    intros.
    apply H.
  Qed.

  Variables A B : Prop.

  Theorem Explosion : False -> A.
  Proof.
    intro H.
    case H. (* whenever you have a term of type False in the context, use case term. The tactic case for each constructor of the type provides a goal. False is defined as a type with no constructors, thus it finishes the goal instantly.*)
  Qed.

  Theorem Reductio : A -> ~ A -> B.
  Proof.
    intros.
    unfold not in H0.
    case ( H0 H ).
  Qed.

End Propositions. (* Now all the declared variables within the section are discarded *)

Section CHI_in_Action. 

  Variables p q r : Prop. (* "Let A, B and C be propositional variables..." *)

  Theorem  I' : p -> p.
  Proof. 
    intro x.
    apply x. (* With the tactic apply, we are giving the proof-term for the propostion to be proven. Here x is the proof of A. If in the context we have id : A and the goal is A we can use apply id. Moreover, such terms can be constructed from other terms in the context, as you will see below. *) 
  Qed.

  Print I'. (* I = fun x : p => x : p -> p  *)
  (* In our notation: \lambda x. x : p -> p *)


  (* K: \lambda xy. x *)
  Theorem K : p -> q -> p.
  Proof.
    intro x.
    intro y.
    apply x.
  Qed.

  Print K. (* K = fun (x : p) (_ : q) => x : p -> q -> p *)

  (* S: \lambda xyz. xz (yz) *) 

  Theorem S : ( p -> q -> r ) -> ( p -> q ) -> p -> r.
  Proof.
    intro x. (* assume p -> q -> r  *)
    intro y. (* assume p -> q *) 
    intro z. (* assume p *)
    (* Now from these assumptions we want to construct the proof of r *)
    apply ( x z ( y z ) ). (* Looks familiar? ;) Remember the rules of typing: "a term of type sigma -> tau can be applied to a term of type sigma etc..." *)
  Qed.

  Print S.


  Print False.
  Print True. 


  Theorem double_negation : p -> ~ ~ p. (* ~ is a notational variant of not *)
  Proof.
    intro x.
    unfold not.
    intro y.
    apply ( y x ).
  Qed.

  Print double_negation.

  Theorem gen_of_double_negation : p -> ( p -> q ) -> q.
  Proof.
    intro x.
    intro y.
    apply ( y x ).
  Qed.

  (* Do you know another name for the above theorem? *) 

  Print gen_of_double_negation.


  Theorem contraposition : ( p -> q ) -> ( ~ q -> ~ p ).
  Proof.
    intro x.
    unfold not.
    intro y.
    intro z.
    apply ( y ( x z ) ).
  Qed.

  Print contraposition.

End CHI_in_Action.

  


