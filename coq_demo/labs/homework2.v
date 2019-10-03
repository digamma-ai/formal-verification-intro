    (* Homework for Lab#2 "Curry-Howard isomorphism in action" *)

Section Lab2.

     (* In class we were proving IPC(->) tautologies and looking at the corresponding simply typed lambda terms. This is the simplest version of Curry-Howard isomorphism. Now we want to extend it to more expressive logics. We add conjunction and disjunction to IPC(->), it means that now along with implication type (with abstraction corresonding to implication introduction and application to implication elimination), we also have conjunction and disjunction type. On the lambda-calculus side we will need to add term construction (corresponding to introduction and elimination rules. Take a moment to recall these rules for conjunction and disjunction. Can you come up with the rules on your own? Miquel will tell us about this in detail in two weeks. In this homework we will try to approach this from Coq. *)

    (* Recall the type Nat: *)

    Inductive Nat : Set :=
      | O : Nat
      | S : Nat -> Nat.

    (* This is the type that has two constructors O and S. That is, when (in the proof) you need to provide an object of type Nat, you can use one of the constructors to do so. On the other hand, if during your proof you need to state some property about natural numbers, you may want to "destruct" a natural number into a smaller one, to which you can apply the induction hypothesis. These is what Nat_rect, Nat_rec and Nat_ind are for. Each inductive type has constructors and destructors, corresponding to familiar introduction and elimination rules when we talk about connectives (does each connective have both introduction and elimination rule in natural deduction?) *)



    (* Task I : in the Coq Reference Manual read about the following tactics:
    intro
    apply 
    split
    elim
     *) 

    (* In what follows use only tactics: 
    intro
    apply 
    apply ... with 
    split
    elim
    unfold
    exact
    *)

    (* Define conjunction and disjunction inductive types.  What would be their constructors? Destructors? Think of natural deduction rules!*)

    (* Conjunction: *)


    Inductive K ( p q : Prop ) : Prop := 
      conj :

    (* Disjunction: *) 

    Inductive A ( p q : Prop ) : Prop :=
        | A_left : 

    (* Negation : *)

    Inductive N ( p : Prop ) : Prop :=

    (* Names are inspired by Polish notation in logic *) 

    (* Prove that your definitions coincide with the ones in Coq ( and, or, not correspondingly *) 

    (* Check what are the corresponding destructors *)

    Check A_ind


    (* Use this information to come up with tactics to prove the following: *)
    
    Variable p q r : Prop.

    Theorem and_definition : p -> q -> K p q.

    (* Prove the same theorem with and without using elim tactic: *)


    Theorem and_commutes_elim : K p q -> K q p.

    Theorem and_commutes_full : K p q -> K q p.

    Theorem or_definition : p -> A p q.


    Print or_definition.

    (* Prove the same theorem with and without using elim tactic: *)


    Theorem or_commutes_elim : A p q -> A q p.

    Theorem or_commutes_full : A p q -> A q p.

    (* /\ is equivalent to Coq's and, prove: *)  

    Theorem and_distribution : p -> q /\ r -> ( p -> q ) /\ ( p -> r ).

    (* In general, for propositional logic you don't have to come up with proofs, Coq can find them automatically: *)

    Theorem and_distribution_tauto : p -> q /\ r -> ( p -> q ) /\ ( p -> r ).
    Proof.
    tauto.
    Qed.

    (*  Look up tauto in the Reference manual! *)

    (* Can you prove this? And with tauto?*) 

    Theorem Peirce : ( ( p -> q ) -> p ) -> p.


    (* In classical propositional logic the connective NAND or Scheffer stroke | is functionally complete. That is, one can express any connective via |. Can you define NAND in Coq? See Wikipedia if you don't know what it is. *) 


    Inductive nand1 ( A B : Prop ) : Prop := 

    Print nand1_ind.  

    Variables A B : Prop.

    (* In classical logic all of the below hold for NAND. Can you prove all of them with your definition of nand1? *)

    Theorem nand_is_not_and : nand A B -> not ( A /\ B ).

    Theorem not_and_is_nand : not ( A /\ B ) -> nand A B.

    Theorem or_of_nots_is_nand_right : not A \/ not B ->  nand A B.

    Theorem or_of_nots_is_nand_left : nand A B -> not A \/ not B.

    Theorem neg_nand : nand A A <-> not A.
    
    Theorem and_nand_right : nand ( nand A A ) ( nand B B ) -> ( A \/ B ).
    
    Theorem and_nand_left : ( A \/ B ) -> nand ( nand A A ) ( nand B B ).

    (*  Is it possible to redefine NAND in a way that you could prove all of the above? Provide an alternative definition of NAND such that different theorems from the above list hold. *)

    Inductive nand2 ( A B : Prop ) : Prop :=

    (* By now you should be convinced that NAND can be defined in at least two ways (there are more!) in intuitionistic logic. These ways are equivalent in classical logic, but not in intuitionistic logic. Moreover, in both cases it's most interesting property is lost: nand is no longer functionally complete. FUN(ctionally complete) FACT: there is a ternary connective that plays this role:
     FUN p q r := ( ( p \/ q ) /\ not r ) \/ ( not p /\ ( q <-> r ) )
     *) 


    Inductive FUN ( p q r : Prop ) : Prop := 

    (* Prove : *)

    Theorem not_FUN : FUN p p p <-> not p.

    (* Express True and False using FUN: *)
    
    Theorem True_FUN :

    Theorem False_FUN : 

    (* Ask for a hint after one hour!  *) 

    (* Express conjunction using FUN: *)

    (* Pre-hint 1: solving this exercise would be proving that FUN is functionally complete in intuitionostic logic. It is not an easy task! So cooperate and ask for hints. *)

    Theorem useful_connective : FUN    <-> not p /\ r  

    Theorem and_FUN : FUN     <-> p /\ q. (* Pre-hint 2: in terms of which connectives can you define /\ in intuitionistic logic? *) 

