(* First lab on using Coq *) 

(* Coq is a proof-assistant and a functional programming language. We 'programmed' on paper with untyped and typed lambda calculus. We can write the same programs in Coq. We will deal with natural numbers and lists. *) 

(* Inductive definitions and recursive functions *)

(* Remember natural numbers which are created using two constructors, zero and successor. *) 
Inductive Nat : Set := (* We are defining the set of natural numbers: smallest set created using these two constructors: *)
  | O : Nat 
  | S : Nat -> Nat. 

(* Note : Set declaration. There are also : Type and : Prop declarations - we will talk about those later *)

(* Similarly we define lists: *) 
Inductive Nat_List : Set := 
  | nil_N : Nat_List
  | cons_N : Nat -> Nat_List -> Nat_List.

(* Note that here we are not giving a particular lambda-term corresponding to nil and cons *) 

Inductive Bool : Set := 
  | true : Bool
  | false : Bool.

Inductive Bool_List : Set := 
  | nil_B : Bool_List
  | cons_B : Bool -> Bool_List -> Bool_List.



Fixpoint plus ( n m : Nat ) : Nat := 
  match n with
    | O => m
    | S p => S ( plus p m )
  end.


Eval simpl in plus ( S O ) ( S O ).

Fixpoint times ( n m : Nat ) : Nat := 
  match n with 
    | O => O
    | S p => plus ( times p m ) m
  end.

Eval simpl in times ( S ( S O ) ) ( S ( S O ) ).

Fixpoint fact ( n : Nat ) : Nat := 
  match n with
    | O => S O
    | S p => times p ( fact p )
  end.

(* Lists *) 

Fixpoint back_cons_N  ( L : Nat_List ) ( a : Nat) : Nat_List := 
  match L with
    | nil_N => cons_N a nil_N 
    | cons_N Head Tail => cons_N Head ( back_cons_N Tail a )
  end.

Eval simpl in back_cons_N ( cons_N O ( cons_N O nil_N) ) ( S O ).

Fixpoint reverse ( L : Nat_List ) : Nat_List :=
  match L with
    | nil_N => nil_N
    | cons_N Head Tail => back_cons_N ( reverse Tail ) Head
  end.

Eval simpl in reverse (
                  cons_N O (
                          cons_N ( S O ) (
                                   cons_N  ( S ( S O ) ) nil_N  )  ) ).

Fixpoint append ( L1 L2 : Nat_List ) : Nat_List :=
  match L1 with 
    | nil_N => L2
    | cons_N Head Tail => cons_N Head ( append Tail L2 )
  end.

Fixpoint reverse2( L : Nat_List ) : Nat_List := 
  match L with
    | nil_N => nil_N
    | cons_N Head Tail => append ( reverse Tail ) ( cons_N Head nil_N )
  end.

Definition pred ( n   : Nat ) : Nat  := 
  match n with
    | O => O
    | S p => p
  end.

Fixpoint monus ( n m : Nat ) : Nat := 
  match m with
    | O => n
    | S p => monus ( pred n ) p
  end.

Eval simpl in monus ( S ( S ( S O ) ) )  O.

Fixpoint leq ( n m : Nat ) : Bool := 
  match ( monus n m ) with
    | O => true
    | _ => false
  end.

Eval simpl in leq ( S O ) O.

Fixpoint filter ( L : Nat_List ) ( n : Nat ) := 
  match L with 
   | nil_N => nil_N
   | cons_N Hd Tl => 
     match ( leq Hd n ) with
      | true => cons_N Hd ( filter Tl n )
      | false => filter Tl n
      end
  end.


Eval simpl in filter ( cons_N  ( S ( S O ) ) ( cons_N ( S ( S O ) ) ( cons_N O nil_N ) ) ) ( S O ).

Fixpoint map ( f : Nat -> Nat ) ( L : Nat_List ) := 
  match L with
    | nil_N => nil_N
    | cons_N Hd Tl => cons_N ( f Hd ) ( map f Tl )
  end. 

Fixpoint foldl ( f : Nat -> Nat -> Nat ) ( L : Nat_List ) : Nat := 
  match L with
    | nil_N => O (* default on empty *)
    | cons_N Hd nil_N => Hd
    | cons_N Hd Tl  => f Hd ( foldl f Tl )
  end.

Eval simpl in foldl plus ( cons_N  ( S ( S O ) ) (
                                     cons_N ( S ( S O ) ) (
                                              cons_N O nil_N ) ) ).

Eval simpl in foldl times ( cons_N ( S ( S ( S O ) ) ) (
                                     cons_N ( S ( S O ) ) (
                                              cons_N ( S O ) nil_N ) ) ).
