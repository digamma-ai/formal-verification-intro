(* 

Since propositional logic is decidable, whenever the goal is a propositional formula, one can call the decision procedure tauto. The proof term is constructed. *)

Variables p q r : Prop.

Theorem S : ( p -> q -> r ) -> ( p -> q ) -> p -> r.
  Proof.
    tauto.
  Qed.

Print S.

(* Consider a private club:

1. Every non-scottish member wears red socks
2. Every member wears a kilt or doesn’t wear red socks
3. The married members don’t go out on Sunday
4. A member goes out on Sunday if and only if they are Scottish
5. Every member who wears a kilt is Scottish and married
6. Every scottish member wears a kilt

Show that these rules are so strict that no one can be accepted. 

*)


Section club.

Variables scottish redsocks wearskilt married goesout : Prop. 

Hypothesis rule1 : ~ scottish -> redsocks.
Hypothesis rule2 : wearskilt \/ ~ redsocks.
Hypothesis rule3 : married -> ~ goesout.
Hypothesis rule4 : goesout <-> scottish.
Hypothesis rule5 : wearskilt -> scottish /\ married.
Hypothesis rule6 : scottish -> wearskilt.

Theorem nobody_is_accepted : False.
  Proof.
    tauto.
  Qed.
    
Print nobody_is_accepted.
