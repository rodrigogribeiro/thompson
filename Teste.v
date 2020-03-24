From Coq Require Import
                 Ascii
                 String 
                 MSets
                 Arith.

Module NSet := Make Nat_as_OT.
Module NSetDec := MSetDecide.WDecide NSet.

Parameter calc : NSet.t -> string -> bool.

Instance calc_proper 
      : Proper (NSet.Equal ==> @eq string ==> @eq bool) calc.
Proof.  
  intros S S' H s s' H1.
  rewrite H1.
  rewrite H. (** error here! *)
