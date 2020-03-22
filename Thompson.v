(**
Thompson construction for RE.
=============================


Here is my first attempt to formalize a construction of
the Thompson NFA construction for regular expressions.
My idea is to build a simple interface for assembling
NFAs from smaller components: as you will see, it is
almost another way to write regular expressions.
 *)


Require Import
        Ascii
        String
        Arith_base
        List
        ListSet
        Tactics.Tactics
        Utils.StringUtils.

Import ListNotations.

(**

First of all, a state is just a natural number and
a set of states is just a (list-based) set of state.
 *)

Definition state := nat.

Definition states := set state.

(** Here I provide some auxiliar names for the
    functions on list set library. Note that
    basically I just specify that we should use
    the decidable equality function for nat. *)

Definition union := set_union eq_nat_dec.
Definition empty := @empty_set nat.
Definition inter := set_inter eq_nat_dec.
Definition is_empty (s : states) :=
  match s with
  | [] => true
  | _  => false
  end.
Definition singleton (s : state) : states :=
  s :: empty.

Definition unions := fold_right (fun x ac => union x ac) empty.

Lemma is_empty_correct : forall s, is_empty s = true <-> s = empty.
Proof.
  induction s ; crush.
  inverts* H1.
Qed.

(**
   We represent NFA by a record formed by its set of starting states,
   its transition function, the set of final states and a natural number
   constant that is used to express the NFA number of states.
 *)

Record nfa : Type
  := NFA {
         size  : nat ;
         start : states ;
         transition : ascii -> state -> states ;
         final : states 
       }.

(** Matching an input string is just a matter of recursivelly tranverse it
    applying NFA transitions. Note that, at each step, we modify the _start_
    of the NFA to denote the current _activated_ states in the NFA.
    A string is only accepted if the intersection between the current active set and
    the final states is not empty.
 *)

Fixpoint run (n : nfa)(ss : states)(xs : string) : bool :=
  match xs with
  | EmptyString  => negb (is_empty (inter ss (final n)))
  | String x xs' => let as' := unions (map (transition n x) ss)
                   in run n as' xs'
  end.

Definition matches (n : nfa)(xs : string) : bool := run n (start n) xs.

(** A basic result which will be useful latter: if we have an nfa which has
    an empty starting state set, then it accepts no string *)

Remark run_empty
  : forall s n, run n empty s = false.
Proof.
  induction s ; crush.
Qed.

Lemma matches_start_empty :
  forall (m : nfa), start m = empty -> forall s, matches m s = false.
Proof.
  intros m Hm.
  unfold matches.
  rewrite Hm.
  intros s.
  apply run_empty.
Qed.

(** sat buils an nfa for a predicate over characters *)

Definition sat (p : ascii -> bool) : nfa :=
  let f x y :=
      match y with
      | 0 => if p x then singleton 1 else empty
      | _ => empty
      end
  in NFA 2 (singleton 0) f (singleton 1).

(** simple NFA which accepts the empty set of strings
    and its correctness proof.*)

Definition zero : nfa :=
  NFA 0 empty (fun _ _ => empty) empty.

Lemma matches_zero_correct : forall s, matches zero s = false.
Proof.
  induction s ; cbn in * ; auto.
Qed.

(** NFA for accepting the empty string and is correctness proof.*)

Definition one : nfa :=
  NFA 1 (singleton 0) (fun _ _ => empty) (singleton 0).

Lemma matches_one_correct : forall s, matches one s = true <-> s = EmptyString.
Proof.
  unfold matches ; induction s ; split ; intros H ; try congruence ; auto.
  -
    simpl in *.
    destruct s.
    rewrite run_empty in H ; crush.
    simpl in *.
    rewrite run_empty in H ; crush.
Qed.

(** single character NFA and its correctness proof *)

Definition chr (c : ascii) : nfa :=
  sat (fun c' => if ascii_dec c c' then true else false).

Ltac ascii_matcher :=
  match goal with
  | [H : context[ascii_dec ?X ?Y] |- _] =>
    destruct (ascii_dec X Y)
  end.

Lemma matches_chr_correct
  : forall s c, matches (chr c) s = true <-> s = String c EmptyString.
Proof.
  unfold matches ; induction s ; crush ; try ascii_matcher ; crush.
  -
    lets J : IHs a ; clear IHs.
    destruct s.
    +
      simpl in * ; auto.
    +
      fequals.
      simpl in *.
      rewrite run_empty in H ; crush.
  -
    rewrite run_empty in H ; crush.
  -
    destruct (ascii_dec c c) ; crush.
Qed.

(**
The shift function is used to ensure the disjointness of the state-sets
of two NFA. The idea is to _shift_ the states of the second nfa by the
size of the first.
 *)

Definition shift (n : nat)(s : states) :=
  map (fun x => x + n) s.

Lemma shift_In
  : forall s x, In x s -> forall n, In (x + n) (shift n s).
Proof.
  induction s ; crush.
Qed.

Lemma shift_disjoint
  : forall n, n > 0 -> forall s x, In x (shift n s) -> In (x - n) s.
Proof.
  intros n Hn. induction s ; intros x Hin ; crush.
Qed.

Lemma shift_id
  : forall s, shift 0 s = s.
Proof.
  induction s ; crush ; fequals*.
Qed.

(** simple boolean test for less-than relation on naturals. *)

Definition ltb (n m : nat) : bool := leb (S n) m.

(** Function for constructing the union of two nfa's.
    For now, I have no clue to prove the correctness... :P
 *)

Definition sum (m m' : nfa) : nfa :=
  match m , m' with
  | NFA nm asm tm fm , NFA nm' asm' tm' fm' =>
    NFA (nm + nm')
        (union asm (shift nm asm'))
        (fun i s =>
           match ltb s nm with
           | true => tm i s 
           | false => shift nm (tm' i (s - nm))
           end)
        (union fm (shift nm fm'))
  end.

Lemma sum_left_sound
  : forall s m m', matches m s = true -> matches (sum m m') s = true.
Proof.
  unfold matches ; induction s ; intros m m' H.
  -
    destruct m ; destruct m' ; crush.
    destruct (is_empty
                (inter (union start0 (shift size0 start1))
                       (union final0 (shift size0 final1)))) eqn : Hemp.
Admitted.

Lemma sum_right_sound
  : forall s m' m, matches m' s = true -> matches (sum m m') s = true.
Admitted.


Lemma sum_complete
  : forall s m m', matches (sum m m') s = true -> matches m s = true \/ matches m' s = true.
Proof.
Admitted.


(** Construction for the concatenation of two nfa's. Need to figure out how
    to do the correctness proofs. *)


Definition prod (m m' : nfa) : nfa :=
  match m , m' with
  | NFA nm asm tm fm , NFA nm' asm' tm' fm' =>
    NFA (nm + nm')
        (if is_empty (inter asm fm)
         then asm
         else union asm (shift nm asm'))
        (fun i s =>
           match ltb s nm with
           | true => if (is_empty (inter (tm i s) fm))
                    then tm i s
                    else union (tm i s) (shift nm asm')
           | false => shift nm (tm' i (s - nm))
           end)
        (shift nm fm')
  end.


Lemma prod_sound
  : forall s s' m m', matches m s   = true ->
                 matches m' s' = true ->
                 matches (prod m m') (s ++ s') = true.
Proof.
Admitted.

Lemma prod_complete
  : forall s m m', matches (prod m m') s = true ->
              exists s1 s2, s = (s1 ++ s2) /\ matches m s1 = true /\
                                       matches m' s2 = true.
Proof.
Admitted.

(** star construction for nfa's. No correctness proofs. *)

Definition star (m : nfa) : nfa :=
  match m with
  | NFA nm asm tm fm => NFA nm
                           asm
                           (fun i s => if is_empty (inter (tm i s) fm)
                                    then tm i s
                                    else union (tm i s) asm)
                           asm
  end.

Lemma star_nil_sound
  : forall m, matches (star m) EmptyString = true.
Proof.
Admitted.

Lemma star_cat_sound
  : forall s s' m, matches m s = true ->
              matches (star m) s' = true ->
              matches (star m) (s ++ s') = true.
Proof.
Admitted.

(**
   Boring regular expression stuff: syntax and semantics.
 *)

Inductive regex : Set :=
| Empty : regex
| Epsilon : regex
| Chr : ascii -> regex
| Cat : regex -> regex -> regex
| Choice : regex -> regex -> regex
| Star : regex -> regex.

Inductive in_regex : string -> regex -> Prop :=
| InEpsilon
  : in_regex "" Epsilon
| InChr
  : forall c, in_regex (String c "") (Chr c)
| InCat
  : forall s s' e e', in_regex s e ->
                 in_regex s' e' ->
                 in_regex (s ++ s') (Cat e e')
| InLeft
  : forall s e e', in_regex s e ->
              in_regex s (Choice e e')
| InRight
  : forall s e e', in_regex s e' ->
              in_regex s (Choice e e')
| InStarNil
  : forall e, in_regex EmptyString (Star e)
| InStarCons
  : forall s s' e, in_regex s e ->
              in_regex s' (Star e) ->
              in_regex (s ++ s') (Star e).

Hint Constructors in_regex : core.

(** Simple computation to translate a RE into a
    NFA using thompson construction *)


Fixpoint thompson (e : regex) : nfa :=
  match e with
  | Empty => zero
  | Epsilon => one
  | Chr c => chr c
  | Cat e e' => prod (thompson e) (thompson e')
  | Choice e e' => sum (thompson e) (thompson e')
  | Star e => star (thompson e)
  end.

(** Correctness of the construction. Here I'm assuming that
    the proofs will by strong induction on string size. *)

Definition thompson_sound_type :=
  fun e s => matches (thompson e)s = true -> in_regex s e.

Lemma thompson_sound_F
  : forall e s, (forall s', string_lt s' s -> thompson_sound_type e s') ->
           thompson_sound_type e s.
Proof.
Admitted.

Lemma thompson_sound
  : forall e s, matches (thompson e) s = true -> in_regex s e.
Proof.
  intros e s.
  eapply (well_founded_induction
            wf_string_lt
            (thompson_sound_type e)).
  apply thompson_sound_F.
Qed.

Definition thompson_complete_type :=
  fun e s => in_regex s e -> matches (thompson e) s = true.

Lemma thompson_complete_F
  : forall e s, (forall s', string_lt s' s -> thompson_complete_type e s') ->
           thompson_complete_type e s.
Proof.
Admitted.

Lemma thompson_complete
  : forall e s, in_regex s e -> matches (thompson e) s = true.
Proof.
  intros e s.
  eapply (well_founded_induction
            wf_string_lt
            (thompson_complete_type e)).
  apply thompson_complete_F.
Qed.

Theorem thompson_correct
  : forall e s, in_regex s e <-> matches (thompson e) s = true.
Proof.
  intros e s ; split.
  -
    apply thompson_complete.
  -
    apply thompson_sound.
Qed.
