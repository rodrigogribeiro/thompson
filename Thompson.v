Require Import
        Ascii
        String
        Arith_base
        List
        ListSet
        Tactics.Tactics
        Utils.StringUtils.

Import ListNotations.

(** definition of nat based set *)

Definition state := nat.

Definition states := set state.

(** definition of a simple NFA *)

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

Record nfa : Type
  := NFA {
         size  : nat ;
         start : states ;
         transition : ascii -> state -> states ;
         final : states 
     }.

Fixpoint matches (n : nfa)(xs : string) : bool :=
  match xs with
  | EmptyString  => negb (is_empty (inter (start n) (final n)))
  | String x xs' => let as' := unions (map (transition n x) (start n))
                in matches (NFA (size n) as' (transition n) (final n)) xs'
  end. 


Lemma matches_start_empty :
  forall (m : nfa), start m = empty -> forall s, matches m s = false.
Proof.
  intros m Hm.
  induction s.
  -
    simpl in * ; crush.
  -
    destruct m.
    simpl in *.
    substs.
    simpl.
    auto.
Qed.

Definition sat (p : ascii -> bool) : nfa :=
  let f x y :=
      match y with
      | 0 => if p x then singleton 1 else empty
      | _ => empty
      end
  in NFA 2 (singleton 0) f (singleton 1).

Definition zero : nfa :=
  NFA 0 empty (fun _ _ => empty) empty.

Lemma matches_zero_correct : forall s, matches zero s = false.
Proof.
  induction s ; cbn in * ; auto.
Qed.

Definition one : nfa :=
  NFA 1 (singleton 0) (fun _ _ => empty) (singleton 0).

Lemma matches_one_correct : forall s, matches one s = true <-> s = EmptyString.
Proof.
  induction s ; split ; intros H ; try congruence ; auto.
  -
    simpl in *.
    destruct s.
    +
      simpl in *.
      congruence.
    +
      simpl in *.
      rewrite H in IHs.
      clear H.
      destruct IHs.
      specialize (H (eq_refl true)).
      congruence.
Qed.

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
  induction s ; crush ; try ascii_matcher ; crush.
  -
    lets J : IHs a ; clear IHs.
    destruct s.
    +
      simpl in * ; auto.
    +
      fequals.
      simpl in *.
      assert (matches
        {|
        size := 2;
        start := empty;
        transition := fun (x : ascii) (y : nat) =>
                      match y with
                      | 0 =>
                          if if ascii_dec a x then true else false
                          then singleton 1
                          else empty
                      | S _ => empty
                      end;
        final := singleton 1 |} s = false).
      apply matches_start_empty ; auto. crush.
  -
      assert (matches
        {|
        size := 2;
        start := empty;
        transition := fun (x : ascii) (y : nat) =>
                      match y with
                      | 0 =>
                          if if ascii_dec c x then true else false
                          then singleton 1
                          else empty
                      | S _ => empty
                      end;
        final := singleton 1 |} s = false).
      apply matches_start_empty ; auto. crush.
  -
    destruct (ascii_dec c c) ; crush.
Qed.

Definition shift (n : nat)(s : states) :=
  map (fun x => x + n) s. 

Definition ltb (n m : nat) : bool := leb (S n) m.

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
Admitted.

Lemma sum_right_sound
  : forall s m' m, matches m' s = true -> matches (sum m m') s = true.
Admitted.


Lemma sum_complete
  : forall s m m', matches (sum m m') s = true -> matches m s = true \/ matches m' s = true.
Proof.
Admitted.


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

(** regular expression syntax *)

Inductive regex : Set :=
| Empty : regex
| Epsilon : regex
| Chr : ascii -> regex
| Cat : regex -> regex -> regex
| Choice : regex -> regex -> regex
| Star : regex -> regex.

(** semantics *)

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

Fixpoint thompson (e : regex) : nfa :=
  match e with
  | Empty => zero
  | Epsilon => one
  | Chr c => chr c
  | Cat e e' => prod (thompson e) (thompson e')
  | Choice e e' => sum (thompson e) (thompson e')
  | Star e => star (thompson e)
  end.

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
