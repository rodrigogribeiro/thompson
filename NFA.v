From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section RE.
  Variable sigma : finType.
  Definition word := seq sigma.

  Inductive regex : Type :=
  | Empty : regex
  | Epsilon : regex
  | Chr : sigma -> regex
  | Cat : regex -> regex -> regex
  | Choice : regex -> regex -> regex
  | Star : regex -> regex.

  Notation "#0"    := (Empty).
  Notation "#1"    := (Epsilon).
  Notation "'#' c" := (Chr c)(at level 40, no associativity).
  Notation "e1 '@' e2" := (Cat e1 e2)(at level 50, left associativity).
  Notation "e1 ':+:' e2" := (Choice e1 e2)(at level 60, right associativity).

  (** languages are just a predicate on words *)

  Definition lang := pred word.

  Implicit Types (x y z : sigma) (w : word) (L : lang).

  Definition empty : lang := pred0.

  Definition eps : lang := pred1 [::].
  
  Definition chr x : lang := pred1 [:: x].
  
  Definition compl L : lang := predC L.

  Definition union L1 L2 : lang
    := [pred w | (w \in L1) || (w \in L2)].
  
  Definition residual x L : lang
    := [pred w | x :: w \in L].

  Definition cat (L1 L2: lang) : lang :=
    fun v => [exists i : 'I_(size v).+1, L1 (take i v) && L2 (drop i v)].

  Definition star L : lang :=
    fix star v :=
      if v is x :: v'
      then cat (residual x L) star v'
      else true.

  (** reflecting properties *)

  Lemma unionP r s w :
    reflect (w \in r \/ w \in s) (w \in union r s).
  Proof.
    rewrite !inE.
    exact: orP.
  Qed.

  Lemma catP {L1 L2 : lang} {w : word} :
    reflect (exists w1 w2, w = w1 ++ w2 /\ w1 \in L1 /\ w2 \in L2) (w \in cat L1 L2).
  Proof.
    apply: (iffP existsP) => [[n] /andP [H1 H2] | [w1] [w2] [e [H1 H2]]].
    - exists (take n w). exists (drop n w). by rewrite cat_take_drop -topredE.
    - have lt_w1: size w1 < (size w).+1 by rewrite e size_cat ltnS leq_addr.
      exists (Ordinal lt_w1); subst.
      rewrite take_size_cat // drop_size_cat //. exact/andP.
  Qed.

  Lemma cat_app w1 w2 L1 L2 : w1 \in L1 -> w2 \in L2 -> w1 ++ w2 \in cat L1 L2.
  Proof.
    move => H1 H2.
    apply/catP.
    exists w1. by exists w2.
  Qed.

  Lemma cat_eq (l1: lang) l2 l3 l4:
    l1 =i l2 -> l3 =i l4 -> cat l1 l3 =i cat l2 l4.
  Proof.
    move => H1 H2 w.
    apply: eq_existsb => n.
    by rewrite (_ : l1 =1 l2) // (_ : l3 =1 l4).
  Qed.

  Lemma starP : forall {L v},
      reflect (exists2 vv, all [predD L & eps] vv & v = flatten vv) (v \in star L).
  Proof.
    move=> L v ;
    elim: {v}_.+1 {-2}v (ltnSn (size v)) => // n IHn [|x v] /= le_v_n.
    -
      by left; exists [::].
      apply: (iffP catP) => [[u] [v'] [def_v [Lxu starLv']] | [[|[|y u] vv] //=]].
      case/IHn: starLv' => [|vv Lvv def_v'].
      by rewrite -ltnS (leq_trans _ le_v_n) // def_v size_cat !ltnS leq_addl.
      by exists ((x :: u) :: vv); [exact/andP | rewrite def_v def_v'].
      case/andP=> Lyu Lvv [def_x def_v]; exists u.
      exists (flatten vv).
      subst. split => //; split => //. apply/IHn; last by exists vv.
      by rewrite -ltnS (leq_trans _ le_v_n) // size_cat !ltnS leq_addl.
  Qed.

  Lemma star_cat w1 w2 L : w1 \in L -> w2 \in (star L) -> w1 ++ w2 \in star L.
  Proof.
    case: w1 => [|a w1] // H1 /starP [vv Ha Hf]. apply/starP.
      by exists ((a::w1) :: vv); rewrite ?Hf //= H1.
  Qed.

  Lemma all1s {T : eqType} {a : T} {s} {P : T -> Prop} :
    (forall b, b \in a :: s -> P b) <-> P a /\ (forall b, b \in s -> P b).
  Proof.
    split => [A|[A B] b /predU1P [->//|]]; last exact: B.
    split => [|b B]; apply: A => //.
    rewrite !inE eq_refl orbC orbT //.
    rewrite !inE B orbT //.
  Qed.

  Lemma starI (L : lang)  vv :
    (forall v, v \in vv -> v \in L) -> flatten vv \in star L.
  Proof.
    elim: vv => /= [//| v vv IHvv /all1s [H1 H2]].
    exact: star_cat _ (IHvv _).
  Qed.

  Lemma star_eq (l1 : lang) l2: l1 =i l2 -> star l1 =i star l2.
  Proof.
    move => H1 w.
    apply/starP/starP;
    move => [] vv H3 H4; exists vv => //;
    erewrite eq_all;
    try eexact H3; move => x /=; by rewrite ?H1 // -?H1.
  Qed.

  (** semantics for RE *)

  Fixpoint re_lang (e : regex) : lang :=
    match e with
    | #0  => empty
    | #1  => eps
    | # c => chr c
    | e1 @ e2 => cat (re_lang e1) (re_lang e2)
    | e1 :+: e2 => union (re_lang e1) (re_lang e2)
    | Star e1 => star (re_lang e1)
    end.

End RE.
 
