From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.


Ltac unfold_config' :=
match goal with
| |- ?a -[_]->* ?b -> _ =>
  unfold_config_expr a;
  unfold_config_expr b
end.

Ltac follow' x :=
  pose proof x as Hx;
  gen Hx;
  unfold_config';
  simpl_rotate;
  intro Hx;
  try (
  follow Hx;
  clear Hx).


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB---0RB4LA2RA_2LB2LA3RA4LB2LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P1 n :=
  forall l r,
  l <* [2]^^n <{{B}} [4] *> [2;4]^^(1+n) *> r -->*
  l <{{B}} [4]^^(1+n) *> [2;4] *> [2;2]^^n *> r.

Lemma P1_n n:
  P1 n.
Proof.
  unfold P1.
  induction n; intros.
  1: es.
  follow' (IHn ([2]*>l) ([2;4]*>r)).
  do 3 (er; sr).
  follow' (IHn ([3]*>l) ([2;2]*>r)).
  es.
Qed.

Definition S1 a b :=
  0inf <* <[1;3] <* [2]^^a <{{B}} [4] *> [2;4]^^(1+a) *> [2;2] *> [2;4]^^b *> [2;2] *> 0inf.

Lemma Inc1 a b:
  S1 a (1+b) -->*
  S1 (1+a) b.
Proof.
  unfold S1.
  follow P1_n.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 (b+a) 0.
Proof.
  gen a.
  ind b Inc1.
Qed.

Definition S2 a b :=
  0inf <* <[1;3] <* [2]^^a <* <[3;0]^^b <* [3] {{A}}> 0inf.

Lemma Inc2 a b:
  S2 (2+a) b -->*
  S2 a (2+b).
Proof.
  es.
Qed.

Lemma Incs2 n a b:
  S2 (n*2+a) b -->*
  S2 a (n*2+b).
Proof.
  gen a b.
  ind n Inc2.
Qed.

Definition config n := S1 0 (n*2).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 2).
  1: es.
  eapply progress_nonhalt_simple.
  unfold config.
  intros i.
  eexists (i*2+2).
  follow Incs1.
  unfold S1.
  follow P1_n.
  mid10 (S2 (i*2+1) (3+i*2)).
  1: es.
  follow Incs2.
  unfold S2.
  replace (i*2+(3+i*2)) with (3+i*4) by lia.
  replace ((i*2+2)*2) with (4+i*4) by lia.
  es.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB---0RB0LA2RA_2LB2LA3RA4LB2LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P1 n :=
  forall l r,
  l <* [2]^^n <{{B}} [4] *> [2;4]^^(1+n) *> r -->*
  l <{{B}} [4]^^(1+n) *> [2;4] *> [2;2]^^n *> r.

Lemma P1_n n:
  P1 n.
Proof.
  unfold P1.
  induction n; intros.
  1: es.
  follow' (IHn ([2]*>l) ([2;4]*>r)).
  do 3 (er; sr).
  follow' (IHn ([3]*>l) ([2;2]*>r)).
  es.
Qed.

Definition S1 a b :=
  0inf <* <[1;3] <* [2]^^a <{{B}} [4] *> [2;4]^^(1+a) *> [2;2] *> [2;4]^^b *> [2;2] *> 0inf.

Lemma Inc1 a b:
  S1 a (1+b) -->*
  S1 (1+a) b.
Proof.
  unfold S1.
  follow P1_n.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 (b+a) 0.
Proof.
  gen a.
  ind b Inc1.
Qed.

Definition S2 a b :=
  0inf <* <[1;3] <* [2]^^a <* <[3;0]^^b <* [3] {{A}}> 0inf.

Lemma Inc2 a b:
  S2 (2+a) b -->*
  S2 a (2+b).
Proof.
  es.
Qed.

Lemma Incs2 n a b:
  S2 (n*2+a) b -->*
  S2 a (n*2+b).
Proof.
  gen a b.
  ind n Inc2.
Qed.

Definition config n := S1 0 (n*2).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 2).
  1: es.
  eapply progress_nonhalt_simple.
  unfold config.
  intros i.
  eexists (i*2+2).
  follow Incs1.
  unfold S1.
  follow P1_n.
  mid10 (S2 (i*2+1) (3+i*2)).
  1: es.
  follow Incs2.
  unfold S2.
  replace (i*2+(3+i*2)) with (3+i*4) by lia.
  replace ((i*2+2)*2) with (4+i*4) by lia.
  es.
Qed.

End TM2.

