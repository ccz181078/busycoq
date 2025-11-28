From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounterFull.
From BusyCoq Require Import SimplTape.
From BusyCoq Require Import NatMod.

Open Scope list.

Ltac rw_rest :=
  repeat (
  rewrite log2_mulpow2 ||
  rewrite log2_mul2 ||
  rewrite log2_mul2add1 ||
  rewrite log2_1 ||
  rewrite log2_pow2 ||
  rewrite rest_mul_pow2_ ||
  rewrite rest_mul2add1 ||
  rewrite rest_mul2 ||
  rewrite rest_pow2_ ||
  rewrite pow2_spec_).

Ltac rw_BinaryCounter :=
  repeat (
  rewrite Counter_pow2' ||
  rewrite Counter_mulpow2 ||
  cbn[BinaryCounter] ||
  rewrite Counter_pow2).

Lemma LIncs_v1 tm QL QR qL qR L R n m
  (LInc:
  forall r n,
  not_full n ->
  L n <{{QL}} qL *> r -[ tm ]->+
  L (Pos.succ n) <* qR {{QR}}> r)
  (RInc:
  forall l n,
  l <* qR {{QR}}> R (n) -[ tm ]->+
  l <{{QL}} qL *> R (1+n)):
  L n <{{QL}} qL *> R (m) -[ tm ]->*
  L (pow2' (log2 n)) <{{QL}} qL *> R ((N.to_nat (rest n))+m).
Proof.
  remember (N.to_nat (rest n)) as r.
  gen n m.
  induction r; intros.
  - assert (rest n = 0)%N as E by lia.
    rewrite <-full_iff_rest in E.
    rewrite full_iff_pow2' in E.
    rewrite <-E.
    finish.
  - assert (rest n <> 0)%N as E by lia.
    pose proof (rest_S _ E) as H.
    rewrite <-not_full_iff_rest in E.
    follow100 (LInc (R (m)) _ E).
    follow100 RInc.
    epose proof (IHr (Pos.succ n) _ (1+m)) as H1.
    follow H1.
    rewrite not_full_log2_S. 2: apply E.
    finish.
Unshelve.
  lia.
Qed.


Lemma pow2_subadd1 a:
  2^a-1+1 = 2^a.
Proof.
  pose proof (Nat.pow_nonzero 2 a).
  lia.
Qed.

Ltac esh :=
  repeat (simpl_rotate; repeat rewrite lpow_mul; cbn; repeat step1; try sr).


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB0RB_0RC1RE_1LD1RC_1RB0LC_1RF0RA_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [0;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;0;1] {{C}}> r) (at level 30).


Definition d0 := [0;0;1].
Definition d1 := [1;1;1].
Definition L l n := BinaryCounter d0 d1 l n.
Definition R n := [1]^^n *> 0inf.

Lemma LInc l r n (Hnf:not_full n):
  L l n <| r -->+
  L l (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  unfold d0,d1.
  es.
Qed.

Lemma RInc l n:
  l |> R (n) -->+
  l <| R (1+n).
Proof.
  unfold R.
  es.
Qed.

Lemma init:
  c0 -->*
  L (L (0inf <* [1;1]) (pow2 9) <* [1]) (pow2 96) <| R 1.
Proof.
  unfold L,R,d0,d1.
  repeat rewrite Counter_pow2.
  solve_init.
Qed.

Lemma LIncs l n m:
  L l n <| R (m) -->*
  L l (pow2' (log2 n)) <| R ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc.
Qed.

Lemma LOv1 l k n m:
  L (L l (pow2 (S k)) <* [1]) (pow2' n) <| R (1+m*3) -->*
  L (L l (((pow2 k)~1)*(pow2 n)) <* <[1;0;1;1]) (pow2 m) <| R 1.
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2 l k n m:
  L (L l (k~0) <* <[1;0;1;1]) (pow2' n) <| R (2+m*3) -->*
  L l (k~1) <| R (6+n*3+m*3).
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2' n m:
  halts tm (L (0inf <* [1;1]) (pow2' n) <| R (2+m*3)).
Proof.
  eapply halts_evstep.
  2:{
    unfold L,R.
    rw_BinaryCounter.
    unfold d0,d1.
    esh.
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma L_mulpow2_S l k n:
  L l (k*(pow2 (S n))) =
  L l ((k*(pow2 n))~0).
Proof.
  f_equal.
  cbn.
  lia.
Qed.

Ltac follow_LIncs :=
  follow LIncs;
  rw_rest; simpl_N_to_nat.

Ltac R_mod :=
match goal with
| |- _ <| R ?x -->* _ =>
  erewrite (div_mod' x 3 _); [|rw_mod_1]
end.

Lemma halt: halts tm c0.
eapply halts_evstep.
2:{
  follow init.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  follow LOv1.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  rewrite L_mulpow2_S.
  follow LOv2.
  follow_LIncs.
  R_mod.
  finish.
}
apply LOv2'.
Unshelve.
all: solve_ge.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB0RB_0RC1RE_1LD1RC_1RB0LC_1RF0RA_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [0;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;0;1] {{C}}> r) (at level 30).


Definition d0 := [0;0;1].
Definition d1 := [1;1;1].
Definition L l n := BinaryCounter d0 d1 l n.
Definition R n := [1]^^n *> 0inf.

Lemma LInc l r n (Hnf:not_full n):
  L l n <| r -->+
  L l (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  unfold d0,d1.
  es.
Qed.

Lemma RInc l n:
  l |> R (n) -->+
  l <| R (1+n).
Proof.
  unfold R.
  es.
Qed.

Lemma init:
  c0 -->*
  L (L (0inf <* [1;1]) (pow2 9) <* [1]) (pow2 96) <| R 1.
Proof.
  unfold L,R,d0,d1.
  repeat rewrite Counter_pow2.
  solve_init.
Qed.

Lemma LIncs l n m:
  L l n <| R (m) -->*
  L l (pow2' (log2 n)) <| R ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc.
Qed.

Lemma LOv1 l k n m:
  L (L l (pow2 (S k)) <* [1]) (pow2' n) <| R (1+m*3) -->*
  L (L l (((pow2 k)~1)*(pow2 n)) <* <[1;0;1;1]) (pow2 m) <| R 1.
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2 l k n m:
  L (L l (k~0) <* <[1;0;1;1]) (pow2' n) <| R (2+m*3) -->*
  L l (k~1) <| R (6+n*3+m*3).
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2' n m:
  halts tm (L (0inf <* [1;1]) (pow2' n) <| R (2+m*3)).
Proof.
  eapply halts_evstep.
  2:{
    unfold L,R.
    rw_BinaryCounter.
    unfold d0,d1.
    esh.
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma L_mulpow2_S l k n:
  L l (k*(pow2 (S n))) =
  L l ((k*(pow2 n))~0).
Proof.
  f_equal.
  cbn.
  lia.
Qed.

Ltac follow_LIncs :=
  follow LIncs;
  rw_rest; simpl_N_to_nat.

Ltac R_mod :=
match goal with
| |- _ <| R ?x -->* _ =>
  erewrite (div_mod' x 3 _); [|rw_mod_1]
end.

Lemma halt: halts tm c0.
eapply halts_evstep.
2:{
  follow init.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  follow LOv1.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  rewrite L_mulpow2_S.
  follow LOv2.
  follow_LIncs.
  R_mod.
  finish.
}
apply LOv2'.
Unshelve.
all: solve_ge.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB0RB_0RC1RF_---1RD_1LE1RD_1RB0LD_1RF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{D}} [0;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;0;1] {{D}}> r) (at level 30).


Definition d0 := [0;0;1].
Definition d1 := [1;1;1].
Definition L l n := BinaryCounter d0 d1 l n.
Definition R n := [1]^^n *> 0inf.

Lemma LInc l r n (Hnf:not_full n):
  L l n <| r -->+
  L l (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  unfold d0,d1.
  es.
Qed.

Lemma RInc l n:
  l |> R (n) -->+
  l <| R (1+n).
Proof.
  unfold R.
  es.
Qed.

Lemma init:
  c0 -->*
  L (L (0inf <* [1;1]) (pow2 9) <* [1]) (pow2 96) <| R 1.
Proof.
  unfold L,R,d0,d1.
  repeat rewrite Counter_pow2.
  solve_init.
Qed.

Lemma LIncs l n m:
  L l n <| R (m) -->*
  L l (pow2' (log2 n)) <| R ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc.
Qed.

Lemma LOv1 l k n m:
  L (L l (pow2 (S k)) <* [1]) (pow2' n) <| R (1+m*3) -->*
  L (L l (((pow2 k)~1)*(pow2 n)) <* <[1;0;1;1]) (pow2 m) <| R 1.
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2 l k n m:
  L (L l (k~0) <* <[1;0;1;1]) (pow2' n) <| R (2+m*3) -->*
  L l (k~1) <| R (6+n*3+m*3).
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2' n m:
  halts tm (L (0inf <* [1;1]) (pow2' n) <| R (2+m*3)).
Proof.
  eapply halts_evstep.
  2:{
    unfold L,R.
    rw_BinaryCounter.
    unfold d0,d1.
    esh.
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma L_mulpow2_S l k n:
  L l (k*(pow2 (S n))) =
  L l ((k*(pow2 n))~0).
Proof.
  f_equal.
  cbn.
  lia.
Qed.

Ltac follow_LIncs :=
  follow LIncs;
  rw_rest; simpl_N_to_nat.

Ltac R_mod :=
match goal with
| |- _ <| R ?x -->* _ =>
  erewrite (div_mod' x 3 _); [|rw_mod_1]
end.

Lemma halt: halts tm c0.
eapply halts_evstep.
2:{
  follow init.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  follow LOv1.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  rewrite L_mulpow2_S.
  follow LOv2.
  follow_LIncs.
  R_mod.
  finish.
}
apply LOv2'.
Unshelve.
all: solve_ge.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RB_1RD0LB_0RB1RE_1RF0RA_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [0;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;0;1] {{B}}> r) (at level 30).


Definition d0 := [0;0;1].
Definition d1 := [1;1;1].
Definition L l n := BinaryCounter d0 d1 l n.
Definition R n := [1]^^n *> 0inf.

Lemma LInc l r n (Hnf:not_full n):
  L l n <| r -->+
  L l (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  unfold d0,d1.
  es.
Qed.

Lemma RInc l n:
  l |> R (n) -->+
  l <| R (1+n).
Proof.
  unfold R.
  es.
Qed.

Lemma init:
  c0 -->*
  L (L (0inf <* [1;1]) (pow2 9) <* [1]) (pow2 96) <| R 1.
Proof.
  unfold L,R,d0,d1.
  repeat rewrite Counter_pow2.
  solve_init.
Qed.

Lemma LIncs l n m:
  L l n <| R (m) -->*
  L l (pow2' (log2 n)) <| R ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc.
Qed.

Lemma LOv1 l k n m:
  L (L l (pow2 (S k)) <* [1]) (pow2' n) <| R (1+m*3) -->*
  L (L l (((pow2 k)~1)*(pow2 n)) <* <[1;0;1;1]) (pow2 m) <| R 1.
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2 l k n m:
  L (L l (k~0) <* <[1;0;1;1]) (pow2' n) <| R (2+m*3) -->*
  L l (k~1) <| R (6+n*3+m*3).
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2' n m:
  halts tm (L (0inf <* [1;1]) (pow2' n) <| R (2+m*3)).
Proof.
  eapply halts_evstep.
  2:{
    unfold L,R.
    rw_BinaryCounter.
    unfold d0,d1.
    esh.
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma L_mulpow2_S l k n:
  L l (k*(pow2 (S n))) =
  L l ((k*(pow2 n))~0).
Proof.
  f_equal.
  cbn.
  lia.
Qed.

Ltac follow_LIncs :=
  follow LIncs;
  rw_rest; simpl_N_to_nat.

Ltac R_mod :=
match goal with
| |- _ <| R ?x -->* _ =>
  erewrite (div_mod' x 3 _); [|rw_mod_1]
end.

Lemma halt: halts tm c0.
eapply halts_evstep.
2:{
  follow init.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  follow LOv1.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  rewrite L_mulpow2_S.
  follow LOv2.
  follow_LIncs.
  R_mod.
  finish.
}
apply LOv2'.
Unshelve.
all: solve_ge.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RB_0RD0LB_---0LE_1RE0RA_1RD1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [0;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;0;1] {{B}}> r) (at level 30).


Definition d0 := [0;0;1].
Definition d1 := [1;1;1].
Definition L l n := BinaryCounter d0 d1 l n.
Definition R n := [1]^^n *> 0inf.

Lemma LInc l r n (Hnf:not_full n):
  L l n <| r -->+
  L l (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  unfold d0,d1.
  es.
Qed.

Lemma RInc l n:
  l |> R (n) -->+
  l <| R (1+n).
Proof.
  unfold R.
  es.
Qed.

Lemma init:
  c0 -->*
  L (L (0inf <* [1;1]) (pow2 9) <* [1]) (pow2 96) <| R 1.
Proof.
  unfold L,R,d0,d1.
  repeat rewrite Counter_pow2.
  solve_init.
Qed.

Lemma LIncs l n m:
  L l n <| R (m) -->*
  L l (pow2' (log2 n)) <| R ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc.
Qed.

Lemma LOv1 l k n m:
  L (L l (pow2 (S k)) <* [1]) (pow2' n) <| R (1+m*3) -->*
  L (L l (((pow2 k)~1)*(pow2 n)) <* <[1;0;1;1]) (pow2 m) <| R 1.
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2 l k n m:
  L (L l (k~0) <* <[1;0;1;1]) (pow2' n) <| R (2+m*3) -->*
  L l (k~1) <| R (6+n*3+m*3).
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2' n m:
  halts tm (L (0inf <* [1;1]) (pow2' n) <| R (2+m*3)).
Proof.
  eapply halts_evstep.
  2:{
    unfold L,R.
    rw_BinaryCounter.
    unfold d0,d1.
    esh.
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma L_mulpow2_S l k n:
  L l (k*(pow2 (S n))) =
  L l ((k*(pow2 n))~0).
Proof.
  f_equal.
  cbn.
  lia.
Qed.

Ltac follow_LIncs :=
  follow LIncs;
  rw_rest; simpl_N_to_nat.

Ltac R_mod :=
match goal with
| |- _ <| R ?x -->* _ =>
  erewrite (div_mod' x 3 _); [|rw_mod_1]
end.

Lemma halt: halts tm c0.
eapply halts_evstep.
2:{
  follow init.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  follow LOv1.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  rewrite L_mulpow2_S.
  follow LOv2.
  follow_LIncs.
  R_mod.
  finish.
}
apply LOv2'.
Unshelve.
all: solve_ge.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RB_1RD0LB_0RB1RE_1RF0RA_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [0;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;0;1] {{B}}> r) (at level 30).


Definition d0 := [0;0;1].
Definition d1 := [1;1;1].
Definition L l n := BinaryCounter d0 d1 l n.
Definition R n := [1]^^n *> 0inf.

Lemma LInc l r n (Hnf:not_full n):
  L l n <| r -->+
  L l (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  unfold d0,d1.
  es.
Qed.

Lemma RInc l n:
  l |> R (n) -->+
  l <| R (1+n).
Proof.
  unfold R.
  es.
Qed.

Lemma init:
  c0 -->*
  L (L (0inf <* [1;1]) (pow2 9) <* [1]) (pow2 96) <| R 1.
Proof.
  unfold L,R,d0,d1.
  repeat rewrite Counter_pow2.
  solve_init.
Qed.

Lemma LIncs l n m:
  L l n <| R (m) -->*
  L l (pow2' (log2 n)) <| R ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc.
Qed.

Lemma LOv1 l k n m:
  L (L l (pow2 (S k)) <* [1]) (pow2' n) <| R (1+m*3) -->*
  L (L l (((pow2 k)~1)*(pow2 n)) <* <[1;0;1;1]) (pow2 m) <| R 1.
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2 l k n m:
  L (L l (k~0) <* <[1;0;1;1]) (pow2' n) <| R (2+m*3) -->*
  L l (k~1) <| R (6+n*3+m*3).
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2' n m:
  halts tm (L (0inf <* [1;1]) (pow2' n) <| R (2+m*3)).
Proof.
  eapply halts_evstep.
  2:{
    unfold L,R.
    rw_BinaryCounter.
    unfold d0,d1.
    esh.
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma L_mulpow2_S l k n:
  L l (k*(pow2 (S n))) =
  L l ((k*(pow2 n))~0).
Proof.
  f_equal.
  cbn.
  lia.
Qed.

Ltac follow_LIncs :=
  follow LIncs;
  rw_rest; simpl_N_to_nat.

Ltac R_mod :=
match goal with
| |- _ <| R ?x -->* _ =>
  erewrite (div_mod' x 3 _); [|rw_mod_1]
end.

Lemma halt: halts tm c0.
eapply halts_evstep.
2:{
  follow init.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  follow LOv1.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  rewrite L_mulpow2_S.
  follow LOv2.
  follow_LIncs.
  R_mod.
  finish.
}
apply LOv2'.
Unshelve.
all: solve_ge.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RB_1RD0LB_0RF1RE_1RE0RA_---1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [0;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;0;1] {{B}}> r) (at level 30).


Definition d0 := [0;0;1].
Definition d1 := [1;1;1].
Definition L l n := BinaryCounter d0 d1 l n.
Definition R n := [1]^^n *> 0inf.

Lemma LInc l r n (Hnf:not_full n):
  L l n <| r -->+
  L l (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  unfold d0,d1.
  es.
Qed.

Lemma RInc l n:
  l |> R (n) -->+
  l <| R (1+n).
Proof.
  unfold R.
  es.
Qed.

Lemma init:
  c0 -->*
  L (L (0inf <* [1;1]) (pow2 9) <* [1]) (pow2 96) <| R 1.
Proof.
  unfold L,R,d0,d1.
  repeat rewrite Counter_pow2.
  solve_init.
Qed.

Lemma LIncs l n m:
  L l n <| R (m) -->*
  L l (pow2' (log2 n)) <| R ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc.
Qed.

Lemma LOv1 l k n m:
  L (L l (pow2 (S k)) <* [1]) (pow2' n) <| R (1+m*3) -->*
  L (L l (((pow2 k)~1)*(pow2 n)) <* <[1;0;1;1]) (pow2 m) <| R 1.
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2 l k n m:
  L (L l (k~0) <* <[1;0;1;1]) (pow2' n) <| R (2+m*3) -->*
  L l (k~1) <| R (6+n*3+m*3).
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2' n m:
  halts tm (L (0inf <* [1;1]) (pow2' n) <| R (2+m*3)).
Proof.
  eapply halts_evstep.
  2:{
    unfold L,R.
    rw_BinaryCounter.
    unfold d0,d1.
    esh.
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma L_mulpow2_S l k n:
  L l (k*(pow2 (S n))) =
  L l ((k*(pow2 n))~0).
Proof.
  f_equal.
  cbn.
  lia.
Qed.

Ltac follow_LIncs :=
  follow LIncs;
  rw_rest; simpl_N_to_nat.

Ltac R_mod :=
match goal with
| |- _ <| R ?x -->* _ =>
  erewrite (div_mod' x 3 _); [|rw_mod_1]
end.

Lemma halt: halts tm c0.
eapply halts_evstep.
2:{
  follow init.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  follow LOv1.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  rewrite L_mulpow2_S.
  follow LOv2.
  follow_LIncs.
  R_mod.
  finish.
}
apply LOv2'.
Unshelve.
all: solve_ge.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RB_1RD0LB_1RF1RE_1RE0RA_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [0;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;0;1] {{B}}> r) (at level 30).


Definition d0 := [0;0;1].
Definition d1 := [1;1;1].
Definition L l n := BinaryCounter d0 d1 l n.
Definition R n := [1]^^n *> 0inf.

Lemma LInc l r n (Hnf:not_full n):
  L l n <| r -->+
  L l (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  unfold d0,d1.
  es.
Qed.

Lemma RInc l n:
  l |> R (n) -->+
  l <| R (1+n).
Proof.
  unfold R.
  es.
Qed.

Lemma init:
  c0 -->*
  L (L (0inf <* [1;1]) (pow2 9) <* [1]) (pow2 96) <| R 1.
Proof.
  unfold L,R,d0,d1.
  repeat rewrite Counter_pow2.
  solve_init.
Qed.

Lemma LIncs l n m:
  L l n <| R (m) -->*
  L l (pow2' (log2 n)) <| R ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc.
Qed.

Lemma LOv1 l k n m:
  L (L l (pow2 (S k)) <* [1]) (pow2' n) <| R (1+m*3) -->*
  L (L l (((pow2 k)~1)*(pow2 n)) <* <[1;0;1;1]) (pow2 m) <| R 1.
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2 l k n m:
  L (L l (k~0) <* <[1;0;1;1]) (pow2' n) <| R (2+m*3) -->*
  L l (k~1) <| R (6+n*3+m*3).
Proof.
  unfold L,R.
  rw_BinaryCounter.
  unfold d0,d1.
  es.
Qed.

Lemma LOv2' n m:
  halts tm (L (0inf <* [1;1]) (pow2' n) <| R (2+m*3)).
Proof.
  eapply halts_evstep.
  2:{
    unfold L,R.
    rw_BinaryCounter.
    unfold d0,d1.
    esh.
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

Lemma L_mulpow2_S l k n:
  L l (k*(pow2 (S n))) =
  L l ((k*(pow2 n))~0).
Proof.
  f_equal.
  cbn.
  lia.
Qed.

Ltac follow_LIncs :=
  follow LIncs;
  rw_rest; simpl_N_to_nat.

Ltac R_mod :=
match goal with
| |- _ <| R ?x -->* _ =>
  erewrite (div_mod' x 3 _); [|rw_mod_1]
end.

Lemma halt: halts tm c0.
eapply halts_evstep.
2:{
  follow init.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  follow LOv1.
  follow_LIncs.
  rewrite pow2_subadd1.
  R_mod.
  rewrite L_mulpow2_S.
  follow LOv2.
  follow_LIncs.
  R_mod.
  finish.
}
apply LOv2'.
Unshelve.
all: solve_ge.
Qed.

End TM12.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC0RD_1LB1RE_---1LC_1LF1RA_0RB0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1;1;1;1;1;1;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1;1;0;1;1] {{A}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0;0;0]^^n *> [1] *> 0inf.
Definition R2 n m := [0;0;0]^^n *> [1] *> [0;0;0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (1+m) -->+
  L (pow2 n) <| R2 1 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 n 0 -->*
  L ((k~1)*(pow2 (1+n))) <| R1 0.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(n,m) :=
  L (pow2' n) <| R1 (1+m).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,22)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 n)) >= m+1).
  2: cbn; lia.
  intros [n m] H.
  remember (3+m+n) as n'.
  remember (((2^n-1-(m+1))*2+1)*2^(1+(m+1))-1) as m'.
  eexists (n',m'-1).
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rw_rest.
    replace (Npos (Pos.of_nat (m+1))) with (N.of_nat (m+1)) by lia.
    rw_rest.
    simpl_N_to_nat.
    finish.
    rewrite <-Heqm'.
    assert (m'>=1) by (subst m'; solve_ge).
    repeat (lia || f_equal).
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  subst.
  replace (1+(m+1)) with (m+2) by lia.
  unfold ge.
  remember ((2^n-1-(m+1))*2+1) as v1.
  replace (3+m+n) with ((n+1)+(m+2)) by lia.
  rewrite (Nat.pow_add_r _ (n+1)).
  remember (2^(m+2)) as v2.
  assert (v1<=2^(n+1)). {
    rewrite Nat.add_comm. cbn. lia.
  }
  pose proof (Nat.mul_le_mono_r v1 (2^(n+1)) v2).
  assert (v1*v2>=2) by (subst; solve_ge).
  lia.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC---_1LD1RE_1RC1LD_1LF1RA_0RD0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{D}} [1;1;1;1;1;1;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1;1;0;1;1] {{A}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0;0;0]^^n *> [1] *> 0inf.
Definition R2 n m := [0;0;0]^^n *> [1] *> [0;0;0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (1+m) -->+
  L (pow2 n) <| R2 1 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 n 0 -->*
  L ((k~1)*(pow2 (1+n))) <| R1 0.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(n,m) :=
  L (pow2' n) <| R1 (1+m).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,22)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 n)) >= m+1).
  2: cbn; lia.
  intros [n m] H.
  remember (3+m+n) as n'.
  remember (((2^n-1-(m+1))*2+1)*2^(1+(m+1))-1) as m'.
  eexists (n',m'-1).
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rw_rest.
    replace (Npos (Pos.of_nat (m+1))) with (N.of_nat (m+1)) by lia.
    rw_rest.
    simpl_N_to_nat.
    finish.
    rewrite <-Heqm'.
    assert (m'>=1) by (subst m'; solve_ge).
    repeat (lia || f_equal).
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  subst.
  replace (1+(m+1)) with (m+2) by lia.
  unfold ge.
  remember ((2^n-1-(m+1))*2+1) as v1.
  replace (3+m+n) with ((n+1)+(m+2)) by lia.
  rewrite (Nat.pow_add_r _ (n+1)).
  remember (2^(m+2)) as v2.
  assert (v1<=2^(n+1)). {
    rewrite Nat.add_comm. cbn. lia.
  }
  pose proof (Nat.mul_le_mono_r v1 (2^(n+1)) v2).
  assert (v1*v2>=2) by (subst; solve_ge).
  lia.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA1LB_1LD1RF_0RE0LD_1RA---_1RE0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1;1;1;1;1;1;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1;1;0;1;1] {{F}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0;0;0]^^n *> [1] *> 0inf.
Definition R2 n m := [0;0;0]^^n *> [1] *> [0;0;0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (1+m) -->+
  L (pow2 n) <| R2 1 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 n 0 -->*
  L ((k~1)*(pow2 (1+n))) <| R1 0.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(n,m) :=
  L (pow2' n) <| R1 (1+m).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,22)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 n)) >= m+1).
  2: cbn; lia.
  intros [n m] H.
  remember (3+m+n) as n'.
  remember (((2^n-1-(m+1))*2+1)*2^(1+(m+1))-1) as m'.
  eexists (n',m'-1).
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rw_rest.
    replace (Npos (Pos.of_nat (m+1))) with (N.of_nat (m+1)) by lia.
    rw_rest.
    simpl_N_to_nat.
    finish.
    rewrite <-Heqm'.
    assert (m'>=1) by (subst m'; solve_ge).
    repeat (lia || f_equal).
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  subst.
  replace (1+(m+1)) with (m+2) by lia.
  unfold ge.
  remember ((2^n-1-(m+1))*2+1) as v1.
  replace (3+m+n) with ((n+1)+(m+2)) by lia.
  rewrite (Nat.pow_add_r _ (n+1)).
  remember (2^(m+2)) as v2.
  assert (v1<=2^(n+1)). {
    rewrite Nat.add_comm. cbn. lia.
  }
  pose proof (Nat.mul_le_mono_r v1 (2^(n+1)) v2).
  assert (v1*v2>=2) by (subst; solve_ge).
  lia.
Qed.

End TM16.

Lemma Npos_Pos_of_nat x:
  Npos (Pos.of_nat (1+x)) = N.of_nat (1+x).
Proof. lia. Qed.

Lemma div_mod'' a b c:
  a mod b = c ->
  a = a/b*b+c.
Proof.
  intros H.
  rewrite Nat.add_comm.
  apply div_mod',H.
Qed.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC---_0LD0LC_1RD0RA_1RE1RF_1LC0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{D}} [0;0;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1] {{E}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0]^^n *> [1] *> 0inf.
Definition R2 n m := [0]^^n *> [1] *> [0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (1+m) -->+
  L (pow2 n) <| R2 1 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 (1+n*3) 0 -->*
  L ((k~1)*(pow2 (1+n))) <| R1 0.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(k,n) :=
  L (pow2' (k*2+1)) <| R1 (1+(n*2)*3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (2,4)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 (n*2+1))) >= m*2*3+1+1 /\ n>=1 /\ m>=1).
  2: cbn; lia.
  intros [n m] [H [Hn Hm]].
  eexists (_,_).
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    1: lia.
    replace (m*2*3+1) with (1+m*2*3) by lia.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rewrite Npos_Pos_of_nat.
    rw_rest.
    simpl_N_to_nat.
    rewrite <-(Nat.add_1_l (n*2+1)).
    repeat rewrite <-(Nat.mul_assoc _ 2 3).
    change (2*3) with 6.
    match goal with
    | |- L (pow2' ?n') <| R1 ?m' -->* _ =>
      erewrite (div_mod' m' 6 _); [|rw_mod_1];
      erewrite (div_mod' n' 2 _); [|rw_mod_1]
    end.
    rewrite Nat.add_comm.
    finish.
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  repeat rewrite <-(Nat.mul_assoc _ 2 3) in *.
  change (2*3) with 6 in *.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  remember (n*2+1) as n0.
  remember (m*2) as m0.
  replace (m*6) with (m0*3) in * by lia.
  split.
  2: split; solve_ge.
  unfold ge.
  remember ((2^n0-1-(1+m0*3))*2+1) as v1.
  rewrite (Nat.add_comm (1+m0)).
  rewrite (Nat.pow_add_r _ (1+n0)).
  remember (2^(1+m0)) as v2.
  apply Nat.le_add_le_sub_l.
  assert (v1+1<=2^(1+n0)). { cbn. lia. }
  assert (v2>=1) by (subst; solve_ge).
  pose proof (Nat.mul_le_mono_r (v1+1) (2^(1+n0)) v2).
  lia.
Unshelve.
  all: solve_ge.
  gen H.
  rw_rest.
  simpl_N_to_nat.
  lia.
Qed.

End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC0LB_0LD---_1RE1LD_1RE1RF_1LB1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{D}} [1;1;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1] {{E}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0]^^n *> [1] *> 0inf.
Definition R2 n m := [0]^^n *> [1] *> [0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (m) -->+
  L (pow2 n) <| R2 0 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 (0+n*3) 0 -->*
  L (((k~1)*(pow2 (n)))~1) <| R1 0.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(k,n) :=
  L (pow2' (k*2+1)) <| R1 (0+(n*2)*3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (2,4)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 (n*2+1))) >= m*2*3+0+2 /\ n>=1 /\ m>=1).
  2: cbn; lia.
  intros [n m] [H [Hn Hm]].
  eexists (_,_).
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    1: lia.
    replace (0+m*2*3+0) with (0+m*2*3) by lia.
    replace (0+m*2*3+1) with (1+m*2*3) by lia.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rewrite Npos_Pos_of_nat.
    rw_rest.
    simpl_N_to_nat.
    replace (S(m*2+S(n*2+1))) with (m*2+1+(1+(n*2+1))) by lia.
    repeat rewrite <-(Nat.mul_assoc _ 2 3).
    change (2*3) with 6.
    match goal with
    | |- L (pow2' ?n') <| R1 ?m' -->* _ =>
      erewrite (div_mod' m' 6 _); [|rw_mod_1];
      erewrite (div_mod' n' 2 _); [|rw_mod_1]
    end.
    rewrite Nat.add_comm.
    finish.
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  repeat rewrite <-(Nat.mul_assoc _ 2 3) in *.
  change (2*3) with 6 in *.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  remember (n*2+1) as n0.
  remember (m*2) as m0.
  replace (m*6) with (m0*3) in * by lia.
  split.
  2: split; solve_ge.
  unfold ge.
  rewrite (Nat.add_comm (m0+1)).
  repeat rewrite Nat.pow_add_r.
  change (2^1) with 2.
  pose proof (Nat.pow_nonzero 2 n0).
  pose proof (Nat.pow_nonzero 2 m0).
  lia.
Unshelve.
  all: solve_ge.
  gen H.
  rw_rest.
  simpl_N_to_nat.
  lia.
Qed.

End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC---_1RD1LC_1RD1RE_1LF1RA_1LC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1;1;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1] {{D}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0]^^n *> [1] *> 0inf.
Definition R2 n m := [0]^^n *> [1] *> [0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (m) -->+
  L (pow2 n) <| R2 0 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 (0+n*3) 0 -->*
  L (((k~1)*(pow2 (n)))~1) <| R1 0.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(k,n) :=
  L (pow2' (k*2+1)) <| R1 (0+(n*2)*3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (2,4)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 (n*2+1))) >= m*2*3+0+2 /\ n>=1 /\ m>=1).
  2: cbn; lia.
  intros [n m] [H [Hn Hm]].
  eexists (_,_).
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    1: lia.
    replace (0+m*2*3+0) with (0+m*2*3) by lia.
    replace (0+m*2*3+1) with (1+m*2*3) by lia.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rewrite Npos_Pos_of_nat.
    rw_rest.
    simpl_N_to_nat.
    replace (S(m*2+S(n*2+1))) with (m*2+1+(1+(n*2+1))) by lia.
    repeat rewrite <-(Nat.mul_assoc _ 2 3).
    change (2*3) with 6.
    match goal with
    | |- L (pow2' ?n') <| R1 ?m' -->* _ =>
      erewrite (div_mod' m' 6 _); [|rw_mod_1];
      erewrite (div_mod' n' 2 _); [|rw_mod_1]
    end.
    rewrite Nat.add_comm.
    finish.
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  repeat rewrite <-(Nat.mul_assoc _ 2 3) in *.
  change (2*3) with 6 in *.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  remember (n*2+1) as n0.
  remember (m*2) as m0.
  replace (m*6) with (m0*3) in * by lia.
  split.
  2: split; solve_ge.
  unfold ge.
  rewrite (Nat.add_comm (m0+1)).
  repeat rewrite Nat.pow_add_r.
  change (2^1) with 2.
  pose proof (Nat.pow_nonzero 2 n0).
  pose proof (Nat.pow_nonzero 2 m0).
  lia.
Unshelve.
  all: solve_ge.
  gen H.
  rw_rest.
  simpl_N_to_nat.
  lia.
Qed.

End TM19.


Module TM20.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD1LC_1RD1RA_0RF0RD_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1;1;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1] {{D}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0]^^n *> [1] *> 0inf.
Definition R2 n m := [0]^^n *> [1] *> [0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (m) -->+
  L (pow2 n) <| R2 0 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 (0+n*3) 0 -->*
  L (((k~1)*(pow2 (n)))~1) <| R1 0.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(k,n) :=
  L (pow2' (k*2+1)) <| R1 (0+(n*2)*3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (2,4)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 (n*2+1))) >= m*2*3+0+2 /\ n>=1 /\ m>=1).
  2: cbn; lia.
  intros [n m] [H [Hn Hm]].
  eexists (_,_).
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    1: lia.
    replace (0+m*2*3+0) with (0+m*2*3) by lia.
    replace (0+m*2*3+1) with (1+m*2*3) by lia.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rewrite Npos_Pos_of_nat.
    rw_rest.
    simpl_N_to_nat.
    replace (S(m*2+S(n*2+1))) with (m*2+1+(1+(n*2+1))) by lia.
    repeat rewrite <-(Nat.mul_assoc _ 2 3).
    change (2*3) with 6.
    match goal with
    | |- L (pow2' ?n') <| R1 ?m' -->* _ =>
      erewrite (div_mod' m' 6 _); [|rw_mod_1];
      erewrite (div_mod' n' 2 _); [|rw_mod_1]
    end.
    rewrite Nat.add_comm.
    finish.
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  repeat rewrite <-(Nat.mul_assoc _ 2 3) in *.
  change (2*3) with 6 in *.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  remember (n*2+1) as n0.
  remember (m*2) as m0.
  replace (m*6) with (m0*3) in * by lia.
  split.
  2: split; solve_ge.
  unfold ge.
  rewrite (Nat.add_comm (m0+1)).
  repeat rewrite Nat.pow_add_r.
  change (2^1) with 2.
  pose proof (Nat.pow_nonzero 2 n0).
  pose proof (Nat.pow_nonzero 2 m0).
  lia.
Unshelve.
  all: solve_ge.
  gen H.
  rw_rest.
  simpl_N_to_nat.
  lia.
Qed.

End TM20.


Module TM21.

Definition tm := Eval compute in (TM_from_str "1RB1RC_0LC---_1RC1RD_1LE0RA_0LF0LE_1RF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{F}} [0;0;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1] {{C}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0]^^n *> [1] *> 0inf.
Definition R2 n m := [0]^^n *> [1] *> [0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (1+m) -->+
  L (pow2 n) <| R2 1 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 (1+n*3) 0 -->*
  L ((k~1)*(pow2 (1+n))) <| R1 0.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(k,n) :=
  L (pow2' (k*2+1)) <| R1 (1+(n*2)*3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (2,4)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 (n*2+1))) >= m*2*3+1+1 /\ n>=1 /\ m>=1).
  2: cbn; lia.
  intros [n m] [H [Hn Hm]].
  eexists (_,_).
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    1: lia.
    replace (m*2*3+1) with (1+m*2*3) by lia.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rewrite Npos_Pos_of_nat.
    rw_rest.
    simpl_N_to_nat.
    rewrite <-(Nat.add_1_l (n*2+1)).
    repeat rewrite <-(Nat.mul_assoc _ 2 3).
    change (2*3) with 6.
    match goal with
    | |- L (pow2' ?n') <| R1 ?m' -->* _ =>
      erewrite (div_mod' m' 6 _); [|rw_mod_1];
      erewrite (div_mod' n' 2 _); [|rw_mod_1]
    end.
    rewrite Nat.add_comm.
    finish.
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  repeat rewrite <-(Nat.mul_assoc _ 2 3) in *.
  change (2*3) with 6 in *.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  remember (n*2+1) as n0.
  remember (m*2) as m0.
  replace (m*6) with (m0*3) in * by lia.
  split.
  2: split; solve_ge.
  unfold ge.
  remember ((2^n0-1-(1+m0*3))*2+1) as v1.
  rewrite (Nat.add_comm (1+m0)).
  rewrite (Nat.pow_add_r _ (1+n0)).
  remember (2^(1+m0)) as v2.
  apply Nat.le_add_le_sub_l.
  assert (v1+1<=2^(1+n0)). { cbn. lia. }
  assert (v2>=1) by (subst; solve_ge).
  pose proof (Nat.mul_le_mono_r (v1+1) (2^(1+n0)) v2).
  lia.
Unshelve.
  all: solve_ge.
  gen H.
  rw_rest.
  simpl_N_to_nat.
  lia.
Qed.

End TM21.


Module TM22.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC---_0LD0LC_1RD0RA_1RE0RF_0LA1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{D}} [0;0;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1] {{E}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0]^^n *> [1] *> 0inf.
Definition R2 n m := [0]^^n *> [1] *> [0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (1+m) -->+
  L (pow2 n) <| R2 1 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 (1+n*3) 0 -->*
  L ((k~1)*(pow2 (1+n))) <| R1 0.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(k,n) :=
  L (pow2' (k*2+1)) <| R1 (1+(n*2)*3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (2,4)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 (n*2+1))) >= m*2*3+1+1 /\ n>=1 /\ m>=1).
  2: cbn; lia.
  intros [n m] [H [Hn Hm]].
  eexists (_,_).
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    1: lia.
    replace (m*2*3+1) with (1+m*2*3) by lia.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rewrite Npos_Pos_of_nat.
    rw_rest.
    simpl_N_to_nat.
    rewrite <-(Nat.add_1_l (n*2+1)).
    repeat rewrite <-(Nat.mul_assoc _ 2 3).
    change (2*3) with 6.
    match goal with
    | |- L (pow2' ?n') <| R1 ?m' -->* _ =>
      erewrite (div_mod' m' 6 _); [|rw_mod_1];
      erewrite (div_mod' n' 2 _); [|rw_mod_1]
    end.
    rewrite Nat.add_comm.
    finish.
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  repeat rewrite <-(Nat.mul_assoc _ 2 3) in *.
  change (2*3) with 6 in *.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  rewrite <-div_mod''.
  2: rw_mod; reflexivity.
  remember (n*2+1) as n0.
  remember (m*2) as m0.
  replace (m*6) with (m0*3) in * by lia.
  split.
  2: split; solve_ge.
  unfold ge.
  remember ((2^n0-1-(1+m0*3))*2+1) as v1.
  rewrite (Nat.add_comm (1+m0)).
  rewrite (Nat.pow_add_r _ (1+n0)).
  remember (2^(1+m0)) as v2.
  apply Nat.le_add_le_sub_l.
  assert (v1+1<=2^(1+n0)). { cbn. lia. }
  assert (v2>=1) by (subst; solve_ge).
  pose proof (Nat.mul_le_mono_r (v1+1) (2^(1+n0)) v2).
  lia.
Unshelve.
  all: solve_ge.
  gen H.
  rw_rest.
  simpl_N_to_nat.
  lia.
Qed.

End TM22.


Module TM23.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0LF_1RD0RF_1LE---_1RF0LE_1RB1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{F}} [0;1;1;1;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1;1;0] {{F}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0;0;0]^^n *> [1] *> 0inf.
Definition R2 n m := [0;0;0]^^n *> [1] *> [0;0;0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (1+m) -->+
  L (pow2 n) <| R2 1 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 n 0 -->*
  L ((k~1)*(pow2 (n))) <| R1 1.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(n,m) :=
  L (pow2' n) <| R1 (1+m).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (3,1)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 n)) >= m+1).
  2: cbn; lia.
  intros [n m] H.
  remember (2+m+n) as n'.
  remember (((2^n-1-(m+1))*2+1)*2^((m+1))-1) as m'.
  eexists (n',m').
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rw_rest.
    replace (Npos (Pos.of_nat (m+1))) with (N.of_nat (m+1)) by lia.
    rw_rest.
    simpl_N_to_nat.
    finish.
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  subst.
  replace (1+(m+1)) with (m+2) by lia.
  unfold ge.
  remember ((2^n-1-(m+1))*2+1) as v1.
  replace (2+m+n) with ((n+1)+(m+1)) by lia.
  rewrite (Nat.pow_add_r _ (n+1)).
  remember (2^(m+1)) as v2.
  assert (v1+1<=2^(n+1)). {
    rewrite (Nat.add_comm n). cbn. lia.
  }
  pose proof (Nat.mul_le_mono_r (v1+1) (2^(n+1)) v2 H0).
  pose proof (Nat.pow_nonzero 2 (m+1)).
  lia.
Qed.

End TM23.


Module TM24.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC---_0LD0LC_1RD0RA_1RE1RF_1RA0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{D}} [0;0;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1] {{E}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0;0;0]^^n *> [1] *> 0inf.
Definition R2 n m := [0;0;0]^^n *> [1] *> [0;0;0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (1+m) -->+
  L (pow2 n) <| R2 1 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 n 0 -->*
  L ((k~1)*(pow2 (n))) <| R1 1.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(n,m) :=
  L (pow2' n) <| R1 (1+m).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (3,1)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 n)) >= m+1).
  2: cbn; lia.
  intros [n m] H.
  remember (2+m+n) as n'.
  remember (((2^n-1-(m+1))*2+1)*2^((m+1))-1) as m'.
  eexists (n',m').
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rw_rest.
    replace (Npos (Pos.of_nat (m+1))) with (N.of_nat (m+1)) by lia.
    rw_rest.
    simpl_N_to_nat.
    finish.
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  subst.
  replace (1+(m+1)) with (m+2) by lia.
  unfold ge.
  remember ((2^n-1-(m+1))*2+1) as v1.
  replace (2+m+n) with ((n+1)+(m+1)) by lia.
  rewrite (Nat.pow_add_r _ (n+1)).
  remember (2^(m+1)) as v2.
  assert (v1+1<=2^(n+1)). {
    rewrite (Nat.add_comm n). cbn. lia.
  }
  pose proof (Nat.mul_le_mono_r (v1+1) (2^(n+1)) v2 H0).
  pose proof (Nat.pow_nonzero 2 (m+1)).
  lia.
Qed.

End TM24.


Module TM25.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC0LB_0RD1RE_1LB---_1LA1RF_1RD0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [0;1;1;1;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1;1;0] {{C}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0;0;0]^^n *> [1] *> 0inf.
Definition R2 n m := [0;0;0]^^n *> [1] *> [0;0;0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (1+m) -->+
  L (pow2 n) <| R2 1 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 n 0 -->*
  L ((k~1)*(pow2 (n))) <| R1 1.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(n,m) :=
  L (pow2' n) <| R1 (1+m).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (3,1)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 n)) >= m+1).
  2: cbn; lia.
  intros [n m] H.
  remember (2+m+n) as n'.
  remember (((2^n-1-(m+1))*2+1)*2^((m+1))-1) as m'.
  eexists (n',m').
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rw_rest.
    replace (Npos (Pos.of_nat (m+1))) with (N.of_nat (m+1)) by lia.
    rw_rest.
    simpl_N_to_nat.
    finish.
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  subst.
  replace (1+(m+1)) with (m+2) by lia.
  unfold ge.
  remember ((2^n-1-(m+1))*2+1) as v1.
  replace (2+m+n) with ((n+1)+(m+1)) by lia.
  rewrite (Nat.pow_add_r _ (n+1)).
  remember (2^(m+1)) as v2.
  assert (v1+1<=2^(n+1)). {
    rewrite (Nat.add_comm n). cbn. lia.
  }
  pose proof (Nat.mul_le_mono_r (v1+1) (2^(n+1)) v2 H0).
  pose proof (Nat.pow_nonzero 2 (m+1)).
  lia.
Qed.

End TM25.


Module TM26.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0LF_1RD0RF_1LE---_1RF0LE_0RD1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{F}} [0;1;1;1;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* <[1;1;0;1;1;0] {{F}}> r) (at level 30).


Definition L n := BinaryCounter <[1;1;0] <[1;1;1] (0inf<*[1]) n.
Definition R1 n := [0;0;0]^^n *> [1] *> 0inf.
Definition R2 n m := [0;0;0]^^n *> [1] *> [0;0;0]^^m *> [1] *> 0inf.

Lemma LInc r n (Hnf:not_full n):
  L n <| r -->+
  L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc; auto.
  es.
Qed.

Lemma RInc1 l n:
  l |> R1 (n) -->+
  l <| R1 (1+n).
Proof.
  unfold R1.
  es.
Qed.

Lemma RInc2 l n m:
  l |> R2 (n) (1+m) -->+
  l <| R2 (1+n) m.
Proof.
  unfold R2.
  es.
Qed.

Lemma LIncs1 n m:
  L n <| R1 (m) -->*
  L (pow2' (log2 n)) <| R1 ((N.to_nat (rest n))+m).
Proof.
  eapply LIncs_v1.
  - apply LInc.
  - apply RInc1.
Qed.

Lemma LIncs2 k n m:
  N.to_nat (rest k) >= m+1 ->
  L k <| R2 n m -->*
  L (((Pos.of_nat (m+1)))+k) |> R2 (m+n) 0.
Proof.
  gen n k.
  induction m; intros.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n 0) _ Hk).
    finish.
  - assert (rest k <> 0)%N as Hk by lia.
    rewrite <-not_full_iff_rest in Hk.
    follow100 (LInc (R2 n (S m)) _ Hk).
    follow100 RInc2.
    follow IHm.
    2: finish.
    pose proof (rest_S k).
    lia.
Qed.

Lemma LOv n m:
  L (pow2' n) <| R1 (1+m) -->+
  L (pow2 n) <| R2 1 m.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Lemma ROv k n:
  L k |> R2 n 0 -->*
  L ((k~1)*(pow2 (n))) <| R1 1.
Proof.
  unfold L,R1,R2.
  rw_BinaryCounter.
  es.
Qed.

Definition config '(n,m) :=
  L (pow2' n) <| R1 (1+m).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (3,1)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,m) => N.to_nat (rest (pow2 n)) >= m+1).
  2: cbn; lia.
  intros [n m] H.
  remember (2+m+n) as n'.
  remember (((2^n-1-(m+1))*2+1)*2^((m+1))-1) as m'.
  eexists (n',m').
  split.
  1:{
    unfold config.
    follow10 LOv.
    follow LIncs2.
    follow ROv.
    follow LIncs1.
    rw_rest.
    rewrite rest_add_. 2: lia.
    rewrite log2_add. 2: lia.
    rw_rest.
    replace (Npos (Pos.of_nat (m+1))) with (N.of_nat (m+1)) by lia.
    rw_rest.
    simpl_N_to_nat.
    finish.
  }
  gen H.
  rw_rest.
  simpl_N_to_nat.
  intros H.
  subst.
  replace (1+(m+1)) with (m+2) by lia.
  unfold ge.
  remember ((2^n-1-(m+1))*2+1) as v1.
  replace (2+m+n) with ((n+1)+(m+1)) by lia.
  rewrite (Nat.pow_add_r _ (n+1)).
  remember (2^(m+1)) as v2.
  assert (v1+1<=2^(n+1)). {
    rewrite (Nat.add_comm n). cbn. lia.
  }
  pose proof (Nat.mul_le_mono_r (v1+1) (2^(n+1)) v2 H0).
  pose proof (Nat.pow_nonzero 2 (m+1)).
  lia.
Qed.

End TM26.


