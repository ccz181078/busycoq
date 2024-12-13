From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Lemma lrcons_shift h1 h2 h3 n:
  lrcons h1 ([(h2,h3)]^^n) h2 =
  (h1,h2)::([(h3,h2)]^^n).
Proof.
  gen h1 h2 h3.
  induction n; intros; cbn.
  1: reflexivity.
  rewrite IHn.
  reflexivity.
Qed.

Ltac es :=
  simpl_rotate;
  repeat intro;
  unfold to_DH_config; cbn;
  execute_with_shift_rule.

Ltac side_S :=
  eapply sideRLseq_S; [es|].

Ltac side_Ss :=
  (repeat side_S);
  simpl_rotate;
  try apply sideRLseq_O.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB1RA_1RC0LF_0LA0RD_1RE---_1RB0RF_0RC0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR':DH0 := (F,[]).
Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (B,[]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [1;0;0;0]^^n *> [0;0;0;1]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hR',hL)::(hRL^^(1+n*2))) (R0 0 (1+n+m)) (R0 (1+n) m).
Proof.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (1+S n*2) with ((1+n*2)+2) by lia.
  rewrite lpow_add.
  rewrite app_comm_cons.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (1+m) 0) (R0 (1+n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold R0.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k {{{ (hR',R) }}} R0 0 (1+n).

Lemma init:
  c0 -->* S0 (3,3).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k {{{ (hL,L) }}} [1] *> r -->+
  LC0 (S k) {{{ (hR',R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (1+n) 0 = [1] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*2-1 = (1+n*2)+(1+m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncs.
    unfold hLR.
    rewrite lrcons_shift.
    rewrite H.
    rewrite lpow_add.
    rewrite app_comm_cons.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite <-Nat.add_assoc.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2+3 <= 2^k*2 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*2-(n*2+3)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA0LE_1RD---_1RB0RE_0RF0LB_0LA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR':DH0 := (F,[0]).
Definition hR:DH0 := (C,[0]).
Definition hL:DH0 := (B,[1]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;0;1]^^n *> [0;0;1;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hR',hL)::(hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  rewrite app_comm_cons.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k {{{ (hR',R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (3,4).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) {{{ (hR',R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*2-1 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncs.
    unfold hLR.
    rewrite lrcons_shift.
    rewrite H.
    rewrite lpow_add.
    rewrite app_comm_cons.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2+1 <= 2^k*2 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*2-(n*2+1)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA0LE_1RD---_1RB0RE_0RF0LB_0LA1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[1;0]).
Definition hL:DH0 := (B,[1;0]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Lemma LIncsMul2 n:
  sideRLs (flip tm) (hLR^^(2^n*4-2)) (LC0 n <* d1b) (LC1 n <* d1).
Proof.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*4-2) with ((2^n*2-1)*2) by lia.
  eapply segRLs_sideRLs_concat.
  2: apply LIncs.
  remember (2^n*2-1) as v1.
  destruct v1 as [|v1].
  1: lia.
  clear Heqv1.
  replace (S v1*2) with (2+v1*2) by lia.
  replace (S v1) with (1+v1) by lia.
  do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;1;0]^^n *> [0;1;0;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k <* d1b {{{ (hR,R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (2,4).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k <* d1 {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) <* d1b {{{ (hR,R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*4-1 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncsMul2.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*4-2) with (2^k*4-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2+1 <= 2^k*4 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*4-(n*2+1)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB0LB_1RC0LA_1LB0RD_1RE0RD_1RB1RF_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR':DH0 := (D,[0]).
Definition hR:DH0 := (D,[0]).
Definition hL:DH0 := (B,[1]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;0;1]^^n *> [0;0;1;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k {{{ (hR',R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (3,5).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) {{{ (hR',R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*2 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncs.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2 <= 2^k*2 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*2-(n*2)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA0RE_0RD0LA_0LB1RD_1RF---_1RA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[1;0]).
Definition hL:DH0 := (A,[1;0]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Lemma LIncsMul2 n:
  sideRLs (flip tm) (hLR^^(2^n*4-2)) (LC0 n <* d1b) (LC1 n <* d1).
Proof.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*4-2) with ((2^n*2-1)*2) by lia.
  eapply segRLs_sideRLs_concat.
  2: apply LIncs.
  remember (2^n*2-1) as v1.
  destruct v1 as [|v1].
  1: lia.
  clear Heqv1.
  replace (S v1*2) with (2+v1*2) by lia.
  replace (S v1) with (1+v1) by lia.
  do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;1;0]^^n *> [0;1;0;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k <* d1b {{{ (hR,R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (2,5).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k <* d1 {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) <* d1b {{{ (hR,R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*4-1 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncsMul2.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*4-2) with (2^k*4-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2+1 <= 2^k*4 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*4-(n*2+1)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA0RE_0RD0LA_0LB0RE_1RF---_1RA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[1;0]).
Definition hL:DH0 := (A,[1;0]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Lemma LIncsMul2 n:
  sideRLs (flip tm) (hLR^^(2^n*4-2)) (LC0 n <* d1b) (LC1 n <* d1).
Proof.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*4-2) with ((2^n*2-1)*2) by lia.
  eapply segRLs_sideRLs_concat.
  2: apply LIncs.
  remember (2^n*2-1) as v1.
  destruct v1 as [|v1].
  1: lia.
  clear Heqv1.
  replace (S v1*2) with (2+v1*2) by lia.
  replace (S v1) with (1+v1) by lia.
  do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;1;0]^^n *> [0;1;0;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k <* d1b {{{ (hR,R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (2,5).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k <* d1 {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) <* d1b {{{ (hR,R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*4-1 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncsMul2.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*4-2) with (2^k*4-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2+1 <= 2^k*4 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*4-(n*2+1)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA0LE_1RD0RC_1RB0RF_1LB0LB_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR':DH0 := (C,[0]).
Definition hR:DH0 := (C,[0]).
Definition hL:DH0 := (B,[1]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;0;1]^^n *> [0;0;1;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k {{{ (hR',R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (3,5).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) {{{ (hR',R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*2 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncs.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2 <= 2^k*2 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*2-(n*2)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA0LE_1RD0RC_1RB1RF_1LB0LB_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR':DH0 := (C,[0]).
Definition hR:DH0 := (C,[0]).
Definition hL:DH0 := (B,[1]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;0;1]^^n *> [0;0;1;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k {{{ (hR',R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (3,5).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) {{{ (hR',R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*2 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncs.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2 <= 2^k*2 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*2-(n*2)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB0LD_0LC0RE_1LA1RC_0RB0LA_1RF---_1RA0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[1;0]).
Definition hL:DH0 := (A,[1;0]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Lemma LIncsMul2 n:
  sideRLs (flip tm) (hLR^^(2^n*4-2)) (LC0 n <* d1b) (LC1 n <* d1).
Proof.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*4-2) with ((2^n*2-1)*2) by lia.
  eapply segRLs_sideRLs_concat.
  2: apply LIncs.
  remember (2^n*2-1) as v1.
  destruct v1 as [|v1].
  1: lia.
  clear Heqv1.
  replace (S v1*2) with (2+v1*2) by lia.
  replace (S v1) with (1+v1) by lia.
  do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;1;0]^^n *> [0;1;0;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k <* d1b {{{ (hR,R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (2,5).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k <* d1 {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) <* d1b {{{ (hR,R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*4-1 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncsMul2.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*4-2) with (2^k*4-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2+1 <= 2^k*4 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*4-(n*2+1)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA0RD_1LA0LA_1RE0RD_1RA1RF_1LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR':DH0 := (D,[0]).
Definition hR:DH0 := (D,[0]).
Definition hL:DH0 := (A,[1]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;0;1]^^n *> [0;0;1;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k {{{ (hR',R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (3,6).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) {{{ (hR',R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*2 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncs.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2 <= 2^k*2 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*2-(n*2)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC0LD_1LB0RF_0RE0LB_0LC1RE_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[1;0]).
Definition hL:DH0 := (B,[1;0]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Lemma LIncsMul2 n:
  sideRLs (flip tm) (hLR^^(2^n*4-2)) (LC0 n <* d1b) (LC1 n <* d1).
Proof.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*4-2) with ((2^n*2-1)*2) by lia.
  eapply segRLs_sideRLs_concat.
  2: apply LIncs.
  remember (2^n*2-1) as v1.
  destruct v1 as [|v1].
  1: lia.
  clear Heqv1.
  replace (S v1*2) with (2+v1*2) by lia.
  replace (S v1) with (1+v1) by lia.
  do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;1;0]^^n *> [0;1;0;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k <* d1b {{{ (hR,R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (2,6).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k <* d1 {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) <* d1b {{{ (hR,R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*4-1 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncsMul2.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*4-2) with (2^k*4-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2+1 <= 2^k*4 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*4-(n*2+1)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC0LD_1LB0RF_0RE0LB_0LC0RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[1;0]).
Definition hL:DH0 := (B,[1;0]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Lemma LIncsMul2 n:
  sideRLs (flip tm) (hLR^^(2^n*4-2)) (LC0 n <* d1b) (LC1 n <* d1).
Proof.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*4-2) with ((2^n*2-1)*2) by lia.
  eapply segRLs_sideRLs_concat.
  2: apply LIncs.
  remember (2^n*2-1) as v1.
  destruct v1 as [|v1].
  1: lia.
  clear Heqv1.
  replace (S v1*2) with (2+v1*2) by lia.
  replace (S v1) with (1+v1) by lia.
  do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;1;0]^^n *> [0;1;0;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k <* d1b {{{ (hR,R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (2,6).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k <* d1 {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) <* d1b {{{ (hR,R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*4-1 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncsMul2.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*4-2) with (2^k*4-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2+1 <= 2^k*4 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*4-(n*2+1)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC0LE_0LD0RF_1LB1RD_0RC0LB_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[1;0]).
Definition hL:DH0 := (B,[1;0]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Lemma LIncsMul2 n:
  sideRLs (flip tm) (hLR^^(2^n*4-2)) (LC0 n <* d1b) (LC1 n <* d1).
Proof.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*4-2) with ((2^n*2-1)*2) by lia.
  eapply segRLs_sideRLs_concat.
  2: apply LIncs.
  remember (2^n*2-1) as v1.
  destruct v1 as [|v1].
  1: lia.
  clear Heqv1.
  replace (S v1*2) with (2+v1*2) by lia.
  replace (S v1) with (1+v1) by lia.
  do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;1;0]^^n *> [0;1;0;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k <* d1b {{{ (hR,R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (2,6).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k <* d1 {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) <* d1b {{{ (hR,R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*4-1 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncsMul2.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*4-2) with (2^k*4-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2+1 <= 2^k*4 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*4-(n*2+1)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC0LD_1LB0RE_1LB0LB_1RA0RE_0RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR':DH0 := (E,[0]).
Definition hR:DH0 := (E,[0]).
Definition hL:DH0 := (B,[1]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;0;1]^^n *> [0;0;1;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k {{{ (hR',R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (3,6).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) {{{ (hR',R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*2 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncs.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2 <= 2^k*2 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*2-(n*2)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC0LD_1LB0RE_1LB0LB_1RA0RE_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR':DH0 := (E,[0]).
Definition hR:DH0 := (E,[0]).
Definition hL:DH0 := (B,[1]).

Definition hRL:= [(hR,hL)].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d0b := <[0;0;1;0].
Definition d1b := <[0;0;1;1].
Definition d0a := <[1;0;1;0].
Definition d1a := <[1;0;1;1].

Definition LC0 n := const 0 <* d0a <* d0b^^n.
Definition LC1 n := const 0 <* d1a <* d1^^n.

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^(2^n*2-1)) (LC0 n) (LC1 n).
Proof.
  unfold LC0,LC1.
  induction n.
  - cbn.
    side_Ss.
  - cbn[Nat.pow].
    cbn[lpow].
    repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    epose proof (Nat.pow_nonzero 2 n).
    replace (2*2^n*2-1) with (3+(2^n*2-2)*2) by lia.
    replace (2^n*2-1) with (1+(2^n*2-2)) by lia.
    generalize (2^n*2-2); intro v1.
    do 2 rewrite lpow_add.
    eapply @segRLs_trans with (w2:=d1).
    + cbn.
      eapply @segRLs_S with (w2:=d1b); execute.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: constructor.
      execute.
    + induction v1.
      1: constructor.
      cbn.
      eapply @segRLs_S' with (w2:=d1') (w3:=d0); execute.
      eapply segRLs_S.
      2: apply IHv1.
      execute.
Qed.

Definition R0 n m := [0;0;0;1]^^n *> [0;0;1;0]^^m *> const 0.

Lemma RIncs0 n m:
  sideRLs tm ((hRL^^(n*2))) (R0 0 (n+m)) (R0 (n) m).
Proof.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (S n*2) with ((n*2)+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S m)); f_equal; lia.
  unfold R0.
  side_Ss.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^n) (R0 (m) 0) (R0 (n+m) 0).
Proof.
  unfold R0.
  gen m.
  induction n; intros m.
  1: cbn; side_Ss.
  replace (hRL^^(S n)) with (hRL^^(n+1)) by (f_equal; lia).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  side_Ss.
Qed.

Definition S0 '(k,n) :=
  LC0 k {{{ (hR',R) }}} R0 0 (n).

Lemma init:
  c0 -->* S0 (3,6).
Proof.
  cbn.
  solve_init.
Qed.

Lemma LOv k r:
  LC1 k {{{ (hL,L) }}} [0] *> r -->+
  LC0 (S k) {{{ (hR',R) }}} r.
Proof.
  unfold LC1,LC0,d0b.
  es.
Qed.

Lemma Rrot n:
  R0 (n) 0 = [0] *> R0 0 n.
Proof.
  unfold R0.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep k n m:
  2^k*2 = (n*2)+(m) ->
  S0 (k,n) -->+
  S0 (S k,m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply @sideRLs_concat with (h2:=hL).
    1: eapply LIncs.
    unfold hLR.
    pose proof (Nat.pow_nonzero 2 k).
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: applys_eq (RIncs0 n 0); f_equal; lia.
    eapply RIncs1.
  - unfold S0.
    rewrite Rrot.
    follow10 LOv.
    finish.
Qed.

Definition P '(k,n) :=
  n*2 <= 2^k*2 /\ True.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  intros [k n] [HP1 _].
  eexists (_,_).
  split.
  1: apply BigStep with (m:=2^k*2-(n*2)).
  1: lia.
  repeat split.
  cbn. lia.
Qed.

End TM15.


Ltac ee :=
  es; er; finish;
  repeat f_equal;
  repeat rewrite Str_cons_def;
  repeat rewrite Str_app_assoc_1;
  cbn[app];
  reflexivity.

Ltac es' :=
  unfold sideRL; cbn; intros;
  execute_with_shift_rule'.

Module TM16.

Definition tm := Eval compute in (TM_from_str "1LB1RB_1RC0RE_0LF0RD_1RA0LD_---0RF_1LC1LB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[0;0]).
Definition hL:DH0 := (B,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (B,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1RB1RD_0LC0RE_1LB1LD_1RB0RF_1RA0RC_---0RC").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (D,[1;0]).
Definition hR':DH0 := (E,<[0;1;0]).
Definition hL':DH0 := (D,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC0RD_1LB1LA_1RE0RC_1LA1RA_---0RC").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (A,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (A,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC0RD_1LB1LA_1RE0RC_0RB1RA_---0RC").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (A,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (A,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM19.


Module TM20.

Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC0RD_1LB1LA_1RE0RC_1LB1RA_---0RC").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (A,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (A,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM20.


Module TM21.

Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC0RD_1LB1LA_1RE0RC_0LE1RA_---0RC").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (A,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (A,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM21.


Module TM22.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC0RD_1LB1LA_1RE0RC_1LA1RA_---1LB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (A,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (A,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM22.


Module TM23.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC0RD_1LB1LA_1RE0RC_0RB1RA_---1LB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (A,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (A,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM23.


Module TM24.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC0RD_1LB1LA_1RE0RC_1LB1RA_---1LB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (A,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (A,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM24.


Module TM25.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC0RD_1LB1LA_1RE0RC_1RB1RA_---1LB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (A,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (A,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM25.


Module TM26.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC0RD_1LB1LA_1RE0RC_0LE1RA_---1LB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (A,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (A,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM26.


Module TM27.

Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC0RD_1LB1LA_1RE0RC_1LB1RA_---0LD").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;0]).
Definition hL:DH0 := (A,[1;0]).
Definition hR':DH0 := (D,<[0;1;0]).
Definition hL':DH0 := (A,[1;0;1]).

Definition hRL:= [(hR',hL')].
Definition hLR:= [(hL,hR)].

Definition d0 := <[0;1;0;1;1].
Definition d1 := <[1;0;1;1;1].
Definition d1' := [1;0;1;1;1].
Definition dh0 := <[1;0;1;0;1; 1;0;1].
Definition dh1 := <[1;0;1;0;1; 1;0;1;0;1].
Definition d1b := <[1;1;0;1;1].
Definition dh := <[1;0;1;1].
Definition m0 := <[1;0;1;1;1;0;1]^^2.

Definition LC0 d m := const 0 <* dh <* dh0 <* d^^m.
Definition LC1 d n m := const 0 <* dh <* d1b^^n <* dh1 <* d^^m.

Lemma LC0_Ov n:
  sideRL tm' hL hR (LC0 d1 n) (LC1 d0 0 n).
Proof.
  unfold LC0,LC1,d0,d1,dh,dh0,dh1.
  es.
Qed.

Lemma LC1_Incs n m:
  sideRLs tm' (hLR^^(2^n*2-2)) (LC1 d0 m n) (LC1 d1 (n+m) 0).
Proof.
  gen m.
  induction n; intros m.
  1: constructor.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2*2^n*2-2) with (2*2^n-1+1+(2^n*2-2)) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S m)); f_equal; lia.
  rewrite lpow_add.
  eapply @sideRLs_trans with (r2:=LC1 d1 m (S n)).
  2: unfold LC1,d1,d0,d1b,dh1,dh; side_Ss.
  unfold LC1.
  eapply @segRLs_sideRLs_concat with (ls2:=[]).
  2: constructor.
  change (2*2^n) with (2^S n).
  eapply @BC.Incs.
  1,2: ee.
  1: ee.
Qed.

Lemma LC_Ov n r:
  LC1 d1 n 0 <* m0 {{{ (hL',L) }}} [0] *> r -->+
  LC0 d0 (1+n) <* m0 {{{ (hR',R) }}} r.
Proof.
  unfold LC0,LC1,d0.
  es.
Qed.

Lemma LC_Incs n:
  sideRLs tm' ([(hL',hR')]^^(2^n*3-2)) (LC0 d0 n <* m0) (LC1 d1 n 0 <* m0).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall' with (h1':=hL) (h2':=hR).
  1: ee.
  1: ee.
  pose proof (Nat.pow_nonzero 2 n) as Hpow.
  replace (2^n*3-2) with (2^n-1+1+(2^n*2-2)) by lia.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (LC1_Incs n 0); f_equal; lia.
  eapply sideRLs_trans.
  2: econstructor; [|constructor]; apply LC0_Ov.
  unfold LC0.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1,2: ee.
  1: ee.
  constructor.
Qed.

Definition w0 := [1;1;1;0;1;1;0].
Definition w1 := [0;1;1;1;0;1;1].

Definition R0 n m k := w1^^n *> w0^^m *> [1;1;1;1;0] *> w0^^k *> [1;1;1;0;1] *> const 0.
Definition R1 n m k := w1^^n *> [0;1;1;1;1] *> w1^^m *> w0^^k *> const 0.
Definition R2 n m := w1^^n *> [0;1;1;1;1] *> w1^^m *> [0;1;1;1;0;1] *> const 0.

Lemma RInc0 n m k:
  sideRLs tm (hRL^^m) (R0 n m k) (R0 (m+n) 0 k).
Proof.
  gen n k.
  induction m; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHm (1+n) k); f_equal; lia.
  unfold R0,w0,w1.
  side_Ss.
Qed.

Lemma ROv0 n m:
  sideRL tm hR' hL' (R0 n 0 m) (R1 n 0 (1+m)).
Proof.
  unfold R0,R1,w0,w1.
  es.
Qed.

Lemma RInc1 n m k k0:
  sideRLs tm (hRL^^k) (R1 (n) m (k*2+k0)) (R1 (n) (k*2+m) (k0)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (2+m)); f_equal; lia.
  unfold R1,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma ROv1 n m:
  sideRL tm hR' hL' (R1 n m 1) (R2 n (1+m)).
Proof.
  unfold R1,R2,w0,w1.
  es'.
Qed.

Lemma RInc2 n m k:
  sideRLs tm (hRL^^k) (R2 n m) (R2 n (k+m)).
Proof.
  gen m.
  induction k; intros.
  1: constructor.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHk (1+m)); f_equal; lia.
  unfold R2,w0,w1.
  econstructor.
  2: constructor.
  es'.
Qed.

Lemma Rrot n m:
  R2 n m = [0] *> R0 0 n m.
Proof.
  unfold R0,R2,w0,w1.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n k:
  sideRLs tm (hRL^^(8+k+n)) (R0 0 6 (n*2)) (R2 6 (1+k+n*2)).
Proof.
  replace (8+k+n) with (6+(1+(n+(1+(k+0))))) by lia.
  repeat rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RInc0.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv0.
  eapply sideRLs_trans.
  1: rewrite (Nat.add_comm 1 (n*2)).
  1: eapply RInc1.
  eapply sideRLs_trans.
  1: apply sideRL_1,ROv1.
  eapply sideRLs_trans.
  1: apply RInc2.
  applys_eq sideRLseq_O; f_equal; lia.
Qed.

Definition S0 '(k,n) := LC0 d0 k <* m0 {{{ (hR',R) }}} R0 0 6 (n*2).

Lemma init': c0 -->* S0 (4,8).
Proof.
  cbn.
  solve_init.
Qed.

Lemma BigStep k n m:
  2^k*3-1 = 8+(1+m*2)+n ->
  S0 (k,n) -->+
  S0 (S k,1+m+n).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    1: eapply LC_Incs.
    pose proof (Nat.pow_nonzero 2 k).
    replace (2^k*3-2) with (2^k*3-1-1) by lia.
    rewrite lrcons_lpow1. 2: lia.
    rewrite H.
    apply RIncs.
  - rewrite Rrot.
    unfold S0.
    applys_eq LC_Ov.
    do 2 f_equal.
    lia.
Qed.

Definition config k := S0 (k+4,2^k*16-8).
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  pose proof (Nat.pow_nonzero 2 i).
  cbn[Nat.pow].
  applys_eq (BigStep (i+4) (2^i*16-8) (2^i*16-1)).
  1: do 2 f_equal; try lia.
  rewrite Nat.pow_add_r; cbn.
  lia.
Qed.

End TM27.
