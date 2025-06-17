From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounterFull.

Open Scope list.

From BusyCoq Require Import Longitudinal.

Lemma lpow_rotate_list {A} (a0:list A) a1 b n:
  (a1::a0)^^n ++ a1::b = a1::(a0++[a1])^^n++b.
Proof.
  induction n; cbn.
  - trivial.
  - repeat rewrite <-app_assoc.
    rewrite IHn.
    trivial.
Qed.

Ltac solve_seg :=
  unfold segRL,segRR,segLL,segLR; intros; cbn;
  (eapply evstep_progress_trans || eapply evstep_trans);
  [ repeat (rewrite Str_app_assoc || cbn[Str_app]);
    simpl_tape;
    finish
  | ];
  (repeat (er; try sr)); finish;
  repeat rewrite Str_cons_def;
  repeat rewrite <-Str_app_assoc;
  cbn[app];
  reflexivity.

Ltac solve_segRLs :=
  repeat (
  (eapply segRLs_S; [solve_seg |]) ||
  (eapply segRLs_RR_LLs; [solve_seg |]) ||
  (eapply segLLs_LR_LLs; [solve_seg |]) ||
  (eapply segLLs_LL_RLs; [solve_seg |]) ||
  eapply segRLs_O ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite lpow_rotate_list ||
  cbn[app]).

Ltac solve_sideRLs :=
  repeat (eapply sideRLseq_S;
  [ intros l;
    unfold to_DH_config; cbn;
    (repeat (er; try sr)) | ] ||
  eapply sideRLseq_O).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA1LF_0RD1RC_0RE---_1RA1RE_0LF1LB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[]).
Definition hL:DH0 := (E,[]).
Definition hRL := [(hR,hL)].
Definition hLR := [(hL,hR)].

Definition C0 a b := [0;0] ++ [1;1]^^a ++ [1;0;1] ++ [1;1]^^b.
Definition C1 a b := [0;0] ++ [1;1]^^a ++ [0] ++ [1;1]^^b.

Lemma CIncs a b:
  segRLs tm' (hRL^^(a*2+1)) (hRL^^a) (C0 a b) (C1 0 (1+a+b)).
Proof.
  gen b.
  induction a; intros.
  - solve_segRLs.
  - replace (S a*2+1) with (2+(a*2+1)) by lia.
    replace (S a) with (1+a) by lia.
    rewrite (lpow_add _ 2 (a*2+1)).
    rewrite (lpow_add _ 1 a).
    eapply segRLs_trans.
    2: applys_eq (IHa (1+b)); f_equal; lia.
    unfold C0,C1.
    solve_segRLs.
Qed.

Fixpoint pow2' n:nat :=
match n with
| O => 0
| S n0 => (pow2' n0)*2+1
end.

Fixpoint RC0 n :=
match n with
| O => [0;0;0;1]*>0inf
| S n0 => C0 (pow2' n0) 0 *> RC0 n0
end.

Fixpoint RC1 n :=
match n with
| O => [0;0;0;1]*>0inf
| S n0 => C1 0 (1+(pow2' n0)) *> RC1 n0
end.

Lemma RIncs n:
  sideRLs tm' (hRL^^(pow2' n)) (RC0 n) (RC1 n).
Proof.
  induction n.
  - solve_sideRLs.
  - cbn[pow2']; cbn[RC0]; cbn[RC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (CIncs (pow2' n) 0); f_equal; lia.
Qed.

Definition LC n := 0inf <* <[1;1]^^n.

Lemma LIncs b:
  sideRLs tm (hLR^^b) (LC 0) (LC (b)).
Proof.
  induction b.
  1: solve_sideRLs.
  replace (S b) with (b+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHb.
  unfold LC.
  simpl_tape.
  solve_sideRLs.
Qed.

Definition S0 n := RC0 n {{E}}> 0inf.

Lemma RRst n r:
  RC1 n <{{F}} r -->*
  RC0 n <* [1] {{A}}> r.
Proof.
  gen r.
  induction n; intros; cbn.
  1: es.
  es; er; follow IHn; es.
Qed.


Lemma BigStep n:
  S0 n -->+
  S0 (S n).
Proof.
  unfold S0.
  epose proof (LIncs (1+pow2' n)) as HL.
  unfold hLR in HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+pow2' n-1) with (pow2' n) in HL by lia.
  epose proof (sideRLs_concat (RIncs n) HL) as H.
  unfold LC in H.
  cbn in H.
  follow10 H.
  follow RRst.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: es.
  eapply progress_nonhalt_simple.
  intros i; eexists; apply BigStep.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0RD_0LB1LC_1RA1LB_0RE1RD_0RF---_1RA1RF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[]).
Definition hL:DH0 := (F,[]).
Definition hRL := [(hR,hL)].
Definition hLR := [(hL,hR)].

Definition C0 a b := [0;0] ++ [1;1]^^a ++ [1;0;1] ++ [1;1]^^b.
Definition C1 a b := [0;0] ++ [1;1]^^a ++ [0] ++ [1;1]^^b.

Lemma CIncs a b:
  segRLs tm' (hRL^^(a*2+1)) (hRL^^a) (C0 a b) (C1 0 (1+a+b)).
Proof.
  gen b.
  induction a; intros.
  - solve_segRLs.
  - replace (S a*2+1) with (2+(a*2+1)) by lia.
    replace (S a) with (1+a) by lia.
    rewrite (lpow_add _ 2 (a*2+1)).
    rewrite (lpow_add _ 1 a).
    eapply segRLs_trans.
    2: applys_eq (IHa (1+b)); f_equal; lia.
    unfold C0,C1.
    solve_segRLs.
Qed.

Fixpoint pow2' n:nat :=
match n with
| O => 0
| S n0 => (pow2' n0)*2+1
end.

Fixpoint RC0 n :=
match n with
| O => [0;0;0;1]*>0inf
| S n0 => C0 (pow2' n0) 0 *> RC0 n0
end.

Fixpoint RC1 n :=
match n with
| O => [0;0;0;1]*>0inf
| S n0 => C1 0 (1+(pow2' n0)) *> RC1 n0
end.

Lemma RIncs n:
  sideRLs tm' (hRL^^(pow2' n)) (RC0 n) (RC1 n).
Proof.
  induction n.
  - solve_sideRLs.
  - cbn[pow2']; cbn[RC0]; cbn[RC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (CIncs (pow2' n) 0); f_equal; lia.
Qed.

Definition LC n := 0inf <* <[1;1]^^n.

Lemma LIncs b:
  sideRLs tm (hLR^^b) (LC 0) (LC (b)).
Proof.
  induction b.
  1: solve_sideRLs.
  replace (S b) with (b+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHb.
  unfold LC.
  simpl_tape.
  solve_sideRLs.
Qed.

Definition S0 n := RC0 n {{F}}> 0inf.

Lemma RRst n r:
  RC1 n <{{B}} r -->*
  RC0 n <* [1] {{A}}> r.
Proof.
  gen r.
  induction n; intros; cbn.
  1: es.
  es; er; follow IHn; es.
Qed.


Lemma BigStep n:
  S0 n -->+
  S0 (S n).
Proof.
  unfold S0.
  epose proof (LIncs (1+pow2' n)) as HL.
  unfold hLR in HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+pow2' n-1) with (pow2' n) in HL by lia.
  epose proof (sideRLs_concat (RIncs n) HL) as H.
  unfold LC in H.
  cbn in H.
  follow10 H.
  follow RRst.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: es.
  eapply progress_nonhalt_simple.
  intros i; eexists; apply BigStep.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC---_0LC1LD_1RA1LC_0RF1RE_1RA1RF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (F,[]).
Definition hRL := [(hR,hL)].
Definition hLR := [(hL,hR)].

Definition C0 a b := [0] ++ [1;1]^^a ++ [1;0;1] ++ [1;1]^^b.
Definition C1 a b := [0] ++ [1;1]^^a ++ [0] ++ [1;1]^^b.

Lemma CIncs a b:
  segRLs tm' (hRL^^(a*2+1)) (hRL^^a) (C0 a b) (C1 0 (1+a+b)).
Proof.
  gen b.
  induction a; intros.
  - solve_segRLs.
  - replace (S a*2+1) with (2+(a*2+1)) by lia.
    replace (S a) with (1+a) by lia.
    rewrite (lpow_add _ 2 (a*2+1)).
    rewrite (lpow_add _ 1 a).
    eapply segRLs_trans.
    2: applys_eq (IHa (1+b)); f_equal; lia.
    unfold C0,C1.
    solve_segRLs.
Qed.

Fixpoint pow2' n:nat :=
match n with
| O => 0
| S n0 => (pow2' n0)*2+1
end.

Fixpoint RC0 n :=
match n with
| O => [0;0;1]*>0inf
| S n0 => C0 (pow2' n0) 0 *> RC0 n0
end.

Fixpoint RC1 n :=
match n with
| O => [0;0;1]*>0inf
| S n0 => C1 0 (1+(pow2' n0)) *> RC1 n0
end.

Lemma RIncs n:
  sideRLs tm' (hRL^^(pow2' n)) (RC0 n) (RC1 n).
Proof.
  induction n.
  - solve_sideRLs.
  - cbn[pow2']; cbn[RC0]; cbn[RC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (CIncs (pow2' n) 0); f_equal; lia.
Qed.

Definition LC n := 0inf <* <[1;1]^^n.

Lemma LIncs b:
  sideRLs tm (hLR^^b) (LC 0) (LC (b)).
Proof.
  induction b.
  1: solve_sideRLs.
  replace (S b) with (b+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHb.
  unfold LC.
  simpl_tape.
  solve_sideRLs.
Qed.

Definition S0 n := RC0 n {{F}}> 0inf.

Lemma RRst n r:
  RC1 n <{{C}} r -->*
  RC0 n <* [1] {{A}}> r.
Proof.
  gen r.
  induction n; intros; cbn.
  1: es.
  es; er; follow IHn; es.
Qed.


Lemma BigStep n:
  S0 n -->+
  S0 (S n).
Proof.
  unfold S0.
  epose proof (LIncs (1+pow2' n)) as HL.
  unfold hLR in HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+pow2' n-1) with (pow2' n) in HL by lia.
  epose proof (sideRLs_concat (RIncs n) HL) as H.
  unfold LC in H.
  cbn in H.
  follow10 H.
  follow RRst.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: es.
  eapply progress_nonhalt_simple.
  intros i; eexists; apply BigStep.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0LC---_0LC1LD_1RA1LC_0RF1RE_1RA1RF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (F,[]).
Definition hRL := [(hR,hL)].
Definition hLR := [(hL,hR)].

Definition C0 a b := [0] ++ [1;1]^^a ++ [1;0;1] ++ [1;1]^^b.
Definition C1 a b := [0] ++ [1;1]^^a ++ [0] ++ [1;1]^^b.

Lemma CIncs a b:
  segRLs tm' (hRL^^(a*2+1)) (hRL^^a) (C0 a b) (C1 0 (1+a+b)).
Proof.
  gen b.
  induction a; intros.
  - solve_segRLs.
  - replace (S a*2+1) with (2+(a*2+1)) by lia.
    replace (S a) with (1+a) by lia.
    rewrite (lpow_add _ 2 (a*2+1)).
    rewrite (lpow_add _ 1 a).
    eapply segRLs_trans.
    2: applys_eq (IHa (1+b)); f_equal; lia.
    unfold C0,C1.
    solve_segRLs.
Qed.

Fixpoint pow2' n:nat :=
match n with
| O => 0
| S n0 => (pow2' n0)*2+1
end.

Fixpoint RC0 n :=
match n with
| O => [0;0;1]*>0inf
| S n0 => C0 (pow2' n0) 0 *> RC0 n0
end.

Fixpoint RC1 n :=
match n with
| O => [0;0;1]*>0inf
| S n0 => C1 0 (1+(pow2' n0)) *> RC1 n0
end.

Lemma RIncs n:
  sideRLs tm' (hRL^^(pow2' n)) (RC0 n) (RC1 n).
Proof.
  induction n.
  - solve_sideRLs.
  - cbn[pow2']; cbn[RC0]; cbn[RC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (CIncs (pow2' n) 0); f_equal; lia.
Qed.

Definition LC n := 0inf <* <[1;1]^^n.

Lemma LIncs b:
  sideRLs tm (hLR^^b) (LC 0) (LC (b)).
Proof.
  induction b.
  1: solve_sideRLs.
  replace (S b) with (b+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHb.
  unfold LC.
  simpl_tape.
  solve_sideRLs.
Qed.

Definition S0 n := RC0 n {{F}}> 0inf.

Lemma RRst n r:
  RC1 n <{{C}} r -->*
  RC0 n <* [1] {{A}}> r.
Proof.
  gen r.
  induction n; intros; cbn.
  1: es.
  es; er; follow IHn; es.
Qed.


Lemma BigStep n:
  S0 n -->+
  S0 (S n).
Proof.
  unfold S0.
  epose proof (LIncs (1+pow2' n)) as HL.
  unfold hLR in HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+pow2' n-1) with (pow2' n) in HL by lia.
  epose proof (sideRLs_concat (RIncs n) HL) as H.
  unfold LC in H.
  cbn in H.
  follow10 H.
  follow RRst.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: es.
  eapply progress_nonhalt_simple.
  intros i; eexists; apply BigStep.
Qed.

End TM4.


