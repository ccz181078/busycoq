From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import SimplTape.

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

Definition tm := Eval compute in (TM_from_str "1RB0LB_0LC---_1RD1LC_0RF0LE_0LC1LE_0RA0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Definition hR:DH0 := (E,[0;0]).
Definition hL:DH0 := (E,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Definition LS '(a,b) :=
  [0] ++ [1]^^(a) ++ [0] ++ [1]^^(1+b).

Ltac flia := repeat (lia || f_equal).

Lemma LIncs a b:
  segRLs tm (hRL^^a) (hRL^^a) (LS (a,b)) (LS (O,a+b)).
Proof.
  gen b.
  induction a; intros.
  1: solve_segRLs.
  change (S a) with (1+a).
  rewrite lpow_add.
  specialize (IHa (1+b)).
  eapply segRLs_trans.
  2: applys_eq IHa; flia.
  solve_segRLs.
Qed.

Fixpoint LC0 n :=
match n with
| O => 0inf
| S n0 => LC0 n0 <* [0;0] <* [1]^^n
end.

Definition LC n := LC0 n <* [0;0].

Lemma LC_Incs n:
  sideRLs tm (hRL^^(1+n)) (LC n) (LC (1+n)).
Proof.
  induction n.
  - cbn.
    simpl_tape.
    solve_sideRLs.
  - rewrite lpow_add.
    eapply @sideRLs_trans with (r2:=LC n <* LS (S n,O)).
    + unfold LS,LC.
      simpl_tape.
      solve_sideRLs.
    + change (LC (1+S n)) with (LC (S n) <* LS (O,S n)).
      eapply segRLs_sideRLs_concat.
      2: apply IHn.
      applys_eq (LIncs (S n) O); flia.
Qed.

Definition RC n := [1]^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  induction n; intros.
  1: solve_sideRLs.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RC.
  solve_sideRLs.
  applys_eq sideRLseq_O.
  simpl_tape; simpl_rotate; trivial.
Qed.

Definition S0 '(m,n) := RC m {{{ (hR,R) }}} LC n.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0(1,1)%nat).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [m n].
  eexists (1+n+m,S n).
  cbn.
  epose proof (LC_Incs n) as HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+n-1) with n in HL by lia.
  epose proof (sideRLs_concat (RC_Incs _ m) HL).
  follow10 H.
  es.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0LE_0LC---_1RD1LC_0RF0LE_0LC1LE_0RA0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Definition hR:DH0 := (E,[0;0]).
Definition hL:DH0 := (E,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Definition LS '(a,b) :=
  [0] ++ [1]^^(a) ++ [0] ++ [1]^^(1+b).

Ltac flia := repeat (lia || f_equal).

Lemma LIncs a b:
  segRLs tm (hRL^^a) (hRL^^a) (LS (a,b)) (LS (O,a+b)).
Proof.
  gen b.
  induction a; intros.
  1: solve_segRLs.
  change (S a) with (1+a).
  rewrite lpow_add.
  specialize (IHa (1+b)).
  eapply segRLs_trans.
  2: applys_eq IHa; flia.
  solve_segRLs.
Qed.

Fixpoint LC0 n :=
match n with
| O => 0inf
| S n0 => LC0 n0 <* [0;0] <* [1]^^n
end.

Definition LC n := LC0 n <* [0;0].

Lemma LC_Incs n:
  sideRLs tm (hRL^^(1+n)) (LC n) (LC (1+n)).
Proof.
  induction n.
  - cbn.
    simpl_tape.
    solve_sideRLs.
  - rewrite lpow_add.
    eapply @sideRLs_trans with (r2:=LC n <* LS (S n,O)).
    + unfold LS,LC.
      simpl_tape.
      solve_sideRLs.
    + change (LC (1+S n)) with (LC (S n) <* LS (O,S n)).
      eapply segRLs_sideRLs_concat.
      2: apply IHn.
      applys_eq (LIncs (S n) O); flia.
Qed.

Definition RC n := [1]^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  induction n; intros.
  1: solve_sideRLs.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RC.
  solve_sideRLs.
  applys_eq sideRLseq_O.
  simpl_tape; simpl_rotate; trivial.
Qed.

Definition S0 '(m,n) := RC m {{{ (hR,R) }}} LC n.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0(1,1)%nat).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [m n].
  eexists (1+n+m,S n).
  cbn.
  epose proof (LC_Incs n) as HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+n-1) with n in HL by lia.
  epose proof (sideRLs_concat (RC_Incs _ m) HL).
  follow10 H.
  es.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC0LF_0RD0RF_1RE0LE_0LA---_0LA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Definition hR:DH0 := (F,[0;0]).
Definition hL:DH0 := (F,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Definition LS '(a,b) :=
  [0] ++ [1]^^(a) ++ [0] ++ [1]^^(1+b).

Ltac flia := repeat (lia || f_equal).

Lemma LIncs a b:
  segRLs tm (hRL^^a) (hRL^^a) (LS (a,b)) (LS (O,a+b)).
Proof.
  gen b.
  induction a; intros.
  1: solve_segRLs.
  change (S a) with (1+a).
  rewrite lpow_add.
  specialize (IHa (1+b)).
  eapply segRLs_trans.
  2: applys_eq IHa; flia.
  solve_segRLs.
Qed.

Fixpoint LC0 n :=
match n with
| O => 0inf
| S n0 => LC0 n0 <* [0;0] <* [1]^^n
end.

Definition LC n := LC0 n <* [0;0].

Lemma LC_Incs n:
  sideRLs tm (hRL^^(1+n)) (LC n) (LC (1+n)).
Proof.
  induction n.
  - cbn.
    simpl_tape.
    solve_sideRLs.
  - rewrite lpow_add.
    eapply @sideRLs_trans with (r2:=LC n <* LS (S n,O)).
    + unfold LS,LC.
      simpl_tape.
      solve_sideRLs.
    + change (LC (1+S n)) with (LC (S n) <* LS (O,S n)).
      eapply segRLs_sideRLs_concat.
      2: apply IHn.
      applys_eq (LIncs (S n) O); flia.
Qed.

Definition RC n := [1]^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  induction n; intros.
  1: solve_sideRLs.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RC.
  solve_sideRLs.
  applys_eq sideRLseq_O.
  simpl_tape; simpl_rotate; trivial.
Qed.

Definition S0 '(m,n) := RC m {{{ (hR,R) }}} LC n.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0(0,1)%nat).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [m n].
  eexists (1+n+m,S n).
  cbn.
  epose proof (LC_Incs n) as HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+n-1) with n in HL by lia.
  epose proof (sideRLs_concat (RC_Incs _ m) HL).
  follow10 H.
  es.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC0LF_0RD0RF_1RE0LF_0LA---_0LA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Definition hR:DH0 := (F,[0;0]).
Definition hL:DH0 := (F,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Definition LS '(a,b) :=
  [0] ++ [1]^^(a) ++ [0] ++ [1]^^(1+b).

Ltac flia := repeat (lia || f_equal).

Lemma LIncs a b:
  segRLs tm (hRL^^a) (hRL^^a) (LS (a,b)) (LS (O,a+b)).
Proof.
  gen b.
  induction a; intros.
  1: solve_segRLs.
  change (S a) with (1+a).
  rewrite lpow_add.
  specialize (IHa (1+b)).
  eapply segRLs_trans.
  2: applys_eq IHa; flia.
  solve_segRLs.
Qed.

Fixpoint LC0 n :=
match n with
| O => 0inf
| S n0 => LC0 n0 <* [0;0] <* [1]^^n
end.

Definition LC n := LC0 n <* [0;0].

Lemma LC_Incs n:
  sideRLs tm (hRL^^(1+n)) (LC n) (LC (1+n)).
Proof.
  induction n.
  - cbn.
    simpl_tape.
    solve_sideRLs.
  - rewrite lpow_add.
    eapply @sideRLs_trans with (r2:=LC n <* LS (S n,O)).
    + unfold LS,LC.
      simpl_tape.
      solve_sideRLs.
    + change (LC (1+S n)) with (LC (S n) <* LS (O,S n)).
      eapply segRLs_sideRLs_concat.
      2: apply IHn.
      applys_eq (LIncs (S n) O); flia.
Qed.

Definition RC n := [1]^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  induction n; intros.
  1: solve_sideRLs.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RC.
  solve_sideRLs.
  applys_eq sideRLseq_O.
  simpl_tape; simpl_rotate; trivial.
Qed.

Definition S0 '(m,n) := RC m {{{ (hR,R) }}} LC n.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0(0,1)%nat).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [m n].
  eexists (1+n+m,S n).
  cbn.
  epose proof (LC_Incs n) as HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+n-1) with n in HL by lia.
  epose proof (sideRLs_concat (RC_Incs _ m) HL).
  follow10 H.
  es.
Qed.

End TM4.



