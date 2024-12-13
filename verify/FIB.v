From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

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

Ltac ee' :=
  es; er; finish;
  repeat f_equal;
  repeat rewrite Str_cons_def;
  repeat rewrite Str_app_assoc_1;
  cbn[app];
  repeat rewrite <-Str_app_assoc;
  try reflexivity.


Ltac flia := repeat (try lia; f_equal).

Lemma lpow_rotate_list{A} (a:A) b c n:
  (a::b)^^n ++ a::c =
  a:: (b++[a])^^n ++ c.
Proof.
  induction n.
  1: reflexivity.
  cbn.
  repeat rewrite <-app_assoc.
  rewrite IHn.
  reflexivity.
Qed.

Ltac simpl_rotate_list :=
  repeat (
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite lpow_rotate_list ||
  rewrite app_nil_r ||
  cbn ||
  reflexivity).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC0RF_1LD1LC_1LE0LE_0RA0LC_---0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[]).
Definition hL:DH0 := (C,[]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0] ++ [1;1;0]^^n.
Definition B1 n := [0] ++ [1;1;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^n) (hRL^^n) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;1] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [1;1;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Definition R1 n := B0 n *> const 0.

Definition P1 n :=
  sideRLs tm (hRL^^n) (const 0) (R1 n).

Definition P2 n :=
  sideRLs tm (hRL^^(n+1)) (R1 n) (R1 (n*2+1)).

Lemma P1_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P1 (m*2+1).
Proof.
  unfold P0,P1,P2,R1.
  replace (m*2+1) with (m+(m+1)) by lia.
  intros HP0 HP1 HP2.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  1: apply HP2.
Qed.

Lemma P2_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P2 (m*2+1).
Proof.
  intros HP0 HP1 HP2.
  pose proof (P0_S m HP0) as HP0'.
  pose proof (P1_S m HP0 HP1 HP2) as HP1'.
  gen HP0 HP1 HP2 HP0' HP1'.
  unfold P0,P1,P2,R1.
  intros HP0 HP1 HP2 HP0' HP1'.
  rewrite lpow_add.
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat.
    1: apply HP0'.
    1: apply HP1'.
  - replace ((m*2+1)*2+1) with (m*2+m*2+3) by lia.
    simpl_tape.
    side_Ss.
Qed.

Lemma Pall i:
  P0 (2^i-1) /\
  P1 (2^i-1) /\
  P2 (2^i-1).
Proof.
  induction i.
  - repeat split.
    + constructor.
    + unfold P1,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
    + unfold P2,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
  - destruct IHi as [HP0 [HP1 HP2]].
    pose proof (Nat.pow_nonzero 2 i) as Hpow.
    replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
    remember (2^i-1) as m.
    repeat split.
    + apply P0_S; auto.
    + apply P1_S; auto.
    + apply P2_S; auto.
Qed.

Definition L n := const 0 <* [1]^^n.
Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L n) (L (m*2+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*2) with (m*2+2) by lia.
  unfold L.
  simpl_tape.
  side_Ss.
Qed.

Definition config '(n,i) := L n {{{ (hR,R) }}} R1 (2^i-1).

Lemma BigStep n i:
  config (n,i) -->+
  config (2^i*2+n,S i).
Proof.
  epose proof (Pall i) as [HP0 [HP1 HP2]].
  unfold P2 in HP2.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  unfold hRL in HP2.
  rewrite <-lrcons_lpow1 in HP2.
  2: lia.
  unfold config.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HP2.
    apply LIncs.
  - cbn[Nat.pow].
    replace ((2^i-1)*2+1) with (2*2^i-1) by lia.
    remember ((2^i-1+1-1)*2+n) as v1.
    replace (2^i*2+n) with (2+v1) by lia.
    unfold L.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (14,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n i].
  eexists (_,_).
  apply BigStep.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB1LA_1LC0LC_0RD0LA_1RE1RD_0RA0RF_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[]).
Definition hL:DH0 := (A,[]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0] ++ [1;1;0]^^n.
Definition B1 n := [0] ++ [1;1;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^n) (hRL^^n) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;1] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [1;1;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Definition R1 n := B0 n *> const 0.

Definition P1 n :=
  sideRLs tm (hRL^^n) (const 0) (R1 n).

Definition P2 n :=
  sideRLs tm (hRL^^(n+1)) (R1 n) (R1 (n*2+1)).

Lemma P1_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P1 (m*2+1).
Proof.
  unfold P0,P1,P2,R1.
  replace (m*2+1) with (m+(m+1)) by lia.
  intros HP0 HP1 HP2.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  1: apply HP2.
Qed.

Lemma P2_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P2 (m*2+1).
Proof.
  intros HP0 HP1 HP2.
  pose proof (P0_S m HP0) as HP0'.
  pose proof (P1_S m HP0 HP1 HP2) as HP1'.
  gen HP0 HP1 HP2 HP0' HP1'.
  unfold P0,P1,P2,R1.
  intros HP0 HP1 HP2 HP0' HP1'.
  rewrite lpow_add.
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat.
    1: apply HP0'.
    1: apply HP1'.
  - replace ((m*2+1)*2+1) with (m*2+m*2+3) by lia.
    simpl_tape.
    side_Ss.
Qed.

Lemma Pall i:
  P0 (2^i-1) /\
  P1 (2^i-1) /\
  P2 (2^i-1).
Proof.
  induction i.
  - repeat split.
    + constructor.
    + unfold P1,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
    + unfold P2,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
  - destruct IHi as [HP0 [HP1 HP2]].
    pose proof (Nat.pow_nonzero 2 i) as Hpow.
    replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
    remember (2^i-1) as m.
    repeat split.
    + apply P0_S; auto.
    + apply P1_S; auto.
    + apply P2_S; auto.
Qed.

Definition L n := const 0 <* [1]^^n.
Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L n) (L (m*2+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*2) with (m*2+2) by lia.
  unfold L.
  simpl_tape.
  side_Ss.
Qed.

Definition config '(n,i) := L n {{{ (hR,R) }}} R1 (2^i-1).

Lemma BigStep n i:
  config (n,i) -->+
  config (2^i*2+n,S i).
Proof.
  epose proof (Pall i) as [HP0 [HP1 HP2]].
  unfold P2 in HP2.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  unfold hRL in HP2.
  rewrite <-lrcons_lpow1 in HP2.
  2: lia.
  unfold config.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HP2.
    apply LIncs.
  - cbn[Nat.pow].
    replace ((2^i-1)*2+1) with (2*2^i-1) by lia.
    remember ((2^i-1+1-1)*2+n) as v1.
    replace (2^i*2+n) with (2+v1) by lia.
    unfold L.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (16,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n i].
  eexists (_,_).
  apply BigStep.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0LB_0RC0LE_1RD1RC_0RE0RF_1LA1LE_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (E,[]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0] ++ [1;1;0]^^n.
Definition B1 n := [0] ++ [1;1;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^n) (hRL^^n) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;1] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [1;1;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Definition R1 n := B0 n *> const 0.

Definition P1 n :=
  sideRLs tm (hRL^^n) (const 0) (R1 n).

Definition P2 n :=
  sideRLs tm (hRL^^(n+1)) (R1 n) (R1 (n*2+1)).

Lemma P1_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P1 (m*2+1).
Proof.
  unfold P0,P1,P2,R1.
  replace (m*2+1) with (m+(m+1)) by lia.
  intros HP0 HP1 HP2.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  1: apply HP2.
Qed.

Lemma P2_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P2 (m*2+1).
Proof.
  intros HP0 HP1 HP2.
  pose proof (P0_S m HP0) as HP0'.
  pose proof (P1_S m HP0 HP1 HP2) as HP1'.
  gen HP0 HP1 HP2 HP0' HP1'.
  unfold P0,P1,P2,R1.
  intros HP0 HP1 HP2 HP0' HP1'.
  rewrite lpow_add.
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat.
    1: apply HP0'.
    1: apply HP1'.
  - replace ((m*2+1)*2+1) with (m*2+m*2+3) by lia.
    simpl_tape.
    side_Ss.
Qed.

Lemma Pall i:
  P0 (2^i-1) /\
  P1 (2^i-1) /\
  P2 (2^i-1).
Proof.
  induction i.
  - repeat split.
    + constructor.
    + unfold P1,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
    + unfold P2,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
  - destruct IHi as [HP0 [HP1 HP2]].
    pose proof (Nat.pow_nonzero 2 i) as Hpow.
    replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
    remember (2^i-1) as m.
    repeat split.
    + apply P0_S; auto.
    + apply P1_S; auto.
    + apply P2_S; auto.
Qed.

Definition L n := const 0 <* [1]^^n.
Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L n) (L (m*2+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*2) with (m*2+2) by lia.
  unfold L.
  simpl_tape.
  side_Ss.
Qed.

Definition config '(n,i) := L n {{{ (hR,R) }}} R1 (2^i-1).

Lemma BigStep n i:
  config (n,i) -->+
  config (2^i*2+n,S i).
Proof.
  epose proof (Pall i) as [HP0 [HP1 HP2]].
  unfold P2 in HP2.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  unfold hRL in HP2.
  rewrite <-lrcons_lpow1 in HP2.
  2: lia.
  unfold config.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HP2.
    apply LIncs.
  - cbn[Nat.pow].
    replace ((2^i-1)*2+1) with (2*2^i-1) by lia.
    remember ((2^i-1+1-1)*2+n) as v1.
    replace (2^i*2+n) with (2+v1) by lia.
    unfold L.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (15,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n i].
  eexists (_,_).
  apply BigStep.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB1RD_0RC0LE_1RD1RC_0RE0RF_1LA1LE_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (E,[]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0] ++ [1;1;0]^^n.
Definition B1 n := [0] ++ [1;1;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^n) (hRL^^n) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;1] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [1;1;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Definition R1 n := B0 n *> const 0.

Definition P1 n :=
  sideRLs tm (hRL^^n) (const 0) (R1 n).

Definition P2 n :=
  sideRLs tm (hRL^^(n+1)) (R1 n) (R1 (n*2+1)).

Lemma P1_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P1 (m*2+1).
Proof.
  unfold P0,P1,P2,R1.
  replace (m*2+1) with (m+(m+1)) by lia.
  intros HP0 HP1 HP2.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  1: apply HP2.
Qed.

Lemma P2_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P2 (m*2+1).
Proof.
  intros HP0 HP1 HP2.
  pose proof (P0_S m HP0) as HP0'.
  pose proof (P1_S m HP0 HP1 HP2) as HP1'.
  gen HP0 HP1 HP2 HP0' HP1'.
  unfold P0,P1,P2,R1.
  intros HP0 HP1 HP2 HP0' HP1'.
  rewrite lpow_add.
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat.
    1: apply HP0'.
    1: apply HP1'.
  - replace ((m*2+1)*2+1) with (m*2+m*2+3) by lia.
    simpl_tape.
    side_Ss.
Qed.

Lemma Pall i:
  P0 (2^i-1) /\
  P1 (2^i-1) /\
  P2 (2^i-1).
Proof.
  induction i.
  - repeat split.
    + constructor.
    + unfold P1,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
    + unfold P2,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
  - destruct IHi as [HP0 [HP1 HP2]].
    pose proof (Nat.pow_nonzero 2 i) as Hpow.
    replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
    remember (2^i-1) as m.
    repeat split.
    + apply P0_S; auto.
    + apply P1_S; auto.
    + apply P2_S; auto.
Qed.

Definition L n := const 0 <* [1]^^n.
Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L n) (L (m*2+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*2) with (m*2+2) by lia.
  unfold L.
  simpl_tape.
  side_Ss.
Qed.

Definition config '(n,i) := L n {{{ (hR,R) }}} R1 (2^i-1).

Lemma BigStep n i:
  config (n,i) -->+
  config (2^i*2+n,S i).
Proof.
  epose proof (Pall i) as [HP0 [HP1 HP2]].
  unfold P2 in HP2.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  unfold hRL in HP2.
  rewrite <-lrcons_lpow1 in HP2.
  2: lia.
  unfold config.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HP2.
    apply LIncs.
  - cbn[Nat.pow].
    replace ((2^i-1)*2+1) with (2*2^i-1) by lia.
    remember ((2^i-1+1-1)*2+n) as v1.
    replace (2^i*2+n) with (2+v1) by lia.
    unfold L.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (15,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n i].
  eexists (_,_).
  apply BigStep.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC0RF_1LD1LC_1LE1RB_0RA0LC_---0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[]).
Definition hL:DH0 := (C,[]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0] ++ [1;1;0]^^n.
Definition B1 n := [0] ++ [1;1;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^n) (hRL^^n) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;1] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [1;1;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Definition R1 n := B0 n *> const 0.

Definition P1 n :=
  sideRLs tm (hRL^^n) (const 0) (R1 n).

Definition P2 n :=
  sideRLs tm (hRL^^(n+1)) (R1 n) (R1 (n*2+1)).

Lemma P1_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P1 (m*2+1).
Proof.
  unfold P0,P1,P2,R1.
  replace (m*2+1) with (m+(m+1)) by lia.
  intros HP0 HP1 HP2.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  1: apply HP2.
Qed.

Lemma P2_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P2 (m*2+1).
Proof.
  intros HP0 HP1 HP2.
  pose proof (P0_S m HP0) as HP0'.
  pose proof (P1_S m HP0 HP1 HP2) as HP1'.
  gen HP0 HP1 HP2 HP0' HP1'.
  unfold P0,P1,P2,R1.
  intros HP0 HP1 HP2 HP0' HP1'.
  rewrite lpow_add.
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat.
    1: apply HP0'.
    1: apply HP1'.
  - replace ((m*2+1)*2+1) with (m*2+m*2+3) by lia.
    simpl_tape.
    side_Ss.
Qed.

Lemma Pall i:
  P0 (2^i-1) /\
  P1 (2^i-1) /\
  P2 (2^i-1).
Proof.
  induction i.
  - repeat split.
    + constructor.
    + unfold P1,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
    + unfold P2,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
  - destruct IHi as [HP0 [HP1 HP2]].
    pose proof (Nat.pow_nonzero 2 i) as Hpow.
    replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
    remember (2^i-1) as m.
    repeat split.
    + apply P0_S; auto.
    + apply P1_S; auto.
    + apply P2_S; auto.
Qed.

Definition L n := const 0 <* [1]^^n.
Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L n) (L (m*2+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*2) with (m*2+2) by lia.
  unfold L.
  simpl_tape.
  side_Ss.
Qed.

Definition config '(n,i) := L n {{{ (hR,R) }}} R1 (2^i-1).

Lemma BigStep n i:
  config (n,i) -->+
  config (2^i*2+n,S i).
Proof.
  epose proof (Pall i) as [HP0 [HP1 HP2]].
  unfold P2 in HP2.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  unfold hRL in HP2.
  rewrite <-lrcons_lpow1 in HP2.
  2: lia.
  unfold config.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HP2.
    apply LIncs.
  - cbn[Nat.pow].
    replace ((2^i-1)*2+1) with (2*2^i-1) by lia.
    remember ((2^i-1+1-1)*2+n) as v1.
    replace (2^i*2+n) with (2+v1) by lia.
    unfold L.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (14,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n i].
  eexists (_,_).
  apply BigStep.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB1LA_1LC1RE_0RD0LA_1RE1RD_0RA0RF_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[]).
Definition hL:DH0 := (A,[]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0] ++ [1;1;0]^^n.
Definition B1 n := [0] ++ [1;1;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^n) (hRL^^n) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;1] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [1;1;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Definition R1 n := B0 n *> const 0.

Definition P1 n :=
  sideRLs tm (hRL^^n) (const 0) (R1 n).

Definition P2 n :=
  sideRLs tm (hRL^^(n+1)) (R1 n) (R1 (n*2+1)).

Lemma P1_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P1 (m*2+1).
Proof.
  unfold P0,P1,P2,R1.
  replace (m*2+1) with (m+(m+1)) by lia.
  intros HP0 HP1 HP2.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  1: apply HP2.
Qed.

Lemma P2_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P2 (m*2+1).
Proof.
  intros HP0 HP1 HP2.
  pose proof (P0_S m HP0) as HP0'.
  pose proof (P1_S m HP0 HP1 HP2) as HP1'.
  gen HP0 HP1 HP2 HP0' HP1'.
  unfold P0,P1,P2,R1.
  intros HP0 HP1 HP2 HP0' HP1'.
  rewrite lpow_add.
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat.
    1: apply HP0'.
    1: apply HP1'.
  - replace ((m*2+1)*2+1) with (m*2+m*2+3) by lia.
    simpl_tape.
    side_Ss.
Qed.

Lemma Pall i:
  P0 (2^i-1) /\
  P1 (2^i-1) /\
  P2 (2^i-1).
Proof.
  induction i.
  - repeat split.
    + constructor.
    + unfold P1,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
    + unfold P2,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
  - destruct IHi as [HP0 [HP1 HP2]].
    pose proof (Nat.pow_nonzero 2 i) as Hpow.
    replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
    remember (2^i-1) as m.
    repeat split.
    + apply P0_S; auto.
    + apply P1_S; auto.
    + apply P2_S; auto.
Qed.

Definition L n := const 0 <* [1]^^n.
Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L n) (L (m*2+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*2) with (m*2+2) by lia.
  unfold L.
  simpl_tape.
  side_Ss.
Qed.

Definition config '(n,i) := L n {{{ (hR,R) }}} R1 (2^i-1).

Lemma BigStep n i:
  config (n,i) -->+
  config (2^i*2+n,S i).
Proof.
  epose proof (Pall i) as [HP0 [HP1 HP2]].
  unfold P2 in HP2.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  unfold hRL in HP2.
  rewrite <-lrcons_lpow1 in HP2.
  2: lia.
  unfold config.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HP2.
    apply LIncs.
  - cbn[Nat.pow].
    replace ((2^i-1)*2+1) with (2*2^i-1) by lia.
    remember ((2^i-1+1-1)*2+n) as v1.
    replace (2^i*2+n) with (2+v1) by lia.
    unfold L.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (16,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n i].
  eexists (_,_).
  apply BigStep.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB0RD_0LC---_0LD1LC_1LE0LE_1LF1RA_0RE1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[1;1]).
Definition hL:DH0 := (C,[1;1]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0] ++ [1;1;0]^^n.
Definition B1 n := [0] ++ [1;1;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^n) (hRL^^n) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;1] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [1;1;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Definition R1 n := B0 n *> const 0.

Definition P1 n :=
  sideRLs tm (hRL^^n) (const 0) (R1 n).

Definition P2 n :=
  sideRLs tm (hRL^^(n+1)) (R1 n) (R1 (n*2+1)).

Lemma P1_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P1 (m*2+1).
Proof.
  unfold P0,P1,P2,R1.
  replace (m*2+1) with (m+(m+1)) by lia.
  intros HP0 HP1 HP2.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  1: apply HP2.
Qed.

Lemma P2_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P2 (m*2+1).
Proof.
  intros HP0 HP1 HP2.
  pose proof (P0_S m HP0) as HP0'.
  pose proof (P1_S m HP0 HP1 HP2) as HP1'.
  gen HP0 HP1 HP2 HP0' HP1'.
  unfold P0,P1,P2,R1.
  intros HP0 HP1 HP2 HP0' HP1'.
  rewrite lpow_add.
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat.
    1: apply HP0'.
    1: apply HP1'.
  - replace ((m*2+1)*2+1) with (m*2+m*2+3) by lia.
    simpl_tape.
    side_Ss.
Qed.

Lemma Pall i:
  P0 (2^i-1) /\
  P1 (2^i-1) /\
  P2 (2^i-1).
Proof.
  induction i.
  - repeat split.
    + constructor.
    + unfold P1,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
    + unfold P2,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
  - destruct IHi as [HP0 [HP1 HP2]].
    pose proof (Nat.pow_nonzero 2 i) as Hpow.
    replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
    remember (2^i-1) as m.
    repeat split.
    + apply P0_S; auto.
    + apply P1_S; auto.
    + apply P2_S; auto.
Qed.

Definition L n := const 0 <* [1]^^n.
Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L n) (L (m*3+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*3) with (m*3+3) by lia.
  unfold L.
  simpl_tape.
  side_Ss.
Qed.

Definition config '(n,i) := L n {{{ (hR,R) }}} R1 (2^i-1).

Lemma BigStep n i:
  config (n,i) -->+
  config (2^i*3+n,S i).
Proof.
  epose proof (Pall i) as [HP0 [HP1 HP2]].
  unfold P2 in HP2.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  unfold hRL in HP2.
  rewrite <-lrcons_lpow1 in HP2.
  2: lia.
  unfold config.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HP2.
    apply LIncs.
  - cbn[Nat.pow].
    replace ((2^i-1)*2+1) with (2*2^i-1) by lia.
    remember ((2^i-1+1-1)*3+n) as v1.
    replace (2^i*3+n) with (3+v1) by lia.
    unfold L.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (23,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n i].
  eexists (_,_).
  apply BigStep.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1LB1RC_0RA1RB_1RD0RF_0LE---_0LF1LE_1LA0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[1;1]).
Definition hL:DH0 := (E,[1;1]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0] ++ [1;1;0]^^n.
Definition B1 n := [0] ++ [1;1;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^n) (hRL^^n) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;1] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [1;1;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Definition R1 n := B0 n *> const 0.

Definition P1 n :=
  sideRLs tm (hRL^^n) (const 0) (R1 n).

Definition P2 n :=
  sideRLs tm (hRL^^(n+1)) (R1 n) (R1 (n*2+1)).

Lemma P1_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P1 (m*2+1).
Proof.
  unfold P0,P1,P2,R1.
  replace (m*2+1) with (m+(m+1)) by lia.
  intros HP0 HP1 HP2.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  1: apply HP2.
Qed.

Lemma P2_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P2 (m*2+1).
Proof.
  intros HP0 HP1 HP2.
  pose proof (P0_S m HP0) as HP0'.
  pose proof (P1_S m HP0 HP1 HP2) as HP1'.
  gen HP0 HP1 HP2 HP0' HP1'.
  unfold P0,P1,P2,R1.
  intros HP0 HP1 HP2 HP0' HP1'.
  rewrite lpow_add.
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat.
    1: apply HP0'.
    1: apply HP1'.
  - replace ((m*2+1)*2+1) with (m*2+m*2+3) by lia.
    simpl_tape.
    side_Ss.
Qed.

Lemma Pall i:
  P0 (2^i-1) /\
  P1 (2^i-1) /\
  P2 (2^i-1).
Proof.
  induction i.
  - repeat split.
    + constructor.
    + unfold P1,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
    + unfold P2,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
  - destruct IHi as [HP0 [HP1 HP2]].
    pose proof (Nat.pow_nonzero 2 i) as Hpow.
    replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
    remember (2^i-1) as m.
    repeat split.
    + apply P0_S; auto.
    + apply P1_S; auto.
    + apply P2_S; auto.
Qed.

Definition L n := const 0 <* [1]^^n.
Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L n) (L (m*3+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*3) with (m*3+3) by lia.
  unfold L.
  simpl_tape.
  side_Ss.
Qed.

Definition config '(n,i) := L n {{{ (hR,R) }}} R1 (2^i-1).

Lemma BigStep n i:
  config (n,i) -->+
  config (2^i*3+n,S i).
Proof.
  epose proof (Pall i) as [HP0 [HP1 HP2]].
  unfold P2 in HP2.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  unfold hRL in HP2.
  rewrite <-lrcons_lpow1 in HP2.
  2: lia.
  unfold config.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HP2.
    apply LIncs.
  - cbn[Nat.pow].
    replace ((2^i-1)*2+1) with (2*2^i-1) by lia.
    remember ((2^i-1+1-1)*3+n) as v1.
    replace (2^i*3+n) with (3+v1) by lia.
    unfold L.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (24,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n i].
  eexists (_,_).
  apply BigStep.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1LB0LB_1LC1RD_0RB1RC_1RE0RA_0LF---_0LA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[1;1]).
Definition hL:DH0 := (F,[1;1]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0] ++ [1;1;0]^^n.
Definition B1 n := [0] ++ [1;1;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^n) (hRL^^n) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;1] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [1;1;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Definition R1 n := B0 n *> const 0.

Definition P1 n :=
  sideRLs tm (hRL^^n) (const 0) (R1 n).

Definition P2 n :=
  sideRLs tm (hRL^^(n+1)) (R1 n) (R1 (n*2+1)).

Lemma P1_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P1 (m*2+1).
Proof.
  unfold P0,P1,P2,R1.
  replace (m*2+1) with (m+(m+1)) by lia.
  intros HP0 HP1 HP2.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply HP1.
  1: apply HP2.
Qed.

Lemma P2_S m:
  P0 m ->
  P1 m ->
  P2 m ->
  P2 (m*2+1).
Proof.
  intros HP0 HP1 HP2.
  pose proof (P0_S m HP0) as HP0'.
  pose proof (P1_S m HP0 HP1 HP2) as HP1'.
  gen HP0 HP1 HP2 HP0' HP1'.
  unfold P0,P1,P2,R1.
  intros HP0 HP1 HP2 HP0' HP1'.
  rewrite lpow_add.
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat.
    1: apply HP0'.
    1: apply HP1'.
  - replace ((m*2+1)*2+1) with (m*2+m*2+3) by lia.
    simpl_tape.
    side_Ss.
Qed.

Lemma Pall i:
  P0 (2^i-1) /\
  P1 (2^i-1) /\
  P2 (2^i-1).
Proof.
  induction i.
  - repeat split.
    + constructor.
    + unfold P1,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
    + unfold P2,R1.
      cbn.
      rewrite <-const_unfold.
      side_Ss.
  - destruct IHi as [HP0 [HP1 HP2]].
    pose proof (Nat.pow_nonzero 2 i) as Hpow.
    replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
    remember (2^i-1) as m.
    repeat split.
    + apply P0_S; auto.
    + apply P1_S; auto.
    + apply P2_S; auto.
Qed.

Definition L n := const 0 <* [1]^^n.
Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L n) (L (m*3+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*3) with (m*3+3) by lia.
  unfold L.
  simpl_tape.
  side_Ss.
Qed.

Definition config '(n,i) := L n {{{ (hR,R) }}} R1 (2^i-1).

Lemma BigStep n i:
  config (n,i) -->+
  config (2^i*3+n,S i).
Proof.
  epose proof (Pall i) as [HP0 [HP1 HP2]].
  unfold P2 in HP2.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  unfold hRL in HP2.
  rewrite <-lrcons_lpow1 in HP2.
  2: lia.
  unfold config.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HP2.
    apply LIncs.
  - cbn[Nat.pow].
    replace ((2^i-1)*2+1) with (2*2^i-1) by lia.
    remember ((2^i-1+1-1)*3+n) as v1.
    replace (2^i*3+n) with (3+v1) by lia.
    unfold L.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (22,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n i].
  eexists (_,_).
  apply BigStep.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LB1RC_0LE1LD_0LF0LC_1RA0RA_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[]).
Definition hL:DH0 := (D,[1;0;1]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0;1;1;1] ++ [0;1;1;1]^^n.
Definition B1 n := [0;1;1;1] ++ [0;1;0;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^(n*2)) (hRL^^(n*2)) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace ((m*2+1)*2) with (m*2+2+m*2) by lia.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    1: apply IHn.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [0;1;0;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  1: ee'.
  1: ee'.
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Lemma P0_i i:
  P0 (2^i-1).
Proof.
  induction i.
  1: constructor.
  pose proof (Nat.pow_nonzero 2 i).
  replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
  apply P0_S,IHi.
Qed.

Definition R0 i := B0 (2^i-1) *> const 0.
Definition R1 i := B1 (2^i-1) *> const 0.

Lemma RIncs i:
  sideRLs tm (hRL^^((2^i-1)*2)) (R0 i) (R1 i).
Proof.
  unfold R0.
  pose proof (P0_i i) as HP0.
  eapply segRLs_sideRLs_concat.
  1: apply HP0.
  generalize ((2^i-1)*2).
  intro n.
  induction n.
  1: constructor.
  econstructor.
  2: apply IHn.
  es.
Qed.

Definition L n := const 0 <* [1;1]^^n.

Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L (n)) (L (m*3+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*3) with (m*3+3) by lia.
  unfold L.
  simpl_tape.
  repeat rewrite lpow_mul.
  side_Ss.
Qed.

Definition config i := L (5) {{{ (hR,R) }}} R0 (i+1).

Lemma BigStep i:
  config i -->+
  config (S (S i)).
Proof.
  unfold config.
  epose proof (RIncs (i+1)) as HR.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  assert (2^(i+1)>=2) as Hpow' by (rewrite Nat.add_comm; cbn; lia).
  unfold hRL in HR.
  rewrite <-lrcons_lpow1 in HR.
  2: lia.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HR.
    apply LIncs.
  - unfold L,R0,R1,B0,B1.
    cbn[Nat.add].
    cbn[Nat.pow].
    remember (2^(i+1)) as m.
    replace (((m - 1) * 2 - 1) * 3 + 5) with ((m*3-2)*2) by lia.
    rewrite lpow_mul.
    replace (2*(2*m)-1) with (2+(m*3-2)+(m-1)) by lia.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 2).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists (_).
  apply BigStep.
Qed.
End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_0LF0LD_0LE1LC_1RA0RA_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[]).
Definition hL:DH0 := (C,[1;0;1]).
Definition hRL := [(hR,hL)].


Definition B0 n := [0;1;1;1] ++ [0;1;1;1]^^n.
Definition B1 n := [0;1;1;1] ++ [0;1;0;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^(n*2)) (hRL^^(n*2)) (B0 n) (B1 n).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace ((m*2+1)*2) with (m*2+2+m*2) by lia.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    1: apply IHn.
  }
  eapply segRLs_trans.
  2: {
    replace (B1 (m+1+m)) with (B1 m ++ [0;1;0;1]^^(1+m)) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply segRLs_wall.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_S'.
  1: ee'.
  1: ee'.
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Lemma P0_i i:
  P0 (2^i-1).
Proof.
  induction i.
  1: constructor.
  pose proof (Nat.pow_nonzero 2 i).
  replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
  apply P0_S,IHi.
Qed.

Definition R0 i := B0 (2^i-1) *> const 0.
Definition R1 i := B1 (2^i-1) *> const 0.

Lemma RIncs i:
  sideRLs tm (hRL^^((2^i-1)*2)) (R0 i) (R1 i).
Proof.
  unfold R0.
  pose proof (P0_i i) as HP0.
  eapply segRLs_sideRLs_concat.
  1: apply HP0.
  generalize ((2^i-1)*2).
  intro n.
  induction n.
  1: constructor.
  econstructor.
  2: apply IHn.
  es.
Qed.

Definition L n := const 0 <* [1;1]^^n.

Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L (n)) (L (m*3+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*3) with (m*3+3) by lia.
  unfold L.
  simpl_tape.
  repeat rewrite lpow_mul.
  side_Ss.
Qed.

Definition config i := L (5) {{{ (hR,R) }}} R0 (i+1).

Lemma BigStep i:
  config i -->+
  config (S (S i)).
Proof.
  unfold config.
  epose proof (RIncs (i+1)) as HR.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  assert (2^(i+1)>=2) as Hpow' by (rewrite Nat.add_comm; cbn; lia).
  unfold hRL in HR.
  rewrite <-lrcons_lpow1 in HR.
  2: lia.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HR.
    apply LIncs.
  - unfold L,R0,R1,B0,B1.
    cbn[Nat.add].
    cbn[Nat.pow].
    remember (2^(i+1)) as m.
    replace (((m - 1) * 2 - 1) * 3 + 5) with ((m*3-2)*2) by lia.
    rewrite lpow_mul.
    replace (2*(2*m)-1) with (2+(m*3-2)+(m-1)) by lia.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 2).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists (_).
  apply BigStep.
Qed.
End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC1RA_1LD0LE_1RB0RB_0RD0LF_---1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[1]).
Definition hL:DH0 := (C,[1;0;0;1;0;0;1]).
Definition hL':DH0 := (C,[1;0;0;1]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR,hL')].


Definition B0 n := [0;0;1;1;1;1] ++ [0;0;1;1;1;1]^^n.

Definition P0 n: Prop :=
  segRLs tm (hRL^^(n*2)) (hRL'^^(n*2)) (B0 n) (B0 0).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace ((m*2+1)*2) with (m*2+2+m*2) by lia.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply @segRLs_concat with (w2:=[0;0;1]^^(m*2)).
    2: apply IHn.
    generalize (m*2).
    intros n.
    induction n.
    1: constructor.
    replace (S n) with (n+1) by lia.
    repeat rewrite lpow_add.
    eapply segRLs_trans.
    1: apply IHn0.
    simpl_rotate_list.
    eapply segRLs_S'.
    3: constructor.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_trans.
  2: eapply IHn.
  eapply segRLs_S'.
  1: ee'.
  1: ee'.
  rewrite lpow_mul.
  simpl_rotate_list.
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Lemma P0_i i:
  P0 (2^i-1).
Proof.
  induction i.
  1: constructor.
  pose proof (Nat.pow_nonzero 2 i).
  replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
  apply P0_S,IHi.
Qed.

Definition R0 i := B0 (2^i-1) *> const 0.
Definition R1 := B0 0 *> const 0.

Lemma RIncs i:
  sideRLs tm (hRL^^((2^i-1)*2)) (R0 i) (R1).
Proof.
  unfold R0.
  pose proof (P0_i i) as HP0.
  eapply segRLs_sideRLs_concat.
  1: apply HP0.
  generalize ((2^i-1)*2).
  intro n.
  induction n.
  1: constructor.
  econstructor.
  2: apply IHn.
  es.
Qed.

Definition L n := const 0 <* [1;1;1]^^n <* [1].

Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L (n)) (L (m*2+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*2) with (m*2+2) by lia.
  unfold L.
  simpl_tape.
  repeat rewrite lpow_mul.
  side_Ss.
Qed.

Definition config i := L (2) {{{ (hR,R) }}} R0 (i+1).

Lemma BigStep i:
  config i -->+
  config (S i).
Proof.
  unfold config.
  epose proof (RIncs (i+1)) as HR.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  assert (2^(i+1)>=2) as Hpow' by (rewrite Nat.add_comm; cbn; lia).
  unfold hRL in HR.
  rewrite <-lrcons_lpow1 in HR.
  2: lia.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HR.
    apply LIncs.
  - unfold L,R0,R1,B0.
    cbn[Nat.add].
    cbn[Nat.pow].
    remember (2^(i+1)) as m.
    replace (((m - 1) * 2 - 1) * 2 + 2) with ((m*2-2)*2) by lia.
    rewrite lpow_mul.
    replace (2*m-1) with (1+(m*2-2)) by lia.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 2).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists (_).
  apply BigStep.
Qed.
End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC1RE_1LD---_1LE0LC_0RA0RB_1RB1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[]).
Definition hL:DH0 := (D,[1;0;1;0]).
Definition hL':DH0 := (D,[1;0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR,hL')].


Definition B0 n := [] ++ [1;0;1;0]^^n.
Goal segRLs tm (hRL^^2) (hRL'^^2) (B0 1) (B0 0).
Proof.
  cbn.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply @segRLs_S' with (w3:=[]).
  1: ee.
  1: ee.
  constructor.
Qed.

Goal
segRLs tm (hRL^^6) (hRL'^^6) (B0 3) (B0 0).
Proof.
  cbn.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply @segRLs_S' with (w3:=[]).
  1: ee.
  1: ee.
  constructor.
Qed.

Definition P0 n: Prop :=
  segRLs tm (hRL^^(n*2)) (hRL'^^(n*2)) (B0 n) (B0 0).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace ((m*2+1)*2) with (m*2+2+m*2) by lia.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;0;1;0] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply @segRLs_concat with (w2:=[1;0] ++ [1;1]^^(m*2) ++ [1;0]).
    2: apply IHn.
    generalize (m*2).
    intros n.
    induction n.
    1: constructor.
    replace (S n) with (n+1) by lia.
    repeat rewrite lpow_add.
    eapply segRLs_trans.
    1: apply IHn0.
    simpl_rotate_list.
    eapply segRLs_S'.
    3: constructor.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_trans.
  2: eapply IHn.
  eapply segRLs_S'.
  1: ee'.
  1: ee'.
  rewrite lpow_mul.
  simpl_rotate_list.
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Lemma P0_i i:
  P0 (2^i-1).
Proof.
  induction i.
  1: constructor.
  pose proof (Nat.pow_nonzero 2 i).
  replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
  apply P0_S,IHi.
Qed.

Definition R0 i := B0 (2^i-1) *> [1;1] *> const 0.
Definition R1 := B0 0 *> [1;1] *> const 0.

Lemma RIncs i:
  sideRLs tm (hRL^^((2^i-1)*2)) (R0 i) (R1).
Proof.
  unfold R0.
  pose proof (P0_i i) as HP0.
  eapply segRLs_sideRLs_concat.
  1: apply HP0.
  generalize ((2^i-1)*2).
  intro n.
  induction n.
  1: constructor.
  econstructor.
  2: apply IHn.
  es.
Qed.

Definition L n := const 0 <* <[1;0]^^n.

Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L (n)) (L (m*2+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*2) with (m*2+2) by lia.
  unfold L.
  simpl_tape.
  repeat rewrite lpow_mul.
  side_Ss.
Qed.

Definition config i := L (2) {{{ (hR,R) }}} R0 (i+1).

Lemma BigStep i:
  config i -->+
  config (S i).
Proof.
  unfold config.
  epose proof (RIncs (i+1)) as HR.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  assert (2^(i+1)>=2) as Hpow' by (rewrite Nat.add_comm; cbn; lia).
  unfold hRL in HR.
  rewrite <-lrcons_lpow1 in HR.
  2: lia.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HR.
    apply LIncs.
  - unfold L,R0,R1,B0.
    cbn[Nat.add].
    cbn[Nat.pow].
    remember (2^(i+1)) as m.
    replace (((m - 1) * 2 - 1) * 2 + 2) with ((m*2-2)*2) by lia.
    rewrite lpow_mul.
    replace (2*m-1) with (1+(m*2-2)) by lia.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 2).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists (_).
  apply BigStep.
Qed.
End TM13.

Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LA_0RD0RF_0RF0RE_1RF1RD_1LA1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[]).
Definition hL:DH0 := (B,[1;0;1;0]).
Definition hL':DH0 := (B,[1;0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR,hL')].


Definition B0 n := [] ++ [1;0;1;0]^^n.
Goal segRLs tm (hRL^^2) (hRL'^^2) (B0 1) (B0 0).
Proof.
  cbn.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply @segRLs_S' with (w3:=[]).
  1: ee.
  1: ee.
  constructor.
Qed.

Goal
segRLs tm (hRL^^6) (hRL'^^6) (B0 3) (B0 0).
Proof.
  cbn.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply segRLs_S'.
  1: ee.
  1: ee.
  eapply @segRLs_S' with (w3:=[]).
  1: ee.
  1: ee.
  constructor.
Qed.

Definition P0 n: Prop :=
  segRLs tm (hRL^^(n*2)) (hRL'^^(n*2)) (B0 n) (B0 0).

Lemma P0_S m:
  P0 m ->
  P0 (m*2+1).
Proof.
  unfold P0.
  intros IHn.
  replace ((m*2+1)*2) with (m*2+2+m*2) by lia.
  replace (m*2+1) with (m+1+m) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: {
    replace (B0 (m+1+m)) with (B0 m ++ [1;0;1;0] ++ B0 m) by simpl_rotate_list.
    eapply segRLs_concat.
    1: apply IHn.
    eapply @segRLs_concat with (w2:=[1;0] ++ [1;1]^^(m*2) ++ [1;0]).
    2: apply IHn.
    generalize (m*2).
    intros n.
    induction n.
    1: constructor.
    replace (S n) with (n+1) by lia.
    repeat rewrite lpow_add.
    eapply segRLs_trans.
    1: apply IHn0.
    simpl_rotate_list.
    eapply segRLs_S'.
    3: constructor.
    1: ee'.
    1: ee'.
  }
  eapply segRLs_trans.
  2: eapply IHn.
  eapply segRLs_S'.
  1: ee'.
  1: ee'.
  rewrite lpow_mul.
  simpl_rotate_list.
  eapply segRLs_S'.
  3: constructor.
  1: ee'.
  1: ee'.
Qed.

Lemma P0_i i:
  P0 (2^i-1).
Proof.
  induction i.
  1: constructor.
  pose proof (Nat.pow_nonzero 2 i).
  replace (2^S i-1) with ((2^i-1)*2+1) by (cbn; lia).
  apply P0_S,IHi.
Qed.

Definition R0 i := B0 (2^i-1) *> [1;1] *> const 0.
Definition R1 := B0 0 *> [1;1] *> const 0.

Lemma RIncs i:
  sideRLs tm (hRL^^((2^i-1)*2)) (R0 i) (R1).
Proof.
  unfold R0.
  pose proof (P0_i i) as HP0.
  eapply segRLs_sideRLs_concat.
  1: apply HP0.
  generalize ((2^i-1)*2).
  intro n.
  induction n.
  1: constructor.
  econstructor.
  2: apply IHn.
  es.
Qed.

Definition L n := const 0 <* <[1;0]^^n.

Lemma LIncs n m:
  sideRLs (flip tm) ([(hL,hR)]^^m) (L (n)) (L (m*2+n)).
Proof.
  induction m.
  1: constructor.
  replace (S m) with (m+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHm.
  replace ((m+1)*2) with (m*2+2) by lia.
  unfold L.
  simpl_tape.
  repeat rewrite lpow_mul.
  side_Ss.
Qed.

Definition config i := L (2) {{{ (hR,R) }}} R0 (i+1).

Lemma BigStep i:
  config i -->+
  config (S i).
Proof.
  unfold config.
  epose proof (RIncs (i+1)) as HR.
  epose proof (Nat.pow_nonzero 2 i) as Hpow.
  assert (2^(i+1)>=2) as Hpow' by (rewrite Nat.add_comm; cbn; lia).
  unfold hRL in HR.
  rewrite <-lrcons_lpow1 in HR.
  2: lia.
  eapply progress_trans.
  - eapply sideRLs_concat.
    2: apply HR.
    apply LIncs.
  - unfold L,R0,R1,B0.
    cbn[Nat.add].
    cbn[Nat.pow].
    remember (2^(i+1)) as m.
    replace (((m - 1) * 2 - 1) * 2 + 2) with ((m*2-2)*2) by lia.
    rewrite lpow_mul.
    replace (2*m-1) with (1+(m*2-2)) by lia.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 2).
  1: cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists (_).
  apply BigStep.
Qed.
End TM14.
