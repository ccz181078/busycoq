From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD1LE_1LE1RF_0LB---_0RA1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[]).
Definition hL:DH0 := (B,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;0;1;0;1].
Definition w1 := [0;1;0;0;1].
Definition w1' := <[0;1;1;0;1].

Definition d0 := <[0;0;0;1].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1;0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;0;1;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+4) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+4))%nat ls) /\
  (Rn (2*2^(k+4)) ls - Rn (2^(k+4)) ls = Z.of_nat (4*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (O,[2;1]%nat,20))).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA---_0RF1LE_1RA0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[]).
Definition hL:DH0 := (A,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;0;1;0;1].
Definition w1 := [0;1;0;0;1].
Definition w1' := <[0;1;1;0;1].

Definition d0 := <[0;0;0;1].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1;0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;0;1;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+5) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+5))%nat ls) /\
  (Rn (2*2^(k+5)) ls - Rn (2^(k+5)) ls = Z.of_nat (4*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[4]%nat,20)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD1LE_1LE1RF_0LB---_0RA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[]).
Definition hL:DH0 := (B,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;0;1;0;1].
Definition w1 := [0;1;0;0;1].
Definition w1' := <[0;1;1;0;1].

Definition d0 := <[0;0;0;1].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1;0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;0;1;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+4) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+4))%nat ls) /\
  (Rn (2*2^(k+4)) ls - Rn (2^(k+4)) ls = Z.of_nat (4*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (O,[2;1]%nat,20))).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1LB_0RF1LF_1RC0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[]).
Definition hL:DH0 := (C,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;0;1;0;1].
Definition w1 := [0;1;0;0;1].
Definition w1' := <[0;1;1;0;1].

Definition d0 := <[0;0;0;1].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1;0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;0;1;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+5) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+5))%nat ls) /\
  (Rn (2*2^(k+5)) ls - Rn (2^(k+5)) ls = Z.of_nat (2*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[]%nat,12)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB0RF_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[]).
Definition hL:DH0 := (D,[]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (D,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0;0].
Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;1].
Definition w1' := <[1;0;1;1;0;1].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;0;1; 0;0;0;1].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;0;1; 0;1;0;1].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn_spec n0 ls:
  (0 < (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (1 + (Z.to_nat (Rn n0 ls) - a - 1))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 1))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 1) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; lia.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> [0;0;1] *> w1^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+1 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 1)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (1+Z.to_nat (v1-v2-1)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-1)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;0;1]) (d1:=d1 <+ <[1;0;1]); execute.
  - cbn[app].
    change w1 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;0;1] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [1] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 1 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 1)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [1] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 1 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+3))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[4;0;0]%nat,20)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB1RF_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (B,[1]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (B,[1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;1].
Definition w1' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (2 + (Z.to_nat (Rn n0 ls) - a - 2))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 3))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 2) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> [0;0;1] *> w1^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w1 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[1]%nat,4)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LE_0RD0LD_1LE1RF_0LB0RC_0RE1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[1]).
Definition hL:DH0 := (E,[1]).

Definition hR':DH0 := (F,[1]).
Definition hL':DH0 := (E,[1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;1].
Definition w2 := [0;0;1;0;0;1].
Definition w2' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*2 + (3 + (Z.to_nat (Rn n0 ls) - a*2 - 3))) by lia.
      eapply (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 2) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 2 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w2 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w2,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w2 d1' ls *> [0;0;1] *> w2^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w2,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w2,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*2+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*2 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 2 + (3+Z.to_nat (v1-v2*2-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*2-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w2 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 2 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 2 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 2 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[]%nat,7)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB1RF_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (D,[0]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (D,[0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;0].
Definition w2 := [0;0;1;0;0;1].
Definition w2' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2)*2 - 3
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*2 + (2 + (Z.to_nat (Rn n0 ls) - a*2 - 2))) by lia.
      eapply (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 2) * 2 - 3))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 2 - 2) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w2 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w2,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w2 d1' ls *> [0;0;1] *> w2^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w2,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w2,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*2+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*2 - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 2 + (2+Z.to_nat (v1-v2*2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*2-2)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w2 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 2 + 2 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 2 - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*2)*2 - 3
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 2 + 2 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[1]%nat,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1LB_0RF1LE_1RC0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[]).
Definition hL:DH0 := (C,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;0;1;0;1].
Definition w1 := [0;1;0;0;1].
Definition w1' := <[0;1;1;0;1].

Definition d0 := <[0;0;0;1].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1;0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;0;1;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+4) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+4))%nat ls) /\
  (Rn (2*2^(k+4)) ls - Rn (2^(k+4)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1%nat,[],12))).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LC_0RD0LC_1LE1RF_0LB0RC_0RE1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[1]).
Definition hL:DH0 := (C,[0]).

Definition hR':DH0 := (F,[1]).
Definition hL':DH0 := (C,[0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;0].
Definition w2 := [0;0;1;0;0;0].
Definition w3 := [0;0;1;0;0;1].
Definition w3' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*3)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w3 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*3 + (3 + (Z.to_nat (Rn n0 ls) - a*3 - 3))) by lia.
      eapply (UC3.Incs tm hR hL w0 w1 w2 w3 w3'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 3) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 3 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w3 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w3,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w3 d1' ls *> [0;0;1] *> w3^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w3,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w3,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*3+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*3 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 3 + (3+Z.to_nat (v1-v2*3-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC3.Incs tm hR hL w0 w1 w2 w3 w3'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*3-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w3 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 3 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 3 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.
Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*3)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 3 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+2))) /\
  Rn' 0 ls <= 0)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (1%nat,[1;1]%nat,13)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      remember (Rn' (2 ^ (k + k0) * 2) ls) as v1.
      remember (Rn' 0 ls) as v2.
      rewrite Z2Nat.id. 2: lia.
      intros HP1.
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
    + cbn[Rn'].
      lia.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD1RE_1LE1RF_0LB---_0RA1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[0]).
Definition hL:DH0 := (B,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;0;1;0].
Definition w1 := [1;0;0;1;0].
Definition w1' := <[0;1;1;0;1].

Definition d0 := <[0;0;0;1].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d1a := [1;0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[1;0;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+4) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+4))%nat ls) /\
  (Rn (2*2^(k+4)) ls - Rn (2^(k+4)) ls = Z.of_nat (4^(k+3))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[2;1],20)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF1LF_1RA0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[0]).
Definition hL:DH0 := (A,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;0;1;0].
Definition w1 := [1;0;0;1;0].
Definition w1' := <[0;1;1;0;1].

Definition d0 := <[0;0;0;1].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d1a := [1;0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[1;0;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+4) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+4))%nat ls) /\
  (Rn (2*2^(k+4)) ls - Rn (2^(k+4)) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[4],20)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1LB1RF_0RC---_1RE1LD_0LC0RE_0RA0LA_0RD1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[1]).
Definition hL:DH0 := (B,[1]).

Definition hR':DH0 := (F,[1;0]).
Definition hL':DH0 := (C,[0;1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;1].
Definition w1' := <[1;1;0;1;1;0].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (2 + (Z.to_nat (Rn n0 ls) - a - 2))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 3))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 2) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> [0;0;1] *> w1^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w1 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [0] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [0] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[1]%nat,4)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RB_0RB0RF_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (D,[0]).

Definition hR':DH0 := (E,[1;0]).
Definition hL':DH0 := (C,[0;1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;1].
Definition w1' := <[1;1;0;1;1;0].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (1 + (Z.to_nat (Rn n0 ls) - a - 1))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 1))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 1) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> [0;0;1] *> w1^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+1 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 1)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (1+Z.to_nat (v1-v2-1)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-1)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w1 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [0] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 1 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 1)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [0] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 2.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 1 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[0;0]%nat,4)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF1LE_1RA0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[0]).
Definition hL:DH0 := (A,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;0;1;0].
Definition w1 := [1;0;0;1;0].
Definition w1' := <[0;1;1;0;1].

Definition d0 := <[0;0;0;1].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d1a := [1;0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[1;0;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+4) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+4))%nat ls) /\
  (Rn (2*2^(k+4)) ls - Rn (2^(k+4)) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[4],20)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD1RE_1LE1RF_0LB---_0RA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[0]).
Definition hL:DH0 := (B,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;0;1;0].
Definition w1 := [1;0;0;1;0].
Definition w1' := <[0;1;1;0;1].

Definition d0 := <[0;0;0;1].
Definition d1 := <[0;1;0;1].
Definition d1' := [1;0;1;0].
Definition d1a := [1;0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[1;0;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+4) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+4))%nat ls) /\
  (Rn (2*2^(k+4)) ls - Rn (2^(k+4)) ls = Z.of_nat (4*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (O,[2;1]%nat,20))).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RB_0RD0RF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (B,[0]).

Definition hR':DH0 := (E,[1;0]).
Definition hL':DH0 := (A,[0;1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;1].
Definition w1' := <[1;1;0;1;1;0].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (1 + (Z.to_nat (Rn n0 ls) - a - 1))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 1))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 1) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> [0;0;1] *> w1^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+1 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 1)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (1+Z.to_nat (v1-v2-1)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-1)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w1 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [0] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 1 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 1)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [0] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 2.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 1 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,[0],2)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD0RF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (B,[0]).

Definition hR':DH0 := (E,[1;0]).
Definition hL':DH0 := (A,[0;1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;1].
Definition w1' := <[1;1;0;1;1;0].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (1 + (Z.to_nat (Rn n0 ls) - a - 1))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 1))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 1) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> [0;0;1] *> w1^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+1 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 1)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (1+Z.to_nat (v1-v2-1)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-1)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w1 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [0] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 1 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 1)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [0] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 2.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 1 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,[0],2)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RB_0RB1RF_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (D,[0]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (D,[0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;0].
Definition w2 := [0;0;1;0;0;1].
Definition w2' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2)*2 - 3
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*2 + (2 + (Z.to_nat (Rn n0 ls) - a*2 - 2))) by lia.
      eapply (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 2) * 2 - 3))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 2 - 2) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w2 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w2,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w2 d1' ls *> [0;0;1] *> w2^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w2,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w2,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*2+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*2 - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 2 + (2+Z.to_nat (v1-v2*2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*2-2)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w2 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 2 + 2 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 2 - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*2)*2 - 3
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 2 + 2 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[1]%nat,3)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM19.


Module TM20.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LC_0RD1RE_1LE1RF_0LB0RC_0RE1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[1]).
Definition hL:DH0 := (C,[0]).

Definition hR':DH0 := (F,[1]).
Definition hL':DH0 := (C,[0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;0].
Definition w2 := [0;0;1;0;0;0].
Definition w3 := [0;0;1;0;0;1].
Definition w3' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*3)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w3 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*3 + (3 + (Z.to_nat (Rn n0 ls) - a*3 - 3))) by lia.
      eapply (UC3.Incs tm hR hL w0 w1 w2 w3 w3'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 3) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 3 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w3 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w3,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w3 d1' ls *> [0;0;1] *> w3^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w3,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w3,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*3+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*3 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 3 + (3+Z.to_nat (v1-v2*3-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC3.Incs tm hR hL w0 w1 w2 w3 w3'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*3-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w3 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 3 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 3 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.
Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*3)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 3 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+2))) /\
  Rn' 0 ls <= 0)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (1%nat,[1;1]%nat,13)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      remember (Rn' (2 ^ (k + k0) * 2) ls) as v1.
      remember (Rn' 0 ls) as v2.
      rewrite Z2Nat.id. 2: lia.
      intros HP1.
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
    + cbn[Rn'].
      lia.
Qed.

End TM20.


Module TM21.

Definition tm := Eval compute in (TM_from_str "1RB1LE_0RC0LC_1LD1RF_0RA---_0LA0RB_0RE1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[1]).
Definition hL:DH0 := (D,[1]).

Definition hR':DH0 := (F,[1;0]).
Definition hL':DH0 := (A,[0;1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;1].
Definition w1' := <[1;1;0;1;1;0].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (2 + (Z.to_nat (Rn n0 ls) - a - 2))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 3))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 2) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> [0;0;1] *> w1^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w1 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [0] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [0] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 2.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[0],1)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM21.


Module TM22.

Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0RB_0RD1RF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (D,[1]).

Definition hR':DH0 := (E,[1;0]).
Definition hL':DH0 := (A,[0;1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;1].
Definition w1' := <[1;1;0;1;1;0].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (2 + (Z.to_nat (Rn n0 ls) - a - 2))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 3))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 2) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> [0;0;1] *> w1^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w1 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [0] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [0] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 2.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[0],1)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM22.


Module TM23.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB1RF_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (B,[1]).

Definition hR':DH0 := (E,[1;0]).
Definition hL':DH0 := (C,[0;1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;1].
Definition w1' := <[1;1;0;1;1;0].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (2 + (Z.to_nat (Rn n0 ls) - a - 2))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 3))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 2) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> [0;0;1] *> w1^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w1 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [0] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [0] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 2.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (1,[1],4)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+1)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM23.


Module TM24.

Definition tm := Eval compute in (TM_from_str "1RB1RC_0RC0LC_1LD1RE_0LA0RB_0RD1RF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (D,[1]).

Definition hR':DH0 := (E,[1;0]).
Definition hL':DH0 := (A,[0;1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;1].
Definition w1' := <[1;1;0;1;1;0].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (2 + (Z.to_nat (Rn n0 ls) - a - 2))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 3))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 2) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> [0;0;1] *> w1^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w1 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [0] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [0] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 3
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 2.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[0],1)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM24.


Module TM25.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RD_0RD0LD_1LE1RF_0LB0RC_0RE1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[1]).
Definition hL:DH0 := (E,[1]).

Definition hR':DH0 := (F,[1]).
Definition hL':DH0 := (E,[1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;1].
Definition w2 := [0;0;1;0;0;1].
Definition w2' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*2 + (3 + (Z.to_nat (Rn n0 ls) - a*2 - 3))) by lia.
      eapply (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 2) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 2 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w2 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w2,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w2 d1' ls *> [0;0;1] *> w2^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w2,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w2,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*2+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*2 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 2 + (3+Z.to_nat (v1-v2*2-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*2-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w2 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 2 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 2 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 2 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (2*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[]%nat,7)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM25.


Module TM26.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RB_0RF1LF_1RC0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[0;1]).
Definition hL:DH0 := (D,[0;0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;0;1;0].
Definition w1 := [1;0;0;1;0].
Definition w1' := <[1;0;1;1;0].

Definition d0 := <[1;0;0;0].
Definition d1 := <[1;0;1;0].
Definition d1' := [1;0;1;0].
Definition d1a := [0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[1;0;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+4) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+4))%nat ls) /\
  (Rn (2*2^(k+4)) ls - Rn (2^(k+4)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],12)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM26.


Module TM27.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD1RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (B,[0]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (B,[0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;0].
Definition w2 := [0;0;1;0;0;0].
Definition w3 := [0;0;1;0;0;1].
Definition w3' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*3)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w3 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*3 + (3 + (Z.to_nat (Rn n0 ls) - a*3 - 3))) by lia.
      eapply (UC3.Incs tm hR hL w0 w1 w2 w3 w3'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 3) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 3 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w3 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w3,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w3 d1' ls *> [0;0;1] *> w3^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w3,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w3,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*3+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*3 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 3 + (3+Z.to_nat (v1-v2*3-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC3.Incs tm hR hL w0 w1 w2 w3 w3'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*3-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w3 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 3 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 3 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.
Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*3)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 3 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4*4^(k+2))) /\
  Rn' 0 ls <= 0)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0%nat,[0;0]%nat,6)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      remember (Rn' (2 ^ (k + k0) * 2) ls) as v1.
      remember (Rn' 0 ls) as v2.
      rewrite Z2Nat.id. 2: lia.
      intros HP1.
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
    + cbn[Rn'].
      lia.
Qed.

End TM27.


Module TM28.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB1RF_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (D,[0]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (D,[0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;0].
Definition w2 := [0;0;1;0;0;0].
Definition w3 := [0;0;1;0;0;1].
Definition w3' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*3)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w3 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*3 + (3 + (Z.to_nat (Rn n0 ls) - a*3 - 3))) by lia.
      eapply (UC3.Incs tm hR hL w0 w1 w2 w3 w3'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 3) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 3 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w3 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w3,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w3 d1' ls *> [0;0;1] *> w3^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w3,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w3,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*3+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*3 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 3 + (3+Z.to_nat (v1-v2*3-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC3.Incs tm hR hL w0 w1 w2 w3 w3'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*3-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w3 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 3 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 3 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.
Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*3)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 3 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4*4^(k+2))) /\
  Rn' 0 ls <= 0)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,[2],6)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      remember (Rn' (2 ^ (k + k0) * 2) ls) as v1.
      remember (Rn' 0 ls) as v2.
      rewrite Z2Nat.id. 2: lia.
      intros HP1.
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
    + cbn[Rn'].
      lia.
Qed.

End TM28.


Module TM29.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB1RF_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (B,[1]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (B,[1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;1].
Definition w2 := [0;0;1;0;0;1].
Definition w2' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*2 + (3 + (Z.to_nat (Rn n0 ls) - a*2 - 3))) by lia.
      eapply (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 2) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 2 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w2 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w2,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w2 d1' ls *> [0;0;1] *> w2^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w2,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w2,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*2+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*2 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 2 + (3+Z.to_nat (v1-v2*2-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*2-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w2 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 2 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 2 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 2 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[3]%nat,6)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM29.


Module TM30.

Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0RB_0RD1RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (D,[1]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (D,[1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;1].
Definition w2 := [0;0;1;0;0;1].
Definition w2' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*2 + (3 + (Z.to_nat (Rn n0 ls) - a*2 - 3))) by lia.
      eapply (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 2) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 2 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w2 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w2,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w2 d1' ls *> [0;0;1] *> w2^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w2,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w2,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*2+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*2 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 2 + (3+Z.to_nat (v1-v2*2-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*2-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w2 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 2 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 2 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 2 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[0;0],6)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM30.


Module TM31.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RB_0RF1LE_1RC0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[0;1]).
Definition hL:DH0 := (D,[0;0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;0;1;0].
Definition w1 := [1;0;0;1;0].
Definition w1' := <[1;0;1;1;0].

Definition d0 := <[1;0;0;0].
Definition d1 := <[1;0;1;0].
Definition d1' := [1;0;1;0].
Definition d1a := [0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[1;0;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+4) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+4))%nat ls) /\
  (Rn (2*2^(k+4)) ls - Rn (2^(k+4)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],12)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM31.


Module TM32.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD1RF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (B,[0]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (B,[0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;0].
Definition w2 := [0;0;1;0;0;1].
Definition w2' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2)*2 - 3
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*2 + (2 + (Z.to_nat (Rn n0 ls) - a*2 - 2))) by lia.
      eapply (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 2) * 2 - 3))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 2 - 2) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w2 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w2,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w2 d1' ls *> [0;0;1] *> w2^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w2,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w2,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*2+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*2 - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 2 + (2+Z.to_nat (v1-v2*2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*2-2)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w2 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 2 + 2 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 2 - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*2)*2 - 3
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 2 + 2 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[1;0]%nat,7)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM32.


Module TM33.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RB_0RD1RF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (B,[0]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (B,[0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;1;0;0;0].
Definition w2 := [0;0;1;0;0;1].
Definition w2' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2)*2 - 3
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*2 + (2 + (Z.to_nat (Rn n0 ls) - a*2 - 2))) by lia.
      eapply (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 2) * 2 - 3))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 2 - 2) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w2 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w2,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w2 d1' ls *> [0;0;1] *> w2^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w2,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w2,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*2+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*2 - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 2 + (2+Z.to_nat (v1-v2*2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*2-2)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w2 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 2 + 2 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 2 - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*2)*2 - 3
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 2 + 2 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (O,[1;0]%nat,7)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM33.


Module TM34.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB1RF_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (B,[1]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (B,[1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;1].
Definition w2 := [0;0;1;0;0;1].
Definition w2' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*2 + (3 + (Z.to_nat (Rn n0 ls) - a*2 - 3))) by lia.
      eapply (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 2) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 2 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w2 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w2,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w2 d1' ls *> [0;0;1] *> w2^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w2,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w2,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*2+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*2 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 2 + (3+Z.to_nat (v1-v2*2-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*2-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w2 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 2 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 2 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 2 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (1,[3],6)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM34.


Module TM35.

Definition tm := Eval compute in (TM_from_str "1RB1RC_0RC0LC_1LD1RE_0LA0RB_0RD1RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (D,[1]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (D,[1]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;1].
Definition w2 := [0;0;1;0;0;1].
Definition w2' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*2 + (3 + (Z.to_nat (Rn n0 ls) - a*2 - 3))) by lia.
      eapply (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 2) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 2 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w2 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w2,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w2 d1' ls *> [0;0;1] *> w2^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w2,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w2,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*2+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*2 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 2 + (3+Z.to_nat (v1-v2*2-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC2.Incs tm hR hL w0 w1 w2 w2'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*2-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w2 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 2 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 2 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*2)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 2 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,[0;0],6)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM35.


Module TM36.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RB_0RD1RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (B,[0]).

Definition hR':DH0 := (E,[1]).
Definition hL':DH0 := (B,[0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;0;0;1;0;0].
Definition w1 := [0;0;0;0;0;0].
Definition w2 := [0;0;1;0;0;0].
Definition w3 := [0;0;1;0;0;1].
Definition w3' := <[1;1;0;1;1;0].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ld1' := [0;1;0;1].
Definition ld1a := [0;1] *> const 0.

Definition d0 := <[1;1;0;1; 0;0;0].
Definition d0' := [1;0;1; 0;1;0;0].
Definition d1 := <[1;1;0;1; 0;1;0].
Definition d1' := [0;0;1; 0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*3)*2 - 5
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w3 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a*3 + (3 + (Z.to_nat (Rn n0 ls) - a*3 - 3))) by lia.
      eapply (UC3.Incs tm hR hL w0 w1 w2 w3 w3'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a * 3) * 2 - 5))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a * 3 - 3) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0]); execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [0;0] *> RC w0 d0' ls *> r = RC w3 d1' ls *> [0;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w3,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;0;0;0;0;0;0;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w3 d1' ls *> [0;0;1] *> w3^^n *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w3,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w3,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)*3+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n)*3 - 3)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 * 3 + (3+Z.to_nat (v1-v2*3-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC3.Incs tm hR hL w0 w1 w2 w3 w3'); execute.
  1,2: f_equal; lia.
  remember (Z.to_nat (v1-v2*3-3)) as v3.
  rewrite lpow_add.
  rewrite <-(Str_app_assoc d1').
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1'++[0;0;1]) (ls2:=[]).
    + eapply @segRLs_S with (w2:=[0;0;0;0;1;0;0;0;0;0]); execute.
      eapply @segRLs_S with (w2:=[0;0;1;0;1;0;0;0;0;0]); execute.
      eapply segRLs_S.
      2: econstructor.
      execute.
    + eapply BCR.Incs with (d0:=d0 <+ <[1;1;0]) (d1:=d1 <+ <[1;1;0]); execute.
  - cbn[app].
    change w3 with ([0;0;1]^^2).
    rewrite <-lpow_mul.
    rewrite <-(lpow_all0 [0;0;0] (v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL [0;0;0] [0;0;1] <[1;1;0] _ _ _ (v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n * 3 + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n * 3 - 3)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [] []); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.
Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n)*3)*2 - 5
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n * 3 + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4*4^(k+2))) /\
  Rn' 0 ls <= 0)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,[0;0],6)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
      epose proof (Nat.pow_nonzero 4 (k+2)).
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      remember (Rn' (2 ^ (k + k0) * 2) ls) as v1.
      remember (Rn' 0 ls) as v2.
      rewrite Z2Nat.id. 2: lia.
      intros HP1.
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
    + cbn[Rn'].
      lia.
Qed.

End TM36.


Module TM37.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LA_0RD0LC_1RF1RE_1LF0RA_1LB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[2],12)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM37.


Module TM38.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LF_0RD0LC_1RF1RE_1LF0RA_1LB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[2],12)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM38.


Module TM39.

Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC0LB_1RE1RD_1LE0RF_1LA0RB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM39.


Module TM40.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC0RE_1LE0LD_1LC---_0RA0LE_1LB0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM40.


Module TM41.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD0LC_1RA1RE_1LA1RF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM41.


Module TM42.

Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC0LB_1RE1RD_1LE1RF_1LA0RB_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM42.


Module TM43.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD0LC_1RA1RE_1LA1RF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM43.


Module TM44.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD0LC_1RA1RE_0LE1RF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM44.


Module TM45.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LF_0RD0LC_1RA1RE_1LA1RE_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM45.


Module TM46.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA0LD_1LB1RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM46.


Module TM47.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA0LD_0LE1RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM47.


Module TM48.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC0LB_1RE1RD_1LE1RD_1LA0RB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM48.


Module TM49.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD0LC_1RA1RE_1LA0RF_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM49.


Module TM50.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD0LC_1RA1RE_0LE0RF_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM50.


Module TM51.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1LC0LA_0RD1RA_1LE1RD_0RC0RC_---1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM51.


Module TM52.

Definition tm := Eval compute in (TM_from_str "1LB1LF_1LC0LA_0RD1RA_1LE1RD_0RC0RC_---1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM52.


Module TM53.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LA_0RD1RE_1LE1RD_0LF0RC_0RF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM53.


Module TM54.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LA_0RD1RE_1LE1RD_1LF0RC_0RE0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM54.


Module TM55.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LA_0RD1RF_1RA1RE_1LF0RA_1LB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM55.


Module TM56.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LA_0RD1RF_1RA1RE_1LF1RE_1LB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM56.


Module TM57.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LA_0RD1RF_1LE1RD_0RC0RC_1LB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM57.


Module TM58.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LA_0RD1RF_1RF1RE_1LF0RA_1LB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM58.


Module TM59.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LF_0RD1RF_0LB1RE_1LF0RA_1LB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM59.


Module TM60.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_1RA1RE_1LA0RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM60.


Module TM61.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_1RA1RE_1LA0RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM61.


Module TM62.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_1RA1RE_1LA0RF_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM62.


Module TM63.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_1RA1RE_1LA1RF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM63.


Module TM64.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_1RA1RE_1LA1RF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM64.


Module TM65.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_1RA1RE_0LE0RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM65.


Module TM66.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_1RA1RE_0LE0RF_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM66.


Module TM67.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_1RA1RE_0LE1RF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM67.


Module TM68.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_0LB1RE_1LA0RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM68.


Module TM69.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_0LB1RE_1LA1RF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM69.


Module TM70.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_0LB1RE_1LA1RF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM70.


Module TM71.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_0LB1RE_0LE0RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM71.


Module TM72.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_0LB1RE_0LE1RF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM72.


Module TM73.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_1RF1RE_1LA0RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM73.


Module TM74.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD0LC_1RA1RE_1LA0RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM74.


Module TM75.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD0LC_1RA1RE_0LE0RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM75.


Module TM76.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LF_0RD1RA_1RA1RE_1LA1RE_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM76.


Module TM77.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LF_0RD1RA_0LB1RE_1LA1RE_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM77.


Module TM78.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LF_0RD1RA_0LB1RE_1LA0RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM78.


Module TM79.

Definition tm := Eval compute in (TM_from_str "1LB1RA_0RC0RC_0RA1RD_1LE1LF_1LC0LD_---1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0;1;0]).
Definition hL:DH0 := (E,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM79.


Module TM80.

Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC1RE_1LD1RC_0RB0RB_1LA0LF_---1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM80.


Module TM81.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA0LD_1LB0RF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM81.


Module TM82.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA0LD_0LE0RF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM82.


Module TM83.

Definition tm := Eval compute in (TM_from_str "1LB1RA_0LC0RF_0RC1RD_1LE---_1LF0LD_0RA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[0;1;0]).
Definition hL:DH0 := (E,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM83.


Module TM84.

Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC1RE_0LA1RD_1LE0RF_1LA0RB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM84.


Module TM85.

Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC1RE_0LA1RD_1LE1RF_1LA0RB_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM85.


Module TM86.

Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC1RE_1RE1RD_1LE0RF_1LA0RB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM86.


Module TM87.

Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC1RE_1RF1RD_1LE0RF_1LA0RB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM87.


Module TM88.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC---_1LD0LB_0RA1RF_1LF0RB_1LC0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM88.


Module TM89.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_1LB1RF_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM89.


Module TM90.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC1RE_0LA1RD_1LE0RF_1LA0RB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM90.


Module TM91.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC0RE_1LE0LD_1LC---_0RA1RB_1LB0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM91.


Module TM92.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RD_1LD0LB_0RE0LD_1RB1RF_1LB0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM92.


Module TM93.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RD_1LD0LB_0RE0LD_1RB1RF_0LF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM93.


Module TM94.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC1RF_0LA1RD_0LD1RE_1LF---_1LA0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM94.


Module TM95.

Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC1RE_0LA1RD_1LE1RF_1LA0RB_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM95.


Module TM96.

Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC1RE_1RE1RD_1LE0RF_1LA0RB_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM96.


Module TM97.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_1LB1RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM97.


Module TM98.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_0LE0RF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM98.


Module TM99.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_0LE1RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM99.


Module TM100.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC1RD_1LD1RC_1LE0RB_0RD0LF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM100.


Module TM101.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC1RE_0LA1RD_1LE1RD_1LA0RB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM101.


Module TM102.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC1RE_1LD1RC_0RB0RB_1LA0RB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM102.


Module TM103.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC1RE_1RF1RD_1LE1RD_1LA0RB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM103.


Module TM104.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC0RE_1LE0LD_1LC---_0RA1RB_1LB1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM104.


Module TM105.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RD_1LD0LB_0RE1RB_0LC1RF_1LB0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM105.


Module TM106.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_1LB0RF_1RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM106.


Module TM107.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_0LE0RF_1RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;0]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM107.


Module TM108.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC1RF_0LA1RD_0LD0RE_1RF---_1LA0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;0]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[0;1;0;0;1].

Definition d0 := <[0;1;0;0].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM108.


Module TM109.

Definition tm := Eval compute in (TM_from_str "1RB1LC_0RC0RF_1LD0LA_1RD1RE_1LC0RB_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[0;1;1]).
Definition hL:DH0 := (C,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[1;1;0;1;1].

Definition d0 := <[1;1;0;1].
Definition d1 := <[1;1;1;1].
Definition d1' := [0;1;0;1].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[1],1)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM109.


Module TM110.

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RB1RC_1LA0RE_1RE1LA_0RA0RF_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[0;1;1]).
Definition hL:DH0 := (A,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[1;1;0;1;1].

Definition d0 := <[1;1;0;1].
Definition d1 := <[1;1;1;1].
Definition d1' := [0;1;0;1].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM110.


Module TM111.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC0LE_1RC1RA_0RB0RF_1RD1LB_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[0;1;1]).
Definition hL:DH0 := (B,[1;0;1]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[1;1;0;1;1].

Definition d0 := <[1;1;0;1].
Definition d1 := <[1;1;1;1].
Definition d1' := [0;1;0;1].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (2,[],6)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM111.


Module TM112.

Definition tm := Eval compute in (TM_from_str "1RB1RD_0RC0RF_1LD1RA_0LE---_1LB0LF_0RC1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[1]).
Definition hL:DH0 := (F,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[1;1;0;1;0].

Definition d0 := <[1;1;0;0].
Definition d1 := <[1;0;1;0].
Definition d1' := [0;1;0;1].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],4)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM112.


Module TM113.

Definition tm := Eval compute in (TM_from_str "1RB1RD_0RC0RF_1LD1RA_0LE---_1LB0LF_0RC1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[1]).
Definition hL:DH0 := (F,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[1;1;0;1;0].

Definition d0 := <[1;1;0;0].
Definition d1 := <[1;0;1;0].
Definition d1' := [0;1;0;1].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],4)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM113.


Module TM114.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC---_1LD0LF_0RA0RF_1RD1RB_0RA1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (F,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[1;1;0;1;0].

Definition d0 := <[1;1;0;0].
Definition d1 := <[1;0;1;0].
Definition d1' := [0;1;0;1].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM114.


Module TM115.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC---_1LD0LF_0RA0RF_1RD1RB_0RA1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (F,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[1;1;0;1;0].

Definition d0 := <[1;1;0;0].
Definition d1 := <[1;0;1;0].
Definition d1' := [0;1;0;1].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM115.


Module TM116.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC0RF_1LE1RD_1RB1RE_0LA---_0RC1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[1]).
Definition hL:DH0 := (F,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[1;1;0;1;0].

Definition d0 := <[1;1;0;0].
Definition d1 := <[1;0;1;0].
Definition d1' := [0;1;0;1].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],0)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM116.


Module TM117.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC0RF_1LE1RD_1RB1RE_0LA---_0RC1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[1]).
Definition hL:DH0 := (F,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;0;1].
Definition w1 := [0;1;1;0;1].
Definition w1' := <[1;1;0;1;0].

Definition d0 := <[1;1;0;0].
Definition d1 := <[1;0;1;0].
Definition d1' := [0;1;0;1].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;0;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - remember (w1 ^^ v3 *> [0; 1; 1] *> const 0) as tg.
    replace (const 0) with (z0^^(v3) *> [0]^^3 *> const 0).
    2: repeat rewrite lpow_all0; solve_const0_eq.
    subst tg.
    rewrite <-lpow_shift.
    eapply @segRLs_sideRLs_concat with (ls2:=hRL).
    + epose proof (UC2.Incs tm hR hL z0 [0;1;1;0;0] w1 w1' _ _ _ _ (v3) 1) as H0.
      Unshelve. all: execute.
      applys_eq H0.
      simpl_tape.
      reflexivity.
    + econstructor.
      2: constructor.
      execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],0)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM117.


Module TM118.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LE_1RD1RC_0LB1RE_1RA0RF_1LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[1]).
Definition hL:DH0 := (B,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;1;0;1;0].
Definition w1 := [1;0;1;1;0].
Definition w1' := <[1;1;1;0;1].

Definition d0 := <[1;1;1;0].
Definition d1 := <[1;1;1;1].
Definition d1' := [1;0;1;0].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition wR1 := [1;0;1;1;0; 1;0;1;0;1;1;0].
Definition wR1' := [1;0;1;1;0; 1;0;1;0;1;0;1;1;0].

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;1;0;1;0; 1;0;1;1;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> wR1 *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,wR1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  cbn[lpow]. cbn[app].
  eapply @sideRLseq_S with (r2:=w1*>w1*>const 0); execute.
  eapply @sideRLseq_S with (r2:=d1'*>wR1*>const 0); execute.
  clear Heqv3.
  induction v3.
  1: constructor.
  replace (S v3) with (v3+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHv3.
  cbn[lpow]. cbn[app].
  eapply @sideRLseq_S.
  2: constructor.
  execute.
  es.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[1],1)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM118.


Module TM119.

Definition tm := Eval compute in (TM_from_str "1LB---_0LC1RE_1LD0LE_1RB1RD_1RF0RA_1LC0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[1]).
Definition hL:DH0 := (C,[0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;1;0;1;0].
Definition w1 := [1;0;1;1;0].
Definition w1' := <[1;1;1;0;1].

Definition d0 := <[1;1;1;0].
Definition d1 := <[1;1;1;1].
Definition d1' := [1;0;1;0].
Definition d1a := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition wR1 := [1;0;1;1;0; 1;0;1;0;1;1;0].
Definition wR1' := [1;0;1;1;0; 1;0;1;0;1;0;1;1;0].

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;1;0;1;0; 1;0;1;1;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> wR1 *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,wR1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  cbn[lpow]. cbn[app].
  eapply @sideRLseq_S with (r2:=w1*>w1*>const 0); execute.
  eapply @sideRLseq_S with (r2:=d1'*>wR1*>const 0); execute.
  clear Heqv3.
  induction v3.
  1: constructor.
  replace (S v3) with (v3+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHv3.
  cbn[lpow]. cbn[app].
  eapply @sideRLseq_S.
  2: constructor.
  execute.
  es.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],2)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM119.


Module TM120.

Definition tm := Eval compute in (TM_from_str "1LB0RB_0LC1LF_0RD0LE_0RE---_1LA1RF_0RA1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[1;1]).
Definition hL:DH0 := (E,[0;0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;0;1;1].
Definition w0' := [1;1;0;1;1].
Definition w1 := [1;1;1;0;0].
Definition w1' := <[1;1;0;0;0].

Definition d0 := <[1;1;0;0].
Definition d1 := <[1;0;0;0].
Definition d1' := [1;1;0;0].
Definition d0' := [0;0;1;1].
Definition d1a := [] *> const 0.

Lemma w0'_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL^^(1+n)) (w0) (w1).
Proof.
  cbn.
  eapply @segRLs_S with (w2:=w0'); execute.
  eapply @segRLs_S' with (w2:=w1') (w3:=w1); execute.
  eapply @segRLs_wall with (w':=w1'); execute.
Qed.

Lemma d0'_Inc n:
  segRLs tm (hRL^^(1+n)) (hRL^^(2+n*2)) d0' d1'.
Proof.
  do 2 rewrite lpow_add.
  eapply @segRLs_lrcons with (h3:=hR) (h4:=hL) (ls2:=[(hL,hR)]) (w3:=d0) (w4:=d1) (w5:=d1').
  1,2: execute.
  1: econstructor.
  2: constructor.
  1: execute.
  eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
Qed.

Lemma UC_Inc' n m:
  segRLs tm (hRL^^(n+(1+m))) (hRL^^(1+m)) (w0^^n) (w1^^n).
Proof.
  induction n.
  1: eapply segRLs_nil.
  replace (S n+(1+m)) with (2+(n+m)) by lia.
  cbn[lpow].
  repeat rewrite <-app_assoc.
  eapply segRLs_concat.
  1: apply w0'_Inc.
  applys_eq IHn.
  f_equal; lia.
Qed.

Lemma UC_Inc n m:
  segRLs tm (hRL^^(n+(1+m))) (hRL^^(2+m*2)) (w0^^n ++ d0') (w1^^n ++ d1').
Proof.
  induction n.
  1: eapply d0'_Inc.
  replace (S n+(1+m)) with (2+(n+m)) by lia.
  cbn[lpow].
  repeat rewrite <-app_assoc.
  eapply segRLs_concat.
  1: apply w0'_Inc.
  applys_eq IHn.
  f_equal; lia.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 < (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (UC_Inc a (Z.to_nat (Rn n0 ls - Z.of_nat a - 1))).
    1,2: f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;1] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [1;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> w1^^n *> [1;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n:
  sideRLs tm (hRL^^(n+2)) ([1] *> const 0) (d1' *> w1^^(n*2+1) *> [1;1;1] *>const 0).
Proof.
  induction n.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - cbn[Nat.add]. cbn[lpow].
    rewrite <-lpow_shift.
    eapply sideRLs_trans.
    1: apply IHn.
    econstructor.
    2: constructor.
    execute.
    es.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2+1)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (1+Z.to_nat (v1-v2-1)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq UC_Inc'.
  1,2: f_equal; lia.
  applys_eq (RIncs (Z.to_nat (v1-v2-2))).
  1: f_equal; lia.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2 + 1)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],3)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM120.


Module TM121.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0RC_0LD1LF_0RE0LA_0RA---_0RB1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[1;1]).
Definition hL:DH0 := (A,[0;0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;0;1;1].
Definition w0' := [1;1;0;1;1].
Definition w1 := [1;1;1;0;0].
Definition w1' := <[1;1;0;0;0].

Definition d0 := <[1;1;0;0].
Definition d1 := <[1;0;0;0].
Definition d1' := [1;1;0;0].
Definition d0' := [0;0;1;1].
Definition d1a := [] *> const 0.

Lemma w0'_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL^^(1+n)) (w0) (w1).
Proof.
  cbn.
  eapply @segRLs_S with (w2:=w0'); execute.
  eapply @segRLs_S' with (w2:=w1') (w3:=w1); execute.
  eapply @segRLs_wall with (w':=w1'); execute.
Qed.

Lemma d0'_Inc n:
  segRLs tm (hRL^^(1+n)) (hRL^^(2+n*2)) d0' d1'.
Proof.
  do 2 rewrite lpow_add.
  eapply @segRLs_lrcons with (h3:=hR) (h4:=hL) (ls2:=[(hL,hR)]) (w3:=d0) (w4:=d1) (w5:=d1').
  1,2: execute.
  1: econstructor.
  2: constructor.
  1: execute.
  eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
Qed.

Lemma UC_Inc' n m:
  segRLs tm (hRL^^(n+(1+m))) (hRL^^(1+m)) (w0^^n) (w1^^n).
Proof.
  induction n.
  1: eapply segRLs_nil.
  replace (S n+(1+m)) with (2+(n+m)) by lia.
  cbn[lpow].
  repeat rewrite <-app_assoc.
  eapply segRLs_concat.
  1: apply w0'_Inc.
  applys_eq IHn.
  f_equal; lia.
Qed.

Lemma UC_Inc n m:
  segRLs tm (hRL^^(n+(1+m))) (hRL^^(2+m*2)) (w0^^n ++ d0') (w1^^n ++ d1').
Proof.
  induction n.
  1: eapply d0'_Inc.
  replace (S n+(1+m)) with (2+(n+m)) by lia.
  cbn[lpow].
  repeat rewrite <-app_assoc.
  eapply segRLs_concat.
  1: apply w0'_Inc.
  applys_eq IHn.
  f_equal; lia.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 < (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (UC_Inc a (Z.to_nat (Rn n0 ls - Z.of_nat a - 1))).
    1,2: f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;1] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [1;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> w1^^n *> [1;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n:
  sideRLs tm (hRL^^(n+2)) ([1] *> const 0) (d1' *> w1^^(n*2+1) *> [1;1;1] *>const 0).
Proof.
  induction n.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - cbn[Nat.add]. cbn[lpow].
    rewrite <-lpow_shift.
    eapply sideRLs_trans.
    1: apply IHn.
    econstructor.
    2: constructor.
    execute.
    es.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2+1)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (1+Z.to_nat (v1-v2-1)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq UC_Inc'.
  1,2: f_equal; lia.
  applys_eq (RIncs (Z.to_nat (v1-v2-2))).
  1: f_equal; lia.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2 + 1)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],1)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM121.


Module TM122.

Definition tm := Eval compute in (TM_from_str "1LB0RB_0LC0RB_0RD0LE_0RE---_1LA1RF_0RA1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[1;1]).
Definition hL:DH0 := (E,[0;0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;0;1;1].
Definition w0' := [1;1;0;1;1].
Definition w1 := [1;1;1;0;0].
Definition w1' := <[1;1;0;0;0].

Definition d0 := <[1;1;0;0].
Definition d1 := <[1;0;0;0].
Definition d1' := [1;1;0;0].
Definition d0' := [0;0;1;1].
Definition d1a := [] *> const 0.

Lemma w0'_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL^^(1+n)) (w0) (w1).
Proof.
  cbn.
  eapply @segRLs_S with (w2:=w0'); execute.
  eapply @segRLs_S' with (w2:=w1') (w3:=w1); execute.
  eapply @segRLs_wall with (w':=w1'); execute.
Qed.

Lemma d0'_Inc n:
  segRLs tm (hRL^^(1+n)) (hRL^^(2+n*2)) d0' d1'.
Proof.
  do 2 rewrite lpow_add.
  eapply @segRLs_lrcons with (h3:=hR) (h4:=hL) (ls2:=[(hL,hR)]) (w3:=d0) (w4:=d1) (w5:=d1').
  1,2: execute.
  1: econstructor.
  2: constructor.
  1: execute.
  eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
Qed.

Lemma UC_Inc' n m:
  segRLs tm (hRL^^(n+(1+m))) (hRL^^(1+m)) (w0^^n) (w1^^n).
Proof.
  induction n.
  1: eapply segRLs_nil.
  replace (S n+(1+m)) with (2+(n+m)) by lia.
  cbn[lpow].
  repeat rewrite <-app_assoc.
  eapply segRLs_concat.
  1: apply w0'_Inc.
  applys_eq IHn.
  f_equal; lia.
Qed.

Lemma UC_Inc n m:
  segRLs tm (hRL^^(n+(1+m))) (hRL^^(2+m*2)) (w0^^n ++ d0') (w1^^n ++ d1').
Proof.
  induction n.
  1: eapply d0'_Inc.
  replace (S n+(1+m)) with (2+(n+m)) by lia.
  cbn[lpow].
  repeat rewrite <-app_assoc.
  eapply segRLs_concat.
  1: apply w0'_Inc.
  applys_eq IHn.
  f_equal; lia.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 < (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (UC_Inc a (Z.to_nat (Rn n0 ls - Z.of_nat a - 1))).
    1,2: f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;1] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [1;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> w1^^n *> [1;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n:
  sideRLs tm (hRL^^(n+2)) ([1] *> const 0) (d1' *> w1^^(n*2+1) *> [1;1;1] *>const 0).
Proof.
  induction n.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - cbn[Nat.add]. cbn[lpow].
    rewrite <-lpow_shift.
    eapply sideRLs_trans.
    1: apply IHn.
    econstructor.
    2: constructor.
    execute.
    es.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2+1)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (1+Z.to_nat (v1-v2-1)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq UC_Inc'.
  1,2: f_equal; lia.
  applys_eq (RIncs (Z.to_nat (v1-v2-2))).
  1: f_equal; lia.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2 + 1)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],3)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM122.


Module TM123.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0RC_0LD0RC_0RE0LA_0RA---_0RB1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[1;1]).
Definition hL:DH0 := (A,[0;0]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;0;1;1].
Definition w0' := [1;1;0;1;1].
Definition w1 := [1;1;1;0;0].
Definition w1' := <[1;1;0;0;0].

Definition d0 := <[1;1;0;0].
Definition d1 := <[1;0;0;0].
Definition d1' := [1;1;0;0].
Definition d0' := [0;0;1;1].
Definition d1a := [] *> const 0.

Lemma w0'_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL^^(1+n)) (w0) (w1).
Proof.
  cbn.
  eapply @segRLs_S with (w2:=w0'); execute.
  eapply @segRLs_S' with (w2:=w1') (w3:=w1); execute.
  eapply @segRLs_wall with (w':=w1'); execute.
Qed.

Lemma d0'_Inc n:
  segRLs tm (hRL^^(1+n)) (hRL^^(2+n*2)) d0' d1'.
Proof.
  do 2 rewrite lpow_add.
  eapply @segRLs_lrcons with (h3:=hR) (h4:=hL) (ls2:=[(hL,hR)]) (w3:=d0) (w4:=d1) (w5:=d1').
  1,2: execute.
  1: econstructor.
  2: constructor.
  1: execute.
  eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
Qed.

Lemma UC_Inc' n m:
  segRLs tm (hRL^^(n+(1+m))) (hRL^^(1+m)) (w0^^n) (w1^^n).
Proof.
  induction n.
  1: eapply segRLs_nil.
  replace (S n+(1+m)) with (2+(n+m)) by lia.
  cbn[lpow].
  repeat rewrite <-app_assoc.
  eapply segRLs_concat.
  1: apply w0'_Inc.
  applys_eq IHn.
  f_equal; lia.
Qed.

Lemma UC_Inc n m:
  segRLs tm (hRL^^(n+(1+m))) (hRL^^(2+m*2)) (w0^^n ++ d0') (w1^^n ++ d1').
Proof.
  induction n.
  1: eapply d0'_Inc.
  replace (S n+(1+m)) with (2+(n+m)) by lia.
  cbn[lpow].
  repeat rewrite <-app_assoc.
  eapply segRLs_concat.
  1: apply w0'_Inc.
  applys_eq IHn.
  f_equal; lia.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 < (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (UC_Inc a (Z.to_nat (Rn n0 ls - Z.of_nat a - 1))).
    1,2: f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;1] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [1;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> w1^^n *> [1;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RIncs n:
  sideRLs tm (hRL^^(n+2)) ([1] *> const 0) (d1' *> w1^^(n*2+1) *> [1;1;1] *>const 0).
Proof.
  induction n.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - cbn[Nat.add]. cbn[lpow].
    rewrite <-lpow_shift.
    eapply sideRLs_trans.
    1: apply IHn.
    econstructor.
    2: constructor.
    execute.
    es.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2+1)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (1+Z.to_nat (v1-v2-1)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq UC_Inc'.
  1,2: f_equal; lia.
  applys_eq (RIncs (Z.to_nat (v1-v2-2))).
  1: f_equal; lia.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2 + 1)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],1)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM123.


Module TM124.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LD_1RA1RC_1LA1LB_0RC0RF_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (B,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;1;0].
Definition w1 := [1;0;1;0;1].
Definition w1' := <[1;1;1;0;1].

Definition d0 := <[1;1;1;0].
Definition d1 := <[1;1;1;1].
Definition d1' := [1;0;1;0].
Definition d1a(b:bool) := (if b then [1] else [1;1]) *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [1;0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2,false)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM124.


Module TM125.

Definition tm := Eval compute in (TM_from_str "1LB1LC_1LC1RE_1RD0LA_1RB1RD_0RD0RF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[]).
Definition hL:DH0 := (C,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;1;0].
Definition w1 := [1;0;1;0;1].
Definition w1' := <[1;1;1;0;1].

Definition d0 := <[1;1;1;0].
Definition d1 := <[1;1;1;1].
Definition d1' := [1;0;1;0].
Definition d1a(b:bool) := (if b then [1] else [1;1]) *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [1;0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2,true)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM125.


Module TM126.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RC_0RA1RD_1LE---_1LA0LF_1LB1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[]).
Definition hL:DH0 := (F,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;1;0;1].
Definition w1 := [0;1;0;1;1].
Definition w1' := <[1;1;0;1;1].

Definition d0 := <[1;1;0;1].
Definition d1 := <[1;1;1;1].
Definition d1' := [0;1;0;1].
Definition d1a(b:bool) := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2,true)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM126.


Module TM127.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RC_0RA1RD_1LE---_1RA0LF_1LB1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[]).
Definition hL:DH0 := (F,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;1;0;1].
Definition w1 := [0;1;0;1;1].
Definition w1' := <[1;1;0;1;1].

Definition d0 := <[1;1;0;1].
Definition d1 := <[1;1;1;1].
Definition d1' := [0;1;0;1].
Definition d1a(b:bool) := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2,true)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM127.


Module TM128.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LD_1RA1RC_1LA1LB_0RC1RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (B,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;1;0].
Definition w1 := [1;0;1;0;1].
Definition w1' := <[1;1;1;0;1].

Definition d0 := <[1;1;1;0].
Definition d1 := <[1;1;1;1].
Definition d1' := [1;0;1;0].
Definition d1a(b:bool) := (if b then [1] else [1;1]) *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [1;0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2,false)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM128.


Module TM129.

Definition tm := Eval compute in (TM_from_str "1LB1LC_1LC1RE_1RD0LA_1RB1RD_0RD1RF_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[]).
Definition hL:DH0 := (C,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;1;0].
Definition w1 := [1;0;1;0;1].
Definition w1' := <[1;1;1;0;1].

Definition d0 := <[1;1;1;0].
Definition d1 := <[1;1;1;1].
Definition d1' := [1;0;1;0].
Definition d1a(b:bool) := (if b then [1] else [1;1]) *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [1;0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],2,true)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM129.


Module TM130.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC1RB_0LD1RD_0RB1RE_1LA---_1LC1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[]).
Definition hL:DH0 := (F,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;1;0;1].
Definition w1 := [0;1;0;1;1].
Definition w1' := <[1;1;0;1;1].

Definition d0 := <[1;1;0;1].
Definition d1 := <[1;1;1;1].
Definition d1' := [0;1;0;1].
Definition d1a(b:bool) := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (4*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[1],1,true)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM130.


Module TM131.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LF_1RD1RC_0LE1RE_0RC1RA_1LD1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (F,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;1;0;1].
Definition w1 := [0;1;0;1;1].
Definition w1' := <[1;1;0;1;1].

Definition d0 := <[1;1;0;1].
Definition d1 := <[1;1;1;1].
Definition d1' := [0;1;0;1].
Definition d1a(b:bool) := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (1*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],4,true)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM131.


Module TM132.

Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LF_1RD1RC_0LE1RE_0RC1RA_1LD1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (F,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;1;1;0;1].
Definition w1 := [0;1;0;1;1].
Definition w1' := <[1;1;0;1;1].

Definition d0 := <[1;1;0;1].
Definition d1 := <[1;1;1;1].
Definition d1' := [0;1;0;1].
Definition d1a(b:bool) := [] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 3.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (1*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],4,true)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM132.


Module TM133.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1RE_1RA0LD_1LB1LC_0RA0RF_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[]).
Definition hL:DH0 := (C,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;1;0].
Definition w1 := [1;0;1;0;1].
Definition w1' := <[1;1;1;0;1].

Definition d0 := <[1;1;1;0].
Definition d1 := <[1;1;1;1].
Definition d1' := [1;0;1;0].
Definition d1a(b:bool) := (if b then [1] else [1;1]) *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [1;0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6,true)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM133.


Module TM134.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1RB_1LA1RE_1LC1LA_0RB0RF_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[]).
Definition hL:DH0 := (A,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;1;0].
Definition w1 := [1;0;1;0;1].
Definition w1' := <[1;1;1;0;1].

Definition d0 := <[1;1;1;0].
Definition d1 := <[1;1;1;1].
Definition d1' := [1;0;1;0].
Definition d1a(b:bool) := (if b then [1] else [1;1]) *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [1;0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6,false)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM134.


Module TM135.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1RE_1RA0LD_1LB1LC_0RA1RF_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[]).
Definition hL:DH0 := (C,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;1;0].
Definition w1 := [1;0;1;0;1].
Definition w1' := <[1;1;1;0;1].

Definition d0 := <[1;1;1;0].
Definition d1 := <[1;1;1;1].
Definition d1' := [1;0;1;0].
Definition d1a(b:bool) := (if b then [1] else [1;1]) *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [1;0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6,true)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM135.


Module TM136.

Definition tm := Eval compute in (TM_from_str "1LB0RA_1RC0LE_---1RD_1RA0RB_1RD0LF_0LA1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[1;1;0]).
Definition hL:DH0 := (A,[0;0;0]).

Definition hR':DH0 := (D,[1;1]).
Definition hL':DH0 := (D,[1;0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;1;0].
Definition w1 := [1;0;1].
Definition w1' := <[0;1;1].

Definition ld0 := <[1;1;1;1;1;0].
Definition ld1 := <[1;1;1;1;1;1].
Definition ld1' := [0;1;0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[0;1;1; 0;1;1;1;1;1].
Definition d0' := [1; 0;1;0;1;0;1; 1;0].
Definition d1 := <[0;1;1; 1;1;1;1;1;1].
Definition d1' := [1;0;1; 0;1;0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (1 + (Z.to_nat (Rn n0 ls) - a - 1))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 1))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 1) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;1;0; 1;0;1] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> w1^^n *> [1;0; 1;1;0; 1;0;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 3)*2+1))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (3+Z.to_nat (v1-v2-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-3)) as v3.
  clear Heqv3.
  induction v3.
  - econstructor.
    1: execute.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (3+S v3) with (3+v3+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    econstructor.
    2: constructor.
    execute. es.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [1;1;1;1;1] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 3)%Z * 2 + 1)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [1;1;1;1;1] [0;1;0;1;0;1]); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 2.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,[2],0)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM136.


Module TM137.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC0LD_---0LA_1RE0LF_1RA0RB_0LA1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1;1;0]).
Definition hL:DH0 := (A,[0;0;0]).

Definition hR':DH0 := (E,[1;1]).
Definition hL':DH0 := (E,[1;0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;1;0].
Definition w1 := [1;0;1].
Definition w1' := <[0;1;1].

Definition ld0 := <[1;1;1;1;1;0].
Definition ld1 := <[1;1;1;1;1;1].
Definition ld1' := [0;1;0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[0;1;1; 0;1;1;1;1;1].
Definition d0' := [1; 0;1;0;1;0;1; 1;0].
Definition d1 := <[0;1;1; 1;1;1;1;1;1].
Definition d1' := [1;0;1; 0;1;0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (1 + (Z.to_nat (Rn n0 ls) - a - 1))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 1))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 1) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;1;0; 1;0;1] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> w1^^n *> [1;0; 1;1;0; 1;0;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 3)*2+1))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (3+Z.to_nat (v1-v2-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-3)) as v3.
  clear Heqv3.
  induction v3.
  - econstructor.
    1: execute.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (3+S v3) with (3+v3+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    econstructor.
    2: constructor.
    execute. es.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [1;1;1;1;1] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 3)%Z * 2 + 1)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [1;1;1;1;1] [0;1;0;1;0;1]); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 2.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,[2],0)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM137.


Module TM138.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LE_---1RD_1RA0RB_1RD0LF_0LA1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (D,[1;1;0]).
Definition hL:DH0 := (A,[0;0;0]).

Definition hR':DH0 := (D,[1;1]).
Definition hL':DH0 := (D,[1;0]).

Definition hRL:= [(hR,hL)].

Definition w0 := [1;1;0].
Definition w1 := [1;0;1].
Definition w1' := <[0;1;1].

Definition ld0 := <[1;1;1;1;1;0].
Definition ld1 := <[1;1;1;1;1;1].
Definition ld1' := [0;1;0;1;0;1].
Definition ld1a := [1] *> const 0.

Definition d0 := <[0;1;1; 0;1;1;1;1;1].
Definition d0' := [1; 0;1;0;1;0;1; 1;0].
Definition d1 := <[0;1;1; 1;1;1;1;1;1].
Definition d1' := [1;0;1; 0;1;0;1;0;1].

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w1 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (1 + (Z.to_nat (Rn n0 ls) - a - 1))) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + replace (Z.to_nat ((Rn n0 ls - Z.of_nat a) * 2 - 1))%Z with (1+(Z.to_nat ((Rn n0 ls - Z.of_nat a - 1) * 2))%Z) by lia.
      do 2 rewrite lpow_add.
      eapply segRLs_trans.
      2: applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      2: f_equal; try lia.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1'); execute.
      constructor.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 d0' ls *> r = RC w1 d1' ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1',d0'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 d0' ls *> w0^^n *> [1;1;0; 1;0;1] *> const 0).

Definition R1 ls n :=
  (RC w1 d1' ls *> w1^^n *> [1;0; 1;1;0; 1;0;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1,d0',d1'.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1,d0',d1' in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+3 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 3)*2+1))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (3+Z.to_nat (v1-v2-3)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-3)) as v3.
  clear Heqv3.
  induction v3.
  - econstructor.
    1: execute.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (3+S v3) with (3+v3+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    econstructor.
    2: constructor.
    execute. es.
Qed.

Definition S0 k ls n :=
  ld1a <* (ld0)^^k <* ld1 <* [1;1;1;1;1] {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 3 <= Rn (2^k*2-1) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k*2-1) ls - Z.of_nat n - 3)%Z * 2 + 1)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + rewrite <-(Str_app_assoc ld1).
      eapply segRLs_sideRLs_concat.
      1: eapply (@segRLs_wall' _ hL hR hL' hR' [1;1;1;1;1] [0;1;0;1;0;1]); execute.
      eapply segRLs_sideRLs_concat.
      1: eapply (BC.IncsMul2 _ hL' hR' ld0 ld1 ld1'); execute.
      constructor.
    + replace (2^k*2-2) with (2^k*2-1-1) by lia.
      rewrite lrcons_lpow1.
      2: epose proof (Nat.pow_nonzero 2 k); lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold ld0,ld1,ld1a.
    solve_LOverflow.
Qed.

Fixpoint Rn'(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => (Z.of_nat n0)-1
| n::ls0 => ((Rn' n0 ls0) - (Z.of_nat n))*2 - 1
end)%Z.

Lemma Rn'_spec n ls:
  n<>O ->
  Rn' (n) ls = Rn (n-1) ls.
Proof.
  destruct n as [|n].
  1: lia.
  intros _.
  replace (S n - 1) with n by lia.
  induction ls;
  cbn[Rn']; cbn[Rn]; lia.
Qed.

Lemma Rn'_2 n0 ls:
  (Rn' (2*n0) ls =
  (Rn' n0 ls)*2 - Rn' 0 ls)%Z.
Proof.
  induction ls.
  - cbn[Rn']. lia.
  - gen IHls; cbn[Rn']; lia.
Qed.

Definition k0:nat := 2.
Definition config '(k,ls,n) := S0 (k+k0) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 3 <= Rn' (2^(k+k0)*2) ls) /\
  (Rn' (2*2^(k+k0)*2) ls - Rn' (2^(k+k0)*2) ls = Z.of_nat (4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,[2],0)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    pose proof (Nat.pow_nonzero 2 (k+k0)).
    rewrite <-Rn'_spec;
    try lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      pose proof (Nat.pow_nonzero 2 (k+k0)).
      rewrite <-Rn'_spec; try lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn'].
      gen HP1.
      repeat rewrite <-Nat.mul_assoc.
      repeat rewrite Rn'_2.
      lia.
Qed.

End TM138.


Module TM139.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA---_0RF1LF_1RA0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[]).
Definition hL:DH0 := (A,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [0;0;1;0;1].
Definition w1 := [0;1;0;0;1].
Definition w1' := <[0;1;1;0;1].

Definition d0 := <[0;0;0;1].
Definition d1 := <[0;1;0;1].
Definition d1' := [0;1;0;1].
Definition d1a := [1;0;1] *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [0;1] *> RC w0 ls *> r = RC w1 ls *> [0;1] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [0;0;1;0] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^(1+n) *> const 0).

Lemma R_rot ls n:
  R1 ls n = [0;1] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite <-H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2))*2)).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  rewrite lpow_add.
  eapply segRLs_sideRLs_concat.
  - eapply @segRLs_trans with (w2:=d1') (ls2:=hRL).
    + eapply @segRLs_S with (w2:=[0;1;0;0]).
      1: execute.
      eapply @segRLs_S' with (w2:=d1) (w3:=d1').
      1,2: execute.
      constructor.
    + eapply BCR.Incs with (d0:=d0) (d1:=d1); execute.
  - rewrite <-(lpow_all0 z0 (1+v3*2)).
    2: solve_const0_eq.
    eapply segRLs_sideRLs_concat.
    2: rewrite lpow_all0; [constructor|solve_const0_eq].
    epose proof (UC1.Incs' tm hR hL z0 w1 w1' _ _ _ (1+v3*2)).
    applys_eq H0.
    Unshelve. all: execute.
Qed.

Definition S0 k ls n :=
  d1a <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z * 2)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition config '(k,ls,n) := S0 (k+4) ls n.
Definition P '(k,ls,n) :=
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+4))%nat ls) /\
  (Rn (2*2^(k+4)) ls - Rn (2^(k+4)) ls = Z.of_nat (1*4^(k+2))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (0,[],4)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[k ls] n] [HP0 [HP1 HP2]].
  eexists (S k,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM139.


Module TM140.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1RB_1LA1RE_1LC1LA_0RB1RF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[]).
Definition hL:DH0 := (A,[]).

Definition hRL:= [(hR,hL)].

Definition z0 := [0;0;0;0;0].
Definition w0 := [1;0;1;1;0].
Definition w1 := [1;0;1;0;1].
Definition w1' := <[1;1;1;0;1].

Definition d0 := <[1;1;1;0].
Definition d1 := <[1;1;1;1].
Definition d1' := [1;0;1;0].
Definition d1a(b:bool) := (if b then [1] else [1;1]) *> const 0.

Fixpoint RC(w:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w ls0) ++ ((w^^n) ++ d1')
end.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n))*2
end)%Z.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 ls) (RC w1 ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    eapply segRLs_concat.
    + replace (Z.to_nat (Rn n0 ls)) with (a + (Z.to_nat (Rn n0 ls) - a)) by lia.
      eapply (UC1.Incs tm hR hL w0 w1 w1'); execute.
    + applys_eq (BCR.Incs tm hR hL d0 d1 d1'); execute.
      f_equal; lia.
Qed.

Lemma RC_rot ls r:
  [1;0] *> RC w0 ls *> r = RC w1 ls *> [1;0] *> r.
Proof.
  gen r.
  induction ls; intros.
  1: reflexivity.
  cbn.
  gen IHls.
  unfold w0,w1,d1'.
  repeat rewrite Str_app_assoc.
  cbn.
  intros IHls.
  rewrite IHls.
  simpl_rotate.
  reflexivity.
Qed.

Definition R0 ls n :=
  (RC w0 ls *> w0^^n *> [1;0;1;1] *> const 0).

Definition R1 ls n :=
  (RC w1 ls *> w1^^n *> [1;0;1;0;1;1] *> const 0).

Lemma R_rot ls n:
  R1 ls n = [1;0] *> R0 ls n.
Proof.
  unfold R0,R1,w0,w1.
  simpl_tape.
  epose proof RC_rot.
  unfold w0,w1 in H; cbn in H.
  rewrite H.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R_spec n0 ls n:
  ((Z.of_nat n)+2 <= (Rn n0 ls))%Z ->
  sideRLs tm (hRL^^n0) (R0 ls n)
  (R1 (n::ls) ((Z.to_nat (Rn n0 ls - (Z.of_nat n) - 2)))).
Proof.
  unfold R0,R1.
  intros H.
  cbn[RC].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Rn_spec; lia.
  remember (Rn n0 ls) as v1.
  remember (Z.of_nat n) as v2.
  replace (Z.to_nat v1) with (Z.to_nat v2 + (2+Z.to_nat (v1-v2-2)%Z)) by lia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (UC1.Incs tm hR hL w0 w1 w1').
  1,2: f_equal; lia.
  1,2,3: execute.
  remember (Z.to_nat (v1-v2-2)) as v3.
  clear Heqv3.
  rewrite (Nat.add_comm 2).
  induction v3.
  - cbn.
    econstructor.
    1: execute.
    econstructor.
    1: execute.
    constructor.
  - replace (S v3+2) with (v3+2+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHv3.
    cbn.
    econstructor.
    2: constructor.
    unfold w1.
    execute; es.
Qed.

Definition S0 k ls n b :=
  d1a b <* (d0)^^k {{{ (hR,R) }}} R0 ls n.

Lemma BigStep k ls n b:
  (Z.of_nat n + 2 <= Rn (2 ^ k) ls)%Z ->
  (S0 k ls n b) -[ tm ]->+
  (S0 (S k) (n::ls) (Z.to_nat (Rn (2^k) ls - Z.of_nat n - 2)%Z) (negb b)).
Proof.
  intros H.
  eapply progress_trans.
  - unfold S0.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR d0 d1 d1'); execute.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply R_spec.
      lia.
  - rewrite R_rot.
    unfold S0.
    unfold d0,d1,d1a.
    destruct b;
    solve_LOverflow.
Qed.

Lemma Rn_2 n0 ls:
  (Rn (2*n0) ls =
  (Rn n0 ls)*2 - Rn 0 ls)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Definition k0 := 4.
Definition config_t:Type := (nat*(list nat)*nat*bool).
Definition config (x : config_t) :=
  let '(k,ls,n,b):=x in
  S0 (k+k0) ls n b.
Definition P (x : config_t) :=
  let '(k,ls,n,_):=x in
  (
  (Z.of_nat n + 2 <= Rn (2 ^ (k+k0))%nat ls) /\
  (Rn (2*2^(k+k0)) ls - Rn (2^(k+k0)) ls = Z.of_nat (2*4^(k+1))) /\
  True)%Z.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=(config (1,[],6,false)%nat)).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; try lia.
  unfold P.
  intros [[[k ls] n] b] [HP0 [HP1 HP2]].
  eexists (S k,_,_,_).
  split.
  - unfold config.
    eapply BigStep.
    lia.
  - repeat split.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      lia.
    + cbn[Nat.add].
      cbn[Nat.pow].
      cbn[Rn].
      gen HP1.
      repeat rewrite Rn_2.
      lia.
Qed.

End TM140.
