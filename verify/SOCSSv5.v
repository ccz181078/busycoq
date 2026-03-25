From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal ES_v3.
From BusyCoq Require Import DivModCases.
Require Import String List PeanoNat NArith Lia.
Open Scope sym.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Ltac cat :=
  eapply segRLs_sideRLs_concat ||
  eapply segRLs_concat.

Ltac tr :=
  eapply sideRLs_trans ||
  eapply segRLs_trans.

Ltac cat1 H :=
  cat; [apply H|].

Ltac wal := apply segRLs_wall''; esc.

Ltac am a a' k b b' :=
  applys_eq (segRLs_addmul_v2 a a' k b b'); unfold DH0; flia; esc.

Ltac seg_nil :=
  repeat (rewrite Nat.mul_1_r || rewrite Nat.add_sub);
  apply segRLs_nil.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;1].
Notation d0 := [0;0;0;0;0].
Notation d1 := [1;0;0;0;0].
Notation d1' := [0;0;0;0;1].


Notation hR := (A,[0]).
Notation hRx := (C,[]).
Notation hL := (C,[0]).
Notation h := [(hR,hL)].
Notation hx := [(hRx,hL)].
Notation hR' := (A,[]).
Notation hL' := (B,[]).
Notation h' := [(hR',hL')].

Open Scope nat.

Lemma ld_Incs k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  am 1 2 k 0 0.
Qed.

Lemma d0_Incs k:
  segRLs tm (h'^^(k*2)) (h'^^k) d0 d0.
Proof.
  am 2 1 k 0 0.
Qed.

Lemma d01_Incs k:
  segRLs tm (h'^^(k*2+1)) (h'^^k) d0 d1.
Proof.
  am 2 1 k 1 0.
Qed.

Lemma d10_Incs k:
  segRLs tm (h'^^(k*2+1)) (h'^^(k+1)) d1 d0.
Proof.
  am 2 1 k 1 1.
Qed.

Lemma d1_Incs k:
  segRLs tm (h'^^(k*2)) (h'^^k) d1 d1.
Proof.
  am 2 1 k 0 0.
Qed.

Lemma m0_Incs k:
  segRLs tm (h^^k) (h'^^k) [] [].
Proof.
  wal.
Qed.

Lemma lds_Incs k n:
  segRLs tm (h^^k) (h^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  induction n.
  1: seg_nil.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  cat1 IHn.
  rewrite Nat.pow_add_r.
  applys_eq ld_Incs; flia.
Qed.

Lemma lds_Incs' k n:
  segRLs tm (h^^k) (h'^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  rewrite <-(app_nil_r (ld^^n)).
  cat1 lds_Incs.
  wal.
Qed.

Lemma d0s_Incs k n:
  segRLs tm (h'^^(k*2^n)) (h'^^k) (d0^^n) (d0^^n).
Proof.
  gen k.
  induction n; intros.
  - seg_nil.
  - cbn[Nat.pow lpow].
    cat.
    2: apply IHn.
    applys_eq d0_Incs; flia.
Qed.

Lemma d01s_Incs k n:
  segRLs tm (h'^^((k+1)*2^n-1)) (h'^^k) (d0^^n) (d1^^n).
Proof.
  gen k.
  induction n; intros.
  - seg_nil.
  - cbn[Nat.pow lpow].
    cat.
    2: apply IHn.
    applys_eq d01_Incs; flia.
Qed.

Lemma d1'_Incs k:
  k<>O ->
  segRLs tm (h'^^(k*2)) (h'^^(k)) d1' d0.
Proof.
  intro.
  am 2 1 (k-1) 2 1.
Qed.

Lemma d1's_Incs k n:
  k<>O ->
  segRLs tm (h'^^(k*2^n)) (h'^^k) (d1'^^n) (d0^^n).
Proof.
  gen k.
  induction n; intros.
  - seg_nil.
  - cbn[Nat.pow lpow].
    cat.
    2: apply IHn; lia.
    applys_eq (d1'_Incs (k*2^n)); flia.
Qed.


Open Scope sym.

Definition RC0 n := (ld^^n *> d0^^n *> d1 *> 0inf).
Definition RC0' n := (ld^^(n+1) *> d1 *> d0^^n *> [0;1] *> 0inf).

Lemma RC0_Rst n:
  [1] *> RC0 (1+n) = RC0' n.
Proof.
  ut; st; simpl_rotate; reflexivity.
Qed.

Definition RC1 n := ld^^(n+1)*>d1*>d0^^n*>[1;1]*>0inf.
Definition RC1' n := ld^^(n+2)*>d0^^n*>[0;0;0;0;1;1]*>0inf.

Lemma RC0_OvIncs n:
  sideRLs tm (h^^1) (RC0' n) (RC1 n).
Proof.
  cat1 lds_Incs'.
  rewrite Nat.pow_add_r,Nat.mul_assoc.
  cat1 d1_Incs.
  cat1 d0s_Incs.
  esc.
Qed.

Lemma RC1_Rst n:
  [1] *> RC1 n = RC1' n.
Proof.
  ut; st; simpl_rotate; reflexivity.
Qed.

Ltac rw_pa := repeat rewrite Nat.pow_add_r.

Definition RC2 n := ld^^(n+2)*>d0^^n*>d0*>d1*>d1*>0inf.
Definition RC2' n := ld^^(n+2)*>d1*>d0^^n*>[0]*>d1*>d1*>0inf.

Lemma RC1_OvIncs n:
  sideRLs tm (h^^1) (RC1' n) (RC2 n).
Proof.
  cat1 lds_Incs'.
  replace (1*2^(n+2)) with (4*2^n) by (rw_pa; lia).
  cat1 d0s_Incs.
  esc.
Qed.

Lemma RC2_Rst n:
  [1] *> RC2 n = RC2' n.
Proof.
  ut; st; simpl_rotate; reflexivity.
Qed.

Definition RC3 n :=
  ld^^(n*2+2)*>ld*>ld^^(n*5+3)*>ld*>ld*>[]*>d1*>d1*>d0*>d1^^(n*5+2)*>d0*>d1*>0inf.

Lemma RC2_OvIncs_0 n:
  sideRLs tm (h^^1) (RC2' (n*2)) (RC3 n).
Proof.
  cat1 lds_Incs.
  eassert (I1:sideRLs tm (h^^(((1+1)*2^(n*2)-1)*2)) ([]*>d1*>d0^^(n*2)*>[0]*>d1*>d1*>0inf) ([]*>d1*>d1^^(n*2)*>[1]*>d1*>d1*>0inf)). {
    cat1 m0_Incs.
    cat1 d1_Incs.
    cat1 d01s_Incs.
    esc.
  }
  replace (1*2^(n*2+2)) with (((1+1)*2^(n*2)-1)*2+2) by (rw_pa; lia).
  rewrite lpow_add.
  tr.
  1: apply I1.
  clear I1.
  eapply @segRLs_sideRLs_concat with (w1:=[1]) (ls2:=hx++h^^3).
  1: esc.
  eapply @sideRLs_trans with (r2:=ld^^(n*5+3)*>[0;0;0;1]*>0inf).
  1: esx.
  cat1 lds_Incs.
  replace (3*2^(n*5+3)) with (2+((2+1)*2^(n*5+2)-1)*2) by (rw_pa; lia).
  eapply sideRLs_trans_add with (w3:=ld*>ld*>[]*>d1*>d1*>d0*>d0^^(n*5+2)*>0inf).
  1: rewrite lpow_all0 by solve_const0_eq.
  1: esc.
  do 2 cat1 ld_Incs.
  cat1 m0_Incs.
  do 2 cat1 d1_Incs.
  cat1 d0_Incs.
  cat1 d01s_Incs.
  esc.
Qed.

Definition RC4 n :=
  ld^^(n*2+1+2)*>ld*>ld^^(n*5+5)*>[]*>d1*>d0*>d0^^(n*5+3)*>d1*>d1*>0inf.

Lemma RC2_OvIncs_1 n:
  sideRLs tm (h^^1) (RC2' (n*2+1)) (RC4 n).
Proof.
  cat1 lds_Incs.
  eassert (I1:sideRLs tm (h^^(((1+1)*2^(n*2+1)-1)*2)) ([]*>d1*>d0^^(n*2+1)*>[0]*>d1*>d1*>0inf) ([]*>d1*>d1^^(n*2+1)*>[1]*>d1*>d1*>0inf)). {
    cat1 m0_Incs.
    cat1 d1_Incs.
    cat1 d01s_Incs.
    esc.
  }
  replace (1*2^(n*2+1+2)) with (((1+1)*2^(n*2+1)-1)*2+2) by (rw_pa; lia).
  rewrite lpow_add.
  tr.
  1: apply I1.
  clear I1.
  eapply @segRLs_sideRLs_concat with (w1:=[1]) (ls2:=hx++h^^3).
  1: esc.
  eapply @sideRLs_trans with (r2:=ld^^(n*5+5)*>[1;0;0;0;1]*>0inf).
  1: esx.
  cat1 lds_Incs.
  replace (3*2^(n*5+5)) with (2+(((2+1)*2^(n*5+3)-1)*2+1)*2) by (rw_pa; lia).
  eapply sideRLs_trans_add with (w3:=[]*>d1*>d1*>d0^^(n*5+3)*>0inf).
  1: rewrite lpow_all0 by solve_const0_eq.
  1: esc.
  cat1 m0_Incs.
  cat1 d1_Incs.
  cat1 d10_Incs.
  rewrite Nat.sub_add by lia.
  cat1 d0s_Incs.
  esc.
Qed.

Definition RC3' n :=
  ld^^(n*7+9)*>d1'*>d0*>d1'^^(n*5+2)*>d0*>d1'*>0inf.

Lemma RC3_Rst n:
  [1] *> RC3 n = RC3' n.
Proof.
  unfold RC3'.
  replace (n*7) with (n*2+n*5) by lia.
  ut; st; simpl_rotate; reflexivity.
Qed.

Lemma RC3_OvIncs n:
  sideRLs tm (h^^1) (RC3' n) (RC0 (n*7+9)).
Proof.
  replace (RC0 (n*7+9)) with (ld^^(n*7+9)*>d0*>d0*>d0^^(n*5+2)*>d0*>d0*>d0^^(n*2+3)*>d1*>0inf).
  2:{
    ut.
    replace (n*7) with (n*5+n*2) by lia.
    st; simpl_rotate; reflexivity.
  }
  cat1 lds_Incs'.
  replace (1*2^(n*7+9)) with ((0+1*2^(n*2+3))*2*2*(2^(n*5+2))*2*2) by (replace (n*7) with (n*2+n*5) by lia; rw_pa; lia).
  cat1 d1'_Incs; [lia|].
  cat1 d0_Incs.
  cat1 d1's_Incs; [lia|].
  cat1 d0_Incs.
  cat1 d1'_Incs; [lia|].
  eapply @sideRLs_trans_add with (w3:=d0^^(n*2+3)*>0inf).
  1: rewrite lpow_all0 by solve_const0_eq.
  1: esc.
  cat1 d0s_Incs.
  esc.
Qed.

Definition RC4' n :=
  ld^^(n*7+10)*>d0^^(n*5+4)*>[0;0;0;0]*>d1*>d1*>0inf.

Lemma RC4_Rst n:
  [1] *> RC4 n = RC4' n.
Proof.
  unfold RC4'.
  replace (n*7) with (n*2+n*5) by lia.
  ut; st; simpl_rotate; reflexivity.
Qed.

Lemma RC4_OvIncs n:
  sideRLs tm (h^^1) (RC4' n) (RC0 (n*7+10)).
Proof.
  replace (RC0 (n*7+10)) with (ld^^(n*7+10)*>d0^^(n*5+4)*>d0*>d0*>d0*>d0^^(n*2+3)*>d1*>0inf).
  2:{
    ut.
    replace (n*7) with (n*5+n*2) by lia.
    st; simpl_rotate; reflexivity.
  }
  cat1 lds_Incs'.
  replace (1*2^(n*7+10)) with (1*2^(n*2+6)*2^(n*5+4)) by (replace (n*7) with (n*2+n*5) by lia; rw_pa; lia).
  cat1 d0s_Incs.
  replace (1*2^(n*2+6)) with (4+((1*2^(n*2+3)-1)*2+1)*2*2) by (rw_pa; lia).
  eapply @sideRLs_trans_add with (w3:=d0*>d0*>d1*>d0^^(n*2+3)*>0inf).
  1: rewrite lpow_all0 by solve_const0_eq.
  1: esc.
  do 2 cat1 d0_Incs.
  cat1 d10_Incs.
  rewrite Nat.sub_add by lia.
  cat1 d0s_Incs.
  esc.
Qed.

Notation lh := (0inf<*<[1;1]).

Lemma BigStep r r':
  sideRLs tm (h^^1) r r' ->
  lh {{{ (hR,R) }}} r -->+
  lh {{{ (hR,R) }}} [1]*>r'.
Proof.
  intros.
  eapply sideRLs_1 in H.
  follow10 H.
  er.
Qed.

Definition S' n :=
  lh {{{ (hR,R) }}} RC0' (n).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 8).
  1: esx.
  eapply progress_nonhalt_simple.
  intros n.
  unfold S'.
  destruct (mod2 n); subst.
  - eexists.
    eapply progress_trans; [apply BigStep,RC0_OvIncs|].
    rewrite RC1_Rst.
    eapply progress_trans; [apply BigStep,RC1_OvIncs|].
    rewrite RC2_Rst.
    eapply progress_trans; [apply BigStep,RC2_OvIncs_0|].
    rewrite RC3_Rst.
    eapply progress_evstep_trans; [apply BigStep,RC3_OvIncs|].
    replace (a*7+9) with (1+(a*7+8)) by lia.
    rewrite RC0_Rst.
    finish.
  - eexists.
    eapply progress_trans; [apply BigStep,RC0_OvIncs|].
    rewrite RC1_Rst.
    eapply progress_trans; [apply BigStep,RC1_OvIncs|].
    rewrite RC2_Rst.
    rewrite Nat.add_comm.
    eapply progress_trans; [apply BigStep,RC2_OvIncs_1|].
    rewrite RC4_Rst.
    eapply progress_evstep_trans; [apply BigStep,RC4_OvIncs|].
    replace (a*7+10) with (1+(a*7+9)) by lia.
    rewrite RC0_Rst.
    finish.
Qed.

End TM1.

