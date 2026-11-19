From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal ES_v3 DivModCases.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RB_1RD0LA_0RA0RD_0RF0RA_1RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[]).
Notation hL := (B,[1;0;0;1]).
Notation h := [(hR,hL)].

Definition RD n := [1;0;0;1;1;1;0;0;1] ++ [1;0;0;1;1;0;0;1]^^n.

Lemma RD_Incs k n:
  segRLs tm (h^^k) (h^^(k*3)) (RD n) (RD (k+n)).
Proof.
  gen n.
  induction k; intros.
  - esx.
  - cbn[Nat.mul lpow].
    rewrite lpow_add.
    eapply segRLs_trans.
    2: applys_eq (IHk (S n)); flia.
    ut; esx.
Qed.

Notation rh := ([1]*>0inf).

Lemma rh_Incs k:
  sideRLs tm (h^^k) rh rh.
Proof.
  apply sideRLs_wall.
  esx.
Qed.

Definition RD1 n := [1;0;0;1;0;1] ++ [1;0;0;1]^^n.

Lemma RD1_Incs n:
  segRLs tm (h^^n) [] (RD1 n) (RD1 0).
Proof.
  induction n.
  - esx.
  - cbn[lpow].
    eapply @segRLs_trans with (ls2:=[]).
    2: apply IHn.
    ut; esx.
Qed.

Lemma RD1_Ov a b r:
  sideRLs tm (h^^2) (RD1 0 *> RD a *> RD (3+b) *> r) (RD (1+a) *> RD 1 *> RD1 (b*2) *> r).
Proof.
  ut; es' a b & r.
Qed.

Lemma RD1_Ov_rh:
  sideRLs tm (h^^2) (RD1 0 *> rh) (RD 0 *> rh).
Proof.
  esc.
Qed.

Inductive RIncs: nat->(list nat)->(list nat)->Prop :=
| RIncs_S a b k0 ls ls':
  b*2+2 <= k0*9 ->
  RIncs (k0*9-(b*2+2)) ls ls' ->
  RIncs k0 (a::3+b::ls) (k0+(1+a)::k0*3+1::ls')
| RIncs_O k0:
  RIncs k0 [] [k0].

Fixpoint RC ls :=
match ls with
| [] => rh
| n::ls => RD n *> RC ls
end.

Lemma RIncs_spec k0 ls ls':
  RIncs k0 ls ls' ->
  sideRLs tm (h^^(2+k0)) (RD1 0 *> RC ls) (RC ls').
Proof.
  intro H.
  induction H; cbn[RC].
  - rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply RD1_Ov.
    eapply segRLs_sideRLs_concat.
    1: apply RD_Incs.
    eapply segRLs_sideRLs_concat.
    1: apply RD_Incs.
    replace (k0*3*3) with (b*2+(k0*9-b*2)) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: applys_eq IHRIncs; flia.
    eapply segRLs_sideRLs_concat.
    1: apply RD1_Incs.
    esx.
  - rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply RD1_Ov_rh.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (RD_Incs k0 0); flia.
    apply rh_Incs.
Qed.

Notation lh := (0inf<*<[1;0;1;0;1;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;1;0;1;0;1;0;1;0;1;0;1;0]).
Notation lh' := (0inf<*<[1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;1;0;1;0]).

Lemma LIncs:
  sideRLs (flip tm) ([(hL,hR)]^^3) lh' lh.
Proof.
  esc.
Qed.

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh' {{{ (hR,R) }}} RD1 0 *> RD 1 *> r.
Proof.
  ut; es' & r.
Qed.

Definition Config ls :=
  lh {{{ (hL,L) }}} RC ls.

Lemma BigStep ls ls':
  RIncs 2 (1%nat::ls) ls' ->
  Config ls -->+ Config ls'.
Proof.
  intros I1.
  apply RIncs_spec in I1.
  unfold Config.
  cbn[RC] in I1.
  follow LRst.
  apply (sideRLs_concat (LIncs) I1).
Qed.

Inductive WF: nat->(list nat)->Prop :=
| WF_S k0 ls:
  WF (k0*12+14) ls ->
  WF (k0*2+2) (k0+1::3+(k0*3+1)::ls)
| WF_O k0 b
  (Hb: b<=k0*9+1):
  WF (k0*2+2) (k0+1::3+b::[]).

Lemma WF_S' k0 ls:
  WF (k0*2+2) (k0+1::ls) ->
  exists ls',
  RIncs (k0*2+2) (k0+1::ls) ls' /\
  WF (k0*2+2) (k0+1::ls').
Proof.
  gen k0.
  remember (length ls) as len.
  gen ls.
  induction len using lt_wf_ind; intros.
  subst.
  inverts H0.
  2:{
    replace k1 with k0 in * by lia.
    clear H2 H3 H.
    eexists; split.
    - ec; [lia|].
      ec.
    - applys_eq WF_S.
      1: flia.
      pose proof O as b'.
      applys_eq (WF_O (k0*6+6) (k0*18+13-(b*2))); flia.
  }
  replace k1 with k0 in * by lia.
  clear H1 H2.
  pose proof H3 as HWF.
  replace (k0*12+14) with ((k0*6+6)*2+2) in HWF by lia.
  inverts H3.
  - replace k2 with (k0*6+6) in * by lia.
    clear H0.
    eapply H in HWF.
    3: reflexivity.
    2: cbn; lia.
    clear H.
    destruct HWF as [ls' [I1 I2]].
    eexists; split.
    + ec; [lia|].
      applys_eq I1; flia.
    + applys_eq (WF_S k0).
      1: flia.
      applys_eq I2; flia.
  - replace k2 with (k0*6+6) in * by lia.
    clear H1 H.
    eexists; split.
    + ec; [lia|].
      ec; [lia|].
      ec.
    + applys_eq (WF_S).
      1: flia.
      applys_eq (WF_S (k0*6+6)).
      1,2: flia.
      applys_eq (WF_O ((k0*6+6)*6+6) (k0*108+121-b*2)); flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=Config [4]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun x => (WF 2 (1::x))%nat).
  2: apply (WF_O 0 1); lia.
  intros x HWF.
  eapply (WF_S' 0) in HWF.
  destruct HWF as [x' [I1 I2]].
  eexists; split.
  - apply BigStep,I1.
  - apply I2.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC0RC_0LA1RA_1LE0RC_0LF---_0LD1LC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[1]).
Notation hL := (C,[1;0;1;1]).
Notation h := [(hR,hL)].

Definition RD n := [1;1;1] ++ [0;1;1]^^n.

Lemma RD_Incs k n:
  segRLs tm (h^^k) (h^^(k*2)) (RD n) (RD (k+n)).
Proof.
  gen n.
  induction k; intros.
  - esx.
  - cbn[Nat.mul lpow].
    rewrite lpow_add.
    eapply segRLs_trans.
    2: applys_eq (IHk (S n)); flia.
    ut; esx.
Qed.

Definition rh(b:bool) := ((if b then [0;1] else [1])*>0inf).

Lemma rh_Incs k n b:
  sideRLs tm (h^^k) (RD n *> rh b) (RD n *> rh b).
Proof.
  apply sideRLs_wall.
  destruct b; esx.
Qed.

Lemma r0inf_Incs k:
  sideRLs tm (h^^k) 0inf 0inf.
Proof.
  apply sideRLs_wall.
  esx.
Qed.

Lemma w011_Incs k:
  segRLs tm (h^^k) (h^^k) [0;1;1] [0;1;1].
Proof.
  apply segRLs_wall''.
  esc.
Qed.

Definition RD1 n := [0;1;1;1] ++ [0;1;1]^^n.

Lemma RD1_Incs n:
  segRLs tm (h^^n) [] (RD1 n) (RD1 0).
Proof.
  induction n.
  - esx.
  - cbn[lpow].
    eapply @segRLs_trans with (ls2:=[]).
    2: apply IHn.
    ut; esx.
Qed.

Lemma RD1_Ov a r:
  sideRLs tm h (RD1 0 *> RD (2+a) *> r) ([0;1;1] *> RD 0 *> RD1 a *> r).
Proof.
  ut; es' a & r.
Qed.

Lemma RD1_IncsOv a k r r':
  2+a<=k*2 ->
  sideRLs tm (h^^(k*2-(2+a))) (RD1 0 *> r) ([0;1;1]*>r') ->
  sideRLs tm (h^^k) (RD1 0 *> RD (2+a) *> r) ([0;1;1] *> RD k *> r').
Proof.
  intros Hk I1.
  replace (h^^k) with (h^^(1+(k-1))) by flia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RD1_Ov.
  eapply segRLs_sideRLs_concat.
  1: apply w011_Incs.
  replace (RD k*>r') with (RD (k-1+0)*>[0;1;1]*>r').
  2:{
    remember (k-1) as k'.
    replace k with (k'+1) by lia.
    ut; st; reflexivity.
  }
  eapply segRLs_sideRLs_concat.
  1: apply RD_Incs.
  replace ((k-1)*2) with (a+(k*2-(2+a))) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: apply I1.
  eapply segRLs_sideRLs_concat.
  1: applys_eq RD1_Incs.
  ec.
Qed.

Lemma RD1_Ov_rh:
  sideRLs tm h (RD1 0 *> rh true) ([0;1;1] *> 0inf).
Proof.
  esx.
Qed.

Lemma RD1_IncsOv_rh k:
  sideRLs tm (h^^(1+k)) (RD1 0 *> rh true) ([0;1;1] *> 0inf).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RD1_Ov_rh.
  eapply segRLs_sideRLs_concat.
  1: apply w011_Incs.
  apply r0inf_Incs.
Qed.

Lemma RD1_Ov_r0inf:
  sideRLs tm h (RD1 0 *> 0inf) (rh true).
Proof.
  esx.
Qed.

Lemma RD1_IncsOv_r0inf_1 k a:
  1+a<=k ->
  sideRLs tm (h^^(1+k)) (RD1 0 *> RD (2+(a*2+1)) *> 0inf) ([0;1;1] *> RD (1+a) *> rh true).
Proof.
  intros Ha.
  eapply sideRLs_trans_add.
  1: apply RD1_Ov.
  eapply segRLs_sideRLs_concat.
  1: apply w011_Incs.
  replace (RD1 (a*2+1) *> 0inf) with (RD1 (a*2) *> [0;1;1] *> 0inf).
  2: ut; st; reflexivity.
  replace k with (a+(1+(k-a-1))) by lia.
  eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RD_Incs.
  1: eapply segRLs_sideRLs_concat.
  1: apply RD1_Incs.
  1: ec.
  eapply sideRLs_trans_add with (w3:=RD (1+a) *> rh true).
  1: ut; esx.
  eapply rh_Incs.
Qed.

Notation lh := (0inf<*<[1;1;1;1;0;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1;1;1;0;1;1;0;1;1;0;1;1;1;1;1;0;1;1;0;1;1;0;1;1;0;1;1;0;1;1;1;1;1;0;1;1;0;1;1;0;1;1;0;1;1;0;1;1;0;1;1;0;1;1;0]).
Notation lh' := (0inf<*<[1;1;1;1;0;1;1;1;1;1;0;1;0;0;1;0;0;1;1;0;1;0;0;1;1;0;1;1;1;1;1;0]).

Lemma LIncs:
  sideRLs (flip tm) ([(hL,hR)]^^14) lh' lh.
Proof.
  esc.
Qed.

Lemma LRst r:
  lh {{{ (hL,L) }}} ([0;1;1] *> r) -->*
  lh' {{{ (hR,R) }}} RD1 0 *> RD 5 *> RD 9 *> r.
Proof.
  ut; es' & r.
Qed.

Fixpoint RC ls (b:bool) :=
match ls with
| [] => if b then rh true else 0inf
| n::ls => RD n *> RC ls b
end.

Definition Config '(ls,b) :=
  lh {{{ (hL,L) }}} [0;1;1] *> RC ls b.

Inductive RIncs: nat->(list nat)->(list nat)->bool->Prop :=
| RIncs_S k0 a ls ls' b:
  2+a<=k0*2 ->
  RIncs (k0*2-(2+a)) ls ls' b ->
  RIncs k0 (2+a::ls) (k0::ls') b
| RIncs_O_1 k0 a:
  1+a/2<=k0 ->
  a mod 2 = O ->
  RIncs (1+k0) [3+a] [1+a/2] false
| RIncs_O_0 k0:
  RIncs (1+k0) [] [] true.

Lemma RIncs_spec k0 ls ls' b:
  RIncs k0 ls ls' b ->
  sideRLs tm (h^^k0) (RD1 0 *> RC ls b) ([0;1;1]*>RC ls' (negb b)).
Proof.
  intro H.
  induction H; cbn[RC negb].
  - apply RD1_IncsOv; auto 1.
  - applys_eq (RD1_IncsOv_r0inf_1 k0 (a/2)); flia.
  - apply RD1_IncsOv_rh.
Qed.

Lemma BigStep ls ls' b:
  RIncs 15 (5::9::ls) ls' b ->
  Config (ls,b) -->+ Config (ls',negb b).
Proof.
  intros I1.
  apply RIncs_spec in I1.
  unfold Config.
  cbn[RC] in I1.
  follow LRst.
  apply (sideRLs_concat (LIncs) I1).
Qed.

Inductive WF: nat->nat->(list nat)->bool->Prop :=
| WF_S a b ls tp:
  a mod 2 = 1%nat ->
  b mod 2 = 1%nat ->
  5<=a<=b ->
  WF b (a+b+1) ls tp ->
  WF a b (a::ls) tp
| WF_O_1 a b:
  a mod 2 = 1%nat ->
  b mod 2 = 1%nat ->
  5<=a<=b ->
  WF a b [a] false
| WF_O_0 a b:
  a mod 2 = 1%nat ->
  b mod 2 = 1%nat ->
  5<=a<=b ->
  WF b (a+b+1) [b;a/2] true
.

Lemma WF_S' a b ls tp:
  WF a b (a::b::ls) tp ->
  exists ls',
  RIncs (a+b+1) (a::b::ls) ls' tp /\
  WF a b (a::b::ls') (negb tp).
Proof.
  intro H.
  induction H.
  - destruct IHWF as [ls' [I1 I2]].
    eexists; split.
    + applys_eq (RIncs_S (a+b+1) (a-2)); flia.
      applys_eq I1; flia.
    + ec; eauto 1.
  - eexists; split.
    + applys_eq (RIncs_O_1 (a+b) (a-3)); flia.
    + ec; eauto 1.
      applys_eq (WF_O_0 a b); flia.
  - eexists; split.
    + applys_eq (RIncs_S (a+b*2+2) (b-2)).
      1-3: flia.
      applys_eq (RIncs_S (a*2+b*3+4) (a/2-2)).
      1-3: flia.
      applys_eq (RIncs_O_0 (a*4+b*6+7-a/2)); flia.
    + ec; try lia.
      ec; try lia.
      applys_eq WF_S; try flia.
      applys_eq WF_O_1; flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=Config ([],false)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(ls,tp) => (WF 5 9 (5::9::ls) tp)).
  2: ec; try lia; ec; lia.
  intros [ls tp] HWF.
  eapply (WF_S') in HWF.
  destruct HWF as [ls' [I1 I2]].
  eexists; split.
  - apply BigStep,I1.
  - apply I2.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RE_0RD0RD_1LE0RB_0LF1RF_1RA0LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,@nil Sym).
Notation hL := (E,[1;0;0]).
Notation h := [(hR,hL)].

Definition RD n := [1;1;1;1;0;0] ++ [1;0;0]^^n.

Lemma RD_Incs k n:
  segRLs tm (h^^k) (h^^(k*2)) (RD n) (RD (k+n)).
Proof.
  gen n.
  induction k; intros.
  - esx.
  - cbn[Nat.mul lpow].
    rewrite lpow_add.
    eapply segRLs_trans.
    2: applys_eq (IHk (S n)); flia.
    ut; esx.
Qed.

Lemma rh_Incs k:
  sideRLs tm (h^^k) 0inf 0inf.
Proof.
  apply sideRLs_wall.
  esc.
Qed.

Definition RD1 n := [1;0] ++ [1;0;0]^^n.

Lemma RD1_Incs n:
  segRLs tm (h^^n) [] (RD1 n) (RD1 0).
Proof.
  induction n.
  - esx.
  - cbn[lpow].
    eapply @segRLs_trans with (ls2:=[]).
    2: apply IHn.
    ut; esx.
Qed.

Lemma RD1_Ov a r:
  sideRLs tm (h) (RD1 0 *> RD (7+a) *> r) ([1;0;0] *> RD 1 *> RD 2 *> RD1 a *> r).
Proof.
  ut; es' a & r.
Qed.

Lemma RD1_Ov_rh:
  RD1 0 *> 0inf = [1;0;0] *> 0inf.
Proof.
  ut; st; reflexivity.
Qed.

Lemma w100_Incs k:
  segRLs tm (h^^k) (h^^k) [1;0;0] [1;0;0].
Proof.
  apply segRLs_wall''; esc.
Qed.

Lemma RD1_IncsOv k0 a r r':
  4+a<=k0*4 ->
  sideRLs tm (h^^(k0*4-(4+a))) (RD1 0 *> r) ([1;0;0] *> r') ->
  sideRLs tm (h^^(k0)) (RD1 0 *> RD (7+a) *> r) ([1;0;0] *> RD (k0) *> RD (k0*2+1) *> r').
Proof.
  intros Hk0 I1.
  replace (RD (k0*2+1) *> r') with (RD (k0*2) *> [1;0;0] *> r') by (ut; st; trivial).
  replace (h^^k0) with (h^^(1+(k0-1))) by flia.
  eapply sideRLs_trans_add.
  1: apply RD1_Ov.
  eapply segRLs_sideRLs_concat.
  1: apply w100_Incs.
  eapply segRLs_sideRLs_concat.
  1: applys_eq RD_Incs; flia.
  eapply segRLs_sideRLs_concat.
  1: applys_eq RD_Incs; flia.
  replace ((k0-1)*2*2) with (a+(k0*4-(4+a))) by lia.
  eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RD1_Incs.
  1: esc.
  apply I1.
Qed.

Lemma RD1_IncsOv_rh k0:
  sideRLs tm (h^^k0) (RD1 0 *> 0inf) ([1;0;0] *> 0inf).
Proof.
  rewrite RD1_Ov_rh.
  eapply segRLs_sideRLs_concat.
  1: apply w100_Incs.
  apply rh_Incs.
Qed.

Inductive RIncs: nat->(list nat)->(list nat)->Prop :=
| RIncs_S a k0 ls ls':
  4+a<=k0*4 ->
  RIncs (k0*4-(4+a)) ls ls' ->
  RIncs k0 (7+a::ls) (k0::k0*2+1::ls')
| RIncs_O k0:
  RIncs k0 [] [].

Fixpoint RC ls :=
match ls with
| [] => 0inf
| n::ls => RD n *> RC ls
end.

Lemma RIncs_spec k0 ls ls':
  RIncs k0 ls ls' ->
  sideRLs tm (h^^(k0)) (RD1 0 *> RC ls) ([1;0;0] *> RC ls').
Proof.
  intro H.
  induction H; cbn[RC].
  - apply RD1_IncsOv; auto 1.
  - apply RD1_IncsOv_rh.
Qed.

Notation lh := (0inf<*<[1;1;1;0;1;0;0;1;0;1;1;1;0;1;0;0;1;0;0;1;0;1;1;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0]).
Notation lh' := (0inf<*<[1;1;1;1;1;0;0;0;1;1;1;1;1;1;0;0;0;1;1;1;1;0;1;0;0;1;0;1;1;1;0;1;0;0;1;0;1;1;1;1;1;0;0;1;0]).

Lemma LIncs:
  sideRLs (flip tm) ([(hL,hR)]^^161) lh' lh.
Proof.
  esc.
Qed.

Lemma LRst r:
  lh {{{ (hL,L) }}} [1;0;0] *> r -->*
  lh' {{{ (hR,R) }}} RD1 0 *> RD 10 *> RD 21 *> RD 41 *> RD 83 *> r.
Proof.
  ut; es' & r.
Qed.

Definition Config ls :=
  lh {{{ (hL,L) }}} [1;0;0] *> RC ls.

Lemma BigStep ls ls':
  RIncs 162 (10::21::41::83::ls) ls' ->
  Config ls -->+ Config ls'.
Proof.
  intros I1.
  apply RIncs_spec in I1.
  unfold Config.
  cbn[RC] in I1.
  follow LRst.
  apply (sideRLs_concat (LIncs) I1).
Qed.

Lemma init:
  c0 -->*
  Config [].
Proof.
  time esx.
Time Qed.

Inductive F: nat->nat->Prop :=
| F_0: F 0 10
| F_2: F 2 41
| F_4: F 4 162
| F_1 n y:
  F (n*2) y ->
  F (1+n*2) (y*2+1)
| F_6 n y0 y:
  F n y0 ->
  7<=y0<=y*4+3 ->
  F (4+n*2) y ->
  F (6+n*2) (y*4+3-y0).

Ltac rw a b :=
  replace a with b in * by lia;
  repeat
  match goal with
  | [H: ?x = ?x |- _] => clear H
  end.

Lemma F_unique [n y y']:
  F n y ->
  F n y' ->
  y=y'.
Proof.
  gen y y'.
  induction n using lt_wf_ind; intros.
  destruct (mod2 n); subst.
  - inverts H0; try lia;
    inverts H1; try lia.
    rw n0 n.
    unshelve epose proof (H (4+n*2) _ _ _ H5 H8); try lia.
    unshelve epose proof (H n _ _ _ H3 H6); lia.
  - inverts H0; try lia.
    inverts H1; try lia.
    rw n a.
    rw n0 a.
    unshelve epose proof (H (a*2) _ _ _ H3 H4); lia.
Qed.

Ltac F_unique :=
  repeat
  match goal with
  | [H1: F ?n ?y, H2: F ?n ?y' |- _] =>
    pose proof (F_unique H1 H2);
    clear H2;
    subst
  end.

Lemma F_mono [n n' y y']:
  F n y ->
  F n' y' ->
  n<=n' ->
  y<=y'.
Proof.
  gen n y y'.
  induction n' using lt_wf_ind; intros.
  destruct n' as [|n'].
  1:{
    rw n O.
    F_unique.
    lia.
  }
  assert (exists y0, F n' y0 /\ y0<=y') as [y0 [I1 I2]].
  {
    clear n y H0 H2.
    destruct (mod2 n'); subst.
    - inverts H1; try lia.
      rw n a.
      eexists; split; [eauto 1|lia].
    - inverts H1; try lia.
      + eexists; split.
        1: eapply (F_1 0); ec.
        lia.
      + eexists; split.
        1: eapply (F_1 1); ec.
        lia.
      + eexists; split.
        * eapply (F_1 (2+n)),H4.
        * unshelve epose proof (H _ _ _ _ _ H2 H4); lia.
  }
  assert (n<S n'\/n=S n') as [E|E] by lia.
  1: unshelve epose proof (H n' _ _ _ _ H0 I1); lia.
  subst.
  F_unique.
  lia.
Qed.

Lemma F_ex n:
  exists y, F n y.
Proof.
  induction n using lt_wf_ind.
  destruct (mod2 n); subst.
  - destruct a as [|[|[|]]].
    1,2,3: ec; ec.
    unshelve epose proof (H (4+n*2) _) as [y I1].
    1: lia.
    unshelve epose proof (H n _) as [y0 I2].
    1: lia.
    ec.
    eapply F_6; eauto 1.
    pose proof (F_mono F_0 I2).
    pose proof (F_mono I2 I1).
    lia.
  - unshelve epose proof (H (a*2) _) as [y I1].
    1: lia.
    ec; ec; apply I1.
Qed.

Inductive WF: nat->(list nat)->Prop :=
| WF_O n: WF n []
| WF_S n y ls:
  F n y ->
  WF (S n) ls ->
  WF n (y::ls).

Lemma WF_S' n ls k:
  WF n ls ->
  F (4+n*2) k ->
  exists ls',
  RIncs k ls ls' /\
  WF (4+n*2) ls'.
Proof.
  gen n k.
  induction ls; intros.
  - eexists; split; ec.
  - inverts H.
    pose proof (F_ex (6+n*2)) as [y0 I1].
    eapply IHls in H5.
    2: apply I1.
    destruct H5 as [ls' [I2 I3]].
    inverts I1.
    1: lia.
    rw n0 n.
    F_unique.
    eexists; split.
    + applys_eq (RIncs_S (y1-7)).
      1,2: flia.
      applys_eq I2; flia.
    + ec; auto 1.
      ec; auto 1.
      apply (F_1 (2+n)); auto 1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  pose proof (F_1 0 _ F_0).
  pose proof (F_1 1 _ F_2).
  eapply progress_nonhalt_cond with (P:=fun ls => WF 0 (10::21::41::83::ls)).
  2: repeat ec; trivial.
  intros ls HP.
  apply WF_S' with (k:=162) in HP.
  2: ec.
  destruct HP as [ls' [I1 I2]].
  eexists; split.
  - apply BigStep,I1.
  - repeat ec; trivial.
Qed.

End TM3.
