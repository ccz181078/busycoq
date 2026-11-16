From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.

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
  cbn[app]).

Ltac solve_sideRLs :=
  repeat (eapply sideRLseq_S;
  [ intros l;
    unfold to_DH_config; cbn;
    (repeat (er; try sr)) | ] ||
  eapply sideRLseq_O).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB2LA1RA---1LA_1LA4RB3LB0RB2RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[]).
Definition hL:DH0 := (A,[]).
Definition hL':DH0 := (A,[1]).
Definition hRL: list (DH0*DH0) := [(hR,hL)].
Definition hRL': list (DH0*DH0) := [(hR,hL')].
Definition hRL4: list (DH0*DH0) := [(hR,hL);(hR,hL);(hR,hL);(hR,hL')].

Definition D a b := [1]^^a ++ [2;2] ++ [3]^^b ++ [2].

Definition D1 n := D (1+n) 1.
Definition D2 n := D n 2.

Definition X a b s :=
  segRLs tm [((B,[0]^^a),hL)] (hRL4^^b) [2] s.

Definition Y a b s :=
  segRLs tm [((A,[0]^^a),hL)] (hRL++(hRL4^^b)) [0] s.

Definition Z b s s' :=
  segRLs tm (hRL++(hRL4^^b)) (hRL4^^b) s s'.

Definition V a b c s :=
  segRLs tm (hRL'^^a) [] s ([1]^^b++[3]^^c++[2]).

Definition W a b c s :=
  segRLs tm (hRL'^^a) (hRL4^^b) s ([1]^^c++[3;3;3;2]).

Definition W1 a b c s :=
  segRLs tm (hRL'^^a) (hRL4^^b) s (D1 c).

Definition W2 a b c s :=
  segRLs tm (hRL'^^a) (hRL4^^b) s (D2 c).

Lemma D_hRL4 n a b:
  segRLs tm (hRL4^^n) [] (D (n*5+a) b) (D a (n*4+b)).
Proof.
  gen a b.
  induction n; intros.
  1: constructor.
  change (S n) with (1+n).
  rewrite lpow_add.
  eapply @segRLs_trans with (ls2:=[]).
  2: {
    replace ((1+n)*4+b) with (n*4+(4+b)) by lia.
    apply IHn.
  }
  solve_segRLs.
  unfold D.
  solve_segRLs.
Qed.

Lemma _1s_hRL' a b:
  segRLs tm (hRL++(hRL4^^a)) (hRL'^^(1+a*4)) ([1]^^b) ([1]^^(1+a*3+b)).
Proof.
  induction a.
  1: solve_segRLs.
  replace (1+S a*4) with ((1+a*4)+4) by lia.
  replace (hRL4^^S a) with (hRL4^^(a+1)) by (f_equal; lia).
  repeat rewrite lpow_add in *.
  rewrite app_assoc.
  eapply segRLs_trans.
  1: apply IHa.
  solve_segRLs.
Qed.

Lemma Z_S1 [a c s]:
  W1 (1+a*4) a c s ->
  Z a s (D1 ((1+a*3)+c)).
Proof.
  unfold W1,Z,D1,D.
  intros HW1.
  replace (1+(1+a*3+c)) with ((1+a*3+0)+(1+c)) by lia.
  rewrite lpow_add.
  rewrite <-app_assoc.
  eapply @segRLs_concat with (w1:=[]).
  1: apply (_1s_hRL' a 0).
  apply HW1.
Qed.

Lemma Z_S2 [a c s]:
  W2 (1+a*4) a c s ->
  Z a s (D2 ((1+a*3)+c)).
Proof.
  unfold W2,Z,D2,D.
  intros HW2.
  rewrite lpow_add.
  rewrite <-app_assoc.
  replace (1+a*3) with (1+a*3+0) by lia.
  eapply @segRLs_concat with (w1:=[]).
  1: apply (_1s_hRL' a 0).
  apply HW2.
Qed.

Lemma W1_S [a b c s]:
  W a b (4+c) s ->
  W1 (a+5) (b+2) c s.
Proof.
  unfold W,W1.
  intros HW.
  repeat rewrite lpow_add.
  eapply segRLs_trans.
  1: apply HW.
  solve_segRLs.
Qed.

Lemma W2_S [a b c s]:
  W a b (5+c) s ->
  W2 (a+6) (b+2) c s.
Proof.
  unfold W,W2.
  intros HW.
  repeat rewrite lpow_add.
  eapply segRLs_trans.
  1: apply HW.
  solve_segRLs.
Qed.

Lemma W_S [a b c d a' b' c' s s']:
  V a (b+1) c s ->
  X c d s' ->
  W a' b' c' s' ->
  W (a+1+a') (0+d+b') (b+c') s.
Proof.
  unfold W,V,X.
  intros HV HX HW.
  repeat rewrite lpow_add.
  eapply segRLs_trans.
  2:{
    rewrite <-app_assoc.
    eapply segRLs_concat.
    2: apply HW.
    eapply segRLs_wall.
    1: solve_seg.
    solve_seg.
  }
  eapply segRLs_trans.
  1: apply HV.
  rewrite lpow_add,<-app_assoc.
  eapply segRLs_concat.
  1: {
    eapply segRLs_wall.
    1: solve_seg.
    solve_seg.
  }
  eapply @segRLs_concat with (ls2:=hRL) (w2:=[]).
  1: solve_segRLs.
  eapply evstep_segRLs_trans.
  2: apply HX.
  es.
Qed.

Lemma V_S1 [a b c s]:
  W a b c s ->
  V (a+3) (3+c) (7+b*4) (s++D1 (b*5+5)).
Proof.
  unfold W,V.
  intros HW.
  rewrite lpow_add.
  eapply @segRLs_trans with (ls2:=[]).
  - eapply segRLs_concat.
    1: apply HW.
    unfold D1.
    replace (1+(b*5+5)) with (b*5+6) by lia.
    apply D_hRL4.
  - cbn.
    solve_segRLs.
Qed.

Lemma V_S2 [a b c s]:
  W a b c s ->
  V (a+4) (2+c) (7+b*4) (s++D2 (b*5+5)).
Proof.
  unfold W,V.
  intros HW.
  rewrite lpow_add.
  eapply @segRLs_trans with (ls2:=[]).
  - eapply segRLs_concat.
    1: apply HW.
    unfold D1.
    replace (1+(b*5+5)) with (b*5+6) by lia.
    apply D_hRL4.
  - cbn.
    solve_segRLs.
Qed.

Lemma Y_S [a b s s']:
  Y a b s ->
  Z b s s' ->
  Y (a+1+a) (b+b) (s++s').
Proof.
  unfold Y,Z.
  intros HY HZ.
  repeat rewrite lpow_add.
  repeat rewrite app_assoc.
  change ([0]^^1) with [0].
  rewrite <-app_cons_r.
  eapply segRLs_trans_1.
  1: apply HY.
  cbn.
  eapply @segRLs_concat with (w1:=[0]).
  1: apply HY.
  apply HZ.
Qed.

Lemma X_S [a b sx sy s']:
  X a b sx ->
  Y a b sy ->
  Z b sx s' ->
  X (a+1+a) (b+b) (sy++s').
Proof.
  unfold X,Y,Z.
  intros HX HY HZ.
  repeat rewrite lpow_add.
  repeat rewrite app_assoc.
  change ([0]^^1) with [0].
  rewrite <-app_cons_r.
  eapply segRLs_trans_1.
  1: apply HX.
  cbn.
  eapply @segRLs_concat with (w1:=[0]).
  1: apply HY.
  apply HZ.
Qed.

Ltac flia := repeat (lia || f_equal).

Section all_S.
Hypothesis n:nat.
Hypothesis sx sy:list sym.
Hypothesis HX: X (15+n*4) (4+n) sx.
Hypothesis HY: Y (15+n*4) (4+n) sy.
Hypothesis HWX: W (11+n*4) (2+n) (7+n*2) sx.
Hypothesis HWY: W (12+n*4) (2+n) (6+n*2) sy.

Lemma HW1: W1 (1+(4+n)*4) (4+n) (2+n*2) sy.
Proof.
  applys_eq (W1_S HWY); lia.
Qed.

Lemma HW2: W2 (1+(4+n)*4) (4+n) (2+n*2) sx.
Proof.
  applys_eq (W2_S HWX); lia.
Qed.

Lemma HZX: Z (4+n) sx (D2 (15+n*5)).
Proof.
  applys_eq (Z_S2 HW2); flia.
Qed.

Lemma HZY: Z (4+n) sy (D1 (15+n*5)).
Proof.
  applys_eq (Z_S1 HW1); flia.
Qed.

Definition n' := n*2+4.
Definition sx' := sy++D2 (15+n*5).
Definition sy' := sy++D1 (15+n*5).

Lemma HVY:
  V (15+n*4) ((8+n*2)+1) (15+n*4) sy'.
Proof.
  unfold sy'.
  applys_eq (V_S1 HWY); flia.
Qed.

Lemma HVX:
  V (16+n*4) ((7+n*2)+1) (15+n*4) sx'.
Proof.
  unfold sx'.
  applys_eq (V_S2 HWY); flia.
Qed.

Lemma HWX':
  W (12+n'*4) (2+n') (4+(2+n'*2)) sx'.
Proof.
  unfold n',sx'.
  applys_eq (W_S HVX HX HWX); flia.
Qed.

Lemma HWY':
  W (11+n'*4) (2+n') (4+(3+n'*2)) sy'.
Proof.
  unfold n',sy'.
  applys_eq (W_S HVY HX HWX); flia.
Qed.

Lemma HW1': W1 (1+(4+n')*4) (4+n') (1+(1+n'*2)) sx'.
Proof.
  applys_eq (W1_S HWX'); lia.
Qed.

Lemma HW2': W2 (1+(4+n')*4) (4+n') (1+(1+n'*2)) sy'.
Proof.
  applys_eq (W2_S HWY'); lia.
Qed.

Lemma HX':
  X (15+n'*4) (4+n') sx'.
Proof.
  unfold n',sx'.
  applys_eq (X_S HX HY HZX); lia.
Qed.

Lemma HY':
  Y (15+n'*4) (4+n') sy'.
Proof.
  unfold n',sy'.
  applys_eq (Y_S HY HZY); lia.
Qed.

Lemma HZX': Z (4+n') sx' (D1 (15+n'*5)).
Proof.
  applys_eq (Z_S1 HW1'); flia.
Qed.

Lemma HZY': Z (4+n') sy' (D2 (15+n'*5)).
Proof.
  applys_eq (Z_S2 HW2'); flia.
Qed.

Definition n'' := n'*2+4.
Definition sx'' := sy'++D1 (15+n'*5).
Definition sy'' := sy'++D2 (15+n'*5).

Lemma HX'':
  X (15+n''*4) (4+n'') sx''.
Proof.
  unfold n'',sx''.
  applys_eq (X_S HX' HY' HZX'); lia.
Qed.

Lemma HY'':
  Y (15+n''*4) (4+n'') sy''.
Proof.
  unfold n'',sy''.
  applys_eq (Y_S HY' HZY'); lia.
Qed.

Lemma HVX':
  V (14+n'*4) ((9+n'*2)+1) (15+n'*4) sx''.
Proof.
  unfold sx''.
  applys_eq (V_S1 HWY'); flia.
Qed.

Lemma HVY':
  V (15+n'*4) ((8+n'*2)+1) (15+n'*4) sy''.
Proof.
  unfold sy''.
  applys_eq (V_S2 HWY'); flia.
Qed.

Lemma HWX'':
  W (11+n''*4) (2+n'') (7+n''*2) sx''.
Proof.
  unfold n''.
  applys_eq (W_S HVX' HX' HWX'); flia.
Qed.

Lemma HWY'':
  W (12+n''*4) (2+n'') (6+n''*2) sy''.
Proof.
  unfold n''.
  applys_eq (W_S HVY' HX' HWX'); flia.
Qed.

End all_S.

Inductive P:nat->Prop :=
| P_intro i n sx sy
  (Hi: n>=i)
  (HX: X (15+n*4) (4+n) sx)
  (HY: Y (15+n*4) (4+n) sy)
  (HWX: W (11+n*4) (2+n) (7+n*2) sx)
  (HWY: W (12+n*4) (2+n) (6+n*2) sy):
  P i.

Definition sx0 := [1;1;1;3;2].
Definition sy0 := [1;1;3;2;2].

Definition sy1 := sy0 ++ D1 0.
Definition sy2 := sy1 ++ D2 5.
Definition sy3 := sy2 ++ D1 15.
Definition sx1 := sy0 ++ D2 0.
Definition sx2 := sy1 ++ D1 5.
Definition sx3 := sy2 ++ D2 15.

Lemma P_spec i: P i.
Proof.
  induction i.
  - eapply P_intro with (n:=O) (sx:=sx2) (sy:=sy2).
    1: lia.
    all: unfolds; solve_segRLs.
  - inverts IHi.
    eapply P_intro with (n:=(n*2+4)*2+4).
    1: lia.
    + eapply HX''; eassumption.
    + eapply HY''; eassumption.
    + eapply HWX''; eassumption.
    + eapply HWY''; eassumption.
Qed.

Lemma _0inf_hRL4 {n}:
  sideRLs tm (hRL++hRL4^^n) 0inf ([1]^^(1+n*3)*>0inf).
Proof.
  induction n.
  1: solve_sideRLs.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add,app_assoc.
  eapply sideRLs_trans.
  1: apply IHn.
  replace (n+1) with (S n) by lia.
  solve_sideRLs.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (sigma_score_unbounded_nonhalt).
  intros i.
  epose proof (P_spec i) as HP.
  inverts HP.
  unfold Y in HY.
  clear HX HWX HWY.
  eexists _,_.
  split.
  - epose proof (segRLs_sideRLs_concat HY (_0inf_hRL4)) as H.
    inverts H.
    inverts H6.
    specialize (H5 0inf).
    cbn in H5.
    rewrite lpow_all0 in H5.
    2: solve_const0_eq.
    repeat rewrite <-const_unfold in H5.
    follow100 H5.
    finish.
  - split.
    + repeat rewrite Str_cons_def.
      solve_sigma_score.
    + lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB2RA3RA4LA0RA_1RA3LB1LB1RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "2" := 3%sym.
Notation "3" := 4%sym.
Notation "4" := 2%sym.

Notation "'A0'" := A.
Notation "'B0'" := B.
Notation "'A'" := B0.
Notation "'B'" := A0.

Definition hR:DH0 := (B,[]).
Definition hL:DH0 := (A,[]).
Definition hL':DH0 := (A,[1]).
Definition hRL: list (DH0*DH0) := [(hR,hL)].
Definition hRL': list (DH0*DH0) := [(hR,hL')].
Definition hRL4: list (DH0*DH0) := [(hR,hL);(hR,hL);(hR,hL);(hR,hL')].

Definition D a b := [1]^^a ++ [2;2] ++ [3]^^b ++ [2].

Definition D1 n := D (1+n) 1.
Definition D2 n := D n 2.

Definition X a b s :=
  segRLs tm [((B,[0]^^a),hL)] (hRL4^^b) [2] s.

Definition Y a b s :=
  segRLs tm [((A,[0]^^a),hL)] (hRL++(hRL4^^b)) [0] s.

Definition Z b s s' :=
  segRLs tm (hRL++(hRL4^^b)) (hRL4^^b) s s'.

Definition V a b c s :=
  segRLs tm (hRL'^^a) [] s ([1]^^b++[3]^^c++[2]).

Definition W a b c s :=
  segRLs tm (hRL'^^a) (hRL4^^b) s ([1]^^c++[3;3;3;2]).

Definition W1 a b c s :=
  segRLs tm (hRL'^^a) (hRL4^^b) s (D1 c).

Definition W2 a b c s :=
  segRLs tm (hRL'^^a) (hRL4^^b) s (D2 c).

Lemma D_hRL4 n a b:
  segRLs tm (hRL4^^n) [] (D (n*5+a) b) (D a (n*4+b)).
Proof.
  gen a b.
  induction n; intros.
  1: constructor.
  change (S n) with (1+n).
  rewrite lpow_add.
  eapply @segRLs_trans with (ls2:=[]).
  2: {
    replace ((1+n)*4+b) with (n*4+(4+b)) by lia.
    apply IHn.
  }
  solve_segRLs.
  unfold D.
  solve_segRLs.
Qed.

Lemma _1s_hRL' a b:
  segRLs tm (hRL++(hRL4^^a)) (hRL'^^(1+a*4)) ([1]^^b) ([1]^^(1+a*3+b)).
Proof.
  induction a.
  1: solve_segRLs.
  replace (1+S a*4) with ((1+a*4)+4) by lia.
  replace (hRL4^^S a) with (hRL4^^(a+1)) by (f_equal; lia).
  repeat rewrite lpow_add in *.
  rewrite app_assoc.
  eapply segRLs_trans.
  1: apply IHa.
  solve_segRLs.
Qed.

Lemma Z_S1 [a c s]:
  W1 (1+a*4) a c s ->
  Z a s (D1 ((1+a*3)+c)).
Proof.
  unfold W1,Z,D1,D.
  intros HW1.
  replace (1+(1+a*3+c)) with ((1+a*3+0)+(1+c)) by lia.
  rewrite lpow_add.
  rewrite <-app_assoc.
  eapply @segRLs_concat with (w1:=[]).
  1: apply (_1s_hRL' a 0).
  apply HW1.
Qed.

Lemma Z_S2 [a c s]:
  W2 (1+a*4) a c s ->
  Z a s (D2 ((1+a*3)+c)).
Proof.
  unfold W2,Z,D2,D.
  intros HW2.
  rewrite lpow_add.
  rewrite <-app_assoc.
  replace (1+a*3) with (1+a*3+0) by lia.
  eapply @segRLs_concat with (w1:=[]).
  1: apply (_1s_hRL' a 0).
  apply HW2.
Qed.

Lemma W1_S [a b c s]:
  W a b (4+c) s ->
  W1 (a+5) (b+2) c s.
Proof.
  unfold W,W1.
  intros HW.
  repeat rewrite lpow_add.
  eapply segRLs_trans.
  1: apply HW.
  solve_segRLs.
Qed.

Lemma W2_S [a b c s]:
  W a b (5+c) s ->
  W2 (a+6) (b+2) c s.
Proof.
  unfold W,W2.
  intros HW.
  repeat rewrite lpow_add.
  eapply segRLs_trans.
  1: apply HW.
  solve_segRLs.
Qed.

Lemma W_S [a b c d a' b' c' s s']:
  V a (b+1) c s ->
  X c d s' ->
  W a' b' c' s' ->
  W (a+1+a') (0+d+b') (b+c') s.
Proof.
  unfold W,V,X.
  intros HV HX HW.
  repeat rewrite lpow_add.
  eapply segRLs_trans.
  2:{
    rewrite <-app_assoc.
    eapply segRLs_concat.
    2: apply HW.
    eapply segRLs_wall.
    1: solve_seg.
    solve_seg.
  }
  eapply segRLs_trans.
  1: apply HV.
  rewrite lpow_add,<-app_assoc.
  eapply segRLs_concat.
  1: {
    eapply segRLs_wall.
    1: solve_seg.
    solve_seg.
  }
  eapply @segRLs_concat with (ls2:=hRL) (w2:=[]).
  1: solve_segRLs.
  eapply evstep_segRLs_trans.
  2: apply HX.
  es.
Qed.

Lemma V_S1 [a b c s]:
  W a b c s ->
  V (a+3) (3+c) (7+b*4) (s++D1 (b*5+5)).
Proof.
  unfold W,V.
  intros HW.
  rewrite lpow_add.
  eapply @segRLs_trans with (ls2:=[]).
  - eapply segRLs_concat.
    1: apply HW.
    unfold D1.
    replace (1+(b*5+5)) with (b*5+6) by lia.
    apply D_hRL4.
  - cbn.
    solve_segRLs.
Qed.

Lemma V_S2 [a b c s]:
  W a b c s ->
  V (a+4) (2+c) (7+b*4) (s++D2 (b*5+5)).
Proof.
  unfold W,V.
  intros HW.
  rewrite lpow_add.
  eapply @segRLs_trans with (ls2:=[]).
  - eapply segRLs_concat.
    1: apply HW.
    unfold D1.
    replace (1+(b*5+5)) with (b*5+6) by lia.
    apply D_hRL4.
  - cbn.
    solve_segRLs.
Qed.

Lemma Y_S [a b s s']:
  Y a b s ->
  Z b s s' ->
  Y (a+1+a) (b+b) (s++s').
Proof.
  unfold Y,Z.
  intros HY HZ.
  repeat rewrite lpow_add.
  repeat rewrite app_assoc.
  change ([0]^^1) with [0].
  rewrite <-app_cons_r.
  eapply segRLs_trans_1.
  1: apply HY.
  cbn.
  eapply @segRLs_concat with (w1:=[0]).
  1: apply HY.
  apply HZ.
Qed.

Lemma X_S [a b sx sy s']:
  X a b sx ->
  Y a b sy ->
  Z b sx s' ->
  X (a+1+a) (b+b) (sy++s').
Proof.
  unfold X,Y,Z.
  intros HX HY HZ.
  repeat rewrite lpow_add.
  repeat rewrite app_assoc.
  change ([0]^^1) with [0].
  rewrite <-app_cons_r.
  eapply segRLs_trans_1.
  1: apply HX.
  cbn.
  eapply @segRLs_concat with (w1:=[0]).
  1: apply HY.
  apply HZ.
Qed.

Ltac flia := repeat (lia || f_equal).

Section all_S.
Hypothesis n:nat.
Hypothesis sx sy:list sym.
Hypothesis HX: X (15+n*4) (4+n) sx.
Hypothesis HY: Y (15+n*4) (4+n) sy.
Hypothesis HWX: W (11+n*4) (2+n) (7+n*2) sx.
Hypothesis HWY: W (12+n*4) (2+n) (6+n*2) sy.

Lemma HW1: W1 (1+(4+n)*4) (4+n) (2+n*2) sy.
Proof.
  applys_eq (W1_S HWY); lia.
Qed.

Lemma HW2: W2 (1+(4+n)*4) (4+n) (2+n*2) sx.
Proof.
  applys_eq (W2_S HWX); lia.
Qed.

Lemma HZX: Z (4+n) sx (D2 (15+n*5)).
Proof.
  applys_eq (Z_S2 HW2); flia.
Qed.

Lemma HZY: Z (4+n) sy (D1 (15+n*5)).
Proof.
  applys_eq (Z_S1 HW1); flia.
Qed.

Definition n' := n*2+4.
Definition sx' := sy++D2 (15+n*5).
Definition sy' := sy++D1 (15+n*5).

Lemma HVY:
  V (15+n*4) ((8+n*2)+1) (15+n*4) sy'.
Proof.
  unfold sy'.
  applys_eq (V_S1 HWY); flia.
Qed.

Lemma HVX:
  V (16+n*4) ((7+n*2)+1) (15+n*4) sx'.
Proof.
  unfold sx'.
  applys_eq (V_S2 HWY); flia.
Qed.

Lemma HWX':
  W (12+n'*4) (2+n') (4+(2+n'*2)) sx'.
Proof.
  unfold n',sx'.
  applys_eq (W_S HVX HX HWX); flia.
Qed.

Lemma HWY':
  W (11+n'*4) (2+n') (4+(3+n'*2)) sy'.
Proof.
  unfold n',sy'.
  applys_eq (W_S HVY HX HWX); flia.
Qed.

Lemma HW1': W1 (1+(4+n')*4) (4+n') (1+(1+n'*2)) sx'.
Proof.
  applys_eq (W1_S HWX'); lia.
Qed.

Lemma HW2': W2 (1+(4+n')*4) (4+n') (1+(1+n'*2)) sy'.
Proof.
  applys_eq (W2_S HWY'); lia.
Qed.

Lemma HX':
  X (15+n'*4) (4+n') sx'.
Proof.
  unfold n',sx'.
  applys_eq (X_S HX HY HZX); lia.
Qed.

Lemma HY':
  Y (15+n'*4) (4+n') sy'.
Proof.
  unfold n',sy'.
  applys_eq (Y_S HY HZY); lia.
Qed.

Lemma HZX': Z (4+n') sx' (D1 (15+n'*5)).
Proof.
  applys_eq (Z_S1 HW1'); flia.
Qed.

Lemma HZY': Z (4+n') sy' (D2 (15+n'*5)).
Proof.
  applys_eq (Z_S2 HW2'); flia.
Qed.

Definition n'' := n'*2+4.
Definition sx'' := sy'++D1 (15+n'*5).
Definition sy'' := sy'++D2 (15+n'*5).

Lemma HX'':
  X (15+n''*4) (4+n'') sx''.
Proof.
  unfold n'',sx''.
  applys_eq (X_S HX' HY' HZX'); lia.
Qed.

Lemma HY'':
  Y (15+n''*4) (4+n'') sy''.
Proof.
  unfold n'',sy''.
  applys_eq (Y_S HY' HZY'); lia.
Qed.

Lemma HVX':
  V (14+n'*4) ((9+n'*2)+1) (15+n'*4) sx''.
Proof.
  unfold sx''.
  applys_eq (V_S1 HWY'); flia.
Qed.

Lemma HVY':
  V (15+n'*4) ((8+n'*2)+1) (15+n'*4) sy''.
Proof.
  unfold sy''.
  applys_eq (V_S2 HWY'); flia.
Qed.

Lemma HWX'':
  W (11+n''*4) (2+n'') (7+n''*2) sx''.
Proof.
  unfold n''.
  applys_eq (W_S HVX' HX' HWX'); flia.
Qed.

Lemma HWY'':
  W (12+n''*4) (2+n'') (6+n''*2) sy''.
Proof.
  unfold n''.
  applys_eq (W_S HVY' HX' HWX'); flia.
Qed.

End all_S.

Inductive P:nat->Prop :=
| P_intro i n sx sy
  (Hi: n>=i)
  (HX: X (15+n*4) (4+n) sx)
  (HY: Y (15+n*4) (4+n) sy)
  (HWX: W (11+n*4) (2+n) (7+n*2) sx)
  (HWY: W (12+n*4) (2+n) (6+n*2) sy):
  P i.

Definition sx0 := [1;1;1;3;2].
Definition sy0 := [1;1;3;2;2].

Definition sy1 := sy0 ++ D1 0.
Definition sy2 := sy1 ++ D2 5.
Definition sy3 := sy2 ++ D1 15.
Definition sx1 := sy0 ++ D2 0.
Definition sx2 := sy1 ++ D1 5.
Definition sx3 := sy2 ++ D2 15.

Lemma P_spec i: P i.
Proof.
  induction i.
  - eapply P_intro with (n:=O) (sx:=sx2) (sy:=sy2).
    1: lia.
    all: unfolds; solve_segRLs.
  - inverts IHi.
    eapply P_intro with (n:=(n*2+4)*2+4).
    1: lia.
    + eapply HX''; eassumption.
    + eapply HY''; eassumption.
    + eapply HWX''; eassumption.
    + eapply HWY''; eassumption.
Qed.

Lemma _0inf_hRL4 {n}:
  sideRLs tm (hRL++hRL4^^n) (1>>0inf) ([1]^^(2+n*3)*>0inf).
Proof.
  induction n.
  1: solve_sideRLs.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add,app_assoc.
  eapply sideRLs_trans.
  1: apply IHn.
  replace (n+1) with (S n) by lia.
  solve_sideRLs.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (sigma_score_unbounded_nonhalt).
  intros i.
  epose proof (P_spec i) as HP.
  inverts HP.
  unfold Y in HY.
  clear HX HWX HWY.
  eexists _,_.
  split.
  - epose proof (segRLs_sideRLs_concat HY (_0inf_hRL4)) as H.
    inverts H.
    inverts H6.
    specialize (H5 0inf).
    cbn in H5.
    rewrite lpow_all0 in H5.
    2: solve_const0_eq.
    repeat rewrite <-const_unfold in H5.
    step1.
    follow100 H5.
    finish.
  - split.
    + repeat rewrite Str_cons_def.
      solve_sigma_score.
    + lia.
Qed.

End TM2.

