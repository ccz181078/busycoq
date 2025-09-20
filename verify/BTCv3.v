From BusyCoq Require Import Individual62 Longitudinal.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.

Open Scope list.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0RD_1RA0LB_0LA0RE_1LA1RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (B,[0;1;0]).
Notation hR := (A,[1]).
Notation hL' := (C,[1;0;1]).
Notation hR' := (C,<[1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR,hL');(hR',hL)].

Notation d0 := [1;0;0;1;0].
Notation d1 := [1;0;1;0;1;0].
Notation d2' := [1;1;0;1;0;1;0].
Notation d2 := [0;1;0;1;0].

Fixpoint R0(x:nat):side :=
match x with
| O => d0 *> 0inf
| S x0 => d0 *> R0 x0
end.

Fixpoint R1(x:nat):side :=
match x with
| O => d2 *> 0inf
| S x0 => d2 *> R1 x0
end.

Fixpoint Rv0(x:nat):nat :=
match x with
| O => 3
| S x0 => (Rv0 x0)+1+(Rv0 x0)+1+1+(Rv0 x0)
end.

Lemma R0_spec n:
  sideRLs tm hRL' (R1 n) (R0 n).
Proof.
  induction n; cbn[R0]; cbn[R1].
  1: esx.
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  esx.
Qed.

Lemma Rv0_spec n:
  sideRLs tm (hRL^^(Rv0 n)) (R0 n) (R1 n).
Proof.
  induction n; cbn[R0]; cbn[R1]; cbn[Rv0].
  1: esx.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply IHn.
  eapply segRLs_wall; [solve_seg|]; solve_seg.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply R0_spec.
  1: esx.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply IHn.
  eapply segRLs_wall; [solve_seg|]; solve_seg.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply R0_spec.
  1: esx.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  1: esx.
  1: esx.

  1: eapply segRLs_sideRLs_concat.
  2: apply IHn.
  eapply segRLs_wall; [solve_seg|]; solve_seg.
Qed.

Definition LC k := 0inf <* <[1;0]^^k.

Lemma LIncs n k:
  sideRLs tm' (hLR^^n) (LC k) (LC (n*2+k)).
Proof.
  unfold LC.
  induction n.
  1: esx.
  rewrite <-Nat.add_1_r.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma RIncs n:
  sideRLs tm (hRL^^(1+1+(Rv0 n))) (d1*>R1 n) (R1 (S n)).
Proof.
  cbn[R1].
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply R0_spec.
  1: esx.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  1: esx.
  1: esx.

  1: eapply segRLs_sideRLs_concat.
  2: apply Rv0_spec.
  eapply segRLs_wall; [solve_seg|]; solve_seg.
Qed.

Definition S0 '(k,n) :=
  LC (1+k) {{{ (hL,L) }}} R1 n.

Lemma BigStep k n:
  S0 (k,n) -->+
  S0 ((Rv0 n)*2+1+k,S n).
Proof.
  unfold S0.
  mid10 (LC k {{{ (hR,R) }}} d1 *> R1 n).
  1: unfold LC; cbn; es_v2.
  epose proof (RIncs n) as I1.
  rewrite <-lrcons_lpow1 in I1 by lia.
  epose proof (sideRLs_concat (LIncs _ _) I1) as I.
  follow100 I.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: esx.
  eapply progress_nonhalt_simple.
  intros [k n]; eexists; apply BigStep.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LA_1LA0RB_0LC0RE_1LC1RF_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (A,[0;1;0]).
Notation hR := (C,[1]).
Notation hL' := (B,[1;0;1]).
Notation hR' := (B,<[1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR,hL');(hR',hL)].

Notation d0 := [1;0;0;1;0].
Notation d1 := [1;0;1;0;1;0].
Notation d2' := [1;1;0;1;0;1;0].
Notation d2 := [0;1;0;1;0].

Fixpoint R0(x:nat):side :=
match x with
| O => d0 *> 0inf
| S x0 => d0 *> R0 x0
end.

Fixpoint R1(x:nat):side :=
match x with
| O => d2 *> 0inf
| S x0 => d2 *> R1 x0
end.

Fixpoint Rv0(x:nat):nat :=
match x with
| O => 3
| S x0 => (Rv0 x0)+1+(Rv0 x0)+1+1+(Rv0 x0)
end.

Lemma R0_spec n:
  sideRLs tm hRL' (R1 n) (R0 n).
Proof.
  induction n; cbn[R0]; cbn[R1].
  1: esx.
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  esx.
Qed.

Lemma Rv0_spec n:
  sideRLs tm (hRL^^(Rv0 n)) (R0 n) (R1 n).
Proof.
  induction n; cbn[R0]; cbn[R1]; cbn[Rv0].
  1: esx.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply IHn.
  eapply segRLs_wall; [solve_seg|]; solve_seg.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply R0_spec.
  1: esx.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply IHn.
  eapply segRLs_wall; [solve_seg|]; solve_seg.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply R0_spec.
  1: esx.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  1: esx.
  1: esx.

  1: eapply segRLs_sideRLs_concat.
  2: apply IHn.
  eapply segRLs_wall; [solve_seg|]; solve_seg.
Qed.

Definition LC k := 0inf <* <[1;0]^^k.

Lemma LIncs n k:
  sideRLs tm' (hLR^^n) (LC k) (LC (n*2+k)).
Proof.
  unfold LC.
  induction n.
  1: esx.
  rewrite <-Nat.add_1_r.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma RIncs n:
  sideRLs tm (hRL^^(1+1+(Rv0 n))) (d1*>R1 n) (R1 (S n)).
Proof.
  cbn[R1].
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply R0_spec.
  1: esx.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  1: esx.
  1: esx.

  1: eapply segRLs_sideRLs_concat.
  2: apply Rv0_spec.
  eapply segRLs_wall; [solve_seg|]; solve_seg.
Qed.

Definition S0 '(k,n) :=
  LC (1+k) {{{ (hL,L) }}} R1 n.

Lemma BigStep k n:
  S0 (k,n) -->+
  S0 ((Rv0 n)*2+1+k,S n).
Proof.
  unfold S0.
  mid10 (LC k {{{ (hR,R) }}} d1 *> R1 n).
  1: unfold LC; cbn; es_v2.
  epose proof (RIncs n) as I1.
  rewrite <-lrcons_lpow1 in I1 by lia.
  epose proof (sideRLs_concat (LIncs _ _) I1) as I.
  follow100 I.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (6,1)%nat).
  1: esx.
  eapply progress_nonhalt_simple.
  intros [k n]; eexists; apply BigStep.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RF_1LF0RD_0LB0RE_1LB1RA_1RB0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (C,[0;1;0]).
Notation hR := (B,[1]).
Notation hL' := (F,[1;0;1]).
Notation hR' := (F,<[1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR,hL');(hR',hL)].

Notation d0 := [1;0;0;1;0].
Notation d1 := [1;0;1;0;1;0].
Notation d2' := [1;1;0;1;0;1;0].
Notation d2 := [0;1;0;1;0].

Fixpoint R0(x:nat):side :=
match x with
| O => d0 *> 0inf
| S x0 => d0 *> R0 x0
end.

Fixpoint R1(x:nat):side :=
match x with
| O => d2 *> 0inf
| S x0 => d2 *> R1 x0
end.

Fixpoint Rv0(x:nat):nat :=
match x with
| O => 3
| S x0 => (Rv0 x0)+1+(Rv0 x0)+1+1+(Rv0 x0)
end.

Lemma R0_spec n:
  sideRLs tm hRL' (R1 n) (R0 n).
Proof.
  induction n; cbn[R0]; cbn[R1].
  1: esx.
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  esx.
Qed.

Lemma Rv0_spec n:
  sideRLs tm (hRL^^(Rv0 n)) (R0 n) (R1 n).
Proof.
  induction n; cbn[R0]; cbn[R1]; cbn[Rv0].
  1: esx.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply IHn.
  eapply segRLs_wall; [solve_seg|]; solve_seg.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply R0_spec.
  1: esx.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply IHn.
  eapply segRLs_wall; [solve_seg|]; solve_seg.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply R0_spec.
  1: esx.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  1: esx.
  1: esx.

  1: eapply segRLs_sideRLs_concat.
  2: apply IHn.
  eapply segRLs_wall; [solve_seg|]; solve_seg.
Qed.

Definition LC k := 0inf <* <[1;0]^^k.

Lemma LIncs n k:
  sideRLs tm' (hLR^^n) (LC k) (LC (n*2+k)).
Proof.
  unfold LC.
  induction n.
  1: esx.
  rewrite <-Nat.add_1_r.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma RIncs n:
  sideRLs tm (hRL^^(1+1+(Rv0 n))) (d1*>R1 n) (R1 (S n)).
Proof.
  cbn[R1].
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  2: apply R0_spec.
  1: esx.

  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  1: esx.
  1: esx.

  1: eapply segRLs_sideRLs_concat.
  2: apply Rv0_spec.
  eapply segRLs_wall; [solve_seg|]; solve_seg.
Qed.

Definition S0 '(k,n) :=
  LC (1+k) {{{ (hL,L) }}} R1 n.

Lemma BigStep k n:
  S0 (k,n) -->+
  S0 ((Rv0 n)*2+1+k,S n).
Proof.
  unfold S0.
  mid10 (LC k {{{ (hR,R) }}} d1 *> R1 n).
  1: unfold LC; cbn; es_v2.
  epose proof (RIncs n) as I1.
  rewrite <-lrcons_lpow1 in I1 by lia.
  epose proof (sideRLs_concat (LIncs _ _) I1) as I.
  follow100 I.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1,0)%nat).
  1: esx.
  eapply progress_nonhalt_simple.
  intros [k n]; eexists; apply BigStep.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB1LF_0RC1RD_0RD1RC_1LE0LA_0LF---_1LD1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (F,[1;1;1]).
Notation hR := (C,[]).
Notation hL' := (F,[0;1]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR,hL')].

Notation d0 := [1;1;1;1;1;1;1;1].
Notation d1 := [1;1;0;1;1;1;1].
Notation d2 := [0;1;1;1;1;1;1;1;1].
Notation d3 := [0;1;1;0;1;1;1;1].

Notation rh0 := ([1;1;0;1;0;1]*>0inf).
Notation rh1 := ([0;1;1;0;1;0;1]*>0inf).
Notation rh2 := ([0;0;1;1;0;1;0;1]*>0inf).

Notation d0' := [0;1;1;0;1;0;1].
Notation d0'' := [0;0;1;1;1;1;1;1;1;1].
Notation d1' := [1;1;1;1;1;0;1].
Notation d2' := [1;1;0;1;0;1].
Notation d3' := [0;1;1;1;1;1;0;1].

Inductive RC: nat->side->nat->side->Prop :=
| RC_h2: RC 0 rh2 0 rh0
| RC_h1: RC 0 rh1 1 rh0
| RC_h0: RC 0 rh0 2 rh0
| RC_d0'' n r m r0:
  RC n r m r0 ->
  RC (S n) (d0''*>r) 0 (d0*>r)
| RC_d0' n r m r0 r1:
  sideRLs tm (hRL^^2) r r0 ->
  RC (S n) (d0''*>r0) m r1 ->
  RC (S n) (d0'*>r) (1+m) r1 
| RC_d3 n r m m0 r0 r1:
  RC n r m0 r0 ->
  RC (S n) (d0'*>r0) m r1 ->
  RC (S n) (d3*>r) (m0+(1+m)) r1 
| RC_d3' n r m r0 r1:
  sideRLs tm (hRL^^1) r r0 ->
  RC (S n) (d3*>r0) m r1 ->
  RC (S n) (d3'*>r) (1+m) r1 
| RC_d2 n r m m0 r0 r1:
  RC n r m0 r0 ->
  RC (S n) (d3'*>r0) m r1 ->
  RC (S n) (d2*>r) (m0+(1+m)) r1 
| RC_d2' n r m r0 r1:
  sideRLs tm (hRL^^2) r r0 ->
  RC (S n) (d2*>r0) m r1 ->
  RC (S n) (d2'*>r) (1+m) r1 
| RC_d1 n r m m0 r0 r1:
  RC n r m0 r0 ->
  RC (S n) (d2'*>r0) m r1 ->
  RC (S n) (d1*>r) (m0+(1+m)) r1 
| RC_d1' n r m r0 r1:
  sideRLs tm (hRL^^1) r r0 ->
  RC (S n) (d1*>r0) m r1 ->
  RC (S n) (d1'*>r) (1+m) r1 
| RC_d0 n r m m0 r0 r1:
  RC n r m0 r0 ->
  RC (S n) (d1'*>r0) m r1 ->
  RC (S n) (d0*>r) (m0+(1+m)) r1 
.

Inductive RC0: nat->side->Prop :=
| RC0_O: RC0 0 rh0
| RC0_S n r m r0: RC n r m r0 -> RC0 (S n) (d0 *> r)
.

Inductive RWF: nat->side->nat->side->Prop :=
| RWF_S n r m r' r0:
  sideRLs tm hRL r r' ->
  RC n r' m r0 ->
  RWF n r (S m) r0
| RWF_O n r r':
  sideRLs tm hRL' r r' ->
  RC0 n r' ->
  RWF n r O r'
.

Ltac ec := econstructor.
Ltac ea := eassumption.

Ltac ssc H :=
  eapply segRLs_sideRLs_concat; [ | apply H]; esx.

Ltac ssc' :=
  match goal with
  | [H:sideRLs _ _ _ _ |- _] =>
    solve[ssc H]
  end.

Section RC_spec_sec.
Hypothesis n : nat.
Hypothesis RWF_spec: forall r m r0, RC n r m r0 -> RWF n r m r0.
Hypothesis RC0_spec: forall r, RC0 n r -> exists m r0, RC n r (2+m) r0.

Ltac solve_v1 :=
  intros Hr HRC;
  ec; [ssc Hr|]; ea.

Ltac solve_v2 :=
  intros Hr HRC;
  apply RWF_spec in Hr;
  inverts Hr;
  [ cbn[Nat.add];
    ec; [ssc'|]; ec; ea | ];
  ec; [ssc'|]; ea.

Lemma RWF_d0'' r m r0:
  RC n r m r0 ->
  RWF (S n) (d0''*>r) 0 (d0*>r).
Proof.
  intros HRC.
  ec.
  2: ec; ea.
  esx.
Qed.

Lemma RWF_d0' r m r0 r1:
  sideRLs tm (hRL^^2) r r0 ->
  RC (S n) (d0''*>r0) m r1 ->
  RWF (S n) (d0'*>r) (1+m) r1.
Proof.
  solve_v1.
Qed.

Lemma RWF_d3 r m m0 r0 r1:
  RC n r m0 r0 ->
  RC (S n) (d0'*>r0) m r1 ->
  RWF (S n) (d3*>r) (m0+(1+m)) r1.
Proof.
  solve_v2.
Qed.

Lemma RWF_d3' r m r0 r1:
  sideRLs tm (hRL^^1) r r0 ->
  RC (S n) (d3*>r0) m r1 ->
  RWF (S n) (d3'*>r) (1+m) r1.
Proof.
  solve_v1.
Qed.

Lemma RWF_d2 r m m0 r0 r1:
  RC n r m0 r0 ->
  RC (S n) (d3'*>r0) m r1 ->
  RWF (S n) (d2*>r) (m0+(1+m)) r1.
Proof.
  solve_v2.
Qed.

Lemma RWF_d2' r m r0 r1:
  sideRLs tm (hRL^^2) r r0 ->
  RC (S n) (d2*>r0) m r1 ->
  RWF (S n) (d2'*>r) (1+m) r1.
Proof.
  solve_v1.
Qed.

Lemma RWF_d1 r m m0 r0 r1:
  RC n r m0 r0 ->
  RC (S n) (d2'*>r0) m r1 ->
  RWF (S n) (d1*>r) (m0+(1+m)) r1.
Proof.
  solve_v2.
Qed.

Lemma RWF_d1' r m r0 r1:
  sideRLs tm (hRL^^1) r r0 ->
  RC (S n) (d1*>r0) m r1 ->
  RWF (S n) (d1'*>r) (1+m) r1.
Proof.
  solve_v1.
Qed.

Lemma RWF_d0 r m m0 r0 r1:
  RC n r m0 r0 ->
  RC (S n) (d1'*>r0) m r1 ->
  RWF (S n) (d0*>r) (m0+(1+m)) r1. 
Proof.
  solve_v2.
Qed.

End RC_spec_sec.


Lemma RC_RC0 n r m r0:
  RC n r m r0 ->
  RC0 n r0.
Proof.
  intros H.
  induction H.
  1-3: ec.
  1: ec; ea.
  all: ea.
Qed.

Ltac solve_v3 H1 IHn :=
  let R1 := fresh "R" in
  epose proof H1 as R1;
  apply RC_RC0,IHn in R1;
  let m := fresh "m" in
  let r := fresh "r" in
  destruct R1 as [m [r R1]];
  apply IHn in R1;
  inverts R1.

Ltac solve_v4 H6 IHn :=
  let R1 := fresh "R" in
  epose proof H6 as R1;
  apply IHn in R1;
  inverts R1.

Lemma RC_spec_1 n:
  (forall r m r0, RC n r m r0 -> RWF n r m r0) /\
  (forall r, RC0 n r -> exists m r0, RC n r (2+m) r0) ->
  forall r,
  RC0 (S n) r ->
  exists (m : nat) (r0 : side), RC (S n) r (2 + m) r0.
Proof.
  intros IHn r H.
  inverts H.
  solve_v3 H1 IHn.
  solve_v3 H4 IHn.
  solve_v4 H6 IHn.
  solve_v3 H8 IHn.
  solve_v3 H10 IHn.
  solve_v4 H12 IHn.

  eexists _,_.
  cbn[Nat.add].
  applys_eq RC_d0.
  1: shelve.
  1: ea.

  eapply RC_d1'.
  1: ea.
  eapply RC_d1.
  1: ea.
  eapply RC_d2'.
  1: eapply @sideRLs_trans with (ls1:=hRL).
  1: ea.
  1: ea.
  eapply RC_d2.
  1: ea.
  eapply RC_d3'.
  1: ea.
  eapply RC_d3.
  1: ea.
  eapply RC_d0'.
  1: eapply @sideRLs_trans with (ls1:=hRL).
  1: ea.
  1: ea.
  eapply RC_d0''.
  1: ea.
  Unshelve.
  1: apply (m+m0+m1+m2+8).
  lia.
Qed.


Lemma RC_spec n:
  (forall r m r0, RC n r m r0 -> RWF n r m r0) /\
  (forall r, RC0 n r -> exists m r0, RC n r (2+m) r0).
Proof.
  induction n.
  - split; intros.
    + inverts H; (ec; [esx|]; ec).
    + inverts H; eexists _,_; ec.
  - split; intros.
    + destruct IHn as [I1 I2].
      inverts H.
      * eapply RWF_d0''; ea.
      * eapply RWF_d0'; ea.
      * eapply RWF_d3; ea.
      * eapply RWF_d3'; ea.
      * eapply RWF_d2; ea.
      * eapply RWF_d2'; ea.
      * eapply RWF_d1; ea.
      * eapply RWF_d1'; ea.
      * eapply RWF_d0; ea.
    + apply RC_spec_1; ea.
Qed.

Definition LC n := 0inf <* <[1;0] <* <[1;1]^^n.

Definition S' '(n,r) := LC n {{{ (hL,L) }}} r.

Lemma BigStep1 k n r m r0:
  RC n r (S m) r0 ->
  exists r',
  S' (k,r) -->+
  S' (k+2,r') /\
  RC n r' m r0.
Proof.
  intros.
  unfold S',LC.
  apply RC_spec in H.
  inverts H.
  inverts H1.
  inverts H7.
  eexists; split.
  2: ea.
  es; er.
  follow100 H6.
  es.
Qed.

Lemma BigStep0 k n r r0:
  RC n r 0 r0 ->
  exists r' r1 m,
  S' (k+2,r) -->+
  S' (k,r') /\
  RC (S n) r' (S m) r1.
Proof.
  intros.
  unfold S',LC.
  apply RC0_S in H.
  apply RC_spec_1 in H.
  2: apply RC_spec.
  destruct H as [m0 [r1 I1]].
  solve_v4 I1 RC_spec.
  inverts H0.
  inverts H7.
  eexists _,_,_; split.
  2: shelve.
  mid10 (LC k {{{ (hR,R) }}} d0 *> r); unfold LC.
  1: es_v2.
  follow100 H6.
  finish.
  Unshelve.
  3: ea.
Qed.

Inductive P: (nat*side)->Prop :=
| P_intro k n r m r0:
  RC n r m r0 ->
  m>=1 \/ k>=2 ->
  P (k,r).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,rh1)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: ec; [ec|]; lia.
  intros [k r] HP.
  inverts HP.
  destruct m.
  - eapply (BigStep0 (k-2)) in H1.
    destruct H1 as [r' [r1' [m [I1 I2]]]].
    rewrite Nat.sub_add in I1 by lia.
    eexists; split.
    1: ea.
    ec; [ea|]; lia.
  - eapply BigStep1 in H1.
    destruct H1 as [r' [I1 I2]].
    eexists; split.
    1: ea.
    ec; [ea|]; lia.
Qed.

End TM4.




