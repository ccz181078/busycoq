From BusyCoq Require Import Individual62 Longitudinal.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.

Open Scope list.


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


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1LC0RB_1RD0LE_1RD1RB_---1LF_0LD1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (F,[]).
Notation hR := (B,[0;1;1]).
Notation hR' := (D,[1;1]).
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].
Notation hRL := [(hR,hL)].

Notation d0 := [1;1;0;1;1;1;1].
Notation d1 := [1;1;1;1;1;1].
Notation d2 := [0;1;1;0;1;1;1;1].
Notation d3 := [0;1;1;1;1;1;1].
Notation dh := ([1;1;0;1;1;0;0;1;1;0;0;1;1;1;1;1;1]*>0inf).

Inductive LC: side->nat->nat->Prop :=
| LC_dh: LC dh 2 O
| LC_0dh: LC (0>>dh) 1 O
| LC_00dh: LC ([0;0]*>dh) 0 O
| LC_00d0 l t h:
  LC l t h ->
  LC (([0;0]++d0)*>l) 0 (S h)
| LC_d0 l t h:
  LC l t h ->
  LC (d0*>l) 4 (S h)
| LC_d1 l t h:
  LC l t h ->
  LC (d1*>l) 3 (S h)
| LC_d2 l t h:
  LC l t h ->
  LC (d2*>l) 2 (S h)
| LC_d3 l t h:
  LC l t h ->
  LC (d3*>l) 1 (S h)
.

Ltac eex :=
  repeat eexists.

Ltac des H :=
  let l':=fresh "l'" in
  let t':=fresh "t'" in
  let I:=fresh "I" in
  let I0:=fresh "I" in
  let I1:=fresh "I" in
  destruct H as [l' [t' [I [I0 I1]]]].

Ltac ssc H :=
  eapply segRLs_sideRLs_concat; [|apply H].

Lemma LC_spec l t h:
  LC l t h ->
  match t with
  | S t => exists l' t', LC l' t' h /\ sideRLs tm' hLR l l' /\ t<=t'
  | O => exists l' t', LC l' t' h /\ sideRLs tm' hLR' l l' /\ 1<=t'
  end.
Proof.
  gen l t.
  induction h; intros.
  {
    inverts H.
    - eex.
      1: apply LC_0dh.
      2: lia.
      esx.
    - eex.
      1: apply LC_00dh.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh.
      2: lia.
      esx.
  }
  inverts H.
  - eex.
    1: eapply LC_d0,H3.
    2: lia.
    esx.
  - specialize (IHh _ _ H3).
    destruct t0.
    + des IHh.
      eex.
      1: eapply LC_d1,I.
      2: lia.
      ssc I0.
      esx.
    + des IHh.
      eex.
      1: eapply LC_d0,I.
      2: lia.
      ssc I0.
      esx.
  - epose proof (IHh _ _ H3) as IHh0.
    destruct t0.
    + des IHh0.
      specialize (IHh _ _ I).
      destruct t'; [lia|].
      des IHh.
      eex.
      1: eapply LC_d2,I2.
      2: lia.
      eapply segRLs_sideRLs_concat.
      2: eapply sideRLs_trans.
      2: apply I0.
      2: apply I3.
      esx.
    + des IHh0.
      eex.
      1: eapply LC_d1,I.
      2: lia.
      ssc I0.
      esx.
  - specialize (IHh _ _ H3).
    destruct t0.
    + des IHh.
      eex.
      1: eapply LC_d3,I.
      2: lia.
      ssc I0.
      esx.
    + des IHh.
      eex.
      1: eapply LC_d2,I.
      2: lia.
      ssc I0.
      esx.
  - epose proof (IHh _ _ H3) as IHh0.
    destruct t0.
    + des IHh0.
      specialize (IHh _ _ I).
      destruct t'; [lia|].
      des IHh.
      eex.
      1: eapply LC_00d0,I2.
      2: lia.
      eapply segRLs_sideRLs_concat.
      2: eapply sideRLs_trans.
      2: apply I0.
      2: apply I3.
      esx.
    + des IHh0.
      eex.
      1: eapply LC_d3,I.
      2: lia.
      ssc I0.
      esx.
Qed.

Definition RC a b :=
  [0;1]^^a *> [1;0;1;1;1] *> [0;1;1;0;1]^^b *> 0inf.

Lemma RInc l a b:
  l {{{ (hR,R) }}} (RC a b) -->*
  l {{{ (hL,L) }}} (RC (S a) (S b)).
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv l a b:
  l {{{ (hR,R) }}} (RC (3+a) b) -->+
  l <* d1 {{{ (hR,R) }}} (RC a b).
Proof.
  unfold RC.
  es.
Qed.

Definition S' '(l,a,b) := l {{{ (hR,R) }}} RC a b.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (dh<*<[0;0],7,57)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(l,a,b) => exists d h, LC l d h /\ 3<=d+a).
  2: eex.
  2: econstructor.
  2: lia.
  intros [[l a] b] [d [h [I I0]]].
  unfold S'.
  destruct d.
  - replace a with (3+(a-3)) by lia.
    eexists (_,_,_); split.
    + eapply ROv.
    + eex.
      1: econstructor; apply I.
      lia.
  - epose proof (LC_spec _ _ _ I) as HLC.
    des HLC.
    eapply sideRLs_1 in I2.
    eexists (_,_,_); split.
    + follow RInc.
      apply unflip_progress in I2.
      apply I2.
    + eex.
      1: apply I1.
      lia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB0RA_0LC---_1RD1RF_0LE0RD_1RC1LF_1LC0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (C,[0]).
Notation hR := (D,[1;1]).
Notation hR' := (D,[0;0;0;0;1;1]).
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].
Notation hRL := [(hR,hL)].

Notation d0 := [0;1;1;0;1;1].
Notation d1 := [0;0;1;1;0;0;1;1].

Inductive LC: side->nat->nat->Prop :=
| LC_dh0: LC ([1;1;1;1;0;1;1;1;1;0;0;0;0;0;0;1;1;1;1;1;1;0;1]*>0inf) 0 O
| LC_dh1: LC ([0;1;0;0;0;1;1;0;1;0;0;1;1;1;1;1;1;0;1]*>0inf) 1 O
| LC_dh2: LC ([0;0;0;0;0;0;1;1;0;1;0;0;1;1;1;1;1;1;0;1]*>0inf) 2 O
| LC_dh3: LC ([0;0;1;1;1;1;1;1;0;0;0;0;0;1;1;1;1;1;1;0;1]*>0inf) 3 O
| LC_dh4: LC ([0;1;1;1;0;1;0;0;0;1;1;1;1;1;1;0;1]*>0inf) 4 O
| LC_dh5: LC ([0;0;0;1;1;0;1;0;0;0;1;1;1;1;1;1;0;1]*>0inf) 5 O
| LC_d0 l t h:
  LC l t h ->
  LC (d0*>l) 6 (S h)
| LC_d05 l t h:
  LC l t h ->
  3<=t ->
  LC ([0;1;1;0;0;0;0;0;1;1]*>l) 5 (S h)
| LC_d04 l t h:
  LC l t h ->
  3<=t ->
  LC ([0;1;1;0;1;0;0;1;1]*>l) 4 (S h)
| LC_d03 l t h:
  LC l t h ->
  2<=t ->
  LC ([0;1;1;1;1;0;0;1;1]*>l) 3 (S h)
| LC_d02 l t h:
  LC l t h ->
  1<=t ->
  LC ([0;0;0;1;1;0;0;1;1]*>l) 2 (S h)
| LC_d01 l t h:
  LC l t h ->
  1<=t ->
  LC ([0;1;1;1;0;0;1;1]*>l) 1 (S h)
| LC_d1 l t h:
  LC l t h ->
  LC (d1*>l) 6 (S h)
| LC_d15 l t h:
  LC l t h ->
  4<=t ->
  LC ([0;0;1;1;0;0;0;0;0;0;1;1]*>l) 5 (S h)
| LC_d14 l t h:
  LC l t h ->
  4<=t ->
  LC ([0;0;1;1;0;1;0;0;0;1;1]*>l) 4 (S h)
| LC_d13 l t h:
  LC l t h ->
  3<=t ->
  LC ([0;0;1;1;1;1;1;1;0;1;1]*>l) 3 (S h)
| LC_d12 l t h:
  LC l t h ->
  2<=t ->
  LC ([0;0;0;0;0;0;1;1;0;1;1]*>l) 2 (S h)
| LC_d11 l t h:
  LC l t h ->
  2<=t ->
  LC ([0;1;0;0;0;1;1;0;1;1]*>l) 1 (S h)
| LC_d10 l t h:
  LC l t h ->
  1<=t ->
  LC ([1;1;1;1;0;1;1;0;1;1]*>l) 0 (S h)
.

Ltac eex :=
  repeat eexists.

Ltac des H :=
  let l':=fresh "l'" in
  let t':=fresh "t'" in
  let I:=fresh "I" in
  let I0:=fresh "I" in
  let I1:=fresh "I" in
  destruct H as [l' [t' [I [I0 I1]]]].

Ltac ssc H :=
  eapply segRLs_sideRLs_concat; [|apply H].

Lemma LC_spec l t h:
  LC l t h ->
  match t with
  | S t => exists l' t', LC l' t' h /\ sideRLs tm' hLR l l' /\ t<=t'
  | O => exists l' t', LC l' t' h /\ sideRLs tm' hLR' l l' /\ 5<=t'
  end.
Proof.
  gen l t.
  induction h; intros.
  {
    inverts H.
    - eex.
      1: apply LC_dh5.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh0.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh1.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh2.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh3.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh4.
      2: lia.
      esx.
  }
  inverts H.
  - destruct t0.
    + specialize (IHh _ _ H3).
      des IHh.
      eex.
      1: eapply LC_d05.
      1: eapply I.
      1,3: lia.
      ssc I0; esx.
    + specialize (IHh _ _ H3).
      des IHh.
      eex.
      1: eapply LC_d0,I.
      2: lia.
      ssc I0; esx.
  - eex.
    1: eapply LC_d04.
    1: eapply H1.
    1,3: lia.
    esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d03.
    1: eapply I.
    1,3: lia.
    ssc I0; esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d02.
    1: eapply I.
    1,3: lia.
    ssc I0; esx.
  - eex.
    1: eapply LC_d01.
    1: eapply H1.
    1,3: lia.
    esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d1.
    1: eapply I.
    2: lia.
    ssc I0; esx.
  - destruct t0.
    + specialize (IHh _ _ H3).
      des IHh.
      eex.
      1: eapply LC_d15.
      1: eapply I.
      1,3: lia.
      ssc I0; esx.
    + specialize (IHh _ _ H3).
      des IHh.
      eex.
      1: eapply LC_d1,I.
      2: lia.
      ssc I0; esx.
  - eex.
    1: eapply LC_d14.
    1: eapply H1.
    1,3: lia.
    esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d13.
    1: eapply I.
    1,3: lia.
    ssc I0; esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d12.
    1: eapply I.
    1,3: lia.
    ssc I0; esx.
  - eex.
    1: eapply LC_d11.
    1: eapply H1.
    1,3: lia.
    esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d10.
    1: eapply I.
    1,3: lia.
    ssc I0; esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d0.
    1: eapply I.
    2: lia.
    ssc I0; esx.
Qed.

Inductive Tp := R0|R1|R2|R3.

Definition RC t a b :=
[1;1;0]^^a *>
match t with
| R0 => [1;1;1;1] *> [1;1;1;0]^^(2+b) *> 0inf
| R1 => [1;0;1;0] *> [1;1;1;0]^^(2+b) *> 0inf
| R2 => [1;1;1;1] *> [1;1;1;0]^^(2+b) *> [1] *> 0inf
| R3 => [1;0;1;0] *> [1;1;1;0]^^(2+b) *> [1] *> 0inf
end.

Lemma RInc l t a b:
  l {{{ (hR,R) }}} (RC t (a) (b)) -->*
  match t with
  | R0 => l {{{ (hL,L) }}} (RC R1 (1+a) (b))
  | R1 => l {{{ (hL,L) }}} (RC R2 (a) (b))
  | R2 => l {{{ (hL,L) }}} (RC R3 (1+a) (b))
  | R3 => l {{{ (hL,L) }}} (RC R0 (a) (1+b))
  end.
Proof.
  unfold RC.
  destruct t; es.
Qed.

Lemma ROv l t a b:
  l {{{ (hR,R) }}} (RC t (2+a) b) -->+
  l <* d0 {{{ (hR,R) }}} (RC t a b).
Proof.
  unfold RC.
  es.
Qed.

Definition S' '(l,t,a,b) := l {{{ (hR,R) }}} RC t a b.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (d1*>d1*>[0;1;0;0;0;1;1;0;1;0;0;1;1;1;1;1;1;0;1]*>0inf,R0,11,8)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(l,t,a,b) => exists d h, LC l d h /\
  match t with
  | R0 | R2 => 2<=(d+1)/2+a
  | R1 | R3 => 2<=d/2+a
  end).
  2: eex.
  2: do 3 econstructor.
  2: lia.
  intros [[[l t] a] b] [d [h [I I0]]].
  unfold S'.
  destruct d.
  - replace a with (2+(a-2)) by (destruct t; lia).
    eexists (_,_,_,_); split.
    + eapply ROv.
    + eex.
      1: econstructor; apply I.
      destruct t; lia.
  - epose proof (LC_spec _ _ _ I) as HLC.
    destruct t.
    all:
    des HLC;
    eapply sideRLs_1 in I2;
    eexists (_,_,_,_); split;
    [ follow RInc;
      apply unflip_progress in I2;
      apply I2
    | eex; [apply I1|]; lia ].
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC1RD_0LA0RC_1LB0LE_1LF0RE_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (B,[0]).
Notation hR := (C,[1;1]).
Notation hR' := (C,[0;0;0;0;1;1]).
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].
Notation hRL := [(hR,hL)].

Notation d0 := [0;1;1;0;1;1].
Notation d1 := [0;0;1;1;0;0;1;1].

Inductive LC: side->nat->nat->Prop :=
| LC_dh0: LC ([1;1;1;1;0;1;1;1;1;0;0;0;0;0;0;1;1;1;1;1;1;0;1]*>0inf) 0 O
| LC_dh1: LC ([0;1;0;0;0;1;1;0;1;0;0;1;1;1;1;1;1;0;1]*>0inf) 1 O
| LC_dh2: LC ([0;0;0;0;0;0;1;1;0;1;0;0;1;1;1;1;1;1;0;1]*>0inf) 2 O
| LC_dh3: LC ([0;0;1;1;1;1;1;1;0;0;0;0;0;1;1;1;1;1;1;0;1]*>0inf) 3 O
| LC_dh4: LC ([0;1;1;1;0;1;0;0;0;1;1;1;1;1;1;0;1]*>0inf) 4 O
| LC_dh5: LC ([0;0;0;1;1;0;1;0;0;0;1;1;1;1;1;1;0;1]*>0inf) 5 O
| LC_d0 l t h:
  LC l t h ->
  LC (d0*>l) 6 (S h)
| LC_d05 l t h:
  LC l t h ->
  3<=t ->
  LC ([0;1;1;0;0;0;0;0;1;1]*>l) 5 (S h)
| LC_d04 l t h:
  LC l t h ->
  3<=t ->
  LC ([0;1;1;0;1;0;0;1;1]*>l) 4 (S h)
| LC_d03 l t h:
  LC l t h ->
  2<=t ->
  LC ([0;1;1;1;1;0;0;1;1]*>l) 3 (S h)
| LC_d02 l t h:
  LC l t h ->
  1<=t ->
  LC ([0;0;0;1;1;0;0;1;1]*>l) 2 (S h)
| LC_d01 l t h:
  LC l t h ->
  1<=t ->
  LC ([0;1;1;1;0;0;1;1]*>l) 1 (S h)
| LC_d1 l t h:
  LC l t h ->
  LC (d1*>l) 6 (S h)
| LC_d15 l t h:
  LC l t h ->
  4<=t ->
  LC ([0;0;1;1;0;0;0;0;0;0;1;1]*>l) 5 (S h)
| LC_d14 l t h:
  LC l t h ->
  4<=t ->
  LC ([0;0;1;1;0;1;0;0;0;1;1]*>l) 4 (S h)
| LC_d13 l t h:
  LC l t h ->
  3<=t ->
  LC ([0;0;1;1;1;1;1;1;0;1;1]*>l) 3 (S h)
| LC_d12 l t h:
  LC l t h ->
  2<=t ->
  LC ([0;0;0;0;0;0;1;1;0;1;1]*>l) 2 (S h)
| LC_d11 l t h:
  LC l t h ->
  2<=t ->
  LC ([0;1;0;0;0;1;1;0;1;1]*>l) 1 (S h)
| LC_d10 l t h:
  LC l t h ->
  1<=t ->
  LC ([1;1;1;1;0;1;1;0;1;1]*>l) 0 (S h)
.

Ltac eex :=
  repeat eexists.

Ltac des H :=
  let l':=fresh "l'" in
  let t':=fresh "t'" in
  let I:=fresh "I" in
  let I0:=fresh "I" in
  let I1:=fresh "I" in
  destruct H as [l' [t' [I [I0 I1]]]].

Ltac ssc H :=
  eapply segRLs_sideRLs_concat; [|apply H].

Lemma LC_spec l t h:
  LC l t h ->
  match t with
  | S t => exists l' t', LC l' t' h /\ sideRLs tm' hLR l l' /\ t<=t'
  | O => exists l' t', LC l' t' h /\ sideRLs tm' hLR' l l' /\ 5<=t'
  end.
Proof.
  gen l t.
  induction h; intros.
  {
    inverts H.
    - eex.
      1: apply LC_dh5.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh0.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh1.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh2.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh3.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh4.
      2: lia.
      esx.
  }
  inverts H.
  - destruct t0.
    + specialize (IHh _ _ H3).
      des IHh.
      eex.
      1: eapply LC_d05.
      1: eapply I.
      1,3: lia.
      ssc I0; esx.
    + specialize (IHh _ _ H3).
      des IHh.
      eex.
      1: eapply LC_d0,I.
      2: lia.
      ssc I0; esx.
  - eex.
    1: eapply LC_d04.
    1: eapply H1.
    1,3: lia.
    esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d03.
    1: eapply I.
    1,3: lia.
    ssc I0; esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d02.
    1: eapply I.
    1,3: lia.
    ssc I0; esx.
  - eex.
    1: eapply LC_d01.
    1: eapply H1.
    1,3: lia.
    esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d1.
    1: eapply I.
    2: lia.
    ssc I0; esx.
  - destruct t0.
    + specialize (IHh _ _ H3).
      des IHh.
      eex.
      1: eapply LC_d15.
      1: eapply I.
      1,3: lia.
      ssc I0; esx.
    + specialize (IHh _ _ H3).
      des IHh.
      eex.
      1: eapply LC_d1,I.
      2: lia.
      ssc I0; esx.
  - eex.
    1: eapply LC_d14.
    1: eapply H1.
    1,3: lia.
    esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d13.
    1: eapply I.
    1,3: lia.
    ssc I0; esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d12.
    1: eapply I.
    1,3: lia.
    ssc I0; esx.
  - eex.
    1: eapply LC_d11.
    1: eapply H1.
    1,3: lia.
    esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d10.
    1: eapply I.
    1,3: lia.
    ssc I0; esx.
  - specialize (IHh _ _ H1).
    destruct t0; [lia|].
    des IHh.
    eex.
    1: eapply LC_d0.
    1: eapply I.
    2: lia.
    ssc I0; esx.
Qed.

Inductive Tp := R0|R1|R2|R3.

Definition RC t a b :=
[1;1;0]^^a *>
match t with
| R0 => [1;1;1;1] *> [1;1;1;0]^^(1+b) *> [1]^^5 *> 0inf
| R1 => [1;0;1;0] *> [1;1;1;0]^^(1+b) *> [1]^^5 *> 0inf
| R2 => [1;1;1;1] *> [1;1;1;0]^^(1+b) *> [1;0;1;0] *> 0inf
| R3 => [1;0;1;0] *> [1;1;1;0]^^(1+b) *> [1;0;1;0] *> 0inf
end.

Lemma RInc l t a b:
  l {{{ (hR,R) }}} (RC t (a) (b)) -->*
  match t with
  | R0 => l {{{ (hL,L) }}} (RC R1 (1+a) (b))
  | R1 => l {{{ (hL,L) }}} (RC R2 (a) (1+b))
  | R2 => l {{{ (hL,L) }}} (RC R3 (1+a) (b))
  | R3 => l {{{ (hL,L) }}} (RC R0 (a) (b))
  end.
Proof.
  unfold RC.
  destruct t; es.
Qed.

Lemma ROv l t a b:
  l {{{ (hR,R) }}} (RC t (2+a) b) -->+
  l <* d0 {{{ (hR,R) }}} (RC t a b).
Proof.
  unfold RC.
  es.
Qed.

Definition S' '(l,t,a,b) := l {{{ (hR,R) }}} RC t a b.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (d1*>d1*>[0;1;0;0;0;1;1;0;1;0;0;1;1;1;1;1;1;0;1]*>0inf,R0,11,8)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(l,t,a,b) => exists d h, LC l d h /\
  match t with
  | R0 | R2 => 2<=(d+1)/2+a
  | R1 | R3 => 2<=d/2+a
  end).
  2: eex.
  2: do 3 econstructor.
  2: lia.
  intros [[[l t] a] b] [d [h [I I0]]].
  unfold S'.
  destruct d.
  - replace a with (2+(a-2)) by (destruct t; lia).
    eexists (_,_,_,_); split.
    + eapply ROv.
    + eex.
      1: econstructor; apply I.
      destruct t; lia.
  - epose proof (LC_spec _ _ _ I) as HLC.
    destruct t.
    all:
    des HLC;
    eapply sideRLs_1 in I2;
    eexists (_,_,_,_); split;
    [ follow RInc;
      apply unflip_progress in I2;
      apply I2
    | eex; [apply I1|]; lia ].
Qed.

End TM7.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC0LE_1LC1LD_0RA1LB_---0LF_0LA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;1;1;1].
Notation d2 := <[1;0;1;1].
Notation d3 := <[1;0;1;1;1].
Notation d4 := <[1;0;1;1;1;1].

Inductive Tp := t0|t2.

Inductive RC: side->Tp->nat->nat->Prop :=
| RC_O n: RC (0inf<*<[1;0;1]^^n) t0 n O
| RC_S0_d0 l n h: RC l t0 n h -> RC (l<*d0) t0 n (S h)
| RC_S0_d4 l n h: RC l t0 n h -> RC (l<*d4) t0 n (S h)
| RC_S0_d3 l n h: RC l t2 n h -> RC (l<*d3) t0 n (S h)
| RC_S2_d0 l n h: RC l t2 n h -> RC (l<*d0) t2 n (S h)
| RC_S2_d2 l n h: RC l t2 n h -> RC (l<*d2) t2 n (S h)
| RC_S2_d3 l n h: RC l t0 n h -> RC (l<*d3) t2 n (S h)
.

Notation hLA := (F,[1]).
Notation hLA1 := (F,[1;1]).
Notation hLD := (D,[1;1]).
Notation hLD1 := (D,[1;1;1]).
Notation hLB := (B,[1;1;1]).
Notation hLB1 := (B,[1;1;1;1]).
Notation hR := (A,[]).

Notation hLRA := [(hLA,hR)].
Notation hLRA1 := [(hLA1,hR)].
Notation hLRD := [(hLD,hR)].
Notation hLRD1 := [(hLD1,hR)].
Notation hLRB := [(hLB,hR)].
Notation hLRB1 := [(hLB1,hR)].

Definition tm' := flip tm.

Ltac eex :=
  repeat eexists.

Ltac des H :=
  let l':=fresh "l'" in
  let I:=fresh "I" in
  let I0:=fresh "I" in
  destruct H as [l' [I I0]].

Ltac ssc H :=
  eapply segRLs_sideRLs_concat; [|apply H].

Lemma RC_spec_0 l t n h:
  RC l t n h ->
  exists l',
  RC l' t (1+n) h /\
  sideRLs tm' hLRA l l'.
Proof.
  intros H.
  induction H.
  - eex.
    1: apply RC_O.
    esx.
  - des IHRC.
    eex.
    1: apply RC_S0_d0,I.
    ssc I0; esx.
  - des IHRC.
    eex.
    1: apply RC_S0_d4,I.
    ssc I0; esx.
  - des IHRC.
    eex.
    1: apply RC_S0_d3,I.
    ssc I0; esx.
  - des IHRC.
    eex.
    1: apply RC_S2_d0,I.
    ssc I0; esx.
  - des IHRC.
    eex.
    1: apply RC_S2_d2,I.
    ssc I0; esx.
  - des IHRC.
    eex.
    1: apply RC_S2_d3,I.
    ssc I0; esx.
Qed.

Ltac des1 H :=
  let l':=fresh "l'" in
  let n':=fresh "n'" in
  let h':=fresh "h'" in
  let I:=fresh "I" in
  let I0:=fresh "I" in
  let J:=fresh "J" in
  destruct H as [l' [n' [h' [I [J I0]]]]].

Ltac eex ::=
  do 3 eexists; split; [| split].

Lemma RC_spec l t n h:
  RC l t n h ->
  match t with
  | t0 =>
    (n>=1 -> exists l' n' h',
    RC l' t0 n' h' /\
    (1+n'>=n /\ (h>=1 -> (n'>=1 /\ h'>=1))) /\
    sideRLs tm' hLRD1 l l') /\
    (n>=1 -> exists l' n' h',
    RC l' t2 n' h' /\
    (1+n'>=n /\ (h>=1 -> (n'>=1 /\ h'>=1))) /\
    sideRLs tm' hLRD l l')
  | t2 =>
    (n>=0 -> exists l' n' h',
    RC l' t0 n' h' /\
    n'>=n+1 /\
    sideRLs tm' hLRB1 l l') /\
    (n>=0 -> exists l' n' h',
    RC l' t2 n' h' /\
    n'>=n+1 /\
    sideRLs tm' hLRB l l') /\
    (n>=0 -> exists l' n' h',
    RC l' t0 n' h' /\
    n'>=n+1 /\
    sideRLs tm' hLRA1 l l')
  end.
Proof.
  gen l t n.
  induction h; intros.
  {
    inverts H.
    split; intros.
    - replace n with (1+(n-1)) by lia.
      eex.
      1: eapply RC_S0_d4.
      1: eapply RC_O with (n:=0+(n-1)).
      1: lia.
      esx.
    - replace n with (1+(n-1)) by lia.
      eex.
      1: eapply RC_S2_d3.
      1: eapply RC_O with (n:=0+(n-1)).
      1: lia.
      esx.
  }
  inverts H.
  all: repeat split; intros.
  - epose proof (RC_spec_0 _ _ _ _ H4) as IHh0.
    des IHh0.
    eex.
    1: eapply RC_S0_d4,I.
    1: lia.
    ssc I0; esx.
  - epose proof (RC_spec_0 _ _ _ _ H4) as IHh0.
    des IHh0.
    eex.
    1: eapply RC_S2_d3,I.
    1: lia.
    ssc I0; esx.
  - epose proof (RC_spec_0 _ _ _ _ H4) as IHh0.
    des IHh0.
    epose proof (IHh _ _ _ I) as IHh1.
    destruct IHh1 as [_ X1].
    des1 X1.
    1: lia.
    epose proof (RC_spec_0 _ _ _ _ I1) as IHh2.
    des IHh2.
    eex.
    1: eapply RC_S0_d3,I3.
    1: lia.
    eapply segRLs_sideRLs_concat.
    2:{
      eapply sideRLs_trans.
      1: apply I0.
      eapply sideRLs_trans.
      1: apply I2.
      apply I4.
    }
    esx.
  - epose proof (RC_spec_0 _ _ _ _ H4) as IHh0.
    des IHh0.
    epose proof (IHh _ _ _ I) as IHh1.
    destruct IHh1 as [_ X1].
    des1 X1.
    1: lia.
    epose proof (RC_spec_0 _ _ _ _ I1) as IHh2.
    des IHh2.
    eex.
    1: eapply RC_S2_d2,I3.
    1: lia.
    eapply segRLs_sideRLs_concat.
    2:{
      eapply sideRLs_trans.
      1: apply I0.
      eapply sideRLs_trans.
      1: apply I2.
      apply I4.
    }
    esx.
  - specialize (IHh _ _ _ H4).
    destruct IHh as [X1 _].
    des1 X1.
    1: lia.
    eex.
    1: eapply RC_S0_d0,I.
    1: lia.
    ssc I0; esx.
  - specialize (IHh _ _ _ H4).
    destruct IHh as [_ [X1 _]].
    des1 X1.
    1: lia.
    eex.
    1: eapply RC_S2_d0,I.
    1: lia.
    ssc I0; esx.
  - specialize (IHh _ _ _ H4).
    destruct IHh as [_ [_ X1]].
    des1 X1.
    1: lia.
    eex.
    1: eapply RC_S0_d4,I.
    1: lia.
    ssc I0; esx.
  - specialize (IHh _ _ _ H4).
    destruct IHh as [_ [_ X1]].
    des1 X1.
    1: lia.
    eex.
    1: eapply RC_S2_d3,I.
    1: lia.
    ssc I0; esx.
  - specialize (IHh _ _ _ H4).
    destruct IHh as [_ [_ X1]].
    des1 X1.
    1: lia.
    eex.
    1: eapply RC_S0_d0,I.
    1: lia.
    ssc I0; esx.
  - specialize (IHh _ _ _ H4).
    destruct IHh as [X1 _].
    des1 X1.
    1: lia.
    eex.
    1: eapply RC_S0_d0,I.
    1: lia.
    ssc I0; esx.
  - specialize (IHh _ _ _ H4).
    destruct IHh as [_ [X1 _]].
    des1 X1.
    1: lia.
    eex.
    1: eapply RC_S2_d0,I.
    1: lia.
    ssc I0; esx.
  - epose proof (RC_spec_0 _ _ _ _ H4) as IHh0.
    des IHh0.
    eex.
    1: eapply RC_S0_d3,I.
    1: lia.
    ssc I0; esx.
  - epose proof (RC_spec_0 _ _ _ _ H4) as IHh0.
    des IHh0.
    epose proof (IHh _ _ _ I) as IHh1.
    destruct IHh1 as [_ X1].
    des1 X1.
    1: lia.
    epose proof (RC_spec_0 _ _ _ _ I1) as IHh2.
    des IHh2.
    eex.
    1: eapply RC_S0_d3,I3.
    1: lia.
    eapply segRLs_sideRLs_concat.
    2:{
      eapply sideRLs_trans.
      1: apply I0.
      eapply sideRLs_trans.
      1: apply I2.
      apply I4.
    }
    esx.
  - epose proof (RC_spec_0 _ _ _ _ H4) as IHh0.
    des IHh0.
    epose proof (IHh _ _ _ I) as IHh1.
    destruct IHh1 as [_ X1].
    des1 X1.
    1: lia.
    epose proof (RC_spec_0 _ _ _ _ I1) as IHh2.
    des IHh2.
    eex.
    1: eapply RC_S2_d2,I3.
    1: lia.
    eapply segRLs_sideRLs_concat.
    2:{
      eapply sideRLs_trans.
      1: apply I0.
      eapply sideRLs_trans.
      1: apply I2.
      apply I4.
    }
    esx.
  - epose proof (RC_spec_0 _ _ _ _ H4) as IHh0.
    des IHh0.
    eex.
    1: eapply RC_S0_d4,I.
    1: lia.
    ssc I0; esx.
Qed.

Definition S' l := l {{{ (hLD1,L) }}} 0inf.

Ltac eex ::=
  repeat eexists.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (0inf <* [1;0;1]^^1 <* d3 <* d3 <* d0)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun l => exists n h, RC l t0 n h /\ n>=1 /\ h>=1).
  2: eex.
  2: repeat econstructor.
  2,3: lia.
  intros l [n [h [I [I0 I1]]]].
  unfold S'.
  apply RC_spec in I.
  destruct I as [X1 _].
  des1 X1.
  1: lia.
  exists l'.
  eex.
  - eapply sideRLs_1 in I2.
    apply unflip_progress in I2.
    follow10 I2.
    es.
  - apply I.
  - lia.
  - lia.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0RA_1LE1LD_0LC---_1LF0LB_1RB0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (C,[]).
Notation hR := (A,[0;1;0]).
Notation hR' := (A,[0;0;1;0]).
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].
Notation hRL := [(hR,hL)].

Notation d0 := [1;0;1;0;1;0].
Notation d1 := [1;0;1;0;0;1;0].
Notation d2 := [0;1;0;1;0].
Notation d3 := [0;1;0;0;1;0].
Notation dx := [0;0;0;0].
Notation d1a := [1;0;1;0;0;0;1;0].
Notation d1b := ([1]++dx++d0).
Notation d1c := ([0;1]++d0).
Notation d3a := [0;1;0;0;0;1;0].
Notation d3b := (dx++d0).

Inductive LC: side->nat->nat->Prop :=
| LC_dh0: LC (dx*>d1a*>0inf) 0 O
| LC_dh4: LC (d1a*>0inf) 4 O
| LC_dh3: LC ([1]*>dx*>d1a*>0inf) 3 O
| LC_dh2: LC ([0;1]*>d1a*>0inf) 2 O
| LC_dh1: LC (d3a*>0inf) 1 O
| LC_d0 l t h:
  LC l t h ->
  LC (d0*>l) 3 (S h)
| LC_d1 l t h:
  LC l t h ->
  LC (d1*>l) 2 (S h)
| LC_d1a l t h:
  LC l t h ->
  2<=t ->
  LC (d1a*>l) 3 (S h)
| LC_d1b l t h:
  LC l t h ->
  LC (d1b*>l) 2 (S h)
| LC_d1c l t h:
  LC l t h ->
  LC (d1c*>l) 1 (S h)
| LC_d2 l t h:
  LC l t h ->
  LC (d2*>l) 1 (S h)
| LC_d3 l t h:
  LC l t h ->
  LC (d3*>l) (2+t) (S h)
| LC_d3a l t h:
  LC l t h ->
  2<=t ->
  LC (d3a*>l) 1 (S h)
| LC_d3b l t h:
  LC l t h ->
  LC (d3b*>l) 0 (S h)
.

Ltac eex :=
  repeat eexists.

Ltac des H :=
  let l':=fresh "l'" in
  let t':=fresh "t'" in
  let I:=fresh "I" in
  let I0:=fresh "I" in
  let I1:=fresh "I" in
  destruct H as [l' [t' [I [I0 I1]]]].

Ltac ssc H :=
  eapply segRLs_sideRLs_concat; [|apply H].

Lemma LC_spec l t h:
  LC l t h ->
  match t with
  | S t => exists l' t', LC l' t' h /\ sideRLs tm' hLR l l' /\ t<=t'
  | O => exists l' t', LC l' t' h /\ sideRLs tm' hLR' l l' /\ 2<=t'
  end.
Proof.
  gen l t.
  induction h; intros.
  {
    inverts H.
    - eex.
      1: apply LC_dh4.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh3.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh2.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh1.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh0.
      2: lia.
      esx.
  }
  inverts H.
  - specialize (IHh _ _ H3).
    destruct t0.
    + des IHh.
      eex.
      1: eapply LC_d1,I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_d0,I.
      2: lia.
      ssc I0; esx.
  - specialize (IHh _ _ H3).
    destruct t0.
    + des IHh.
      eex.
      1: eapply LC_d1a.
      1: apply I.
      1,3: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_d1,I.
      2: lia.
      ssc I0; esx.
  - epose proof (IHh _ _ H1) as IHh0.
    destruct t0; [lia|].
    des IHh0.
    epose proof (IHh _ _ I) as IHh1.
    destruct t'; [lia|].
    des IHh1.
    eex.
    1: eapply LC_d1b,I2.
    2: lia.
    eapply segRLs_sideRLs_concat.
    2: eapply sideRLs_trans; eassumption.
    esx.
  - eex.
    eapply LC_d1c,H3.
    2: lia.
    esx.
  - eex.
    eapply LC_d2,H3.
    2: lia.
    esx.
  - specialize (IHh _ _ H3).
    destruct t0.
    + des IHh.
      eex.
      1: eapply LC_d3,I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_d2,I.
      2: lia.
      ssc I0; esx.
  - specialize (IHh _ _ H3).
    destruct t0.
    + des IHh.
      eex.
      1: eapply LC_d3a.
      1: eapply I.
      1,3: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_d3,I.
      2: lia.
      ssc I0; esx.
  - epose proof (IHh _ _ H1) as IHh0.
    destruct t0; [lia|].
    des IHh0.
    epose proof (IHh _ _ I) as IHh1.
    destruct t'; [lia|].
    des IHh1.
    eex.
    1: eapply LC_d3b,I2.
    2: lia.
    eapply segRLs_sideRLs_concat.
    2: eapply sideRLs_trans; eassumption.
    esx.
  - eex.
    eapply LC_d0,H3.
    2: lia.
    esx.
Qed.

Definition RC a :=
  [0;1;1;0;1]^^a *> [0;1;1] *> 0inf.

Lemma RInc l a:
  l {{{ (hR,R) }}} (RC a) -->*
  l {{{ (hL,L) }}} (RC (S a)).
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv l a:
  l {{{ (hR,R) }}} (RC (1+a)) -->+
  l <* d2 {{{ (hR,R) }}} (RC a).
Proof.
  unfold RC.
  es.
Qed.

Definition S' '(l,a) := l {{{ (hR,R) }}} RC a.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (d3*>d1a*>0inf,1)%nat).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(l,a) => exists d h, LC l d h /\ 1<=d+a).
  2: eex.
  2: do 2 econstructor.
  2: lia.
  intros [l a] [d [h [I I0]]].
  unfold S'.
  destruct d.
  - replace a with (1+(a-1)) by lia.
    eexists (_,_); split.
    + eapply ROv.
    + eex.
      1: econstructor; apply I.
      lia.
  - epose proof (LC_spec _ _ _ I) as HLC.
    des HLC.
    eapply sideRLs_1 in I2.
    eexists (_,_); split.
    + follow RInc.
      apply unflip_progress in I2.
      apply I2.
    + eex.
      1: apply I1.
      lia.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC1LA_1RE0LD_1LC1LB_---0RA_1RD0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (C,[]).
Notation hR := (D,[1;0;0;1;0]).
Notation hR' := (B,[1;0]).
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].
Notation hRL := [(hR,hL)].

Notation d0 := [1;1;0; 1;0;1;0;1;0].
Notation d1 := [1;1;0; 1;1;0].
Notation d2 := [1;1;0; 1;1;0; 1;0].
Notation d3 := [1;0;1;0; 1;0;1;0;1;0].
Notation d4 := [1;0;1;0; 1;1;0].
Notation d5 := [1;0;1;0; 1;1;0; 1;0].
Notation d5a := [1;0;0; 1;0;1;0;1;0;1;0].
Notation dh := ([1;0;1;1;0;1]*>0inf).

Inductive LC: side->nat->nat->Prop :=
| LC_dh0: LC ([1;0;0]*>dh) 0 O
| LC_dh2: LC ([1]*>dh) 2 O
| LC_dh1: LC ([1;0]*>dh) 1 O
| LC_d0 l t h:
  LC l t h ->
  LC (d0*>l) 6 (S h)
| LC_d1 l t h:
  LC l t h ->
  LC (d1*>l) 5 (S h)
| LC_d2 l t h:
  LC l t h ->
  LC (d2*>l) 4 (S h)
| LC_d3 l t h:
  LC l t h ->
  LC (d3*>l) 3 (S h)
| LC_d4 l t h:
  LC l t h ->
  LC (d4*>l) 2 (S h)
| LC_d5 l t h:
  LC l t h ->
  LC (d5*>l) 1 (S h)
| LC_d5a l t h:
  LC l t h ->
  LC (d5a*>l) 0 (S h)
.

Ltac eex :=
  repeat eexists.

Ltac des H :=
  let l':=fresh "l'" in
  let t':=fresh "t'" in
  let I:=fresh "I" in
  let I0:=fresh "I" in
  let I1:=fresh "I" in
  destruct H as [l' [t' [I [I0 I1]]]].

Ltac ssc H :=
  eapply segRLs_sideRLs_concat; [|apply H].

Lemma LC_spec l t h:
  LC l t h ->
  match t with
  | S t => exists l' t', LC l' t' h /\ sideRLs tm' hLR l l' /\ t<=t'
  | O => exists l' t', LC l' t' h /\ sideRLs tm' hLR' l l' /\ 1<=t'
  end.
Proof.
  gen l t.
  induction h; intros.
  {
    inverts H.
    - eex.
      1: apply LC_dh2.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh1.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh0.
      2: lia.
      esx.
  }
  inverts H.
  - specialize (IHh _ _ H3).
    destruct t0.
    + des IHh.
      eex.
      1: eapply LC_d1,I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_d0,I.
      2: lia.
      ssc I0; esx.
  - epose proof (IHh _ _ H3) as IHh0.
    destruct t0.
    + des IHh0.
      epose proof (IHh _ _ I) as IHh1.
      destruct t'; [lia|].
      des IHh1.
      eex.
      1: eapply LC_d2,I2.
      2: lia.
      eapply segRLs_sideRLs_concat.
      2: eapply sideRLs_trans; eassumption.
      esx.
    + des IHh0.
      eex.
      1: eapply LC_d1,I.
      2: lia.
      ssc I0; esx.
  - epose proof (IHh _ _ H3) as IHh0.
    destruct t0.
    + des IHh0.
      epose proof (IHh _ _ I) as IHh1.
      destruct t'; [lia|].
      des IHh1.
      eex.
      1: eapply LC_d3,I2.
      2: lia.
      eapply segRLs_sideRLs_concat.
      2: eapply sideRLs_trans; eassumption.
      esx.
    + des IHh0.
      eex.
      1: eapply LC_d2,I.
      2: lia.
      ssc I0; esx.
  - specialize (IHh _ _ H3).
    destruct t0.
    + des IHh.
      eex.
      1: eapply LC_d4,I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_d3,I.
      2: lia.
      ssc I0; esx.
  - epose proof (IHh _ _ H3) as IHh0.
    destruct t0.
    + des IHh0.
      epose proof (IHh _ _ I) as IHh1.
      destruct t'; [lia|].
      des IHh1.
      eex.
      1: eapply LC_d5,I2.
      2: lia.
      eapply segRLs_sideRLs_concat.
      2: eapply sideRLs_trans; eassumption.
      esx.
    + des IHh0.
      eex.
      1: eapply LC_d4,I.
      2: lia.
      ssc I0; esx.
  - epose proof (IHh _ _ H3) as IHh0.
    destruct t0.
    + des IHh0.
      epose proof (IHh _ _ I) as IHh1.
      destruct t'; [lia|].
      des IHh1.
      eex.
      1: eapply LC_d5a,I2.
      2: lia.
      eapply segRLs_sideRLs_concat.
      2: eapply sideRLs_trans; eassumption.
      esx.
    + des IHh0.
      eex.
      1: eapply LC_d5,I.
      2: lia.
      ssc I0; esx.
  - eex.
    eapply LC_d0,H3.
    2: lia.
    esx.
Qed.

Definition RC a :=
  [1;0;1;0;1] *> [0;0;1;0;1;0;1;0;1]^^a *> 0inf.

Lemma RInc l a:
  l {{{ (hR,R) }}} (RC a) -->*
  l {{{ (hL,L) }}} (RC (S a)).
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv l a:
  l {{{ (hR,R) }}} (RC (1+a)) -->+
  l <* d0 {{{ (hR,R) }}} (RC a).
Proof.
  unfold RC.
  es.
Qed.

Definition S' '(l,a) := l {{{ (hR,R) }}} RC a.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' ([1;0;0]*>dh,1%nat)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(l,a) => exists d h, LC l d h /\ 1<=d+a).
  2: eex.
  2: econstructor.
  2: lia.
  intros [l a] [d [h [I I0]]].
  unfold S'.
  destruct d.
  - replace a with (1+(a-1)) by lia.
    eexists (_,_); split.
    + eapply ROv.
    + eex.
      1: econstructor; apply I.
      lia.
  - epose proof (LC_spec _ _ _ I) as HLC.
    des HLC.
    eapply sideRLs_1 in I2.
    eexists (_,_); split.
    + follow RInc.
      apply unflip_progress in I2.
      apply I2.
    + eex.
      1: apply I1.
      lia.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1LE_0LD1LC_1RD1RE_1LF0RA_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (C,[1]).
Notation hR := (A,[1;1]).
Notation hLx := (B,[0]).
Notation hRx := (B,[1;1]).
Notation hLR := [(hL,hR);(hL,hR)].
Notation hLRx := [(hLx,hRx);(hLx,hRx)].

Notation a0 := [1;1;1;1;1].
Notation a1 := [1;1;1;0;1].
Notation a2 := [0;1;0;1;1].
Notation a3 := [0;1;0;0;1].

Notation b0 := [0;1;1;1;1].
Notation b1 := [0;1;1;0;1].
Notation b2 := [1;0;1;1;1;1;1].
Notation b3 := [1;0;1;1;1;0;1].

Notation rh0 := ([1;1;1]*>0inf).
Notation rh1 := ([0;1]*>0inf).
Notation rh2 := ([0;1;1]*>0inf).

Notation hLR' := [(hL,(A,[0;1]));(hLx,hRx)].
Notation hLRx' := [(hLx,hRx);(hLx,(B,[1;0;1;1]))].

Inductive Tp := tA | tB.

Inductive LC: side->nat->nat->Tp->Prop :=
| LC_dh0: LC rh0 1 O tA
| LC_dh1: LC rh1 0 O tA
| LC_dh2: LC rh2 0 O tB
| LC_a0 l t h:
  LC l t h tA ->
  LC (a0*>l) 2 (S h) tA
| LC_a1 l t h:
  LC l t h tB ->
  LC (a1*>l) 1 (S h) tA
| LC_a1' l t h:
  LC l t h tA ->
  LC ([1;1;1;0;0;1;1]*>l) 1 (S h) tA
| LC_a2 l t h:
  LC l t h tA ->
  LC (a2*>l) 1 (S h) tA
| LC_a3 l t h:
  LC l t h tB ->
  LC (a3*>l) 1 (S h) tA
| LC_a3' l t h:
  LC l t h tA ->
  LC ([0;1;0;0;0;1;1]*>l) 0 (S h) tA
| LC_b0 l t h:
  LC l t h tA ->
  LC (b0*>l) 1 (S h) tB
| LC_b1 l t h:
  LC l t h tB ->
  LC (b1*>l) 1 (S h) tB
| LC_b1' l t h:
  LC l t h tA ->
  1<=t ->
  LC ([0;1;1;0;0;1;1]*>l) 1 (S h) tB
| LC_b2 l t h:
  LC l t h tA ->
  LC (b2*>l) 1 (S h) tB
| LC_b3 l t h:
  LC l t h tB ->
  LC (b3*>l) 1 (S h) tB
| LC_b3' l t h:
  LC l t h tA ->
  LC ([1;0;1;1;1;0;0;1;1]*>l) 0 (S h) tB
  .

Ltac eex :=
  repeat eexists.

Ltac des H :=
  let l':=fresh "l'" in
  let t':=fresh "t'" in
  let I:=fresh "I" in
  let I0:=fresh "I" in
  let I1:=fresh "I" in
  destruct H as [l' [t' [I [I0 I1]]]].

Ltac ssc H :=
  eapply segRLs_sideRLs_concat; [|apply H].

Lemma LC_spec l t h t0:
  LC l t h t0 ->
  match t,t0 with
  | S t,tA => exists l' t', LC l' t' h tA /\ sideRLs tm' hLR l l' /\ t<=t'
  | S t,tB => exists l' t', LC l' t' h tB /\ sideRLs tm' hLRx l l' /\ t<=t'
  | O,tA => exists l' t', LC l' t' h tB /\ sideRLs tm' hLR' l l' /\ 0<=t'
  | O,tB => exists l' t', LC l' t' h tA /\ sideRLs tm' hLRx' l l' /\ 1<=t'
  end.
Proof.
  gen l t t0.
  induction h; intros.
  {
    inverts H.
    - eex.
      1: apply LC_dh1.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh2.
      2: lia.
      esx.
    - eex.
      1: apply LC_dh0.
      2: lia.
      esx.
  }
  inverts H.
  - specialize (IHh _ _ _ H3).
    destruct t1.
    + des IHh.
      eex.
      1: eapply LC_a1,I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_a0,I.
      2: lia.
      ssc I0; esx.
  - specialize (IHh _ _ _ H3).
    destruct t1.
    + des IHh.
      eex.
      1: eapply LC_a1',I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_a1,I.
      2: lia.
      ssc I0; esx.
  - eex.
    1: eapply LC_a2,H3.
    2: lia.
    esx.
  - specialize (IHh _ _ _ H3).
    destruct t1.
    + des IHh.
      eex.
      1: eapply LC_a3,I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_a2,I.
      2: lia.
      ssc I0; esx.
  - specialize (IHh _ _ _ H3).
    destruct t1.
    + des IHh.
      eex.
      1: eapply LC_a3',I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_a3,I.
      2: lia.
      ssc I0; esx.
  - eex.
    1: eapply LC_b0,H3.
    2: lia.
    esx.
  - specialize (IHh _ _ _ H3).
    destruct t1.
    + des IHh.
      eex.
      1: eapply LC_b1,I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_b0,I.
      2: lia.
      ssc I0; esx.
  - specialize (IHh _ _ _ H3).
    destruct t1.
    + des IHh.
      eex.
      1: eapply LC_b1'.
      1: eapply I.
      1,3: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_b1,I.
      2: lia.
      ssc I0; esx.
  - specialize (IHh _ _ _ H1).
    destruct t1; [lia|].
    des IHh.
    eex.
    1: eapply LC_b2,I.
    2: lia.
    ssc I0; esx.
  - specialize (IHh _ _ _ H3).
    destruct t1.
    + des IHh.
      eex.
      1: eapply LC_b3,I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_b2,I.
      2: lia.
      ssc I0; esx.
  - specialize (IHh _ _ _ H3).
    destruct t1.
    + des IHh.
      eex.
      1: eapply LC_b3',I.
      2: lia.
      ssc I0; esx.
    + des IHh.
      eex.
      1: eapply LC_b3,I.
      2: lia.
      ssc I0; esx.
  - eex.
    1: eapply LC_a0,H3.
    2: lia.
    esx.
Qed.

Definition RC a :=
  [1]^^a *> 0inf.

Lemma RInc l a:
  l {{{ (hR,R) }}} (RC a) -->*
  l {{{ (hL,L) }}} (RC (2+a)).
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv l a:
  l {{{ (hR,R) }}} (RC (5+a)) -->+
  l <* a0 {{{ (hR,R) }}} (RC a).
Proof.
  unfold RC.
  es.
Qed.

Definition S' '(l,a) := l {{{ (hR,R) }}} RC a.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (a2*>rh0,6)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(l,a) => exists d h, LC l d h tA /\ 5<=d*4+a).
  2: eex.
  2: do 2 econstructor.
  2: lia.
  intros [l a] [d [h [I I0]]].
  unfold S'.
  destruct d.
  - replace a with (5+(a-5)) by lia.
    eexists (_,_); split.
    + eapply ROv.
    + eex.
      1: econstructor; apply I.
      lia.
  - epose proof (LC_spec _ _ _ _ I) as HLC.
    des HLC.
    eapply @sideRLs_split with (ls1:=[(hL,hR)]) in I2.
    destruct I2 as [l'0 [I2a I2b]].
    eapply sideRLs_1 in I2a,I2b.
    eexists (_,_); split.
    + follow RInc.
      apply unflip_progress in I2a,I2b.
      follow11 I2a.
      follow RInc.
      apply I2b.
    + eex.
      1: apply I1.
      lia.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LD_1RA1RC_1LA0LE_1LF0RC_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity).

Notation a01 := [1;1;0;0;1;1].
Notation a23 := [1;0;1;1].
Notation a4 := [1;0;1;1;1].

Notation b01 := [1;1;1].
Notation b2 := [1;1;0;1].
Notation b3 := [1;1;1;0;0].
Notation b4 := [1;1;1;0;0;1].

Notation h0 := [((C,<[1]),(A,[1;1;0;0;1]))].
Notation h1 := [((C,<[0]),(B,[1]));((C,<[0]),(B,[1;1;0;1;1]))].
Notation h2 := [((E,<[1]),(D,[0]));((E,<[1]),(D,[0;1;1;0;1]))].
Notation h3 := [((C,<[0]),(B,[1;1;1;0;0]))].

Notation h0' := [((C,<[1]),(E,[0;0;1]))].
Notation h1' := [((C,<[0]),(A,[1]));((C,<[0]),(B,[1;1;1;0;0;1]))].
Notation h2' := [((C,<[1]),(E,[0]));((A,<[1]),(D,[0]));((A,<[1]),(E,[0;0;1;1;0;1]))].
Notation h3' := [((E,<[1]),(D,[0]));((E,<[1]),(D,[0;1;1;1;0;0]))].

Inductive Tp := tA | tB.

Inductive LC: side->nat->nat->Tp->Prop :=
| LC_dh0: LC (a01*>0inf) 1 O tA
| LC_dh1: LC (a23*>0inf) 1 O tA
| LC_dh2: LC (a4*>0inf) 1 O tA
| LC_dh3: LC (b01*>0inf) 1 O tB
| LC_dh4: LC (b4*>0inf) 0 O tB
| LC_a01 l t h tp:
  LC l t h tp ->
  LC (a01*>l) 1 (S h) tA
| LC_a23 l t h tp:
  LC l t h tp ->
  LC (a23*>l) 1 (S h) tA
| LC_a4 l t h:
  LC l t h tB ->
  LC (a4*>l) 1 (S h) tA
| LC_b01 l t h tp:
  LC l t h tp ->
  LC (b01*>l) 1 (S h) tB
| LC_b2 l t h:
  LC l t h tB ->
  LC (b2*>l) 1 (S h) tB
| LC_b3 l t h:
  LC l t h tB ->
  LC (b3*>l) 1 (S h) tB
| LC_b4 l t h:
  LC l t h tB ->
  LC (b4*>l) t (S h) tB
  .

Ltac eex := repeat eexists.

Ltac ec := econstructor.

Ltac ssc H :=
  eapply segRLs_sideRLs_concat; [|apply H].

Inductive is_hRL: _->_->Prop :=
| is_h0 tp: is_hRL h0 tp
| is_h1 tp: is_hRL h1 tp
| is_h2: is_hRL h2 tB
| is_h3: is_hRL h3 tB.

Inductive is_hRL': _->_->Prop :=
| is_h0': is_hRL' h0' tA
| is_h1': is_hRL' h1' tB
| is_h2': is_hRL' h2' tB
| is_h3': is_hRL' h3' tB.

Inductive t_mono: _->_->Prop :=
| tAB: t_mono tA tB
| tAA: t_mono tA tA
| tBB: t_mono tB tB.

Lemma LC_spec l t h t0:
  LC l t h t0 ->
  match t with
  | S t =>
    forall hRL,
    is_hRL hRL t0 ->
    exists l' t' t0', LC l' t' h t0' /\ sideRLs tm hRL l l' /\ t<=t' /\ t_mono t0 t0'
  | O =>
    forall hRL' t0',
    is_hRL' hRL' t0' ->
    exists l' t', LC l' t' h t0' /\ sideRLs tm hRL' l l' /\ 1<=t'
  end.
Proof.
  gen l t t0.
  induction h; intros.
  {
    inverts H.
    - introv X; inverts X.
      all: exists (a23*>0inf); eex; [ec|esc|lia|ec].
    - introv X; inverts X.
      all: exists (a4*>0inf); eex; [ec|esc|lia|ec].
    - introv X; inverts X.
      all: exists (b01*>0inf); eex; [ec|esc|lia|ec].
    - introv X; inverts X.
      all: exists (b4*>0inf); eex; [ec|esc|lia|ec].
    - introv X; inverts X.
      1: exists (a01*>0inf); eex; [ec|esc|lia].
      all: exists (b01*>0inf); eex; [ec|esc|lia].
  }
  inverts H.
  - rename H3 into IH.
    apply IHh in IH; clear IHh.
    destruct t1.
    + epose proof (IH _ _ is_h0') as [l' [t' [I1 [I2 I3]]]].
      introv X; inverts X.
      all: eexists (a23*>_); eex; [ec; apply I1 | ssc I2; esc | lia |ec].
    + epose proof (IH _ (is_h0 _)) as [l' [t' [t0' [I1 [I2 [I3 I4]]]]]].
      introv X; inverts X.
      all: eexists (a01*>_); eex; [ec; apply I1 | ssc I2; esc | lia |ec].
  - rename H3 into IH.
    apply IHh in IH; clear IHh.
    destruct t1.
    + epose proof (IH _ _ is_h1') as [l' [t' [I1 [I2 I3]]]].
      introv X; inverts X.
      all: eexists (a4*>_); eex; [ec; apply I1 | ssc I2; esc | lia | ec].
    + epose proof (IH _ (is_h1 _)) as [l' [t' [t0' [I1 [I2 [I3 I4]]]]]].
      introv X; inverts X.
      all: eexists (a23*>_); eex; [ec; apply I1 | ssc I2; esc | lia | ec].
  - rename H3 into IH.
    apply IHh in IH; clear IHh.
    destruct t1.
    + epose proof (IH _ _ is_h0') as [l' [t' [I1 [I2 I3]]]].
      introv X; inverts X.
      all: eexists (b01*>_); eex; [ec; apply I1 | ssc I2; esc | lia | ec].
    + epose proof (IH _ (is_h0 _)) as [l' [t' [t0' [I1 [I2 [I3 I4]]]]]].
      inverts I4.
      introv X; inverts X.
      all: eexists (a4*>_); eex; [ec; apply I1 | ssc I2; esc | lia |ec].
  - rename H3 into IH.
    apply IHh in IH; clear IHh.
    destruct t1.
    + epose proof (IH _ _ is_h2') as [l' [t' [I1 [I2 I3]]]].
      introv X; inverts X.
      all: eexists (b2*>_); eex; [ec; apply I1 | ssc I2; esc | lia | ec].
    + epose proof (IH _ (is_h0 _)) as [l' [t' [t0' [I1 [I2 [I3 I4]]]]]].
      introv X; inverts X.
      all: eexists (b01*>_); eex; [ec; apply I1 | ssc I2; esc | lia |ec].
  - rename H3 into IH.
    apply IHh in IH; clear IHh.
    destruct t1.
    + epose proof (IH _ _ is_h3') as [l' [t' [I1 [I2 I3]]]].
      introv X; inverts X.
      all: eexists (b3*>_); eex; [ec; apply I1 | ssc I2; esc | lia | ec].
    + epose proof (IH _ (is_h2)) as [l' [t' [t0' [I1 [I2 [I3 I4]]]]]].
      inverts I4.
      introv X; inverts X.
      all: eexists (b2*>_); eex; [ec; apply I1 | ssc I2; esc | lia |ec].
  - rename H3 into IH.
    apply IHh in IH; clear IHh.
    destruct t1.
    + epose proof (IH _ _ is_h1') as [l' [t' [I1 [I2 I3]]]].
      introv X; inverts X.
      all: eexists (b4*>_); eex; [ec; apply I1 | ssc I2; esc | lia | ec].
    + epose proof (IH _ (is_h3)) as [l' [t' [t0' [I1 [I2 [I3 I4]]]]]].
      inverts I4.
      introv X; inverts X.
      all: eexists (b3*>_); eex; [ec; apply I1 | ssc I2; esc | lia |ec].
  - rename H3 into IH.
    apply IHh in IH; clear IHh.
    destruct t.
    + epose proof (IH _ _ is_h0') as [l' [t' [I1 [I2 I3]]]].
      introv X; inverts X.
      1: eexists (a01*>_); eex; [ec; apply I1 | ssc I2; esc | lia ].
      all: eexists (b01*>_); eex; [ec; apply I1 | ssc I2; esc | lia ].
    + epose proof (IH _ (is_h0 _)) as [l' [t' [t0' [I1 [I2 [I3 I4]]]]]].
      inverts I4.
      introv X; inverts X.
      all: eexists (b4*>_); eex; [ec; apply I1 | ssc I2; esc | lia |ec].
Qed.

Definition S' (r:side) := 0inf <* [1] <* <[1] {{C}}> r.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (a23*>0inf)).
  1: unfold S'; esx.
  eapply progress_nonhalt_cond with (P:=fun l => exists t h t0, LC l (S t) h t0).
  2: eex; ec.
  intros l [t [h [t0 I0]]].
  apply LC_spec in I0.
  epose proof (I0 _ (is_h0 _)) as [l' [t' [t0' [I1 [I2 [I3 I4]]]]]].
  eapply sideRLs_1 in I2.
  unfold S'.
  eexists (a01*>l'); split.
  - follow10 I2; er.
  - eex; ec; eauto 1.
Qed.

End TM14.


