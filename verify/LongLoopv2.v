From BusyCoq Require Import LongLoop.
From BusyCoq Require Import Individual62.
From BusyCoq Require LongAcc.

Module LongLoop62 := LongLoop BB62.
Import LongLoop62.

Require Import ZArith.
Require Import String.

Close Scope N.

Import Eqb.

Ltac esx :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.segRLs_c_spec with (T:=10^6); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]) ||
  (eapply evstep_c_spec;
   eapply Individual62.Enumerate.Permute.Flip.Compute.TM.evstep_c_spec;
   change c0 with (Individual62.Enumerate.Permute.Flip.Compute.TM.c0);
   cbn; solve_init).

Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; repeat rewrite <-const_unfold; reflexivity.


Module LongAcc62 := LongAcc.LongAcc BB62.

Lemma find_spec {X Y} {E:Eqb X} (x0:X) ls (y0:Y):
  List.find (fun '(x,y) => eqb x x0) ls &&& (fun '(x,y) => Some y) = Some y0 ->
  List.In (x0,y0) ls.
Proof.
  intros.
  unfold if_Some in H.
  destruct (List.find (fun '(x,_) => eqb x x0)) eqn:E0.
  2: inverts H.
  eapply List.find_some in E0.
  destruct E0 as [I1 I2].
  destruct p as [x y].
  destruct (eqb_spec x x0); [|inverts I2].
  subst.
  inverts H; trivial.
Qed.

Lemma f2_spec' tm ls T:
  List.forallb (fun '(h,w,(a0,a1,h')) =>
  BoundedConfig.segRLs_c tm ([h] ^^ N.to_nat (2 ^ a0)) ([h'] ^^ N.to_nat (2 ^ a1)) w w T) ls = true ->
  forall w h a0 a1 h',
  List.In (h, w, (a0, a1, h')) ls ->
  segRLs tm ([h] ^^ N.to_nat (2 ^ a0)) ([h'] ^^ N.to_nat (2 ^ a1)) w w.
Proof.
  intros.
  rewrite List.forallb_forall in H.
  apply H in H0.
  apply BoundedConfig.segRLs_c_spec in H0.
  apply H0.
Qed.

Lemma f1_spec' tm ls T:
  List.forallb (fun '(h,w,(ws,hs)) => BoundedConfig.segRLs_c tm [h] hs w (List.concat ws) T) ls = true ->
  forall w h ws hs,
  List.In (h, w, (ws, hs)) ls ->
  segRLs tm [h] hs w (List.concat ws).
Proof.
  intros.
  rewrite List.forallb_forall in H.
  apply H in H0.
  apply BoundedConfig.segRLs_c_spec in H0.
  apply H0.
Qed.

Lemma f0_spec' tm ls T:
  List.forallb (fun '(h,w,(ws',w')) => BoundedConfig.sideRLs_c tm [h] w ((List.concat ws')++w') T) ls = true ->
  forall w h w',
  List.In (h, w, w') ls ->
  sideRLs tm [h] (w *> 0inf) (to_side w').
Proof.
  intros.
  rewrite List.forallb_forall in H.
  apply H in H0.
  destruct w' as [ws' w'].
  apply BoundedConfig.sideRLs_c_spec in H0.
  rewrite Str_app_assoc in H0.
  apply H0.
Qed.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1RD_0LC---_1LD0LB_1LE0RF_1RF1RD_0RD0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((F,<[1;0]),(D,[1;0])).
Notation h1 := ((A,<[]),(B,[])).
Notation h2 := ((D,<[1]),(B,[])).
Notation h3 := ((D,<[1;0;0;1]),(D,[1;0])).
Notation h4 := ((F,<[1;0;0;1;0]),(D,[1;0])).
Notation h5 := ((D,<[1;1;0;1;0;0;1;0;0]),(D,[1;0])).
Notation h6 := ((D,<[1;1;0;1;0;0;1;0;1;0;1;0;0]),(D,[1;0])).
Notation h7 := ((D,<[1;1;0;1;1;0;1;0;0;1;0;0;1;0;1;0;1]),(D,[1;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1;1]),([[1;1;1]],[h0;h0]))::
((h0,[1]),([[1]],[h1]))::
((h1,[0;0;0;0]),([[1;0;0;0]],[]))::
((h1,[1;0;0;0]),([[0;0;0;0]],[h1]))::
((h3,[1;1;1]),([[1;1;1]],[h3;h0]))::
((h3,[1]),([],[h4]))::
((h4,[1;0;0;0]),([],[h5]))::
((h5,[0;0;0;0]),([[1;1;1;1;0;0;0;0;1;0;0]],[]))::
((h0,[1;1;1;1;0;0;0;0;1;0;0]),([],[h6]))::
((h6,[1;0;0;0]),([],[h7]))::
((h7,[0;0;0;0]),([[1;1;1];[1;1;1];[1;1;1];[1];[1;0;0;0];[0;0;0;0];[1]],[]))::
((h1,[1]),([],[h2]))::
((h2,[1;0;0;0]),([[0;0;0;0];[1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h2,[]),([[0;0;0;0];[1;0;0;0]],[]))::
((h1,[]),([[1;0;0;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1;1]),(0%N,1%N,h0))::
((h0,[1]),(0%N,0%N,h1))::
((h1,[0;0;0;0]),(1%N,0%N,h1))::
((h1,[1;0;0;0]),(1%N,0%N,h1))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;1;1]]^^21++[[1];[1;0;0;0];[0;0;0;0];[1;0;0;0];[0;0;0;0]]++[[1;0;0;0]]^^17,[]).

Definition hs_step:(list head) := [h3].

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=0%nat) (T:=N.to_nat (10^5)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=32) (T:=23%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 9%N.
  - time vm_compute; reflexivity.
Time Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1RD_0RC1RA_0LD1RF_1LE0RB_1RB0LE_0RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((B,<[]),(E,[])).
Notation h1 := ((C,<[0;0]),(E,[0;0])).
Notation h2 := ((C,<[0]),(E,[])).
Notation h3 := ((D,<[0;0;1;0]),(E,[0;0])).
Notation h4 := ((D,<[0;1;0]),(E,[])).
Notation h5 := ((C,<[0;1;0;0;0]),(E,[])).
Notation h6 := ((D,<[0;1;0;0;0;1;0]),(E,[])).
Notation h7 := ((C,<[0;0;1;0;1;1;1;0]),(E,[0;0])).
Notation h8 := ((D,<[0;0;1;0;1;1;1;0;1;0]),(E,[0;0])).
Notation h9 := ((C,<[0;0;1;0;1;1;1;0;1;0;0;0]),(E,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h1,[1;0;1;0]),([[1;0;1;0]],[h1;h1]))::
((h0,[0;0]),([[1;0]],[]))::
((h0,[1;0]),([[0;0]],[h0]))::
((h1,[0;0;1;0;1;0;0]),([[0;0;1;0;1;0;0]],[h0]))::
((h0,[0;1;0;1;0;1;0;0;0]),([[0;1;0;1;0;1;0;0;0]],[h0;h0]))::
((h0,[0;1;0;0;0]),([[0;1;0;0;0]],[h0]))::
((h1,[1;0;0;0]),([[1;0;0;0]],[h0;h0]))::
((h3,[1;0;1;0]),([[1;0;1;0]],[h3;h1]))::
((h3,[0;0;1;0;1;0;0]),([[1;0;0;0];[1;0];[0;0]],[h2]))::
((h2,[0;0]),([[1;0];[0]],[]))::
((h0,[0]),([],[h2]))::
((h2,[0;1;0;1;0;1;0;0;0]),([[1;0];[1;0];[1;0];[1;0];[0;0]],[]))::
((h3,[1;0;0;0]),([],[h7]))::
((h7,[1;0]),([],[h8]))::
((h8,[1;0]),([],[h9]))::
((h9,[0;0]),([[1;0;1;0];[0;0;1;0;1;0;0]],[h2;h0]))::
((h2,[1;0]),([],[h4]))::
((h4,[1;0]),([],[h5]))::
((h5,[1;0]),([],[h6]))::
((h6,[0;0]),([[0;1;0;1;0;1;0;0;0]],[h0;h0]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[1;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h1,[1;0;1;0]),(0%N,1%N,h1))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[1;0]),(1%N,0%N,h0))::
((h1,[0;0;1;0;1;0;0]),(0%N,0%N,h0))::
((h0,[0;1;0;1;0;1;0;0;0]),(0%N,1%N,h0))::
((h0,[0;1;0;0;0]),(0%N,0%N,h0))::
((h1,[1;0;0;0]),(0%N,1%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0]]^^27++[[1;0;0;0];[1;0];[1;0];[0;0];[0;0];[0;0];[0;0];[1;0];[1;0];[1;0];[0;0];[0;0];[1;0];[0;0];[0;0];[0;0];[0;0];[0;0];[0;1;0;0;0];[1;0];[1;0]]++[[0;0]]^^10++[[1;0];[0;0];[0;0];[0;0];[0;0];[0;0];[0;0];[1;0]],[]).

Definition hs_step:(list head) := [h3]^^2.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0;1;0]) (pp:=0%nat) (T:=N.to_nat (10^5)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=14) (T:=114%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 13%N.
  - time vm_compute; reflexivity.
Time Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA1LD_1RA0RA_0RF0LE_0LD1LB_---1LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((C,<[]),(D,[])).
Notation h1 := ((C,<[]),(B,[])).
Notation h2 := ((A,<[0]),(D,[])).
Notation h3 := ((A,<[0]),(B,[])).
Notation h4 := ((A,<[0;1;1]),(D,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1;0;1;1;0]),([[1;1;0;1;1;0]],[h0;h0]))::
((h0,[0;0]),([[1;1]],[]))::
((h0,[1;1]),([[0;0]],[h0]))::
((h1,[1;1]),([[1;1]],[h1]))::
((h0,[1;1;0;1]),([[1;1;0;1]],[h1;h1]))::
((h1,[1;0]),([[1;0]],[h0]))::
((h1,[1;1;1;0]),([[1;1;1;0]],[h0]))::
((h4,[1;1;0;1;1;0]),([[1;1;0;1;1;0]],[h4;h0]))::
((h4,[1;1;0;1]),([[1;1;0;1;1;0]],[h2;h0]))::
((h2,[1;1;1;0]),([[0;0]],[h4]))::
((h4,[1;1]),([[1;1;0;1]],[h3;h1]))::
((h3,[1;1;0;1;1;0]),([[1;1;1;0]],[h4]))::
((h3,[1;1;0;1]),([[1;1;1;0]],[h2]))::
((h3,[1;1]),([[1;1]],[h3]))::
((h2,[1;1]),([[0;0]],[h2]))::
((h4,[0;0]),([[0;0];[1;1;0]],[]))::
((h0,[1;1;0]),([],[h4]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1]),([[0;0]],[1;1]))::
((h3,[1;1]),([[1;1;1;0]],[1;1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1;0;1;1;0]),(0%N,1%N,h0))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[1;1]),(1%N,0%N,h0))::
((h1,[1;1]),(0%N,0%N,h1))::
((h0,[1;1;0;1]),(0%N,1%N,h1))::
((h1,[1;0]),(0%N,0%N,h0))::
((h1,[1;1;1;0]),(0%N,0%N,h0))::
((h3,[1;1]),(0%N,0%N,h3))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;1;0;1;1;0];[1;1;0;1;1;0];[1;1;0;1;1;0];[1;1;0;1;1;0];[1;1;0;1;1;0];[1;1;0;1;1;0];[1;1;0;1;1;0];[1;1;0;1;1;0];[1;1;0;1;1;0];[1;1;0;1;1;0];[1;1;0;1];[1;1;1;0];[1;1];[1;1;0;1;1;0];[1;1];[1;1;0;1];[1;1;1;0];[1;1];[1;1;0;1;1;0];[1;1;0;1];[1;1;1;0];[1;1];[1;1;0;1];[1;1;1;0];[1;1;0;1];[1;1;1;0];[1;1;0;1;1;0];[1;1];[1;1];[1;1;0;1];[1;1];[1;1;1;0];[1;1];[1;1;0;1;1;0];[1;1;0;1];[1;1;1;0];[1;1;0;1];[1;1];[1;1];[1;1];[1;1];[1;1];[1;1;1;0];[1;1;0;1];[1;1];[1;1];[1;1];[1;1];[1;1;1;0];[1;1];[1;1];[1;1];[1;1];[1;1];[1;1];[1;1];[1;1];[1;1];[1;1];[1;1;0;1;1;0];[1;1];[1;1;0;1];[1;1];[1;1;1;0];[1;1];[1;1];[1;1];[1;1];[1;1;0;1];[1;1];[1;1;1;0];[1;1];[1;1];[1;1;0;1];[1;1;1;0];[0;0];[1;1]],[1;1]).

Definition hs_step:(list head) := [h4]^^2.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;1;1;1;1;1;1;1;0;1]) (pp:=0%nat) (T:=N.to_nat (10^5)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=8) (T:=83%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 55%N.
  - time vm_compute; reflexivity.
Time Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE0RF_0LE1LA_0LA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((B,<[]),(A,[])).
Notation h1 := ((D,<[1;1;1;0]),(A,[])).
Notation h2 := ((B,<[0;0;0;1]),(A,[])).
Notation h3 := ((C,<[1;0;1]),(A,[])).
Notation h4 := ((A,<[1;1;1]),(A,[])).
Notation h5 := ((B,<[1;0;1;0;1;0]),(A,[])).
Notation h6 := ((A,<[1;0;1;0;1;0;1]),(A,[])).
Notation h7 := ((D,<[1;0;1;0;1;0;1;1;1;0]),(A,[])).
Notation h8 := ((A,<[1;0;1;0;1;1;1;0;1;1;1;1;1;1]),(A,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;0;1;0;1]),([[0;0;1;0;1]],[h0;h0]))::
((h0,[0;0;0;0]),([[1;0;1;0]],[]))::
((h0,[1;0;1;0]),([[0;0;0;0]],[h0]))::
((h2,[0;0;0;0;0;1;0;1;0;0;0;0]),([[0;0;0;0;0;1;0;1;0;0;0;0]],[h0;h0;h0;h0;h1]))::
((h0,[0;1;0;1]),([],[h0;h0;h1]))::
((h1,[0;0;1;0;1]),([[0;0;1;0;1];[0;1;0;1]],[]))::
((h1,[0;0;0;0]),([[0;0;1;0;1];[0;0;0]],[]))::
((h0,[0;0;0]),([[1;0;1]],[]))::
((h0,[1;0;1]),([],[h4]))::
((h4,[0;0;0;0]),([[0;0;0;0];[1;0;1]],[]))::
((h4,[0;0;1;0;1]),([[0;0;0;0]],[h0;h0;h1]))::
((h4,[1;0;1;0]),([[0;0;0;0];[0;1;0]],[]))::
((h0,[0;1;0]),([],[h3]))::
((h3,[0;0;1;0;1]),([[0;0;0;0];[0;0;0];[1]],[]))::
((h4,[1]),([[0;0;0;0]],[]))::
((h3,[1;0;1]),([],[h5]))::
((h5,[1]),([],[h6]))::
((h6,[0;0;0]),([],[h7]))::
((h7,[0;0;0;0]),([],[h8]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h4,[1;0;1]),([[0;0;0;0]],[0;1]))::
((h8,[0;1]),([[0;0;0;0];[1;0;1;0];[0;1;0;1];[0;0;0;0];[0;0;1;0;1];[0;0;0;0];[0;0;0]],[1;0;1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;0;1;0;1]),(0%N,1%N,h0))::
((h0,[0;0;0;0]),(1%N,0%N,h0))::
((h0,[1;0;1;0]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;0;0;0;0;1;0;1;0;0;0;0];[0;0;1;0;1];[0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;0;0];[0;0;0;0];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;1;0;1];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[1;0;1;0];[0;0;0;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[1;0;1;0];[0;0;0;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;0;0];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;1;0;1];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;0;0];[1;0;1;0];[0;0;0;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;0;0];[0;0;0];[1];[0;0;0];[0;0;0;0]],[0;1]).

Definition hs_step:(list head) := [h2]^^3.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf) (pp:=1%nat) (T:=N.to_nat (10^5)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - change 0inf with ([]*>0inf).
    esx.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=60) (T:=136%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 1%N.
  - time vm_compute; reflexivity.
Time Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE0RF_0LE1LA_1RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((B,<[]),(A,[])).
Notation h1 := ((D,<[1;1;1;0]),(A,[])).
Notation h2 := ((B,<[0;0;0;1]),(A,[])).
Notation h3 := ((C,<[1;0;1]),(A,[])).
Notation h4 := ((A,<[1;1;1]),(A,[])).
Notation h5 := ((B,<[1;0;1;0;1;0]),(A,[])).
Notation h6 := ((A,<[1;0;1;0;1;0;1]),(A,[])).
Notation h7 := ((D,<[1;0;1;0;1;0;1;1;1;0]),(A,[])).
Notation h8 := ((A,<[1;0;1;0;1;1;1;0;1;1;1;1;1;1]),(A,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;0;1;0;1]),([[0;0;1;0;1]],[h0;h0]))::
((h0,[0;0;0;0]),([[1;0;1;0]],[]))::
((h0,[1;0;1;0]),([[0;0;0;0]],[h0]))::
((h2,[0;0;0;0;0;1;0;1;0;0;0;0]),([[0;0;0;0;0;1;0;1;0;0;0;0]],[h0;h0;h0;h0;h1]))::
((h0,[0;1;0;1]),([],[h0;h0;h1]))::
((h1,[0;0;1;0;1]),([[0;0;1;0;1];[0;1;0;1]],[]))::
((h1,[0;0;0;0]),([[0;0;1;0;1];[0;0;0]],[]))::
((h0,[0;0;0]),([[1;0;1]],[]))::
((h0,[1;0;1]),([],[h4]))::
((h4,[0;0;0;0]),([[0;0;0;0];[1;0;1]],[]))::
((h4,[0;0;1;0;1]),([[0;0;0;0]],[h0;h0;h1]))::
((h4,[1;0;1;0]),([[0;0;0;0];[0;1;0]],[]))::
((h0,[0;1;0]),([],[h3]))::
((h3,[0;0;1;0;1]),([[0;0;0;0];[0;0;0];[1]],[]))::
((h4,[1]),([[0;0;0;0]],[]))::
((h3,[1;0;1]),([],[h5]))::
((h5,[1]),([],[h6]))::
((h6,[0;0;0]),([],[h7]))::
((h7,[0;0;0;0]),([],[h8]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h4,[1;0;1]),([[0;0;0;0]],[0;1]))::
((h8,[0;1]),([[0;0;0;0];[1;0;1;0];[0;1;0;1];[0;0;0;0];[0;0;1;0;1];[0;0;0;0];[0;0;0]],[1;0;1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;0;1;0;1]),(0%N,1%N,h0))::
((h0,[0;0;0;0]),(1%N,0%N,h0))::
((h0,[1;0;1;0]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;0;0;0;0;1;0;1;0;0;0;0];[0;0;1;0;1];[0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;0;0];[0;0;0;0];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;1;0;1];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[1;0;1;0];[0;0;0;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[1;0;1;0];[0;0;0;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;0;0];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;1;0;1];[0;0;1;0;1];[0;0;0;0];[1;0;1;0];[0;0;0;0];[1;0;1;0];[0;0;0;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;0;0];[0;0;0];[1];[0;0;0];[0;0;0;0]],[0;1]).

Definition hs_step:(list head) := [h2]^^3.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf) (pp:=1%nat) (T:=N.to_nat (10^5)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - change 0inf with ([]*>0inf).
    esx.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=60) (T:=136%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 1%N.
  - time vm_compute; reflexivity.
Time Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA0RF_0RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[]),(C,[])).
Notation h1 := ((E,<[]),(C,[0])).
Notation h2 := ((B,<[1]),(C,[])).
Notation h3 := ((B,<[1;1]),(C,[0])).
Notation h4 := ((E,<[1;1;0]),(C,[])).
Notation h5 := ((A,<[1;0;0;0]),(C,[0])).
Notation h6 := ((E,<[1;1;0;1;0]),(C,[])).
Notation h7 := ((E,<[1;1;0;1;0;1;0]),(C,[])).
Notation h8 := ((E,<[1;1;0;1;0;1;0;1;0]),(C,[])).
Notation h9 := ((E,<[1;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h10 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h11 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h12 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0]),([[0;1;1;0]],[h0;h0]))::
((h0,[0;0]),([[0;1]],[]))::
((h0,[0;1]),([[0;0]],[h0]))::
((h5,[0;1;1;0]),([[0;1;1;0];[0;1;1;0]],[h0;h0;h0;h1]))::
((h1,[0;1;1;0]),([[0;1;1;0]],[h0;h1]))::
((h0,[0;1;1;1;0]),([[0;0];[0;1;1;0]],[h0;h1]))::
((h1,[0;0]),([],[h3]))::
((h3,[0;1;1;0]),([[0;1;1;1;0]],[]))::
((h3,[0;0]),([[0;1];[0]],[]))::
((h0,[0]),([],[h2]))::
((h2,[0;1;1;0]),([[0;1;1;1;0]],[]))::
((h2,[0;0]),([[0;1];[0]],[]))::
((h2,[0;1]),([[0;1;1]],[]))::
((h0,[0;1;1]),([],[h4]))::
((h4,[0;1]),([],[h6]))::
((h6,[0;1]),([],[h7]))::
((h7,[0;1]),([],[h8]))::
((h8,[0;1]),([],[h9]))::
((h9,[0;1]),([],[h10]))::
((h10,[0;1]),([],[h11]))::
((h11,[0;1]),([],[h12]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[0;1]],[]))::
((h12,[]),([[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1]],[]))::
((h4,[]),([],[0;1;1;0;0;0;0;1]))::
((h0,[0;1;1;0;0;0;0;1]),([],[0;1;1;0;0;0;0;0;0;1]))::
((h0,[0;1;1;0;0;0;0;0;0;1]),([],[0;1;1;0;0;0;0;1;0;1]))::
((h2,[0;1;1;0;0;0;0;1;0;1]),([],[0;1;1;1;0;0;0;0;1;0;1]))::
((h0,[0;1;1;1;0;0;0;0;1;0;1]),([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1]],[]))::
((h9,[]),([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0]),(0%N,1%N,h0))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[0;1]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1]],[]).

Definition hs_step:(list head) := [h5]^^4.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=0%nat) (T:=N.to_nat (10^5)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=10) (T:=44%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 10%N.
  - time vm_compute; reflexivity.
Time Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation A := BB62.B.
Notation B := BB62.C.
Notation C := BB62.D.

Notation h0 := ((A,<[]),(C,[])).
Notation h1 := ((E,<[]),(C,[0])).
Notation h2 := ((B,<[1]),(C,[])).
Notation h3 := ((B,<[1;1]),(C,[0])).
Notation h4 := ((E,<[1;1;0]),(C,[])).
Notation h5 := ((A,<[1;0;0;0]),(C,[0])).
Notation h6 := ((E,<[1;1;0;1;0]),(C,[])).
Notation h7 := ((E,<[1;1;0;1;0;1;0]),(C,[])).
Notation h8 := ((E,<[1;1;0;1;0;1;0;1;0]),(C,[])).
Notation h9 := ((E,<[1;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h10 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h11 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h12 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0]),([[0;1;1;0]],[h0;h0]))::
((h0,[0;0]),([[0;1]],[]))::
((h0,[0;1]),([[0;0]],[h0]))::
((h5,[0;1;1;0]),([[0;1;1;0];[0;1;1;0]],[h0;h0;h0;h1]))::
((h1,[0;1;1;0]),([[0;1;1;0]],[h0;h1]))::
((h0,[0;1;1;1;0]),([[0;0];[0;1;1;0]],[h0;h1]))::
((h1,[0;0]),([],[h3]))::
((h3,[0;1;1;0]),([[0;1;1;1;0]],[]))::
((h3,[0;0]),([[0;1];[0]],[]))::
((h0,[0]),([],[h2]))::
((h2,[0;1;1;0]),([[0;1;1;1;0]],[]))::
((h2,[0;0]),([[0;1];[0]],[]))::
((h2,[0;1]),([[0;1;1]],[]))::
((h0,[0;1;1]),([],[h4]))::
((h4,[0;1]),([],[h6]))::
((h6,[0;1]),([],[h7]))::
((h7,[0;1]),([],[h8]))::
((h8,[0;1]),([],[h9]))::
((h9,[0;1]),([],[h10]))::
((h10,[0;1]),([],[h11]))::
((h11,[0;1]),([],[h12]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[0;1]],[]))::
((h12,[]),([[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1]],[]))::
((h4,[]),([],[0;1;1;0;0;0;0;1]))::
((h0,[0;1;1;0;0;0;0;1]),([],[0;1;1;0;0;0;0;0;0;1]))::
((h0,[0;1;1;0;0;0;0;0;0;1]),([],[0;1;1;0;0;0;0;1;0;1]))::
((h2,[0;1;1;0;0;0;0;1;0;1]),([],[0;1;1;1;0;0;0;0;1;0;1]))::
((h0,[0;1;1;1;0;0;0;0;1;0;1]),([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1]],[]))::
((h9,[]),([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0]),(0%N,1%N,h0))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[0;1]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;0];[0;1];[0;1];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1]],[]).

Definition hs_step:(list head) := [h5]^^4.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=0%nat) (T:=N.to_nat (10^5)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=10) (T:=54%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 10%N.
  - time vm_compute; reflexivity.
Time Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RD0LD_1RA0RE_1RD0RF_0RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation A := BB62.D.
Notation B := BB62.A.
Notation C := BB62.B.

Notation h0 := ((A,<[]),(C,[])).
Notation h1 := ((E,<[]),(C,[0])).
Notation h2 := ((B,<[1]),(C,[])).
Notation h3 := ((B,<[1;1]),(C,[0])).
Notation h4 := ((E,<[1;1;0]),(C,[])).
Notation h5 := ((A,<[1;0;0;0]),(C,[0])).
Notation h6 := ((E,<[1;1;0;1;0]),(C,[])).
Notation h7 := ((E,<[1;1;0;1;0;1;0]),(C,[])).
Notation h8 := ((E,<[1;1;0;1;0;1;0;1;0]),(C,[])).
Notation h9 := ((E,<[1;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h10 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h11 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h12 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0]),([[0;1;1;0]],[h0;h0]))::
((h0,[0;0]),([[0;1]],[]))::
((h0,[0;1]),([[0;0]],[h0]))::
((h5,[0;1;1;0]),([[0;1;1;0];[0;1;1;0]],[h0;h0;h0;h1]))::
((h1,[0;1;1;0]),([[0;1;1;0]],[h0;h1]))::
((h0,[0;1;1;1;0]),([[0;0];[0;1;1;0]],[h0;h1]))::
((h1,[0;0]),([],[h3]))::
((h3,[0;1;1;0]),([[0;1;1;1;0]],[]))::
((h3,[0;0]),([[0;1];[0]],[]))::
((h0,[0]),([],[h2]))::
((h2,[0;1;1;0]),([[0;1;1;1;0]],[]))::
((h2,[0;0]),([[0;1];[0]],[]))::
((h2,[0;1]),([[0;1;1]],[]))::
((h0,[0;1;1]),([],[h4]))::
((h4,[0;1]),([],[h6]))::
((h6,[0;1]),([],[h7]))::
((h7,[0;1]),([],[h8]))::
((h8,[0;1]),([],[h9]))::
((h9,[0;1]),([],[h10]))::
((h10,[0;1]),([],[h11]))::
((h11,[0;1]),([],[h12]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[0;1]],[]))::
((h12,[]),([[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1]],[]))::
((h4,[]),([],[0;1;1;0;0;0;0;1]))::
((h0,[0;1;1;0;0;0;0;1]),([],[0;1;1;0;0;0;0;0;0;1]))::
((h0,[0;1;1;0;0;0;0;0;0;1]),([],[0;1;1;0;0;0;0;1;0;1]))::
((h2,[0;1;1;0;0;0;0;1;0;1]),([],[0;1;1;1;0;0;0;0;1;0;1]))::
((h0,[0;1;1;1;0;0;0;0;1;0;1]),([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1]],[]))::
((h9,[]),([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0]),(0%N,1%N,h0))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[0;1]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1];[0;1];[0;1];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1]],[]).

Definition hs_step:(list head) := [h5]^^4.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=0%nat) (T:=N.to_nat (10^5)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=10) (T:=51%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 10%N.
  - time vm_compute; reflexivity.
Time Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0LC_1RE0RD_1RC0RF_1LA1RC_0RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation A := BB62.C.
Notation B := BB62.E.
Notation C := BB62.A.
Notation E := BB62.D.

Notation h0 := ((A,<[]),(C,[])).
Notation h1 := ((E,<[]),(C,[0])).
Notation h2 := ((B,<[1]),(C,[])).
Notation h3 := ((B,<[1;1]),(C,[0])).
Notation h4 := ((E,<[1;1;0]),(C,[])).
Notation h5 := ((A,<[1;0;0;0]),(C,[0])).
Notation h6 := ((E,<[1;1;0;1;0]),(C,[])).
Notation h7 := ((E,<[1;1;0;1;0;1;0]),(C,[])).
Notation h8 := ((E,<[1;1;0;1;0;1;0;1;0]),(C,[])).
Notation h9 := ((E,<[1;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h10 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h11 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).
Notation h12 := ((E,<[1;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0]),(C,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0]),([[0;1;1;0]],[h0;h0]))::
((h0,[0;0]),([[0;1]],[]))::
((h0,[0;1]),([[0;0]],[h0]))::
((h5,[0;1;1;0]),([[0;1;1;0];[0;1;1;0]],[h0;h0;h0;h1]))::
((h1,[0;1;1;0]),([[0;1;1;0]],[h0;h1]))::
((h0,[0;1;1;1;0]),([[0;0];[0;1;1;0]],[h0;h1]))::
((h1,[0;0]),([],[h3]))::
((h3,[0;1;1;0]),([[0;1;1;1;0]],[]))::
((h3,[0;0]),([[0;1];[0]],[]))::
((h0,[0]),([],[h2]))::
((h2,[0;1;1;0]),([[0;1;1;1;0]],[]))::
((h2,[0;0]),([[0;1];[0]],[]))::
((h2,[0;1]),([[0;1;1]],[]))::
((h0,[0;1;1]),([],[h4]))::
((h4,[0;1]),([],[h6]))::
((h6,[0;1]),([],[h7]))::
((h7,[0;1]),([],[h8]))::
((h8,[0;1]),([],[h9]))::
((h9,[0;1]),([],[h10]))::
((h10,[0;1]),([],[h11]))::
((h11,[0;1]),([],[h12]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[0;1]],[]))::
((h12,[]),([[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1]],[]))::
((h4,[]),([],[0;1;1;0;0;0;0;1]))::
((h0,[0;1;1;0;0;0;0;1]),([],[0;1;1;0;0;0;0;0;0;1]))::
((h0,[0;1;1;0;0;0;0;0;0;1]),([],[0;1;1;0;0;0;0;1;0;1]))::
((h2,[0;1;1;0;0;0;0;1;0;1]),([],[0;1;1;1;0;0;0;0;1;0;1]))::
((h0,[0;1;1;1;0;0;0;0;1;0;1]),([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1]],[]))::
((h9,[]),([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0]),(0%N,1%N,h0))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[0;1]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;1;1;0];[0;1;1;0];[0;1;1;0];[0;1];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1]],[]).

Definition hs_step:(list head) := [h5]^^4.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=1%nat) (T:=N.to_nat (10^5)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=10) (T:=49%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 10%N.
  - time vm_compute; reflexivity.
Time Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_1RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((C,<[0]),(A,[0])).
Notation h1 := ((E,<[0;1]),(A,[0])).
Notation h2 := ((D,<[0;1;0]),(A,[0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;0;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[0;0;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[0;0;0]),([[0;0;0];[1;0]],[]))::
((h0,[1;0]),([],[h2]))::
((h2,[1;0;0]),([[1;0;1;0]],[h1]))::
((h1,[0;0;0]),([[0;0;0];[1]],[]))::
((h0,[1]),([],[h1]))::
((h1,[1;0;0]),([[1;0;1;0]],[h0]))::
((h1,[1;0;1;0]),([[1;0;1;0]],[h1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[1;0;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[0;0;0]),(1%N,0%N,h0))::
((h0,[1;0;0]),(1%N,0%N,h0))::
((h1,[1;0;1;0]),(0%N,0%N,h1))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;0];[0;0;0];[1;0;1;0];[1;0;1;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[1;0;0];[1;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0]],[]).

Definition hs_step:(list head) := [h2]^^74.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=2%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=10) (T:=49%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 7%N.
  - native_check_eq.
Time Qed.
End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0RA_0RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((C,<[0]),(A,[0])).
Notation h1 := ((E,<[0;1]),(A,[0])).
Notation h2 := ((D,<[0;1;0]),(A,[0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;0;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[0;0;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[0;0;0]),([[0;0;0];[1;0]],[]))::
((h0,[1;0]),([],[h2]))::
((h2,[1;0;0]),([[1;0;1;0]],[h1]))::
((h1,[0;0;0]),([[0;0;0];[1]],[]))::
((h0,[1]),([],[h1]))::
((h1,[1;0;0]),([[1;0;1;0]],[h0]))::
((h1,[1;0;1;0]),([[1;0;1;0]],[h1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[1;0;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[0;0;0]),(1%N,0%N,h0))::
((h0,[1;0;0]),(1%N,0%N,h0))::
((h1,[1;0;1;0]),(0%N,0%N,h1))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;0];[0;0;0];[1;0;1;0];[1;0;1;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[1;0;0];[1;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0]],[]).

Definition hs_step:(list head) := [h2]^^74.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=2%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=12) (T:=49%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 7%N.
  - native_check_eq.
Time Qed.
End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0RC_1RA0LD_1LC0LE_0LC1RF_0RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((B,<[]),(C,[])).
Notation h1 := ((C,<[0]),(C,[])).
Notation h2 := ((A,<[0;1]),(C,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;0;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[0;0;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[1;0;0]),([[1;0;1;0]],[h1]))::
((h1,[1;0;1;0]),([[1;0;0];[1;0]],[]))::
((h0,[1;0]),([],[h2]))::
((h1,[1;0;0]),([[1;0;0];[0]],[]))::
((h0,[0]),([[1]],[]))::
((h0,[1]),([],[h1]))::
((h1,[0;0;0]),([[0;0;0];[1]],[]))::
((h2,[0;0;0]),([[0;0;0];[1;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1]),([[0;0;0]],[1]))::
((h1,[1]),([],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[0;0;0]),(1%N,0%N,h0))::
((h0,[1;0;0]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;0];[1;0;1;0];[1;0;0];[1;0;0];[1;0;0];[1;0;0];[1;0;1;0];[1;0;0];[0;0;0];[1;0;1;0];[1;0;0];[0;0;0];[1;0;0];[1;0;0];[1;0;0];[1;0;1;0];[0;0;0];[0;0;0];[1;0;0];[0;0;0];[0;0;0];[1;0;0]],[1]).

Definition hs_step:(list head) := [h2]^^6.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[]) (pp:=3%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=10) (T:=39%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 2%N.
  - native_check_eq.
Time Qed.
End TM12.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1LB0RB_1RC0LE_1RA0RD_0LB1RF_1LB0LD_0RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[]),(B,[])).
Notation h1 := ((B,<[0]),(B,[])).
Notation h2 := ((C,<[0;1]),(B,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;0;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[0;0;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[1;0;0]),([[1;0;1;0]],[h1]))::
((h1,[1;0;1;0]),([[1;0;0];[1;0]],[]))::
((h0,[1;0]),([],[h2]))::
((h1,[1;0;0]),([[1;0;0];[0]],[]))::
((h0,[0]),([[1]],[]))::
((h0,[1]),([],[h1]))::
((h1,[0;0;0]),([[0;0;0];[1]],[]))::
((h2,[0;0;0]),([[0;0;0];[1;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1]),([[0;0;0]],[1]))::
((h1,[1]),([],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[0;0;0]),(1%N,0%N,h0))::
((h0,[1;0;0]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;0];[1;0;1;0];[1;0;0];[1;0;0];[1;0;0];[1;0;0];[1;0;0];[1;0;1;0];[0;0;0];[1;0;0];[1;0;0];[1;0;0];[1;0;0];[1;0;0];[1;0;0];[1;0;1;0];[0;0;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0]],[1]).

Definition hs_step:(list head) := [h2]^^6.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[]) (pp:=3%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=10) (T:=40%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 2%N.
  - native_check_eq.
Time Qed.
End TM13.


Module TM14.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD0LA_0LB1RE_0LE0RF_1RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[1]),(A,[0])).
Notation h1 := ((C,<[1;0]),(A,[0])).
Notation h2 := ((D,<[1;0;0]),(A,[0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[1;1;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[1;1;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[1;0;0]),([[1;0;1;0]],[h1]))::
((h1,[1;1;0]),([[1;0;1;0]],[]))::
((h2,[1;1;0]),([[1;1;0];[1;0]],[h0]))::
((h0,[1;0]),([],[h2]))::
((h1,[1;0;1;0]),([[1;0;0];[1;0]],[]))::
((h1,[1;0;0]),([[1;0;0];[0]],[]))::
((h0,[0]),([[1]],[]))::
((h0,[1]),([],[h1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[1;0;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[1;1;0]),(1%N,0%N,h0))::
((h0,[1;0;0]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;0];[1;1;0];[1;0;0];[1;0;0];[1;0;0]],[]).

Definition hs_step:(list head) := [h2]^^12.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=17%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - esx.
  - native_check_eq.
Time Qed.
End TM14.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1LB---_1LC0RE_0RD0LA_0LB1RD_1RF0LE_1LC0RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((F,<[1]),(A,[0])).
Notation h1 := ((C,<[1;0]),(A,[0])).
Notation h2 := ((D,<[1;0;0]),(A,[0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[1;1;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[1;1;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[1;0;0]),([[1;0;1;0]],[h1]))::
((h1,[1;1;0]),([[1;0;1;0]],[]))::
((h2,[1;1;0]),([[1;1;0];[1;0]],[h0]))::
((h0,[1;0]),([],[h2]))::
((h1,[1;0;1;0]),([[1;0;0];[1;0]],[]))::
((h1,[1;0;0]),([[1;0;0];[0]],[]))::
((h0,[0]),([[1]],[]))::
((h0,[1]),([],[h1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[1;0;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[1;1;0]),(1%N,0%N,h0))::
((h0,[1;0;0]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;0];[1;1;0];[1;0;0];[1;0;0];[1;0;0]],[]).

Definition hs_step:(list head) := [h2]^^12.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=17%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - esx.
  - native_check_eq.
Time Qed.
End TM15.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0RA1RF_0RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[1;0]),(B,[0;0])).
Notation h1 := ((C,<[1;0;0]),(B,[0;0])).
Notation h2 := ((D,<[1;0;0;0]),(B,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;1;0]),([[1;1;0]],[]))::
((h0,[1;1;0]),([[0;1;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[1;1;0]),([[1;0;1;0];[1]],[h0]))::
((h0,[1]),([],[h1]))::
((h1,[0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h2,[0;1;0]),([[0;1;0]],[h2]))::
((h1,[1;0;1;0]),([[0;1;0]],[h2]))::
((h1,[1;1;0]),([[0;1;0];[0]],[h0]))::
((h0,[0]),([[1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1]),([[0;1;0]],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[0;1;0]),(1%N,0%N,h0))::
((h0,[1;1;0]),(1%N,0%N,h0))::
((h2,[0;1;0]),(0%N,0%N,h2))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[0;1;0];[0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[0;1;0];[1;1;0]],[1]).

Definition hs_step:(list head) := [h2]^^20.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=5%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - esx.
  - native_check_eq.
Time Qed.
End TM16.


Module TM17.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RD_1RD0LC_0RE1LC_0LB1RF_0RB1RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((B,<[1;0]),(C,[0;0])).
Notation h1 := ((E,<[1;0;0;0]),(C,[0;0])).
Notation h2 := ((B,<[1;1;1]),(C,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;1;0]),([[1;1;0]],[]))::
((h0,[1;1;0]),([[0;1;0]],[h0]))::
((h1,[1;0;1;0]),([[1;0;1;0]],[h1;h0]))::
((h1,[0;1;0]),([[0;1;0]],[h1]))::
((h1,[1;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[1;0;1;0]),([[0;0;0;1;0]],[h0;h0]))::
((h0,[0;0;0;1;0]),([[1;0;0;1;0]],[]))::
((h0,[1;0;0;1;0]),([[0;1;0]],[h1]))::
((h2,[0;1;0]),([[0;1;1;0]],[]))::
((h0,[0;1;1;0]),([[1;1;1;0]],[]))::
((h0,[1;1;1;0]),([[0;1;0]],[h2]))::
((h2,[1;1;0]),([[0;0;1;0]],[]))::
((h0,[0;0;1;0]),([[1;0;1;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1]),([[0;1;0]],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[0;1;0]),(1%N,0%N,h0))::
((h0,[1;1;0]),(1%N,0%N,h0))::
((h1,[0;1;0]),(0%N,0%N,h1))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;1;0];[1;1;0];[1;1;0];[1;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;1;0];[1;1;0];[1;1;0];[1;1;0];[1;1;0];[0;1;0];[1;1;0];[1;1;0];[1;1;0];[1;1;0];[1;1;0];[0;1;0];[0;1;0];[1;1;0];[1;1;0];[0;1;0];[0;1;0];[0;1;0];[0;1;0];[1;1;0];[0;1;0];[0;1;0];[0;1;0];[1;1;0];[0;1;0];[0;1;0];[0;1;0];[1;1;0];[0;1;0];[0;1;0];[0;1;0]],[1]).

Definition hs_step:(list head) := [h1]^^20.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=4%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - eapply evstep_trans.
    + eapply evstep_c_spec.
      eapply LongAcc62.TM.Compute.TM.evstep_c_spec.
      eapply LongAcc62.decide_evstep with
        (D:=16) (T:=50%N) (T0:=(10^6)%N) (T1:=10^3).
      time native_compute; reflexivity.
    + ut.
      stepn 11%N.
  - native_check_eq.
Time Qed.
End TM17.


Module TM18.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RB_1LD0RB_0LF0LE_0LD1LC_0RA1RF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((B,<[]),(E,[])).
Notation h1 := ((C,<[1]),(E,[])).
Notation h2 := ((B,<[1;0;0]),(E,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1]),([[0;1;1]],[h0;h0]))::
((h0,[0;0]),([[0;1]],[]))::
((h0,[0;1]),([[0;0]],[h0]))::
((h1,[0;1;1]),([[0;1;1;1]],[]))::
((h0,[0;1;1;1]),([[0;1;1]],[h0;h1]))::
((h1,[0;0]),([[0;1];[0]],[]))::
((h0,[0]),([],[h1]))::
((h1,[0;1]),([[0;1;1]],[]))::
((h2,[0;1;1;1]),([[0;1;1];[0;1;1]],[h0;h1;h0;h0]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[0;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1]),(0%N,1%N,h0))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[0;1]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1];[0;1;1;1];[0;1;1];[0;1;1];[0;1];[0;1;1];[0;1;1];[0;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;0];[0;0];[0;1]],[]).

Definition hs_step:(list head) := [h1;h2]^^42.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=4%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - esx.
  - native_check_eq.
Time Qed.
End TM18.


Module TM19.
Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0RA_0LE0LD_0LC1LB_0RF1RE_1RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[]),(D,[])).
Notation h1 := ((B,<[1]),(D,[])).
Notation h2 := ((A,<[1;0;0]),(D,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1]),([[0;1;1]],[h0;h0]))::
((h0,[0;0]),([[0;1]],[]))::
((h0,[0;1]),([[0;0]],[h0]))::
((h1,[0;1;1]),([[0;1;1;1]],[]))::
((h0,[0;1;1;1]),([[0;1;1]],[h0;h1]))::
((h1,[0;0]),([[0;1];[0]],[]))::
((h0,[0]),([],[h1]))::
((h1,[0;1]),([[0;1;1]],[]))::
((h2,[0;1;1;1]),([[0;1;1];[0;1;1]],[h0;h1;h0;h0]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[0;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1]),(0%N,1%N,h0))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[0;1]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1];[0;1;1;1];[0;1];[0;1;1];[0;1];[0;1;1];[0;1];[0;1;1];[0;1;1];[0;1];[0;1];[0;0];[0;0];[0;1];[0;1];[0;1];[0;0];[0;0];[0;0];[0;1]],[]).

Definition hs_step:(list head) := [h1;h2]^^42.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=4%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - esx.
  - native_check_eq.
Time Qed.
End TM19.


Module TM20.
Definition tm := Eval compute in (TM_from_str "1LB0RE_0LC0LF_0RD1RC_1RE---_1RA0RE_0LB1LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((E,<[]),(F,[])).
Notation h1 := ((A,<[1]),(F,[])).
Notation h2 := ((E,<[1;0;0]),(F,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1]),([[0;1;1]],[h0;h0]))::
((h0,[0;0]),([[0;1]],[]))::
((h0,[0;1]),([[0;0]],[h0]))::
((h1,[0;1;1]),([[0;1;1;1]],[]))::
((h0,[0;1;1;1]),([[0;1;1]],[h0;h1]))::
((h1,[0;0]),([[0;1];[0]],[]))::
((h0,[0]),([],[h1]))::
((h1,[0;1]),([[0;1;1]],[]))::
((h2,[0;1;1;1]),([[0;1;1];[0;1;1]],[h0;h1;h0;h0]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[0;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1]),(0%N,1%N,h0))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[0;1]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1];[0;1;1;1];[0;1;1];[0;1];[0;1;1];[0;1];[0;1;1];[0;1;1];[0;1];[0;1;1];[0;1;1];[0;1;1];[0;1];[0;1];[0;1];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1];[0;0];[0;0];[0;0];[0;1]],[]).

Definition hs_step:(list head) := [h1;h2]^^42.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=4%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - esx.
  - native_check_eq.
Time Qed.
End TM20.


Module TM21.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC0RA_1RD0RF_1LA0RC_1LB1LA_0LA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((D,<[0;1]),(B,[1;0])).
Notation h1 := ((D,<[]),(A,[])).
Notation h2 := ((C,<[0;1;0]),(B,[1;0])).
Notation h3 := ((B,<[]),(A,[])).
Notation h4 := ((C,<[1]),(A,[])).
Notation h5 := ((B,<[0;1;0;1]),(A,[])).
Notation h6 := ((A,<[0;1;0;1;0;1;0;1;0]),(A,[])).
Notation h7 := ((C,<[0;1;0;1;0;1;1;1;1;1;0;1;0]),(A,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;0;0;0]),([[1;0;0;0]],[]))::
((h0,[1;0;0;0]),([[0;0;0;0]],[h0]))::
((h1,[1;0;1;0]),([[1;0;1;0]],[h1;h1]))::
((h1,[1;0;1;0;1;0;0;0;1;0;0;0]),([[1;0;1;0;1;0;0;0;0;0;0;0]],[h0]))::
((h1,[1;0;1;0;1;0;0;0;0;0;0;0]),([[1;0;1;0;1;0;0;0;1;0;0;0]],[]))::
((h1,[1;0;1;0;1;0;0;0]),([[1;0;1;0;1;0;0;0]],[h1]))::
((h4,[1;0;1;0]),([[1;0;1;0]],[h4]))::
((h4,[1;0;1;0;1;0;0;0]),([[1;0;1;0;1;0;1;0;1]],[]))::
((h4,[1;0;1;0;1;0;0;0;1;0;0;0]),([[1;0;1;0;1;0;1;0;1;1;0;0;0]],[]))::
((h3,[1;0;1;0]),([[1;0;1;0]],[h3;h1]))::
((h5,[1;0;1;0]),([[1;0;1;0];[1;0;1;0]],[h3;h1;h1;h1]))::
((h3,[1;0;1;0;1;0;0;0]),([[1;0;1;0;1;0;0;0]],[h1;h1]))::
((h3,[1;0;1;0;1;0;1;0;1]),([],[h6]))::
((h6,[1;0;1;0]),([[1;0;1;0;1;0;0;0];[1;0;1;0]],[h4;h1]))::
((h1,[1;0;1;0;1;0;1;0;1;1;0;0;0]),([],[h7]))::
((h7,[1;0;0;0]),([[1;0;1;0];[1;0;1;0;1;0;0;0;1;0;0;0]],[h2]))::
((h2,[1;0;0;0]),([[0;0;0;0]],[h2]))::
((h2,[0;0;0;0]),([[0;0;0;0];[1]],[]))::
((h0,[1]),([],[h2]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h2,[1]),([[0;0;0;0];[0;0;0;0]],[1]))::
((h0,[1]),([[0;0;0;0]],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;0;0;0]),(1%N,0%N,h0))::
((h0,[1;0;0;0]),(1%N,0%N,h0))::
((h1,[1;0;1;0]),(0%N,1%N,h1))::
((h1,[1;0;1;0;1;0;0;0;1;0;0;0]),(1%N,0%N,h0))::
((h1,[1;0;1;0;1;0;0;0;0;0;0;0]),(1%N,0%N,h0))::
((h1,[1;0;1;0;1;0;0;0]),(0%N,0%N,h1))::
((h4,[1;0;1;0]),(0%N,0%N,h4))::
((h3,[1;0;1;0;1;0;0;0]),(0%N,1%N,h1))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0;1;0;0;0];[1;0;1;0];[1;0;1;0];[1;0;1;0;1;0;0;0;1;0;0;0];[1;0;0;0];[0;0;0;0];[0;0;0;0]],[1]).

Definition hs_step:(list head) := [h4;h5;h3]^^2.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;1]) (pp:=3%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - esx.
  - native_check_eq.
Time Qed.
End TM21.


Module TM22.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0LD_0RF0RD_1RE0RB_1LA1RD_0RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((D,<[]),(A,[])).
Notation h1 := ((E,<[1]),(A,[])).
Notation h2 := ((B,<[0]),(A,[])).
Notation h3 := ((B,<[1;1;0]),(A,[])).
Notation h4 := ((C,<[1;1;0;1]),(A,[])).
Notation h5 := ((F,<[1;1;0;1;0]),(A,[])).
Notation h6 := ((B,<[1;1;0;1;0;0]),(A,[])).
Notation h7 := ((E,<[1;1;0;1;0;0;1]),(A,[])).
Notation h8 := ((B,<[1;1;0;1;0;0;0]),(A,[])).
Notation h9 := ((C,<[1;1;0;1;0;0;0;1]),(A,[])).
Notation h10 := ((F,<[1;1;0;1;0;0;1;0]),(A,[])).
Notation h11 := ((F,<[1;1;0;1;0;0;0;1;0]),(A,[])).
Notation h12 := ((B,<[1;1;0;1;0;0;0;1;0;0;0]),(A,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0;0;0;1;1]),([[0;1;1;0;0;0;1;1]],[h0;h0]))::
((h0,[0;0]),([[0;1]],[]))::
((h0,[0;1]),([[0;0]],[h0]))::
((h0,[0;1;1]),([],[h3]))::
((h3,[0;1;1;0;0;0;1;1]),([[0;1;1;0;0;0;1;1]],[h0;h0;h3]))::
((h3,[0;1;1]),([],[h6]))::
((h6,[0;0]),([],[h10]))::
((h10,[0;1;1]),([[0;1;1;0;0;0;1;1]],[h0;h0;h3]))::
((h3,[0;0]),([],[h5]))::
((h5,[0;0]),([],[h7]))::
((h7,[0;0]),([[0;1;1;0;0;0;1;1]],[h1;h0]))::
((h7,[0;1;1]),([[0;1;1;0;0;0;1;1];[0;0]],[h0]))::
((h1,[0;0]),([[0;1];[0]],[]))::
((h0,[0]),([],[h1]))::
((h1,[0;1;1;0;0;0;1;1]),([[0;1];[1;1];[0;0];[0;1;1]],[]))::
((h5,[0;1;1;0;0;0;1;1]),([[0;1;1;0;0;0;1;1];[0;0]],[h3]))::
((h5,[0;1]),([],[h8]))::
((h8,[0;1;1;0;0;0;1;1]),([[0;1;1];[0;1];[1;1];[0;0];[0;1;1]],[h0;h0;h3]))::
((h7,[0;1]),([[0;1;1]],[h3;h0;h3]))::
((h3,[0;1]),([[0;0];[0;1;1]],[h0]))::
((h0,[1;1]),([[0;1]],[]))::
((h5,[0;1;1]),([[0;1;1;0;0;0;1;1]],[h0;h0]))::
((h1,[0;1]),([[0;1;1]],[]))::
((h3,[0]),([],[h4]))::
((h4,[0;0]),([[0;1;1]],[h0;h0;h0;h3]))::
((h8,[0;1]),([[0;1;1]],[h0;h3;h0;h3]))::
((h1,[0;1;1]),([[0;1];[1;1]],[]))::
((h6,[0;1;1]),([[0;0];[0;1;1];[0;1;1]],[h2]))::
((h2,[0;1;1]),([[0;1;1]],[h2]))::
((h2,[0;1]),([[0;1;1]],[h0]))::
((h10,[0;0]),([[0;1;1]],[h1;h0;h0;h3;h0;h3]))::
((h8,[0]),([],[h9]))::
((h9,[0;0]),([[0;1;1];[0;1];[1;1]],[h0;h0;h0;h3]))::
((h8,[0;0]),([],[h11]))::
((h11,[0;0]),([[0;1;1];[0;1];[1;1]],[h1;h0;h0;h3]))::
((h6,[0;1]),([[0;0];[0;1;1];[0;1;1]],[h0]))::
((h8,[0;1;1]),([[0;1;1;0;0;0;1;1]],[h2;h2;h0]))::
((h11,[0;1]),([],[h12]))::
((h12,[0;1;1;0;0;0;1;1]),([[0;1;1];[0;1];[1;1];[0;1];[1;1];[0;0];[0;1;1]],[h0;h0;h3]))::
((h11,[0;1;1]),([[0;1;1];[0;1];[1;1];[0;0];[0;1;1]],[h0;h0]))::
((h7,[0;1;1;0;0;0;1;1]),([[0;1;1;0;0;0;1;1];[0;0];[0;1];[0;1;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h5,[0;1]),([[0;1;1];[0;1];[1;1];[0;0];[0;1;1];[0;0]],[0;1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0;0;0;1;1]),(0%N,1%N,h0))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[0;1]),(1%N,0%N,h0))::
((h2,[0;1;1]),(0%N,0%N,h2))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;0];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;0];[0;1];[0;0];[0;1;1];[0;0];[0;0];[0;0];[0;0];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;0];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;0];[0;1];[0;1];[0;1];[0;0];[0;1];[0;1];[0;1];[0;1];[0;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1];[0;1;1];[0;0]],[0;1]).

Definition hs_step:(list head) := [h3]^^24.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=4%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - stepn 12920484%N.
  - native_check_eq.
Time Qed.
End TM22.


Module TM23.
Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC0RD_0RD---_1RE0RA_1LF1RD_1LA0LF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((D,<[]),(F,[])).
Notation h1 := ((E,<[1]),(F,[])).
Notation h2 := ((A,<[0]),(F,[])).
Notation h3 := ((A,<[1;1;0]),(F,[])).
Notation h4 := ((B,<[1;1;0;1]),(F,[])).
Notation h5 := ((C,<[1;1;0;1;0]),(F,[])).
Notation h6 := ((A,<[1;1;0;1;0;0]),(F,[])).
Notation h7 := ((E,<[1;1;0;1;0;0;1]),(F,[])).
Notation h8 := ((A,<[1;1;0;1;0;0;0]),(F,[])).
Notation h9 := ((B,<[1;1;0;1;0;0;0;1]),(F,[])).
Notation h10 := ((C,<[1;1;0;1;0;0;1;0]),(F,[])).
Notation h11 := ((C,<[1;1;0;1;0;0;0;1;0]),(F,[])).
Notation h12 := ((A,<[1;1;0;1;0;0;0;1;0;0;0]),(F,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0;0;0;1;1]),([[0;1;1;0;0;0;1;1]],[h0;h0]))::
((h0,[0;0]),([[0;1]],[]))::
((h0,[0;1]),([[0;0]],[h0]))::
((h0,[0;1;1]),([],[h3]))::
((h3,[0;1;1;0;0;0;1;1]),([[0;1;1;0;0;0;1;1]],[h0;h0;h3]))::
((h3,[0;1;1]),([],[h6]))::
((h6,[0;0]),([],[h10]))::
((h10,[0;1;1]),([[0;1;1;0;0;0;1;1]],[h0;h0;h3]))::
((h3,[0;0]),([],[h5]))::
((h5,[0;0]),([],[h7]))::
((h7,[0;0]),([[0;1;1;0;0;0;1;1]],[h1;h0]))::
((h7,[0;1;1]),([[0;1;1;0;0;0;1;1];[0;0]],[h0]))::
((h1,[0;0]),([[0;1];[0]],[]))::
((h0,[0]),([],[h1]))::
((h1,[0;1;1;0;0;0;1;1]),([[0;1];[1;1];[0;0];[0;1;1]],[]))::
((h5,[0;1;1;0;0;0;1;1]),([[0;1;1;0;0;0;1;1];[0;0]],[h3]))::
((h5,[0;1]),([],[h8]))::
((h8,[0;1;1;0;0;0;1;1]),([[0;1;1];[0;1];[1;1];[0;0];[0;1;1]],[h0;h0;h3]))::
((h7,[0;1]),([[0;1;1]],[h3;h0;h3]))::
((h3,[0;1]),([[0;0];[0;1;1]],[h0]))::
((h0,[1;1]),([[0;1]],[]))::
((h5,[0;1;1]),([[0;1;1;0;0;0;1;1]],[h0;h0]))::
((h1,[0;1]),([[0;1;1]],[]))::
((h3,[0]),([],[h4]))::
((h4,[0;0]),([[0;1;1]],[h0;h0;h0;h3]))::
((h8,[0;1]),([[0;1;1]],[h0;h3;h0;h3]))::
((h1,[0;1;1]),([[0;1];[1;1]],[]))::
((h6,[0;1;1]),([[0;0];[0;1;1];[0;1;1]],[h2]))::
((h2,[0;1;1]),([[0;1;1]],[h2]))::
((h2,[0;1]),([[0;1;1]],[h0]))::
((h10,[0;0]),([[0;1;1]],[h1;h0;h0;h3;h0;h3]))::
((h8,[0]),([],[h9]))::
((h9,[0;0]),([[0;1;1];[0;1];[1;1]],[h0;h0;h0;h3]))::
((h8,[0;0]),([],[h11]))::
((h11,[0;0]),([[0;1;1];[0;1];[1;1]],[h1;h0;h0;h3]))::
((h6,[0;1]),([[0;0];[0;1;1];[0;1;1]],[h0]))::
((h8,[0;1;1]),([[0;1;1;0;0;0;1;1]],[h2;h2;h0]))::
((h11,[0;1]),([],[h12]))::
((h12,[0;1;1;0;0;0;1;1]),([[0;1;1];[0;1];[1;1];[0;1];[1;1];[0;0];[0;1;1]],[h0;h0;h3]))::
((h11,[0;1;1]),([[0;1;1];[0;1];[1;1];[0;0];[0;1;1]],[h0;h0]))::
((h7,[0;1;1;0;0;0;1;1]),([[0;1;1;0;0;0;1;1];[0;0];[0;1];[0;1;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h5,[0;1]),([[0;1;1];[0;1];[1;1];[0;0];[0;1;1];[0;0]],[0;1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;1;0;0;0;1;1]),(0%N,1%N,h0))::
((h0,[0;0]),(1%N,0%N,h0))::
((h0,[0;1]),(1%N,0%N,h0))::
((h2,[0;1;1]),(0%N,0%N,h2))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;0];[0;1];[1;1];[0;0];[0;1;1];[0;1;1;0;0;0;1;1];[0;0];[0;1];[0;1];[0;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;0];[0;1;1;0;0;0;1;1];[0;0];[0;1];[0;0];[0;0];[0;0];[0;0];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;0];[0;1];[0;0];[0;1;1;0;0;0;1;1];[0;0];[0;0];[0;0];[0;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;0];[0;1];[0;0];[0;0];[0;0];[0;1];[0;0];[0;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;1;1;0;0;0;1;1];[0;0];[0;1];[0;1];[0;0];[0;0];[0;1];[0;1];[0;1];[0;1];[0;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1;1];[0;1];[0;1;1];[0;0]],[0;1]).

Definition hs_step:(list head) := [h3]^^24.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=4%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - do 7 (eapply evstep_trans; [time stepn (10^7)%N|]).
    stepn 2952764%N.
  - native_check_eq.
Time Qed.
End TM23.


Module TM24.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC0LD_1LD1RA_1LB1LD_0RF1RC_---1RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((E,<[]),(D,[])).
Notation h1 := ((F,<[1;1;0;0]),(D,[])).
Notation h2 := ((A,<[1;1]),(D,[])).
Notation h3 := ((A,<[0;0;1;1]),(D,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1;1;0;1]),([[1;1;1;0;1]],[h0;h0]))::
((h0,[1;0;1]),([[1;1;1]],[]))::
((h0,[1;1;1]),([[1;0;1]],[h0]))::
((h3,[1;1;1;0;1]),([[1;1;1;0;1]],[h1;h0]))::
((h1,[1;1;1;0;1]),([[1;1;1;0;1]],[h1]))::
((h1,[1;1;1]),([[1;1;1;0;1]],[h2;h0]))::
((h2,[1;1;1;0;1]),([[1;0;1];[1;1;1;0]],[]))::
((h0,[1;1;1;0]),([],[h1]))::
((h2,[1;1;1]),([[1;0;1]],[h2]))::
((h2,[1;0;1]),([[1;1;1;0;1]],[h0;h0]))::
((h1,[1;0;1]),([[1;1;1];[1;1;0;1]],[h0]))::
((h0,[1;1;0;1]),([[1;1;1;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1]),([[1;1;1]],[1;1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1;1;0;1]),(0%N,1%N,h0))::
((h0,[1;0;1]),(1%N,0%N,h0))::
((h0,[1;1;1]),(1%N,0%N,h0))::
((h1,[1;1;1;0;1]),(0%N,0%N,h1))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1;0;1];[1;1;1];[1;0;1];[1;0;1];[1;1;1;0;1];[1;0;1];[1;1;1];[1;0;1];[1;1;1;0;1];[1;1;1];[1;0;1];[1;1;1];[1;1;1];[1;1;1];[1;0;1];[1;0;1];[1;0;1];[1;0;1];[1;1;1]],[1;1]).

Definition hs_step:(list head) := [h3]^^28.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[]) (pp:=6%nat) (T:=N.to_nat (10^6)).
  - intros.
    unfold f2 in H.
    apply find_spec in H.
    gen w h a0 a1 h'.
    apply f2_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f1 in H.
    apply find_spec in H.
    gen w h ws hs.
    apply f1_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - intros.
    unfold f0 in H.
    apply find_spec in H.
    gen w h w'.
    apply f0_spec' with (T:=(10^3)).
    time vm_compute; reflexivity.
  - reflexivity.
  - intro X; inverts X.
  - apply BoundedConfig.sideRLs_c_spec with (T:=10^4); reflexivity.
  - esx.
  - native_check_eq.
Time Qed.
End TM24.


