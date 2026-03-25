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
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD0LA_1LA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((E,<[1]),(B,[0])).
Notation h1 := ((D,<[1;0]),(B,[0])).
Notation h2 := ((B,<[1;0;0]),(B,[0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;0;1]),([[0;1;0;1]],[h0;h0]))::
((h0,[1;0;1]),([[0;0;1]],[]))::
((h0,[0;0;1]),([[1;0;1]],[h0]))::
((h2,[0;1;0;1]),([[0;1;0;1]],[h2;h0]))::
((h2,[0;0;1]),([[0;1;0;1];[0]],[]))::
((h2,[1;0;1]),([[1];[0;1;0;1]],[]))::
((h0,[0]),([],[h1]))::
((h1,[1;0;1]),([[0;1;0;1]],[h0;h0]))::
((h1,[0;0;1]),([[1;0;1];[1]],[]))::
((h1,[0;1;0;1]),([[1;0;1]],[h2]))::
((h0,[1]),([[0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[1;0;1]],[]))::
((h1,[]),([[1;0;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;0;1]),(0%N,1%N,h0))::
((h0,[1;0;1]),(1%N,0%N,h0))::
((h0,[0;0;1]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;0;1];[0;1;0;1];[0;0;1];[1;0;1]],[]).

Definition hs_step:(list head) := [h2]^^132.

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
End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0RF_1LD1RE_0LA0RB_0RD0LA_1LC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((E,<[0;1]),(A,[0;1])).
Notation h1 := ((D,<[0;1;0]),(A,[0;1])).
Notation h2 := ((B,<[0;1;0;0]),(A,[0;1])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;0;1]),([[0;1;0;1]],[h0;h0]))::
((h0,[1;0;1]),([[0;0;1]],[]))::
((h0,[0;0;1]),([[1;0;1]],[h0]))::
((h2,[0;1;0;1]),([[0;1;0;1]],[h2;h0]))::
((h2,[0;0;1]),([[0;1;0;1];[0]],[]))::
((h2,[1;0;1]),([[1];[0;1;0;1]],[]))::
((h0,[0]),([],[h1]))::
((h1,[1;0;1]),([[0;1;0;1]],[h0;h0]))::
((h1,[0;0;1]),([[1;0;1];[1]],[]))::
((h1,[0;1;0;1]),([[1;0;1]],[h2]))::
((h0,[1]),([[0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[1;0;1]],[]))::
((h1,[]),([[1;0;1]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;1;0;1]),(0%N,1%N,h0))::
((h0,[1;0;1]),(1%N,0%N,h0))::
((h0,[0;0;1]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[0;1;0;1];[0;1;0;1];[0;0;1];[1;0;1]],[]).

Definition hs_step:(list head) := [h2]^^132.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=5%nat) (T:=N.to_nat (10^6)).
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
End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0LF_0LA1RF_0RA1RB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[1;0]),(F,[0;0])).
Notation h1 := ((D,<[1;0;0]),(F,[0;0])).
Notation h2 := ((E,<[1;0;0;0]),(F,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;1;0]),([[1;1;0]],[]))::
((h0,[1;1;0]),([[0;1;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[1;1;0]),([[1;0;1;0];[1]],[]))::
((h0,[1]),([],[h1]))::
((h1,[1;0;1;0]),([[0;1;0]],[h2]))::
((h1,[1;1;0]),([[0;1;0];[0]],[]))::
((h0,[0]),([[1]],[]))::
((h1,[0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h2,[0;1;0]),([[0;1;0]],[h2]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h1,[1]),([[0;1;0]],[1]))::
((h0,[1]),([[0;1;0]],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[0;1;0]),(1%N,0%N,h0))::
((h0,[1;1;0]),(1%N,0%N,h0))::
((h2,[0;1;0]),(0%N,0%N,h2))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;1;0];[1;1;0];[1;1;0];[1;1;0]],[1]).

Definition hs_step:(list head) := [h2]^^(141*4).

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
  - esx.
  - native_check_eq.
Time Qed.
End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA1RF_0LD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((D,<[0;1]),(A,[0;0])).
Notation h1 := ((E,<[0;1;0]),(A,[0;0])).
Notation h2 := ((C,<[0;1;1;0]),(A,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;0;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[0;0;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[0;0;0]),([[0;0;0];[1;0]],[]))::
((h0,[1;0]),([],[h2]))::
((h2,[1;0;0]),([[1;0;1;0]],[h1]))::
((h1,[1;0;0]),([[1;0;1;0]],[h0]))::
((h1,[0;0;0]),([[0;0;0];[1]],[]))::
((h0,[1]),([],[h1]))::
((h1,[1;0;1;0]),([[1;0;0];[0;0]],[h0;h0]))::
((h0,[0;0]),([[1;0]],[]))::
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
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[1;0;0]],[]).

Definition hs_step:(list head) := [h2]^^368.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=6%nat) (T:=N.to_nat (10^6)).
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
End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA1RB_0LB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((D,<[0;1]),(A,[0;0])).
Notation h1 := ((E,<[0;1;0]),(A,[0;0])).
Notation h2 := ((C,<[0;1;1;0]),(A,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;0;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[0;0;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[0;0;0]),([[0;0;0];[1;0]],[]))::
((h0,[1;0]),([],[h2]))::
((h2,[1;0;0]),([[1;0;1;0]],[h1]))::
((h1,[1;0;0]),([[1;0;1;0]],[h0]))::
((h1,[0;0;0]),([[0;0;0];[1]],[]))::
((h0,[1]),([],[h1]))::
((h1,[1;0;1;0]),([[1;0;0];[0;0]],[h0;h0]))::
((h0,[0;0]),([[1;0]],[]))::
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
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[1;0;0]],[]).

Definition hs_step:(list head) := [h2]^^368.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=6%nat) (T:=N.to_nat (10^6)).
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
End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA0RE_0LB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((D,<[0;1]),(A,[0;0])).
Notation h1 := ((E,<[0;1;0]),(A,[0;0])).
Notation h2 := ((C,<[0;1;1;0]),(A,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;0;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[0;0;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[0;0;0]),([[0;0;0];[1;0]],[]))::
((h0,[1;0]),([],[h2]))::
((h2,[1;0;0]),([[1;0;1;0]],[h1]))::
((h1,[1;0;0]),([[1;0;1;0]],[h0]))::
((h1,[0;0;0]),([[0;0;0];[1]],[]))::
((h0,[1]),([],[h1]))::
((h1,[1;0;1;0]),([[1;0;0];[0;0]],[h0;h0]))::
((h0,[0;0]),([[1;0]],[]))::
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
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;0];[0;0;0];[0;0;0];[1;0;0];[1;0;0]],[]).

Definition hs_step:(list head) := [h2]^^368.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=6%nat) (T:=N.to_nat (10^6)).
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
End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA1RB_1RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((D,<[0;1]),(A,[0;0])).
Notation h1 := ((C,<[0;1;1;0]),(A,[0;0;1;0])).
Notation h2 := ((E,<[0;1;0]),(A,[0;0])).
Notation h3 := ((C,<[0;1;1;0]),(A,[0;0])).
Notation h4 := ((E,<[0;1;1;0;0;1]),(A,[0;0;1;0])).
Notation h5 := ((E,<[0;1;1;1;0;1;0]),(A,[0;0;1;0])).
Notation h6 := ((E,<[0;1;1;0;0;1]),(A,[0;0])).
Notation h7 := ((D,<[0;1;0;1;0;1]),(A,[0;0])).
Notation h8 := ((E,<[0;1;1;1;0;1;0]),(A,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h1,[1;0;1;0]),([[1;0;1;0]],[h1;h1]))::
((h1,[1;0;0;0;0]),([[1;0;0;0;0]],[h0]))::
((h1,[1;0;1;0;0]),([[1;0;1;0;0]],[h0]))::
((h0,[0;0;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[0;0;0]],[h0]))::
((h0,[1;0;1;0;1;0]),([[1;0;1;0;1;0]],[h1;h1]))::
((h4,[1;0;1;0]),([[1;0;1;0]],[h4;h1]))::
((h4,[1;0;0;0;0]),([[1;0;1;0;0];[1;0]],[]))::
((h4,[1;0;1;0;0]),([[1;0;1;0]],[h5;h1]))::
((h0,[1;0]),([],[h3]))::
((h3,[0;0;0]),([[0;0;0];[1;0]],[]))::
((h3,[1;0;0]),([],[h8]))::
((h8,[1;0;0]),([[1;0;1;0;1;0];[1;0]],[h0]))::
((h1,[1;0]),([],[h4]))::
((h4,[1;0;0]),([[1;0;1;0;0]],[h0]))::
((h5,[0;0;0]),([[1;0;0;0;0];[1]],[]))::
((h0,[1]),([],[h2]))::
((h2,[0;0;0]),([[0;0;0];[1]],[]))::
((h2,[1;0;1;0;1;0]),([[1;0;0];[0;0;1;0]],[h1;h1]))::
((h0,[0;0;1;0]),([[1;0;1;0]],[]))::
((h0,[1;0;1;0]),([],[h6]))::
((h6,[1;0;1;0;0]),([[1;0;1;0;1;0]],[h5;h1]))::
((h2,[1;0;0]),([],[h7]))::
((h7,[1;0;0]),([[1;0;1;0;0;0;0]],[h0]))::
((h0,[1;0;1;0;0;0;0]),([[1;0;1;0;0;0;0]],[h0]))::
((h8,[1;0;1;0;1;0]),([[1;0;1;0;1;0;0;0;0;1;0]],[h1;h1]))::
((h0,[1;0;1;0;1;0;0;0;0;1;0]),([[1;0;1;0;1;0;0;1;0;1;0]],[]))::
((h0,[1;0;1;0;1;0;0;1;0;1;0]),([[1;0;1;0;1;0;0];[1;0]],[h4]))::
((h0,[1;0;1;0;1;0;0]),([[1;0;1;0;1;0;0]],[h0]))::
((h3,[1;0;1;0;0]),([[1;0;1;0;1;0;0]],[h0]))::
((h3,[1;0;1;0;0;0;0]),([[1;0;1;0;1;0;0;1;0]],[]))::
((h0,[1;0;1;0;1;0;0;1;0]),([[1;0;1;0;1;0;0]],[h3]))::
((h8,[0;0;0]),([[1;0;1;0;0;0;0];[1]],[]))::
((h2,[1;0;1;0;1;0;0]),([[1;0;0];[0;0;1;0;0]],[h0]))::
((h0,[0;0;1;0;0]),([[1;0;1;0;0]],[]))::
((h0,[1;0;1;0;0]),([],[h8]))::
((h8,[1;0;1;0;1;0;0]),([[1;0;1;0;1;0;0;0;0;1;0;0]],[h0]))::
((h0,[1;0;1;0;1;0;0;0;0;1;0;0]),([[1;0;1;0;1;0;0;1;0;1;0;0]],[]))::
((h0,[1;0;1;0;1;0;0;1;0;1;0;0]),([[1;0;1;0;1;0;0];[1;0;1;0]],[h2]))::
((h6,[1;0;0]),([[1;0;1;0;1;0;0]],[h0]))::
((h8,[1;0;1;0;0;0;0]),([[1;0;1;0;1;0;0];[0;0;0];[0;0]],[h0]))::
((h0,[0;0]),([[1;0]],[]))::
((h4,[0;0;0]),([[1;0;0;0;0]],[h0]))::
((h6,[0;0;0]),([[1;0;1;0;0;0;0]],[h0]))::
((h6,[1;0;0;0;0]),([[1;0;1;0;1;0;0];[1;0]],[]))::
((h5,[1;0;1;0;1;0;0]),([[1;0;1;0;0];[0;0;1;0;0]],[h0]))::
((h3,[1;0;1;0;1;0;0]),([[1;0;1;0;1;0]],[h5;h1]))::
((h5,[1;0;1;0;0;0;0]),([[1;0;1;0;0];[0;0;0];[0;0]],[h0]))::
((h4,[1;0;1;0;1;0]),([[1;0;1;0];[1;0;1;0]],[h1;h1;h1;h1]))::
((h2,[1;0;1;0;0;0;0]),([[1;0;0];[0;0;0];[0;0]],[h0]))::
((h7,[1;0;1;0;1;0]),([[1;0;1;0;1;0];[1;0;1;0]],[h1;h1]))::
((h6,[1;0;1;0;1;0]),([[1;0;1;0;1;0];[1;0;1;0]],[h1;h1;h1;h1]))::
((h5,[1;0;0]),([[1;0;1;0];[1;0]],[h0]))::
((h4,[1;0;1;0;1;0;0]),([[1;0;1;0];[1;0;1;0;0]],[h0;h0]))::
((h3,[1;0;1;0]),([[1;0;1;0;1;0]],[h1;h1]))::
((h3,[1;0;1;0;1;0]),([[1;0;1;0;1;0]],[h4;h1]))::
((h5,[1;0;1;0;1;0]),([[1;0;1;0;0];[0;0;1;0]],[h1;h1]))::
((h6,[1;0;1;0]),([[1;0;1;0;1;0]],[h4;h1]))::
((h4,[1;0;1;0;0;0;0]),([[1;0;1;0];[1;0;0;0;0]],[h0;h0]))::
((h6,[1;0;1;0;0;0;0]),([[1;0;1;0;1;0];[1;0;0;0;0]],[h0;h0]))::
((h7,[0;0;0]),([[1;0;1;0;1;0;0]],[]))::
((h7,[1;0;1;0;0;0;0]),([[1;0;1;0;1;0];[1;0;0;0;0]],[h0]))::
((h7,[1;0;1;0;1;0;0]),([[1;0;1;0;1;0];[1;0;1;0;0]],[h0]))::
((h6,[1;0;1;0;1;0;0]),([[1;0;1;0;1;0];[1;0;1;0;0]],[h0;h0]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[]),([[1;0;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h1,[1;0;1;0]),(0%N,1%N,h1))::
((h1,[1;0;0;0;0]),(0%N,0%N,h0))::
((h1,[1;0;1;0;0]),(0%N,0%N,h0))::
((h0,[0;0;0]),(1%N,0%N,h0))::
((h0,[1;0;0]),(1%N,0%N,h0))::
((h0,[1;0;1;0;1;0]),(0%N,1%N,h1))::
((h0,[1;0;1;0;0;0;0]),(0%N,0%N,h0))::
((h0,[1;0;1;0;1;0;0]),(0%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;0;0;0];[0;0;0];[0;0;0];[1;0;0];[1;0;0]],[]).

Definition hs_step:(list head) := [h4]^^368.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=6%nat) (T:=N.to_nat (10^6)).
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
End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RC_0RE0LD_0RE1LB_0LB1RF_1RB0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((B,<[]),(C,[])).
Notation h1 := ((C,<[0]),(C,[])).
Notation h2 := ((E,<[0;0]),(C,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[1;1;0]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[1;1;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[1;1;0]),([[1;1;0]],[h0;h2]))::
((h2,[1;0;0]),([[1;0;1;0]],[h1]))::
((h0,[1;0]),([],[h2]))::
((h1,[1;0;1;0]),([[1;0;0];[1;0]],[]))::
((h1,[1;1;0]),([[1;0;1;0]],[]))::
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

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;0];[1;1;0];[1;1;0];[1;1;0];[1;1;0];[1;0;0];[1;0;0]],[]).

Definition hs_step:(list head) := [h2;h0]^^108.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;1]) (pp:=6%nat) (T:=N.to_nat (10^6)).
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
End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC0RF_1RB0RD_0LE0RA_1LF1RC_1RE0LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((E,<[1;0;1]),(D,[0;1;0])).
Notation h1 := ((C,<[1;0;1;1]),(D,[0;1;0])).
Notation h2 := ((B,<[1;0;1;1;1]),(D,[0;1;0])).
Notation h3 := ((B,<[1;0;1;1;0;0;1]),(D,[0;1;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;1;0]),([[1;1;0]],[]))::
((h0,[1;1;0]),([[0;1;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[1;1;0]),([[1;0;1;0];[1]],[]))::
((h2,[0;1;0]),([[0;1;0]],[h2]))::
((h1,[1;0;1;0]),([[0;1;0]],[h2]))::
((h1,[1;1;0]),([],[h3]))::
((h1,[0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h3,[0;1;0]),([[0;1;0];[1;0;1;0]],[h0;h0;h0;h0]))::
((h3,[1;1;0]),([[0;1;0];[1;1;0;0]],[]))::
((h3,[1;0;1;0]),([[0;1;0];[1;1;0]],[h2]))::
((h0,[1;1;0;0]),([[0;1;0];[1]],[]))::
((h0,[1]),([],[h1]))::
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

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;1;0];[1;1;0];[0;1;0];[1;1;0];[0;1;0];[0;1;0];[0;1;0];[0;1;0]],[1]).

Definition hs_step:(list head) := [h2]^^172.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[]) (pp:=8%nat) (T:=N.to_nat (10^6)).
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
End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA1RD_0LB0RF_1RE0RC_0LD0RA_1RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((B,<[1;0;1]),(C,[0;1;0])).
Notation h1 := ((D,<[1;0;1;1]),(C,[0;1;0])).
Notation h2 := ((E,<[1;0;1;1;1]),(C,[0;1;0])).
Notation h3 := ((E,<[1;0;1;1;0;0;1]),(C,[0;1;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;1;0]),([[1;1;0]],[]))::
((h0,[1;1;0]),([[0;1;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[1;1;0]),([[1;0;1;0];[1]],[]))::
((h2,[0;1;0]),([[0;1;0]],[h2]))::
((h1,[1;0;1;0]),([[0;1;0]],[h2]))::
((h1,[1;1;0]),([],[h3]))::
((h1,[0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h3,[0;1;0]),([[0;1;0];[1;0;1;0]],[h0;h0;h0;h0]))::
((h3,[1;1;0]),([[0;1;0];[1;1;0;0]],[]))::
((h3,[1;0;1;0]),([[0;1;0];[1;1;0]],[h2]))::
((h0,[1;1;0;0]),([[0;1;0];[1]],[]))::
((h0,[1]),([],[h1]))::
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

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;1;0];[1;1;0];[0;1;0];[1;1;0];[0;1;0];[0;1;0];[0;1;0];[0;1;0]],[1]).

Definition hs_step:(list head) := [h2]^^172.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0;0]) (pp:=8%nat) (T:=N.to_nat (10^6)).
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
End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0RE_0LA1RF_0RA1RB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[1;0]),(F,[0;0])).
Notation h1 := ((D,<[1;0;0]),(F,[0;0])).
Notation h2 := ((E,<[1;0;0;0]),(F,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;1;0]),([[1;1;0]],[]))::
((h0,[1;1;0]),([[0;1;0]],[h0]))::
((h2,[1;0;1;0]),([[1;0;1;0]],[h2;h0]))::
((h2,[0;1;0]),([[0;1;0]],[h2]))::
((h2,[1;1;0]),([[1;0;1;0];[1]],[]))::
((h0,[1]),([],[h1]))::
((h1,[1;0;1;0]),([[0;1;0]],[h2]))::
((h1,[0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h1,[1;1;0]),([[1;0;1;0]],[h0;h0]))::
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

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;1;0];[1;1;0];[1;1;0];[1;1;0]],[1]).

Definition hs_step:(list head) := [h2]^^60.

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
  - esx.
  - native_check_eq.
Time Qed.
End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0RA1RF_0RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[1;0]),(B,[0;0])).
Notation h1 := ((D,<[1;0;0;0]),(B,[0;0])).
Notation h2 := ((C,<[1;1;0;1;1;0]),(B,[0;0])).
Notation h3 := ((C,<[1;0;0;0;1;1;0]),(B,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;1;0]),([[1;1;0]],[]))::
((h0,[1;1;0]),([[0;1;0]],[h0]))::
((h1,[1;0;1;0]),([[1;0;1;0]],[h1;h0]))::
((h1,[0;1;0]),([[0;1;0]],[h1]))::
((h1,[1;1;0]),([],[h3]))::
((h0,[1;0]),([],[h1]))::
((h3,[1;0;1;0]),([[1;0;1;0];[1;1;0];[1;0]],[]))::
((h3,[0;1;0]),([[1;0;1;0];[1;0;1;0]],[h0;h0]))::
((h3,[1;1;0]),([[1;0;1;0];[1;1;1;0]],[]))::
((h0,[1;1;1;0]),([],[h2]))::
((h2,[1;0;1;0]),([[0;1;0];[0;1;0];[1;0]],[]))::
((h2,[1;1;0]),([[0;1;0];[0;1;1;0]],[]))::
((h2,[0;1;0]),([[0;1;0];[0;0;1;0]],[h0;h0]))::
((h0,[0;1;1;0]),([[1;1;1;0]],[]))::
((h0,[0;0;1;0]),([[1;0;1;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1]),([[0;1;0]],[1]))::
((h1,[1]),([[1;0;1;0];[0;1;0]],[1]))::
((h2,[1]),([[0;1;0];[0;1;0]],[]))::
((h0,[]),([],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[0;1;0]),(1%N,0%N,h0))::
((h0,[1;1;0]),(1%N,0%N,h0))::
((h1,[0;1;0]),(0%N,0%N,h1))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;0;1;0];[0;1;0];[0;1;0];[0;1;0];[0;1;0];[0;1;0];[0;1;0];[0;1;0]],[1]).

Definition hs_step:(list head) := [h1]^^(19*4).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1;0]) (pp:=6%nat) (T:=N.to_nat (10^6)).
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
End TM12.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0RA1RF_1RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[1;0]),(B,[0;0])).
Notation h1 := ((D,<[1;0;0;0]),(B,[0;0])).
Notation h2 := ((C,<[1;1;0;1;1;1]),(B,[0;0])).
Notation h3 := ((C,<[1;0;0;0;1;1;1]),(B,[0;0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),([[1;0;1;0]],[h0;h0]))::
((h0,[0;1;0]),([[1;1;0]],[]))::
((h0,[1;1;0]),([[0;1;0]],[h0]))::
((h1,[1;0;1;0]),([[1;0;1;0]],[h1;h0]))::
((h1,[0;1;0]),([[0;1;0]],[h1]))::
((h1,[1;1;0]),([],[h3]))::
((h0,[1;0]),([],[h1]))::
((h3,[1;0;1;0]),([[1;0;1;0];[1;1;0];[1;0]],[]))::
((h3,[0;1;0]),([[1;0;1;0];[1;0;1;0]],[h0]))::
((h3,[1;1;0]),([[1;0;1;0];[1;1;1;0]],[]))::
((h0,[1;1;1;0]),([],[h2]))::
((h2,[1;0;1;0]),([[0;1;0];[0;1;0];[1;0]],[]))::
((h2,[1;1;0]),([[0;1;0];[0;1;1;0]],[]))::
((h2,[0;1;0]),([[0;1;0];[0;0;1;0]],[h0]))::
((h0,[0;1;1;0]),([[1;1;1;0]],[]))::
((h0,[0;0;1;0]),([[1;0;1;0]],[]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1]),([[0;1;0]],[1]))::
((h1,[1]),([[1;0;1;0];[0;1;0]],[1]))::
((h2,[1]),([[0;1;0];[0;1;0]],[]))::
((h0,[]),([],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[0;1;0]),(1%N,0%N,h0))::
((h0,[1;1;0]),(1%N,0%N,h0))::
((h1,[0;1;0]),(0%N,0%N,h1))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;0;1;0];[1;1;0];[0;1;0];[0;1;0];[0;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;1;0];[1;0;1;0];[1;1;0];[1;1;0];[1;1;0];[0;1;0];[0;1;0];[0;1;0];[0;1;0];[0;1;0]],[1]).

Definition hs_step:(list head) := [h1]^^(387*4).

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
    match goal with
    | |- List.forallb ?f ?x = _ =>
      pose (List.map f x) as v1;
      vm_compute in v1
    end.
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
End TM13.

