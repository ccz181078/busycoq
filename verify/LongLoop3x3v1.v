From BusyCoq Require Import LongLoop.
From BusyCoq Require Import Individual33.

Module LongLoop62 := LongLoop BB33.
Import LongLoop62.

Require Import ZArith.
Require Import String.

Close Scope N.

Import Eqb.

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

Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; repeat rewrite <-const_unfold; reflexivity.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB2LB1RC_1RA2LB0LB_2RB---0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[]),(B,[])).
Notation h1 := ((C,<[1]),(B,[])).
Notation h2 := ((B,<[1;2]),(B,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[2;2]),([[2;2]],[h0;h0]))::
((h0,[2;0;2]),([[2;0;0]],[]))::
((h0,[2;0;0]),([[2;0;2]],[h0]))::
((h1,[2;2]),([[2;2]],[h1;h0]))::
((h1,[2;0;2]),([[2;2];[2;2]],[]))::
((h1,[2;0;0]),([[2;2];[2;0]],[]))::
((h0,[2;0]),([],[h2]))::
((h2,[2;0;0]),([[2;0;0];[0;0]],[]))::
((h0,[0;0]),([[1;0]],[]))::
((h0,[1;0]),([[2;0]],[]))::
((h2,[2;0;2]),([[2;0;0];[0;2]],[]))::
((h0,[0;2]),([[1;2]],[]))::
((h0,[1;2]),([[2;2]],[]))::
((h2,[2;2]),([[2;0;0];[2]],[]))::
((h0,[2]),([],[h1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1]),([],[2]))::
((h0,[2]),([[2;0;2]],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[2;2]),(0%N,1%N,h0))::
((h0,[2;0;2]),(1%N,0%N,h0))::
((h0,[2;0;0]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[2;2];[2;2];[2;2];[2;2];[2;0;2];[2;0;2];[2;0;2]],[1]).

Definition hs_step:(list head) := [h1]^^30.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=1%nat) (T:=N.to_nat (10^5)).
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
  - stepn 314%N.
  - native_check_eq.
Time Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RC1RC_1RA2LB0LB_2RB---0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((A,<[]),(B,[])).
Notation h1 := ((C,<[1]),(B,[])).
Notation h2 := ((B,<[1;2]),(B,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[2;2]),([[2;2]],[h0;h0]))::
((h0,[2;0;2]),([[2;0;0]],[]))::
((h0,[2;0;0]),([[2;0;2]],[h0]))::
((h1,[2;2]),([[2;2]],[h1;h0]))::
((h1,[2;0;0]),([[2;2]],[h2]))::
((h2,[2;0;2]),([[2;0;0];[0;2]],[]))::
((h0,[0;2]),([[1;2]],[]))::
((h0,[1;2]),([[2;2]],[h0;h0]))::
((h2,[2;2]),([[2;0;0];[2]],[]))::
((h0,[2]),([],[h1]))::
((h1,[2;0;2]),([[2;2];[2;2]],[h0;h0]))::
((h2,[2;0;0]),([[2;0;0];[0;0]],[]))::
((h0,[0;0]),([[1;0]],[]))::
((h0,[1;0]),([],[h2]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1]),([[2;0;2]],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[2;2]),(0%N,1%N,h0))::
((h0,[2;0;2]),(1%N,0%N,h0))::
((h0,[2;0;0]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[2;2];[2;2];[2;2];[2;2];[2;2];[2;0;0];[2;0;2];[2;0;2];[2;0;2];[2;0;2]],[1]).

Definition hs_step:(list head) := [h1]^^15.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=4%nat) (T:=N.to_nat (10^5)).
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
  - stepn 593%N.
  - native_check_eq.
Time Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0RC---_2RC0LB1LB_2LC2RA2RB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((C,<[]),(B,[])).
Notation h1 := ((A,<[2]),(B,[])).
Notation h2 := ((B,<[2;1]),(B,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1]),([[1;1]],[h0;h0]))::
((h0,[1;0;1]),([[1;0;0]],[]))::
((h0,[1;0;0]),([[1;0;1]],[h0]))::
((h1,[1;1]),([[1;1]],[h1;h0]))::
((h1,[1;0;1]),([[1;1];[2;1]],[]))::
((h0,[2;1]),([[1;0]],[]))::
((h0,[1;0]),([],[h2]))::
((h2,[1;0;1]),([[1;0;0;0;1]],[]))::
((h0,[1;0;0;0;1]),([[1;0;1];[1;1]],[]))::
((h2,[1;0;0]),([[1;0;0;0;0]],[]))::
((h0,[1;0;0;0;0]),([[1;0;1];[1;0]],[]))::
((h0,[2;0]),([[1;1]],[h0]))::
((h1,[1;0;0]),([[1;1];[2;0]],[]))::
((h2,[1;1]),([[1;0;0];[1]],[]))::
((h0,[1]),([],[h1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1]),([[1;0;1]],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1]),(0%N,1%N,h0))::
((h0,[1;0;1]),(1%N,0%N,h0))::
((h0,[1;0;0]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;1];[1;1];[1;1];[1;1];[1;1];[1;0;1];[1;0;1];[1;0;0];[1;0;0]],[1]).

Definition hs_step:(list head) := [h1]^^30.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[2]) (pp:=1%nat) (T:=N.to_nat (10^5)).
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
  - stepn 484%N.
  - native_check_eq.
Time Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB2RB0RC_2RA2LA1LB_---2RA1RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((C,<[]),(B,[])).
Notation h1 := ((A,<[2]),(B,[])).
Notation h2 := ((C,<[0]),(B,[])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1;1;2]),([[1;1;1;2]],[h0;h0]))::
((h0,[1;1;2]),([[1;1;1]],[]))::
((h0,[1;1;1]),([[1;1;2]],[h0]))::
((h1,[1;1;1;2]),([[1;1;2];[1]],[h2]))::
((h2,[1;1;1;2]),([[1;1;2;1]],[h0;h0;h2]))::
((h2,[1;1;1]),([[1;1;1;2]],[h0;h0;h0]))::
((h0,[1]),([],[h1]))::
((h1,[1;1;2;1]),([[1;1;1;2]],[h1;h0]))::
((h2,[1;1;2]),([[1;1;2]],[h1]))::
((h1,[1;1;2]),([[1;1;1;2]],[h0;h0]))::
((h1,[1;1;1]),([[1;1;2]],[h1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1]),([[1;1;1]],[1]))::
((h0,[1]),([],[1;1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[1;1;1;2]),(0%N,1%N,h0))::
((h0,[1;1;2]),(1%N,0%N,h0))::
((h0,[1;1;1]),(1%N,0%N,h0))::
((h2,[1;1;2]),(0%N,0%N,h1))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1;1;1;2];[1;1;1;2];[1;1;1;2];[1;1;1];[1;1;1;2];[1;1;1;2];[1;1;1];[1;1;1;2];[1;1;2];[1;1;1];[1;1;2];[1;1;2];[1;1;2]],[1;1]).

Definition hs_step:(list head) := [h1;h0;h2]^^65.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[2;0;1;1]) (pp:=2%nat) (T:=N.to_nat (10^5)).
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
  - stepn 3462%N.
  - native_check_eq.
Time Qed.

End TM4.

