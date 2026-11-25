From BusyCoq Require Import LongLoop.
From BusyCoq Require Import Individual62.

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
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h0 := ((B,<[0]),(E,[0])).
Notation h1 := ((C,<[0;1;0]),(E,[0])).
Notation h2 := ((D,<[0;1;0;0]),(E,[0])).
Notation h3 := ((F,<[0;1;0;1;0;1]),(E,[0])).
Notation h4 := ((B,<[0;1;0;1;0;1;0;1]),(E,[0])).
Notation h5 := ((F,<[0;1]),(E,[0])).
Notation h6 := ((C,<[0;1;0;1;0;1;0;1;1;0]),(E,[0])).
Notation h7 := ((B,<[0;1;0;1]),(E,[0])).
Notation h8 := ((C,<[0;1;0;1;1;0]),(E,[0])).

Definition f1 (w:seg)(h:head):option((list seg)*(list head)) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h1,[1]),([],[h2]))::
((h1,[1;0;1;0]),([[1;0;1;0]],[h1;h0]))::
((h1,[0;0;0]),([[0;0;0];[1;0]],[]))::
((h0,[0;0;0]),([[1;0;0]],[]))::
((h1,[1;0;0]),([],[h3]))::
((h3,[1;0]),([],[h4]))::
((h0,[1;0]),([],[h1]))::
((h3,[0;0;0]),([[1;0;1;0];[0;0;0];[1]],[]))::
((h0,[1]),([],[h5]))::
((h3,[1;0;1;0]),([],[h6]))::
((h6,[0;0;0]),([[1;0;1;0];[1;0;1;0];[1;0;1;0]],[h0;h0]))::
((h5,[0;0;0]),([[0;0;0];[1]],[]))::
((h5,[1;0]),([],[h7]))::
((h5,[1;0;1;0]),([],[h8]))::
((h8,[1;0;1;0]),([[1;0;0];[0;0;1;0]],[h1;h0]))::
((h0,[0;0;1;0]),([[1;0;1;0]],[]))::
((h6,[1;0;1;0]),([[1;0;1;0];[1;0;0];[0;0;1;0]],[h1;h0]))::
((h8,[1;0;0]),([[1;0;0];[0;0;1;0]],[h5]))::
((h6,[1;0;0]),([[1;0;1;0];[1;0;0];[0;0;1;0]],[h5]))::
((h3,[1;0;0]),([[1;0;1;0];[0;0;0];[1]],[]))::
((h5,[1;0;0]),([[0;0;0];[1]],[]))::
((h8,[0;0;0]),([[1;0;1;0];[1;0;1;0]],[h0;h0]))::
((h0,[1;0;0]),([[0;0;0]],[h0]))::
nil) &&& (fun '(x,y) => Some y).

Definition f0 (w:seg)(h:head):option((list seg)*seg) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h2,[]),([[1;0;1;0];[0;0;0]],[1]))::
((h4,[1]),([[1;0;1;0];[1;0;1;0];[1;0;1;0];[0;0;0]],[1]))::
((h0,[1]),([[0;0;0]],[1]))::
((h5,[1]),([[0;0;0]],[1]))::
((h7,[1]),([[1;0;1;0];[1;0;1;0];[0;0;0]],[1]))::
nil) &&& (fun '(x,y) => Some y).

Definition f2 (w:seg)(h:head):option(N*N*head) :=
List.find (fun '(x,y) => eqb x (h,w)) (
((h0,[0;0;0]),(1%N,0%N,h0))::
((h0,[1;0;1;0]),(0%N,1%N,h0))::
((h0,[1;0;0]),(1%N,0%N,h0))::
nil) &&& (fun '(x,y) => Some y).

Definition ws_init:(list seg)*seg := ([[1]],[]).

Definition hs_step:(list head) := [h1]^^86.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply decide_nonhalt_spec with
  (tm:=tm) (f2:=f2) (f1:=f1) (f0:=f0) (hs_step:=hs_step) (ws_init:=ws_init)
  (lh:=0inf<*<[1]) (pp:=7%nat) (T:=N.to_nat (10^6)).
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

Print Assumptions TM1.nonhalt.
