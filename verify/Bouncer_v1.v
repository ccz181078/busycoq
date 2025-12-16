From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.


Definition if_None {A} (a:option A) b :=
match a with
| None => b tt
| _ => a
end.

Notation "a ||| b" := (if_None a b) (at level 30, right associativity).

Import Eqb.

Ltac des_if H :=
  cbn[if_None] in H;
  cbn[if_Some] in H;
  let E:=fresh "E" in
  match type of H with
  | ?a ||| _ = _ =>
    destruct a eqn:E
  | ?a &&& _ = _ =>
    destruct a eqn:E
  end.

Ltac crefl := vm_compute; try reflexivity.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0RC_---1LD_1RA0LD_1RA1RF_1RD0RF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;1;1;0] {{E}}> r) (at level 30).

Inductive LC: side->Prop :=
| LC_O: LC 0inf
| LC_w0 l: LC l -> LC (l <* <[1;1;1])
| LC_w1 l: LC l -> LC (l <* <[1;1;1;0]).

Ltac esf := repeat (es; er; try follow).

Lemma LC_spec l r:
  LC l ->
  l <| r -->*
  l |> r.
Proof.
  intro H.
  gen r.
  induction H; esf.
Qed.

Section maxT_sec.

Hypothesis maxT:nat.

Definition RInc r :=
skip_prefix [0;0;0] r ||| (fun _ =>
skip_prefix [0;0;1;1] r ||| (fun _ =>
sideRL_c tm (E,<[1;1;1;0]) (D,<[0;0]) r maxT)).

Lemma RInc_spec l r r':
  RInc r = Some r' ->
  LC l ->
  exists l',
  l |> r -->+ l' |> r' /\ LC l'.
Proof.
  unfold RInc.
  intros H HLC.
  des_if H.
  {
    inverts H.
    apply skip_prefix_spec in E; subst.
    eexists; split.
    - er.
    - apply LC_w0,HLC.
  }
  clear E.
  des_if H.
  {
    inverts H.
    apply skip_prefix_spec in E; subst.
    eexists; split.
    - er.
    - apply LC_w1,HLC.
  }
  clear E.
  cbn[if_None] in H.
  {
    apply sideRL_c_spec in H.
    unfold sideRL in H.
    eexists; split.
    - follow10 H.
      follow LC_spec.
      finish.
    - apply HLC.
  }
Qed.

Import Eqb.

Definition RIncs n (r:side) :=
  N.iter n (fun x => x &&& RInc) (Some r).

Lemma RIncs_spec n l r r':
  LC l ->
  RIncs n r = Some r' ->
  exists l', l |> r -->* l' |> r' /\ LC l'.
Proof.
  gen l r r'.
  induction n using N.peano_ind.
  - introv HLC H.
    inverts H.
    eexists; split.
    + finish.
    + auto 1.
  - introv HLC H.
    unfold RIncs in H.
    rewrite N.iter_succ in H.
    des_if H.
    + inverts H.
      eapply IHn in E.
      2: apply HLC.
      destruct E as [l'0 [I3 I4]].
      eapply RInc_spec in H1.
      2: apply I4.
      destruct H1 as [l' [I1 I2]].
      apply progress_evstep in I1.
      eexists; split.
      * follow I3; apply I1.
      * auto 1.
    + inverts H.
Qed.

Lemma nh l r0 T1 T2 r1 r2:
  c0 -->* l |> r0 ->
  LC l ->
  RIncs T1 r0 = Some r1 ->
  RInc r1 = Some r2 ->
  RIncs (T2-1-T1) r2 = Some r1 ->
  ~halts tm c0.
Proof.
  intros Hl HLC I1 I2 I3.
  eapply RIncs_spec in I1.
  2: apply HLC.
  destruct I1 as [l' [I1a I1b]].
  pose (fun l=>l|>r1) as f.
  eapply multistep_nonhalt with (c':=f l').
  1: follow Hl; apply I1a.
  eapply progress_nonhalt_cond with (P:=LC).
  2: shelve.
  intros l0 HP.
  unfold f.
  eapply RInc_spec in I2.
  2: shelve.
  destruct I2 as [l'0 [I2a I2b]].
  eapply RIncs_spec in I3.
  2: shelve.
  destruct I3 as [l'1 [I3a I3b]].
  eexists; split.
  2: shelve.
  follow10 I2a.
  apply I3a.
  Unshelve.
  all: auto 1.
Qed.

End maxT_sec.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nh with (maxT:=10^5) (r0:=[1;1;1]*>0inf) (T1:=212766%N) (T2:=676370%N).
  1: er.
  1: apply LC_w1,LC_O.
  1: crefl.
  1: crefl.
  1: native_check_eq.
Time Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RA_1RC0LB_1RD0RF_1LE0RE_---1LB_1RC1RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [0;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;1;1;0] {{F}}> r) (at level 30).

Inductive LC: side->Prop :=
| LC_O: LC 0inf
| LC_w0 l: LC l -> LC (l <* <[1;1;1])
| LC_w1 l: LC l -> LC (l <* <[1;1;1;0]).

Ltac esf := repeat (es; er; try follow).

Lemma LC_spec l r:
  LC l ->
  l <| r -->*
  l |> r.
Proof.
  intro H.
  gen r.
  induction H; esf.
Qed.

Section maxT_sec.

Hypothesis maxT:nat.

Definition RInc r :=
skip_prefix [0;0;0] r ||| (fun _ =>
skip_prefix [0;0;1;1] r ||| (fun _ =>
sideRL_c tm (F,<[1;1;1;0]) (B,<[0;0]) r maxT)).

Lemma RInc_spec l r r':
  RInc r = Some r' ->
  LC l ->
  exists l',
  l |> r -->+ l' |> r' /\ LC l'.
Proof.
  unfold RInc.
  intros H HLC.
  des_if H.
  {
    inverts H.
    apply skip_prefix_spec in E; subst.
    eexists; split.
    - er.
    - apply LC_w0,HLC.
  }
  clear E.
  des_if H.
  {
    inverts H.
    apply skip_prefix_spec in E; subst.
    eexists; split.
    - er.
    - apply LC_w1,HLC.
  }
  clear E.
  cbn[if_None] in H.
  {
    apply sideRL_c_spec in H.
    unfold sideRL in H.
    eexists; split.
    - follow10 H.
      follow LC_spec.
      finish.
    - apply HLC.
  }
Qed.

Import Eqb.

Definition RIncs n (r:side) :=
  N.iter n (fun x => x &&& RInc) (Some r).

Lemma RIncs_spec n l r r':
  LC l ->
  RIncs n r = Some r' ->
  exists l', l |> r -->* l' |> r' /\ LC l'.
Proof.
  gen l r r'.
  induction n using N.peano_ind.
  - introv HLC H.
    inverts H.
    eexists; split.
    + finish.
    + auto 1.
  - introv HLC H.
    unfold RIncs in H.
    rewrite N.iter_succ in H.
    des_if H.
    + inverts H.
      eapply IHn in E.
      2: apply HLC.
      destruct E as [l'0 [I3 I4]].
      eapply RInc_spec in H1.
      2: apply I4.
      destruct H1 as [l' [I1 I2]].
      apply progress_evstep in I1.
      eexists; split.
      * follow I3; apply I1.
      * auto 1.
    + inverts H.
Qed.

Lemma nh l r0 T1 T2 r1 r2:
  c0 -->* l |> r0 ->
  LC l ->
  RIncs T1 r0 = Some r1 ->
  RInc r1 = Some r2 ->
  RIncs (T2-1-T1) r2 = Some r1 ->
  ~halts tm c0.
Proof.
  intros Hl HLC I1 I2 I3.
  eapply RIncs_spec in I1.
  2: apply HLC.
  destruct I1 as [l' [I1a I1b]].
  pose (fun l=>l|>r1) as f.
  eapply multistep_nonhalt with (c':=f l').
  1: follow Hl; apply I1a.
  eapply progress_nonhalt_cond with (P:=LC).
  2: shelve.
  intros l0 HP.
  unfold f.
  eapply RInc_spec in I2.
  2: shelve.
  destruct I2 as [l'0 [I2a I2b]].
  eapply RIncs_spec in I3.
  2: shelve.
  destruct I3 as [l'1 [I3a I3b]].
  eexists; split.
  2: shelve.
  follow10 I2a.
  apply I3a.
  Unshelve.
  all: auto 1.
Qed.

End maxT_sec.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nh with (maxT:=10^5) (r0:=[1;1;1;1]*>0inf) (T1:=90758%N) (T2:=554362%N).
  1: er.
  1: apply LC_w1,LC_O.
  1: crefl.
  1: crefl.
  1: native_check_eq.
Time Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0LA_---1LD_1RA1LF_0RA1RD_1LC0LB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,<[0;1;0;1;0;1;0]).
Notation hL := (D,[1;1;1;1;1]).

Notation "l <| r" := (l {{{ (hL,L) }}} r) (at level 30).
Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Notation w0 := [0;1;1;1;0;1;1;1;1;1;1].
Notation w1 := [0;1;1;1;0;1;1;1;0;1;0;1].

Inductive LC: side->Prop :=
| LC_O: LC (0inf<*<[1;0;1;0;1;1;1])
| LC_w0 l: LC l -> LC (l <* <[0;1;0;1;1;0;1;0;1;1;1])
| LC_w1 l: LC l -> LC (l <* <[0;1;0;1;0;1;0;1;0;1;1;1]).

Ltac esf := repeat (es; er; try follow).

Lemma LC_spec l r:
  LC l ->
  l <| r -->*
  l |> r.
Proof.
  intro H.
  gen r.
  induction H; esf.
Qed.

Section maxT_sec.

Hypothesis maxT:nat.

Fixpoint chk_prefix T r :=
match T with
| O => Some tt
| S T =>
  (skip_prefix w0 r ||| (fun _ => skip_prefix w1 r)) &&& (fun r => chk_prefix T r)
end.

Definition RInc r :=
(chk_prefix 3 r &&& (fun _ => skip_prefix w0 r)) ||| (fun _ =>
(chk_prefix 3 r &&& (fun _ => skip_prefix w1 r)) ||| (fun _ =>
sideRL_c tm hR hL r maxT)).

Lemma RInc_spec l r r':
  RInc r = Some r' ->
  LC l ->
  exists l',
  l |> r -->+ l' |> r' /\ LC l'.
Proof.
  unfold RInc.
  intros H HLC.
  des_if H.
  {
    inverts H.
    des_if E; inverts E.
    apply skip_prefix_spec in H0; subst.
    eexists; split.
    - er.
    - apply LC_w0,HLC.
  }
  clear E.
  des_if H.
  {
    inverts H.
    des_if E; inverts E.
    apply skip_prefix_spec in H0; subst.
    eexists; split.
    - er.
    - apply LC_w1,HLC.
  }
  clear E.
  cbn[if_None] in H.
  {
    apply sideRL_c_spec in H.
    unfold sideRL in H.
    eexists; split.
    - follow10 H.
      follow LC_spec.
      finish.
    - apply HLC.
  }
Qed.

Import Eqb.

Definition RIncs n (r:side) :=
  N.iter n (fun x => x &&& RInc) (Some r).

Lemma RIncs_spec n l r r':
  LC l ->
  RIncs n r = Some r' ->
  exists l', l |> r -->* l' |> r' /\ LC l'.
Proof.
  gen l r r'.
  induction n using N.peano_ind.
  - introv HLC H.
    inverts H.
    eexists; split.
    + finish.
    + auto 1.
  - introv HLC H.
    unfold RIncs in H.
    rewrite N.iter_succ in H.
    des_if H.
    + inverts H.
      eapply IHn in E.
      2: apply HLC.
      destruct E as [l'0 [I3 I4]].
      eapply RInc_spec in H1.
      2: apply I4.
      destruct H1 as [l' [I1 I2]].
      apply progress_evstep in I1.
      eexists; split.
      * follow I3; apply I1.
      * auto 1.
    + inverts H.
Qed.

Lemma nh l r0 T1 T2 r1 r2:
  c0 -->* l |> r0 ->
  LC l ->
  RIncs T1 r0 = Some r1 ->
  RInc r1 = Some r2 ->
  RIncs (T2-1-T1) r2 = Some r1 ->
  ~halts tm c0.
Proof.
  intros Hl HLC I1 I2 I3.
  eapply RIncs_spec in I1.
  2: apply HLC.
  destruct I1 as [l' [I1a I1b]].
  pose (fun l=>l|>r1) as f.
  eapply multistep_nonhalt with (c':=f l').
  1: follow Hl; apply I1a.
  eapply progress_nonhalt_cond with (P:=LC).
  2: shelve.
  intros l0 HP.
  unfold f.
  eapply RInc_spec in I2.
  2: shelve.
  destruct I2 as [l'0 [I2a I2b]].
  eapply RIncs_spec in I3.
  2: shelve.
  destruct I3 as [l'1 [I3a I3b]].
  eexists; split.
  2: shelve.
  follow10 I2a.
  apply I3a.
  Unshelve.
  all: auto 1.
Qed.

End maxT_sec.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nh with (maxT:=10^6) (r0:=_>>_) (T1:=2827%N) (T2:=36372%N).
  1: stepn' 5992%N.
  1: apply LC_w1,LC_O.
  1: crefl.
  1: crefl.
  1: native_check_eq.
Time Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB1LF_1RB0RC_1RD0LA_0RE1RC_1LA1LB_---0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0;1;1;0;1;1;1]).
Notation hL := (B,[1;0;0;0;0]).

Notation "l <| r" := (l {{{ (hL,L) }}} r) (at level 30).
Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).

Notation w0 := [0;1;1;0;1;0].
Notation w1 := [1;1;0;1;0;1;0].

Inductive LC: side->Prop :=
| LC_O: LC (0inf)
| LC_w0 l: LC l -> LC (l <* <[1;1;1;0;1;1])
| LC_w1 l: LC l -> LC (l <* <[0;1;1;1;0;1;1]).

Ltac esf := repeat (es; er; try follow).

Lemma LC_spec l r:
  LC l ->
  l <| r -->*
  l |> r.
Proof.
  intro H.
  gen r.
  induction H; esf.
Qed.

Section maxT_sec.

Hypothesis maxT:nat.

Fixpoint chk_prefix T r :=
match T with
| O => Some tt
| S T =>
  (skip_prefix w0 r ||| (fun _ => skip_prefix w1 r)) &&& (fun r => chk_prefix T r)
end.

Definition RInc r :=
(chk_prefix 5 r &&& (fun _ => skip_prefix w0 r)) ||| (fun _ =>
(chk_prefix 5 r &&& (fun _ => skip_prefix w1 r)) ||| (fun _ =>
sideRL_c tm hR hL r maxT)).

Lemma RInc_spec l r r':
  RInc r = Some r' ->
  LC l ->
  exists l',
  l |> r -->+ l' |> r' /\ LC l'.
Proof.
  unfold RInc.
  intros H HLC.
  des_if H.
  {
    inverts H.
    des_if E; inverts E.
    apply skip_prefix_spec in H0; subst.
    eexists; split.
    - er.
    - apply LC_w0,HLC.
  }
  clear E.
  des_if H.
  {
    inverts H.
    des_if E; inverts E.
    apply skip_prefix_spec in H0; subst.
    eexists; split.
    - er.
    - apply LC_w1,HLC.
  }
  clear E.
  cbn[if_None] in H.
  {
    apply sideRL_c_spec in H.
    unfold sideRL in H.
    eexists; split.
    - follow10 H.
      follow LC_spec.
      finish.
    - apply HLC.
  }
Qed.

Import Eqb.

Definition RIncs n (r:side) :=
  N.iter n (fun x => x &&& RInc) (Some r).

Lemma RIncs_spec n l r r':
  LC l ->
  RIncs n r = Some r' ->
  exists l', l |> r -->* l' |> r' /\ LC l'.
Proof.
  gen l r r'.
  induction n using N.peano_ind.
  - introv HLC H.
    inverts H.
    eexists; split.
    + finish.
    + auto 1.
  - introv HLC H.
    unfold RIncs in H.
    rewrite N.iter_succ in H.
    des_if H.
    + inverts H.
      eapply IHn in E.
      2: apply HLC.
      destruct E as [l'0 [I3 I4]].
      eapply RInc_spec in H1.
      2: apply I4.
      destruct H1 as [l' [I1 I2]].
      apply progress_evstep in I1.
      eexists; split.
      * follow I3; apply I1.
      * auto 1.
    + inverts H.
Qed.

Lemma nh l r0 T1 T2 r1 r2:
  c0 -->* l |> r0 ->
  LC l ->
  RIncs T1 r0 = Some r1 ->
  RInc r1 = Some r2 ->
  RIncs (T2-1-T1) r2 = Some r1 ->
  ~halts tm c0.
Proof.
  intros Hl HLC I1 I2 I3.
  eapply RIncs_spec in I1.
  2: apply HLC.
  destruct I1 as [l' [I1a I1b]].
  pose (fun l=>l|>r1) as f.
  eapply multistep_nonhalt with (c':=f l').
  1: follow Hl; apply I1a.
  eapply progress_nonhalt_cond with (P:=LC).
  2: shelve.
  intros l0 HP.
  unfold f.
  eapply RInc_spec in I2.
  2: shelve.
  destruct I2 as [l'0 [I2a I2b]].
  eapply RIncs_spec in I3.
  2: shelve.
  destruct I3 as [l'1 [I3a I3b]].
  eexists; split.
  2: shelve.
  follow10 I2a.
  apply I3a.
  Unshelve.
  all: auto 1.
Qed.

End maxT_sec.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nh with (maxT:=10^4) (r0:=_>>_) (T1:=0%N) (T2:=15701%N).
  1: stepn' 21015%N.
  1: apply LC_w0,LC_O.
  1: crefl.
  1: crefl.
  1: native_check_eq.
Time Qed.

End TM4.


