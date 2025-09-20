From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.


Ltac step1s_follow H :=
  (follow H || (step1; step1s_follow H)).

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC---_1LD0LC_1RD1RE_1RF1RF_0RA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Notation "l |> r" :=
  (l {{F}}> r) (at level 30).

Notation "l <1| r" :=
  (l <{{C}} r) (at level 30).

Notation "l <2| r" :=
  (l <{{D}} [1] *> r) (at level 30).

Definition P0 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [1] *> [0]^^n0 *> r -->*
    l <1| [0]^^n *> [1] *> r.

Definition P1 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [0] *> [0]^^n0 *> r -->*
    l <2| [0]^^n *> [1] *> r.

Definition P3 i n n0 :=
  forall l r,
    l <* [1;1] |> [0]^^n *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^i |> r.

Definition P4 i n0 n1 :=
  forall l r,
    l <* [1] <* [0;0]^^i |> [0]^^(1+n1) *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^(1+i) |> r.

Lemma nxtP0:
  forall i n n1,
    P0 i (1+n) n1 ->
    P3 i n n1 ->
    P0 (i+1) (3+n1+n) (n1+n1).
Proof.
  intros i n n1.
  unfold P0,P3.
  intros HP0 HP3 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP0.
  step1s_follow HP3.
  follow HP0.
  es.
Qed.

Lemma nxtP1:
  forall i n n1,
    P0 i (1+n) n1 ->
    P1 i (1+n) (1+n1) ->
    P3 i n n1 ->
    P1 (i+1) (3+n1+n) (1+n1+n1).
Proof.
  intros i n n1.
  unfold P0,P1,P3.
  intros HP0 HP1 HP3 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP1.
  step1s_follow HP3.
  follow HP0.
  es.
Qed.

Lemma nxtP3:
  forall i n n1,
    P3 i n n1 ->
    P4 i n1 (n1+1) ->
    P3 (i+1) (2+n1+n) (n1+n1).
Proof.
  intros i n n1.
  unfold P3,P4.
  intros HP3 HP4 l r.
  rewrite (Nat.add_comm _ n).
  rewrite lpow_add,Str_app_assoc.
  step1s_follow HP3.
  replace (2+n1) with (1+(n1+1)) by lia.
  follow HP4.
  es.
Qed.

Lemma nxtP4:
  forall i n n1,
    P1 i (n+1) (n1+1) ->
    P3 i n n1 ->
    P4 i n1 (n1+1).
Proof.
  intros i n n1.
  unfold P1,P3,P4.
  intros HP1 HP3 l r.
  rewrite lpow_add,Str_app_assoc.
  follow HP1.
  repeat rewrite lpow_add,Str_app_assoc.
  step1s_follow HP3.
  es.
Qed.

Fixpoint Ns i :=
match i with
| O => (0,1)%nat
| S i0 =>
  let (n,n1):=Ns i0 in
  (2+n1+n,n1+n1)
end.

Lemma Pi_spec i:
  let (n,n1):=Ns i in
  P0 i (1+n) n1 /\
  P1 i (1+n) (1+n1) /\
  P3 i n n1 /\
  P4 i n1 (n1+1).
Proof.
  induction i.
  - intros; cbn; unfold P0,P1,P3,P4; repeat split; es.
  - cbn.
    destruct (Ns i) as [n n1].
    replace (S i) with (i+1) by lia.
    destruct IHi as [HP0 [HP1 [HP3 HP4]]].
    pose proof (nxtP0 _ _ _ HP0 HP3) as HP0'.
    pose proof (nxtP1 _ _ _ HP0 HP1 HP3) as HP1'.
    pose proof (nxtP3 _ _ _ HP3 HP4) as HP3'.
    repeat split; try assumption.
    eapply nxtP4 with (n:=2+n1+n).
    + applys_eq HP1'; lia.
    + applys_eq HP3'; lia.
Qed.

Definition S0 i :=
  0inf <* [1] <* [1;1] |> [0]^^(fst (Ns i)) *> [1] *> 0inf.

Lemma BigStep i:
  S0 i -->+ S0 (S i).
Proof.
  unfold S0.
  cbn[Ns].
  epose proof (Pi_spec i) as HPi.
  destruct (Ns i) as [n n1].
  unfold P3,P0 in HPi.
  destruct HPi as [HP0 [_ [HP3 _]]].
  follow HP3.
  epose proof (HP0 _ 0inf) as HP0.
  rewrite (lpow_all0 [0]) in HP0 by solve_const0_eq.
  follow HP0.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: unfold S0; esx.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  apply BigStep.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC---_1LD0LC_1RD1RE_1RF0LD_0RA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Notation "l |> r" :=
  (l {{F}}> r) (at level 30).

Notation "l <1| r" :=
  (l <{{C}} r) (at level 30).

Notation "l <2| r" :=
  (l <{{D}} [1] *> r) (at level 30).

Definition P0 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [1] *> [0]^^n0 *> r -->*
    l <1| [0]^^n *> [1] *> r.

Definition P1 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [0] *> [0]^^n0 *> r -->*
    l <2| [0]^^n *> [1] *> r.

Definition P3 i n n0 :=
  forall l r,
    l <* [1;1] |> [0]^^n *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^i |> r.

Definition P4 i n0 n1 :=
  forall l r,
    l <* [1] <* [0;0]^^i |> [0]^^(1+n1) *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^(1+i) |> r.

Lemma nxtP0:
  forall i n n1,
    P0 i (1+n) n1 ->
    P3 i n n1 ->
    P0 (i+1) (3+n1+n) (n1+n1).
Proof.
  intros i n n1.
  unfold P0,P3.
  intros HP0 HP3 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP0.
  step1s_follow HP3.
  follow HP0.
  es.
Qed.

Lemma nxtP1:
  forall i n n1,
    P0 i (1+n) n1 ->
    P1 i (1+n) (1+n1) ->
    P3 i n n1 ->
    P1 (i+1) (3+n1+n) (1+n1+n1).
Proof.
  intros i n n1.
  unfold P0,P1,P3.
  intros HP0 HP1 HP3 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP1.
  step1s_follow HP3.
  follow HP0.
  es.
Qed.

Lemma nxtP3:
  forall i n n1,
    P3 i n n1 ->
    P4 i n1 (n1+1) ->
    P3 (i+1) (2+n1+n) (n1+n1).
Proof.
  intros i n n1.
  unfold P3,P4.
  intros HP3 HP4 l r.
  rewrite (Nat.add_comm _ n).
  rewrite lpow_add,Str_app_assoc.
  step1s_follow HP3.
  replace (2+n1) with (1+(n1+1)) by lia.
  follow HP4.
  es.
Qed.

Lemma nxtP4:
  forall i n n1,
    P1 i (n+1) (n1+1) ->
    P3 i n n1 ->
    P4 i n1 (n1+1).
Proof.
  intros i n n1.
  unfold P1,P3,P4.
  intros HP1 HP3 l r.
  rewrite lpow_add,Str_app_assoc.
  follow HP1.
  repeat rewrite lpow_add,Str_app_assoc.
  step1s_follow HP3.
  es.
Qed.

Fixpoint Ns i :=
match i with
| O => (0,1)%nat
| S i0 =>
  let (n,n1):=Ns i0 in
  (2+n1+n,n1+n1)
end.

Lemma Pi_spec i:
  let (n,n1):=Ns i in
  P0 i (1+n) n1 /\
  P1 i (1+n) (1+n1) /\
  P3 i n n1 /\
  P4 i n1 (n1+1).
Proof.
  induction i.
  - intros; cbn; unfold P0,P1,P3,P4; repeat split; es.
  - cbn.
    destruct (Ns i) as [n n1].
    replace (S i) with (i+1) by lia.
    destruct IHi as [HP0 [HP1 [HP3 HP4]]].
    pose proof (nxtP0 _ _ _ HP0 HP3) as HP0'.
    pose proof (nxtP1 _ _ _ HP0 HP1 HP3) as HP1'.
    pose proof (nxtP3 _ _ _ HP3 HP4) as HP3'.
    repeat split; try assumption.
    eapply nxtP4 with (n:=2+n1+n).
    + applys_eq HP1'; lia.
    + applys_eq HP3'; lia.
Qed.

Definition S0 i :=
  0inf <* [1] <* [1;1] |> [0]^^(fst (Ns i)) *> [1] *> 0inf.

Lemma BigStep i:
  S0 i -->+ S0 (S i).
Proof.
  unfold S0.
  cbn[Ns].
  epose proof (Pi_spec i) as HPi.
  destruct (Ns i) as [n n1].
  unfold P3,P0 in HPi.
  destruct HPi as [HP0 [_ [HP3 _]]].
  follow HP3.
  epose proof (HP0 _ 0inf) as HP0.
  rewrite (lpow_all0 [0]) in HP0 by solve_const0_eq.
  follow HP0.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: unfold S0; esx.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  apply BigStep.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC---_1LD0LC_1RD1RE_1LD1RF_0RA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Notation "l |> r" :=
  (l {{F}}> r) (at level 30).

Notation "l <1| r" :=
  (l <{{C}} r) (at level 30).

Notation "l <2| r" :=
  (l <{{D}} [1] *> r) (at level 30).

Definition P0 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [1] *> [0]^^n0 *> r -->*
    l <1| [0]^^n *> [1] *> r.

Definition P1 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [0] *> [0]^^n0 *> r -->*
    l <2| [0]^^n *> [1] *> r.

Definition P3 i n n0 :=
  forall l r,
    l <* [1;1] |> [0]^^n *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^i |> r.

Definition P4 i n0 n1 :=
  forall l r,
    l <* [1] <* [0;0]^^i |> [0]^^(1+n1) *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^(1+i) |> r.

Lemma nxtP0:
  forall i n n1,
    P0 i (1+n) n1 ->
    P3 i n n1 ->
    P0 (i+1) (3+n1+n) (n1+n1).
Proof.
  intros i n n1.
  unfold P0,P3.
  intros HP0 HP3 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP0.
  step1s_follow HP3.
  follow HP0.
  es.
Qed.

Lemma nxtP1:
  forall i n n1,
    P0 i (1+n) n1 ->
    P1 i (1+n) (1+n1) ->
    P3 i n n1 ->
    P1 (i+1) (3+n1+n) (1+n1+n1).
Proof.
  intros i n n1.
  unfold P0,P1,P3.
  intros HP0 HP1 HP3 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP1.
  step1s_follow HP3.
  follow HP0.
  es.
Qed.

Lemma nxtP3:
  forall i n n1,
    P3 i n n1 ->
    P4 i n1 (n1+1) ->
    P3 (i+1) (2+n1+n) (n1+n1).
Proof.
  intros i n n1.
  unfold P3,P4.
  intros HP3 HP4 l r.
  rewrite (Nat.add_comm _ n).
  rewrite lpow_add,Str_app_assoc.
  step1s_follow HP3.
  replace (2+n1) with (1+(n1+1)) by lia.
  follow HP4.
  es.
Qed.

Lemma nxtP4:
  forall i n n1,
    P1 i (n+1) (n1+1) ->
    P3 i n n1 ->
    P4 i n1 (n1+1).
Proof.
  intros i n n1.
  unfold P1,P3,P4.
  intros HP1 HP3 l r.
  rewrite lpow_add,Str_app_assoc.
  follow HP1.
  repeat rewrite lpow_add,Str_app_assoc.
  step1s_follow HP3.
  es.
Qed.

Fixpoint Ns i :=
match i with
| O => (0,1)%nat
| S i0 =>
  let (n,n1):=Ns i0 in
  (2+n1+n,n1+n1)
end.

Lemma Pi_spec i:
  let (n,n1):=Ns i in
  P0 i (1+n) n1 /\
  P1 i (1+n) (1+n1) /\
  P3 i n n1 /\
  P4 i n1 (n1+1).
Proof.
  induction i.
  - intros; cbn; unfold P0,P1,P3,P4; repeat split; es.
  - cbn.
    destruct (Ns i) as [n n1].
    replace (S i) with (i+1) by lia.
    destruct IHi as [HP0 [HP1 [HP3 HP4]]].
    pose proof (nxtP0 _ _ _ HP0 HP3) as HP0'.
    pose proof (nxtP1 _ _ _ HP0 HP1 HP3) as HP1'.
    pose proof (nxtP3 _ _ _ HP3 HP4) as HP3'.
    repeat split; try assumption.
    eapply nxtP4 with (n:=2+n1+n).
    + applys_eq HP1'; lia.
    + applys_eq HP3'; lia.
Qed.

Definition S0 i :=
  0inf <* [1] <* [1;1] |> [0]^^(fst (Ns i)) *> [1] *> 0inf.

Lemma BigStep i:
  S0 i -->+ S0 (S i).
Proof.
  unfold S0.
  cbn[Ns].
  epose proof (Pi_spec i) as HPi.
  destruct (Ns i) as [n n1].
  unfold P3,P0 in HPi.
  destruct HPi as [HP0 [_ [HP3 _]]].
  follow HP3.
  epose proof (HP0 _ 0inf) as HP0.
  rewrite (lpow_all0 [0]) in HP0 by solve_const0_eq.
  follow HP0.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: unfold S0; esx.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  apply BigStep.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB0LD_1LC0LB_1RD1RA_0RE1RC_0RF---_0RA1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Notation "l |> r" :=
  (l {{F}}> r) (at level 30).

Notation "l <1| r" :=
  (l <{{B}} r) (at level 30).

Notation "l <2| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Definition P0 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [1] *> [0]^^n0 *> r -->*
    l <1| [0]^^n *> [1] *> r.

Definition P1 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [0] *> [0]^^n0 *> r -->*
    l <2| [0]^^n *> [1] *> r.

Definition P3 i n n0 :=
  forall l r,
    l <* [1;1] {{D}}> [0]^^n *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^i |> r.

Definition P4 i n0 n1 :=
  forall l r,
    l <* [1] <* [0;0]^^i |> [0]^^(1+n1) *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^(1+i) |> r.

Lemma nxtP0:
  forall i n n1,
    P0 i (1+n) n1 ->
    P3 i n n1 ->
    P0 (i+1) (3+n1+n) (n1+n1).
Proof.
  intros i n n1.
  unfold P0,P3.
  intros HP0 HP3 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP0.
  step1s_follow HP3.
  follow HP0.
  es.
Qed.

Lemma nxtP1:
  forall i n n1,
    P0 i (1+n) n1 ->
    P1 i (1+n) (1+n1) ->
    P3 i n n1 ->
    P1 (i+1) (3+n1+n) (1+n1+n1).
Proof.
  intros i n n1.
  unfold P0,P1,P3.
  intros HP0 HP1 HP3 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP1.
  step1s_follow HP3.
  follow HP0.
  es.
Qed.

Lemma nxtP3:
  forall i n n1,
    P3 i n n1 ->
    P4 i n1 (n1+1) ->
    P3 (i+1) (2+n1+n) (n1+n1).
Proof.
  intros i n n1.
  unfold P3,P4.
  intros HP3 HP4 l r.
  rewrite (Nat.add_comm _ n).
  rewrite lpow_add,Str_app_assoc.
  step1s_follow HP3.
  replace (2+n1) with (1+(n1+1)) by lia.
  follow HP4.
  es.
Qed.

Lemma nxtP4:
  forall i n n1,
    P1 i (n+1) (n1+1) ->
    P3 i n n1 ->
    P4 i n1 (n1+1).
Proof.
  intros i n n1.
  unfold P1,P3,P4.
  intros HP1 HP3 l r.
  rewrite lpow_add,Str_app_assoc.
  follow HP1.
  repeat rewrite lpow_add,Str_app_assoc.
  step1s_follow HP3.
  es.
Qed.

Fixpoint Ns i :=
match i with
| O => (2,1)%nat
| S i0 =>
  let (n,n1):=Ns i0 in
  (2+n1+n,n1+n1)
end.

Lemma Pi_spec i:
  let (n,n1):=Ns i in
  P0 (S i) (1+n) n1 /\
  P1 (S i) (1+n) (1+n1) /\
  P3 (S i) n n1 /\
  P4 (S i) n1 (n1+1).
Proof.
  induction i.
  - intros; cbn; unfold P0,P1,P3,P4; repeat split; es.
  - cbn.
    destruct (Ns i) as [n n1].
    replace (S i) with (i+1) by lia.
    destruct IHi as [HP0 [HP1 [HP3 HP4]]].
    pose proof (nxtP0 _ _ _ HP0 HP3) as HP0'.
    pose proof (nxtP1 _ _ _ HP0 HP1 HP3) as HP1'.
    pose proof (nxtP3 _ _ _ HP3 HP4) as HP3'.
    repeat split; try assumption.
    eapply nxtP4 with (n:=2+n1+n).
    + applys_eq HP1'; lia.
    + applys_eq HP3'; lia.
Qed.

Definition S0 i :=
  0inf <* [1] <* [1;1] {{D}}> [0]^^(fst (Ns i)) *> [1] *> 0inf.

Lemma BigStep i:
  S0 i -->+ S0 (S i).
Proof.
  unfold S0.
  cbn[Ns].
  epose proof (Pi_spec i) as HPi.
  destruct (Ns i) as [n n1].
  unfold P3,P0 in HPi.
  destruct HPi as [HP0 [_ [HP3 _]]].
  follow HP3.
  epose proof (HP0 _ 0inf) as HP0.
  rewrite (lpow_all0 [0]) in HP0 by solve_const0_eq.
  follow HP0.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: unfold S0; esx.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  apply BigStep.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB0LD_1LC0LB_1RD1RA_0RE1RC_0RF---_0RA0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Notation "l |> r" :=
  (l {{F}}> r) (at level 30).

Notation "l <1| r" :=
  (l <{{B}} r) (at level 30).

Notation "l <2| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Definition P0 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [1] *> [0]^^n0 *> r -->*
    l <1| [0]^^n *> [1] *> r.

Definition P1 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [0] *> [0]^^n0 *> r -->*
    l <2| [0]^^n *> [1] *> r.

Definition P3 i n n0 :=
  forall l r,
    l <* [1;1] {{D}}> [0]^^n *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^i |> r.

Definition P4 i n0 n1 :=
  forall l r,
    l <* [1] <* [0;0]^^i |> [0]^^(1+n1) *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^(1+i) |> r.

Lemma nxtP0:
  forall i n n1,
    P0 i (1+n) n1 ->
    P3 i n n1 ->
    P0 (i+1) (3+n1+n) (n1+n1).
Proof.
  intros i n n1.
  unfold P0,P3.
  intros HP0 HP3 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP0.
  step1s_follow HP3.
  follow HP0.
  es.
Qed.

Lemma nxtP1:
  forall i n n1,
    P0 i (1+n) n1 ->
    P1 i (1+n) (1+n1) ->
    P3 i n n1 ->
    P1 (i+1) (3+n1+n) (1+n1+n1).
Proof.
  intros i n n1.
  unfold P0,P1,P3.
  intros HP0 HP1 HP3 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP1.
  step1s_follow HP3.
  follow HP0.
  es.
Qed.

Lemma nxtP3:
  forall i n n1,
    P3 i n n1 ->
    P4 i n1 (n1+1) ->
    P3 (i+1) (2+n1+n) (n1+n1).
Proof.
  intros i n n1.
  unfold P3,P4.
  intros HP3 HP4 l r.
  rewrite (Nat.add_comm _ n).
  rewrite lpow_add,Str_app_assoc.
  step1s_follow HP3.
  replace (2+n1) with (1+(n1+1)) by lia.
  follow HP4.
  es.
Qed.

Lemma nxtP4:
  forall i n n1,
    P1 i (n+1) (n1+1) ->
    P3 i n n1 ->
    P4 i n1 (n1+1).
Proof.
  intros i n n1.
  unfold P1,P3,P4.
  intros HP1 HP3 l r.
  rewrite lpow_add,Str_app_assoc.
  follow HP1.
  repeat rewrite lpow_add,Str_app_assoc.
  step1s_follow HP3.
  es.
Qed.

Fixpoint Ns i :=
match i with
| O => (2,1)%nat
| S i0 =>
  let (n,n1):=Ns i0 in
  (2+n1+n,n1+n1)
end.

Lemma Pi_spec i:
  let (n,n1):=Ns i in
  P0 (S i) (1+n) n1 /\
  P1 (S i) (1+n) (1+n1) /\
  P3 (S i) n n1 /\
  P4 (S i) n1 (n1+1).
Proof.
  induction i.
  - intros; cbn; unfold P0,P1,P3,P4; repeat split; es.
  - cbn.
    destruct (Ns i) as [n n1].
    replace (S i) with (i+1) by lia.
    destruct IHi as [HP0 [HP1 [HP3 HP4]]].
    pose proof (nxtP0 _ _ _ HP0 HP3) as HP0'.
    pose proof (nxtP1 _ _ _ HP0 HP1 HP3) as HP1'.
    pose proof (nxtP3 _ _ _ HP3 HP4) as HP3'.
    repeat split; try assumption.
    eapply nxtP4 with (n:=2+n1+n).
    + applys_eq HP1'; lia.
    + applys_eq HP3'; lia.
Qed.

Definition S0 i :=
  0inf <* [1] <* [1;1] {{D}}> [0]^^(fst (Ns i)) *> [1] *> 0inf.

Lemma BigStep i:
  S0 i -->+ S0 (S i).
Proof.
  unfold S0.
  cbn[Ns].
  epose proof (Pi_spec i) as HPi.
  destruct (Ns i) as [n n1].
  unfold P3,P0 in HPi.
  destruct HPi as [HP0 [_ [HP3 _]]].
  follow HP3.
  epose proof (HP0 _ 0inf) as HP0.
  rewrite (lpow_all0 [0]) in HP0 by solve_const0_eq.
  follow HP0.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: unfold S0; esx.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  apply BigStep.
Qed.

End TM5.



