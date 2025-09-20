From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC0RA_1LD0LF_0RD1RE_1LC1RB_0LD1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l {{C}}> r) (at level 30).
Notation "l |2> r" := (l {{E}}> r) (at level 30).
Notation "l <| r" := (l <{{D}} [0;0] *> r) (at level 30).

Definition S0 a b c r :=
  0inf <* <[0;1]^^a <* <[1;0]^^b |> [1;0]^^c *> r.

Lemma Inc0 a b c r:
  S0 (1+a) b (1+c) r -->*
  S0 a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n a b c r:
  S0 (n+a) b (n+c) r -->*
  S0 a (n*2+b) c r.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Definition S1 a b :=
  0inf <* <[0;1]^^a <* <[1;0]^^(1+b) |> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (3+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*3+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Definition P a :=
  forall r,
  0inf <| [1;0]^^a *> r -->*
  0inf <* <[0;1]^^a |2> r.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+1+a+1) by lia.
  unfold P.
  intros HP r.
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP.
  mid (S0 (a+0) 1 (a+0) ([1;0]*>r)).
  1: es.
  follow Incs0.
  unfold S0.
  replace (a*2) with (a+a) by lia.
  mid (0inf <| [1;0]^^a *> [1;0]^^(1+a) *> [0] *> r).
  1: es.
  follow HP.
  mid (S0 (a+0) 1 (a+0) ([0]*>r)).
  1: es.
  follow Incs0.
  replace (a*2) with (a+a) by lia.
  es.
Qed.

Definition S a :=
  0inf <| [1;0]^^a *> 0inf.

Lemma BigStep a n:
  a+1<=n<=a*2 ->
  P a ->
  S n -->+
  S (a*4+3-n).
Proof.
  unfold P,S.
  intros Hn HP.
  remember (a*4+1-n) as v1.
  replace (a*4+3-n) with (2+v1) by lia.
  replace n with (a+1+(n-a-1)) by lia.
  do 2 rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid10 (S0 a 1 (n-a-1) 0inf).
  1: es.
  remember (n-a-1) as b.
  mid (S0 (b+(a-b)) 1 (b+0) 0inf).
  1: finish.
  follow Incs0.
  mid (S1 (a-b) (b*2)).
  1: es.
  follow Incs1.
  replace ((a-b)*3+b*2) with (v1) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 5).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a, a+1<=n<=a*2 /\ P a).
  2: exists 4; split; [lia|]; unfold P; es.
  intros n [a [Ha HP]].
  eexists; split.
  1: eapply BigStep; eassumption.
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC0RA_1RD0LE_1LC1RB_0LF1LA_0RF1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l {{C}}> r) (at level 30).
Notation "l |2> r" := (l {{D}}> r) (at level 30).
Notation "l <| r" := (l <{{F}} [0;0] *> r) (at level 30).

Definition S0 a b c r :=
  0inf <* <[0;1]^^a <* <[1;0]^^b |> [1;0]^^c *> r.

Lemma Inc0 a b c r:
  S0 (1+a) b (1+c) r -->*
  S0 a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n a b c r:
  S0 (n+a) b (n+c) r -->*
  S0 a (n*2+b) c r.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Definition S1 a b :=
  0inf <* <[0;1]^^a <* <[1;0]^^(1+b) |> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (3+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*3+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Definition P a :=
  forall r,
  0inf <| [1;0]^^a *> r -->*
  0inf <* <[0;1]^^a |2> r.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+1+a+1) by lia.
  unfold P.
  intros HP r.
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP.
  mid (S0 (a+0) 1 (a+0) ([1;0]*>r)).
  1: es.
  follow Incs0.
  unfold S0.
  replace (a*2) with (a+a) by lia.
  mid (0inf <| [1;0]^^a *> [1;0]^^(1+a) *> [0] *> r).
  1: es.
  follow HP.
  mid (S0 (a+0) 1 (a+0) ([0]*>r)).
  1: es.
  follow Incs0.
  replace (a*2) with (a+a) by lia.
  es.
Qed.

Definition S a :=
  0inf <| [1;0]^^a *> 0inf.

Lemma BigStep a n:
  a+1<=n<=a*2 ->
  P a ->
  S n -->+
  S (a*4+3-n).
Proof.
  unfold P,S.
  intros Hn HP.
  remember (a*4+1-n) as v1.
  replace (a*4+3-n) with (2+v1) by lia.
  replace n with (a+1+(n-a-1)) by lia.
  do 2 rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid10 (S0 a 1 (n-a-1) 0inf).
  1: es.
  remember (n-a-1) as b.
  mid (S0 (b+(a-b)) 1 (b+0) 0inf).
  1: finish.
  follow Incs0.
  mid (S1 (a-b) (b*2)).
  1: es.
  follow Incs1.
  replace ((a-b)*3+b*2) with (v1) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 5).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a, a+1<=n<=a*2 /\ P a).
  2: exists 4; split; [lia|]; unfold P; es.
  intros n [a [Ha HP]].
  eexists; split.
  1: eapply BigStep; eassumption.
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA0LD_1RB0RA_0RF1LE_0LD0LF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* [1] {{B}}> r) (at level 30).
Notation "l |2> r" := (l <* [1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{D}} [0;1;0] *> r) (at level 30).

Definition S0 a b c r :=
  0inf <* <[0;1]^^a <* <[1;0]^^b |> [1;0]^^c *> r.

Lemma Inc0 a b c r:
  S0 (1+a) b (1+c) r -->*
  S0 a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n a b c r:
  S0 (n+a) b (n+c) r -->*
  S0 a (n*2+b) c r.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Definition S1 a b :=
  0inf <* <[0;1]^^a <* <[1;0]^^(1+b) |> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (3+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*3+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Definition P a :=
  forall r,
  0inf <| [1;0]^^a *> r -->*
  0inf <* <[0;1]^^a |2> r.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+1+a+1) by lia.
  unfold P.
  intros HP r.
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP.
  mid (S0 (a+0) 1 (a+0) ([1;0]*>r)).
  1: es.
  follow Incs0.
  unfold S0.
  replace (a*2) with (a+a) by lia.
  mid (0inf <| [1;0]^^a *> [1;0]^^(1+a) *> [0] *> r).
  1: es.
  follow HP.
  mid (S0 (a+0) 1 (a+0) ([0]*>r)).
  1: es.
  follow Incs0.
  replace (a*2) with (a+a) by lia.
  es.
Qed.

Definition S a :=
  0inf <| [1;0]^^a *> 0inf.

Lemma BigStep a n:
  a+1<=n<=a*2 ->
  P a ->
  S n -->+
  S (a*4+3-n).
Proof.
  unfold P,S.
  intros Hn HP.
  remember (a*4+1-n) as v1.
  replace (a*4+3-n) with (2+v1) by lia.
  replace n with (a+1+(n-a-1)) by lia.
  do 2 rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid10 (S0 a 1 (n-a-1) 0inf).
  1: es.
  remember (n-a-1) as b.
  mid (S0 (b+(a-b)) 1 (b+0) 0inf).
  1: finish.
  follow Incs0.
  mid (S1 (a-b) (b*2)).
  1: es.
  follow Incs1.
  replace ((a-b)*3+b*2) with (v1) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 5).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a, a+1<=n<=a*2 /\ P a).
  2: exists 4; split; [lia|]; unfold P; es.
  intros n [a [Ha HP]].
  eexists; split.
  1: eapply BigStep; eassumption.
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA0LD_1RB0LD_0RF1LE_0LD0LF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* [1] {{B}}> r) (at level 30).
Notation "l |2> r" := (l <* [1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{D}} [0;1;0] *> r) (at level 30).

Definition S0 a b c r :=
  0inf <* <[0;1]^^a <* <[1;0]^^b |> [1;0]^^c *> r.

Lemma Inc0 a b c r:
  S0 (1+a) b (1+c) r -->*
  S0 a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n a b c r:
  S0 (n+a) b (n+c) r -->*
  S0 a (n*2+b) c r.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Definition S1 a b :=
  0inf <* <[0;1]^^a <* <[1;0]^^(1+b) |> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (3+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*3+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Definition P a :=
  forall r,
  0inf <| [1;0]^^a *> r -->*
  0inf <* <[0;1]^^a |2> r.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+1+a+1) by lia.
  unfold P.
  intros HP r.
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP.
  mid (S0 (a+0) 1 (a+0) ([1;0]*>r)).
  1: es.
  follow Incs0.
  unfold S0.
  replace (a*2) with (a+a) by lia.
  mid (0inf <| [1;0]^^a *> [1;0]^^(1+a) *> [0] *> r).
  1: es.
  follow HP.
  mid (S0 (a+0) 1 (a+0) ([0]*>r)).
  1: es.
  follow Incs0.
  replace (a*2) with (a+a) by lia.
  es.
Qed.

Definition S a :=
  0inf <| [1;0]^^a *> 0inf.

Lemma BigStep a n:
  a+1<=n<=a*2 ->
  P a ->
  S n -->+
  S (a*4+3-n).
Proof.
  unfold P,S.
  intros Hn HP.
  remember (a*4+1-n) as v1.
  replace (a*4+3-n) with (2+v1) by lia.
  replace n with (a+1+(n-a-1)) by lia.
  do 2 rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid10 (S0 a 1 (n-a-1) 0inf).
  1: es.
  remember (n-a-1) as b.
  mid (S0 (b+(a-b)) 1 (b+0) 0inf).
  1: finish.
  follow Incs0.
  mid (S1 (a-b) (b*2)).
  1: es.
  follow Incs1.
  replace ((a-b)*3+b*2) with (v1) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 5).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a, a+1<=n<=a*2 /\ P a).
  2: exists 4; split; [lia|]; unfold P; es.
  intros n [a [Ha HP]].
  eexists; split.
  1: eapply BigStep; eassumption.
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB1LE_0RC1RE_1RE0RD_1LE0RC_1RD0LF_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* [1] {{E}}> r) (at level 30).
Notation "l |2> r" := (l <* [1] {{D}}> r) (at level 30).
Notation "l <| r" := (l <{{B}} [1;1;0] *> r) (at level 30).

Definition S0 a b c r :=
  0inf <* <[0;1]^^a <* <[1;0]^^b |> [1;0]^^c *> r.

Lemma Inc0 a b c r:
  S0 (1+a) b (1+c) r -->*
  S0 a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n a b c r:
  S0 (n+a) b (n+c) r -->*
  S0 a (n*2+b) c r.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Definition S1 a b :=
  0inf <* <[0;1]^^a <* <[1;0]^^(1+b) |> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (3+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*3+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Definition P a :=
  forall r,
  0inf <| [1;0]^^a *> r -->*
  0inf <* <[0;1]^^a |2> r.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+1+a+1) by lia.
  unfold P.
  intros HP r.
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP.
  mid (S0 (a+0) 1 (a+0) ([1;0]*>r)).
  1: es.
  follow Incs0.
  unfold S0.
  replace (a*2) with (a+a) by lia.
  mid (0inf <| [1;0]^^a *> [1;0]^^(1+a) *> [0] *> r).
  1: es.
  follow HP.
  mid (S0 (a+0) 1 (a+0) ([0]*>r)).
  1: es.
  follow Incs0.
  replace (a*2) with (a+a) by lia.
  es.
Qed.

Definition S a :=
  0inf <| [1;0]^^a *> 0inf.

Lemma BigStep a n:
  a+1<=n<=a*2 ->
  P a ->
  S n -->+
  S (a*4+3-n).
Proof.
  unfold P,S.
  intros Hn HP.
  remember (a*4+1-n) as v1.
  replace (a*4+3-n) with (2+v1) by lia.
  replace n with (a+1+(n-a-1)) by lia.
  do 2 rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid10 (S0 a 1 (n-a-1) 0inf).
  1: es.
  remember (n-a-1) as b.
  mid (S0 (b+(a-b)) 1 (b+0) 0inf).
  1: finish.
  follow Incs0.
  mid (S1 (a-b) (b*2)).
  1: es.
  follow Incs1.
  replace ((a-b)*3+b*2) with (v1) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 5).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a, a+1<=n<=a*2 /\ P a).
  2: exists 4; split; [lia|]; unfold P; es.
  intros n [a [Ha HP]].
  eexists; split.
  1: eapply BigStep; eassumption.
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RA_1RD0LE_0RE0RF_1LF0RC_0LC1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l {{C}}> r) (at level 30).
Notation "l |2> r" := (l {{D}}> r) (at level 30).
Notation "l <| r" := (l <{{F}} r) (at level 30).

Definition S0 l a b c r :=
  l <* <[0;1;0]^^a <* [0] <* <[0;1;0]^^b <* [0] |> [1;0;0]^^c *> r.

Lemma Inc0 l a b c r:
  S0 l (1+a) b (1+c) r -->*
  S0 l a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n l a b c r:
  S0 l (n+a) b (n+c) r -->*
  S0 l a (n*2+b) c r.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1 l a b:
  S0 l (1+a) b 0 0inf -->*
  S0 l a (3+b) 0 0inf.
Proof.
  unfold S0.
  es_v2.
Qed.

Lemma Incs1 l a b:
  S0 l a b 0 0inf -->*
  S0 l 0 (a*3+b) 0 0inf.
Proof.
  gen b.
  ind a Inc1.
Qed.

Definition P a :=
  forall l r,
  l <* [1] <| [1;0;0;1] *> [0;0;1]^^a *> r -->*
  l <* [1;1;1] <* <[0;1;0]^^a <* <[0;1] |2> r.


Lemma P' a:
  P a ->
  forall l r,
  l <* [1] <| [1;0;0]^^(2+a) *> r -->*
  l <* [1]^^5 <* <[0;1;0]^^a <* <[0;1] |2> r.
Proof.
  unfold P.
  intros HP l r.
  epose proof (HP l ([0;0]*>r)) as I1.
  eapply evstep_trans.
  2: follow I1.
  1: es.
  er; sr.
  follow HP.
  finish.
Qed.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  intros HP l r.
  epose proof (P' _ HP) as HP'.
  replace (a*2+2) with (2+a+a) by lia.
  specialize (HP' l ([1;0;0]^^(1+a) *> [1] *> r)). 
  eapply evstep_trans.
  2: follow HP'.
  1: es.
  do 11 step1.
  mid (S0 ([1]^^5*>l) (a+0) 1 (a+0) ([1]*>r)).
  1: es.
  follow Incs0.
  unfold S0.
  replace (a*2) with (a+a) by lia.
  es.
Qed.

Definition S '(a0,a) :=
  0inf <* [1]^^a0 <* [1] <| [1;0;0]^^a *> 0inf.

Lemma BigStep a0 a n:
  a+3<=n<=a*2+3 ->
  P a ->
  S (a0,n) -->+
  S (2+a0,a*4+8-n).
Proof.
  intros Ha HP.
  remember (a*4+4-n) as v1.
  replace (a*4+8-n) with (4+v1) by lia.
  unfold S.
  epose proof (P' _ HP) as HP'.
  remember (n-a-3) as b.
  replace n with (2+a+(1+b)) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP'.
  mid10 (S0 (0inf<*[1]^^(5+a0)) a 1 (b+0) 0inf).
  1: es.
  replace a with (b+(a-b)) by lia.
  follow Incs0.
  follow Incs1.
  replace ((a-b)*3+(b*2+1)) with v1 by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(O,3)).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(a0,n) => exists a, a+3<=n<=a*2+3 /\ P a).
  2: exists O; split; [lia|]; unfold P; es.
  intros [a0 n] [a [Ha HP]].
  eexists; split.
  1: eapply BigStep; eassumption.
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC---_1RD0LE_0RE0RF_1LF0RC_0LC1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l {{C}}> r) (at level 30).
Notation "l |2> r" := (l {{D}}> r) (at level 30).
Notation "l <| r" := (l <{{F}} r) (at level 30).

Definition S0 l a b c r :=
  l <* <[0;1;0]^^a <* [0] <* <[0;1;0]^^b <* [0] |> [1;0;0]^^c *> r.

Lemma Inc0 l a b c r:
  S0 l (1+a) b (1+c) r -->*
  S0 l a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n l a b c r:
  S0 l (n+a) b (n+c) r -->*
  S0 l a (n*2+b) c r.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1 l a b:
  S0 l (1+a) b 0 0inf -->*
  S0 l a (3+b) 0 0inf.
Proof.
  unfold S0.
  es_v2.
Qed.

Lemma Incs1 l a b:
  S0 l a b 0 0inf -->*
  S0 l 0 (a*3+b) 0 0inf.
Proof.
  gen b.
  ind a Inc1.
Qed.

Definition P a :=
  forall l r,
  l <* [1] <| [1;0;0;1] *> [0;0;1]^^a *> r -->*
  l <* [1;1;1] <* <[0;1;0]^^a <* <[0;1] |2> r.


Lemma P' a:
  P a ->
  forall l r,
  l <* [1] <| [1;0;0]^^(2+a) *> r -->*
  l <* [1]^^5 <* <[0;1;0]^^a <* <[0;1] |2> r.
Proof.
  unfold P.
  intros HP l r.
  epose proof (HP l ([0;0]*>r)) as I1.
  eapply evstep_trans.
  2: follow I1.
  1: es.
  er; sr.
  follow HP.
  finish.
Qed.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  intros HP l r.
  epose proof (P' _ HP) as HP'.
  replace (a*2+2) with (2+a+a) by lia.
  specialize (HP' l ([1;0;0]^^(1+a) *> [1] *> r)). 
  eapply evstep_trans.
  2: follow HP'.
  1: es.
  do 11 step1.
  mid (S0 ([1]^^5*>l) (a+0) 1 (a+0) ([1]*>r)).
  1: es.
  follow Incs0.
  unfold S0.
  replace (a*2) with (a+a) by lia.
  es.
Qed.

Definition S '(a0,a) :=
  0inf <* [1]^^a0 <* [1] <| [1;0;0]^^a *> 0inf.

Lemma BigStep a0 a n:
  a+3<=n<=a*2+3 ->
  P a ->
  S (a0,n) -->+
  S (2+a0,a*4+8-n).
Proof.
  intros Ha HP.
  remember (a*4+4-n) as v1.
  replace (a*4+8-n) with (4+v1) by lia.
  unfold S.
  epose proof (P' _ HP) as HP'.
  remember (n-a-3) as b.
  replace n with (2+a+(1+b)) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP'.
  mid10 (S0 (0inf<*[1]^^(5+a0)) a 1 (b+0) 0inf).
  1: es.
  replace a with (b+(a-b)) by lia.
  follow Incs0.
  follow Incs1.
  replace ((a-b)*3+(b*2+1)) with v1 by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(O,3)).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(a0,n) => exists a, a+3<=n<=a*2+3 /\ P a).
  2: exists O; split; [lia|]; unfold P; es.
  intros [a0 n] [a [Ha HP]].
  eexists; split.
  1: eapply BigStep; eassumption.
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RF_1LD0RB_1LA---_1LB0LD_1RA1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c r :=
  0inf <* <[1;0;1]^^a <* <[0;1;1]^^b {{B}}> [0;0;1]^^c *> r.

Lemma Inc0 a b c r:
  S0 (2+a) b (1+c) r -->*
  S0 a (3+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n a b c r:
  S0 (n*2+a) b (n+c) r -->*
  S0 a (n*3+b) c r.
Proof.
  gen a b c r.
  ind n Inc0.
Qed.

Lemma Inc1 a b:
  S0 (1+a) b 0 0inf -->*
  S0 a (2+b) 0 0inf.
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S0 a b 0 0inf -->*
  S0 0 (a*2+b) 0 0inf.
Proof.
  gen b.
  ind a Inc1.
Qed.

Notation "l <| r" := (l <{{E}} [0;1] *> r) (at level 30).

Definition P n :=
  forall r,
  0inf <| [0;0;1]^^(1+n) *> r -->*
  0inf <* <[1;0;1]^^n <* <[1;0;0] {{B}}> r.

Lemma P_S_1 n:
  P (n*2+1) ->
  P (n*3+5).
Proof.
  unfold P.
  intros HP r.
  mid (0inf <| [0;0;1]^^(1+(n*2+1)) *> [0;0;1]^^(n+4) *> r).
  1: replace (n*3) with (n*2+n) by lia; es.
  follow HP.
  mid (S0 (n*2+1) 2 (n+3) r).
  1: es.
  follow Incs0.
  mid (0inf <| [0;0;1]^^(n*3+4) *> [1;1;0;0;1] *> r).
  1: es.
  mid (0inf <| [0;0;1]^^(1+(n*2+1)) *> [0;0;1]^^(n+2) *> [1;1;0;0;1] *> r).
  1: replace (n*3) with (n*2+n) by lia; es.
  follow HP.
  mid (S0 (n*2+1) 2 (n+1) ([1;1;0;0;1]*>r)).
  1: es.
  follow Incs0.
  es.
Qed.

Lemma P_S_0 n:
  P (n*2) ->
  P (n*3+3).
Proof.
  unfold P.
  intros HP r.
  mid (0inf <| [0;0;1]^^(1+(n*2)) *> [0;0;1]^^(n+3) *> r).
  1: replace (n*3) with (n*2+n) by lia; es.
  follow HP.
  mid (S0 (n*2+0) 2 (n+2) r).
  1: es.
  follow Incs0.
  mid (0inf <| [0;0;1]^^(n*3+2) *> [0;0;0;0;1] *> r).
  1: es.
  mid (0inf <| [0;0;1]^^(1+(n*2)) *> [0;0;1]^^(n+1) *> [0;0;0;0;1] *> r).
  1: replace (n*3) with (n*2+n) by lia; es.
  follow HP.
  mid (S0 (n*2+0) 2 (n+0) ([0;0;0;0;1]*>r)).
  1: es.
  follow Incs0.
  es.
Qed.

Lemma P_S n:
  P n ->
  P (n+n/2+(n mod 2)+3).
Proof.
  intros HP.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  replace n with (n1*2+n2) in * by lia.
  destruct n2 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r in HP.
    apply P_S_0 in HP.
    applys_eq HP; lia.
  - apply P_S_1 in HP.
    applys_eq HP; lia.
Qed.

Definition S2 n := 0inf <| [0;0;1]^^n *> [1] *> 0inf.

Lemma BigStep a n:
  a+2<=n /\ n*2<=a*3+4 ->
  P a ->
  S2 n -->+
  S2 (a*3+6-n).
Proof.
  unfold P,S2.
  intros Hn HP.
  remember (a*3+6-n) as v2.
  replace n with ((1+a)+(1+(n-a-2))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid10 (S0 a 2 (n-a-2) ([1]*>0inf)).
  1: es.
  remember (n-a-2) as b.
  mid (S0 (b*2+(a-b*2)) 2 (b+0) ([1]*>0inf)).
  1: finish.
  follow Incs0.
  mid (S0 (a-b*2) (b*3+3) 0 0inf).
  1: es.
  follow Incs1.
  unfold S0.
  remember (((a - b * 2) * 2 + (b * 3 + 3))) as v1.
  mid (S2 (1+v1)).
  1: es.
  unfold S2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S2 7).
  1: unfold S2; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a, (a+2<=n /\ n<=a+a/2+1) /\ P a).
  2: exists 5; split; [lia|]; unfold P; es.
  intros n [a [Ha HP]].
  eexists; split.
  1: eapply (BigStep a); [lia|apply HP].
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB1RB_1RC0LF_0RD0RA_0LE0RC_1LB---_1LC0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c r :=
  0inf <* <[1;0;1]^^a <* <[0;1;1]^^b {{C}}> [0;0;1]^^c *> r.

Lemma Inc0 a b c r:
  S0 (2+a) b (1+c) r -->*
  S0 a (3+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n a b c r:
  S0 (n*2+a) b (n+c) r -->*
  S0 a (n*3+b) c r.
Proof.
  gen a b c r.
  ind n Inc0.
Qed.

Lemma Inc1 a b:
  S0 (1+a) b 0 0inf -->*
  S0 a (2+b) 0 0inf.
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S0 a b 0 0inf -->*
  S0 0 (a*2+b) 0 0inf.
Proof.
  gen b.
  ind a Inc1.
Qed.

Notation "l <| r" := (l <{{F}} [0;1] *> r) (at level 30).

Definition P n :=
  forall r,
  0inf <| [0;0;1]^^(1+n) *> r -->*
  0inf <* <[1;0;1]^^n <* <[1;0;0] {{C}}> r.

Lemma P_S_1 n:
  P (n*2+1) ->
  P (n*3+4).
Proof.
  unfold P.
  intros HP r.
  mid (0inf <| [0;0;1]^^(1+(n*2+1)) *> [0;0;1]^^(n+3) *> r).
  1: replace (n*3) with (n*2+n) by lia; es.
  follow HP.
  mid (S0 (n*2+1) 2 (n+2) r).
  1: es.
  follow Incs0.
  mid (0inf <| [0;0;1]^^(n*3+4) *> [0;1] *> r).
  1: es.
  mid (0inf <| [0;0;1]^^(1+(n*2+1)) *> [0;0;1]^^(n+2) *> [0;1] *> r).
  1: replace (n*3) with (n*2+n) by lia; es.
  follow HP.
  mid (S0 (n*2+1) 2 (n+1) ([0;1]*>r)).
  1: es.
  follow Incs0.
  es.
Qed.

Lemma P_S_0 n:
  P (n*2) ->
  P (n*3+3).
Proof.
  unfold P.
  intros HP r.
  mid (0inf <| [0;0;1]^^(1+(n*2)) *> [0;0;1]^^(n+3) *> r).
  1: replace (n*3) with (n*2+n) by lia; es.
  follow HP.
  mid (S0 (n*2+0) 2 (n+2) r).
  1: es.
  follow Incs0.
  mid (0inf <| [0;0;1]^^(n*3+2) *> [0;0;0;0;1] *> r).
  1: es.
  mid (0inf <| [0;0;1]^^(1+(n*2)) *> [0;0;1]^^(n+1) *> [0;0;0;0;1] *> r).
  1: replace (n*3) with (n*2+n) by lia; es.
  follow HP.
  mid (S0 (n*2+0) 2 (n+0) ([0;0;0;0;1]*>r)).
  1: es.
  follow Incs0.
  es.
Qed.

Lemma P_S n:
  P n ->
  P (n+n/2+3).
Proof.
  intros HP.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  replace n with (n1*2+n2) in * by lia.
  destruct n2 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r in HP.
    apply P_S_0 in HP.
    applys_eq HP; lia.
  - apply P_S_1 in HP.
    applys_eq HP; lia.
Qed.

Definition S2 n := 0inf <| [0;0;1]^^n *> 0inf.

Lemma BigStep a n:
  a+2<=n /\ n*2<=a*3+4 ->
  P a ->
  S2 n -->+
  S2 (a*3+5-n).
Proof.
  unfold P,S2.
  intros Hn HP.
  remember (a*3+5-n) as v2.
  replace n with ((1+a)+(1+(n-a-2))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid10 (S0 a 2 (n-a-2) (0inf)).
  1: es.
  remember (n-a-2) as b.
  mid (S0 (b*2+(a-b*2)) 2 (b+0) (0inf)).
  1: finish.
  follow Incs0.
  mid (S0 (a-b*2) (b*3+2) 0 0inf).
  1: es.
  follow Incs1.
  remember (((a - b * 2) * 2 + (b * 3 + 2))) as v1.
  replace v2 with (1+v1) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S2 6).
  1: unfold S2; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a, (a+2<=n /\ n<=a+a/2) /\ P a).
  2: exists 4; split; [lia|]; unfold P; es.
  intros n [a [Ha HP]].
  eexists; split.
  1: eapply (BigStep a); [lia|apply HP].
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1LB0RF_0RC1LE_---0RD_1RA1RA_1RD0LA_1RD1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c r :=
  0inf <* <[1;1;0]^^a <* <[1;1] <* <[1;1;0]^^b <* <[1;1] {{A}}> [0;1;1]^^c *> r.

Lemma Inc0 a b c r:
  S0 (1+a) b (1+c) r -->*
  S0 a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n a b c r:
  S0 (n+a) b (n+c) r -->*
  S0 a (n*2+b) c r.
Proof.
  gen a b c r.
  ind n Inc0.
Qed.

Lemma Inc1 a b:
  S0 (1+a) b 0 0inf -->*
  S0 a (3+b) 0 0inf.
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S0 a b 0 0inf -->*
  S0 0 (a*3+b) 0 0inf.
Proof.
  gen b.
  ind a Inc1.
Qed.

Notation "l <| r" := (l <{{B}} [1] *> r) (at level 30).

Definition P n :=
  forall r,
  0inf <| [0;1;1]^^(4+n) *> r -->*
  S0 n 2 0 r.

Lemma P_S n:
  P n ->
  P (n*2+4).
Proof.
  unfold P.
  intros HP r.
  mid (0inf <| [0;1;1]^^(4+n) *> [0;1;1]^^(4+n) *> r).
  1: replace (n*2) with (n+n) by lia; es.
  follow HP.
  mid (S0 (n+0) 2 (n+4) r).
  1: es.
  follow Incs0.
  mid (0inf <| [0;1;1]^^(n*2+5) *> [1;1;0;1;1;0;1;1] *> r).
  1: es.
  mid (0inf <| [0;1;1]^^(4+n) *> [0;1;1]^^(1+n) *> [1;1;0;1;1;0;1;1] *> r).
  1: replace (n*2) with (n+n) by lia; es.
  follow HP.
  mid (S0 (n+0) 2 (n+1) ([1;1;0;1;1;0;1;1]*>r)).
  1: es.
  follow Incs0.
  es.
Qed.

Definition S2 n := 0inf <| [0;1;1]^^n *> 0inf.

Lemma BigStep a n:
  a+4<=n<=a*2+4 ->
  P a ->
  S2 n -->+
  S2 (a*4+10-n).
Proof.
  unfold P,S2.
  intros Hn HP.
  remember (a*3+6-n) as v2.
  replace n with ((4+a)+((n-a-4))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid01 (S0 a 2 (n-a-4) 0inf).
  1: es.
  remember (n-a-4) as b.
  mid01 (S0 (b+(a-b)) 2 (b+0) 0inf).
  1: finish.
  follow Incs0.
  follow Incs1.
  remember (((a - b) * 3 + (b * 2 + 2))) as v1.
  unfold S0.
  mid10 (S2 (4+v1)).
  1: es.
  unfold S2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S2 13).
  1: unfold S2; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a, (a+4<=n<=a*2+2) /\ P a).
  2: exists 8; split; [lia|]; apply (P_S 2); unfold P; es.
  intros n [a [Ha HP]].
  eexists; split.
  1: eapply (BigStep a); [lia|apply HP].
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1LF_0RA0LB_0RE0RF_1RC0LB_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c r :=
  0inf <* <[0;1]^^a <* [1] <* <[0;1]^^b {{D}}> [0;1]^^c *> r.

Lemma Inc0 a b c r:
  S0 (1+a) b (1+c) r -->*
  S0 a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs0 n a b c r:
  S0 (n+a) b (n+c) r -->*
  S0 a (n*2+b) c r.
Proof.
  gen a b c r.
  ind n Inc0.
Qed.

Lemma Inc1 a b:
  S0 (1+a) b 0 0inf -->*
  S0 a (4+b) 0 0inf.
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S0 a b 0 0inf -->*
  S0 0 (a*4+b) 0 0inf.
Proof.
  gen b.
  ind a Inc1.
Qed.

Notation "l <| r" := (l <{{C}} [1] *> r) (at level 30).

Definition P n :=
  forall r,
  0inf <| [0;1]^^(2+n) *> r -->*
  S0 n 1 0 r.

Lemma P_S n:
  P n ->
  P (n*2+2).
Proof.
  unfold P.
  intros HP r.
  mid (0inf <| [0;1]^^(2+n) *> [0;1]^^(2+n) *> r).
  1: replace (n*2) with (n+n) by lia; es.
  follow HP.
  mid (S0 (n+0) 1 (n+2) r).
  1: es.
  follow Incs0.
  mid (0inf <| [0;1]^^(n*2+2) *> [0;0;1] *> r).
  1: es.
  mid (0inf <| [0;1]^^(2+n) *> [0;1]^^(n) *> [0;0;1] *> r).
  1: replace (n*2) with (n+n) by lia; es.
  follow HP.
  mid (S0 (n+0) 1 (n+0) ([0;0;1]*>r)).
  1: es.
  follow Incs0.
  es.
Qed.

Definition S2 n := 0inf <| [0;1]^^n *> 0inf.

Lemma BigStep a n:
  a+2<=n<=a*2+2 ->
  P a ->
  S2 n -->+
  S2 (a*6+8-n*2).
Proof.
  unfold P,S2.
  intros Hn HP.
  replace n with ((2+a)+((n-a-2))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid01 (S0 a 1 (n-a-2) 0inf).
  1: es.
  remember (n-a-2) as b.
  mid01 (S0 (b+(a-b)) 1 (b+0) 0inf).
  1: finish.
  follow Incs0.
  follow Incs1.
  remember (((a - b) * 4 + (b * 2 + 1))) as v1.
  mid10 (S2 (3+v1)).
  1: es.
  unfold S2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S2 12).
  1: unfold S2; esx.
  eapply progress_nonhalt_cond with (P:=fun n => exists a, (a+2<=n<=a*2+2) /\ P a).
  2: exists 6; split; [lia|]; apply (P_S 2); unfold P; es.
  intros n [a [Ha HP]].
  eexists; split.
  1: eapply (BigStep a); [lia|apply HP].
  eexists; split.
  2: apply P_S,HP.
  lia.
Qed.

End TM11.


