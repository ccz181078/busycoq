From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import SimplTape.
From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.
Ltac flia := repeat (lia || f_equal).

Open Scope list.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LC---_1LA1RD_1LF1RE_0RD1LC_0LA0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{D}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1] <* <[1;0]^^(n*3+4) <* [1]^^(n*3+2) |> 0inf.

Lemma BigStep n:
  P (n*3+2) ->
  S n -->+
  S (n*4+4).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold P,S in *.
  follow HP.
  mid01 (S2 0 (n*3+n*3+6) 0).
  1: es.
  mid01 (S2 0 ((n*2+2)*3+0) 0).
  1: finish.
  follow S2_Incs.
  mid10 (0inf <* <[1;1;1;0;1;0] <* <[1;0]^^((n*3+2)*2+2) <* [1]^^((n*3+2)*2+2) |> 0inf).
  1: es.
  follow HP0.
  mid (S2 1 (13+n*6+n*6) 1).
  1: es.
  mid (S2 1 ((n*4+4)*3+1) 1).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  repeat (er; sr).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+2)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC---_1LF1RD_0RC1LE_1LA1RC_0LA0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{C}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1] <* <[1;0]^^(n*3+4) <* [1]^^(n*3+2) |> 0inf.

Lemma BigStep n:
  P (n*3+2) ->
  S n -->+
  S (n*4+4).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold P,S in *.
  follow HP.
  mid01 (S2 0 (n*3+n*3+6) 0).
  1: es.
  mid01 (S2 0 ((n*2+2)*3+0) 0).
  1: finish.
  follow S2_Incs.
  mid10 (0inf <* <[1;1;1;0;1;0] <* <[1;0]^^((n*3+2)*2+2) <* [1]^^((n*3+2)*2+2) |> 0inf).
  1: es.
  follow HP0.
  mid (S2 1 (13+n*6+n*6) 1).
  1: es.
  mid (S2 1 ((n*4+4)*3+1) 1).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  repeat (er; sr).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+2)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC---_0RD1LF_1LE1RC_0LA0LD_1LA1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{D}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1] <* <[1;0]^^(n*3+4) <* [1]^^(n*3+2) |> 0inf.

Lemma BigStep n:
  P (n*3+2) ->
  S n -->+
  S (n*4+4).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold P,S in *.
  follow HP.
  mid01 (S2 0 (n*3+n*3+6) 0).
  1: es.
  mid01 (S2 0 ((n*2+2)*3+0) 0).
  1: finish.
  follow S2_Incs.
  mid10 (0inf <* <[1;1;1;0;1;0] <* <[1;0]^^((n*3+2)*2+2) <* [1]^^((n*3+2)*2+2) |> 0inf).
  1: es.
  follow HP0.
  mid (S2 1 (13+n*6+n*6) 1).
  1: es.
  mid (S2 1 ((n*4+4)*3+1) 1).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  repeat (er; sr).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+2)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LC---_1LA1RD_1LF1RE_0RD1RE_0LA0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{D}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1] <* <[1;0]^^(n*3+4) <* [1]^^(n*3+2) |> 0inf.

Lemma BigStep n:
  P (n*3+2) ->
  S n -->+
  S (n*4+4).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold P,S in *.
  follow HP.
  mid01 (S2 0 (n*3+n*3+6) 0).
  1: es.
  mid01 (S2 0 ((n*2+2)*3+0) 0).
  1: finish.
  follow S2_Incs.
  mid10 (0inf <* <[1;1;1;0;1;0] <* <[1;0]^^((n*3+2)*2+2) <* [1]^^((n*3+2)*2+2) |> 0inf).
  1: es.
  follow HP0.
  mid (S2 1 (13+n*6+n*6) 1).
  1: es.
  mid (S2 1 ((n*4+4)*3+1) 1).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  repeat (er; sr).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+2)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC---_0RD1RC_1LE1RC_0LA0LD_1LA1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{D}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1] <* <[1;0]^^(n*3+4) <* [1]^^(n*3+2) |> 0inf.

Lemma BigStep n:
  P (n*3+2) ->
  S n -->+
  S (n*4+4).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold P,S in *.
  follow HP.
  mid01 (S2 0 (n*3+n*3+6) 0).
  1: es.
  mid01 (S2 0 ((n*2+2)*3+0) 0).
  1: finish.
  follow S2_Incs.
  mid10 (0inf <* <[1;1;1;0;1;0] <* <[1;0]^^((n*3+2)*2+2) <* [1]^^((n*3+2)*2+2) |> 0inf).
  1: es.
  follow HP0.
  mid (S2 1 (13+n*6+n*6) 1).
  1: es.
  mid (S2 1 ((n*4+4)*3+1) 1).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  repeat (er; sr).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+2)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC---_1LE1RD_0RC1RD_0LA0LC_1LA1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{C}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1] <* <[1;0]^^(n*3+4) <* [1]^^(n*3+2) |> 0inf.

Lemma BigStep n:
  P (n*3+2) ->
  S n -->+
  S (n*4+4).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold P,S in *.
  follow HP.
  mid01 (S2 0 (n*3+n*3+6) 0).
  1: es.
  mid01 (S2 0 ((n*2+2)*3+0) 0).
  1: finish.
  follow S2_Incs.
  mid10 (0inf <* <[1;1;1;0;1;0] <* <[1;0]^^((n*3+2)*2+2) <* [1]^^((n*3+2)*2+2) |> 0inf).
  1: es.
  follow HP0.
  mid (S2 1 (13+n*6+n*6) 1).
  1: es.
  mid (S2 1 ((n*4+4)*3+1) 1).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  repeat (er; sr).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+2)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC---_0RD1RC_1LE1RC_0LA0LD_1LA1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{D}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1] <* <[1;0]^^(n*3+4) <* [1]^^(n*3+2) |> 0inf.

Lemma BigStep n:
  P (n*3+2) ->
  S n -->+
  S (n*4+4).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold P,S in *.
  follow HP.
  mid01 (S2 0 (n*3+n*3+6) 0).
  1: es.
  mid01 (S2 0 ((n*2+2)*3+0) 0).
  1: finish.
  follow S2_Incs.
  mid10 (0inf <* <[1;1;1;0;1;0] <* <[1;0]^^((n*3+2)*2+2) <* [1]^^((n*3+2)*2+2) |> 0inf).
  1: es.
  follow HP0.
  mid (S2 1 (13+n*6+n*6) 1).
  1: es.
  mid (S2 1 ((n*4+4)*3+1) 1).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  repeat (er; sr).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+2)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RE_0LD0LB_1RA0LF_0RB1RE_1LD1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{B}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S' a:
  P a ->
  0inf <* <[1;0]^^(a*2+3) <* [1]^^(a*2+1) |> 0inf -->*
  0inf <* <[1;1] <* <[1;0]^^(a*4+5) |> 0inf.
Proof.
  unfold P; intros HP.
  replace (a*2+1) with (a+(1+a)) by lia.
  replace (a*4+5) with (5+a+a+a*2) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (0inf<*<[1;0]^^(a*2+3)) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (0inf <* <[1;1] <* <[1;0]^^(5+a+a*2) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S'' a:
  P a ->
  0inf <* <[1;1] <* <[1;0]^^(a*2+3) <* [1]^^(a*2+1) |> 0inf -->*
  0inf <* <[1] <* <[1;0]^^(a*4+5) |> 0inf.
Proof.
  unfold P; intros HP.
  replace (a*2+1) with (a+(1+a)) by lia.
  replace (a*4+5) with (5+a+a+a*2) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (0inf<*<[1;1]<*<[1;0]^^(a*2+3)) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (0inf <* <[1] <* <[1;0]^^(5+a+a*2) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1;0]^^((n*3+2)*2+3) <* [1]^^((n*3+2)*2+1) |> 0inf.

Lemma BigStep n:
  P (n*3+2) ->
  S n -->+
  S (n*4+4).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold P,S in *.
  follow (P_S' _ HP).
  mid10 (S2 1 (n*12+12) 1).
  1: es.
  mid (S2 1 ((n*4+4)*3+0) 1).
  1: finish.
  follow S2_Incs.
  eapply evstep_trans.
  2: follow (P_S'' _ HP0).
  1: es.
  mid (S2 0 (n*24+29) 0).
  1: es.
  mid (S2 0 ((n*8+9)*3+2) 0).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  do 7 (er; sr).
  st; er.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+2)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RE_0LD0LB_1RA0LF_0RB1LF_1LD1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{B}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S' a:
  P a ->
  0inf <* <[1;0]^^(a*2+3) <* [1]^^(a*2+1) |> 0inf -->*
  0inf <* <[1;1] <* <[1;0]^^(a*4+5) |> 0inf.
Proof.
  unfold P; intros HP.
  replace (a*2+1) with (a+(1+a)) by lia.
  replace (a*4+5) with (5+a+a+a*2) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (0inf<*<[1;0]^^(a*2+3)) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (0inf <* <[1;1] <* <[1;0]^^(5+a+a*2) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S'' a:
  P a ->
  0inf <* <[1;1] <* <[1;0]^^(a*2+3) <* [1]^^(a*2+1) |> 0inf -->*
  0inf <* <[1] <* <[1;0]^^(a*4+5) |> 0inf.
Proof.
  unfold P; intros HP.
  replace (a*2+1) with (a+(1+a)) by lia.
  replace (a*4+5) with (5+a+a+a*2) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (0inf<*<[1;1]<*<[1;0]^^(a*2+3)) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (0inf <* <[1] <* <[1;0]^^(5+a+a*2) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1;0]^^((n*3+2)*2+3) <* [1]^^((n*3+2)*2+1) |> 0inf.

Lemma BigStep n:
  P (n*3+2) ->
  S n -->+
  S (n*4+4).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold P,S in *.
  follow (P_S' _ HP).
  mid10 (S2 1 (n*12+12) 1).
  1: es.
  mid (S2 1 ((n*4+4)*3+0) 1).
  1: finish.
  follow S2_Incs.
  eapply evstep_trans.
  2: follow (P_S'' _ HP0).
  1: es.
  mid (S2 0 (n*24+29) 0).
  1: es.
  mid (S2 0 ((n*8+9)*3+2) 0).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  do 7 (er; sr).
  st; er.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+2)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC---_1LA1RD_1LE1RF_0LA0LD_0RD1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{D}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S' a:
  P (a+3) ->
  0inf <* <[1;1;0;1] <* <[1;0]^^(a*2+6) <* [1]^^(a*2+4) |> 0inf -->*
  0inf <* [1] <* <[1;0]^^(a*4+15) |> 0inf.
Proof.
  unfold P; intros HP.
  replace (a*2+4) with ((a+3)+(1+a)) by lia.
  replace (a*4+15) with (15+a+a+a*2) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (0inf<*<[1;1;0;1]<*<[1;0]^^(a*2+6)) (a+0) 0 (a+3) 0).
  1: es.
  follow S1_Incs.
  mid (0inf <* <[1] <* <[1;0]^^(12+a+a*2) <* [1]^^(a+3) |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S'' a:
  P (a+3) ->
  0inf <* <[1;1;0;1] <* <[1;0]^^(a*2+6) <* [1]^^(a*2+5) |> 0inf -->*
  0inf <* <[1;1;0;1] <* <[1;0]^^(a*4+14) |> 0inf.
Proof.
  unfold P; intros HP.
  replace (a*2+5) with ((a+3)+(2+a)) by lia.
  replace (a*4+14) with (14+a+a+a*2) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (0inf<*<[1;1;0;1]<*<[1;0]^^(a*2+6)) (a+1+0) 0 (a+1+2) 0).
  1: es.
  follow S1_Incs.
  mid (0inf <* <[1;1;0;1] <* <[1;0]^^(11+a+a*2) <* [1]^^(a+3) |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;1;0;1] <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1;1;0;1] <* <[1;0]^^(n*6+6) <* [1]^^(n*6+4) |> 0inf.

Lemma BigStep n:
  P (n*3+3) ->
  S n -->+
  S (n*4+5).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold S.
  follow (P_S' _ HP).
  mid10 (S2 0 (n*12+14) 1).
  1: es.
  mid (S2 0 ((n*4+4)*3+2) 1).
  1: finish.
  follow S2_Incs.
  replace ((n*3+3)*2+2) with (n*6+5+3) in HP0 by lia.
  epose proof (P_S'' _ HP0) as HP0'.
  eapply evstep_trans.
  2: follow HP0'.
  1: es.
  mid (S2 2 (n*24+32) 2).
  1: es.
  mid (S2 2 ((n*8+10)*3+2) 2).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  do 7 (er; sr).
  st; er.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 1).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+3)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC---_1LA1RD_1LE1RF_0LA0LD_0RD1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* <[1;0] {{D}}> r) (at level 30).

Definition S1 l a b c d :=
  l <* [1]^^a <* <[1;0]^^b <* [1] <* <[1;0]^^c |> [0] *> [1]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b (1+c) d -->*
  S1 l a (1+b) c (1+d).
Proof.
  es.
Qed.

Lemma S1_Incs n l a b c d:
  S1 l (n+a) b (n+c) d -->*
  S1 l a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n S1_Inc.
Qed.

Definition P a :=
  forall l,
  l <* [1]^^a |> 0inf -->*
  l <* <[1;0]^^a |> 0inf.

Lemma P_S a:
  P a ->
  P (a*2+2).
Proof.
  replace (a*2+2) with (a+(2+a)) by lia.
  unfold P; intros HP l.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (l<*[1]) (a+0) 0 (a+0) 0).
  1: es.
  follow S1_Incs.
  mid (l <* <[1;0]^^(2+a) <* [1]^^a |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S' a:
  P (a+3) ->
  0inf <* <[1;1;0;1] <* <[1;0]^^(a*2+6) <* [1]^^(a*2+4) |> 0inf -->*
  0inf <* [1] <* <[1;0]^^(a*4+15) |> 0inf.
Proof.
  unfold P; intros HP.
  replace (a*2+4) with ((a+3)+(1+a)) by lia.
  replace (a*4+15) with (15+a+a+a*2) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (0inf<*<[1;1;0;1]<*<[1;0]^^(a*2+6)) (a+0) 0 (a+3) 0).
  1: es.
  follow S1_Incs.
  mid (0inf <* <[1] <* <[1;0]^^(12+a+a*2) <* [1]^^(a+3) |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S'' a:
  P (a+3) ->
  0inf <* <[1;1;0;1] <* <[1;0]^^(a*2+6) <* [1]^^(a*2+5) |> 0inf -->*
  0inf <* <[1;1;0;1] <* <[1;0]^^(a*4+14) |> 0inf.
Proof.
  unfold P; intros HP.
  replace (a*2+5) with ((a+3)+(2+a)) by lia.
  replace (a*4+14) with (14+a+a+a*2) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP.
  mid (S1 (0inf<*<[1;1;0;1]<*<[1;0]^^(a*2+6)) (a+1+0) 0 (a+1+2) 0).
  1: es.
  follow S1_Incs.
  mid (0inf <* <[1;1;0;1] <* <[1;0]^^(11+a+a*2) <* [1]^^(a+3) |> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b c :=
  0inf <* <[1;1;0;1] <* <[1;0]^^a <* [1] <* <[1;0]^^b |> [0] *> [1]^^c *> 0inf.

Lemma S2_Inc b c d:
  S2 b (3+c) d -->*
  S2 (3+b) c (3+d).
Proof.
  es.
Qed.

Lemma S2_Incs n b c d:
  S2 b (n*3+c) d -->*
  S2 (n*3+b) c (n*3+d).
Proof.
  gen b c d.
  ind n S2_Inc.
Qed.

Definition S n :=
  0inf <* <[1;1;0;1] <* <[1;0]^^(n*6+6) <* [1]^^(n*6+4) |> 0inf.

Lemma BigStep n:
  P (n*3+3) ->
  S n -->+
  S (n*4+5).
Proof.
  intros HP.
  pose proof (P_S _ HP) as HP0.
  unfold S.
  follow (P_S' _ HP).
  mid10 (S2 0 (n*12+14) 1).
  1: es.
  mid (S2 0 ((n*4+4)*3+2) 1).
  1: finish.
  follow S2_Incs.
  replace ((n*3+3)*2+2) with (n*6+5+3) in HP0 by lia.
  epose proof (P_S'' _ HP0) as HP0'.
  eapply evstep_trans.
  2: follow HP0'.
  1: es.
  mid (S2 2 (n*24+32) 2).
  1: es.
  mid (S2 2 ((n*8+10)*3+2) 2).
  1: finish.
  follow S2_Incs.
  unfold S2,S.
  do 7 (er; sr).
  st; er.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 1).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun n => P (n*3+3)).
  2: unfold P; es.
  intros n HP.
  eexists; split.
  1: apply BigStep,HP.
  applys_eq (P_S _ (P_S _ HP)); flia.
Qed.

End TM11.


