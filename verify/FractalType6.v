From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import SimplTape.

Open Scope list.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0LC0RA_0LE1LD_0RD0LE_1RA0RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} r) (at level 30).
Notation "l |> r" := (l <* [1] {{A}}> r) (at level 30).


Definition S1 l a b c d :=
  l <* <[1;0]^^a <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b c (1+d) -->*
  S1 l a (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S1_Incs l a b c d:
  S1 l a b c (a+d) -->*
  S1 l 0 (a+b) (a+c) d.
Proof.
  gen b c d.
  ind a S1_Inc.
Qed.

Definition S2 b c d :=
  0inf <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S2_Inc b c d:
  S2 b c (1+d) -->*
  S2 (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S2_Incs b c d:
  S2 b c d -->*
  S2 (d+b) (d+c) 0.
Proof.
  gen b c.
  ind d S2_Inc.
Qed.

Definition P b :=
  forall l,
  l <* <[1;0]^^(1+b) |> 0inf -->*
  S1 l 0 (1+b) b 1.

Lemma P_S n:
  P n ->
  P (n+n+3).
Proof.
  unfold P.
  intros HP l.
  mid (l <* <[1;0]^^(3+n) <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (l <* <[1;0]^^(1+n) <* <[1;1] <* <[1;0]^^(3+n) <* [0] <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (S1 l (1+n) (3+n) (2+n) ((1+n)+1)).
  1: es.
  follow S1_Incs.
  finish.
Qed.

Definition S0 n :=
  0inf <* <[1] <* <[1;0]^^(3+n) <* <[0] <* <[1;0]^^(1+n) |> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P,S1; es.
  intros n HP.
  eexists. split.
  2: apply P_S,HP.
  unfold S0,P in *.
  follow HP.
  fold_tape.
  mid10 (S2 (3+n) (2+n) (2+n)). 
  1: es.
  follow S2_Incs.
  es.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0LC0RA_0LE1LD_0LE0RC_1RA0RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} r) (at level 30).
Notation "l |> r" := (l <* [1] {{A}}> r) (at level 30).


Definition S1 l a b c d :=
  l <* <[1;0]^^a <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b c (1+d) -->*
  S1 l a (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S1_Incs l a b c d:
  S1 l a b c (a+d) -->*
  S1 l 0 (a+b) (a+c) d.
Proof.
  gen b c d.
  ind a S1_Inc.
Qed.

Definition S2 b c d :=
  0inf <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S2_Inc b c d:
  S2 b c (1+d) -->*
  S2 (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S2_Incs b c d:
  S2 b c d -->*
  S2 (d+b) (d+c) 0.
Proof.
  gen b c.
  ind d S2_Inc.
Qed.

Definition P b :=
  forall l,
  l <* <[1;0]^^(1+b) |> 0inf -->*
  S1 l 0 (1+b) b 1.

Lemma P_S n:
  P n ->
  P (n+n+3).
Proof.
  unfold P.
  intros HP l.
  mid (l <* <[1;0]^^(3+n) <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (l <* <[1;0]^^(1+n) <* <[1;1] <* <[1;0]^^(3+n) <* [0] <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (S1 l (1+n) (3+n) (2+n) ((1+n)+1)).
  1: es.
  follow S1_Incs.
  finish.
Qed.

Definition S0 n :=
  0inf <* <[1] <* <[1;0]^^(3+n) <* <[0] <* <[1;0]^^(1+n) |> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P,S1; es.
  intros n HP.
  eexists. split.
  2: apply P_S,HP.
  unfold S0,P in *.
  follow HP.
  fold_tape.
  mid10 (S2 (3+n) (2+n) (2+n)). 
  1: es.
  follow S2_Incs.
  es.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC0RA_0LD0RB_0LA1LE_0LA0LA_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} r) (at level 30).
Notation "l |> r" := (l <* [1] {{B}}> r) (at level 30).


Definition S1 l a b c d :=
  l <* <[1;0]^^a <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b c (1+d) -->*
  S1 l a (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S1_Incs l a b c d:
  S1 l a b c (a+d) -->*
  S1 l 0 (a+b) (a+c) d.
Proof.
  gen b c d.
  ind a S1_Inc.
Qed.

Definition S2 b c d :=
  0inf <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S2_Inc b c d:
  S2 b c (1+d) -->*
  S2 (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S2_Incs b c d:
  S2 b c d -->*
  S2 (d+b) (d+c) 0.
Proof.
  gen b c.
  ind d S2_Inc.
Qed.

Definition P b :=
  forall l,
  l <* <[1;0]^^(1+b) |> 0inf -->*
  S1 l 0 (1+b) b 1.

Lemma P_S n:
  P n ->
  P (n+n+3).
Proof.
  unfold P.
  intros HP l.
  mid (l <* <[1;0]^^(3+n) <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (l <* <[1;0]^^(1+n) <* <[1;1] <* <[1;0]^^(3+n) <* [0] <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (S1 l (1+n) (3+n) (2+n) ((1+n)+1)).
  1: es.
  follow S1_Incs.
  finish.
Qed.

Definition S0 n :=
  0inf <* <[1] <* <[1;0]^^(3+n) <* <[0] <* <[1;0]^^(1+n) |> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P,S1; es.
  intros n HP.
  eexists. split.
  2: apply P_S,HP.
  unfold S0,P in *.
  follow HP.
  fold_tape.
  mid10 (S2 (3+n) (2+n) (2+n)). 
  1: es.
  follow S2_Incs.
  es.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB---_0LC0RE_0LD1LF_1RE0RA_1RB0RD_1RC0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} r) (at level 30).
Notation "l |> r" := (l <* [1] {{E}}> r) (at level 30).


Definition S1 l a b c d :=
  l <* <[1;0]^^a <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b c (1+d) -->*
  S1 l a (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S1_Incs l a b c d:
  S1 l a b c (a+d) -->*
  S1 l 0 (a+b) (a+c) d.
Proof.
  gen b c d.
  ind a S1_Inc.
Qed.

Definition S2 b c d :=
  0inf <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S2_Inc b c d:
  S2 b c (1+d) -->*
  S2 (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S2_Incs b c d:
  S2 b c d -->*
  S2 (d+b) (d+c) 0.
Proof.
  gen b c.
  ind d S2_Inc.
Qed.

Definition P b :=
  forall l,
  l <* <[1;0]^^(1+b) |> 0inf -->*
  S1 l 0 (1+b) b 1.

Lemma P_S n:
  P n ->
  P (n+n+3).
Proof.
  unfold P.
  intros HP l.
  mid (l <* <[1;0]^^(3+n) <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (l <* <[1;0]^^(1+n) <* <[1;1] <* <[1;0]^^(3+n) <* [0] <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (S1 l (1+n) (3+n) (2+n) ((1+n)+1)).
  1: es.
  follow S1_Incs.
  finish.
Qed.

Definition S0 n :=
  0inf <* <[1] <* <[1;0]^^(4+n) <* <[0] <* <[1;0]^^(1+n) |> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P,S1; es.
  intros n HP.
  eexists. split.
  2: apply P_S,HP.
  unfold S0,P in *.
  follow HP.
  fold_tape.
  mid10 (S2 (4+n) (2+n) (2+n)). 
  1: es.
  follow S2_Incs.
  es.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB---_0LC0RE_0LD1LF_1RE0RA_1RB0RD_0LD0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} r) (at level 30).
Notation "l |> r" := (l <* [1] {{E}}> r) (at level 30).


Definition S1 l a b c d :=
  l <* <[1;0]^^a <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b c (1+d) -->*
  S1 l a (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S1_Incs l a b c d:
  S1 l a b c (a+d) -->*
  S1 l 0 (a+b) (a+c) d.
Proof.
  gen b c d.
  ind a S1_Inc.
Qed.

Definition S2 b c d :=
  0inf <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S2_Inc b c d:
  S2 b c (1+d) -->*
  S2 (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S2_Incs b c d:
  S2 b c d -->*
  S2 (d+b) (d+c) 0.
Proof.
  gen b c.
  ind d S2_Inc.
Qed.

Definition P b :=
  forall l,
  l <* <[1;0]^^(1+b) |> 0inf -->*
  S1 l 0 (1+b) b 1.

Lemma P_S n:
  P n ->
  P (n+n+3).
Proof.
  unfold P.
  intros HP l.
  mid (l <* <[1;0]^^(3+n) <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (l <* <[1;0]^^(1+n) <* <[1;1] <* <[1;0]^^(3+n) <* [0] <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (S1 l (1+n) (3+n) (2+n) ((1+n)+1)).
  1: es.
  follow S1_Incs.
  finish.
Qed.

Definition S0 n :=
  0inf <* <[1] <* <[1;0]^^(4+n) <* <[0] <* <[1;0]^^(1+n) |> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P,S1; es.
  intros n HP.
  eexists. split.
  2: apply P_S,HP.
  unfold S0,P in *.
  follow HP.
  fold_tape.
  mid10 (S2 (4+n) (2+n) (2+n)). 
  1: es.
  follow S2_Incs.
  es.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB---_0LC0RE_0LD1LF_1RE0RA_1RB0RD_0LD0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} r) (at level 30).
Notation "l |> r" := (l <* [1] {{E}}> r) (at level 30).


Definition S1 l a b c d :=
  l <* <[1;0]^^a <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b c (1+d) -->*
  S1 l a (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S1_Incs l a b c d:
  S1 l a b c (a+d) -->*
  S1 l 0 (a+b) (a+c) d.
Proof.
  gen b c d.
  ind a S1_Inc.
Qed.

Definition S2 b c d :=
  0inf <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S2_Inc b c d:
  S2 b c (1+d) -->*
  S2 (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S2_Incs b c d:
  S2 b c d -->*
  S2 (d+b) (d+c) 0.
Proof.
  gen b c.
  ind d S2_Inc.
Qed.

Definition P b :=
  forall l,
  l <* <[1;0]^^(1+b) |> 0inf -->*
  S1 l 0 (1+b) b 1.

Lemma P_S n:
  P n ->
  P (n+n+3).
Proof.
  unfold P.
  intros HP l.
  mid (l <* <[1;0]^^(3+n) <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (l <* <[1;0]^^(1+n) <* <[1;1] <* <[1;0]^^(3+n) <* [0] <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (S1 l (1+n) (3+n) (2+n) ((1+n)+1)).
  1: es.
  follow S1_Incs.
  finish.
Qed.

Definition S0 n :=
  0inf <* <[1] <* <[1;0]^^(4+n) <* <[0] <* <[1;0]^^(1+n) |> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P,S1; es.
  intros n HP.
  eexists. split.
  2: apply P_S,HP.
  unfold S0,P in *.
  follow HP.
  fold_tape.
  mid10 (S2 (4+n) (2+n) (2+n)). 
  1: es.
  follow S2_Incs.
  es.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB---_0LC0RE_0LD1LF_1RE0RA_1RB0RD_0RF0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} r) (at level 30).
Notation "l |> r" := (l <* [1] {{E}}> r) (at level 30).


Definition S1 l a b c d :=
  l <* <[1;0]^^a <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b c (1+d) -->*
  S1 l a (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S1_Incs l a b c d:
  S1 l a b c (a+d) -->*
  S1 l 0 (a+b) (a+c) d.
Proof.
  gen b c d.
  ind a S1_Inc.
Qed.

Definition S2 b c d :=
  0inf <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S2_Inc b c d:
  S2 b c (1+d) -->*
  S2 (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S2_Incs b c d:
  S2 b c d -->*
  S2 (d+b) (d+c) 0.
Proof.
  gen b c.
  ind d S2_Inc.
Qed.

Definition P b :=
  forall l,
  l <* <[1;0]^^(1+b) |> 0inf -->*
  S1 l 0 (1+b) b 1.

Lemma P_S n:
  P n ->
  P (n+n+3).
Proof.
  unfold P.
  intros HP l.
  mid (l <* <[1;0]^^(3+n) <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (l <* <[1;0]^^(1+n) <* <[1;1] <* <[1;0]^^(3+n) <* [0] <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (S1 l (1+n) (3+n) (2+n) ((1+n)+1)).
  1: es.
  follow S1_Incs.
  finish.
Qed.

Definition S0 n :=
  0inf <* <[1] <* <[1;0]^^(4+n) <* <[0] <* <[1;0]^^(1+n) |> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P,S1; es.
  intros n HP.
  eexists. split.
  2: apply P_S,HP.
  unfold S0,P in *.
  follow HP.
  fold_tape.
  mid10 (S2 (4+n) (2+n) (2+n)). 
  1: es.
  follow S2_Incs.
  es.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0LC0RA_0LE1LD_1RC0LE_1RA0RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} r) (at level 30).
Notation "l |> r" := (l <* [1] {{A}}> r) (at level 30).


Definition S1 l a b c d :=
  l <* <[1;0]^^a <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S1_Inc l a b c d:
  S1 l (1+a) b c (1+d) -->*
  S1 l a (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S1_Incs l a b c d:
  S1 l a b c (a+d) -->*
  S1 l 0 (a+b) (a+c) d.
Proof.
  gen b c d.
  ind a S1_Inc.
Qed.

Definition S2 b c d :=
  0inf <| [0;1]^^(1+b) *> [1] *> [0;1]^^c *> [1;0]^^d *> 0inf.

Lemma S2_Inc b c d:
  S2 b c (1+d) -->*
  S2 (1+b) (1+c) d.
Proof.
  es.
Qed.

Lemma S2_Incs b c d:
  S2 b c d -->*
  S2 (d+b) (d+c) 0.
Proof.
  gen b c.
  ind d S2_Inc.
Qed.

Definition P b :=
  forall l,
  l <* <[1;0]^^(1+b) |> 0inf -->*
  S1 l 0 (1+b) b 1.

Lemma P_S n:
  P n ->
  P (n+n+3).
Proof.
  unfold P.
  intros HP l.
  mid (l <* <[1;0]^^(3+n) <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (l <* <[1;0]^^(1+n) <* <[1;1] <* <[1;0]^^(3+n) <* [0] <* <[1;0]^^(1+n) |> 0inf).
  1: es.
  follow HP.
  mid (S1 l (1+n) (3+n) (2+n) ((1+n)+1)).
  1: es.
  follow S1_Incs.
  finish.
Qed.

Definition S0 n :=
  0inf <* <[1] <* <[1;0]^^(3+n) <* <[0] <* <[1;0]^^(1+n) |> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P,S1; es.
  intros n HP.
  eexists. split.
  2: apply P_S,HP.
  unfold S0,P in *.
  follow HP.
  fold_tape.
  mid10 (S2 (3+n) (2+n) (2+n)). 
  1: es.
  follow S2_Incs.
  es.
Qed.

End TM8.


