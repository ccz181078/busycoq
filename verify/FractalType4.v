From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC0RD_1RA0LB_1LE1RF_0LE1LC_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c d :=
  l <* <[0;1]^^a <{{E}} [0] *> [0;1;1;0;1;0]^^b *> [1;0]^^c *> [0] *> [1;0;0]^^d *> 0inf.

Lemma Inc1 l a b c d:
  S1 l (2+a) b c (2+d) -->*
  S1 l a (1+b) (2+c) d.
Proof.
  unfold S1.
  es.
Qed.

Lemma Incs1 l a b c d n:
  S1 l (n*2+a) b c (n*2+d) -->*
  S1 l a (n+b) (n*2+c) d.
Proof.
  gen l a b c d.
  ind n Inc1.
Qed.

Definition P a :=
  forall l,
  l <* <[0;1]^^a {{A}}> 0inf -->*
  l <{{B}} [0;1] *> [0;1;0]^^a *> 0inf.

Lemma P_S' b:
  P (2+b*2) ->
  P ((2+b*2)+(5+b*2)).
Proof.
  unfold P.
  intros HP l.
  rewrite (lpow_add _ (2+b*2) (5+b*2)),Str_app_assoc.
  follow HP.
  mid (S1 l (b*2+4) 1 0 (b*2+1)).
  1: es.
  follow Incs1.
  unfold S1.
  mid ([1;0]^^(2+b*2)*>[1;1;0]^^(5+b*2)*>l {{A}}> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S b:
  P (1+b*2) ->
  P ((1+b*2)+(3+b*2)).
Proof.
  unfold P.
  intros HP l.
  rewrite (lpow_add _ (1+b*2) (3+b*2)),Str_app_assoc.
  follow HP.
  mid (S1 l (b*2+2) 1 0 (b*2+0)).
  1: es.
  follow Incs1.
  unfold S1.
  mid ([1;0]^^(1+b*2)*>[1;1;0]^^(3+b*2)*>l {{A}}> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b :=
  0inf <{{C}} [1] *> [0;1]^^a *> [0;1;0]^^b *> 0inf.

Lemma Inc2 a b:
  S2 a (2+b) -->*
  S2 (4+a) b.
Proof.
  unfold S2.
  es.
Qed.

Lemma Incs2 a b n:
  S2 a (n*2+b) -->*
  S2 (n*4+a) b.
Proof.
  gen a b.
  ind n Inc2.
Qed.

Definition S3 a :=
  0inf <* <[0;1]^^a {{A}}> 0inf.

Lemma BigStep1 b:
  P (1+b*2) ->
  S3 (1+b*2) -->+
  S3 (4+b*4).
Proof.
  unfold P,S3.
  intros HP.
  follow HP.
  step1.
  mid (S2 1 (b*2+1)).
  1: es.
  follow Incs2.
  unfold S2.
  es.
Qed.

Lemma BigStep2 b:
  P (2+b*2) ->
  S3 (2+b*2) -->+
  S3 (7+b*4).
Proof.
  unfold P,S3.
  intros HP.
  follow HP.
  step1.
  mid (S2 1 (b*2+2)).
  1: es.
  follow Incs2.
  unfold S2.
  es.
Qed.

Definition S4 a := S3 (1+a*2).
Definition P1 a := P (1+a*2).

Lemma BigStep b:
  P1 b ->
  S4 b -->+
  S4 (5+b*4) /\
  P1 (5+b*4).
Proof.
  unfold S4,P1.
  intros HP.
  epose proof (P_S _ HP) as HP'.
  replace (1+b*2+(3+b*2)) with (2+(1+b*2)*2) in HP' by lia.
  epose proof (P_S' _ HP') as HP''.
  split.
  2: applys_eq HP''; lia.
  follow11 (BigStep1 _ HP).
  replace (4+b*4) with (2+(1+b*2)*2) by lia.
  follow10 (BigStep2 _ HP').
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S4 1).
  1: unfold S4,S3; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1,P; es.
  intros i HP.
  eexists.
  apply BigStep,HP.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC0RE_0LC1LD_1RA0LB_1LC1RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c d :=
  l <* <[0;1]^^a <{{C}} [0] *> [0;1;1;0;1;0]^^b *> [1;0]^^c *> [0] *> [1;0;0]^^d *> 0inf.

Lemma Inc1 l a b c d:
  S1 l (2+a) b c (2+d) -->*
  S1 l a (1+b) (2+c) d.
Proof.
  unfold S1.
  es.
Qed.

Lemma Incs1 l a b c d n:
  S1 l (n*2+a) b c (n*2+d) -->*
  S1 l a (n+b) (n*2+c) d.
Proof.
  gen l a b c d.
  ind n Inc1.
Qed.

Definition P a :=
  forall l,
  l <* <[0;1]^^a {{A}}> 0inf -->*
  l <{{B}} [0;1] *> [0;1;0]^^a *> 0inf.

Lemma P_S' b:
  P (2+b*2) ->
  P ((2+b*2)+(5+b*2)).
Proof.
  unfold P.
  intros HP l.
  rewrite (lpow_add _ (2+b*2) (5+b*2)),Str_app_assoc.
  follow HP.
  mid (S1 l (b*2+4) 1 0 (b*2+1)).
  1: es.
  follow Incs1.
  unfold S1.
  mid ([1;0]^^(2+b*2)*>[1;1;0]^^(5+b*2)*>l {{A}}> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S b:
  P (1+b*2) ->
  P ((1+b*2)+(3+b*2)).
Proof.
  unfold P.
  intros HP l.
  rewrite (lpow_add _ (1+b*2) (3+b*2)),Str_app_assoc.
  follow HP.
  mid (S1 l (b*2+2) 1 0 (b*2+0)).
  1: es.
  follow Incs1.
  unfold S1.
  mid ([1;0]^^(1+b*2)*>[1;1;0]^^(3+b*2)*>l {{A}}> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b :=
  0inf <{{D}} [1] *> [0;1]^^a *> [0;1;0]^^b *> 0inf.

Lemma Inc2 a b:
  S2 a (2+b) -->*
  S2 (4+a) b.
Proof.
  unfold S2.
  es.
Qed.

Lemma Incs2 a b n:
  S2 a (n*2+b) -->*
  S2 (n*4+a) b.
Proof.
  gen a b.
  ind n Inc2.
Qed.

Definition S3 a :=
  0inf <* <[0;1]^^a {{A}}> 0inf.

Lemma BigStep1 b:
  P (1+b*2) ->
  S3 (1+b*2) -->+
  S3 (4+b*4).
Proof.
  unfold P,S3.
  intros HP.
  follow HP.
  step1.
  mid (S2 1 (b*2+1)).
  1: es.
  follow Incs2.
  unfold S2.
  es.
Qed.

Lemma BigStep2 b:
  P (2+b*2) ->
  S3 (2+b*2) -->+
  S3 (7+b*4).
Proof.
  unfold P,S3.
  intros HP.
  follow HP.
  step1.
  mid (S2 1 (b*2+2)).
  1: es.
  follow Incs2.
  unfold S2.
  es.
Qed.

Definition S4 a := S3 (1+a*2).
Definition P1 a := P (1+a*2).

Lemma BigStep b:
  P1 b ->
  S4 b -->+
  S4 (5+b*4) /\
  P1 (5+b*4).
Proof.
  unfold S4,P1.
  intros HP.
  epose proof (P_S _ HP) as HP'.
  replace (1+b*2+(3+b*2)) with (2+(1+b*2)*2) in HP' by lia.
  epose proof (P_S' _ HP') as HP''.
  split.
  2: applys_eq HP''; lia.
  follow11 (BigStep1 _ HP).
  replace (4+b*4) with (2+(1+b*2)*2) by lia.
  follow10 (BigStep2 _ HP').
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S4 1).
  1: unfold S4,S3; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1,P; es.
  intros i HP.
  eexists.
  apply BigStep,HP.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC0RF_0LD---_0LD1LE_1RA0LB_1LC1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c d :=
  l <* <[0;1]^^a <{{D}} [0] *> [0;1;1;0;1;0]^^b *> [1;0]^^c *> [0] *> [1;0;0]^^d *> 0inf.

Lemma Inc1 l a b c d:
  S1 l (2+a) b c (2+d) -->*
  S1 l a (1+b) (2+c) d.
Proof.
  unfold S1.
  es.
Qed.

Lemma Incs1 l a b c d n:
  S1 l (n*2+a) b c (n*2+d) -->*
  S1 l a (n+b) (n*2+c) d.
Proof.
  gen l a b c d.
  ind n Inc1.
Qed.

Definition P a :=
  forall l,
  l <* <[0;1]^^a {{A}}> 0inf -->*
  l <{{B}} [0;1] *> [0;1;0]^^a *> 0inf.

Lemma P_S' b:
  P (2+b*2) ->
  P ((2+b*2)+(5+b*2)).
Proof.
  unfold P.
  intros HP l.
  rewrite (lpow_add _ (2+b*2) (5+b*2)),Str_app_assoc.
  follow HP.
  mid (S1 l (b*2+4) 1 0 (b*2+1)).
  1: es.
  follow Incs1.
  unfold S1.
  mid ([1;0]^^(2+b*2)*>[1;1;0]^^(5+b*2)*>l {{A}}> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S b:
  P (1+b*2) ->
  P ((1+b*2)+(3+b*2)).
Proof.
  unfold P.
  intros HP l.
  rewrite (lpow_add _ (1+b*2) (3+b*2)),Str_app_assoc.
  follow HP.
  mid (S1 l (b*2+2) 1 0 (b*2+0)).
  1: es.
  follow Incs1.
  unfold S1.
  mid ([1;0]^^(1+b*2)*>[1;1;0]^^(3+b*2)*>l {{A}}> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b :=
  0inf <{{E}} [1] *> [0;1]^^a *> [0;1;0]^^b *> 0inf.

Lemma Inc2 a b:
  S2 a (2+b) -->*
  S2 (4+a) b.
Proof.
  unfold S2.
  es.
Qed.

Lemma Incs2 a b n:
  S2 a (n*2+b) -->*
  S2 (n*4+a) b.
Proof.
  gen a b.
  ind n Inc2.
Qed.

Definition S3 a :=
  0inf <* <[0;1]^^a {{A}}> 0inf.

Lemma BigStep1 b:
  P (1+b*2) ->
  S3 (1+b*2) -->+
  S3 (4+b*4).
Proof.
  unfold P,S3.
  intros HP.
  follow HP.
  step1.
  mid (S2 1 (b*2+1)).
  1: es.
  follow Incs2.
  unfold S2.
  es.
Qed.

Lemma BigStep2 b:
  P (2+b*2) ->
  S3 (2+b*2) -->+
  S3 (7+b*4).
Proof.
  unfold P,S3.
  intros HP.
  follow HP.
  step1.
  mid (S2 1 (b*2+2)).
  1: es.
  follow Incs2.
  unfold S2.
  es.
Qed.

Definition S4 a := S3 (1+a*2).
Definition P1 a := P (1+a*2).

Lemma BigStep b:
  P1 b ->
  S4 b -->+
  S4 (5+b*4) /\
  P1 (5+b*4).
Proof.
  unfold S4,P1.
  intros HP.
  epose proof (P_S _ HP) as HP'.
  replace (1+b*2+(3+b*2)) with (2+(1+b*2)*2) in HP' by lia.
  epose proof (P_S' _ HP') as HP''.
  split.
  2: applys_eq HP''; lia.
  follow11 (BigStep1 _ HP).
  replace (4+b*4) with (2+(1+b*2)*2) by lia.
  follow10 (BigStep2 _ HP').
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S4 1).
  1: unfold S4,S3; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1,P; es.
  intros i HP.
  eexists.
  apply BigStep,HP.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC0RF_0LD---_0LD1LE_1RA0LB_1LD1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c d :=
  l <* <[0;1]^^a <{{D}} [0] *> [0;1;1;0;1;0]^^b *> [1;0]^^c *> [0] *> [1;0;0]^^d *> 0inf.

Lemma Inc1 l a b c d:
  S1 l (2+a) b c (2+d) -->*
  S1 l a (1+b) (2+c) d.
Proof.
  unfold S1.
  es.
Qed.

Lemma Incs1 l a b c d n:
  S1 l (n*2+a) b c (n*2+d) -->*
  S1 l a (n+b) (n*2+c) d.
Proof.
  gen l a b c d.
  ind n Inc1.
Qed.

Definition P a :=
  forall l,
  l <* <[0;1]^^a {{A}}> 0inf -->*
  l <{{B}} [0;1] *> [0;1;0]^^a *> 0inf.

Lemma P_S' b:
  P (2+b*2) ->
  P ((2+b*2)+(5+b*2)).
Proof.
  unfold P.
  intros HP l.
  rewrite (lpow_add _ (2+b*2) (5+b*2)),Str_app_assoc.
  follow HP.
  mid (S1 l (b*2+4) 1 0 (b*2+1)).
  1: es.
  follow Incs1.
  unfold S1.
  mid ([1;0]^^(2+b*2)*>[1;1;0]^^(5+b*2)*>l {{A}}> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S b:
  P (1+b*2) ->
  P ((1+b*2)+(3+b*2)).
Proof.
  unfold P.
  intros HP l.
  rewrite (lpow_add _ (1+b*2) (3+b*2)),Str_app_assoc.
  follow HP.
  mid (S1 l (b*2+2) 1 0 (b*2+0)).
  1: es.
  follow Incs1.
  unfold S1.
  mid ([1;0]^^(1+b*2)*>[1;1;0]^^(3+b*2)*>l {{A}}> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b :=
  0inf <{{E}} [1] *> [0;1]^^a *> [0;1;0]^^b *> 0inf.

Lemma Inc2 a b:
  S2 a (2+b) -->*
  S2 (4+a) b.
Proof.
  unfold S2.
  es.
Qed.

Lemma Incs2 a b n:
  S2 a (n*2+b) -->*
  S2 (n*4+a) b.
Proof.
  gen a b.
  ind n Inc2.
Qed.

Definition S3 a :=
  0inf <* <[0;1]^^a {{A}}> 0inf.

Lemma BigStep1 b:
  P (1+b*2) ->
  S3 (1+b*2) -->+
  S3 (4+b*4).
Proof.
  unfold P,S3.
  intros HP.
  follow HP.
  step1.
  mid (S2 1 (b*2+1)).
  1: es.
  follow Incs2.
  unfold S2.
  es.
Qed.

Lemma BigStep2 b:
  P (2+b*2) ->
  S3 (2+b*2) -->+
  S3 (7+b*4).
Proof.
  unfold P,S3.
  intros HP.
  follow HP.
  step1.
  mid (S2 1 (b*2+2)).
  1: es.
  follow Incs2.
  unfold S2.
  es.
Qed.

Definition S4 a := S3 (1+a*2).
Definition P1 a := P (1+a*2).

Lemma BigStep b:
  P1 b ->
  S4 b -->+
  S4 (5+b*4) /\
  P1 (5+b*4).
Proof.
  unfold S4,P1.
  intros HP.
  epose proof (P_S _ HP) as HP'.
  replace (1+b*2+(3+b*2)) with (2+(1+b*2)*2) in HP' by lia.
  epose proof (P_S' _ HP') as HP''.
  split.
  2: applys_eq HP''; lia.
  follow11 (BigStep1 _ HP).
  replace (4+b*4) with (2+(1+b*2)*2) by lia.
  follow10 (BigStep2 _ HP').
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S4 1).
  1: unfold S4,S3; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1,P; es.
  intros i HP.
  eexists.
  apply BigStep,HP.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC0RF_0LD---_1LA1LE_1RA0LB_1LC1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c d :=
  l <* <[0;1]^^a <{{A}} [1] *> [0;1;1;0;1;0]^^b *> [1;0]^^c *> [0] *> [1;0;0]^^d *> 0inf.

Lemma Inc1 l a b c d:
  S1 l (2+a) b c (2+d) -->*
  S1 l a (1+b) (2+c) d.
Proof.
  unfold S1.
  es.
Qed.

Lemma Incs1 l a b c d n:
  S1 l (n*2+a) b c (n*2+d) -->*
  S1 l a (n+b) (n*2+c) d.
Proof.
  gen l a b c d.
  ind n Inc1.
Qed.

Definition P a :=
  forall l,
  l <* <[0;1]^^a {{A}}> 0inf -->*
  l <{{B}} [0;1] *> [0;1;0]^^a *> 0inf.

Lemma P_S' b:
  P (2+b*2) ->
  P ((2+b*2)+(5+b*2)).
Proof.
  unfold P.
  intros HP l.
  rewrite (lpow_add _ (2+b*2) (5+b*2)),Str_app_assoc.
  follow HP.
  mid (S1 l (b*2+4) 1 0 (b*2+1)).
  1: es.
  follow Incs1.
  unfold S1.
  mid ([1;0]^^(2+b*2)*>[1;1;0]^^(5+b*2)*>l {{A}}> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Lemma P_S b:
  P (1+b*2) ->
  P ((1+b*2)+(3+b*2)).
Proof.
  unfold P.
  intros HP l.
  rewrite (lpow_add _ (1+b*2) (3+b*2)),Str_app_assoc.
  follow HP.
  mid (S1 l (b*2+2) 1 0 (b*2+0)).
  1: es.
  follow Incs1.
  unfold S1.
  mid ([1;0]^^(1+b*2)*>[1;1;0]^^(3+b*2)*>l {{A}}> 0inf).
  1: es.
  follow HP.
  es.
Qed.

Definition S2 a b :=
  0inf <{{E}} [1] *> [0;1]^^a *> [0;1;0]^^b *> 0inf.

Lemma Inc2 a b:
  S2 a (2+b) -->*
  S2 (4+a) b.
Proof.
  unfold S2.
  es.
Qed.

Lemma Incs2 a b n:
  S2 a (n*2+b) -->*
  S2 (n*4+a) b.
Proof.
  gen a b.
  ind n Inc2.
Qed.

Definition S3 a :=
  0inf <* <[0;1]^^a {{A}}> 0inf.

Lemma BigStep1 b:
  P (1+b*2) ->
  S3 (1+b*2) -->+
  S3 (4+b*4).
Proof.
  unfold P,S3.
  intros HP.
  follow HP.
  step1.
  mid (S2 1 (b*2+1)).
  1: es.
  follow Incs2.
  unfold S2.
  es.
Qed.

Lemma BigStep2 b:
  P (2+b*2) ->
  S3 (2+b*2) -->+
  S3 (7+b*4).
Proof.
  unfold P,S3.
  intros HP.
  follow HP.
  step1.
  mid (S2 1 (b*2+2)).
  1: es.
  follow Incs2.
  unfold S2.
  es.
Qed.

Definition S4 a := S3 (1+a*2).
Definition P1 a := P (1+a*2).

Lemma BigStep b:
  P1 b ->
  S4 b -->+
  S4 (5+b*4) /\
  P1 (5+b*4).
Proof.
  unfold S4,P1.
  intros HP.
  epose proof (P_S _ HP) as HP'.
  replace (1+b*2+(3+b*2)) with (2+(1+b*2)*2) in HP' by lia.
  epose proof (P_S' _ HP') as HP''.
  split.
  2: applys_eq HP''; lia.
  follow11 (BigStep1 _ HP).
  replace (4+b*4) with (2+(1+b*2)*2) by lia.
  follow10 (BigStep2 _ HP').
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S4 1).
  1: unfold S4,S3; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1,P; es.
  intros i HP.
  eexists.
  apply BigStep,HP.
Qed.

End TM5.


