From BusyCoq Require Import Individual62 Longitudinal.
Require Import Lia.
Require Import ZArith.
Require Import String List.
Require Import ZifyNat.

Open Scope list.




Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC0LD_0RE1RA_0LB1LA_1RC1RF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(1+b*2) *> [0;0] *> [0;1]^^c *> [0;0;0;1] *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a (1+b) (1+c).
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(0+b*4) *> [0;1]^^(c*2) *> [0;0;0;1] *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Definition S2 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(1+b*2) *> [0;1;1;0;0]^^2 *> [0;1]^^(0+c) *> [0;0;0;1] *> const 0.

Lemma Inc2 a b c:
  S2 (1+a) b c -->*
  S2 a (1+b) (1+c).
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2s a b c:
  S2 a b c -->*
  S2 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc2.
Qed.

Lemma Ov0 b c:
  S0 0 b (2+c*2) -->*
  S1 b 1 c.
Proof.
  es.
Qed.

Lemma Ov1 a b:
  S1 (2+a) b 0 -->*
  S2 a (1+b*2) 0.
Proof.
  es.
Qed.

Lemma Ov2 b c:
  S2 0 b c -->+
  S0 b 1 (3+c).
Proof.
  es.
Qed.

Lemma BigStep b c:
  2+c <= b ->
  S0 0 b (2+c*2) -->+
  S0 0 (2+b+c) (2+b*2).
Proof.
  intro H.
  follow Ov0.
  follow (Inc1s (b-c) 1 0 c).
  replace (b-c) with (2+(b-c-2)) by lia.
  follow Ov1.
  follow Inc2s.
  follow10 Ov2.
  follow Inc0s.
  finish.
Qed.

Definition config '(b,c) :=
  S0 0 b (2+c*2).


Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (3,1)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=fun '(b,c) => 2+c<=b).
  2: lia.
  intros [b c].
  exists (2+b+c,b).
  unfold config.
  split.
  1: apply BigStep,H.
  lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0RF_0RC0LD_0RE1RA_0LB1LF_1RC---_1LB0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(1+b*2) *> [0;0] *> [0;1]^^c *> [0;0;0;1] *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a (1+b) (1+c).
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(0+b*4) *> [0;1]^^(c*2) *> [0;0;0;1] *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Definition S2 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(1+b*2) *> [0;1;1;0;0]^^2 *> [0;1]^^(0+c) *> [0;0;0;1] *> const 0.

Lemma Inc2 a b c:
  S2 (1+a) b c -->*
  S2 a (1+b) (1+c).
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2s a b c:
  S2 a b c -->*
  S2 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc2.
Qed.

Lemma Ov0 b c:
  S0 0 b (2+c*2) -->*
  S1 b 1 c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Ov1 a b:
  S1 (2+a) b 0 -->*
  S2 a (1+b*2) 0.
Proof.
  es.
Qed.

Lemma Ov2 b c:
  S2 0 b c -->+
  S0 b 1 (3+c).
Proof.
  es.
Qed.

Lemma BigStep b c:
  2+c <= b ->
  S0 0 b (2+c*2) -->+
  S0 0 (2+b+c) (2+b*2).
Proof.
  intro H.
  follow Ov0.
  follow (Inc1s (b-c) 1 0 c).
  replace (b-c) with (2+(b-c-2)) by lia.
  follow Ov1.
  follow Inc2s.
  follow10 Ov2.
  follow Inc0s.
  finish.
Qed.

Definition config '(b,c) :=
  S0 0 b (2+c*2).


Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (3,1)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=fun '(b,c) => 2+c<=b).
  2: lia.
  intros [b c].
  exists (2+b+c,b).
  unfold config.
  split.
  1: apply BigStep,H.
  lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC0LE_0RF1RD_1LB0RA_0LB1LD_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(1+b*2) *> [0;0] *> [0;1]^^c *> [0;0;0;1] *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a (1+b) (1+c).
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(0+b*4) *> [0;1]^^(c*2) *> [0;0;0;1] *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Definition S2 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(1+b*2) *> [0;1;1;0;0]^^2 *> [0;1]^^(0+c) *> [0;0;0;1] *> const 0.

Lemma Inc2 a b c:
  S2 (1+a) b c -->*
  S2 a (1+b) (1+c).
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2s a b c:
  S2 a b c -->*
  S2 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc2.
Qed.

Lemma Ov0 b c:
  S0 0 b (2+c*2) -->*
  S1 b 1 c.
Proof.
  es.
Qed.

Lemma Ov1 a b:
  S1 (2+a) b 0 -->*
  S2 a (1+b*2) 0.
Proof.
  es.
Qed.

Lemma Ov2 b c:
  S2 0 b c -->+
  S0 b 1 (3+c).
Proof.
  es.
Qed.

Lemma BigStep b c:
  2+c <= b ->
  S0 0 b (2+c*2) -->+
  S0 0 (2+b+c) (2+b*2).
Proof.
  intro H.
  follow Ov0.
  follow (Inc1s (b-c) 1 0 c).
  replace (b-c) with (2+(b-c-2)) by lia.
  follow Ov1.
  follow Inc2s.
  follow10 Ov2.
  follow Inc0s.
  finish.
Qed.

Definition config '(b,c) :=
  S0 0 b (2+c*2).


Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (3,1)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=fun '(b,c) => 2+c<=b).
  2: lia.
  intros [b c].
  exists (2+b+c,b).
  unfold config.
  split.
  1: apply BigStep,H.
  lia.
Qed.

End TM3.




Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB0RF_0RC0LD_0RE1RA_0LB1LA_1RC---_1RA0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(1+b*2) *> [0;0] *> [0;1]^^c *> [0;0;0;1] *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a (1+b) (1+c).
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(0+b*4) *> [0;1]^^(c*2) *> [0;0;0;1] *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Definition S2 a b c :=
  const 0 <{{B}} [0] *> [0;1;1]^^(1+a*2) *> [0;0] *> [0;1;1]^^(1+b*2) *> [0;1;1;0;0]^^2 *> [0;1]^^(0+c) *> [0;0;0;1] *> const 0.

Lemma Inc2 a b c:
  S2 (1+a) b c -->*
  S2 a (1+b) (1+c).
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2s a b c:
  S2 a b c -->*
  S2 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc2.
Qed.

Lemma Ov0 b c:
  S0 0 b (2+c*2) -->*
  S1 b 1 c.
Proof.
  es.
Qed.

Lemma Ov1 a b:
  S1 (2+a) b 0 -->*
  S2 a (1+b*2) 0.
Proof.
  es.
Qed.

Lemma Ov2 b c:
  S2 0 b c -->+
  S0 b 1 (3+c).
Proof.
  es.
Qed.

Lemma BigStep b c:
  2+c <= b ->
  S0 0 b (2+c*2) -->+
  S0 0 (2+b+c) (2+b*2).
Proof.
  intro H.
  follow Ov0.
  follow (Inc1s (b-c) 1 0 c).
  replace (b-c) with (2+(b-c-2)) by lia.
  follow Ov1.
  follow Inc2s.
  follow10 Ov2.
  follow Inc0s.
  finish.
Qed.

Definition config '(b,c) :=
  S0 0 b (2+c*2).


Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (3,1)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=fun '(b,c) => 2+c<=b).
  2: lia.
  intros [b c].
  exists (2+b+c,b).
  unfold config.
  split.
  1: apply BigStep,H.
  lia.
Qed.

End TM4.



Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC1LD_1RA0RB_0LB0RE_0RA0LF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <{{B}} [0;1]^^(1+a) *> [0;0] *> [0;1]^^b *> [0;0;0] *> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a (1+b) (1+c).
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <{{B}} [0;1]^^(1+a) *> [0;0;0] *> [1;0]^^(b*2) *> [1]^^(1+c) *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.


Lemma Ov0 b c:
  S0 0 b c -->+
  S1 b 1 c.
Proof.
  es.
Qed.

Lemma Ov1 a b:
  S1 a b 0 -->*
  S0 a (1+b*2) 0.
Proof.
  es.
Qed.

Lemma BigStep b c:
  c<=b ->
  S0 0 b c -->+
  S0 0 (3+b+c) (b-c).
Proof.
  intros H.
  follow10 Ov0.
  follow (Inc1s (b-c) 1 0 c).
  follow Ov1.
  follow Inc0s.
  finish.
Qed.

Definition config '(b,c) :=
  S0 0 b c.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (14,5)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=fun '(b,c) => c<=b).
  2: lia.
  intros [b c].
  exists (3+b+c,b-c).
  unfold config.
  split.
  1: apply BigStep,H.
  lia.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC---_0RA0LF_0LD0RE_1RC1LF_0LE1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c :=
  const 0 <{{E}} [0;1]^^(1+a*2) *> [0;0;1;1;1] *> [0;1]^^(1+b*2) *> [0;0] *> [1]^^(c*2) *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a (1+b) (1+c).
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <{{E}} [0;1]^^(1+a*2) *> [0;0;1;1] *> [1;0]^^(b*4) *> [1]^^(2+c*2) *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) 0 c.
Proof.
  es.
Qed.

Lemma Ov1 a b:
  S1 (1+a) b 0 -->+
  S0 a (1+b*2) 1.
Proof.
  es.
Qed.

Lemma BigStep a:
  S1 (1+a) a 0 -->+
  S1 (1+(2+a*2)) (2+a*2) 0.
Proof.
  follow10 Ov1.
  follow Inc0s.
  follow (Ov0 (1+a*3) a).
  follow (Inc1s (1+(2+a*2)) 0 0 a).
  follow100 Ov1.
  follow Inc0s.
  follow (Ov0 (3+a*4) (2+a*2)).
  follow (Inc1s (3+a*2) 0 0 (2+a*2)).
  finish.
Qed.

Definition config a :=
  S1 (1+a) a 0.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config 0).
  1: unfold config,S1; solve_init.
  apply progress_nonhalt_simple.
  intros a.
  exists (2+a*2).
  unfold config.
  apply BigStep.
Qed.

End TM6.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1LB1LC_1LC0LC_1LD0LE_0RE1LF_0LA0RD_1RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c d :=
  const 0 <* [0;0;1]^^a <* [0;1;1]^^2 {{D}}> [0;1;0]^^b *> [0;1;0;0;1;1]^^c *> [0;0] *> [1;0;0;1;1;0]^^d *> const 0.

Lemma Inc0 a b c d:
  S0 (1+a) b (1+c) d -->*
  S0 a (1+b) c (1+d).
Proof.
  es.
Qed.

Definition S1 a b c d :=
  const 0 <* [0;0;1]^^2 <* [0;1] {{D}}> [0;1;1]^^a *> [0;1;0]^^b *> [0;1;0;0;1;1]^^c *> [0;0] *> [1;0;0;1;1;0]^^d *> const 0.

Lemma Inc1 a b c d:
  S1 a b (1+c) d -->*
  S1 (1+a) b c (1+d).
Proof.
  es.
Qed.

Definition S2 a b c d :=
  const 0 <* [0;0;1]^^a <* [1;0;1]^^b <* [0;0;0;1] <* [0;0;1;1;0;1]^^c <{{C}} [1;0] *> [0;1;0;0;1;1]^^2 *> [0;0] *> [1;0;0;1;1;0]^^d *> const 0.

Lemma Inc2 a b c d:
  S2 a (2+b) c d -->*
  S2 (1+a) b c (1+d).
Proof.
  unfold S2.
  es.
Qed.

Lemma Inc0s a b c d n:
  S0 (n+a) b (n+c) d -->*
  S0 a (n+b) c (n+d).
Proof.
  gen a b c d.
  ind n Inc0.
Qed.

Lemma Inc1s a b c d:
  S1 a b c d -->*
  S1 (c+a) b 0 (c+d).
Proof.
  gen a b d.
  ind c Inc1.
Qed.

Lemma Inc2s a b c d n:
  S2 a (n*2+b) c d -->*
  S2 (n+a) b c (n+d).
Proof.
  gen a b c d.
  ind n Inc2.
Qed.

Lemma Ov0 b c d:
  S0 0 b (5+c) d -->*
  S1 2 (2+b) c (5+d).
Proof.
  es.
Qed.

Lemma Ov1 a b d:
  S1 a (1+b) 0 (3+d) -->*
  S2 (2+a) b d 1.
Proof.
  es.
Qed.

Lemma Ov2_0 a b c:
  S2 (2+a) 0 b c -->+
  S0 a 0 (1+b) (2+c).
Proof.
  es.
Qed.

Lemma Ov2_1 a b c:
  S2 (2+a) 1 b c -->+
  S0 a 0 (2+b) (2+c).
Proof.
  es.
Qed.

Lemma BigStep00 a b c:
  4+a*2<=b ->
  S2 (2+a*2) 0 b c -->+
  S2 (2+(b-a-2)) 1 (b+c) (a+1).
Proof.
  intro H.
  follow10 Ov2_0.
  follow (Inc0s 0 0 (5+(b-a*2-4)) (2+c) (a*2)).
  follow Ov0.
  follow Inc1s.
  mid (S1 (b-a*2-2) (1+(a*2+1)) 0 (3+(b+c))).
  1: finish.
  follow Ov1.
  follow Inc2s.
  finish.
Qed.

Lemma BigStep01 a b c:
  5+a*2<=b ->
  S2 (2+(1+a*2)) 0 b c -->+
  S2 (2+(b-a-2)) 0 (b+c) (a+2).
Proof.
  intro H.
  follow10 Ov2_0.
  follow (Inc0s 0 0 (5+(b-a*2-5)) (2+c) (1+a*2)).
  follow Ov0.
  follow Inc1s.
  mid (S1 (b-a*2-3) (1+((1+a)*2+0)) 0 (3+(b+c))).
  1: finish.
  follow Ov1.
  follow Inc2s.
  finish.
Qed.

Lemma BigStep10 a b c:
  3+a*2<=b ->
  S2 (2+a*2) 1 b c -->+
  S2 (2+(b-a-1)) 1 (1+b+c) (a+1).
Proof.
  intro H.
  follow10 Ov2_1.
  follow (Inc0s 0 0 (5+(b-a*2-3)) (2+c) (a*2)).
  follow Ov0.
  follow Inc1s.
  mid (S1 (b-a*2-1) (1+(a*2+1)) 0 (3+(1+b+c))).
  1: finish.
  follow Ov1.
  follow Inc2s.
  finish.
Qed.

Lemma BigStep11 a b c:
  5+a*2<=b ->
  S2 (2+(1+a*2)) 1 b c -->+
  S2 (2+(b-a-1)) 0 (1+b+c) (a+2).
Proof.
  intro H.
  follow10 Ov2_1.
  follow (Inc0s 0 0 (5+(b-a*2-4)) (2+c) (1+a*2)).
  follow Ov0.
  follow Inc1s.
  mid (S1 (b-a*2-2) (1+((1+a)*2+0)) 0 (3+(1+b+c))).
  1: finish.
  follow Ov1.
  follow Inc2s.
  finish.
Qed.

Definition config '(a,i,b,c) := S2 (2+a) i b c.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (32,0,58,14)%nat).
  1: unfold config,S2; solve_init.
  apply progress_nonhalt_cond with (P:=fun '(a,i,b,c) => 3<=a /\ (i=0\/i=1)%nat /\ 5+a<=b /\ 3<=c).
  2: lia.
  intros [[[a i] b] c] [H [H0 [H1 H2]]].
  destruct (Nat.Even_or_Odd a) as [[a0 E]|[a0 E]];
  subst a;
  destruct H0 as [H0|H0];
  subst i;
  unfold config;
  replace (2*a0) with (a0*2) by lia;
  replace (a0*2+1) with (1+a0*2) by lia;
  eexists (_,_,_,_); split.
  - apply BigStep00; lia.
  - lia.
  - apply BigStep10; lia.
  - lia.
  - apply BigStep01; lia.
  - lia.
  - apply BigStep11; lia.
  - lia.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC0LE_1RD0RA_0LE0RB_---1LF_0LB0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c :=
  const 0 <{{B}} [0] *> [1;0;0]^^(a) *> [0;0;1]^^b *> [0;0;0;0] *> [1;0]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a (1+b) (1+c).
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <{{B}} [0;1] *> [0;0;1]^^(a) *> [0;0;0;0] *> [1;0;0]^^(b*3) *> [1;0]^^(c) *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (2+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n*2+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 b c:
  S0 0 b c -->+
  S1 b 0 (1+c).
Proof.
  es.
Qed.

Lemma Ov1_1 a b:
  S1 a b 1 -->*
  S0 (1+a) (1+b*3) 0.
Proof.
  es.
Qed.

Lemma Ov1_0 a b:
  S1 a b 0 -->*
  S0 (1+a) (b*3) 0.
Proof.
  es.
Qed.

Lemma BigStep00 a b:
  S1 (a*2) b 0 -->+
  S1 (a+b*3) (1+a) 0.
Proof.
  follow Ov1_0.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (a+b*3) 0 0 (1+a)).
  finish.
Qed.

Lemma BigStep01 a b:
  S1 (1+a*2) b 0 -->+
  S1 (1+a+b*3) (1+a) 1.
Proof.
  follow Ov1_0.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (1+a+b*3) 0 1 (1+a)).
  finish.
Qed.

Lemma BigStep10 a b:
  S1 (a*2) b 1 -->+
  S1 (1+a+b*3) (1+a) 0.
Proof.
  follow Ov1_1.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (1+a+b*3) 0 0 (1+a)).
  finish.
Qed.

Lemma BigStep11 a b:
  S1 (1+a*2) b 1 -->+
  S1 (2+a+b*3) (1+a) 1.
Proof.
  follow Ov1_1.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (2+a+b*3) 0 1 (1+a)).
  finish.
Qed.

Definition config '(a,b,i) := S1 a b i.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (58,19,1)%nat).
  1: unfold config,S1; solve_init.
  apply progress_nonhalt_cond with (P:=fun '(a,b,i) => (i=0\/i=1)%nat).
  2: lia.
  intros [[a b] i] H0.
  destruct (Nat.Even_or_Odd a) as [[a0 E]|[a0 E]];
  subst a;
  destruct H0 as [H0|H0];
  subst i;
  unfold config;
  replace (2*a0) with (a0*2) by lia;
  replace (a0*2+1) with (1+a0*2) by lia;
  eexists (_,_,_); split.
  - apply BigStep00; lia.
  - lia.
  - apply BigStep10; lia.
  - lia.
  - apply BigStep01; lia.
  - lia.
  - apply BigStep11; lia.
  - lia.
Qed.

End TM11.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC0RE_---1LD_0LE0LF_1RA0LC_1RE0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c :=
  const 0 <{{E}} [0] *> [1;0;0]^^(a) *> [0;0;1]^^b *> [0;0;0;0] *> [1;0]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a (1+b) (1+c).
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <{{E}} [0;1] *> [0;0;1]^^(a) *> [0;0;0;0] *> [1;0;0]^^(b*3) *> [1;0]^^(c) *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (2+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n*2+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 b c:
  S0 0 b c -->+
  S1 b 0 (1+c).
Proof.
  es.
Qed.

Lemma Ov1_1 a b:
  S1 a b 1 -->*
  S0 (1+a) (1+b*3) 0.
Proof.
  es.
Qed.

Lemma Ov1_0 a b:
  S1 a b 0 -->*
  S0 (1+a) (b*3) 0.
Proof.
  es.
Qed.

Lemma BigStep00 a b:
  S1 (a*2) b 0 -->+
  S1 (a+b*3) (1+a) 0.
Proof.
  follow Ov1_0.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (a+b*3) 0 0 (1+a)).
  finish.
Qed.

Lemma BigStep01 a b:
  S1 (1+a*2) b 0 -->+
  S1 (1+a+b*3) (1+a) 1.
Proof.
  follow Ov1_0.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (1+a+b*3) 0 1 (1+a)).
  finish.
Qed.

Lemma BigStep10 a b:
  S1 (a*2) b 1 -->+
  S1 (1+a+b*3) (1+a) 0.
Proof.
  follow Ov1_1.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (1+a+b*3) 0 0 (1+a)).
  finish.
Qed.

Lemma BigStep11 a b:
  S1 (1+a*2) b 1 -->+
  S1 (2+a+b*3) (1+a) 1.
Proof.
  follow Ov1_1.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (2+a+b*3) 0 1 (1+a)).
  finish.
Qed.

Definition config '(a,b,i) := S1 a b i.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (61,20,0)%nat).
  1: unfold config,S1; solve_init.
  apply progress_nonhalt_cond with (P:=fun '(a,b,i) => (i=0\/i=1)%nat).
  2: lia.
  intros [[a b] i] H0.
  destruct (Nat.Even_or_Odd a) as [[a0 E]|[a0 E]];
  subst a;
  destruct H0 as [H0|H0];
  subst i;
  unfold config;
  replace (2*a0) with (a0*2) by lia;
  replace (a0*2+1) with (1+a0*2) by lia;
  eexists (_,_,_); split.
  - apply BigStep00; lia.
  - lia.
  - apply BigStep10; lia.
  - lia.
  - apply BigStep01; lia.
  - lia.
  - apply BigStep11; lia.
  - lia.
Qed.

End TM12.

Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RF_0LD0RA_---1LE_0LA0LF_1RA0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c :=
  const 0 <{{A}} [0] *> [1;0;0]^^(a) *> [0;0;1]^^b *> [0;0;0;0] *> [1;0]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a (1+b) (1+c).
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <{{A}} [0;1] *> [0;0;1]^^(a) *> [0;0;0;0] *> [1;0;0]^^(b*3) *> [1;0]^^(c) *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (2+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n*2+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 b c:
  S0 0 b c -->+
  S1 b 0 (1+c).
Proof.
  es.
Qed.

Lemma Ov1_1 a b:
  S1 a b 1 -->*
  S0 (1+a) (1+b*3) 0.
Proof.
  es.
Qed.

Lemma Ov1_0 a b:
  S1 a b 0 -->*
  S0 (1+a) (b*3) 0.
Proof.
  es.
Qed.

Lemma BigStep00 a b:
  S1 (a*2) b 0 -->+
  S1 (a+b*3) (1+a) 0.
Proof.
  follow Ov1_0.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (a+b*3) 0 0 (1+a)).
  finish.
Qed.

Lemma BigStep01 a b:
  S1 (1+a*2) b 0 -->+
  S1 (1+a+b*3) (1+a) 1.
Proof.
  follow Ov1_0.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (1+a+b*3) 0 1 (1+a)).
  finish.
Qed.

Lemma BigStep10 a b:
  S1 (a*2) b 1 -->+
  S1 (1+a+b*3) (1+a) 0.
Proof.
  follow Ov1_1.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (1+a+b*3) 0 0 (1+a)).
  finish.
Qed.

Lemma BigStep11 a b:
  S1 (1+a*2) b 1 -->+
  S1 (2+a+b*3) (1+a) 1.
Proof.
  follow Ov1_1.
  follow Inc0s.
  follow10 Ov0.
  follow (Inc1s (2+a+b*3) 0 1 (1+a)).
  finish.
Qed.

Definition config '(a,b,i) := S1 a b i.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (45,16,0)%nat).
  1: unfold config,S1; solve_init.
  apply progress_nonhalt_cond with (P:=fun '(a,b,i) => (i=0\/i=1)%nat).
  2: lia.
  intros [[a b] i] H0.
  destruct (Nat.Even_or_Odd a) as [[a0 E]|[a0 E]];
  subst a;
  destruct H0 as [H0|H0];
  subst i;
  unfold config;
  replace (2*a0) with (a0*2) by lia;
  replace (a0*2+1) with (1+a0*2) by lia;
  eexists (_,_,_); split.
  - apply BigStep00; lia.
  - lia.
  - apply BigStep10; lia.
  - lia.
  - apply BigStep01; lia.
  - lia.
  - apply BigStep11; lia.
  - lia.
Qed.

End TM13.


Module TM21.
Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC---_0RA1LD_1LE0LF_1LC0LD_1RF0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d :=
  0inf <* <[1]^^a <* <[1;0;1;0;1;1;1]^^b <{{D}} [0] *> [1;0]^^c *> [1;0;1;0;1;1;1]^^d *> 0inf.

Lemma Inc1 a b c d:
  S1 a (1+b) c d -->*
  S1 a b (1+c) (1+d).
Proof.
  es.
Qed.

Lemma Incs1 a b c d:
  S1 a b c d -->*
  S1 a 0 (b+c) (b+d).
Proof.
  gen c d.
  ind b Inc1.
Qed.

Lemma Inc2 a c d:
  S1 (3+a) 0 (1+c) d -->*
  S1 a 0 c (1+d).
Proof.
  es.
Qed.

Lemma Incs2 n a c d:
  S1 (n*3+a) 0 (n+c) d -->*
  S1 a 0 c (n+d).
Proof.
  gen a c d.
  ind n Inc2.
Qed.

Lemma Rst0 c d:
  S1 0 0 c (1+d) -->+
  S1 (c*2+4) d 1 1.
Proof.
  es.
Qed.

Lemma Rst1 c d:
  S1 1 0 c (1+d) -->+
  S1 (c*2+3) d 1 1.
Proof.
  es.
Qed.

Lemma Rst2 c d:
  S1 2 0 c d -->+
  S1 (c*2) d 1 1.
Proof.
  es.
Qed.

Lemma Incs12 n a b:
  S1 (n*3+a) (n+b) 1 1 -->*
  S1 a 0 (b+1) (1+(n*2+b)).
Proof.
  follow Incs1.
  rewrite <-Nat.add_assoc.
  follow Incs2.
  finish.
Qed.

Definition S '(a,b) := S1 a b 1 1.

Close Scope sym.

Lemma BigStep a b:
  a/3<=b ->
  exists c1 c2,
  S (a,b) -->+
  S ((b-a/3)*2+2+c1,b+a/3+c2) /\
  c1<=4 /\ c2<=1.
Proof.
  unfold S.
  remember (a/3) as a1.
  remember (a mod 3) as a2.
  replace a with (a1*3+a2) by lia.
  intros Hb.
  remember (b-a1) as b1.
  replace b with (a1+b1) by lia.
  destruct a2 as [|[|[|]]]. 4: lia.
  - exists 4,0.
    split. 2: lia.
    follow Incs12.
    follow10 Rst0.
    finish.
  - exists 3,0.
    split. 2: lia.
    follow Incs12.
    follow10 Rst1.
    finish.
  - exists 0,1.
    split. 2: lia.
    follow Incs12.
    follow10 Rst2.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (54,50)).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun '(a,b) => a<=b+b/3 /\ b<=a+a/3 /\ 50<=a /\ 50<=b).
  2: lia.
  intros [a b] HP.
  unshelve epose proof (BigStep a b _) as [c1 [c2 [I1 I2]]].
  1: lia.
  eexists (_,_).
  split.
  1: apply I1.
  lia.
Qed.

End TM21.


Module TM22.
Definition tm := Eval compute in (TM_from_str "1LB---_0RC1LD_1RA1RB_1LE0LF_1LB0LD_1RF0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d :=
  0inf <* <[1]^^a <* <[1;0;1;0;1;1;1]^^b <{{D}} [0] *> [1;0]^^c *> [1;0;1;0;1;1;1]^^d *> 0inf.

Lemma Inc1 a b c d:
  S1 a (1+b) c d -->*
  S1 a b (1+c) (1+d).
Proof.
  es.
Qed.

Lemma Incs1 a b c d:
  S1 a b c d -->*
  S1 a 0 (b+c) (b+d).
Proof.
  gen c d.
  ind b Inc1.
Qed.

Lemma Inc2 a c d:
  S1 (3+a) 0 (1+c) d -->*
  S1 a 0 c (1+d).
Proof.
  es.
Qed.

Lemma Incs2 n a c d:
  S1 (n*3+a) 0 (n+c) d -->*
  S1 a 0 c (n+d).
Proof.
  gen a c d.
  ind n Inc2.
Qed.

Lemma Rst0 c d:
  S1 0 0 c (1+d) -->+
  S1 (c*2+4) d 1 1.
Proof.
  es.
Qed.

Lemma Rst1 c d:
  S1 1 0 c (1+d) -->+
  S1 (c*2+3) d 1 1.
Proof.
  es.
Qed.

Lemma Rst2 c d:
  S1 2 0 c d -->+
  S1 (c*2) d 1 1.
Proof.
  es.
Qed.

Lemma Incs12 n a b:
  S1 (n*3+a) (n+b) 1 1 -->*
  S1 a 0 (b+1) (1+(n*2+b)).
Proof.
  follow Incs1.
  rewrite <-Nat.add_assoc.
  follow Incs2.
  finish.
Qed.

Definition S '(a,b) := S1 a b 1 1.

Close Scope sym.

Lemma BigStep a b:
  a/3<=b ->
  exists c1 c2,
  S (a,b) -->+
  S ((b-a/3)*2+2+c1,b+a/3+c2) /\
  c1<=4 /\ c2<=1.
Proof.
  unfold S.
  remember (a/3) as a1.
  remember (a mod 3) as a2.
  replace a with (a1*3+a2) by lia.
  intros Hb.
  remember (b-a1) as b1.
  replace b with (a1+b1) by lia.
  destruct a2 as [|[|[|]]]. 4: lia.
  - exists 4,0.
    split. 2: lia.
    follow Incs12.
    follow10 Rst0.
    finish.
  - exists 3,0.
    split. 2: lia.
    follow Incs12.
    follow10 Rst1.
    finish.
  - exists 0,1.
    split. 2: lia.
    follow Incs12.
    follow10 Rst2.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (55,55)).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun '(a,b) => a<=b+b/3 /\ b<=a+a/3 /\ 50<=a /\ 50<=b).
  2: lia.
  intros [a b] HP.
  unshelve epose proof (BigStep a b _) as [c1 [c2 [I1 I2]]].
  1: lia.
  eexists (_,_).
  split.
  1: apply I1.
  lia.
Qed.

End TM22.


Module TM23.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1LC0LA_0RD1LA_1RF1RC_1RE0RB_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d :=
  0inf <* <[1]^^a <* <[1;0;1;0;1;1;1]^^b <{{A}} [0] *> [1;0]^^c *> [1;0;1;0;1;1;1]^^d *> 0inf.

Lemma Inc1 a b c d:
  S1 a (1+b) c d -->*
  S1 a b (1+c) (1+d).
Proof.
  es.
Qed.

Lemma Incs1 a b c d:
  S1 a b c d -->*
  S1 a 0 (b+c) (b+d).
Proof.
  gen c d.
  ind b Inc1.
Qed.

Lemma Inc2 a c d:
  S1 (3+a) 0 (1+c) d -->*
  S1 a 0 c (1+d).
Proof.
  es.
Qed.

Lemma Incs2 n a c d:
  S1 (n*3+a) 0 (n+c) d -->*
  S1 a 0 c (n+d).
Proof.
  gen a c d.
  ind n Inc2.
Qed.

Lemma Rst0 c d:
  S1 0 0 c (1+d) -->+
  S1 (c*2+4) d 1 1.
Proof.
  es.
Qed.

Lemma Rst1 c d:
  S1 1 0 c (1+d) -->+
  S1 (c*2+3) d 1 1.
Proof.
  es.
Qed.

Lemma Rst2 c d:
  S1 2 0 c d -->+
  S1 (c*2) d 1 1.
Proof.
  es.
Qed.

Lemma Incs12 n a b:
  S1 (n*3+a) (n+b) 1 1 -->*
  S1 a 0 (b+1) (1+(n*2+b)).
Proof.
  follow Incs1.
  rewrite <-Nat.add_assoc.
  follow Incs2.
  finish.
Qed.

Definition S '(a,b) := S1 a b 1 1.

Close Scope sym.

Lemma BigStep a b:
  a/3<=b ->
  exists c1 c2,
  S (a,b) -->+
  S ((b-a/3)*2+2+c1,b+a/3+c2) /\
  c1<=4 /\ c2<=1.
Proof.
  unfold S.
  remember (a/3) as a1.
  remember (a mod 3) as a2.
  replace a with (a1*3+a2) by lia.
  intros Hb.
  remember (b-a1) as b1.
  replace b with (a1+b1) by lia.
  destruct a2 as [|[|[|]]]. 4: lia.
  - exists 4,0.
    split. 2: lia.
    follow Incs12.
    follow10 Rst0.
    finish.
  - exists 3,0.
    split. 2: lia.
    follow Incs12.
    follow10 Rst1.
    finish.
  - exists 0,1.
    split. 2: lia.
    follow Incs12.
    follow10 Rst2.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (64,69)).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun '(a,b) => a<=b+b/3 /\ b<=a+a/3 /\ 50<=a /\ 50<=b).
  2: lia.
  intros [a b] HP.
  unshelve epose proof (BigStep a b _) as [c1 [c2 [I1 I2]]].
  1: lia.
  eexists (_,_).
  split.
  1: apply I1.
  lia.
Qed.

End TM23.


Module TM24.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1LC0RD_1LA0LD_1LB1RE_0RB0RC_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d e :=
  0inf <* <[1;0;1]^^a <* <[1;0;0;1;0;0;1]^^b <{{D}} [0;1;1]^^c *> [0;1;1;1;1;1;1]^^d *> [0;1;1] *> ([0] ++ [1]^^10)^^e *> 0inf.

Lemma Inc1 a b c d e:
  S1 a (2+b) c d e -->*
  S1 a b (2+c) d (1+e).
Proof.
  es.
Qed.

Lemma Incs1 n a b c d e:
  S1 a (n*2+b) c d e -->*
  S1 a b (n*2+c) d (n+e).
Proof.
  gen a b c d e.
  ind n Inc1.
Qed.

Lemma Inc2 a c d e:
  S1 (4+a) 0 (4+c) d e -->*
  S1 a 0 c d (3+e).
Proof.
  es.
Qed.

Lemma Incs2 n a c d e:
  S1 (n*4+a) 0 (n*4+c) d e -->*
  S1 a 0 c d (n*3+e).
Proof.
  gen a c d e.
  ind n Inc2.
Qed.

Definition S0 a b c d e :=
  0inf <* <[1;0;1]^^a <* <[1;0;0;1;0;0;1]^^b <* <[1;0;1] <* <[1;0;0;1;0;0;0;1;0;0;1]^^c <{{D}} [0;1;1;1;1;1;1]^^d *> [0;1;1] *> ([0] ++ [1]^^10)^^e *> 0inf.

Lemma Inc0 a b c d e:
  S0 a b (2+c) d e -->*
  S0 a b c (2+d) (1+e).
Proof.
  es.
Qed.

Lemma Incs0 n a b c d e:
  S0 a b (n*2+c) d e -->*
  S0 a b c (n*2+d) (n+e).
Proof.
  gen a b c d e.
  ind n Inc0.
Qed.

Lemma Ov0_0 a b d e:
  S0 a (1+b) 0 (1+d) e -->*
  S1 a b 3 d (1+e).
Proof.
  es.
Qed.

Lemma Ov0_1 a b d e:
  S0 a (2+b) 1 d e -->*
  S1 a b 4 d (2+e).
Proof.
  es.
Qed.

Lemma Ov1_1 a c d e:
  S1 (2+a) 1 (1+c) d e -->*
  S1 a 0 c d (2+e).
Proof.
  es.
Qed.

Lemma Ov2_0 c d e:
  S1 0 0 c d (2+e) -->+
  S0 (1+c) d e 2 1.
Proof.
  es.
Qed.

Lemma Ov2_1 c d e:
  S1 1 0 (1+c) d (1+e) -->+
  S0 c d e 2 1.
Proof.
  es.
Qed.

Lemma Ov2_2 c d e:
  S1 2 0 (1+c) d e -->+
  S0 c d e 1 1.
Proof.
  es.
Qed.

Lemma Ov2_3 c d e:
  S1 3 0 (3+c) d e -->+
  S0 c d (1+e) 1 1.
Proof.
  es.
Qed.

Lemma BigStep0 a b c d:
  2<=b ->
  S0 a b c (1+d) 1 -->*
  S1 a (b-1-(c mod 2)) (3+(c mod 2)) (c+d) (c/2+2+(c mod 2)).
Proof.
  intros.
  remember (c/2) as c1.
  remember (c mod 2) as c2.
  replace c with (c1*2+c2) by lia.
  destruct c2 as [|[|]]. 3: lia.
  - follow Incs0.
    replace b with (1+(b-1)) by lia.
    replace (c1*2+(1+d)) with (1+(c1*2+d)) by lia.
    follow Ov0_0.
    finish.
  - follow Incs0.
    replace b with (2+(b-2)) by lia.
    follow Ov0_1.
    finish.
Qed.

Lemma BigStep1 a b c d e:
  2<=a ->
  S1 a b (3+c) d e -->*
  S1 (a-(b mod 2)*2) 0 (b+c+(3-(b mod 2)*2)) d (e+b/2+(b mod 2)*2).
Proof.
  intros.
  remember (b/2) as b1.
  remember (b mod 2) as b2.
  replace b with (b1*2+b2) by lia.
  destruct b2 as [|[|]]. 3: lia.
  - follow Incs1.
    finish.
  - follow Incs1.
    replace a with (2+(a-2)) by lia.
    replace (b1*2+(3+c)) with (1+(b1*2+c+2)) by lia.
    follow Ov1_1.
    finish.
Qed.

Lemma BigStep2 a c d e:
  2<=e ->
  a+3<=c ->
  S1 a 0 c d e -->+
  S0 (c+(1-((a mod 4) mod 2))-a) d (a/4*3+e+(a mod 4)-2) (1+(1-(a mod 4)/2)) 1.
Proof.
  intros.
  remember (a/4) as a1.
  remember (a mod 4) as a2.
  replace a with (a1*4+a2) in * by lia.
  replace c with (a1*4+(c-a1*4)) by lia.
  destruct a2 as [|[|[|[|]]]]; cbn. 5: lia.
  - follow Incs2.
    replace (a1*3+e) with (2+(a1*3+e-2)) by lia.
    follow10 Ov2_0.
    finish.
  - follow Incs2.
    mid01 (S1 1 0 (1+(c-a1*4-1)) d (1+(a1*3+e-1))).
    1: finish.
    follow10 Ov2_1.
    finish.
  - follow Incs2.
    mid01 (S1 2 0 (1+(c-a1*4-1)) d (a1*3+e)).
    1: finish.
    follow10 Ov2_2.
    finish.
  - follow Incs2.
    mid01 (S1 3 0 (3+(c-a1*4-3)) d (a1*3+e)).
    1: finish.
    follow10 Ov2_3.
    finish.
Qed.

Lemma BigStep2' a c d e:
  2<=e ->
  a+3<=c ->
  S1 a 0 c d e -->*
  S0 (c+(1-((a mod 4) mod 2))-a) d (a/4*3+e+(a mod 4)-2) (1+(1-(a mod 4)/2)) 1.
Proof.
  intros.
  apply progress_evstep.
  apply BigStep2; auto.
Qed.

Definition P '(a,b,c,d) :=
  2<=a /\
  2<=b /\
  2<=c /\
  d<=1 /\
  a+1<=b /\
  b+5<=a+c /\
  a+c*2+14<=b*6 /\
  a+b*4+33<=c*10.

Definition S '(a,b,c,d) := S0 a b c (1+d) 1.

Lemma BigStep x:
  P x ->
  exists x',
  S x -->+ S x' /\ P x'.
Proof.
  unfold P,S.
  destruct x as [[[a b] c] d].
  intros HP.
  eexists (_,_,_,_).
  split.
  - follow BigStep0.
    1: lia.
    follow BigStep1.
    1: lia.
    apply BigStep2.
    1: lia.
    lia.
  - repeat split.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (7,9,9,O)).
  1: unfold S,S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P; lia.
  intros [[[a b] c] d].
  apply BigStep.
Qed.

End TM24.


Module TM25.
Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC1LF_1LA0RD_1LC1RE_0RC0RA_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d e :=
  0inf <* <[1;0;1]^^a <* <[1;0;0;1;0;0;1]^^b <{{D}} [0;1;1]^^c *> [0;1;1;1;1;1;1]^^d *> [0;1;1] *> ([0] ++ [1]^^10)^^e *> 0inf.

Lemma Inc1 a b c d e:
  S1 a (2+b) c d e -->*
  S1 a b (2+c) d (1+e).
Proof.
  es.
Qed.

Lemma Incs1 n a b c d e:
  S1 a (n*2+b) c d e -->*
  S1 a b (n*2+c) d (n+e).
Proof.
  gen a b c d e.
  ind n Inc1.
Qed.

Lemma Inc2 a c d e:
  S1 (4+a) 0 (4+c) d e -->*
  S1 a 0 c d (3+e).
Proof.
  es.
Qed.

Lemma Incs2 n a c d e:
  S1 (n*4+a) 0 (n*4+c) d e -->*
  S1 a 0 c d (n*3+e).
Proof.
  gen a c d e.
  ind n Inc2.
Qed.

Definition S0 a b c d e :=
  0inf <* <[1;0;1]^^a <* <[1;0;0;1;0;0;1]^^b <* <[1;0;1] <* <[1;0;0;1;0;0;0;1;0;0;1]^^c <{{D}} [0;1;1;1;1;1;1]^^d *> [0;1;1] *> ([0] ++ [1]^^10)^^e *> 0inf.

Lemma Inc0 a b c d e:
  S0 a b (2+c) d e -->*
  S0 a b c (2+d) (1+e).
Proof.
  es.
Qed.

Lemma Incs0 n a b c d e:
  S0 a b (n*2+c) d e -->*
  S0 a b c (n*2+d) (n+e).
Proof.
  gen a b c d e.
  ind n Inc0.
Qed.

Lemma Ov0_0 a b d e:
  S0 a (1+b) 0 (1+d) e -->*
  S1 a b 3 d (1+e).
Proof.
  es.
Qed.

Lemma Ov0_1 a b d e:
  S0 a (2+b) 1 d e -->*
  S1 a b 4 d (2+e).
Proof.
  es.
Qed.

Lemma Ov1_1 a c d e:
  S1 (2+a) 1 (1+c) d e -->*
  S1 a 0 c d (2+e).
Proof.
  es.
Qed.

Lemma Ov2_0 c d e:
  S1 0 0 c d (2+e) -->+
  S0 (1+c) d e 2 1.
Proof.
  es.
Qed.

Lemma Ov2_1 c d e:
  S1 1 0 (1+c) d (1+e) -->+
  S0 c d e 2 1.
Proof.
  es.
Qed.

Lemma Ov2_2 c d e:
  S1 2 0 (1+c) d e -->+
  S0 c d e 1 1.
Proof.
  es.
Qed.

Lemma Ov2_3 c d e:
  S1 3 0 (3+c) d e -->+
  S0 c d (1+e) 1 1.
Proof.
  es.
Qed.

Lemma BigStep0 a b c d:
  2<=b ->
  S0 a b c (1+d) 1 -->*
  S1 a (b-1-(c mod 2)) (3+(c mod 2)) (c+d) (c/2+2+(c mod 2)).
Proof.
  intros.
  remember (c/2) as c1.
  remember (c mod 2) as c2.
  replace c with (c1*2+c2) by lia.
  destruct c2 as [|[|]]. 3: lia.
  - follow Incs0.
    replace b with (1+(b-1)) by lia.
    replace (c1*2+(1+d)) with (1+(c1*2+d)) by lia.
    follow Ov0_0.
    finish.
  - follow Incs0.
    replace b with (2+(b-2)) by lia.
    follow Ov0_1.
    finish.
Qed.

Lemma BigStep1 a b c d e:
  2<=a ->
  S1 a b (3+c) d e -->*
  S1 (a-(b mod 2)*2) 0 (b+c+(3-(b mod 2)*2)) d (e+b/2+(b mod 2)*2).
Proof.
  intros.
  remember (b/2) as b1.
  remember (b mod 2) as b2.
  replace b with (b1*2+b2) by lia.
  destruct b2 as [|[|]]. 3: lia.
  - follow Incs1.
    finish.
  - follow Incs1.
    replace a with (2+(a-2)) by lia.
    replace (b1*2+(3+c)) with (1+(b1*2+c+2)) by lia.
    follow Ov1_1.
    finish.
Qed.

Lemma BigStep2 a c d e:
  2<=e ->
  a+3<=c ->
  S1 a 0 c d e -->+
  S0 (c+(1-((a mod 4) mod 2))-a) d (a/4*3+e+(a mod 4)-2) (1+(1-(a mod 4)/2)) 1.
Proof.
  intros.
  remember (a/4) as a1.
  remember (a mod 4) as a2.
  replace a with (a1*4+a2) in * by lia.
  replace c with (a1*4+(c-a1*4)) by lia.
  destruct a2 as [|[|[|[|]]]]; cbn. 5: lia.
  - follow Incs2.
    replace (a1*3+e) with (2+(a1*3+e-2)) by lia.
    follow10 Ov2_0.
    finish.
  - follow Incs2.
    mid01 (S1 1 0 (1+(c-a1*4-1)) d (1+(a1*3+e-1))).
    1: finish.
    follow10 Ov2_1.
    finish.
  - follow Incs2.
    mid01 (S1 2 0 (1+(c-a1*4-1)) d (a1*3+e)).
    1: finish.
    follow10 Ov2_2.
    finish.
  - follow Incs2.
    mid01 (S1 3 0 (3+(c-a1*4-3)) d (a1*3+e)).
    1: finish.
    follow10 Ov2_3.
    finish.
Qed.

Lemma BigStep2' a c d e:
  2<=e ->
  a+3<=c ->
  S1 a 0 c d e -->*
  S0 (c+(1-((a mod 4) mod 2))-a) d (a/4*3+e+(a mod 4)-2) (1+(1-(a mod 4)/2)) 1.
Proof.
  intros.
  apply progress_evstep.
  apply BigStep2; auto.
Qed.

Definition P '(a,b,c,d) :=
  2<=a /\
  2<=b /\
  2<=c /\
  d<=1 /\
  a+1<=b /\
  b+5<=a+c /\
  a+c*2+14<=b*6 /\
  a+b*4+33<=c*10.

Definition S '(a,b,c,d) := S0 a b c (1+d) 1.

Lemma BigStep x:
  P x ->
  exists x',
  S x -->+ S x' /\ P x'.
Proof.
  unfold P,S.
  destruct x as [[[a b] c] d].
  intros HP.
  eexists (_,_,_,_).
  split.
  - follow BigStep0.
    1: lia.
    follow BigStep1.
    1: lia.
    apply BigStep2.
    1: lia.
    lia.
  - repeat split.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (5,10,10,1%nat)).
  1: unfold S,S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P; lia.
  intros [[[a b] c] d].
  apply BigStep.
Qed.

End TM25.


Module TM26.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0RA_1LD0LA_1RB1LF_0RB0RC_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d e :=
  0inf <* <[1;0;1]^^a <* <[1;0;0;1;0;0;1]^^b <{{A}} [0;1;1]^^c *> [0;1;1;1;1;1;1]^^d *> [0;1;1] *> ([0] ++ [1]^^10)^^e *> 0inf.

Lemma Inc1 a b c d e:
  S1 a (2+b) c d e -->*
  S1 a b (2+c) d (1+e).
Proof.
  es.
Qed.

Lemma Incs1 n a b c d e:
  S1 a (n*2+b) c d e -->*
  S1 a b (n*2+c) d (n+e).
Proof.
  gen a b c d e.
  ind n Inc1.
Qed.

Lemma Inc2 a c d e:
  S1 (4+a) 0 (4+c) d e -->*
  S1 a 0 c d (3+e).
Proof.
  es.
Qed.

Lemma Incs2 n a c d e:
  S1 (n*4+a) 0 (n*4+c) d e -->*
  S1 a 0 c d (n*3+e).
Proof.
  gen a c d e.
  ind n Inc2.
Qed.

Definition S0 a b c d e :=
  0inf <* <[1;0;1]^^a <* <[1;0;0;1;0;0;1]^^b <* <[1;0;1] <* <[1;0;0;1;0;0;0;1;0;0;1]^^c <{{A}} [0;1;1;1;1;1;1]^^d *> [0;1;1] *> ([0] ++ [1]^^10)^^e *> 0inf.

Lemma Inc0 a b c d e:
  S0 a b (2+c) d e -->*
  S0 a b c (2+d) (1+e).
Proof.
  es.
Qed.

Lemma Incs0 n a b c d e:
  S0 a b (n*2+c) d e -->*
  S0 a b c (n*2+d) (n+e).
Proof.
  gen a b c d e.
  ind n Inc0.
Qed.

Lemma Ov0_0 a b d e:
  S0 a (1+b) 0 (1+d) e -->*
  S1 a b 3 d (1+e).
Proof.
  es.
Qed.

Lemma Ov0_1 a b d e:
  S0 a (2+b) 1 d e -->*
  S1 a b 4 d (2+e).
Proof.
  es.
Qed.

Lemma Ov1_1 a c d e:
  S1 (2+a) 1 (1+c) d e -->*
  S1 a 0 c d (2+e).
Proof.
  es.
Qed.

Lemma Ov2_0 c d e:
  S1 0 0 c d (2+e) -->+
  S0 (1+c) d e 2 1.
Proof.
  es.
Qed.

Lemma Ov2_1 c d e:
  S1 1 0 (1+c) d (1+e) -->+
  S0 c d e 2 1.
Proof.
  es.
Qed.

Lemma Ov2_2 c d e:
  S1 2 0 (1+c) d e -->+
  S0 c d e 1 1.
Proof.
  es.
Qed.

Lemma Ov2_3 c d e:
  S1 3 0 (3+c) d e -->+
  S0 c d (1+e) 1 1.
Proof.
  es.
Qed.

Lemma BigStep0 a b c d:
  2<=b ->
  S0 a b c (1+d) 1 -->*
  S1 a (b-1-(c mod 2)) (3+(c mod 2)) (c+d) (c/2+2+(c mod 2)).
Proof.
  intros.
  remember (c/2) as c1.
  remember (c mod 2) as c2.
  replace c with (c1*2+c2) by lia.
  destruct c2 as [|[|]]. 3: lia.
  - follow Incs0.
    replace b with (1+(b-1)) by lia.
    replace (c1*2+(1+d)) with (1+(c1*2+d)) by lia.
    follow Ov0_0.
    finish.
  - follow Incs0.
    replace b with (2+(b-2)) by lia.
    follow Ov0_1.
    finish.
Qed.

Lemma BigStep1 a b c d e:
  2<=a ->
  S1 a b (3+c) d e -->*
  S1 (a-(b mod 2)*2) 0 (b+c+(3-(b mod 2)*2)) d (e+b/2+(b mod 2)*2).
Proof.
  intros.
  remember (b/2) as b1.
  remember (b mod 2) as b2.
  replace b with (b1*2+b2) by lia.
  destruct b2 as [|[|]]. 3: lia.
  - follow Incs1.
    finish.
  - follow Incs1.
    replace a with (2+(a-2)) by lia.
    replace (b1*2+(3+c)) with (1+(b1*2+c+2)) by lia.
    follow Ov1_1.
    finish.
Qed.

Lemma BigStep2 a c d e:
  2<=e ->
  a+3<=c ->
  S1 a 0 c d e -->+
  S0 (c+(1-((a mod 4) mod 2))-a) d (a/4*3+e+(a mod 4)-2) (1+(1-(a mod 4)/2)) 1.
Proof.
  intros.
  remember (a/4) as a1.
  remember (a mod 4) as a2.
  replace a with (a1*4+a2) in * by lia.
  replace c with (a1*4+(c-a1*4)) by lia.
  destruct a2 as [|[|[|[|]]]]; cbn. 5: lia.
  - follow Incs2.
    replace (a1*3+e) with (2+(a1*3+e-2)) by lia.
    follow10 Ov2_0.
    finish.
  - follow Incs2.
    mid01 (S1 1 0 (1+(c-a1*4-1)) d (1+(a1*3+e-1))).
    1: finish.
    follow10 Ov2_1.
    finish.
  - follow Incs2.
    mid01 (S1 2 0 (1+(c-a1*4-1)) d (a1*3+e)).
    1: finish.
    follow10 Ov2_2.
    finish.
  - follow Incs2.
    mid01 (S1 3 0 (3+(c-a1*4-3)) d (a1*3+e)).
    1: finish.
    follow10 Ov2_3.
    finish.
Qed.

Lemma BigStep2' a c d e:
  2<=e ->
  a+3<=c ->
  S1 a 0 c d e -->*
  S0 (c+(1-((a mod 4) mod 2))-a) d (a/4*3+e+(a mod 4)-2) (1+(1-(a mod 4)/2)) 1.
Proof.
  intros.
  apply progress_evstep.
  apply BigStep2; auto.
Qed.

Definition P '(a,b,c,d) :=
  2<=a /\
  2<=b /\
  2<=c /\
  d<=1 /\
  a+1<=b /\
  b+5<=a+c /\
  a+c*2+14<=b*6 /\
  a+b*4+33<=c*10.

Definition S '(a,b,c,d) := S0 a b c (1+d) 1.

Lemma BigStep x:
  P x ->
  exists x',
  S x -->+ S x' /\ P x'.
Proof.
  unfold P,S.
  destruct x as [[[a b] c] d].
  intros HP.
  eexists (_,_,_,_).
  split.
  - follow BigStep0.
    1: lia.
    follow BigStep1.
    1: lia.
    apply BigStep2.
    1: lia.
    lia.
  - repeat split.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (2,8,13,0%nat)).
  1: unfold S,S0; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: unfold P; lia.
  intros [[[a b] c] d].
  apply BigStep.
Qed.

End TM26.


From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.

Module TM27.
Definition tm := Eval compute in (TM_from_str "1RB0LB_1LA0LC_1LB1RD_0LD0RE_1RC0RF_1RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d e :=
  0inf <{{B}} [1;0]^^a *> [0] *> [1;0]^^b *> [1] *> [1;0]^^(1+c) *> [0] *> [1;0]^^d *> [1] *> [1;0]^^(1+e) *> 0inf.

Lemma Inc1 a b c d e:
  S1 a (1+b) c (1+d) e -->*
  S1 (2+a) b (1+c) d (3+e).
Proof.
  es.
Qed.

Lemma Inc2 a c d e:
  S1 a 0 c (1+d) e -->*
  S1 (2+a) 0 c d (3+e).
Proof.
  es.
Qed.

Lemma Incs1 n a b c d e:
  S1 a (n+b) c (n+d) e -->*
  S1 (n*2+a) b (n+c) d (n*3+e).
Proof.
  gen a b c d e.
  ind n Inc1.
Qed.

Lemma Incs2 a c d e:
  S1 a 0 c d e -->*
  S1 (d*2+a) 0 c 0 (d*3+e).
Proof.
  gen a c e.
  ind d Inc2.
Qed.

Lemma Rst a c e:
  S1 a 0 c 0 e -->+
  S1 0 (2+a) 1 (2+c+e) 5.
Proof.
  unfold S1.
  do 21 (er; sr).
  es_v2.
Qed.

Definition S2 '(a,b) := S1 0 (a+0) 1 (a+b) 5.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S2 (24,21)).
  1: unfold S2,S1; esx.
  eapply progress_nonhalt_simple.
  intros [a b].
  exists (2+a*2+b*2,6+a*2+b).
  unfold S2.
  follow Incs1.
  follow Incs2.
  follow10 Rst.
  finish.
Qed.

End TM27.


Module TM28.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1LC1RA_1LA0LD_0LC0RE_1LF0RA_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hR := (B,[]).
Notation hL := (A,[1;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Definition RC0 a b c := [1;1;0]^^a *> [1;1;1;1;1;1;0;1;1;0]^^b *> [1;1]^^(1+c) *> 0inf.

Lemma RIncs0b a b c:
  sideRLs tm (hRL^^(b*2)) (RC0 a b c) (RC0 (b*2+a) 0 c).
Proof.
  unfold RC0.
  gen a.
  induction b; intros.
  1: esx.
  replace (S b*2) with (2+b*2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHb (2+a)); flia.
  esx.
Qed.

Lemma RIncs0c a c:
  sideRLs tm (hRL^^c) (RC0 a 0 c) (RC0 a 0 0).
Proof.
  unfold RC0.
  induction c.
  1: esx.
  replace (S c) with (1+c) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq IHc; flia.
  esx.
Qed.

Definition RC1 a b := [1;1;0]^^a *> [0] *> [1]^^b *> 0inf.

Lemma RIncs1 a b:
  sideRLs tm (hRL^^a) (RC1 a b) (RC1 0 (a+b)).
Proof.
  unfold RC1.
  gen b.
  induction a; intros.
  1: esx.
  replace (S a) with (1+a) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHa (S b)); flia.
  esx.
Qed.

Definition RC2 a b := [0] *> [1;1;1;0;1;1;0;1;1;1]^^a *> [1]^^b *> 0inf.

Notation hR1 := (B,<[0;0;1;0;0;1;0;0;1;0;0;1;1;1;1;1;1;1]).
Notation hRL4 := [(hR1,hL);(hR,hL);(hR,hL);(hR,hL)].
Notation hLR4 := [(hL,hR1);(hL,hR);(hL,hR);(hL,hR)].

Lemma RIncs2 a b:
  sideRLs tm (hRL4^^a) (RC2 0 b) (RC2 a b).
Proof.
  unfold RC2.
  induction a.
  1: esx.
  replace (S a) with (a+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHa.
  esx.
Qed.

Lemma RIncs a b c n:
  sideRLs tm (hRL^^(b*2+c+1+(b*2+a))++hRL4^^n) (RC0 a b c) (RC2 n ((b*2+a)+1)).
Proof.
  eapply sideRLs_trans.
  2: apply RIncs2.
  remember (b*2+a) as v1.
  repeat rewrite lpow_add.
  unfold RC0,RC2.
  eapply sideRLs_trans.
  1: eapply sideRLs_trans.
  1: eapply sideRLs_trans.
  1: apply RIncs0b.
  1: apply RIncs0c.
  2: apply RIncs1.
  subst.
  unfold RC0,RC1.
  esx.
Qed.

Definition MC0 b c :=
  <[0;0;1;0;0;1;1;1;1;1;1;1;1;1]^^b <+ <[0;1;1;1;1;1;1;1] <+ <[0;0;1;0;0;1;0;0;1;0;0;1;1;1;1;1;1;1]^^c.

Lemma MIncs0 b c:
  segRLs tm' (hLR^^(b*2)) [] (MC0 b c) (MC0 0 (b+c)).
Proof.
  unfold MC0.
  gen c.
  induction b; intros.
  1: esx.
  replace (S b*2) with (2+b*2) by lia.
  rewrite lpow_add.
  eapply @segRLs_trans with (ls2:=[]).
  2: applys_eq (IHb (1+c)); flia.
  esx.
Qed.

Definition MC1 c :=
  <[0;0;1;0;0;1;0;0;1;0;0;1;1;1;1;1;1;1]^^c.

Lemma MIncs1 n c:
  segRLs tm' (hLR^^n) (hLR^^n) (MC1 c) (MC1 c).
Proof.
  unfold MC1.
  eapply segRLs_wall.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma MIncs1' c:
  segRLs tm' (hLR4^^c) (hLR^^(c*4)) (MC1 c) (MC1 0).
Proof.
  unfold MC1.
  induction c.
  1: esx.
  replace (S c*4) with (4+c*4) by lia.
  replace (S c) with (1+c) by lia.
  do 2 rewrite lpow_add.
  eapply segRLs_trans.
  2: apply IHc.
  esx.
Qed.

Notation hL2 := (C,[0;1;1;0;1;0;1;0;1;0]).
Notation hLR2 := [(hL2,hR)].
Lemma MInc01 c:
  segRLs tm' hLR hLR2 (MC0 0 c) (MC1 c).
Proof.
  unfold MC0,MC1.
  esx.
Qed.

Lemma MIncs b n:
  segRLs tm' (hLR^^(b*2+1+n)++hLR4^^b) (hLR2++hLR^^(n+b*4)) (MC0 b 0) (MC1 0).
Proof.
  repeat rewrite lpow_add.
  rewrite app_assoc.
  eapply segRLs_trans.
  1: eapply segRLs_trans.
  1: eapply @segRLs_trans with (ls2:=[]).
  1: apply MIncs0.
  1: apply MInc01.
  1: rewrite Nat.add_0_r.
  1: apply MIncs1.
  apply MIncs1'.
Qed.

Definition LC0 a :=
  0inf <* <[0;0;1;1;1]^^a. 

Definition LC0' a :=
  0inf <* <[0;0;1;1;1]^^a <* <[0;0;1;1;1;1;1;1;1;1;1].

Definition LC1 a b :=
  0inf <* <[0;0;1;1;1]^^a <* <[1] <* <[1;1;0;0;1;0;0;1;1;1;1;1;1;1]^^b. 

Definition LC1' a b :=
  0inf <* <[0;0;1;1;1]^^a <* <[1] <* <[1;1;0;0;1;0;0;1;1;1;1;1;1;1]^^b <* <[1;1] <* <[0;0;1;0;0;1;0;0;1;0;0;1;1;1;1;1;1;1].

Lemma LInc0 a:
  sideRLs tm' hLR2 (LC0 (1+a)) (LC1 a 1).
Proof.
  unfold LC0,LC1.
  esx.
Qed.

Lemma LInc0' a:
  sideRLs tm' hLR2 (LC0' a) (LC1' a 0).
Proof.
  unfold LC0',LC1'.
  esx.
Qed.

Lemma LIncs1 n a b:
  sideRLs tm' (hLR^^(n*2)) (LC1 (n*2+a) b) (LC1 a (n+b)).
Proof.
  unfold LC1.
  gen b.
  induction n; intros.
  1: esx.
  replace (S n*2) with (2+n*2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S b)); flia.
  esx.
Qed.

Lemma LIncs1' n a b:
  sideRLs tm' (hLR^^(n*2)) (LC1' (n*2+a) b) (LC1' a (n+b)).
Proof.
  unfold LC1'.
  gen b.
  induction n; intros.
  1: esx.
  replace (S n*2) with (2+n*2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHn (S b)); flia.
  esx.
Qed.

Definition LC2 a b :=
  0inf <* <[0;0;1;1;1]^^a <* <[0;0;1] <* <[1;1;0;0;1;0;0;1;1;1;1;1;1;1]^^b. 

Definition LC2' a b :=
  0inf <* <[0;0;1;1;1]^^a <* <[0;0;1] <* <[1;1;0;0;1;0;0;1;1;1;1;1;1;1]^^b <* <[1;1] <* <[0;0;1;0;0;1;0;0;1;0;0;1;1;1;1;1;1;1].

Definition LC2x a b :=
  0inf <* <[0;0;1;1;1]^^a <* <[1;1;1;1] <* <[1;1;0;0;1;0;0;1;1;1;1;1;1;1]^^b. 

Definition LC2x' a b :=
  0inf <* <[0;0;1;1;1]^^a <* <[1;1;1;1] <* <[1;1;0;0;1;0;0;1;1;1;1;1;1;1]^^b <* <[1;1] <* <[0;0;1;0;0;1;0;0;1;0;0;1;1;1;1;1;1;1].

Lemma LIncs2 a b:
  sideRLs tm' (hLR^^a) (LC1 0 b) (LC2 a b).
Proof.
  unfold LC1,LC2.
  induction a.
  1: esx.
  replace (S a) with (a+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq IHa; flia.
  esx.
Qed.

Lemma LIncs2' a b:
  sideRLs tm' (hLR^^a) (LC1' 0 b) (LC2' a b).
Proof.
  unfold LC1',LC2'.
  induction a.
  1: esx.
  replace (S a) with (a+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq IHa; flia.
  esx.
Qed.

Lemma LIncs2x a b:
  sideRLs tm' (hLR^^a) (LC1 1 b) (LC2x a b).
Proof.
  unfold LC1,LC2x.
  induction a.
  1: esx.
  replace (S a) with (a+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq IHa; flia.
  esx.
Qed.

Lemma LIncs2x' a b:
  sideRLs tm' (hLR^^a) (LC1' 1 b) (LC2x' a b).
Proof.
  unfold LC1',LC2x'.
  induction a.
  1: esx.
  replace (S a) with (a+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq IHa; flia.
  esx.
Qed.

Lemma LIncs n m:
  sideRLs tm' (hLR2++hLR^^(n*2+m)) (LC0 (1+(n*2+0))) (LC2 m (n+1)).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply LInc0.
  eapply sideRLs_trans.
  1: apply LIncs1.
  apply LIncs2.
Qed.

Lemma LIncs' n m:
  sideRLs tm' (hLR2++hLR^^(n*2+m)) (LC0' ((n*2+0))) (LC2' m (n+0)).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply LInc0'.
  eapply sideRLs_trans.
  1: apply LIncs1'.
  apply LIncs2'.
Qed.

Lemma LIncsx n m:
  sideRLs tm' (hLR2++hLR^^(n*2+m)) (LC0 (1+(n*2+1))) (LC2x m (n+1)).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply LInc0.
  eapply sideRLs_trans.
  1: apply LIncs1.
  apply LIncs2x.
Qed.

Lemma LIncsx' n m:
  sideRLs tm' (hLR2++hLR^^(n*2+m)) (LC0' ((n*2+1))) (LC2x' m (n+0)).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply LInc0'.
  eapply sideRLs_trans.
  1: apply LIncs1'.
  apply LIncs2x'.
Qed.


Definition S0 a b c d :=
  LC0 a <* MC0 b 0 {{{ (hR,R) }}} RC0 4 c d.

Definition S0' a b c d :=
  LC0' a <* MC0 b 0 {{{ (hR,R) }}} RC0 4 c d.

Definition S0x a b c d :=
  LC0 a <* MC0 b 0 {{{ (hL,L) }}} RC0 4 c d.

Definition S0x' a b c d :=
  LC0' a <* MC0 b 0 {{{ (hL,L) }}} RC0 4 c d.

Lemma init:
  c0 -->* S0x 21 5 5 5.
Proof.
  unfold S0x.
  esx.
Qed.

Lemma lrcons_hLR_hLR4 n m:
  lrcons hR (hLR^^n++hLR4^^m) hL = (hRL^^S n++hRL4^^m).
Proof.
  induction n.
  - cbn.
    induction m.
    1: trivial.
    cbn.
    rewrite <-IHm.
    trivial.
  - cbn in *.
    rewrite <-IHn.
    trivial.
Qed.

Lemma S0_nxt_1 a b c d:
  1<=a ->
  a*2<=b*2+c*4+d+3 ->
  b*2+1<=c*4+d+4 ->
  S0 (1+a*2) b c d -->+
  S0 (4+(c*4+d+3+b*2-a*2)) (a-1) b (3+c).
Proof.
  intros.
  unfold S0.
  epose proof (RIncs 4 c d b) as HR.
  epose proof (MIncs b (c*4+d+4-(b*2+1))) as HM.
  rewrite Nat.add_comm,Nat.sub_add in HM by lia.
  epose proof (LIncs a (c*4+d+3+b*2-a*2)) as HL.
  eassert (HL':_). {
    eapply segRLs_sideRLs_concat.
    2: apply HL.
    applys_eq HM; flia.
  }
  clear HM HL.
  replace (c*2+d+1+(c*2+4)) with (S(c*4+d+4)) in * by lia.
  epose proof (sideRLs_concat HL') as I1.
  rewrite lrcons_hLR_hLR4 in I1.
  specialize (I1 HR).
  rewrite Nat.add_0_r in *.
  follow10 I1.
  cbn.
  unfold LC2.
  remember (c*4+d+3+b*2-a*2) as v1.
  remember (a-1) as a'.
  replace a with (1+a') in * by lia.
  es.
Qed.

Lemma S0_nxt_0 a b c d:
  1<=a ->
  a*2<=b*2+c*4+d+3 ->
  b*2+1<=c*4+d+4 ->
  S0 (1+(a*2+1)) b c d -->+
  S0' (2+(c*4+d+3+b*2-a*2)) (a-1) b (3+c).
Proof.
  intros.
  unfold S0.
  epose proof (RIncs 4 c d b) as HR.
  epose proof (MIncs b (c*4+d+4-(b*2+1))) as HM.
  rewrite Nat.add_comm,Nat.sub_add in HM by lia.
  epose proof (LIncsx a (c*4+d+3+b*2-a*2)) as HL.
  eassert (HL':_). {
    eapply segRLs_sideRLs_concat.
    2: apply HL.
    applys_eq HM; flia.
  }
  clear HM HL.
  replace (c*2+d+1+(c*2+4)) with (S(c*4+d+4)) in * by lia.
  epose proof (sideRLs_concat HL') as I1.
  rewrite lrcons_hLR_hLR4 in I1.
  specialize (I1 HR).
  follow10 I1.
  cbn.
  unfold LC2x.
  remember (c*4+d+3+b*2-a*2) as v1.
  remember (a-1) as a'.
  replace a with (1+a') in * by lia.
  es.
Qed.

Lemma S0'_nxt_0 a b c d:
  1<=a ->
  a*2<=b*2+c*4+d+3 ->
  b*2+1<=c*4+d+4 ->
  S0' (a*2) b c d -->+
  S0x (6+(c*4+d+3+b*2-a*2)) (a-1) b (3+c).
Proof.
  intros.
  unfold S0'.
  epose proof (RIncs 4 c d b) as HR.
  epose proof (MIncs b (c*4+d+4-(b*2+1))) as HM.
  rewrite Nat.add_comm,Nat.sub_add in HM by lia.
  epose proof (LIncs' a (c*4+d+3+b*2-a*2)) as HL.
  eassert (HL':_). {
    eapply segRLs_sideRLs_concat.
    2: apply HL.
    applys_eq HM; flia.
  }
  clear HM HL.
  replace (c*2+d+1+(c*2+4)) with (S(c*4+d+4)) in * by lia.
  epose proof (sideRLs_concat HL') as I1.
  rewrite lrcons_hLR_hLR4 in I1.
  specialize (I1 HR).
  rewrite Nat.add_0_r in *.
  follow10 I1.
  cbn.
  unfold LC2.
  remember (c*4+d+3+b*2-a*2) as v1.
  remember (a-1) as a'.
  replace a with (1+a') in * by lia.
  es.
Qed.

Lemma S0'_nxt_1 a b c d:
  1<=a ->
  a*2<=b*2+c*4+d+3 ->
  b*2+1<=c*4+d+4 ->
  S0' (a*2+1) b c d -->+
  S0x' (4+(c*4+d+3+b*2-a*2)) (a-1) b (3+c).
Proof.
  intros.
  unfold S0'.
  epose proof (RIncs 4 c d b) as HR.
  epose proof (MIncs b (c*4+d+4-(b*2+1))) as HM.
  rewrite Nat.add_comm,Nat.sub_add in HM by lia.
  epose proof (LIncsx' a (c*4+d+3+b*2-a*2)) as HL.
  eassert (HL':_). {
    eapply segRLs_sideRLs_concat.
    2: apply HL.
    applys_eq HM; flia.
  }
  clear HM HL.
  replace (c*2+d+1+(c*2+4)) with (S(c*4+d+4)) in * by lia.
  epose proof (sideRLs_concat HL') as I1.
  rewrite lrcons_hLR_hLR4 in I1.
  specialize (I1 HR).
  rewrite Nat.add_0_r in *.
  follow10 I1.
  cbn.
  unfold LC2.
  remember (c*4+d+3+b*2-a*2) as v1.
  remember (a-1) as a'.
  replace a with (1+a') in * by lia.
  es.
Qed.

Lemma lcons_hLR_hLR4 n m:
  (hLR^^n++hLR4^^m,hL) = lcons hL (hRL^^n++hRL4^^m).
Proof.
  induction n.
  - cbn.
    induction m.
    1: trivial.
    cbn.
    rewrite <-IHm.
    trivial.
  - cbn in *.
    rewrite <-IHn.
    trivial.
Qed.

Lemma S0x_nxt_1 a b c d:
  1<=a ->
  a*2<=b*2+c*4+d+4 ->
  b*2+1<=c*4+d+5 ->
  S0x (1+a*2) b c d -->+
  S0 (4+(c*4+d+4+b*2-a*2)) (a-1) b (3+c).
Proof.
  intros.
  unfold S0x.
  epose proof (RIncs 4 c d b) as HR.
  epose proof (MIncs b ((c*4+d+5)-(b*2+1))) as HM.
  rewrite Nat.add_comm,Nat.sub_add in HM by lia.
  epose proof (LIncs a (c*4+d+4+b*2-a*2)) as HL.
  eassert (HL':_). {
    eapply segRLs_sideRLs_concat.
    2: apply HL.
    applys_eq HM; flia.
  }
  clear HM HL.
  replace (c*2+d+1+(c*2+4)) with (c*4+d+5) in * by lia.
  eassert (I1:_). {
    eapply sideRLs_concat_v2_L.
    4: apply HR.
    3: apply HL'.
    2: rewrite Nat.add_comm; cbn; congruence.
    rewrite lcons_hLR_hLR4; reflexivity.
  }
  rewrite Nat.add_0_r in *.
  follow10 I1.
  cbn.
  unfold LC2.
  remember (c*4+d+4+b*2-a*2) as v1.
  remember (a-1) as a'.
  replace a with (1+a') in * by lia.
  es.
Qed.

Lemma S0x_nxt_0 a b c d:
  1<=a ->
  a*2<=b*2+c*4+d+4 ->
  b*2+1<=c*4+d+5 ->
  S0x (1+(a*2+1)) b c d -->+
  S0' (2+(c*4+d+4+b*2-a*2)) (a-1) b (3+c).
Proof.
  intros.
  unfold S0x.
  epose proof (RIncs 4 c d b) as HR.
  epose proof (MIncs b ((c*4+d+5)-(b*2+1))) as HM.
  rewrite Nat.add_comm,Nat.sub_add in HM by lia.
  epose proof (LIncsx a (c*4+d+4+b*2-a*2)) as HL.
  eassert (HL':_). {
    eapply segRLs_sideRLs_concat.
    2: apply HL.
    applys_eq HM; flia.
  }
  clear HM HL.
  replace (c*2+d+1+(c*2+4)) with (c*4+d+5) in * by lia.
  eassert (I1:_). {
    eapply sideRLs_concat_v2_L.
    4: apply HR.
    3: apply HL'.
    2: rewrite Nat.add_comm; cbn; congruence.
    rewrite lcons_hLR_hLR4; reflexivity.
  }
  follow10 I1.
  cbn.
  unfold LC2.
  remember (c*4+d+4+b*2-a*2) as v1.
  remember (a-1) as a'.
  replace a with (1+a') in * by lia.
  es.
Qed.

Lemma S0x'_nxt_0 a b c d:
  1<=a ->
  a*2<=b*2+c*4+d+4 ->
  b*2+1<=c*4+d+5 ->
  S0x' (a*2) b c d -->+
  S0x (6+(c*4+d+4+b*2-a*2)) (a-1) b (3+c).
Proof.
  intros.
  unfold S0x'.
  epose proof (RIncs 4 c d b) as HR.
  epose proof (MIncs b ((c*4+d+5)-(b*2+1))) as HM.
  rewrite Nat.add_comm,Nat.sub_add in HM by lia.
  epose proof (LIncs' a (c*4+d+4+b*2-a*2)) as HL.
  eassert (HL':_). {
    eapply segRLs_sideRLs_concat.
    2: apply HL.
    applys_eq HM; flia.
  }
  clear HM HL.
  replace (c*2+d+1+(c*2+4)) with (c*4+d+5) in * by lia.
  eassert (I1:_). {
    eapply sideRLs_concat_v2_L.
    4: apply HR.
    3: apply HL'.
    2: rewrite Nat.add_comm; cbn; congruence.
    rewrite lcons_hLR_hLR4; reflexivity.
  }
  rewrite Nat.add_0_r in *.
  follow10 I1.
  cbn.
  unfold LC2.
  remember (c*4+d+4+b*2-a*2) as v1.
  remember (a-1) as a'.
  replace a with (1+a') in * by lia.
  es.
Qed.

Lemma S0x'_nxt_1 a b c d:
  1<=a ->
  a*2<=b*2+c*4+d+4 ->
  b*2+1<=c*4+d+5 ->
  S0x' (a*2+1) b c d -->+
  S0x' (4+(c*4+d+4+b*2-a*2)) (a-1) b (3+c).
Proof.
  intros.
  unfold S0x'.
  epose proof (RIncs 4 c d b) as HR.
  epose proof (MIncs b ((c*4+d+5)-(b*2+1))) as HM.
  rewrite Nat.add_comm,Nat.sub_add in HM by lia.
  epose proof (LIncsx' a (c*4+d+4+b*2-a*2)) as HL.
  eassert (HL':_). {
    eapply segRLs_sideRLs_concat.
    2: apply HL.
    applys_eq HM; flia.
  }
  clear HM HL.
  replace (c*2+d+1+(c*2+4)) with (c*4+d+5) in * by lia.
  eassert (I1:_). {
    eapply sideRLs_concat_v2_L.
    4: apply HR.
    3: apply HL'.
    2: rewrite Nat.add_comm; cbn; congruence.
    rewrite lcons_hLR_hLR4; reflexivity.
  }
  rewrite Nat.add_0_r in *.
  follow10 I1.
  cbn.
  unfold LC2.
  remember (c*4+d+4+b*2-a*2) as v1.
  remember (a-1) as a'.
  replace a with (1+a') in * by lia.
  es.
Qed.

Definition S1 '(a,b,c,d,t',tx) :=
match t',tx with
| O,O => S0 (1+a) b c d
| O,S _ => S0x (1+a) b c d
| S _,O => S0' a b c d
| S _,S _ => S0x' a b c d
end.

Lemma BigStep a b c d t' tx:
  2<=a ->
  a<=b*2+c*4+d+3 ->
  b*2+1<=c*4+d+4 ->
  t'<=1 ->
  tx<=1 ->
  S1 (a,b,c,d,t',tx) -->+
  S1 (3+t'*2+tx+(b*2+c*4+d+3-a),a/2-1,b,3+c,a mod 2,t').
Proof.
  intros.
  remember (a/2) as a'.
  remember (a mod 2) as am2.
  replace a with (a'*2+am2) in * by lia.
  unfold S1.
  destruct am2 as [|[|]]. 3: lia.
  - destruct t',tx; rewrite Nat.add_0_r.
    applys_eq (S0_nxt_1 a'); flia.
    applys_eq (S0x_nxt_1 a'); flia.
    applys_eq (S0'_nxt_0 a'); flia.
    applys_eq (S0x'_nxt_0 a'); flia.
  - destruct t',tx.
    applys_eq (S0_nxt_0 a'); flia.
    applys_eq (S0x_nxt_0 a'); flia.
    applys_eq (S0'_nxt_1 a'); flia.
    applys_eq (S0x'_nxt_1 a'); flia.
Qed.

Opaque S1.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 (20,5,5,5,0,1)%nat).
  1: apply init.
  do 6
  (eapply multistep_nonhalt;
  [ apply progress_evstep,BigStep; try lia | ]; cbn).
  eapply progress_nonhalt_cond with (P:=fun '(a,b,c,d,t',tx) =>
  2<=a /\ a<=b*2+c*4+d+3 /\ b*2+1<=c*4+d+4 /\ t'<=1 /\ tx<=1 /\ c*3+d+6<=a*2+b*2 /\ a<=b*4+c+8 /\ a<=b+c*7+d*2 /\ b+c*4+d+7<=a*3 /\ c*4+d*6<=a*3+b*10+8 /\ a*7<=b*4+c*22+d*6+19 /\ c*22+d*7+32<=a*9+b*8 /\ a*5+b*4+11<=c*29+d*9 /\ a>=20 /\ b>=20 /\ c>=20 /\ d>=20).
  2: lia.
  intros [[[[[a b] c] d] t] tx] HP.
  eexists; split.
  1: apply BigStep; lia.
  repeat split; try lia.
Qed.

End TM28.


Module TM29.
Definition tm := Eval compute in (TM_from_str "1RB1LC_0RC1RB_1LD0LE_1RE---_0LF0RE_1LA1LF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b :=
  0inf <{{F}} [1]^^a *> [0;0;1] *> [0;1;1]^^b *> 0inf.

Lemma Inc0 a b:
  S0 a (1+b) -->*
  S0 (5+a) b.
Proof.
  es.
Qed.

Lemma Incs0 a b:
  S0 a b -->*
  S0 (b*5+a) 0.
Proof.
  gen a.
  ind b Inc0.
Qed.

Lemma Ov2 a:
  S0 (5+a*3) 0 -->+
  S0 (a*5+15) 0.
Proof.
  mid10 (S0 15 a).
  1: es.
  follow Incs0.
  finish.
Qed.

Lemma Ov0 a:
  S0 (a*3) 0 -->+
  S0 (a*5+7) 0.
Proof.
  mid10 (S0 2 (1+a)).
  1: es.
  follow Incs0.
  finish.
Qed.

Definition S1 a b c :=
  0inf <* [1] <* [0]^^a <{{F}} [1]^^b *> [0;0;1] *> [0;1;1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (2+a) b (1+c) -->*
  S1 a (5+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n*2+a) b (n+c) -->*
  S1 a (n*5+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov1' b c:
  S1 1 b c -->*
  S1 (3+b) 0 c.
Proof.
  es.
Qed.

Lemma Ov0' b c:
  S1 0 b (1+c) -->*
  S0 (6+b) c.
Proof.
  es.
Qed.

Lemma Ov1 a:
  169<=a ->
  S0 (1+a*3) 0 -->+
  S0 (a*5-319) 0.
Proof.
  intros.
  mid10 (S1 1 2 (1+a)).
  1: es.
  follow Ov1'.
  mid (S1 (2*2+1) 0 (2+(a-1))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (6*2+1) 0 (6+(a-7))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (16*2+1) 0 (16+(a-23))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (41*2+1) 0 (41+(a-64))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (104*2+0) 0 (104+(1+(a-169)))).
  1: finish.
  follow Incs1.
  follow Ov0'.
  follow Incs0.
  finish.
Qed.

Definition S' n := S0 n 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 532).
  1: eapply without_counter with (n:=N.to_nat 92485).
  1: eapply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
  eapply progress_nonhalt_cond with (P:=fun n=>n>=510).
  2: lia.
  intros n HP.
  remember (n mod 3) as n1.
  unfold S'.
  destruct n1 as [|[|[|]]].
  4: lia.
  - replace n with (n/3*3) by lia.
    eexists; split.
    1: apply Ov0.
    lia.
  - replace n with (1+n/3*3) by lia.
    eexists; split.
    1: apply Ov1; lia.
    lia.
  - replace n with (5+(n/3-1)*3) by lia.
    eexists; split.
    1: apply Ov2.
    lia.
Qed.

End TM29.


Module TM30.
Definition tm := Eval compute in (TM_from_str "1LB0LC_1RC---_0LD0RC_1LE1LD_1RF1LA_0RA1RF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b :=
  0inf <{{D}} [1]^^a *> [0;0;1] *> [0;1;1]^^b *> 0inf.

Lemma Inc0 a b:
  S0 a (1+b) -->*
  S0 (5+a) b.
Proof.
  es.
Qed.

Lemma Incs0 a b:
  S0 a b -->*
  S0 (b*5+a) 0.
Proof.
  gen a.
  ind b Inc0.
Qed.

Lemma Ov2 a:
  S0 (5+a*3) 0 -->+
  S0 (a*5+15) 0.
Proof.
  mid10 (S0 15 a).
  1: es.
  follow Incs0.
  finish.
Qed.

Lemma Ov0 a:
  S0 (a*3) 0 -->+
  S0 (a*5+7) 0.
Proof.
  mid10 (S0 2 (1+a)).
  1: es.
  follow Incs0.
  finish.
Qed.

Definition S1 a b c :=
  0inf <* [1] <* [0]^^a <{{D}} [1]^^b *> [0;0;1] *> [0;1;1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (2+a) b (1+c) -->*
  S1 a (5+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n*2+a) b (n+c) -->*
  S1 a (n*5+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov1' b c:
  S1 1 b c -->*
  S1 (3+b) 0 c.
Proof.
  es.
Qed.

Lemma Ov0' b c:
  S1 0 b (1+c) -->*
  S0 (6+b) c.
Proof.
  es.
Qed.

Lemma Ov1 a:
  169<=a ->
  S0 (1+a*3) 0 -->+
  S0 (a*5-319) 0.
Proof.
  intros.
  mid10 (S1 1 2 (1+a)).
  1: es.
  follow Ov1'.
  mid (S1 (2*2+1) 0 (2+(a-1))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (6*2+1) 0 (6+(a-7))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (16*2+1) 0 (16+(a-23))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (41*2+1) 0 (41+(a-64))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (104*2+0) 0 (104+(1+(a-169)))).
  1: finish.
  follow Incs1.
  follow Ov0'.
  follow Incs0.
  finish.
Qed.

Definition S' n := S0 n 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 1041).
  1: eapply without_counter with (n:=N.to_nat 616734).
  1: eapply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
  eapply progress_nonhalt_cond with (P:=fun n=>n>=510).
  2: lia.
  intros n HP.
  remember (n mod 3) as n1.
  unfold S'.
  destruct n1 as [|[|[|]]].
  4: lia.
  - replace n with (n/3*3) by lia.
    eexists; split.
    1: apply Ov0.
    lia.
  - replace n with (1+n/3*3) by lia.
    eexists; split.
    1: apply Ov1; lia.
    lia.
  - replace n with (5+(n/3-1)*3) by lia.
    eexists; split.
    1: apply Ov2.
    lia.
Qed.

End TM30.


Module TM31.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC0RB_1LD1LC_1RE1LF_0RF1RE_1LA0LB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b :=
  0inf <{{C}} [1]^^a *> [0;0;1] *> [0;1;1]^^b *> 0inf.

Lemma Inc0 a b:
  S0 a (1+b) -->*
  S0 (5+a) b.
Proof.
  es.
Qed.

Lemma Incs0 a b:
  S0 a b -->*
  S0 (b*5+a) 0.
Proof.
  gen a.
  ind b Inc0.
Qed.

Lemma Ov2 a:
  S0 (5+a*3) 0 -->+
  S0 (a*5+15) 0.
Proof.
  mid10 (S0 15 a).
  1: es.
  follow Incs0.
  finish.
Qed.

Lemma Ov0 a:
  S0 (a*3) 0 -->+
  S0 (a*5+7) 0.
Proof.
  mid10 (S0 2 (1+a)).
  1: es.
  follow Incs0.
  finish.
Qed.

Definition S1 a b c :=
  0inf <* [1] <* [0]^^a <{{C}} [1]^^b *> [0;0;1] *> [0;1;1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (2+a) b (1+c) -->*
  S1 a (5+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n*2+a) b (n+c) -->*
  S1 a (n*5+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov1' b c:
  S1 1 b c -->*
  S1 (3+b) 0 c.
Proof.
  es.
Qed.

Lemma Ov0' b c:
  S1 0 b (1+c) -->*
  S0 (6+b) c.
Proof.
  es.
Qed.

Lemma Ov1 a:
  169<=a ->
  S0 (1+a*3) 0 -->+
  S0 (a*5-319) 0.
Proof.
  intros.
  mid10 (S1 1 2 (1+a)).
  1: es.
  follow Ov1'.
  mid (S1 (2*2+1) 0 (2+(a-1))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (6*2+1) 0 (6+(a-7))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (16*2+1) 0 (16+(a-23))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (41*2+1) 0 (41+(a-64))).
  1: finish.
  follow Incs1.
  follow Ov1'.
  mid (S1 (104*2+0) 0 (104+(1+(a-169)))).
  1: finish.
  follow Incs1.
  follow Ov0'.
  follow Incs0.
  finish.
Qed.

Definition S' n := S0 n 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 562).
  1: eapply without_counter with (n:=N.to_nat 114973).
  1: eapply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
  eapply progress_nonhalt_cond with (P:=fun n=>n>=510).
  2: lia.
  intros n HP.
  remember (n mod 3) as n1.
  unfold S'.
  destruct n1 as [|[|[|]]].
  4: lia.
  - replace n with (n/3*3) by lia.
    eexists; split.
    1: apply Ov0.
    lia.
  - replace n with (1+n/3*3) by lia.
    eexists; split.
    1: apply Ov1; lia.
    lia.
  - replace n with (5+(n/3-1)*3) by lia.
    eexists; split.
    1: apply Ov2.
    lia.
Qed.

End TM31.


Module TM32.
Definition tm := Eval compute in (TM_from_str "1LB1LE_0LC1LF_1RD1RC_1LA0RD_0RC0RF_---0LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b :=
  0inf <{{A}} [1;0;1;0;1;0;1] *> [1;1;1]^^a *> [0] *> [1;0]^^b *> 0inf.

Lemma Inc0 a b:
  S0 a (4+b) -->+
  S0 (5+a) b.
Proof.
  es.
Qed.

Lemma Ov00 a:
  S0 (4+a*2) 0 -->+
  S0 10 (a*3).
Proof.
  es.
Qed.

Lemma Ov01 a:
  S0 (a*2) 1 -->+
  S0 2 (3+a*3).
Proof.
  es.
Qed.

Lemma Ov03 a:
  S0 (a*2) 3 -->+
  S0 10 (1+a*3).
Proof.
  es.
Qed.

Lemma Ov10 a:
  S0 (a*2+1) 0 -->+
  S0 4 (a*3).
Proof.
  es.
Qed.

Lemma Ov12 a:
  S0 (a*2+1) 2 -->+
  S0 2 (5+a*3).
Proof.
  es.
Qed.

Lemma Ov13 a:
  S0 (a*2+1) 3 -->+
  S0 4 (7+a*3).
Proof.
  es.
Qed.

Definition S1 l a b c :=
  l <* [0]^^(1+a) <{{B}} [1;1;1]^^b *> [0] *> [1;0]^^c *> 0inf.

Lemma Inc1 l a b c:
  S1 l (2+a) b (2+c) -->*
  S1 l a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c:
  S1 l (n*2+a) b (n*2+c) -->*
  S1 l a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov1a b c:
  S1 (0inf <* [1]^^5 <* [0]^^4 <* [1]^^7) 1 (1+b) (1+c) -->*
  S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^6) (2+b*3) 1 c.
Proof. es. Qed.

Lemma Ov0b b c k:
  S1 (0inf <* [1]^^k <* [0]^^4 <* [1]^^6) 0 (1+b) (1+c) -->*
  S1 (0inf <* [1]^^k <* [0]^^4 <* [1]^^7) (1+b*3) 1 c.
Proof. es. Qed.

Lemma Ov1c b c:
  S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^7) 1 (1+b) (1+c) -->*
  S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^6) (2+b*3) 1 c.
Proof. es. Qed.

Lemma Ov1d b c:
  S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^7) 1 b c -->*
  S1 0inf 0 (12+b) c.
Proof. es. Qed.


Lemma Ov11 a:
  273<=a ->
  S0 (a*2+1) 1 -->+
  S1 0inf 0 559 (a*3-817).
Proof.
  intros.
  unfold S0.
  st.
  do 4 (er; sr).
  do 132 step1.
  mid (S1 (0inf <* [1]^^5 <* [0]^^4 <* [1]^^7) 7 1 (1+a*3)).
  1: es.
  mid (S1 (0inf <* [1]^^5 <* [0]^^4 <* [1]^^7) (3*2+1) 1 (3*2+(1+(a*3-6)))).
  1: finish.
  follow Incs1.
  follow (Ov1a 6).
  mid (S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^6) (10*2+0) 1 (10*2+(1+(a*3-27)))).
  1: finish.
  follow Incs1.
  follow (Ov0b 20).
  mid (S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^7) (30*2+1) 1 (30*2+(1+(a*3-88)))).
  1: finish.
  follow Incs1.
  follow (Ov1c 60).
  mid (S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^6) (91*2+0) 1 (91*2+(1+(a*3-271)))).
  1: finish.
  follow Incs1.
  follow (Ov0b 182).
  mid (S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^7) (273*2+1) 1 (273*2+((a*3-817)))).
  1: finish.
  follow Incs1.
  follow Ov1d.
  finish.
Qed.

Lemma Ov02 a:
  273<=a ->
  S0 (a*2) 2 -->+
  S1 0inf 0 559 (a*3-818).
Proof.
  intros.
  unfold S0.
  st.
  do 4 (er; sr).
  do 132 step1.
  mid (S1 (0inf <* [1]^^5 <* [0]^^4 <* [1]^^7) 7 1 (a*3)).
  1: es.
  mid (S1 (0inf <* [1]^^5 <* [0]^^4 <* [1]^^7) (3*2+1) 1 (3*2+(1+(a*3-7)))).
  1: finish.
  follow Incs1.
  follow (Ov1a 6).
  mid (S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^6) (10*2+0) 1 (10*2+(1+(a*3-28)))).
  1: finish.
  follow Incs1.
  follow (Ov0b 20).
  mid (S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^7) (30*2+1) 1 (30*2+(1+(a*3-89)))).
  1: finish.
  follow Incs1.
  follow (Ov1c 60).
  mid (S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^6) (91*2+0) 1 (91*2+(1+(a*3-272)))).
  1: finish.
  follow Incs1.
  follow (Ov0b 182).
  mid (S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^7) (273*2+1) 1 (273*2+((a*3-818)))).
  1: finish.
  follow Incs1.
  follow Ov1d.
  finish.
Qed.

Lemma Inc1' b c:
  S1 0inf 0 b (2+c) -->+
  S1 0inf 0 (2+b) c.
Proof.
  es.
Qed.

Lemma Rst00 b:
  S1 0inf 0 (2+b*2) 0 -->+
  S1 0inf 0 2 (2+b*3).
Proof.
  es.
Qed.

Lemma Rst01 b:
  S1 0inf 0 (2+b*2) 1 -->+
  S0 5 (b*3).
Proof.
  es.
Qed.

Lemma Rst10 b:
  S1 0inf 0 (5+b*2) 0 -->+
  S0 5 (2+b*3).
Proof.
  es.
Qed.

Lemma Rst11 b:
  S1 0inf 0 (1+b*2) 1 -->+
  S1 0inf 0 2 (3+b*3).
Proof.
  es.
Qed.

Inductive Config :=
| cfg0(a b:nat)
| cfg1(a b:nat).

Definition cfg(x:Config) :=
match x with
| cfg0 a b => S0 a b
| cfg1 a b => S1 0inf 0 a b
end.

Definition P(x:Config):Prop :=
match x with
| cfg0 a b => a*3+b*2>=1900
| cfg1 a b => a*3+b*2>=1900
end.

Ltac flia :=
  lia || (f_equal; flia).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=cfg (cfg0 647 3)).
  1: eapply without_counter with (n:=N.to_nat 961886).
  1: eapply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
  eapply progress_nonhalt_cond with (P:=P); unfold P.
  2: lia.
  intros [a b|a b] HP; cbn[cfg].
  - destruct b as [|[|[|[|]]]].
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov00 (a/2-2)); flia.
        lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov10 (a/2)); flia.
        lia.
    }
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov01 (a/2)); flia.
        lia.
      - eexists (cfg1 _ _); split.
        1: applys_eq (Ov11 (a/2)); flia.
        lia.
    }
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg1 _ _); split.
        1: applys_eq (Ov02 (a/2)); flia.
        lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov12 (a/2)); flia.
        lia.
    }
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov03 (a/2)); flia.
        lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov13 (a/2)); flia.
        lia.
    }
    {
      eexists (cfg0 _ _); split.
      1: apply Inc0.
      lia.
    }
  - destruct b as [|[|]].
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg1 _ _); split.
        1: applys_eq (Rst00 (a/2-1)); flia.
        lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Rst10 (a/2-2)); flia.
        lia.
    }
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Rst01 (a/2-1)); flia.
        lia.
      - eexists (cfg1 _ _); split.
        1: applys_eq (Rst11 (a/2)); flia.
        lia.
    }
    {
      eexists (cfg1 _ _); split.
      1: apply Inc1'.
      lia.
    }
Qed.

End TM32.


Module TM33.
Definition tm := Eval compute in (TM_from_str "1LB0RA_1LC1LE_0LD1LF_1RA1RD_0RD0RF_---0LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b :=
  0inf <{{B}} [1;0;1;0;1;0;1] *> [1;1;1]^^a *> [0] *> [1;0]^^b *> 0inf.

Lemma Inc0 a b:
  S0 a (4+b) -->+
  S0 (5+a) b.
Proof.
  es.
Qed.

Lemma Ov00 a:
  S0 (4+a*2) 0 -->+
  S0 10 (a*3).
Proof.
  es.
Qed.

Lemma Ov01 a:
  S0 (a*2) 1 -->+
  S0 2 (3+a*3).
Proof.
  es.
Qed.

Lemma Ov03 a:
  S0 (a*2) 3 -->+
  S0 10 (1+a*3).
Proof.
  es.
Qed.

Lemma Ov10 a:
  S0 (a*2+1) 0 -->+
  S0 4 (a*3).
Proof.
  es.
Qed.

Lemma Ov12 a:
  S0 (a*2+1) 2 -->+
  S0 2 (5+a*3).
Proof.
  es.
Qed.

Lemma Ov13 a:
  S0 (a*2+1) 3 -->+
  S0 4 (7+a*3).
Proof.
  es.
Qed.

Definition S1 l a b c :=
  l <* [0]^^(1+a) <{{C}} [1;1;1]^^b *> [0] *> [1;0]^^c *> 0inf.

Lemma Inc1 l a b c:
  S1 l (2+a) b (2+c) -->*
  S1 l a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c:
  S1 l (n*2+a) b (n*2+c) -->*
  S1 l a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov1a b c:
  S1 (0inf <* [1]^^5 <* [0]^^4 <* [1]^^7) 1 (1+b) (1+c) -->*
  S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^6) (2+b*3) 1 c.
Proof. es. Qed.

Lemma Ov0b b c k:
  S1 (0inf <* [1]^^k <* [0]^^4 <* [1]^^6) 0 (1+b) (1+c) -->*
  S1 (0inf <* [1]^^k <* [0]^^4 <* [1]^^7) (1+b*3) 1 c.
Proof. es. Qed.

Lemma Ov1c b c:
  S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^7) 1 (1+b) (1+c) -->*
  S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^6) (2+b*3) 1 c.
Proof. es. Qed.

Lemma Ov1d b c:
  S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^7) 1 b c -->*
  S1 0inf 0 (12+b) c.
Proof. es. Qed.


Lemma Ov11 a:
  273<=a ->
  S0 (a*2+1) 1 -->+
  S1 0inf 0 559 (a*3-817).
Proof.
  intros.
  unfold S0.
  st.
  do 4 (er; sr).
  do 132 step1.
  mid (S1 (0inf <* [1]^^5 <* [0]^^4 <* [1]^^7) 7 1 (1+a*3)).
  1: es.
  mid (S1 (0inf <* [1]^^5 <* [0]^^4 <* [1]^^7) (3*2+1) 1 (3*2+(1+(a*3-6)))).
  1: finish.
  follow Incs1.
  follow (Ov1a 6).
  mid (S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^6) (10*2+0) 1 (10*2+(1+(a*3-27)))).
  1: finish.
  follow Incs1.
  follow (Ov0b 20).
  mid (S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^7) (30*2+1) 1 (30*2+(1+(a*3-88)))).
  1: finish.
  follow Incs1.
  follow (Ov1c 60).
  mid (S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^6) (91*2+0) 1 (91*2+(1+(a*3-271)))).
  1: finish.
  follow Incs1.
  follow (Ov0b 182).
  mid (S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^7) (273*2+1) 1 (273*2+((a*3-817)))).
  1: finish.
  follow Incs1.
  follow Ov1d.
  finish.
Qed.

Lemma Ov02 a:
  273<=a ->
  S0 (a*2) 2 -->+
  S1 0inf 0 559 (a*3-818).
Proof.
  intros.
  unfold S0.
  st.
  do 4 (er; sr).
  do 132 step1.
  mid (S1 (0inf <* [1]^^5 <* [0]^^4 <* [1]^^7) 7 1 (a*3)).
  1: es.
  mid (S1 (0inf <* [1]^^5 <* [0]^^4 <* [1]^^7) (3*2+1) 1 (3*2+(1+(a*3-7)))).
  1: finish.
  follow Incs1.
  follow (Ov1a 6).
  mid (S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^6) (10*2+0) 1 (10*2+(1+(a*3-28)))).
  1: finish.
  follow Incs1.
  follow (Ov0b 20).
  mid (S1 (0inf <* [1]^^9 <* [0]^^4 <* [1]^^7) (30*2+1) 1 (30*2+(1+(a*3-89)))).
  1: finish.
  follow Incs1.
  follow (Ov1c 60).
  mid (S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^6) (91*2+0) 1 (91*2+(1+(a*3-272)))).
  1: finish.
  follow Incs1.
  follow (Ov0b 182).
  mid (S1 (0inf <* [1]^^15 <* [0]^^4 <* [1]^^7) (273*2+1) 1 (273*2+((a*3-818)))).
  1: finish.
  follow Incs1.
  follow Ov1d.
  finish.
Qed.

Lemma Inc1' b c:
  S1 0inf 0 b (2+c) -->+
  S1 0inf 0 (2+b) c.
Proof.
  es.
Qed.

Lemma Rst00 b:
  S1 0inf 0 (2+b*2) 0 -->+
  S1 0inf 0 2 (2+b*3).
Proof.
  es.
Qed.

Lemma Rst01 b:
  S1 0inf 0 (2+b*2) 1 -->+
  S0 5 (b*3).
Proof.
  es.
Qed.

Lemma Rst10 b:
  S1 0inf 0 (5+b*2) 0 -->+
  S0 5 (2+b*3).
Proof.
  es.
Qed.

Lemma Rst11 b:
  S1 0inf 0 (1+b*2) 1 -->+
  S1 0inf 0 2 (3+b*3).
Proof.
  es.
Qed.

Inductive Config :=
| cfg0(a b:nat)
| cfg1(a b:nat).

Definition cfg(x:Config) :=
match x with
| cfg0 a b => S0 a b
| cfg1 a b => S1 0inf 0 a b
end.

Definition P(x:Config):Prop :=
match x with
| cfg0 a b => a*3+b*2>=1900
| cfg1 a b => a*3+b*2>=1900
end.

Ltac flia :=
  lia || (f_equal; flia).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=cfg (cfg0 274 615)).
  1: eapply without_counter with (n:=N.to_nat 956340).
  1: eapply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
  eapply progress_nonhalt_cond with (P:=P); unfold P.
  2: lia.
  intros [a b|a b] HP; cbn[cfg].
  - destruct b as [|[|[|[|]]]].
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov00 (a/2-2)); flia.
        lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov10 (a/2)); flia.
        lia.
    }
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov01 (a/2)); flia.
        lia.
      - eexists (cfg1 _ _); split.
        1: applys_eq (Ov11 (a/2)); flia.
        lia.
    }
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg1 _ _); split.
        1: applys_eq (Ov02 (a/2)); flia.
        lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov12 (a/2)); flia.
        lia.
    }
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov03 (a/2)); flia.
        lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Ov13 (a/2)); flia.
        lia.
    }
    {
      eexists (cfg0 _ _); split.
      1: apply Inc0.
      lia.
    }
  - destruct b as [|[|]].
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg1 _ _); split.
        1: applys_eq (Rst00 (a/2-1)); flia.
        lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Rst10 (a/2-2)); flia.
        lia.
    }
    {
      assert ((a mod 2 = 0\/a mod 2 = 1)%nat) as [E|E] by lia.
      - eexists (cfg0 _ _); split.
        1: applys_eq (Rst01 (a/2-1)); flia.
        lia.
      - eexists (cfg1 _ _); split.
        1: applys_eq (Rst11 (a/2)); flia.
        lia.
    }
    {
      eexists (cfg1 _ _); split.
      1: apply Inc1'.
      lia.
    }
Qed.

End TM33.


From BusyCoq Require Import ES_v3.

Module TM34.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC0RE_1RE0LD_0LC0LB_1RA0RF_1RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S' '(a,b) := 0inf <* <[0;1;1]^^a <* <[0] <* <[0;1;1]^^b {{B}}> 0inf.

Open Scope string.

Lemma Ov0 b:
  S' (O,b) -->+
  S' (430+b,6).
Proof.
  unfold S'.
  es' b.
Qed.

Lemma Ov1 b:
  S' (1%nat,b) -->+
  S' (3+b,6).
Proof.
  es.
Qed.

Lemma Ov2 b:
  S' (2,b) -->+
  S' (5+b,2).
Proof.
  es.
Qed.

Lemma Ov3 b:
  S' (3,b) -->+
  S' (O,8+b).
Proof.
  es.
Qed.

Lemma Inc a b:
  S' (4+a,b) -->+
  S' (a,7+b).
Proof.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,3)).
  1: esx.
  eapply progress_nonhalt_simple.
  intros [a b].
  destruct a as [|[|[|[|]]]]; eexists.
  - apply Ov0.
  - apply Ov1.
  - apply Ov2.
  - apply Ov3.
  - apply Inc.
Qed.

End TM34.


Module TM35.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC1RB_1LD0RA_1RA0LE_0LD0LC_1RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S' '(a,b) := 0inf <* <[0;1;1]^^a <* <[0] <* <[0;1;1]^^b {{C}}> 0inf.

Open Scope string.

Lemma Ov0 b:
  S' (O,b) -->+
  S' (430+b,6).
Proof.
  unfold S'.
  es' b.
Qed.

Lemma Ov1 b:
  S' (1%nat,b) -->+
  S' (3+b,6).
Proof.
  es.
Qed.

Lemma Ov2 b:
  S' (2,b) -->+
  S' (5+b,2).
Proof.
  es.
Qed.

Lemma Ov3 b:
  S' (3,b) -->+
  S' (O,8+b).
Proof.
  es.
Qed.

Lemma Inc a b:
  S' (4+a,b) -->+
  S' (a,7+b).
Proof.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,1%nat)).
  1: esx.
  eapply progress_nonhalt_simple.
  intros [a b].
  destruct a as [|[|[|[|]]]]; eexists.
  - apply Ov0.
  - apply Ov1.
  - apply Ov2.
  - apply Ov3.
  - apply Inc.
Qed.

End TM35.


Module TM36.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC0RF_1RD1RC_1LA0RB_0LA0LD_1RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S' '(a,b) := 0inf <* <[0;1;1]^^a <* <[0] <* <[0;1;1]^^b {{D}}> 0inf.

Open Scope string.

Lemma Ov0 b:
  S' (O,b) -->+
  S' (430+b,6).
Proof.
  unfold S'.
  es' b.
Qed.

Lemma Ov1 b:
  S' (1%nat,b) -->+
  S' (3+b,6).
Proof.
  es.
Qed.

Lemma Ov2 b:
  S' (2,b) -->+
  S' (5+b,2).
Proof.
  es.
Qed.

Lemma Ov3 b:
  S' (3,b) -->+
  S' (O,8+b).
Proof.
  es.
Qed.

Lemma Inc a b:
  S' (4+a,b) -->+
  S' (a,7+b).
Proof.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,2)).
  1: esx.
  eapply progress_nonhalt_simple.
  intros [a b].
  destruct a as [|[|[|[|]]]]; eexists.
  - apply Ov0.
  - apply Ov1.
  - apply Ov2.
  - apply Ov3.
  - apply Inc.
Qed.

End TM36.


Module TM37.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LF_1RE0RD_1RB---_1RA1RE_0LB0LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S' '(a,b) := 0inf <* <[0;1;1]^^a <* <[0] <* <[0;1;1]^^b {{A}}> 0inf.

Open Scope string.

Lemma Ov0 b:
  S' (O,b) -->+
  S' (430+b,6).
Proof.
  unfold S'.
  es' b.
Qed.

Lemma Ov1 b:
  S' (1%nat,b) -->+
  S' (3+b,6).
Proof.
  es.
Qed.

Lemma Ov2 b:
  S' (2,b) -->+
  S' (5+b,2).
Proof.
  es.
Qed.

Lemma Ov3 b:
  S' (3,b) -->+
  S' (O,8+b).
Proof.
  es.
Qed.

Lemma Inc a b:
  S' (4+a,b) -->+
  S' (a,7+b).
Proof.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,O)).
  1: esx.
  eapply progress_nonhalt_simple.
  intros [a b].
  destruct a as [|[|[|[|]]]]; eexists.
  - apply Ov0.
  - apply Ov1.
  - apply Ov2.
  - apply Ov3.
  - apply Inc.
Qed.

End TM37.


Module TM38.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LF_1RD0RA_1RE1RD_1LB0RC_0LB0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S' '(a,b) := 0inf <* <[0;1;1]^^a <* <[0] <* <[0;1;1]^^b {{E}}> 0inf.

Open Scope string.

Lemma Ov0 b:
  S' (O,b) -->+
  S' (430+b,6).
Proof.
  unfold S'.
  es' b.
Qed.

Lemma Ov1 b:
  S' (1%nat,b) -->+
  S' (3+b,6).
Proof.
  es.
Qed.

Lemma Ov2 b:
  S' (2,b) -->+
  S' (5+b,2).
Proof.
  es.
Qed.

Lemma Ov3 b:
  S' (3,b) -->+
  S' (O,8+b).
Proof.
  es.
Qed.

Lemma Inc a b:
  S' (4+a,b) -->+
  S' (a,7+b).
Proof.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,5)).
  1: esx.
  eapply progress_nonhalt_simple.
  intros [a b].
  destruct a as [|[|[|[|]]]]; eexists.
  - apply Ov0.
  - apply Ov1.
  - apply Ov2.
  - apply Ov3.
  - apply Inc.
Qed.

End TM38.


Module TM39.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0RF_1LD0RB_0LE0LC_0RA1LF_0RD0LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S' '(a,b) := 0inf <* <[0;1;1;0]^^a <* <[0;1;0;1]^^b {{C}}> 0inf.

Open Scope string.

Lemma Ov0 b:
  S' (O,6+b) -->+
  S' (b,125).
Proof.
  unfold S'.
  es' b.
Qed.

Lemma Ov1 b:
  S' (1%nat,b) -->+
  S' (O,2+b).
Proof.
  es.
Qed.

Lemma Inc a b:
  S' (2+a,b) -->+
  S' (a,3+b).
Proof.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,7)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(a,b) => a+b>=6).
  2: lia.
  intros [a b] HP.
  destruct a as [|[|]]; eexists; (split; [|shelve]).
  - applys_eq (Ov0 (b-6)); flia.
  - apply Ov1.
  - apply Inc.
  Unshelve.
  all: lia.
Qed.

End TM39.


Module TM40.
Definition tm := Eval compute in (TM_from_str "1LB0RE_0LC0LA_0RD1LF_1LE---_1RA0RF_0RB0LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S' '(a,b) := 0inf <* <[0;1;1;0]^^a <* <[0;1;0;1]^^b {{A}}> 0inf.

Open Scope string.

Lemma Ov0 b:
  S' (O,6+b) -->+
  S' (b,125).
Proof.
  unfold S'.
  es' b.
Qed.

Lemma Ov1 b:
  S' (1%nat,b) -->+
  S' (O,2+b).
Proof.
  es.
Qed.

Lemma Inc a b:
  S' (2+a,b) -->+
  S' (a,3+b).
Proof.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,14)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(a,b) => a+b>=6).
  2: lia.
  intros [a b] HP.
  destruct a as [|[|]]; eexists; (split; [|shelve]).
  - applys_eq (Ov0 (b-6)); flia.
  - apply Ov1.
  - apply Inc.
  Unshelve.
  all: lia.
Qed.

End TM40.


Module TM41.
Definition tm := Eval compute in (TM_from_str "1RB0RB_0RC0LF_0RD0RA_0LE---_1LE0LA_1LF1RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[]).
Notation hL := (F,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma RIncs n r:
  sideRLs tm (hRL^^(2^n-1)) ([1;1;1]^^n*>r) ([1;1;0]^^n*>r).
Proof.
  induction n.
  1: esx.
  cbn[Nat.pow].
  cbn[lpow].
  repeat rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  applys_eq (segRLs_addmul_v2 2 1 (2^n-1) 1 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Lemma LIncs l n:
  sideRLs (flip tm) (hLR^^n) (l<*<[1;0;0]) (l<*<[1;0;0]).
Proof.
  eapply sideRLs_wall; esx.
Qed.

Lemma LIncs_1 l n:
  sideRLs (flip tm) (hLR^^n) (l<*<[1;0;0;0;0;0]) (l<*<[1;0;0;0;0;0]).
Proof.
  eapply sideRLs_wall; esx.
Qed.

Lemma Incs l n r:
  l <* <[1;0;0] {{C}}> [1;1;1]^^n *> r -->*
  l <* <[1;0;0] {{C}}> [1;1;0]^^n *> r.
Proof.
  apply (sideRLs_concat_1 (RIncs n r) (LIncs l _)).
Qed.

Definition S1 l m n :=
  l <* [0] <* [1]^^m <* <[1;0;0] {{C}}> [1;1;1]^^n *> 0inf.

Lemma Inc1 l m n:
  S1 l (2+m) n -->*
  S1 l m (1+n).
Proof.
  unfold S1.
  follow Incs.
  es.
Qed.

Lemma Incs1 l m n m0:
  S1 l (m*2+m0) n -->*
  S1 l m0 (m+n).
Proof.
  gen n m0.
  ind m Inc1.
Qed.

Lemma init:
  c0 -->*
  S1 (0inf<<1<<1<<0<<0<<1<<0<<0) 23 2.
Proof.
  unfold S1.
  esx.
Qed.

Ltac follow'_0 H :=
  let I1:=fresh "I" in
  epose proof H as I1;
  (eapply evstep_progress_trans || eapply evstep_trans); [| follow I1; clear I1]; [es | ].

Tactic Notation "follow'" uconstr(H) := follow'_0 H.

Lemma Ov_0100_1 l n:
  S1 (l<<0<<1<<0<<0) 1 n -->*
  S1 (l<<1<<0<<0) (n*3+2) 2.
Proof.
  unfold S1.
  follow Incs.
  follow' (sideRLs_concat_1 (RIncs (1+n) 0inf) (LIncs_1 _ _)).
  es.
Qed.

Lemma Ov_0_0 l n:
  S1 (l<<0) 0 (2+n) -->*
  S1 (l<<0<<1<<0<<0) (n*3+2) 2.
Proof.
  unfold S1.
  follow Incs.
  es.
Qed.

Lemma Ov_101100_1 l n:
  halts tm (S1 (l<<1<<0<<1<<1<<0<<0) 1 n).
Proof.
  eapply halts_evstep.
  2:{
  unfold S1.
  follow Incs.
  follow' (sideRLs_concat_1 (RIncs (1+n) 0inf) (LIncs_1 _ _)).
  finish.
  }
  esx.
Qed.

From BusyCoq Require Import NatMod_v2.

Import NatModTactics.

Ltac follow'' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac mstep :=
  follow'' Incs1; rw_all;
  match goal with
  | |- S1 (_<<0<<1<<0<<0) (_ .[Nconst 1]) _ -->* _ => follow'' Ov_0100_1
  | |- S1 (_<<0) (_ .[Nconst 0]) _ -->* _ => follow'' Ov_0_0
  end; rw_all.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
    follow init...
    repeat mstep.
    follow'' Incs1.
    finish.
  }
  apply Ov_101100_1.
Time Qed.

End TM41.


