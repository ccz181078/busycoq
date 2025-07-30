From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import ZifyNat.

Open Scope list.


Ltac flia :=
  lia || (f_equal; flia).


Ltac solve_steps :=
repeat rewrite <-Str_app_assoc;
repeat rewrite simpl_directed_head_l;
repeat rewrite simpl_directed_head_r;
repeat rewrite l_const0_app_nil;
repeat rewrite r_const0_app_nil;
repeat rewrite config_to_cconfig;
repeat rewrite simpl_directed_head_l;
repeat rewrite simpl_directed_head_r;
repeat rewrite l_const0_app_nil;
repeat rewrite r_const0_app_nil;
repeat rewrite config_to_cconfig;
apply cconfig_evstep_dec_spec with (n:=1000000);
vm_compute;
reflexivity.

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


