From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Ltac er := execute_with_rotate.
Ltac sr := use_shift_rule; simpl_rotate.

Ltac unfold_config_expr x :=
match x with
| ?a ?b => unfold_config_expr a
| ?a => try (unfold a)
end.

Ltac unfold_config :=
match goal with
| |- ?a -[_]->* ?b =>
  unfold_config_expr a;
  unfold_config_expr b
| |- ?a -[_]->+ ?b =>
  unfold_config_expr a;
  unfold_config_expr b
end.

Ltac es :=
  intros;
  unfold_config;
  repeat
  (rewrite lpow_add ||
  rewrite Str_app_assoc ||
  rewrite lpow_mul);
  simpl_tape;
  execute_with_shift_rule.

Ltac ind n H :=
  induction n as [|n IHn]; intros;
  [ finish |
    cbn[Nat.add];
    follow H;
    follow IHn;
    finish ].

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

Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1RC0LD_1LD0RA_1LF0LE_1LB1LC_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c :=
  const 0 <* [0;0;1]^^a <* [1;0;1]^^b <* [1] <{{B}} [1;0;0]^^2 *> [1;0;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 a b (1+c) -->*
  S0 (1+a) (1+b) c.
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <* [0;0;1]^^a <* [0;1;1]^^2 {{A}}> [0;0] *> [1;0;0]^^(b*2) *> [1;0;1]^^c *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 (c+a) (c+b) 0.
Proof.
  gen a b.
  ind c Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition config a := S0 (3+a) a 0.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config 3).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_simple.
  intros a.
  exists (5+a*2).
  unfold config.
  mid10 (S1 (2+a) 0 (2+a)).
  1: unfold S0,S1; es.
  follow (Inc1s 0 0 0 (2+a)).
  mid (S0 3 0 (5+a*2)).
  1: unfold S0,S1; es.
  follow Inc0s.
  finish.
Qed.

End TM7.

Module TM8.
Definition tm := Eval compute in (TM_from_str "1LB0RE_1LC0LF_1LD---_1RA0LB_1RD0RD_1LD1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;0;1]^^a <* [1;0;1]^^b <{{B}} [0] *> [1;0;0]^^2 *> [1;0;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 a b (1+c) -->*
  S0 (1+a) (1+b) c.
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <* [0;0;1]^^a <* [0;1;1]^^2 <* [1;1] {{A}}> [1;0;0]^^(b*2) *> [1;0;1]^^c *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 (c+a) (c+b) 0.
Proof.
  gen a b.
  ind c Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition config a := S0 (3+a) a 0.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config 1).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_simple.
  intros a.
  exists (5+a*2).
  unfold config.
  mid10 (S1 (2+a) 0 (2+a)).
  1: unfold S0,S1; es.
  follow (Inc1s 0 0 0 (2+a)).
  mid (S0 3 0 (5+a*2)).
  1: unfold S0,S1; es.
  follow Inc0s.
  finish.
Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1LB0RE_0LC1LF_1LD---_1RA0LB_0RD1RD_1LD1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;0;1]^^a <* [1;0;1]^^b <{{B}} [0] *> [1;1;0]^^2 *> [1;1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 a b (1+c) -->*
  S0 (1+a) (1+b) c.
Proof.
  es.
Qed.

Definition S1 a b c :=
  const 0 <* [0;0;1]^^a <* [0;1;1]^^2 <* [1;1] {{A}}> [1;1;0]^^(b*2) *> [1;1;1]^^c *> const 0.

Lemma Inc1 a b c:
  S1 (1+a) b (1+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Inc0s a b c:
  S0 a b c -->*
  S0 (c+a) (c+b) 0.
Proof.
  gen a b.
  ind c Inc0.
Qed.

Lemma Inc1s a b c n:
  S1 (n+a) b (n+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition config a := S0 (3+a) a 0.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config 1).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_simple.
  intros a.
  exists (5+a*2).
  unfold config.
  mid10 (S1 (2+a) 0 (2+a)).
  1: unfold S0,S1; es.
  follow (Inc1s 0 0 0 (2+a)).
  mid (S0 3 0 (5+a*2)).
  1: unfold S0,S1; es.
  follow Inc0s.
  finish.
Qed.

End TM9.


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

Module TM14.
Definition tm := Eval compute in (TM_from_str "1RB1RD_0LC1LE_1LD1LB_1RA1LF_---0RC_0LD0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c d e :=
  const 0 <* [1;1]^^a <{{F}} [1] *> [0;1]^^b *> [1;0]^^c *> [1;1;0]^^d *> [1;0]^^e *> [1;1] *> const 0.

Lemma Inc0 a b c d e:
  S0 (1+a) b c d e -->*
  S0 a b (1+c) d e.
Proof.
  es.
Qed.

Lemma Inc0s a b c d e:
  S0 a b c d e -->*
  S0 0 b (a+c) d e.
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Ov0 b c d e:
  S0 0 b c (1+d) e -->*
  S0 (2+b) c 2 d e.
Proof.
  unfold S0.
  es.
Qed.

Lemma IncOv0 b c d e:
  S0 0 b c (2+d) e -->*
  S0 0 (4+b) (4+c) d e.
Proof.
  follow Ov0.
  follow Inc0s.
  follow Ov0.
  follow Inc0s.
  finish.
Qed.

Lemma IncOv0s b c d e n:
  S0 0 b c (n*2+d) e -->*
  S0 0 (n*4+b) (n*4+c) d e.
Proof.
  gen b c d e.
  ind n IncOv0.
Qed.

Definition S1 a b c :=
  const 0 <* [1;1]^^a <{{F}} [1] *> [0;1]^^b *> [1;0]^^(1+c) *> const 0.

Lemma Ov0' b c e:
  S0 0 b c 0 e -->*
  S1 (2+b) (c+e) 1.
Proof.
  es.
Qed.

Lemma Inc1 a b c:
  S1 (1+a) b c -->*
  S1 a b (1+c).
Proof.
  es.
Qed.

Lemma Inc1s a b c:
  S1 a b c -->*
  S1 0 b (a+c).
Proof.
  gen b c.
  ind a Inc1.
Qed.

Lemma Ov1_2 b c:
  S1 0 (2+b*3) c -->+
  S0 2 1 1 (b*2+1) (1+c).
Proof.
  es.
Qed.

Lemma BigStep b c:
  S1 0 (2+b*3) c -->+
  S1 0 (6+b*4+c) (6+b*4).
Proof.
  follow10 Ov1_2.
  follow Inc0s.
  follow IncOv0s.
  follow Ov0.
  follow Inc0s.
  follow Ov0'.
  follow Inc1s.
  finish.
Qed.

Definition config n := S1 0 (2+(7*2^n-2)*3) (14*2^n-2).

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config O).
  1: unfold config,S1; solve_init.
  apply progress_nonhalt_simple.
  intros n.
  exists (S n).
  unfold config.
  follow10 BigStep.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n).
  finish.
Qed.

End TM14.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB0RE_0LB0RC_1LD---_1LE0LA_1RA0RF_1RE0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c d e :=
  const 0 <* [1]^^a <* [0] <{{E}} [1] *> [1;0]^^b *> [1;1] *> [0]^^c *> [0;1]^^d *> [1;0]^^e *> const 0.

Lemma Inc0 a b c d e:
  S0 a (1+b) c d e -->*
  S0 (1+a) b (1+c) d e.
Proof.
  es.
Qed.

Definition S1 a b c d e :=
  const 0 <* [1]^^(a) <{{D}} [1;0]^^b *> [0]^^(c) *> [0;1]^^d *> [1;0]^^e *> const 0.

Lemma Inc1 a b c d e:
  S1 (3+a) b (3+c) d e -->*
  S1 a (3+b) c d e.
Proof.
  es.
Qed.

Definition S2 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <* [0] <{{E}} [1] *> [1;0]^^d *> [1;1] *> [0]^^e *> [1]^^f *> const 0.

Lemma Inc2 a b c d e f:
  S2 a b c (1+d) e f -->*
  S2 a b (1+c) d (1+e) f.
Proof.
  es.
Qed.

Definition S3 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <{{D}} [1] *> [0;1]^^(d) *> [0]^^e *> [1]^^f *> const 0.

Lemma Inc3 a b c d e f:
  S3 a b (3+c) d (3+e) f -->*
  S3 a b c (3+d) e f.
Proof.
  es.
Qed.

Definition S2' a b c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <* [0] <{{E}} [1] *> [1;0]^^d *> [1;1] *> const 0.

Lemma Inc2' a b c d:
  S2' a b c (1+d) -->*
  S2' a b (1+c) d.
Proof.
  es.
Qed.

Definition S3' a b c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <{{D}} [1] *> [0;1]^^(d) *> const 0.

Lemma Inc3' a b c d:
  S3' a b (3+c) d -->*
  S3' a b c (3+d).
Proof.
  es.
Qed.

Lemma Inc0s a b c d e:
  S0 a b c d e -->*
  S0 (b+a) 0 (b+c) d e.
Proof.
  gen a c.
  ind b Inc0.
Qed.

Lemma Inc1s a b c d e n:
  S1 (n*3+a) b (n*3+c) d e -->*
  S1 a (n*3+b) c d e.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2s a b c d e f:
  S2 a b c d e f -->*
  S2 a b (d+c) 0 (d+e) f.
Proof.
  gen c e.
  ind d Inc2.
Qed.

Lemma Inc3s a b c d e f n:
  S3 a b (n*3+c) d (n*3+e) f -->*
  S3 a b c (n*3+d) e f.
Proof.
  gen c d e.
  ind n Inc3.
Qed.

Lemma Inc2s' a b c d:
  S2' a b c d -->*
  S2' a b (d+c) 0.
Proof.
  gen c.
  ind d Inc2'.
Qed.

Lemma Inc3s' a b c d n:
  S3' a b (n*3+c) d -->*
  S3' a b c (n*3+d).
Proof.
  gen c d.
  ind n Inc3'.
Qed.


Lemma Incs2323 a b d:
  S2 a (1+b) 0 (1+d*3) 1 1 -->*
  S3' a b 0 (4+d*3).
Proof.
  follow Inc2s.
  mid (S3 a (1+b) (1+d*3) 1 (3+d*3) 1); [es|].
  follow (Inc3s a (1+b) 1 1 3 1 d).
  mid (S2' a b 0 (3+d*3)); [es|].
  follow Inc2s'.
  mid (S3' a b (3+d*3) 1); [es|].
  follow (Inc3s' a b 0 1 (1+d)).
  finish.
Qed.

Lemma Incs0101 b d e:
  S0 1 (1+b*3) 0 (1+d) e -->*
  S1 3 (2+b*3) 3 d e.
Proof.
  follow Inc0s.
  mid (S1 (2+b*3) 2 (1+b*3) (1+d) e); [es|].
  follow (Inc1s 2 2 1 (1+d) e b).
  mid (S0 0 (3+b*3) 0 d e); [es|].
  follow Inc0s.
  mid (S1 (3+b*3) 2 (3+b*3) d e); [es|].
  follow (Inc1s 3 2 3 d e b).
  finish.
Qed.

Definition S4 b d e :=
  S0 1 (1+b*3) 0 (1+d*3) (2+e*3).

Lemma Inc4 b d e:
  S4 b (1+d) e -->*
  S4 (1+b) d (1+e).
Proof.
  unfold S4.
  follow Incs0101.
  mid (S2 (4+b*3) (1+(1+d*3)) 0 (1+e*3) 1 1); [es|].
  follow Incs2323.
  es.
Qed.

Lemma Inc4s b d e:
  S4 b d e -->*
  S4 (d+b) 0 (d+e).
Proof.
  gen b e.
  ind d Inc4.
Qed.

Definition S5 a b c :=
  const 0 <* [1]^^a <* [0] <{{E}} [1] *> [1;0]^^b *> [1;1] *> [0]^^c *> [1] *> const 0.

Lemma Inc5 a b c:
  S5 a (1+b) c -->*
  S5 (1+a) b (1+c).
Proof.
  es.
Qed.

Lemma Inc5s a b c:
  S5 a b c -->*
  S5 (b+a) 0 (b+c).
Proof.
  gen a c.
  ind b Inc5.
Qed.

Definition S6 a b c :=
  const 0 <* [1]^^(a) <{{D}} [1;0]^^b *> [0]^^(c) *> [1] *> const 0.

Lemma Inc6 a b c:
  S6 (3+a) b (3+c) -->*
  S6 a (3+b) c.
Proof.
  es.
Qed.

Lemma Inc6s a b c n:
  S6 (n*3+a) b (n*3+c) -->*
  S6 a (n*3+b) c.
Proof.
  gen a b c.
  ind n Inc6.
Qed.

Definition config n :=
  S6 1 (2+n*3) 1.

Lemma BigStep n:
  config n -->+
  config (2+n*2).
Proof.
  unfold config.
  mid10 (S4 0 (n) 0); [unfold S4; es|].
  follow Inc4s.
  unfold S4.
  follow Incs0101.
  mid (S5 1 (6+n*3+n*3) 1); [es|].
  mid (S5 1 ((2+n*2)*3) 1); [finish|].
  remember (2+n*2) as n0.
  follow Inc5s.
  mid (S6 (1+n0*3) 2 (1+n0*3)); [es|].
  follow (Inc6s 1 2 1 n0).
  finish.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config O).
  1: unfold config,S6; solve_init.
  apply progress_nonhalt_simple.
  intros n.
  eexists.
  apply BigStep.
Qed.

End TM15.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC0LD_1RD0RE_0RA0RC_1RC0LA_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c d e :=
  const 0 <* [1]^^a <* [0] <{{C}} [1] *> [1;0]^^b *> [1;1] *> [0]^^c *> [0;1]^^d *> [1;0]^^e *> const 0.

Lemma Inc0 a b c d e:
  S0 a (1+b) c d e -->*
  S0 (1+a) b (1+c) d e.
Proof.
  es.
Qed.

Definition S1 a b c d e :=
  const 0 <* [1]^^(a) <{{B}} [1;0]^^b *> [0]^^(c) *> [0;1]^^d *> [1;0]^^e *> const 0.

Lemma Inc1 a b c d e:
  S1 (3+a) b (3+c) d e -->*
  S1 a (3+b) c d e.
Proof.
  es.
Qed.

Definition S2 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <* [0] <{{C}} [1] *> [1;0]^^d *> [1;1] *> [0]^^e *> [1]^^f *> const 0.

Lemma Inc2 a b c d e f:
  S2 a b c (1+d) e f -->*
  S2 a b (1+c) d (1+e) f.
Proof.
  es.
Qed.

Definition S3 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <{{B}} [1] *> [0;1]^^(d) *> [0]^^e *> [1]^^f *> const 0.

Lemma Inc3 a b c d e f:
  S3 a b (3+c) d (3+e) f -->*
  S3 a b c (3+d) e f.
Proof.
  es.
Qed.

Definition S2' a b c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <* [0] <{{C}} [1] *> [1;0]^^d *> [1;1] *> const 0.

Lemma Inc2' a b c d:
  S2' a b c (1+d) -->*
  S2' a b (1+c) d.
Proof.
  es.
Qed.

Definition S3' a b c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <{{B}} [1] *> [0;1]^^(d) *> const 0.

Lemma Inc3' a b c d:
  S3' a b (3+c) d -->*
  S3' a b c (3+d).
Proof.
  es.
Qed.

Lemma Inc0s a b c d e:
  S0 a b c d e -->*
  S0 (b+a) 0 (b+c) d e.
Proof.
  gen a c.
  ind b Inc0.
Qed.

Lemma Inc1s a b c d e n:
  S1 (n*3+a) b (n*3+c) d e -->*
  S1 a (n*3+b) c d e.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2s a b c d e f:
  S2 a b c d e f -->*
  S2 a b (d+c) 0 (d+e) f.
Proof.
  gen c e.
  ind d Inc2.
Qed.

Lemma Inc3s a b c d e f n:
  S3 a b (n*3+c) d (n*3+e) f -->*
  S3 a b c (n*3+d) e f.
Proof.
  gen c d e.
  ind n Inc3.
Qed.

Lemma Inc2s' a b c d:
  S2' a b c d -->*
  S2' a b (d+c) 0.
Proof.
  gen c.
  ind d Inc2'.
Qed.

Lemma Inc3s' a b c d n:
  S3' a b (n*3+c) d -->*
  S3' a b c (n*3+d).
Proof.
  gen c d.
  ind n Inc3'.
Qed.


Lemma Incs2323 a b d:
  S2 a (1+b) 0 (1+d*3) 1 1 -->*
  S3' a b 0 (4+d*3).
Proof.
  follow Inc2s.
  mid (S3 a (1+b) (1+d*3) 1 (3+d*3) 1); [es|].
  follow (Inc3s a (1+b) 1 1 3 1 d).
  mid (S2' a b 0 (3+d*3)); [es|].
  follow Inc2s'.
  mid (S3' a b (3+d*3) 1); [es|].
  follow (Inc3s' a b 0 1 (1+d)).
  finish.
Qed.

Lemma Incs0101 b d e:
  S0 1 (1+b*3) 0 (1+d) e -->*
  S1 3 (2+b*3) 3 d e.
Proof.
  follow Inc0s.
  mid (S1 (2+b*3) 2 (1+b*3) (1+d) e); [es|].
  follow (Inc1s 2 2 1 (1+d) e b).
  mid (S0 0 (3+b*3) 0 d e); [es|].
  follow Inc0s.
  mid (S1 (3+b*3) 2 (3+b*3) d e); [es|].
  follow (Inc1s 3 2 3 d e b).
  finish.
Qed.

Definition S4 b d e :=
  S0 1 (1+b*3) 0 (1+d*3) (2+e*3).

Lemma Inc4 b d e:
  S4 b (1+d) e -->*
  S4 (1+b) d (1+e).
Proof.
  unfold S4.
  follow Incs0101.
  mid (S2 (4+b*3) (1+(1+d*3)) 0 (1+e*3) 1 1); [es|].
  follow Incs2323.
  es.
Qed.

Lemma Inc4s b d e:
  S4 b d e -->*
  S4 (d+b) 0 (d+e).
Proof.
  gen b e.
  ind d Inc4.
Qed.

Definition S5 a b c :=
  const 0 <* [1]^^a <* [0] <{{C}} [1] *> [1;0]^^b *> [1;1] *> [0]^^c *> [1] *> const 0.

Lemma Inc5 a b c:
  S5 a (1+b) c -->*
  S5 (1+a) b (1+c).
Proof.
  es.
Qed.

Lemma Inc5s a b c:
  S5 a b c -->*
  S5 (b+a) 0 (b+c).
Proof.
  gen a c.
  ind b Inc5.
Qed.

Definition S6 a b c :=
  const 0 <* [1]^^(a) <{{B}} [1;0]^^b *> [0]^^(c) *> [1] *> const 0.

Lemma Inc6 a b c:
  S6 (3+a) b (3+c) -->*
  S6 a (3+b) c.
Proof.
  es.
Qed.

Lemma Inc6s a b c n:
  S6 (n*3+a) b (n*3+c) -->*
  S6 a (n*3+b) c.
Proof.
  gen a b c.
  ind n Inc6.
Qed.

Definition config n :=
  S6 1 (2+n*3) 1.

Lemma BigStep n:
  config n -->+
  config (2+n*2).
Proof.
  unfold config.
  mid10 (S4 0 (n) 0); [unfold S4; es|].
  follow Inc4s.
  unfold S4.
  follow Incs0101.
  mid (S5 1 (6+n*3+n*3) 1); [es|].
  mid (S5 1 ((2+n*2)*3) 1); [finish|].
  remember (2+n*2) as n0.
  follow Inc5s.
  mid (S6 (1+n0*3) 2 (1+n0*3)); [es|].
  follow (Inc6s 1 2 1 n0).
  finish.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config O).
  1: unfold config,S6; solve_init.
  apply progress_nonhalt_simple.
  intros n.
  eexists.
  apply BigStep.
Qed.

End TM16.

Module TM17.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LD_1RD0RE_0RA0RC_1RC0LA_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c d e :=
  const 0 <* [1]^^a <* [0] <{{C}} [1] *> [1;0]^^b *> [1;1] *> [0]^^c *> [0;1]^^d *> [1;0]^^e *> const 0.

Lemma Inc0 a b c d e:
  S0 a (1+b) c d e -->*
  S0 (1+a) b (1+c) d e.
Proof.
  es.
Qed.

Definition S1 a b c d e :=
  const 0 <* [1]^^(a) <{{B}} [1;0]^^b *> [0]^^(c) *> [0;1]^^d *> [1;0]^^e *> const 0.

Lemma Inc1 a b c d e:
  S1 (3+a) b (3+c) d e -->*
  S1 a (3+b) c d e.
Proof.
  es.
Qed.

Definition S2 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <* [0] <{{C}} [1] *> [1;0]^^d *> [1;1] *> [0]^^e *> [1]^^f *> const 0.

Lemma Inc2 a b c d e f:
  S2 a b c (1+d) e f -->*
  S2 a b (1+c) d (1+e) f.
Proof.
  es.
Qed.

Definition S3 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <{{B}} [1] *> [0;1]^^(d) *> [0]^^e *> [1]^^f *> const 0.

Lemma Inc3 a b c d e f:
  S3 a b (3+c) d (3+e) f -->*
  S3 a b c (3+d) e f.
Proof.
  es.
Qed.

Definition S2' a b c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <* [0] <{{C}} [1] *> [1;0]^^d *> [1;1] *> const 0.

Lemma Inc2' a b c d:
  S2' a b c (1+d) -->*
  S2' a b (1+c) d.
Proof.
  es.
Qed.

Definition S3' a b c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <{{B}} [1] *> [0;1]^^(d) *> const 0.

Lemma Inc3' a b c d:
  S3' a b (3+c) d -->*
  S3' a b c (3+d).
Proof.
  es.
Qed.

Lemma Inc0s a b c d e:
  S0 a b c d e -->*
  S0 (b+a) 0 (b+c) d e.
Proof.
  gen a c.
  ind b Inc0.
Qed.

Lemma Inc1s a b c d e n:
  S1 (n*3+a) b (n*3+c) d e -->*
  S1 a (n*3+b) c d e.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2s a b c d e f:
  S2 a b c d e f -->*
  S2 a b (d+c) 0 (d+e) f.
Proof.
  gen c e.
  ind d Inc2.
Qed.

Lemma Inc3s a b c d e f n:
  S3 a b (n*3+c) d (n*3+e) f -->*
  S3 a b c (n*3+d) e f.
Proof.
  gen c d e.
  ind n Inc3.
Qed.

Lemma Inc2s' a b c d:
  S2' a b c d -->*
  S2' a b (d+c) 0.
Proof.
  gen c.
  ind d Inc2'.
Qed.

Lemma Inc3s' a b c d n:
  S3' a b (n*3+c) d -->*
  S3' a b c (n*3+d).
Proof.
  gen c d.
  ind n Inc3'.
Qed.


Lemma Incs2323 a b d:
  S2 a (1+b) 0 (1+d*3) 1 1 -->*
  S3' a b 0 (4+d*3).
Proof.
  follow Inc2s.
  mid (S3 a (1+b) (1+d*3) 1 (3+d*3) 1); [es|].
  follow (Inc3s a (1+b) 1 1 3 1 d).
  mid (S2' a b 0 (3+d*3)); [es|].
  follow Inc2s'.
  mid (S3' a b (3+d*3) 1); [es|].
  follow (Inc3s' a b 0 1 (1+d)).
  finish.
Qed.

Lemma Incs0101 b d e:
  S0 1 (1+b*3) 0 (1+d) e -->*
  S1 3 (2+b*3) 3 d e.
Proof.
  follow Inc0s.
  mid (S1 (2+b*3) 2 (1+b*3) (1+d) e); [es|].
  follow (Inc1s 2 2 1 (1+d) e b).
  mid (S0 0 (3+b*3) 0 d e); [es|].
  follow Inc0s.
  mid (S1 (3+b*3) 2 (3+b*3) d e); [es|].
  follow (Inc1s 3 2 3 d e b).
  finish.
Qed.

Definition S4 b d e :=
  S0 1 (1+b*3) 0 (1+d*3) (2+e*3).

Lemma Inc4 b d e:
  S4 b (1+d) e -->*
  S4 (1+b) d (1+e).
Proof.
  unfold S4.
  follow Incs0101.
  mid (S2 (4+b*3) (1+(1+d*3)) 0 (1+e*3) 1 1); [es|].
  follow Incs2323.
  es.
Qed.

Lemma Inc4s b d e:
  S4 b d e -->*
  S4 (d+b) 0 (d+e).
Proof.
  gen b e.
  ind d Inc4.
Qed.

Definition S5 a b c :=
  const 0 <* [1]^^a <* [0] <{{C}} [1] *> [1;0]^^b *> [1;1] *> [0]^^c *> [1] *> const 0.

Lemma Inc5 a b c:
  S5 a (1+b) c -->*
  S5 (1+a) b (1+c).
Proof.
  es.
Qed.

Lemma Inc5s a b c:
  S5 a b c -->*
  S5 (b+a) 0 (b+c).
Proof.
  gen a c.
  ind b Inc5.
Qed.

Definition S6 a b c :=
  const 0 <* [1]^^(a) <{{B}} [1;0]^^b *> [0]^^(c) *> [1] *> const 0.

Lemma Inc6 a b c:
  S6 (3+a) b (3+c) -->*
  S6 a (3+b) c.
Proof.
  es.
Qed.

Lemma Inc6s a b c n:
  S6 (n*3+a) b (n*3+c) -->*
  S6 a (n*3+b) c.
Proof.
  gen a b c.
  ind n Inc6.
Qed.

Definition config n :=
  S6 1 (2+n*3) 1.

Lemma BigStep n:
  config n -->+
  config (2+n*2).
Proof.
  unfold config.
  mid10 (S4 0 (n) 0); [unfold S4; es|].
  follow Inc4s.
  unfold S4.
  follow Incs0101.
  mid (S5 1 (6+n*3+n*3) 1); [es|].
  mid (S5 1 ((2+n*2)*3) 1); [finish|].
  remember (2+n*2) as n0.
  follow Inc5s.
  mid (S6 (1+n0*3) 2 (1+n0*3)); [es|].
  follow (Inc6s 1 2 1 n0).
  finish.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config O).
  1: unfold config,S6; solve_init.
  apply progress_nonhalt_simple.
  intros n.
  eexists.
  apply BigStep.
Qed.

End TM17.

Module TM18.
Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC0LD_1RD0RE_0RA0RC_1RC0LA_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c d e :=
  const 0 <* [1]^^a <* [0] <{{C}} [1] *> [1;0]^^b *> [1;1] *> [0]^^c *> [0;1]^^d *> [1;0]^^e *> const 0.

Lemma Inc0 a b c d e:
  S0 a (1+b) c d e -->*
  S0 (1+a) b (1+c) d e.
Proof.
  es.
Qed.

Definition S1 a b c d e :=
  const 0 <* [1]^^(a) <{{B}} [1;0]^^b *> [0]^^(c) *> [0;1]^^d *> [1;0]^^e *> const 0.

Lemma Inc1 a b c d e:
  S1 (3+a) b (3+c) d e -->*
  S1 a (3+b) c d e.
Proof.
  es.
Qed.

Definition S2 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <* [0] <{{C}} [1] *> [1;0]^^d *> [1;1] *> [0]^^e *> [1]^^f *> const 0.

Lemma Inc2 a b c d e f:
  S2 a b c (1+d) e f -->*
  S2 a b (1+c) d (1+e) f.
Proof.
  es.
Qed.

Definition S3 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <{{B}} [1] *> [0;1]^^(d) *> [0]^^e *> [1]^^f *> const 0.

Lemma Inc3 a b c d e f:
  S3 a b (3+c) d (3+e) f -->*
  S3 a b c (3+d) e f.
Proof.
  es.
Qed.

Definition S2' a b c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <* [0] <{{C}} [1] *> [1;0]^^d *> [1;1] *> const 0.

Lemma Inc2' a b c d:
  S2' a b c (1+d) -->*
  S2' a b (1+c) d.
Proof.
  es.
Qed.

Definition S3' a b c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <{{B}} [1] *> [0;1]^^(d) *> const 0.

Lemma Inc3' a b c d:
  S3' a b (3+c) d -->*
  S3' a b c (3+d).
Proof.
  es.
Qed.

Lemma Inc0s a b c d e:
  S0 a b c d e -->*
  S0 (b+a) 0 (b+c) d e.
Proof.
  gen a c.
  ind b Inc0.
Qed.

Lemma Inc1s a b c d e n:
  S1 (n*3+a) b (n*3+c) d e -->*
  S1 a (n*3+b) c d e.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2s a b c d e f:
  S2 a b c d e f -->*
  S2 a b (d+c) 0 (d+e) f.
Proof.
  gen c e.
  ind d Inc2.
Qed.

Lemma Inc3s a b c d e f n:
  S3 a b (n*3+c) d (n*3+e) f -->*
  S3 a b c (n*3+d) e f.
Proof.
  gen c d e.
  ind n Inc3.
Qed.

Lemma Inc2s' a b c d:
  S2' a b c d -->*
  S2' a b (d+c) 0.
Proof.
  gen c.
  ind d Inc2'.
Qed.

Lemma Inc3s' a b c d n:
  S3' a b (n*3+c) d -->*
  S3' a b c (n*3+d).
Proof.
  gen c d.
  ind n Inc3'.
Qed.


Lemma Incs2323 a b d:
  S2 a (1+b) 0 (1+d*3) 1 1 -->*
  S3' a b 0 (4+d*3).
Proof.
  follow Inc2s.
  mid (S3 a (1+b) (1+d*3) 1 (3+d*3) 1); [es|].
  follow (Inc3s a (1+b) 1 1 3 1 d).
  mid (S2' a b 0 (3+d*3)); [es|].
  follow Inc2s'.
  mid (S3' a b (3+d*3) 1); [es|].
  follow (Inc3s' a b 0 1 (1+d)).
  finish.
Qed.

Lemma Incs0101 b d e:
  S0 1 (1+b*3) 0 (1+d) e -->*
  S1 3 (2+b*3) 3 d e.
Proof.
  follow Inc0s.
  mid (S1 (2+b*3) 2 (1+b*3) (1+d) e); [es|].
  follow (Inc1s 2 2 1 (1+d) e b).
  mid (S0 0 (3+b*3) 0 d e); [es|].
  follow Inc0s.
  mid (S1 (3+b*3) 2 (3+b*3) d e); [es|].
  follow (Inc1s 3 2 3 d e b).
  finish.
Qed.

Definition S4 b d e :=
  S0 1 (1+b*3) 0 (1+d*3) (2+e*3).

Lemma Inc4 b d e:
  S4 b (1+d) e -->*
  S4 (1+b) d (1+e).
Proof.
  unfold S4.
  follow Incs0101.
  mid (S2 (4+b*3) (1+(1+d*3)) 0 (1+e*3) 1 1); [es|].
  follow Incs2323.
  es.
Qed.

Lemma Inc4s b d e:
  S4 b d e -->*
  S4 (d+b) 0 (d+e).
Proof.
  gen b e.
  ind d Inc4.
Qed.

Definition S5 a b c :=
  const 0 <* [1]^^a <* [0] <{{C}} [1] *> [1;0]^^b *> [1;1] *> [0]^^c *> [1] *> const 0.

Lemma Inc5 a b c:
  S5 a (1+b) c -->*
  S5 (1+a) b (1+c).
Proof.
  es.
Qed.

Lemma Inc5s a b c:
  S5 a b c -->*
  S5 (b+a) 0 (b+c).
Proof.
  gen a c.
  ind b Inc5.
Qed.

Definition S6 a b c :=
  const 0 <* [1]^^(a) <{{B}} [1;0]^^b *> [0]^^(c) *> [1] *> const 0.

Lemma Inc6 a b c:
  S6 (3+a) b (3+c) -->*
  S6 a (3+b) c.
Proof.
  es.
Qed.

Lemma Inc6s a b c n:
  S6 (n*3+a) b (n*3+c) -->*
  S6 a (n*3+b) c.
Proof.
  gen a b c.
  ind n Inc6.
Qed.

Definition config n :=
  S5 1 (n*3) 1.

Lemma BigStep n:
  config n -->+
  config (3+n*2).
Proof.
  unfold config.
  follow Inc5s.
  mid10 (S6 (1+n*3) 2 (1+n*3)); [es|].
  follow (Inc6s 1 2 1 n).
  mid (S4 0 n 1); [unfold S4; es|].
  follow Inc4s.
  unfold S4.
  follow Incs0101.
  mid (S5 1 (9+n*3+n*3) 1); [es|].
  finish.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config O).
  1: unfold config,S5; solve_init.
  apply progress_nonhalt_simple.
  intros n.
  eexists.
  apply BigStep.
Qed.

End TM18.


Module TM19.
Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC0LD_1RD0RE_0RA0RC_1RC0LA_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c d e :=
  const 0 <* [1]^^a <* [0;1] {{C}}> [1;0]^^b *> [1;1] *> [0]^^c *> [0;1]^^d *> [1;0]^^e *> [0;1] *> const 0.

Lemma Inc0 a b c d e:
  S0 a (1+b) c d e -->*
  S0 (1+a) b (1+c) d e.
Proof.
  es.
Qed.

Definition S1 a b c d e :=
  const 0 <* [1]^^(a) <{{B}} [1;0]^^b *> [0]^^(c) *> [0;1]^^d *> [1;0]^^e *> [0;1] *> const 0.

Lemma Inc1 a b c d e:
  S1 (3+a) b (3+c) d e -->*
  S1 a (3+b) c d e.
Proof.
  es.
Qed.

Definition S2 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <* [0] <{{C}} [1] *> [1;0]^^d *> [1;1] *> [0]^^e *> [1]^^f *> [0;1] *> const 0.

Lemma Inc2 a b c d e f:
  S2 a b c (1+d) e f -->*
  S2 a b (1+c) d (1+e) f.
Proof.
  es.
Qed.

Definition S3 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <{{B}} [1] *> [0;1]^^(d) *> [0]^^e *> [1]^^f *> [0;1] *> const 0.

Lemma Inc3 a b c d e f:
  S3 a b (3+c) d (3+e) f -->*
  S3 a b c (3+d) e f.
Proof.
  es.
Qed.

Lemma Inc0s a b c d e:
  S0 a b c d e -->*
  S0 (b+a) 0 (b+c) d e.
Proof.
  gen a c.
  ind b Inc0.
Qed.

Lemma Inc1s a b c d e n:
  S1 (n*3+a) b (n*3+c) d e -->*
  S1 a (n*3+b) c d e.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2s a b c d e f:
  S2 a b c d e f -->*
  S2 a b (d+c) 0 (d+e) f.
Proof.
  gen c e.
  ind d Inc2.
Qed.

Lemma Inc3s a b c d e f n:
  S3 a b (n*3+c) d (n*3+e) f -->*
  S3 a b c (n*3+d) e f.
Proof.
  gen c d e.
  ind n Inc3.
Qed.

Lemma Incs2323 a b d:
  S2 a (1+b) 0 (1+d*3) 1 1-->*
  S3 a b 0 (4+d*3) 1 0.
Proof.
  follow Inc2s.
  mid (S3 a (1+b) (1+d*3) 1 (3+d*3) 1); [es|].
  follow (Inc3s a (1+b) 1 1 3 1 d).
  mid (S2 a b 0 (3+d*3) 0 0); [es|].
  follow Inc2s.
  mid (S3 a b (3+d*3) 1 (4+d*3) 0); [es|].
  follow (Inc3s a b 0 1 1 0 (1+d)).
  finish.
Qed.

Lemma Incs0101 b d e:
  S0 1 (1+b*3) 0 (1+d) e -->*
  S1 3 (2+b*3) 3 d e.
Proof.
  follow Inc0s.
  mid (S1 (2+b*3) 2 (1+b*3) (1+d) e); [es|].
  follow (Inc1s 2 2 1 (1+d) e b).
  mid (S0 0 (3+b*3) 0 d e); [es|].
  follow Inc0s.
  mid (S1 (3+b*3) 2 (3+b*3) d e); [es|].
  follow (Inc1s 3 2 3 d e b).
  finish.
Qed.



Definition S4 b d e :=
  S0 1 (1+b*3) 0 (3+d*3) (2+e*3).

Lemma Inc4 b d e:
  S4 b (1+d) e -->*
  S4 (1+b) d (1+e).
Proof.
  unfold S4.
  replace (3+(1+d)*3) with (1+(2+(1+d)*3)) by lia.
  follow Incs0101.
  mid (S2 (4+b*3) (1+((1+d)*3)) 0 (1+e*3) 1 1); [es|].
  follow Incs2323.
  es.
Qed.

Lemma Inc4s b d e:
  S4 b d e -->*
  S4 (d+b) 0 (d+e).
Proof.
  gen b e.
  ind d Inc4.
Qed.

Definition S2' a c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1]^^c <* [0] <{{C}} [1] *> [1;0]^^d *> [1;1] *> const 0.

Lemma Inc2' a c d:
  S2' a c (1+d) -->*
  S2' a (1+c) d.
Proof.
  es.
Qed.

Lemma Inc2s' a c d:
  S2' a c d -->*
  S2' a (d+c) 0.
Proof.
  gen c.
  ind d Inc2'.
Qed.

Definition S3' a c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1]^^c <{{B}} [1] *> [0;1]^^(d) *> const 0.

Lemma Inc3' a c d:
  S3' a (3+c) d -->*
  S3' a c (3+d).
Proof.
  es.
Qed.

Lemma Inc3s' a c d n:
  S3' a (n*3+c) d -->*
  S3' a c (n*3+d).
Proof.
  gen c d.
  ind n Inc3'.
Qed.


Definition S0' a b c d :=
  const 0 <* [1]^^a <* [0;1] {{C}}> [1;0]^^b *> [1;1] *> [0]^^c *> [0;1]^^d *> const 0.

Lemma Inc0' a b c d:
  S0' a (1+b) c d -->*
  S0' (1+a) b (1+c) d.
Proof.
  es.
Qed.

Lemma Inc0s' a b c d:
  S0' a b c d -->*
  S0' (b+a) 0 (b+c) d.
Proof.
  gen a c.
  ind b Inc0'.
Qed.


Definition S1' a b c d :=
  const 0 <* [1]^^(a) <{{B}} [1;0]^^b *> [0]^^(c) *> [1;0]^^d *> const 0.

Lemma Inc1' a b c d:
  S1' (3+a) b (3+c) d -->*
  S1' a (3+b) c d.
Proof.
  es.
Qed.

Lemma Inc1s' a b c d n:
  S1' (n*3+a) b (n*3+c) d -->*
  S1' a (n*3+b) c d.
Proof.
  gen a b c.
  ind n Inc1'.
Qed.

Definition config n :=
  S4 1 n 0.

Lemma BigStep n:
  config n -->+
  config (5+n*2).
Proof.
  unfold config.
  follow Inc4s.
  unfold S4.
  change (3+0*3) with 3.
  follow Incs0101.
  mid10 (S2 (4+(n+1)*3) 1 0 (1+n*3) 1 1); [es|].
  follow Incs2323.
  mid (S2' (6+n*3) 1 (9+n*3)); [es|].
  follow Inc2s'.
  mid (S3' (6+n*3) (10+n*3) 1); [es|].
  follow (Inc3s' (6+n*3) 1 1 (3+n)).
  mid (S0' 1 (6+n*3) 0 (10+n*3)); [es|].
  follow Inc0s'.
  mid (S1' (7+n*3) 2 (7+n*3) (10+n*3)); [es|].
  follow (Inc1s' 1 2 1 (10+n*3) (2+n)).
  mid (S2 1 (7+n*3) 1 (10+n*3) 0 0); [es|].
  follow Inc2s.
  mid (S3 1 (7+n*3) (11+n*3) 1 (11+n*3) 0); [es|].
  follow (Inc3s 1 (7+n*3) 2 1 2 0 (3+n)).
  mid (S0 1 4 0 (18+n*3+n*3) 2).
  2: finish.
  es.
Qed.


Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config O).
  1: unfold config,S4,S0; solve_init.
  apply progress_nonhalt_simple.
  intros n.
  eexists.
  apply BigStep.
Qed.

End TM19.


Module TM20.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LD_1RD0RE_0RA0RC_1RC0LA_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Definition S0 a b c d e :=
  const 0 <* [1]^^a <* [0;1] {{C}}> [1;0]^^b *> [1;1] *> [0]^^c *> [0;1]^^d *> [1;0]^^e *> [0;1] *> const 0.

Lemma Inc0 a b c d e:
  S0 a (1+b) c d e -->*
  S0 (1+a) b (1+c) d e.
Proof.
  es.
Qed.

Definition S1 a b c d e :=
  const 0 <* [1]^^(a) <{{B}} [1;0]^^b *> [0]^^(c) *> [0;1]^^d *> [1;0]^^e *> [0;1] *> const 0.

Lemma Inc1 a b c d e:
  S1 (3+a) b (3+c) d e -->*
  S1 a (3+b) c d e.
Proof.
  es.
Qed.

Definition S2 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <* [0] <{{C}} [1] *> [1;0]^^d *> [1;1] *> [0]^^e *> [1]^^f *> [0;1] *> const 0.

Lemma Inc2 a b c d e f:
  S2 a b c (1+d) e f -->*
  S2 a b (1+c) d (1+e) f.
Proof.
  es.
Qed.

Definition S3 a b c d e f :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1;1] <* [1;0]^^b <* [1]^^c <{{B}} [1] *> [0;1]^^(d) *> [0]^^e *> [1]^^f *> [0;1] *> const 0.

Lemma Inc3 a b c d e f:
  S3 a b (3+c) d (3+e) f -->*
  S3 a b c (3+d) e f.
Proof.
  es.
Qed.

Lemma Inc0s a b c d e:
  S0 a b c d e -->*
  S0 (b+a) 0 (b+c) d e.
Proof.
  gen a c.
  ind b Inc0.
Qed.

Lemma Inc1s a b c d e n:
  S1 (n*3+a) b (n*3+c) d e -->*
  S1 a (n*3+b) c d e.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2s a b c d e f:
  S2 a b c d e f -->*
  S2 a b (d+c) 0 (d+e) f.
Proof.
  gen c e.
  ind d Inc2.
Qed.

Lemma Inc3s a b c d e f n:
  S3 a b (n*3+c) d (n*3+e) f -->*
  S3 a b c (n*3+d) e f.
Proof.
  gen c d e.
  ind n Inc3.
Qed.

Lemma Incs2323 a b d:
  S2 a (1+b) 0 (1+d*3) 1 1-->*
  S3 a b 0 (4+d*3) 1 0.
Proof.
  follow Inc2s.
  mid (S3 a (1+b) (1+d*3) 1 (3+d*3) 1); [es|].
  follow (Inc3s a (1+b) 1 1 3 1 d).
  mid (S2 a b 0 (3+d*3) 0 0); [es|].
  follow Inc2s.
  mid (S3 a b (3+d*3) 1 (4+d*3) 0); [es|].
  follow (Inc3s a b 0 1 1 0 (1+d)).
  finish.
Qed.

Lemma Incs0101 b d e:
  S0 1 (1+b*3) 0 (1+d) e -->*
  S1 3 (2+b*3) 3 d e.
Proof.
  follow Inc0s.
  mid (S1 (2+b*3) 2 (1+b*3) (1+d) e); [es|].
  follow (Inc1s 2 2 1 (1+d) e b).
  mid (S0 0 (3+b*3) 0 d e); [es|].
  follow Inc0s.
  mid (S1 (3+b*3) 2 (3+b*3) d e); [es|].
  follow (Inc1s 3 2 3 d e b).
  finish.
Qed.



Definition S4 b d e :=
  S0 1 (1+b*3) 0 (3+d*3) (2+e*3).

Lemma Inc4 b d e:
  S4 b (1+d) e -->*
  S4 (1+b) d (1+e).
Proof.
  unfold S4.
  replace (3+(1+d)*3) with (1+(2+(1+d)*3)) by lia.
  follow Incs0101.
  mid (S2 (4+b*3) (1+((1+d)*3)) 0 (1+e*3) 1 1); [es|].
  follow Incs2323.
  es.
Qed.

Lemma Inc4s b d e:
  S4 b d e -->*
  S4 (d+b) 0 (d+e).
Proof.
  gen b e.
  ind d Inc4.
Qed.

Definition S2' a c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1]^^c <* [0] <{{C}} [1] *> [1;0]^^d *> [1;1] *> const 0.

Lemma Inc2' a c d:
  S2' a c (1+d) -->*
  S2' a (1+c) d.
Proof.
  es.
Qed.

Lemma Inc2s' a c d:
  S2' a c d -->*
  S2' a (d+c) 0.
Proof.
  gen c.
  ind d Inc2'.
Qed.

Definition S3' a c d :=
  const 0 <* [0;0;1] <* [0;1]^^a <* [1]^^c <{{B}} [1] *> [0;1]^^(d) *> const 0.

Lemma Inc3' a c d:
  S3' a (3+c) d -->*
  S3' a c (3+d).
Proof.
  es.
Qed.

Lemma Inc3s' a c d n:
  S3' a (n*3+c) d -->*
  S3' a c (n*3+d).
Proof.
  gen c d.
  ind n Inc3'.
Qed.


Definition S0' a b c d :=
  const 0 <* [1]^^a <* [0;1] {{C}}> [1;0]^^b *> [1;1] *> [0]^^c *> [0;1]^^d *> const 0.

Lemma Inc0' a b c d:
  S0' a (1+b) c d -->*
  S0' (1+a) b (1+c) d.
Proof.
  es.
Qed.

Lemma Inc0s' a b c d:
  S0' a b c d -->*
  S0' (b+a) 0 (b+c) d.
Proof.
  gen a c.
  ind b Inc0'.
Qed.


Definition S1' a b c d :=
  const 0 <* [1]^^(a) <{{B}} [1;0]^^b *> [0]^^(c) *> [1;0]^^d *> const 0.

Lemma Inc1' a b c d:
  S1' (3+a) b (3+c) d -->*
  S1' a (3+b) c d.
Proof.
  es.
Qed.

Lemma Inc1s' a b c d n:
  S1' (n*3+a) b (n*3+c) d -->*
  S1' a (n*3+b) c d.
Proof.
  gen a b c.
  ind n Inc1'.
Qed.

Definition config n :=
  S4 1 n 0.

Lemma BigStep n:
  config n -->+
  config (5+n*2).
Proof.
  unfold config.
  follow Inc4s.
  unfold S4.
  change (3+0*3) with 3.
  follow Incs0101.
  mid10 (S2 (4+(n+1)*3) 1 0 (1+n*3) 1 1); [es|].
  follow Incs2323.
  mid (S2' (6+n*3) 1 (9+n*3)); [es|].
  follow Inc2s'.
  mid (S3' (6+n*3) (10+n*3) 1); [es|].
  follow (Inc3s' (6+n*3) 1 1 (3+n)).
  mid (S0' 1 (6+n*3) 0 (10+n*3)); [es|].
  follow Inc0s'.
  mid (S1' (7+n*3) 2 (7+n*3) (10+n*3)); [es|].
  follow (Inc1s' 1 2 1 (10+n*3) (2+n)).
  mid (S2 1 (7+n*3) 1 (10+n*3) 0 0); [es|].
  follow Inc2s.
  mid (S3 1 (7+n*3) (11+n*3) 1 (11+n*3) 0); [es|].
  follow (Inc3s 1 (7+n*3) 2 1 2 0 (3+n)).
  mid (S0 1 4 0 (18+n*3+n*3) 2).
  2: finish.
  es.
Qed.


Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config O).
  1: unfold config,S4,S0; solve_init.
  apply progress_nonhalt_simple.
  intros n.
  eexists.
  apply BigStep.
Qed.

End TM20.
