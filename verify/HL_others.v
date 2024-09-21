From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Ltac er := execute_with_rotate.
Ltac sr := use_shift_rule; simpl_rotate.

Ltac es :=
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc;
  repeat rewrite lpow_mul;
  execute_with_shift_rule.

Ltac step1s_follow H :=
  (follow H || (step1; step1s_follow H)).

Ltac ind n H :=
  induction n as [|n IHn]; intros;
  [ finish |
    cbn[Nat.add];
    follow H;
    follow IHn;
    finish ].

Module test1.
Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0RD_0LE0LD_1RA0LB_1LA1LF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c d r :=
  const 0 <{{A}} [1;0]^^(1+a*2) *> [1;1;1] *> [0;1]^^(b*2) *> [0;1;0]^^c *> [0;0;1]^^d *> r.

Lemma Inc0 a b c d r:
  S0 a (2+b) c (3+d) r -->*
  S0 (2+a) b (5+c) d r.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc0s a b c d n r:
  S0 a (n*2+b) c (n*3+d) r -->*
  S0 (n*2+a) b (n*5+c) d r.
Proof.
  gen a b c d.
  ind n Inc0.
Qed.

Definition S1 a b c d r :=
  const 0 <{{A}} [1;0]^^(1+a*2) *> [1;1;1] *> [0;1]^^(1+b*2) *> [0;0;1]^^c *> [0;0;0] *> [1;0;0]^^d *> r.

Lemma Inc1 a b c d r:
  S1 a (2+b) c (3+d) r -->*
  S1 (2+a) b (5+c) d r.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc1s a b c d n r:
  S1 a (n*2+b) c (n*3+d) r -->*
  S1 (n*2+a) b (n*5+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Lemma Rst0 a b c r:
  S0 a 1 b (3+c) r -->*
  S1 1 (1+a) 4 b ([1;1] *> [0;0;1]^^c *> r).
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Rst1 a b c r:
  S1 a 0 (1+b) (1+c) r -->+
  S0 1 a 5 b ([0;0;0] *> [1;0;0]^^c *> r).
Proof.
  unfold S0,S1.
  es.
Qed.

Definition config(x:nat*side):=
  let (i,r):=x in
    S0 1 (1+i*2) 5 (3+5*i) r.

Lemma init:
  c0 -->*
  config (2,[0;0;0;1;0;0;1;0;0;1;0;0;1;1;0;0;1;0;0;1;0;0;0;1;0;0;1;1]*>const 0).
Proof.
  unfold config,S0.
  solve_init.
Qed.

Opaque S0 S1.

Lemma nonhalt:~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  destruct i as [i r].
  eexists (S i,_).
  unfold config.
  follow (Inc0s 1 1 5 (3+i*2) i r).
  follow Rst0.
  epose proof (Inc1s 1 0 4 (1+(1+i*2)) (1+i) _) as H.
  follow H.
  replace ((1+i)*5+4) with (1+(8+i*5)) by lia.
  follow10 Rst1.
  finish.
Qed.

End test1.


Module test2.
Definition tm := Eval compute in (TM_from_str "1LB1LF_1RC0RB_1LE0RD_1RB0LC_0LA0LD_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c d r :=
  const 0 <{{B}} [1;0]^^(1+a*2) *> [1;1;1] *> [0;1]^^(b*2) *> [0;1;0]^^c *> [0;0;1]^^d *> r.

Lemma Inc0 a b c d r:
  S0 a (2+b) c (3+d) r -->*
  S0 (2+a) b (5+c) d r.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc0s a b c d n r:
  S0 a (n*2+b) c (n*3+d) r -->*
  S0 (n*2+a) b (n*5+c) d r.
Proof.
  gen a b c d.
  ind n Inc0.
Qed.

Definition S1 a b c d r :=
  const 0 <{{B}} [1;0]^^(1+a*2) *> [1;1;1] *> [0;1]^^(1+b*2) *> [0;0;1]^^c *> [0;0;0] *> [1;0;0]^^d *> r.

Lemma Inc1 a b c d r:
  S1 a (2+b) c (3+d) r -->*
  S1 (2+a) b (5+c) d r.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc1s a b c d n r:
  S1 a (n*2+b) c (n*3+d) r -->*
  S1 (n*2+a) b (n*5+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Lemma Rst0 a b c r:
  S0 a 1 b (3+c) r -->*
  S1 1 (1+a) 4 b ([1;1] *> [0;0;1]^^c *> r).
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Rst1 a b c r:
  S1 a 0 (1+b) (1+c) r -->+
  S0 1 a 5 b ([0;0;0] *> [1;0;0]^^c *> r).
Proof.
  unfold S0,S1.
  es.
Qed.

Definition config(x:nat*side):=
  let (i,r):=x in
    S0 1 (1+i*2) 5 (3+5*i) r.

Lemma init:
  c0 -->*
  config (2,[0;0;0;1;0;0;1;0;0;1;0;0;1;1;0;0;1;0;0;1;0;0;0;1;0;0;1;1;0;1]*>const 0).
Proof.
  unfold config,S0.
  solve_init.
Qed.

Opaque S0 S1.

Lemma nonhalt:~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  destruct i as [i r].
  eexists (S i,_).
  unfold config.
  follow (Inc0s 1 1 5 (3+i*2) i r).
  follow Rst0.
  epose proof (Inc1s 1 0 4 (1+(1+i*2)) (1+i) _) as H.
  follow H.
  replace ((1+i)*5+4) with (1+(8+i*5)) by lia.
  follow10 Rst1.
  finish.
Qed.

End test2.

Module test3.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC0RB_1LD0RA_0LE0LA_1LB1LF_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c d r :=
  const 0 <{{B}} [1;0]^^(1+a*2) *> [1;1;1] *> [0;1]^^(b*2) *> [0;1;0]^^c *> [0;0;1]^^d *> r.

Lemma Inc0 a b c d r:
  S0 a (2+b) c (3+d) r -->*
  S0 (2+a) b (5+c) d r.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc0s a b c d n r:
  S0 a (n*2+b) c (n*3+d) r -->*
  S0 (n*2+a) b (n*5+c) d r.
Proof.
  gen a b c d.
  ind n Inc0.
Qed.

Definition S1 a b c d r :=
  const 0 <{{B}} [1;0]^^(1+a*2) *> [1;1;1] *> [0;1]^^(1+b*2) *> [0;0;1]^^c *> [0;0;0] *> [1;0;0]^^d *> r.

Lemma Inc1 a b c d r:
  S1 a (2+b) c (3+d) r -->*
  S1 (2+a) b (5+c) d r.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc1s a b c d n r:
  S1 a (n*2+b) c (n*3+d) r -->*
  S1 (n*2+a) b (n*5+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Lemma Rst0 a b c r:
  S0 a 1 b (3+c) r -->*
  S1 1 (1+a) 4 b ([1;1] *> [0;0;1]^^c *> r).
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Rst1 a b c r:
  S1 a 0 (1+b) (1+c) r -->+
  S0 1 a 5 b ([0;0;0] *> [1;0;0]^^c *> r).
Proof.
  unfold S0,S1.
  es.
Qed.

Definition config(x:nat*side):=
  let (i,r):=x in
    S0 1 (1+i*2) 5 (3+5*i) r.

Lemma init:
  c0 -->*
  config (2,[0;0;0;1;0;0;1;0;0;1;0;0;1;1;0;0;1;0;0;1;0;0;0;1;0;0;1;1;0;0;0;1]*>const 0).
Proof.
  unfold config,S0.
  solve_init.
Qed.

Opaque S0 S1.

Lemma nonhalt:~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  destruct i as [i r].
  eexists (S i,_).
  unfold config.
  follow (Inc0s 1 1 5 (3+i*2) i r).
  follow Rst0.
  epose proof (Inc1s 1 0 4 (1+(1+i*2)) (1+i) _) as H.
  follow H.
  replace ((1+i)*5+4) with (1+(8+i*5)) by lia.
  follow10 Rst1.
  finish.
Qed.

End test3.


Module test4.
Definition tm := Eval compute in (TM_from_str "1LB0RE_0LC0LE_1LD1LF_1RA0RD_1RD0LA_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c d r :=
  const 0 <{{D}} [1;0]^^(1+a*2) *> [1;1;1] *> [0;1]^^(b*2) *> [0;1;0]^^c *> [0;0;1]^^d *> r.

Lemma Inc0 a b c d r:
  S0 a (2+b) c (3+d) r -->*
  S0 (2+a) b (5+c) d r.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc0s a b c d n r:
  S0 a (n*2+b) c (n*3+d) r -->*
  S0 (n*2+a) b (n*5+c) d r.
Proof.
  gen a b c d.
  ind n Inc0.
Qed.

Definition S1 a b c d r :=
  const 0 <{{D}} [1;0]^^(1+a*2) *> [1;1;1] *> [0;1]^^(1+b*2) *> [0;0;1]^^c *> [0;0;0] *> [1;0;0]^^d *> r.

Lemma Inc1 a b c d r:
  S1 a (2+b) c (3+d) r -->*
  S1 (2+a) b (5+c) d r.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc1s a b c d n r:
  S1 a (n*2+b) c (n*3+d) r -->*
  S1 (n*2+a) b (n*5+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Lemma Rst0 a b c r:
  S0 a 1 b (3+c) r -->*
  S1 1 (1+a) 4 b ([1;1] *> [0;0;1]^^c *> r).
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Rst1 a b c r:
  S1 a 0 (1+b) (1+c) r -->+
  S0 1 a 5 b ([0;0;0] *> [1;0;0]^^c *> r).
Proof.
  unfold S0,S1.
  es.
Qed.

Definition config(x:nat*side):=
  let (i,r):=x in
    S0 1 (1+i*2) 5 (3+5*i) r.

Lemma init:
  c0 -->*
  config (2,[0;0;0;1;0;0;1;0;0;1;0;0;1;1;0;0;1;0;0;1;0;0;0;1;0;0;1;1;0;0;0;1;0;0;1]*>const 0).
Proof.
  unfold config,S0.
  solve_init.
Qed.

Opaque S0 S1.

Lemma nonhalt:~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  destruct i as [i r].
  eexists (S i,_).
  unfold config.
  follow (Inc0s 1 1 5 (3+i*2) i r).
  follow Rst0.
  epose proof (Inc1s 1 0 4 (1+(1+i*2)) (1+i) _) as H.
  follow H.
  replace ((1+i)*5+4) with (1+(8+i*5)) by lia.
  follow10 Rst1.
  finish.
Qed.

End test4.

Module test5.
Definition tm := Eval compute in (TM_from_str "1LB---_1LC0RF_0LD0LF_1LE1LA_1RB0RE_1RE0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c d r :=
  const 0 <{{E}} [1;0]^^(1+a*2) *> [1;1;1] *> [0;1]^^(b*2) *> [0;1;0]^^c *> [0;0;1]^^d *> r.

Lemma Inc0 a b c d r:
  S0 a (2+b) c (3+d) r -->*
  S0 (2+a) b (5+c) d r.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc0s a b c d n r:
  S0 a (n*2+b) c (n*3+d) r -->*
  S0 (n*2+a) b (n*5+c) d r.
Proof.
  gen a b c d.
  ind n Inc0.
Qed.

Definition S1 a b c d r :=
  const 0 <{{E}} [1;0]^^(1+a*2) *> [1;1;1] *> [0;1]^^(1+b*2) *> [0;0;1]^^c *> [0;0;0] *> [1;0;0]^^d *> r.

Lemma Inc1 a b c d r:
  S1 a (2+b) c (3+d) r -->*
  S1 (2+a) b (5+c) d r.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc1s a b c d n r:
  S1 a (n*2+b) c (n*3+d) r -->*
  S1 (n*2+a) b (n*5+c) d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Lemma Rst0 a b c r:
  S0 a 1 b (3+c) r -->*
  S1 1 (1+a) 4 b ([1;1] *> [0;0;1]^^c *> r).
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Rst1 a b c r:
  S1 a 0 (1+b) (1+c) r -->+
  S0 1 a 5 b ([0;0;0] *> [1;0;0]^^c *> r).
Proof.
  unfold S0,S1.
  es.
Qed.

Definition config(x:nat*side):=
  let (i,r):=x in
    S0 1 (1+i*2) 5 (3+5*i) r.

Lemma init:
  c0 -->*
  config (2,[0;0;0;1;0;0;1;0;0;1;0;0;1;1;0;0;1;0;0;1;0;0;0;1;0;0;1;1;0;1;0;0;1;0;0;1]*>const 0).
Proof.
  unfold config,S0.
  solve_init.
Qed.

Opaque S0 S1.

Lemma nonhalt:~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  destruct i as [i r].
  eexists (S i,_).
  unfold config.
  follow (Inc0s 1 1 5 (3+i*2) i r).
  follow Rst0.
  epose proof (Inc1s 1 0 4 (1+(1+i*2)) (1+i) _) as H.
  follow H.
  replace ((1+i)*5+4) with (1+(8+i*5)) by lia.
  follow10 Rst1.
  finish.
Qed.

End test5.

Module test6.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1LC0LE_1RD0LB_1RA0RE_0LC1RF_0RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b r :=
  const 0 <{{C}} [1] *> [0;1]^^a *> [0;0] *> [0;1]^^b *> r.

Lemma Inc0 a b r:
  S0 (1+a) b r -->*
  S0 a (2+b) r.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc0s a b r:
  S0 a b r -->*
  S0 0 (a*2+b) r.
Proof.
  gen b.
  ind a Inc0.
Qed.

Definition S1 a b c r :=
  const 0 <* [0;1;0;1] <* [0;1;1;1]^^a <* [0;1] <{{C}} [1;0;0;0] *> [0;1]^^b *> [0;0] *> [0;1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc1s a b c n r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c r :=
  const 0 <* [0;1;0;1] <* [0;1;1;1]^^a <* [1] <{{E}} [0] *> [0;1]^^b *> [0;0] *> [0;1]^^c *> r.

Lemma Inc2 a b c r:
  S2 (1+a) b c r -->*
  S2 a (1+b) (1+c) r.
Proof.
  unfold S2.
  es.
Qed.

Lemma Inc2s a b c r:
  S2 a b c r -->*
  S2 0 (a+b) (a+c) r.
Proof.
  gen b c.
  ind a Inc2.
Qed.

Definition config(x:nat*side):=
  let (n,r):=x in
    S0 (2+n) (1+n) ([0;0;0;0] *> r).

Lemma init:
  c0 -->* config (1%nat,[0;0;0;1;0;1;0;0;0;1;0;1;0;1;0;0;0;0;1]*>const 0).
Proof.
  unfold config,S0.
  solve_init.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  destruct i as [n r].
  eexists (S n,_).
  unfold config.
  follow Inc0s.
  replace ((2+n)*2+(1+n)) with (5+n*3) by lia.
  mid10 (S1 0 (n*3+1) 2 ([0;0] *> r)).
  1: unfold S0,S1; es.
  follow Inc1s.
  mid (S2 (1+n) 0 0 ([0;0;0;0] *> [0;1]^^n *> [0;0;0;1] *> r)).
  1: unfold S1,S2; es.
  follow Inc2s.
  unfold S2,S0; es.
Qed.

End test6.

