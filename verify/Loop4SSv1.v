From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounterFull.

Open Scope list.

Ltac er := execute_with_rotate.
Ltac sr := use_shift_rule; simpl_rotate.

Ltac es :=
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc;
  repeat rewrite lpow_mul;
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

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD0RF_---0LA_1RB0LF_0RD1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c := const 0 <* [1;1]^^a <* [0] <{{A}} [1] *> [1;1]^^b *> [0] *> [1]^^c *> const 0.

Lemma Inc a b c:
  S0 a (1+b) c -->*
  S0 (1+a) b (1+c).
Proof.
  unfold S0.
  es.
Qed.

Lemma Incs a b c:
  S0 a b c -->*
  S0 (b+a) 0 (b+c).
Proof.
  gen a c.
  ind b Inc.
Qed.

Lemma Rst_S a c:
  S0 a 0 (3+c*2) -->+
  S0 (2+a) c 1.
Proof.
  unfold S0.
  es.
Qed.

Lemma Rst_O a:
  S0 a 0 1 -->+
  S0 0 (2+a) 1.
Proof.
  unfold S0.
  es.
Qed.

Lemma IncsRst a b:
  S0 a (2+b*2) 1 -->+
  S0 (4+b*2+a) b 1.
Proof.
  follow Incs.
  replace (2+b*2+1) with (3+b*2) by lia.
  follow10 (Rst_S (2+b*2+a) b).
  finish.
Qed.

Definition config(x:nat*nat):=
  let (a,b):=x in
  S0 (4*2^b*(2^a-1)) (2*2^b-2) 1.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (0,0)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_simple.
  intro i.
  destruct i as [a b].
  destruct b as [|b].
  - exists (O,S a).
    unfold config.
    follow10 Rst_O.
    cbn.
    pose proof (Nat.pow_nonzero 2 a).
    finish.
  - exists (S a,b).
    unfold config.
    pose proof (Nat.pow_nonzero 2 a).
    pose proof (Nat.pow_nonzero 2 b).
    replace (2*2^S b-2) with (2+(2*2^b-2)*2) by (cbn; lia).
    follow10 IncsRst.
    cbn[Nat.pow].
    remember (2^a) as a0.
    remember (2^b) as b0.
    replace (4 + (2 * b0 - 2) * 2 + 4 * (2 * b0) * (a0 - 1)) with
    ((4 * b0) + (8 * b0) * (a0 - 1)) by lia.
    repeat rewrite Nat.mul_sub_distr_l.
    rewrite Nat.add_sub_assoc.
    1: finish.
    apply Nat.mul_le_mono_l.
    lia.
Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RE_0LC1RA_0LD1LC_0RA1LA_1LF1RE_---0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c := const 0 <* [1;1]^^(1+a) <* [0] <{{C}} [1;1]^^b *> [0] *> [1]^^c *> const 0.

Lemma Inc a b c:
  S0 a (1+b) c -->*
  S0 (1+a) b (1+c).
Proof.
  unfold S0.
  es.
Qed.

Lemma Incs a b c:
  S0 a b c -->*
  S0 (b+a) 0 (b+c).
Proof.
  gen a c.
  ind b Inc.
Qed.

Lemma Rst_S a c:
  S0 a 0 (3+c*2) -->+
  S0 (2+a) c 1.
Proof.
  unfold S0.
  es.
Qed.

Lemma Rst_O a:
  S0 a 0 1 -->+
  S0 0 (2+a) 1.
Proof.
  unfold S0.
  es.
Qed.

Lemma IncsRst a b:
  S0 a (2+b*2) 1 -->+
  S0 (4+b*2+a) b 1.
Proof.
  follow Incs.
  replace (2+b*2+1) with (3+b*2) by lia.
  follow10 (Rst_S (2+b*2+a) b).
  finish.
Qed.

Definition config(x:nat*nat):=
  let (a,b):=x in
  S0 (4*2^b*(2^a-1)) (2*2^b-2) 1.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (0,0)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_simple.
  intro i.
  destruct i as [a b].
  destruct b as [|b].
  - exists (O,S a).
    unfold config.
    follow10 Rst_O.
    cbn.
    pose proof (Nat.pow_nonzero 2 a).
    finish.
  - exists (S a,b).
    unfold config.
    pose proof (Nat.pow_nonzero 2 a).
    pose proof (Nat.pow_nonzero 2 b).
    replace (2*2^S b-2) with (2+(2*2^b-2)*2) by (cbn; lia).
    follow10 IncsRst.
    cbn[Nat.pow].
    remember (2^a) as a0.
    remember (2^b) as b0.
    replace (4 + (2 * b0 - 2) * 2 + 4 * (2 * b0) * (a0 - 1)) with
    ((4 * b0) + (8 * b0) * (a0 - 1)) by lia.
    repeat rewrite Nat.mul_sub_distr_l.
    rewrite Nat.add_sub_assoc.
    1: finish.
    apply Nat.mul_le_mono_l.
    lia.
Qed.

End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC1RB_0LD1LC_1RA0LE_0LF1LD_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c := const 0 <* [0;1]^^(1+a) <{{C}} [1;1]^^b *> [0;1]^^c *> const 0.
Definition S1 b c := const 0 <{{C}} [1] *> [1;1]^^b *> [0;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma ROv0 a b:
  S0 (3+a) (1+b) 0 -->+
  S0 a 4 b.
Proof.
  unfold S0.
  es.
Qed.

Lemma LROv b:
  S0 1 b 0 -->+
  S1 1 b.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (4+b) 0 -->*
  S0 b 6 0.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Inc a b:
  3<=a ->
  1<=b ->
  2+b<=a ->
  S0 (a) (b) 0 -->+
  S0 (a-b-2) (2+b*2) 0.
Proof.
  intros H H0 H1.
  replace (S0 a b 0) with (S0 (3+(a-3)) (1+(b-1)) 0) by (f_equal; lia).
  follow10 ROv0.
  follow (Inc0s (a-b-2) 4 0 (b-1)).
  finish.
Qed.

Lemma Ov b:
  2<=b ->
  S0 1 b 0 -->+
  S0 (b*2-3) 6 0.
Proof.
  intros H.
  replace (S0 1 b 0) with (S0 1 (1+(b-1)) 0) by (f_equal; lia).
  follow10 LROv.
  follow Inc1s.
  follow (ROv1 (b*2-3)).
  finish.
Qed.

Fixpoint bi n :=
match n with
| O => 6
| S n0 => 2+(bi n0)*2
end.

Fixpoint dai n :=
match n with
| O => O
| S n0 => dai n0 + bi n0 + 2
end.

Lemma bi_spec n:
  2 + bi n = 8*2^n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma dai_spec n:
  8 + dai n = 8*2^n.
Proof.
  induction n as [|n]; cbn.
  1: reflexivity.
  pose proof (bi_spec n); lia.
Qed.

Definition config(x:nat*nat):=
  let (a,b):=x in
  S0 (1+dai a-dai b) (bi b) 0.

Lemma Inc' a b:
  b<a ->
  config (a,b) -->+
  config (a,S b).
Proof.
  intros H.
  unfold config.
  cbn[dai].
  cbn[bi].
  pose proof (bi_spec b).
  pose proof (dai_spec a).
  pose proof (dai_spec b).
  pose proof (dai_spec (S b)) as H3.
  cbn[dai] in H3.
  cbn[Nat.pow] in H3.
  pose proof (Nat.pow_lt_mono_r 2 b a).
  pose proof (Nat.pow_le_mono_r 2 (S b) a) as H5.
  cbn[Nat.pow] in H5.
  applys_eq Inc; flia.
Qed.

Lemma Ov' a:
  config (a,a) -->+
  config (S a,O).
Proof.
  unfold config.
  pose proof (bi_spec a).
  pose proof (dai_spec a).
  cbn[dai].
  applys_eq (Ov (bi a)); flia.
Qed.

Definition P(x:nat*nat):Prop :=
let (a,b):=x in b<=a.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (0,0)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=P).
  2: unfold P; lia.
  intros i HP.
  destruct i as [a b].
  unfold P in HP.
  assert (b<a\/b=a) as E by lia.
  destruct E as [E|E].
  - eexists. split.
    1: apply Inc',E.
    unfold P. lia.
  - subst. eexists. split.
    1: apply Ov'.
    unfold P. lia.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC1RB_0LD1LC_1RA0LE_1LF1LD_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c := const 0 <* [0;1]^^(1+a) <{{C}} [1;1]^^b *> [0;1]^^c *> const 0.
Definition S1 b c := const 0 <{{C}} [1] *> [1;1]^^b *> [0;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma ROv0 a b:
  S0 (3+a) (1+b) 0 -->+
  S0 a 4 b.
Proof.
  unfold S0.
  es.
Qed.

Lemma LROv b:
  S0 1 b 0 -->+
  S1 1 b.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (4+b) 0 -->*
  S0 b 6 0.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Inc a b:
  3<=a ->
  1<=b ->
  2+b<=a ->
  S0 (a) (b) 0 -->+
  S0 (a-b-2) (2+b*2) 0.
Proof.
  intros H H0 H1.
  replace (S0 a b 0) with (S0 (3+(a-3)) (1+(b-1)) 0) by (f_equal; lia).
  follow10 ROv0.
  follow (Inc0s (a-b-2) 4 0 (b-1)).
  finish.
Qed.

Lemma Ov b:
  2<=b ->
  S0 1 b 0 -->+
  S0 (b*2-3) 6 0.
Proof.
  intros H.
  replace (S0 1 b 0) with (S0 1 (1+(b-1)) 0) by (f_equal; lia).
  follow10 LROv.
  follow Inc1s.
  follow (ROv1 (b*2-3)).
  finish.
Qed.

Fixpoint bi n :=
match n with
| O => 6
| S n0 => 2+(bi n0)*2
end.

Fixpoint dai n :=
match n with
| O => O
| S n0 => dai n0 + bi n0 + 2
end.

Lemma bi_spec n:
  2 + bi n = 8*2^n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma dai_spec n:
  8 + dai n = 8*2^n.
Proof.
  induction n as [|n]; cbn.
  1: reflexivity.
  pose proof (bi_spec n); lia.
Qed.

Definition config(x:nat*nat):=
  let (a,b):=x in
  S0 (1+dai a-dai b) (bi b) 0.

Lemma Inc' a b:
  b<a ->
  config (a,b) -->+
  config (a,S b).
Proof.
  intros H.
  unfold config.
  cbn[dai].
  cbn[bi].
  pose proof (bi_spec b).
  pose proof (dai_spec a).
  pose proof (dai_spec b).
  pose proof (dai_spec (S b)) as H3.
  cbn[dai] in H3.
  cbn[Nat.pow] in H3.
  pose proof (Nat.pow_lt_mono_r 2 b a).
  pose proof (Nat.pow_le_mono_r 2 (S b) a) as H5.
  cbn[Nat.pow] in H5.
  applys_eq Inc; flia.
Qed.

Lemma Ov' a:
  config (a,a) -->+
  config (S a,O).
Proof.
  unfold config.
  pose proof (bi_spec a).
  pose proof (dai_spec a).
  cbn[dai].
  applys_eq (Ov (bi a)); flia.
Qed.

Definition P(x:nat*nat):Prop :=
let (a,b):=x in b<=a.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (0,0)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=P).
  2: unfold P; lia.
  intros i HP.
  destruct i as [a b].
  unfold P in HP.
  assert (b<a\/b=a) as E by lia.
  destruct E as [E|E].
  - eexists. split.
    1: apply Inc',E.
    unfold P. lia.
  - subst. eexists. split.
    1: apply Ov'.
    unfold P. lia.
Qed.

End TM4.



Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC0RA_1RA1LB_1LA1RE_0RF0LD_---0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 c b a := const 0 <* [1] <* [0;0]^^a <* [0;1]^^b <* [1] {{B}}> [1;1]^^c *> const 0.
Definition S1 b c := const 0 <* [0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.


Lemma ROv0 a b:
  S0 (2+a) b 0 -->+
  S0 a 1 (1+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LROv b:
  S0 0 b 0 -->+
  S1 0 (1+b).
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 b 0 -->*
  S0 b 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Inc a b:
  2<=a ->
  3+b<=a ->
  S0 (a) (b) 0 -->+
  S0 (a-b-3) (3+b*2) 0.
Proof.
  intros H H1.
  replace (S0 a b 0) with (S0 (2+(a-2)) b 0) by flia.
  follow10 ROv0.
  follow (Inc0s (a-b-3) 1 0 (1+b)).
  finish.
Qed.

Lemma Ov b:
  S0 0 b 0 -->+
  S0 (2+b*2) 1 0.
Proof.
  follow10 LROv.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Fixpoint bi n :=
match n with
| O => 1%nat
| S n0 => 3+(bi n0)*2
end.

Fixpoint dai n :=
match n with
| O => O
| S n0 => dai n0 + bi n0 + 3
end.

Lemma bi_spec n:
  3 + bi n = 4*2^n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma dai_spec n:
  4 + dai n = 4*2^n.
Proof.
  induction n as [|n]; cbn.
  1: reflexivity.
  pose proof (bi_spec n); lia.
Qed.

Definition config(x:nat*nat):=
  let (a,b):=x in
  S0 (dai a-dai b) (bi b) 0.

Lemma Inc' a b:
  b<a ->
  config (a,b) -->+
  config (a,S b).
Proof.
  intros H.
  unfold config.
  cbn[dai].
  cbn[bi].
  pose proof (bi_spec b).
  pose proof (dai_spec a).
  pose proof (dai_spec b).
  pose proof (dai_spec (S b)) as H3.
  cbn[dai] in H3.
  cbn[Nat.pow] in H3.
  pose proof (Nat.pow_lt_mono_r 2 b a).
  pose proof (Nat.pow_le_mono_r 2 (S b) a) as H5.
  cbn[Nat.pow] in H5.
  applys_eq Inc; flia.
Qed.

Lemma Ov' a:
  config (a,a) -->+
  config (S a,O).
Proof.
  unfold config.
  pose proof (bi_spec a).
  pose proof (dai_spec a).
  cbn[dai].
  applys_eq (Ov (bi a)); flia.
Qed.

Definition P(x:nat*nat):Prop :=
let (a,b):=x in b<=a.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (0,0)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=P).
  2: unfold P; lia.
  intros i HP.
  destruct i as [a b].
  unfold P in HP.
  assert (b<a\/b=a) as E by lia.
  destruct E as [E|E].
  - eexists. split.
    1: apply Inc',E.
    unfold P. lia.
  - subst. eexists. split.
    1: apply Ov'.
    unfold P. lia.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC0RA_1RD1LB_0RF0LE_1LA1RD_---0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 c b a := const 0 <* [1] <* [0;0]^^a <* [0;1]^^b <* [1] {{B}}> [1;1]^^c *> const 0.
Definition S1 b c := const 0 <* [0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.


Lemma ROv0 a b:
  S0 (2+a) b 0 -->+
  S0 a 1 (1+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LROv b:
  S0 0 b 0 -->+
  S1 0 (1+b).
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 b 0 -->*
  S0 b 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Inc a b:
  2<=a ->
  3+b<=a ->
  S0 (a) (b) 0 -->+
  S0 (a-b-3) (3+b*2) 0.
Proof.
  intros H H1.
  replace (S0 a b 0) with (S0 (2+(a-2)) b 0) by flia.
  follow10 ROv0.
  follow (Inc0s (a-b-3) 1 0 (1+b)).
  finish.
Qed.

Lemma Ov b:
  S0 0 b 0 -->+
  S0 (2+b*2) 1 0.
Proof.
  follow10 LROv.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Fixpoint bi n :=
match n with
| O => 1%nat
| S n0 => 3+(bi n0)*2
end.

Fixpoint dai n :=
match n with
| O => O
| S n0 => dai n0 + bi n0 + 3
end.

Lemma bi_spec n:
  3 + bi n = 4*2^n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma dai_spec n:
  4 + dai n = 4*2^n.
Proof.
  induction n as [|n]; cbn.
  1: reflexivity.
  pose proof (bi_spec n); lia.
Qed.

Definition config(x:nat*nat):=
  let (a,b):=x in
  S0 (dai a-dai b) (bi b) 0.

Lemma Inc' a b:
  b<a ->
  config (a,b) -->+
  config (a,S b).
Proof.
  intros H.
  unfold config.
  cbn[dai].
  cbn[bi].
  pose proof (bi_spec b).
  pose proof (dai_spec a).
  pose proof (dai_spec b).
  pose proof (dai_spec (S b)) as H3.
  cbn[dai] in H3.
  cbn[Nat.pow] in H3.
  pose proof (Nat.pow_lt_mono_r 2 b a).
  pose proof (Nat.pow_le_mono_r 2 (S b) a) as H5.
  cbn[Nat.pow] in H5.
  applys_eq Inc; flia.
Qed.

Lemma Ov' a:
  config (a,a) -->+
  config (S a,O).
Proof.
  unfold config.
  pose proof (bi_spec a).
  pose proof (dai_spec a).
  cbn[dai].
  applys_eq (Ov (bi a)); flia.
Qed.

Definition P(x:nat*nat):Prop :=
let (a,b):=x in b<=a.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (0,0)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=P).
  2: unfold P; lia.
  intros i HP.
  destruct i as [a b].
  unfold P in HP.
  assert (b<a\/b=a) as E by lia.
  destruct E as [E|E].
  - eexists. split.
    1: apply Inc',E.
    unfold P. lia.
  - subst. eexists. split.
    1: apply Ov'.
    unfold P. lia.
Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC0RA_0RD1LB_1LA1RE_0RF1RB_---0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 c b a := const 0 <* [1] <* [0;0]^^a <* [0;1]^^b {{A}}> [1;1]^^c *> const 0.
Definition S1 b c := const 0 <* [0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.


Lemma ROv0 a b:
  S0 (2+a) b 0 -->+
  S0 a 1 (1+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LROv b:
  S0 0 b 0 -->+
  S1 0 (1+b).
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 b 0 -->*
  S0 b 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Inc a b:
  2<=a ->
  3+b<=a ->
  S0 (a) (b) 0 -->+
  S0 (a-b-3) (3+b*2) 0.
Proof.
  intros H H1.
  replace (S0 a b 0) with (S0 (2+(a-2)) b 0) by flia.
  follow10 ROv0.
  follow (Inc0s (a-b-3) 1 0 (1+b)).
  finish.
Qed.

Lemma Ov b:
  S0 0 b 0 -->+
  S0 (2+b*2) 1 0.
Proof.
  follow10 LROv.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Fixpoint bi n :=
match n with
| O => 1%nat
| S n0 => 3+(bi n0)*2
end.

Fixpoint dai n :=
match n with
| O => O
| S n0 => dai n0 + bi n0 + 3
end.

Lemma bi_spec n:
  3 + bi n = 4*2^n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma dai_spec n:
  4 + dai n = 4*2^n.
Proof.
  induction n as [|n]; cbn.
  1: reflexivity.
  pose proof (bi_spec n); lia.
Qed.

Definition config(x:nat*nat):=
  let (a,b):=x in
  S0 (dai a-dai b) (bi b) 0.

Lemma Inc' a b:
  b<a ->
  config (a,b) -->+
  config (a,S b).
Proof.
  intros H.
  unfold config.
  cbn[dai].
  cbn[bi].
  pose proof (bi_spec b).
  pose proof (dai_spec a).
  pose proof (dai_spec b).
  pose proof (dai_spec (S b)) as H3.
  cbn[dai] in H3.
  cbn[Nat.pow] in H3.
  pose proof (Nat.pow_lt_mono_r 2 b a).
  pose proof (Nat.pow_le_mono_r 2 (S b) a) as H5.
  cbn[Nat.pow] in H5.
  applys_eq Inc; flia.
Qed.

Lemma Ov' a:
  config (a,a) -->+
  config (S a,O).
Proof.
  unfold config.
  pose proof (bi_spec a).
  pose proof (dai_spec a).
  cbn[dai].
  applys_eq (Ov (bi a)); flia.
Qed.

Definition P(x:nat*nat):Prop :=
let (a,b):=x in b<=a.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (0,0)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=P).
  2: unfold P; lia.
  intros i HP.
  destruct i as [a b].
  unfold P in HP.
  assert (b<a\/b=a) as E by lia.
  destruct E as [E|E].
  - eexists. split.
    1: apply Inc',E.
    unfold P. lia.
  - subst. eexists. split.
    1: apply Ov'.
    unfold P. lia.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LA_1LD0RB_1RA1LC_0RF0RC_---0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 c b a := const 0 <* [1;1] <* [0;0]^^a <* [0;1]^^b {{B}}> [1;1]^^c *> const 0.
Definition S1 b c := const 0 <* [0;1]^^b {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.


Lemma ROv0 a b:
  S0 (3+a) b 0 -->+
  S0 a 2 (1+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LROv b:
  S0 0 b 0 -->+
  S1 1 (1+b).
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 b 2 0.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma Inc a b:
  4+b<=a ->
  S0 (a) (b) 0 -->+
  S0 (a-b-4) (4+b*2) 0.
Proof.
  intros H1.
  replace (S0 a b 0) with (S0 (3+(a-3)) b 0) by flia.
  follow10 ROv0.
  follow (Inc0s (a-b-4) 2 0 (1+b)).
  finish.
Qed.

Lemma Ov b:
  S0 0 b 0 -->+
  S0 (2+b*2) 2 0.
Proof.
  follow10 LROv.
  follow Inc1s.
  replace ((1+b)*2+1) with (1+(2+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Fixpoint bi n :=
match n with
| O => 2%nat
| S n0 => 4+(bi n0)*2
end.

Fixpoint dai n :=
match n with
| O => O
| S n0 => dai n0 + bi n0 + 4
end.

Lemma bi_spec n:
  4 + bi n = 6*2^n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma dai_spec n:
  6 + dai n = 6*2^n.
Proof.
  induction n as [|n]; cbn.
  1: reflexivity.
  pose proof (bi_spec n); lia.
Qed.

Definition config(x:nat*nat):=
  let (a,b):=x in
  S0 (dai a-dai b) (bi b) 0.

Lemma Inc' a b:
  b<a ->
  config (a,b) -->+
  config (a,S b).
Proof.
  intros H.
  unfold config.
  cbn[dai].
  cbn[bi].
  pose proof (bi_spec b).
  pose proof (dai_spec a).
  pose proof (dai_spec b).
  pose proof (dai_spec (S b)) as H3.
  cbn[dai] in H3.
  cbn[Nat.pow] in H3.
  pose proof (Nat.pow_lt_mono_r 2 b a).
  pose proof (Nat.pow_le_mono_r 2 (S b) a) as H5.
  cbn[Nat.pow] in H5.
  applys_eq Inc; flia.
Qed.

Lemma Ov' a:
  config (a,a) -->+
  config (S a,O).
Proof.
  unfold config.
  pose proof (bi_spec a).
  pose proof (dai_spec a).
  cbn[dai].
  applys_eq (Ov (bi a)); flia.
Qed.

Definition P(x:nat*nat):Prop :=
let (a,b):=x in b<=a.

Lemma nonhalt:~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (0,0)%nat).
  1: unfold config,S0; solve_init.
  apply progress_nonhalt_cond with (P:=P).
  2: unfold P; lia.
  intros i HP.
  destruct i as [a b].
  unfold P in HP.
  assert (b<a\/b=a) as E by lia.
  destruct E as [E|E].
  - eexists. split.
    1: apply Inc',E.
    unfold P. lia.
  - subst. eexists. split.
    1: apply Ov'.
    unfold P. lia.
Qed.

End TM8.




