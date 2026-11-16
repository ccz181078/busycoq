From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Ltac unfold_config' :=
match goal with
| |- ?a -[_]->* ?b -> _ =>
  unfold_config_expr a;
  unfold_config_expr b
end.

Ltac follow' x :=
  pose proof x as Hx;
  gen Hx;
  unfold_config';
  simpl_rotate;
  intro Hx;
  try (
  follow Hx;
  clear Hx).

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0RC0LA_1RD1RC_0LB0LE_0RC1LF_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Definition R b c := [1;1]^^b *> [0] *> [1]^^c *> 0inf.

Lemma Inc1 l a b c:
  l <* [1]^^(2+a) <| R b (1+c) -->*
  l <* [1]^^(1+a) <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs1 l n b:
  l <* [1]^^(1+n) <| R b n -->*
  l <* [1]^^1 <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc1.
Qed.

Lemma Inc2 b c:
  0inf <| R b (1+c) -->*
  0inf <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs2 n b:
  0inf <| R b n -->*
  0inf <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc2.
Qed.

Lemma LROv l b:
  l <* <[0;1] <| R b 0 -->*
  l <| R 0 (1+b*2).
Proof.
  unfold R.
  es.
Qed.

Lemma ROv1 l b:
  l <* <[1;1] <| R (b) 0 -->*
  l <* <[1;0;1] <* [1]^^(b*2) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Lemma ROv2 b:
  0inf <| R (b) 0 -->+
  0inf <* [1]^^(1+b*2) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l,
  l <* [1]^^(1+n*2) <| R 0 0 -->*
  l <* [1] <| R n 0.

Lemma P1_S n:
  P1 n ->
  P1 (1+n*2).
Proof.
  unfold P1.
  intros HP1 l.
  replace (1+(1+n*2)*2) with ((1+n*2)+(2+n*2)) by lia.
  simpl_tape.
  follow HP1.
  simpl_tape.
  follow ROv1.
  follow' (HP1 ([0]*>[1]^^(2+n*2)*>l)).
  follow LROv.
  follow (Incs1 l (1+n*2)).
  cbn.
  finish.
Qed.

Definition config n :=
  0inf <* [1]^^(1+n*2) <| R 0 0.

Lemma BigStep n:
  P1 n ->
  config n -->+
  config (1+n*2).
Proof.
  unfold P1,config.
  intros HP1.
  follow HP1.
  rewrite const_unfold.
  follow LROv.
  follow Incs2.
  follow10 ROv2.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: unfold config,R; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1; es.
  unfold config.
  intros n HP1.
  eexists.
  split.
  2: apply P1_S,HP1.
  apply BigStep,HP1.
Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0LA_0RD1LF_1RE1RD_0LB0LC_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [0;1] *> r) (at level 30).

Definition R b c := [1;1]^^b *> [0] *> [1]^^c *> 0inf.

Lemma Inc1 l a b c:
  l <* [1]^^(1+a) <| R b (1+c) -->*
  l <* [1]^^(a) <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs1 l n b:
  l <* [1]^^(n) <| R b (n) -->*
  l <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc1.
Qed.

Lemma Inc2 b c:
  0inf <| R b (2+c) -->*
  0inf <| R (2+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs2 n b:
  0inf <| R b (1+n*2) -->*
  0inf <| R (n*2+b) 1.
Proof.
  gen b.
  ind n Inc2.
Qed.

Lemma LROv l b:
  l <* <[1;0] <| R b 0 -->*
  l <| R 0 (1+b*2).
Proof.
  unfold R.
  es.
Qed.

Lemma ROv1 l b:
  l <* <[1] <| R (b) 0 -->*
  l <* <[1;0] <* [1]^^(b*2) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Lemma ROv2 b:
  0inf <| R (b) 1 -->+
  0inf <* [0;1] <* [1]^^(2+b*2) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l,
  l <* [1]^^(n*2) <| R 0 0 -->*
  l <| R n 0.

Lemma P1_S n:
  P1 n ->
  P1 (1+n*2).
Proof.
  unfold P1.
  intros HP1 l.
  replace ((1+n*2)*2) with ((n*2)+(2+n*2)) by lia.
  simpl_tape.
  follow HP1.
  simpl_tape.
  follow ROv1.
  follow' (HP1 ([0]*>[1]^^(2+n*2)*>l)).
  follow LROv.
  follow (Incs1 l (1+n*2)).
  cbn.
  finish.
Qed.

Definition config n :=
  0inf <* <[1;0] <* [1]^^(n*2) <| R 0 0.

Lemma BigStep n:
  P1 n ->
  config n -->+
  config (1+n*2).
Proof.
  unfold P1,config.
  intros HP1.
  follow HP1.
  follow LROv.
  follow Incs2.
  follow10 ROv2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: unfold config,R; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1; es.
  unfold config.
  intros n HP1.
  eexists.
  split.
  2: apply P1_S,HP1.
  apply BigStep,HP1.
Qed.

End TM2.



Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0LB_1LA1RC_0RD1LF_1RE1RD_0LA0LC_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [0;1] *> r) (at level 30).

Definition R b c := [1;1]^^b *> [0] *> [1]^^c *> 0inf.

Lemma Inc1 l a b c:
  l <* [1]^^(1+a) <| R b (1+c) -->*
  l <* [1]^^(a) <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs1 l n b:
  l <* [1]^^(n) <| R b (n) -->*
  l <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc1.
Qed.

Lemma Inc2 b c:
  0inf <| R b (2+c) -->*
  0inf <| R (2+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs2 n b:
  0inf <| R (b) (n*2) -->*
  0inf <| R (n*2+b) 0.
Proof.
  gen b.
  ind n Inc2.
Qed.

Lemma LROv l b:
  l <* [0;1] <| R b 0 -->*
  l <| R 0 (1+b*2).
Proof.
  unfold R.
  es.
Qed.

Lemma LROv' l b:
  l <* <[1;1;0] <| R b 0 -->*
  l <| R 1 (b*2).
Proof.
  unfold R.
  es.
Qed.

Lemma ROv1 l b:
  l <* <[1] <| R (b) 0 -->*
  l <* <[1;0] <* [1]^^(b*2) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Lemma ROv2 b:
  0inf <| R (b) 0 -->+
  0inf <* <[1;1;0] <* [1]^^(b*2) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l,
  l <* [1]^^(n*2) <| R 0 0 -->*
  l <| R n 0.

Lemma P1_S n:
  P1 n ->
  P1 (1+n*2).
Proof.
  unfold P1.
  intros HP1 l.
  replace ((1+n*2)*2) with ((n*2)+(2+n*2)) by lia.
  simpl_tape.
  follow HP1.
  simpl_tape.
  follow ROv1.
  follow' (HP1 ([0]*>[1]^^(2+n*2)*>l)).
  follow LROv.
  follow (Incs1 l (1+n*2)).
  cbn.
  finish.
Qed.

Definition config n :=
  0inf <* <[1;1;0] <* [1]^^(n*2) <| R 0 0.

Lemma BigStep n:
  P1 n ->
  config n -->+
  config (1+n*2).
Proof.
  unfold P1,config.
  intros HP1.
  follow HP1.
  follow LROv'.
  follow Incs2.
  follow10 ROv2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config,R; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1; es.
  unfold config.
  intros n HP1.
  eexists.
  split.
  2: apply P1_S,HP1.
  apply BigStep,HP1.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0RA0LA_0RD1LF_1RE1RD_0LB0LC_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [0] *> r) (at level 30).

Definition R b c := [1;1]^^b *> [1;0] *> [1]^^c *> 0inf.

Lemma Inc1 l a b c:
  l <* [1]^^(1+a) <| R (b) (1+c) -->*
  l <* [1]^^(a) <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs1 l n b:
  l <* [1]^^(n) <| R b (n) -->*
  l <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc1.
Qed.

Lemma Inc2 b c:
  0inf <| R b (1+c) -->*
  0inf <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs2 n b:
  0inf <| R b n -->*
  0inf <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc2.
Qed.

Lemma LROv l b:
  l <* [0;1] <| R b 0 -->*
  l <| R 0 (1+b*2).
Proof.
  unfold R.
  es.
Qed.

Lemma ROv1 l b:
  l <* <[1] <| R (b) 0 -->*
  l <* <[1;0] <* [1]^^(b*2) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Lemma ROv2 b:
  0inf <| R (b) 0 -->+
  0inf <* [0;1] <* [1]^^(b*2) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l,
  l <* [1]^^(n*2) <| R 0 0 -->*
  l <| R n 0.

Lemma P1_S n:
  P1 n ->
  P1 (1+n*2).
Proof.
  unfold P1.
  intros HP1 l.
  replace ((1+n*2)*2) with ((n*2)+(2+n*2)) by lia.
  simpl_tape.
  follow HP1.
  simpl_tape.
  follow ROv1.
  follow' (HP1 ([0]*>[1]^^(2+n*2)*>l)).
  follow LROv.
  follow (Incs1 l (1+n*2)).
  cbn.
  es.
Qed.

Definition config n :=
  0inf <* <[1;0] <* [1]^^(n*2) <| R 0 0.

Lemma BigStep n:
  P1 n ->
  config n -->+
  config (1+n*2).
Proof.
  unfold P1,config.
  intros HP1.
  follow HP1.
  follow LROv.
  follow Incs2.
  follow10 ROv2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: unfold config,R; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1; es.
  unfold config.
  intros n HP1.
  eexists.
  split.
  2: apply P1_S,HP1.
  apply BigStep,HP1.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB1LF_0RC0LE_1RD1RC_0LB0LA_1LB1RB_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Definition R b c := [1;1]^^b *> [0] *> [1]^^c *> 0inf.

Lemma Inc1 l a b c:
  l <* [1]^^(2+a) <| R b (1+c) -->*
  l <* [1]^^(1+a) <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs1 l n b:
  l <* [1]^^(1+n) <| R b n -->*
  l <* [1]^^1 <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc1.
Qed.

Lemma Inc2 b c:
  0inf <| R b (1+c) -->*
  0inf <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs2 n b:
  0inf <| R b n -->*
  0inf <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc2.
Qed.

Lemma LROv l b:
  l <* <[0;1] <| R b 0 -->*
  l <| R 0 (1+b*2).
Proof.
  unfold R.
  es.
Qed.

Lemma ROv1 l b:
  l <* <[1;1] <| R (b) 0 -->*
  l <* <[1;0;1] <* [1]^^(b*2) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Lemma ROv2 b:
  0inf <| R (b) 0 -->+
  0inf <* [1]^^(1+b*2) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l,
  l <* [1]^^(1+n*2) <| R 0 0 -->*
  l <* [1] <| R n 0.

Lemma P1_S n:
  P1 n ->
  P1 (1+n*2).
Proof.
  unfold P1.
  intros HP1 l.
  replace (1+(1+n*2)*2) with ((1+n*2)+(2+n*2)) by lia.
  simpl_tape.
  follow HP1.
  simpl_tape.
  follow ROv1.
  follow' (HP1 ([0]*>[1]^^(2+n*2)*>l)).
  follow LROv.
  follow (Incs1 l (1+n*2)).
  cbn.
  finish.
Qed.

Definition config n :=
  0inf <* [1]^^(1+n*2) <| R 0 0.

Lemma BigStep n:
  P1 n ->
  config n -->+
  config (1+n*2).
Proof.
  unfold P1,config.
  intros HP1.
  follow HP1.
  rewrite const_unfold.
  follow LROv.
  follow Incs2.
  follow10 ROv2.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: unfold config,R; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1; es.
  unfold config.
  intros n HP1.
  eexists.
  split.
  2: apply P1_S,HP1.
  apply BigStep,HP1.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC1RB_0LA0LF_---0LE_0RB1RE_1LA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [1] *> r) (at level 30).

Definition R b c := [1;1;1]^^b *> [1;0] *> [1]^^c *> 0inf.

Lemma Inc1 l a b c:
  l <* [1]^^(3+a) <| R (b) (1+c) -->*
  l <* [1]^^(1+a) <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs1 l n b:
  l <* [1]^^(1+n*2) <| R b n -->*
  l <* [1]^^1 <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc1.
Qed.

Lemma Inc2 b c:
  0inf <| R b (1+c) -->*
  0inf <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs2 n b:
  0inf <| R b n -->*
  0inf <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc2.
Qed.

Lemma LROv l b:
  l <* <[0;1;1] <| R b 0 -->*
  l <| R 0 (2+b*3).
Proof.
  unfold R.
  es.
Qed.

Lemma ROv1 l b:
  l <* <[1;1;1] <| R (b) 0 -->*
  l <* <[1;0;1;1] <* [1]^^(b*3) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Lemma ROv2 b:
  0inf <| R (b) 0 -->+
  0inf <* <[0;1;1] <* [1]^^(b*3) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l,
  l <* [1]^^(1+n*3) <| R 0 0 -->*
  l <* [1] <| R n 0.

Lemma P1_S n:
  P1 n ->
  P1 (2+n*3).
Proof.
  unfold P1.
  intros HP1 l.
  replace (1+(2+n*3)*3) with ((1+n*3)+(6+n*6)) by lia.
  simpl_tape.
  follow HP1.
  simpl_tape.
  follow ROv1.
  follow' (HP1 ([1;0]*>[1]^^(5+n*6)*>l)).
  follow LROv.
  follow' (Incs1 l (2+n*3) 0).
  finish.
Qed.

Definition config n :=
  0inf <* [1] <* [1]^^(1+n*3) <| R 0 0.

Lemma BigStep n:
  P1 n ->
  config n -->+
  config (2+n*3).
Proof.
  unfold P1,config.
  intros HP1.
  follow HP1.
  rewrite const_unfold.
  follow LROv.
  follow Incs2.
  follow10 ROv2.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: unfold config,R; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1; es.
  unfold config.
  intros n HP1.
  eexists.
  split.
  2: apply P1_S,HP1.
  apply BigStep,HP1.
Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB1LE_0RC1RB_1RD1RC_0LA0LF_---0LB_1LA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [1] *> r) (at level 30).

Definition R b c := [1;1;1]^^b *> [1;0] *> [1]^^c *> 0inf.

Lemma Inc1 l a b c:
  l <* [1]^^(3+a) <| R (b) (1+c) -->*
  l <* [1]^^(1+a) <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs1 l n b:
  l <* [1]^^(1+n*2) <| R b n -->*
  l <* [1]^^1 <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc1.
Qed.

Lemma Inc2 b c:
  0inf <| R b (1+c) -->*
  0inf <| R (1+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs2 n b:
  0inf <| R b n -->*
  0inf <| R (n+b) 0.
Proof.
  gen b.
  ind n Inc2.
Qed.

Lemma LROv l b:
  l <* <[0;1;1] <| R b 0 -->*
  l <| R 0 (2+b*3).
Proof.
  unfold R.
  es.
Qed.

Lemma ROv1 l b:
  l <* <[1;1;1] <| R (b) 0 -->*
  l <* <[1;0;1;1] <* [1]^^(b*3) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Lemma ROv2 b:
  0inf <| R (b) 0 -->+
  0inf <* <[0;1;1] <* [1]^^(b*3) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l,
  l <* [1]^^(1+n*3) <| R 0 0 -->*
  l <* [1] <| R n 0.

Lemma P1_S n:
  P1 n ->
  P1 (2+n*3).
Proof.
  unfold P1.
  intros HP1 l.
  replace (1+(2+n*3)*3) with ((1+n*3)+(6+n*6)) by lia.
  simpl_tape.
  follow HP1.
  simpl_tape.
  follow ROv1.
  follow' (HP1 ([1;0]*>[1]^^(5+n*6)*>l)).
  follow LROv.
  follow' (Incs1 l (2+n*3) 0).
  finish.
Qed.

Definition config n :=
  0inf <* [1] <* [1]^^(1+n*3) <| R 0 0.

Lemma BigStep n:
  P1 n ->
  config n -->+
  config (2+n*3).
Proof.
  unfold P1,config.
  intros HP1.
  follow HP1.
  rewrite const_unfold.
  follow LROv.
  follow Incs2.
  follow10 ROv2.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: unfold config,R; solve_init.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1; es.
  unfold config.
  intros n HP1.
  eexists.
  split.
  2: apply P1_S,HP1.
  apply BigStep,HP1.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0LC0RB_1LA1LD_1LC0RE_1RD0LF_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{E}} [1;0] *> r) (at level 30).

Definition R b c k r := [1;0;1;0]^^(b) *> [1;1]^^c *> [0;1;0] *> [1;0]^^k *> r.

Lemma Inc l r a b c k:
  l <* [0;0]^^(1+a) <| R b (1+c) k r -->*
  l <* [0;0]^^(a) <| R (1+b) c k r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs l r n b k:
  l <* [0;0]^^(n) <| R b (n) k r -->*
  l <| R (n+b) 0 k r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b k:
  l <* <[0;0;0;0] <| R (b) 0 k r -->*
  l <* <[1;0] <* [0;0]^^(b*2) <| R 0 0 (S k) r.
Proof.
  unfold R.
  es.
Qed.

Lemma LROv l r b k:
  l <* <[1;0] <| R b 0 (S k) r -->*
  l <| R 0 (2+b*2) k r.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l r k,
  l <* [0;0]^^(n*2) <| R 0 0 k r -->*
  l <| R n 0 k r.

Lemma P1_S n:
  P1 n ->
  P1 (2+n*2).
Proof.
  unfold P1.
  intros HP1 l r k.
  replace ((2+n*2)*2) with (n*2+2+2+n*2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1.
  follow ROv.
  follow HP1.
  follow LROv.
  rewrite lpow_add'.
  follow Incs.
  finish.
Qed.

Lemma P1_n n0:
  exists n, P1 n /\ n0<=n.
Proof.
  induction n0.
  - exists O; split.
    2: lia.
    unfold P1.
    es.
  - destruct IHn0 as [n1 [HP1 Hn1]].
    eexists; split.
    1: apply P1_S,HP1.
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P1_n n) as [n1 [HP1 Hn1]].
  specialize (HP1 0inf 0inf O).
  unfold R in HP1.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    solve_init.
  - split.
    1: solve_sigma_score.
    lia.
Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC0LD_0LB0RC_1LA0RE_1RD0LF_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{E}} [1;0] *> r) (at level 30).

Definition R b c k r := [1;0;1;0]^^(b) *> [1;1]^^c *> [1;0;0;0] *> [0;0]^^k *> r.

Lemma Inc l r a b c k:
  l <* [0;0]^^(1+a) <| R b (1+c) k r -->*
  l <* [0;0]^^(a) <| R (1+b) c k r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs l r n b k:
  l <* [0;0]^^(n) <| R b (n) k r -->*
  l <| R (n+b) 0 k r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b k:
  l <* <[0;0;0;0] <| R (b) 0 k r -->*
  l <* <[1;0] <* [0;0]^^(b*2) <| R 0 0 (S k) r.
Proof.
  unfold R.
  es.
Qed.

Lemma LROv l r b k:
  l <* <[1;0] <| R b 0 (S k) r -->*
  l <| R 0 (2+b*2) k r.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l r k,
  l <* [0;0]^^(n*2) <| R 0 0 k r -->*
  l <| R n 0 k r.

Lemma P1_S n:
  P1 n ->
  P1 (2+n*2).
Proof.
  unfold P1.
  intros HP1 l r k.
  replace ((2+n*2)*2) with (n*2+2+2+n*2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1.
  follow ROv.
  follow HP1.
  follow LROv.
  rewrite lpow_add'.
  follow Incs.
  finish.
Qed.

Lemma P1_n n0:
  exists n, P1 n /\ n0<=n.
Proof.
  induction n0.
  - exists O; split.
    2: lia.
    unfold P1.
    es.
  - destruct IHn0 as [n1 [HP1 Hn1]].
    eexists; split.
    1: apply P1_S,HP1.
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P1_n n) as [n1 [HP1 Hn1]].
  specialize (HP1 0inf 0inf O).
  unfold R in HP1.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    solve_init.
  - split.
    1: solve_sigma_score.
    lia.
Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1LB0RE_1LC1LA_1RD0LC_0LB0RD_1RA0LF_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{E}} [1;0] *> r) (at level 30).

Definition R b c k r := [1;0;1;0]^^(b) *> [1;1]^^c *> [0;1;0] *> [1;0]^^k *> r.

Lemma Inc l r a b c k:
  l <* [0;0]^^(1+a) <| R b (1+c) k r -->*
  l <* [0;0]^^(a) <| R (1+b) c k r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs l r n b k:
  l <* [0;0]^^(n) <| R b (n) k r -->*
  l <| R (n+b) 0 k r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b k:
  l <* <[0;0;0;0] <| R (b) 0 k r -->*
  l <* <[1;0] <* [0;0]^^(b*2) <| R 0 0 (S k) r.
Proof.
  unfold R.
  es.
Qed.

Lemma LROv l r b k:
  l <* <[1;0] <| R b 0 (S k) r -->*
  l <| R 0 (2+b*2) k r.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l r k,
  l <* [0;0]^^(n*2) <| R 0 0 k r -->*
  l <| R n 0 k r.

Lemma P1_S n:
  P1 n ->
  P1 (2+n*2).
Proof.
  unfold P1.
  intros HP1 l r k.
  replace ((2+n*2)*2) with (n*2+2+2+n*2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1.
  follow ROv.
  follow HP1.
  follow LROv.
  rewrite lpow_add'.
  follow Incs.
  finish.
Qed.

Lemma P1_n n0:
  exists n, P1 n /\ n0<=n.
Proof.
  induction n0.
  - exists O; split.
    2: lia.
    unfold P1.
    es.
  - destruct IHn0 as [n1 [HP1 Hn1]].
    eexists; split.
    1: apply P1_S,HP1.
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P1_n n) as [n1 [HP1 Hn1]].
  specialize (HP1 0inf ([0;1]*>0inf) O).
  unfold R in HP1.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    solve_init.
  - split.
    1: solve_sigma_score.
    lia.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC0LB_0LA0RC_1LA0RE_1RD0LF_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{E}} [1;0] *> r) (at level 30).

Definition R b c k r := [1;0;1;0]^^(b) *> [1;1]^^c *> [0;1;0] *> [1;0]^^k *> r.

Lemma Inc l r a b c k:
  l <* [0;0]^^(1+a) <| R b (1+c) k r -->*
  l <* [0;0]^^(a) <| R (1+b) c k r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs l r n b k:
  l <* [0;0]^^(n) <| R b (n) k r -->*
  l <| R (n+b) 0 k r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b k:
  l <* <[0;0;0;0] <| R (b) 0 k r -->*
  l <* <[1;0] <* [0;0]^^(b*2) <| R 0 0 (S k) r.
Proof.
  unfold R.
  es.
Qed.

Lemma LROv l r b k:
  l <* <[1;0] <| R b 0 (S k) r -->*
  l <| R 0 (2+b*2) k r.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l r k,
  l <* [0;0]^^(n*2) <| R 0 0 k r -->*
  l <| R n 0 k r.

Lemma P1_S n:
  P1 n ->
  P1 (2+n*2).
Proof.
  unfold P1.
  intros HP1 l r k.
  replace ((2+n*2)*2) with (n*2+2+2+n*2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1.
  follow ROv.
  follow HP1.
  follow LROv.
  rewrite lpow_add'.
  follow Incs.
  finish.
Qed.

Lemma P1_n n0:
  exists n, P1 n /\ n0<=n.
Proof.
  induction n0.
  - exists O; split.
    2: lia.
    unfold P1.
    es.
  - destruct IHn0 as [n1 [HP1 Hn1]].
    eexists; split.
    1: apply P1_S,HP1.
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P1_n n) as [n1 [HP1 Hn1]].
  specialize (HP1 0inf ([1;0]*>0inf) O).
  unfold R in HP1.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    solve_init.
  - split.
    1: solve_sigma_score.
    lia.
Qed.

End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LA_1LD0RB_1LE1LC_1RF0LC_0LE0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1;0] *> r) (at level 30).

Definition R b c k r := [1;0;1;0]^^(b) *> [1;1]^^c *> [1;0;0;0] *> [0;0]^^k *> r.

Lemma Inc l r a b c k:
  l <* [0;0]^^(1+a) <| R b (1+c) k r -->*
  l <* [0;0]^^(a) <| R (1+b) c k r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs l r n b k:
  l <* [0;0]^^(n) <| R b (n) k r -->*
  l <| R (n+b) 0 k r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b k:
  l <* <[0;0;0;0] <| R (b) 0 k r -->*
  l <* <[1;0] <* [0;0]^^(b*2) <| R 0 0 (S k) r.
Proof.
  unfold R.
  es.
Qed.

Lemma LROv l r b k:
  l <* <[1;0] <| R b 0 (S k) r -->*
  l <| R 0 (2+b*2) k r.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l r k,
  l <* [0;0]^^(n*2) <| R 0 0 k r -->*
  l <| R n 0 k r.

Lemma P1_S n:
  P1 n ->
  P1 (2+n*2).
Proof.
  unfold P1.
  intros HP1 l r k.
  replace ((2+n*2)*2) with (n*2+2+2+n*2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1.
  follow ROv.
  follow HP1.
  follow LROv.
  rewrite lpow_add'.
  follow Incs.
  finish.
Qed.

Lemma P1_n n0:
  exists n, P1 n /\ n0<=n.
Proof.
  induction n0.
  - exists O; split.
    2: lia.
    unfold P1.
    es.
  - destruct IHn0 as [n1 [HP1 Hn1]].
    eexists; split.
    1: apply P1_S,HP1.
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P1_n n) as [n1 [HP1 Hn1]].
  specialize (HP1 0inf ([0;1;1;1;1]*>0inf) O).
  unfold R in HP1.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    solve_init.
  - split.
    1: solve_sigma_score.
    lia.
Qed.

End TM12.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC0RA_1LD1LB_1RE0LD_0LC0RE_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [1;0] *> r) (at level 30).

Definition R b c k r := [1;0;1;0]^^(b) *> [1;1]^^c *> [0;1;0] *> [1;0]^^k *> r.

Lemma Inc l r a b c k:
  l <* [0;0]^^(1+a) <| R b (1+c) k r -->*
  l <* [0;0]^^(a) <| R (1+b) c k r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs l r n b k:
  l <* [0;0]^^(n) <| R b (n) k r -->*
  l <| R (n+b) 0 k r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b k:
  l <* <[0;0;0;0] <| R (b) 0 k r -->*
  l <* <[1;0] <* [0;0]^^(b*2) <| R 0 0 (S k) r.
Proof.
  unfold R.
  es.
Qed.

Lemma LROv l r b k:
  l <* <[1;0] <| R b 0 (S k) r -->*
  l <| R 0 (2+b*2) k r.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l r k,
  l <* [0;0]^^(n*2) <| R 0 0 k r -->*
  l <| R n 0 k r.

Lemma P1_S n:
  P1 n ->
  P1 (2+n*2).
Proof.
  unfold P1.
  intros HP1 l r k.
  replace ((2+n*2)*2) with (n*2+2+2+n*2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1.
  follow ROv.
  follow HP1.
  follow LROv.
  rewrite lpow_add'.
  follow Incs.
  finish.
Qed.

Lemma P1_n n0:
  exists n, P1 n /\ n0<=n.
Proof.
  induction n0.
  - exists O; split.
    2: lia.
    unfold P1.
    es.
  - destruct IHn0 as [n1 [HP1 Hn1]].
    eexists; split.
    1: apply P1_S,HP1.
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P1_n n) as [n1 [HP1 Hn1]].
  specialize (HP1 0inf ([1;1;1;0;1;0;1]*>0inf) O).
  unfold R in HP1.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    solve_init.
  - split.
    1: solve_sigma_score.
    lia.
Qed.

End TM13.


Module TM14.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LA_1LD0RB_1LE1LC_1RF0LE_0LD0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1;0] *> r) (at level 30).

Definition R b c k r := [1;0;1;0]^^(b) *> [1;1]^^c *> [0;1;0] *> [1;0]^^k *> r.

Lemma Inc l r a b c k:
  l <* [0;0]^^(1+a) <| R b (1+c) k r -->*
  l <* [0;0]^^(a) <| R (1+b) c k r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs l r n b k:
  l <* [0;0]^^(n) <| R b (n) k r -->*
  l <| R (n+b) 0 k r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b k:
  l <* <[0;0;0;0] <| R (b) 0 k r -->*
  l <* <[1;0] <* [0;0]^^(b*2) <| R 0 0 (S k) r.
Proof.
  unfold R.
  es.
Qed.

Lemma LROv l r b k:
  l <* <[1;0] <| R b 0 (S k) r -->*
  l <| R 0 (2+b*2) k r.
Proof.
  unfold R.
  es.
Qed.

Definition P1 n :=
  forall l r k,
  l <* [0;0]^^(n*2) <| R 0 0 k r -->*
  l <| R n 0 k r.

Lemma P1_S n:
  P1 n ->
  P1 (2+n*2).
Proof.
  unfold P1.
  intros HP1 l r k.
  replace ((2+n*2)*2) with (n*2+2+2+n*2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1.
  follow ROv.
  follow HP1.
  follow LROv.
  rewrite lpow_add'.
  follow Incs.
  finish.
Qed.

Lemma P1_n n0:
  exists n, P1 n /\ n0<=n.
Proof.
  induction n0.
  - exists O; split.
    2: lia.
    unfold P1.
    es.
  - destruct IHn0 as [n1 [HP1 Hn1]].
    eexists; split.
    1: apply P1_S,HP1.
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P1_n n) as [n1 [HP1 Hn1]].
  specialize (HP1 0inf ([1;1;1;1;1;1;1;0;1;0;1]*>0inf) O).
  unfold R in HP1.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    solve_init.
  - split.
    1: solve_sigma_score.
    lia.
Qed.

End TM14.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC0RB_0LD0LA_0RA1LC_1LE1LF_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [] *> r) (at level 30).

Definition R b c := [1]^^(3+b) *> [0] *> [1]^^c *> const 0.

Lemma Inc l a b c:
  l <* [0]^^(2+a) <| R b (1+c) -->*
  l <* [0]^^(a) <| R (3+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs l n b:
  l <* [0]^^(n*2) <| R b n -->*
  l <| R (n*3+b) 0.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l b:
  l <* [0;0] <| R (b) 0 -->*
  l <* <[0;1] <* [0]^^(b) <| R 1 0.
Proof.
  unfold R.
  es.
Qed.

Lemma LROv0 l b:
  l <* <[0;0;1] <| R b 0 -->*
  l <| R 0 (2+b).
Proof.
  unfold R.
  es.
Qed.

Lemma LROv1 l b:
  l <* <[0;0;1;0] <| R b 0 -->*
  l <| R 1 (2+b).
Proof.
  unfold R.
  es.
Qed.

Definition P0 n :=
  forall l,
  l <* [0]^^n <| R 0 0 -->*
  l <| R n 0.

Definition P1 n :=
  forall l,
  l <* [0]^^n <| R 1 0 -->*
  l <| R (1+n) 0.

Lemma P1_S n:
  P1 n ->
  P1 (9+n*3).
Proof.
  unfold P1.
  intros HP1 l.
  replace (9+n*3) with (n+2+1+6+n*2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1.
  follow ROv.
  rewrite Nat.add_comm,<-lpow_add'.
  follow HP1.
  follow LROv1.
  rewrite lpow_add'.
  replace (6+n*2) with ((3+n)*2) by lia.
  follow Incs.
  finish.
Qed.

Lemma P0_S n:
  P0 n ->
  P1 n ->
  P0 (9+n*3).
Proof.
  unfold P0,P1.
  intros HP0 HP1 l.
  replace (9+n*3) with (n+2+1+6+n*2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP0.
  follow ROv.
  follow HP1.
  follow LROv0.
  rewrite lpow_add'.
  replace (6+n*2) with ((3+n)*2) by lia.
  follow Incs.
  finish.
Qed.

Lemma P_n n0:
  exists n, P0 n /\ P1 n /\ n0<=n.
Proof.
  induction n0.
  - exists O; repeat split.
    3: lia.
    + unfold P0; es.
    + unfold P1; es.
  - destruct IHn0 as [n1 [HP0 [HP1 Hn1]]].
    eexists; repeat split.
    2: apply P1_S,HP1.
    1: apply P0_S; assumption.
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [n1 [HP0 [HP1 Hn1]]].
  specialize (HP0 0inf).
  unfold R in HP0.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP0.
    rewrite lpow_all0.
    2: solve_const0_eq.
    solve_init.
  - split.
    1: solve_sigma_score.
    lia.
Qed.

End TM15.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1RB0LB_1LA1RC_0RD0RC_1RF0LE_1LE1LB_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [] *> r) (at level 30).

Definition R b c := [1]^^(2+b) *> [0] *> [1]^^c *> const 0.

Lemma Inc l a b c:
  l <* [0]^^(2+a) <| R b (2+c) -->*
  l <* [0]^^(a) <| R (4+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs l n b:
  l <* [0]^^(n*2) <| R b (n*2) -->*
  l <| R (n*4+b) 0.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs' l n b:
  l <* [0]^^(n*2) <| R b (1+n*2) -->*
  l <| R (n*4+b) 1.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l b:
  l <* [0;0] <| R (b) 0 -->*
  l <* <[1;1;0] <* [0]^^(b) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Lemma LROv l b:
  l <* <[1;1;0] <| R b 0 -->*
  l <| R 0 (2+b).
Proof.
  unfold R.
  es.
Qed.

Lemma LROv' l b:
  l <* <[0;0;1;0] <| R b 0 -->*
  l <| R 2 (1+b).
Proof.
  unfold R.
  es.
Qed.

Definition P0 n :=
  forall l,
  l <* [0]^^(n*2) <| R 0 0 -->+
  l <| R (n*2) 0.

Lemma P0_S n:
  P0 n ->
  P0 (2+n*2).
Proof.
  unfold P0.
  intros HP0 l.
  replace ((2+n*2)*2) with (n*2+2+2+n*2) by lia.
  repeat rewrite <-lpow_add'.
  follow10 HP0.
  follow ROv.
  follow100 HP0.
  follow LROv.
  rewrite lpow_add'.
  replace (2+n*2) with ((1+n)*2) by lia.
  follow Incs.
  finish.
Qed.

Definition config n :=
  0inf <* <[0;0;1;0] <* [0]^^(n*2) <| R 0 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 2).
  1: unfold config,R; solve_init.
  eapply progress_nonhalt_cond with (P:=P0).
  2: unfold P0; es.
  intros n HP0.
  eexists; split.
  2: apply P0_S,HP0.
  unfold config.
  unfold P0 in HP0.
  follow10 (HP0 ([0;1;0;0]*>0inf)).
  follow LROv'.
  rewrite <-(lpow_all0 [0] (n*2)).
  2: solve_const0_eq.
  follow Incs'.
  rewrite lpow_all0.
  2: solve_const0_eq.
  unfold R.
  es.
Qed.

End TM16.


Module TM17.
Definition tm := Eval compute in (TM_from_str "1RB1LB_1LC0RF_0RA1LD_1LE---_0LC0LA_1RE0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{E}} [] *> r) (at level 30).

Definition R b c := [1]^^(8+b) *> [0] *> [1]^^c *> const 0.

Lemma Inc l a b c:
  l <* [0]^^(2+a) <| R b (1+c) -->*
  l <* [0]^^(a) <| R (3+b) c.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs l n b:
  l <* [0]^^(n*2) <| R b n -->*
  l <| R (n*3+b) 0.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l b:
  l <* [0;0] <| R (b) 0 -->*
  l <* <[0;1;0] <* [0]^^(b) <| R 0 0.
Proof.
  unfold R.
  es.
Qed.

Lemma LROv l b:
  l <* <[0;0;0;0;0;1;0] <| R b 0 -->*
  l <| R 0 (6+b).
Proof.
  unfold R.
  es.
Qed.

Lemma LROv' l b:
  l <* <[0;0;1;0;0;0;1;0] <| R b 0 -->*
  l <| R 0 (7+b).
Proof.
  unfold R.
  es.
Qed.

Definition P0 n :=
  forall l,
  l <* [0]^^(n*2) <| R 0 0 -->+
  l <| R (n*2) 0.

Lemma P0_S n:
  P0 n ->
  P0 (9+n*3).
Proof.
  unfold P0.
  intros HP0 l.
  replace ((9+n*3)*2) with (n*2+2+4+(6+n*2)*2) by lia.
  repeat rewrite <-lpow_add'.
  follow10 HP0.
  follow ROv.
  follow100 HP0.
  follow LROv.
  follow Incs.
  finish.
Qed.

Definition config n :=
  0inf <* <[0;0;1;0;0;0;0] <* [0]^^(n*2) <| R 0 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 9).
  1: unfold config,R; solve_init.
  eapply progress_nonhalt_cond with (P:=P0).
  2: unfold P0; es.
  intros n HP0.
  eexists; split.
  2: apply P0_S,HP0.
  unfold config.
  unfold P0 in HP0.
  follow10 (HP0 ([0;0]*>[0;0;1;0;0]*>0inf)).
  follow ROv.
  follow100 HP0.
  follow LROv'.
  rewrite <-(lpow_all0 [0] ((7+n*2)*2)).
  2: solve_const0_eq.
  follow Incs.
  rewrite lpow_all0.
  2: solve_const0_eq.
  unfold R.
  es.
Qed.

End TM17.


