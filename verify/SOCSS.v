From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import SimplTape.

Open Scope list.


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

Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC0RA_1LA0RD_1RE1LE_1LC1RC_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l {{C}}> [1;0;1;0]^^n *> [1;0;0] *> r -->*
  l <{{A}} [1;0;1;0]^^n *> [1;1;1] *> r.

Definition P1 n :=
  forall l r,
  l <* <[0;1;1] {{C}}> [0;1;0;1]^^n *> [1;1] *> r -->*
  l <{{A}} [1;0;1;0]^^n *> [1;1;1;1;1] *> r.

Lemma P1_n n:
  P1 n.
Proof.
  unfold P1.
  induction n.
  1: es.
  intros l r.
  do 10 step1.
  follow IHn.
  er.
  follow IHn.
  es.
Qed.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  do 10 step1.
  follow IHn.
  er.
  follow (P1_n n).
  es.
Qed.

Definition S0 a b :=
  0inf <* <[1;0]^^a <* <[0;0;1;1] {{C}}> [1;0;1;0]^^b *> [1] *> 0inf.

Lemma Inc a b:
  S0 (1+a) b -->*
  S0 a (1+b).
Proof.
  unfold S0.
  replace (0inf) with ([0;0]*>0inf) by solve_const0_eq.
  follow (P0_n b).
  er.
  follow (P1_n b).
  es.
Qed.

Lemma Incs a b:
  S0 a b -->*
  S0 0 (a+b).
Proof.
  gen b.
  ind a Inc.
Qed.

Lemma BigStep n:
  S0 (n) 0 -->+
  S0 (n*2+4) 0.
Proof.
  follow Incs.
  unfold S0.
  replace (0inf) with ([0;0]*>0inf) by solve_const0_eq.
  follow (P0_n (n+0)).
  er.
  replace (0inf) with ([0]*>0inf) by solve_const0_eq.
  follow (P1_n n).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 2 0).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S0 x 0).
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0RF_0LA0RB_1RE1LE_1LA1RA_---1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l {{A}}> [1;0;1;0]^^n *> [1;0;0] *> r -->*
  l <{{B}} [1;0;1;0]^^n *> [1;1;1] *> r.

Definition P1 n :=
  forall l r,
  l <* <[0;1;1] {{A}}> [0;1;0;1]^^n *> [1;1] *> r -->*
  l <{{B}} [1;0;1;0]^^n *> [1;1;1;1;1] *> r.

Lemma P1_n n:
  P1 n.
Proof.
  unfold P1.
  induction n.
  1: es.
  intros l r.
  do 10 step1.
  follow IHn.
  er.
  follow IHn.
  es.
Qed.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  do 10 step1.
  follow IHn.
  er.
  follow (P1_n n).
  es.
Qed.

Definition S0 a b :=
  0inf <* <[1;0]^^a <* <[0;0;1;1] {{A}}> [1;0;1;0]^^b *> [1] *> 0inf.

Lemma Inc a b:
  S0 (1+a) b -->*
  S0 a (1+b).
Proof.
  unfold S0.
  replace (0inf) with ([0;0]*>0inf) by solve_const0_eq.
  follow (P0_n b).
  er.
  follow (P1_n b).
  es.
Qed.

Lemma Incs a b:
  S0 a b -->*
  S0 0 (a+b).
Proof.
  gen b.
  ind a Inc.
Qed.

Lemma BigStep n:
  S0 (n) 0 -->+
  S0 (n*2+4) 0.
Proof.
  follow Incs.
  unfold S0.
  replace (0inf) with ([0;0]*>0inf) by solve_const0_eq.
  follow (P0_n (n+0)).
  er.
  replace (0inf) with ([0]*>0inf) by solve_const0_eq.
  follow (P1_n n).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 4 0).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S0 x 0).
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC0RF_1LD1RB_1RE0LA_1LF0RD_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l {{D}}> [0;1]^^(4+n*3) *> [0;0] *> r -->*
  l <{{A}} [0;1]^^(3+n*3) *> [0;0;1;1] *> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  do 6 step1.
  follow IHn.
  do 4 (er; sr).
  do 4 step1.
  follow' (IHn ([0;1;0;1;1]*>l) ([1]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf {{D}}> [0;1]^^(4+n*3) *> 0inf.

Definition S1 a b :=
  0inf <* <[0;1]^^a <{{D}} [1;0]^^b *> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof. es. Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma BigStep n:
  S0 n -->+ S0 (n*2+3).
Proof.
  unfold S0.
  replace (0inf) with ([0;0]*>0inf) by solve_const0_eq.
  follow (P0_n n).
  remember (3+n*3) as n'.
  es. er.
  unfold Sym.
  replace (1>>0inf) with ([1;0]*>0inf) by solve_const0_eq.
  follow (Incs1 n' 7).
  subst.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 2).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LE_1LD0RB_---0LB_1RF1LB_1RA0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l {{B}}> [0;1]^^(4+n*3) *> [0;0] *> r -->*
  l <{{E}} [0;1]^^(3+n*3) *> [0;0;1;1] *> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  do 6 step1.
  follow IHn.
  do 4 (er; sr).
  do 4 step1.
  follow' (IHn ([0;1;0;1;1]*>l) ([1]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf {{B}}> [0;1]^^(4+n*3) *> 0inf.

Definition S1 a b :=
  0inf <* <[0;1]^^a <{{B}} [1;0]^^b *> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof. es. Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma BigStep n:
  S0 n -->+ S0 (n*2+3).
Proof.
  unfold S0.
  replace (0inf) with ([0;0]*>0inf) by solve_const0_eq.
  follow (P0_n n).
  remember (3+n*3) as n'.
  es. er.
  unfold Sym.
  replace (1>>0inf) with ([1;0]*>0inf) by solve_const0_eq.
  follow (Incs1 n' 7).
  subst.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RA_1LD0LC_1RE0LD_1RF0RB_0RE0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l <* <[1;0]^^n <* [0] {{B}}> [0;0]^^n *> r -->*
  l <* [1;1]^^n <* [0] <* [1;1]^^n {{B}}> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([0;1]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  step1.
  follow' (IHn ([1;1]*>l) ([1;0]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* [1] <* <[1;0]^^n <* [0] {{B}}> 0inf.

Lemma BigStep n:
  S0 (1+n) -->+ S0 (1+(1+n)*2).
Proof.
  unfold S0.
  replace (0inf) with (([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow (P0_n (1+n)).
  simpl_lpow_all0.
  do 4 (er; sr).
  rewrite lpow_add'.
  replace (n+n) with (n*2) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1+5)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S0 (1+x)).
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0LB_1RE0RD_1LA1RF_0RC0RC_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l <* <[1;0]^^n <* [0] {{D}}> [0;0]^^n *> r -->*
  l <* [1;1]^^n <* [0] <* [1;1]^^n {{D}}> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([0;1]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  step1.
  follow' (IHn ([1;1]*>l) ([1;0]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* [1] <* <[1;0]^^n <* [0] {{D}}> 0inf.

Lemma BigStep n:
  S0 (1+n) -->+ S0 (1+(1+n)*2).
Proof.
  unfold S0.
  replace (0inf) with (([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow (P0_n (1+n)).
  simpl_lpow_all0.
  do 4 (er; sr).
  rewrite lpow_add'.
  replace (n+n) with (n*2) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1+6)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S0 (1+x)).
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD0LF_1RF0RA_1RA---_0RD0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l <* <[1;0]^^n <* [0] {{A}}> [0;0]^^n *> r -->*
  l <* [1;1]^^n <* [0] <* [1;1]^^n {{A}}> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([0;1]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  step1.
  follow' (IHn ([1;1]*>l) ([1;0]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^n <* [0] {{A}}> 0inf.

Lemma BigStep n:
  S0 n -->+ S0 (2+n*2).
Proof.
  unfold S0.
  replace (0inf) with (([0;0]^^(n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow (P0_n (n)).
  simpl_lpow_all0.
  do 3 (er; sr).
  er.
  follow (P0_n n).
  do 4 (er; sr).
  rewrite lpow_add'.
  replace (n+n) with (n*2) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1+5)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_0LD0RE_1RD0LC_1RE0RA_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l {{E}}> [0;0]^^n *> [0;1;0;0] *> [0;0]^^n *> r -->*
  l <* <[0;1]^^n <* <[0;0;1;1] <* [1;1]^^n {{A}}> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  do 2 step1.
  follow' (IHn ([1;1]*>l) ([0;0]*>r)).
  do 2 (er; sr).
  do 2 step1.
  follow' (IHn ([1;0]*>l) ([1;0]*>r)).
  es.
Qed.

Definition S0 '(m,n) :=
  0inf <* [1]^^m <* [0] {{E}}> [0;0]^^n *> [0;1] *> 0inf.

Lemma BigStep m n:
  S0 (m,n) -->+ S0 (1+n*2+m,1+n).
Proof.
  unfold S0.
  replace (0inf) with (([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow (P0_n (n)).
  simpl_lpow_all0.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1,0)%nat).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [m n].
  eexists.
  apply BigStep.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RA_1LD0LC_0LE0RF_1RE0LD_1RF0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l {{F}}> [0;0]^^n *> [0;1;0;0] *> [0;0]^^n *> r -->*
  l <* <[0;1]^^n <* <[0;0;1;1] <* [1;1]^^n {{B}}> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  do 2 step1.
  follow' (IHn ([1;1]*>l) ([0;0]*>r)).
  do 2 (er; sr).
  do 2 step1.
  follow' (IHn ([1;0]*>l) ([1;0]*>r)).
  es.
Qed.

Definition S0 '(m,n) :=
  0inf <* [1]^^m <* [0] {{F}}> [0;0]^^n *> [0;1] *> 0inf.

Lemma BigStep m n:
  S0 (m,n) -->+ S0 (1+n*2+m,1+n).
Proof.
  unfold S0.
  replace (0inf) with (([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow (P0_n (n)).
  simpl_lpow_all0.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (5,1)%nat).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [m n].
  eexists.
  apply BigStep.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1RB1LA_0LB1RC_1LA1RD_0LE0RB_1LB0RF_0RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma P0_n n:
  forall l r,
  l <* <[1;1;0]^^n <{{A}} [1;1;1;0] *> r -->*
  l <{{A}} [1;1;1]^^(1+n) *> [0] *> r.
Proof.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([0;1;1]*>l) r).
  er. sr.
  er.
  follow IHn.
  es.
Qed.

Definition S1 m n :=
  0inf <* [1] <* <[1;1;0]^^m <{{A}} [1;1;1;0] *> [1;0]^^n *> 0inf.

Lemma Inc1 m n:
  S1 m (1+n) -->*
  S1 (1+m) n.
Proof.
  follow P0_n.
  es.
Qed.

Lemma Incs1 m n:
  S1 m n -->*
  S1 (n+m) 0.
Proof.
  gen m.
  ind n Inc1.
Qed.

Lemma P1_n n:
  forall l r,
  l <* <[1;1;0]^^(1+n) <{{A}} [1;1;0] *> [0;0]^^(1+n) *> r -->*
  l <* <[1;1;1]^^(1+n) <{{A}} [1;1;0] *> [1;0]^^(1+n) *> r.
Proof.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([0;1;1]*>l) ([0;0]*>r)).
  do 4 (er; sr).
  do 3 step1.
  follow' (IHn ([1;1;1]*>l) ([1;0]*>r)).
  es.
Qed.

Lemma BigStep n:
  S1 (n) 0 -->+ S1 (2+n*2) 0.
Proof.
  unfold S1.
  follow (P0_n).
  er. sr.
  do 2 step1.
  replace (0inf) with ([0]*>([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow P1_n.
  rewrite (lpow_all0 [0;0]).
  2: solve_const0_eq.
  do 2 (er; sr).
  do 6 step1.
  mid (S1 (1+n) (1+n)).
  1: unfold S1; es.
  follow Incs1.
  replace (1+n+(1+n)) with (2+n*2) by lia.
  unfold S1.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 1 0).
  1: unfold S1; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S1 x 0).
  intros.
  eexists.
  apply BigStep.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC1LB_0LC1RA_0LE0RC_1LC0RF_0RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma P0_n n:
  forall l r,
  l <* <[1;1;0]^^n <{{B}} [1;1;1;0] *> r -->*
  l <{{B}} [1;1;1]^^(1+n) *> [0] *> r.
Proof.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([0;1;1]*>l) r).
  er. sr.
  er.
  follow IHn.
  es.
Qed.

Definition S1 m n :=
  0inf <* [1] <* <[1;1;0]^^m <{{B}} [1;1;1;0] *> [1;0]^^n *> 0inf.

Lemma Inc1 m n:
  S1 m (1+n) -->*
  S1 (1+m) n.
Proof.
  follow P0_n.
  es.
Qed.

Lemma Incs1 m n:
  S1 m n -->*
  S1 (n+m) 0.
Proof.
  gen m.
  ind n Inc1.
Qed.

Lemma P1_n n:
  forall l r,
  l <* <[1;1;0]^^(1+n) <{{B}} [1;1;0] *> [0;0]^^(1+n) *> r -->*
  l <* <[1;1;1]^^(1+n) <{{B}} [1;1;0] *> [1;0]^^(1+n) *> r.
Proof.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([0;1;1]*>l) ([0;0]*>r)).
  do 4 (er; sr).
  do 3 step1.
  follow' (IHn ([1;1;1]*>l) ([1;0]*>r)).
  es.
Qed.

Lemma BigStep n:
  S1 (n) 0 -->+ S1 (2+n*2) 0.
Proof.
  unfold S1.
  follow (P0_n).
  er. sr.
  do 2 step1.
  replace (0inf) with ([0]*>([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow P1_n.
  rewrite (lpow_all0 [0;0]).
  2: solve_const0_eq.
  do 2 (er; sr).
  do 6 step1.
  mid (S1 (1+n) (1+n)).
  1: unfold S1; es.
  follow Incs1.
  replace (1+n+(1+n)) with (2+n*2) by lia.
  unfold S1.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 2 0).
  1: unfold S1; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S1 x 0).
  intros.
  eexists.
  apply BigStep.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1LB0RB_1RB0RC_1RD0LF_1LE1RC_1LA0LE_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma P0_n n:
  forall l r,
  l <* [1;1]^^n <* <[1;0] {{C}}> [0;0]^^(1+n) *> r -->*
  l <* <[0;1]^^n <* [0] {{B}}> [1] *> [0;1]^^(1+n) *> r.
Proof.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([1;1]*>l) ([0;0]*>r)).
  do 4 (er; sr).
  step1.
  follow' (IHn ([1;0]*>l) ([0;1]*>r)).
  es.
Qed.

Fixpoint L n :=
match n with
| O => 0inf
| S n0 => L n0 <* [0] <* [1;1]^^(n*2)
end.

Lemma LInc n r:
  L n <* <[1;0] {{C}}> [0;0]^^(2+n*2) *> r -->+
  L (S n) <* <[1;0] {{C}}> r.
Proof.
  gen r.
  induction n; intros.
  1: es.
  cbn[L] in *.
  follow' (P0_n (2+n*2) ([0]*>L n) ([0;0]*>r)).
  do 3 (er; sr).
  do 2 step1.
  follow100 IHn. clear IHn.
  es.
Qed.

Definition S0 n :=
  L n <* <[1;0] {{C}}> 0inf.

Lemma BigStep n:
  S0 n -->+ S0 (S n).
Proof.
  unfold S0.
  replace (0inf) with ([0;0]^^(2+n*2)*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow10 LInc.
  simpl_lpow_all0.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros.
  eexists.
  apply BigStep.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1LB0RB_1RB1RC_0RD0LF_1LE0RC_0LE1LA_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma P0_n n:
  forall l r,
  l <* [1;1]^^n <* <[1;1] {{C}}> [0;0]^^(1+n) *> r -->*
  l <* <[0;1]^^n <* [0] {{B}}> [1] *> [0;1]^^(1+n) *> r.
Proof.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([1;1]*>l) ([0;0]*>r)).
  do 4 (er; sr).
  step1.
  follow' (IHn ([1;0]*>l) ([0;1]*>r)).
  es.
Qed.

Fixpoint L n :=
match n with
| O => 0inf
| S n0 => L n0 <* [0] <* [1;1]^^(n*2)
end.

Lemma LInc n r:
  L n <* <[1;1] {{C}}> [0;0]^^(2+n*2) *> r -->+
  L (S n) <* <[1;1] {{C}}> r.
Proof.
  gen r.
  induction n; intros.
  1: es.
  cbn[L] in *.
  follow' (P0_n (2+n*2) ([0]*>L n) ([0;0]*>r)).
  do 3 (er; sr).
  do 2 step1.
  follow100 IHn. clear IHn.
  es.
Qed.

Definition S0 n :=
  L n <* <[1;1] {{C}}> 0inf.

Lemma BigStep n:
  S0 n -->+ S0 (S n).
Proof.
  unfold S0.
  replace (0inf) with ([0;0]^^(2+n*2)*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow10 LInc.
  simpl_lpow_all0.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros.
  eexists.
  apply BigStep.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC0RA_1LE0LD_0LC1RA_1RA0LE_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma P0_n n:
  forall l r,
  l <* [1] {{A}}> [0;0]^^n *> r -->*
  l <* [1] <* <[1;0]^^n {{A}}> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (IHn l ([0;0]*>r)).
  er; sr.
  step1.
  follow' (IHn l ([0;1]*>r)).
  es.
Qed.

Lemma P1_n n:
  forall l r,
  l <* <[0;1]^^(n) <* [0;0;0] {{A}}> [0;0]^^(1+n) *> r -->*
  l <* [1;1]^^(n) <* <[1;0;0] {{A}}> [0;1]^^(1+n) *> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (IHn ([1;0]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  step1.
  follow' (P0_n (1+n) l ([1]*>[0;0]^^(2+n)*>[1]*>r)).
  do 2 step1.
  follow' (IHn ([1;1]*>l) ([0;1]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* [1;1] <* <[0;1]^^n <* [0;0;0] {{A}}> 0inf.

Lemma P2_n n m:
  forall l r,
  l <* [1] <* <[1;0]^^n {{A}}> [0;1] *> [0;0]^^m *> r -->*
  l <* [1] <* <[1;0]^^(m+n) {{A}}> [0;1] *> r.
Proof.
  gen n.
  induction m; intros.
  1: es.
  er; sr.
  step1.
  follow' (P0_n (1+n) l ([0;1]*>[0;0]^^m*>r)).
  follow (IHm (1+n)).
  es.
Qed.

Lemma BigStep n:
  S0 n -->+
  S0 (3+n+n).
Proof.
  unfold S0.
  replace (0inf) with ([0;0]^^(1+n)*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow P1_n.
  simpl_lpow_all0.
  do 3 (er; sr).
  step1.
  follow' (P0_n (1+n) (0inf) ([0;1]*>[0;0]^^(2+n)*>[1]*>0inf)).
  follow' (P2_n (1+n) (2+n) (0inf) ([1]*>0inf)).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 2).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros.
  eexists.
  apply BigStep.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RA_1LD0RB_0RC0LE_0LD0LF_1RD0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma P0_n n:
  forall l r,
  l <* [0;0] {{B}}> [0;0]^^n *> r -->*
  l <* [0;0] <* <[1;0]^^n {{B}}> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (IHn l ([0;0]*>r)).
  er; sr.
  do 4 step1.
  follow' (IHn l ([0;1]*>r)).
  es.
Qed.

Lemma P1_n n:
  forall l r,
  l <* <[0;1]^^(1+n) <* <[0;1;1] {{B}}> [0;0]^^(1+n) *> r -->*
  l <* <[1;0]^^(1+n) <* <[0;1;1] {{B}}> [0;1]^^(1+n) *> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (IHn ([1;0]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  do 6 step1.
  follow' (P0_n (1+n) ([1]*>l) ([1]*>[0;0]^^(2+n)*>[1]*>r)).
  do 2 step1.
  follow' (IHn ([0;1]*>l) ([0;1]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* [0;0] <* <[0;1]^^(1+n) <* <[0;1;1] {{B}}> 0inf.

Lemma P2_n n m:
  forall l r,
  l <* [0;0] <* <[1;0]^^n {{B}}> [0;1] *> [0;0]^^m *> r -->*
  l <* [0;0] <* <[1;0]^^(m+n) {{B}}> [0;1] *> r.
Proof.
  gen n.
  induction m; intros.
  1: es.
  er; sr.
  do 4 step1.
  follow' (P0_n (1+n) l ([0;1]*>[0;0]^^m*>r)).
  follow' (IHm (1+n) l r).
  es.
Qed.

Lemma BigStep n:
  S0 n -->+
  S0 (3+n+n).
Proof.
  unfold S0.
  replace (0inf) with ([0;0]^^(1+n)*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow P1_n.
  simpl_lpow_all0.
  do 3 (er; sr).
  do 4 step1.
  unfold Sym.
  replace (0inf) with ([0;0]*>0inf) by solve_const0_eq.
  follow' (P0_n (1+n) (0inf) ([0;1]*>[0;0]^^(2+n)*>[1;0;0]*>0inf)).
  follow' (P2_n (1+n) (2+n) (0inf) ([1]*>0inf)).
  simpl_lpow_all0.
  follow' Hx.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 2).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros.
  eexists.
  apply BigStep.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RE_0LB1RD_0RC0RD_1LF1RA_1RA0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma P0_n n:
  forall l r,
  l <* [0;1;0]^^(1+n) <* [0] {{C}}> [0] *> [0;0;0]^^(n) *> r -->*
  l <* <[1;1;0]^^(n) <* <[0;1;0;0] {{C}}> [0] *> [1;1;0]^^(n) *> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (IHn ([0;1;0]*>l) ([0;0;0]*>r)).
  do 4 (er; sr).
  follow' (IHn ([0;1;1]*>l) ([1;1;0]*>r)).
  es.
Qed.

Lemma P1_n n:
  forall l r,
  l <* [0;0;0] <* [0;1;0]^^(1+n) <* [0] {{C}}> [0] *> [0;0;0]^^(1+n) *> r -->*
  l <* <[0;1;1]^^n <* <[1;1;0;0;0;0;1] <* [0;1;0]^^(1+n) <* [0] {{C}}> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (P0_n (S n) ([0;0;0]*>l) ([0;0;0]*>r)).
  do 4 (er; sr).
  follow' (IHn ([1;1;0]*>l) ([1;1;0]*>r)).
  es.
Qed.

Lemma P2_n n:
  forall l r,
  l <* <[0;0;0;0;1] <* [0;1;0]^^(1+n) <* [0] {{C}}> [0] *> [0;0;0]^^(1+n) *> r -->+
  l <* <[0;1;1]^^(1+n) <* <[0;0;0] <* [0;1;0]^^(2+n) <* [0] {{C}}> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (P0_n (S n) ([1;0;0;0;0]*>l) ([0;0;0]*>r)).
  do 4 (er; sr).
  follow' (progress_evstep _ _ _ (IHn ([1;1;0]*>l) ([1;1;0]*>r))).
  es.
Qed.

Definition S0 '(l,n) :=
  l <* [0;0;0] <* [0;1;0]^^(1+n) <* [0] {{C}}> 0inf.

Lemma BigStep l n:
  exists c',
  S0 (l,n) -->+
  S0 c'.
Proof.
  exists ([1;1]*>[0;1;1]^^(1+n)*>[1;1;0]^^n*>l,1+n).
  unfold S0.
  replace (0inf) with ([0]*>[0;0;0]^^(1+n)*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow P1_n.
  replace (0inf) with ([0]*>[0;0;0]^^(1+n)*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  cbn.
  follow10 P2_n.
  rewrite (lpow_all0 [0;0;0]).
  2: solve_const0_eq.
  repeat rewrite <-const_unfold.
  rewrite (lpow_all0 [0;0;0]).
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (0inf,O)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [l n].
  apply BigStep.
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC---_1LD1RF_0LC1RE_0RD0RE_1LA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma P0_n n:
  forall l r,
  l <* [0;1;0]^^(1+n) <* [0] {{D}}> [0] *> [0;0;0]^^(n) *> r -->*
  l <* <[1;1;0]^^(n) <* <[0;1;0;0] {{D}}> [0] *> [1;1;0]^^(n) *> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (IHn ([0;1;0]*>l) ([0;0;0]*>r)).
  do 4 (er; sr).
  follow' (IHn ([0;1;1]*>l) ([1;1;0]*>r)).
  es.
Qed.

Lemma P1_n n:
  forall l r,
  l <* [0;0;0] <* [0;1;0]^^(1+n) <* [0] {{D}}> [0] *> [0;0;0]^^(1+n) *> r -->*
  l <* <[0;1;1]^^n <* <[1;1;0;0;0;0;1] <* [0;1;0]^^(1+n) <* [0] {{D}}> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (P0_n (S n) ([0;0;0]*>l) ([0;0;0]*>r)).
  do 4 (er; sr).
  follow' (IHn ([1;1;0]*>l) ([1;1;0]*>r)).
  es.
Qed.

Lemma P2_n n:
  forall l r,
  l <* <[0;0;0;0;1] <* [0;1;0]^^(1+n) <* [0] {{D}}> [0] *> [0;0;0]^^(1+n) *> r -->+
  l <* <[0;1;1]^^(1+n) <* <[0;0;0] <* [0;1;0]^^(2+n) <* [0] {{D}}> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (P0_n (S n) ([1;0;0;0;0]*>l) ([0;0;0]*>r)).
  do 4 (er; sr).
  follow' (progress_evstep _ _ _ (IHn ([1;1;0]*>l) ([1;1;0]*>r))).
  es.
Qed.

Definition S0 '(l,n) :=
  l <* [0;0;0] <* [0;1;0]^^(1+n) <* [0] {{D}}> 0inf.

Lemma BigStep l n:
  exists c',
  S0 (l,n) -->+
  S0 c'.
Proof.
  exists ([1;1]*>[0;1;1]^^(1+n)*>[1;1;0]^^n*>l,1+n).
  unfold S0.
  replace (0inf) with ([0]*>[0;0;0]^^(1+n)*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow P1_n.
  replace (0inf) with ([0]*>[0;0;0]^^(1+n)*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  cbn.
  follow10 P2_n.
  simpl_lpow_all0.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 ([1;1;0;1;1;1;1]*>0inf,1%nat)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [l n].
  apply BigStep.
Qed.

End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC---_1LD0RF_0LD0LA_1LD0RA_0RC1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma P0_n n:
  forall l r,
  l <* <[0;1]^^(n) <* [0] <{{A}} [0;1;1;0] *> [0;0]^^(1+n) *> r -->*
  l <{{A}} [0;1] *> [1;1]^^(1+n) *> [0] *> [0;1]^^(1+n) *> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (IHn ([1;0]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  do 7 step1.
  follow' (IHn ([1;1]*>l) ([0;1]*>r)).
  es.
Qed.

Lemma P1_n n:
  forall l r,
  l <* <[0;1]^^(n) <* [0] <{{A}} [0;1] *> [0;0]^^(n) *> r -->*
  l <* [1;1]^^(1+n) <* [0;0]^^n <* [0] {{F}}> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (IHn ([1;0]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  do 2 step1.
  follow' (IHn ([1;1]*>l) ([0;1]*>r)).
  es.
Qed.

Definition S0 '(l,n) :=
  l <* [0;0;0] <* <[1;0]^^(1+n) {{A}}> 0inf.

Lemma BigStep l n:
  exists c',
  S0 (l,n) -->+
  S0 c'.
Proof.
  exists ([1;1;1]*>[0;1]^^(4+n)*>[1;1;1;1]*>[0;1]^^(4+n)*>[1]*>l,2+n).
  unfold S0.
  do 7 step1.
  unfold Sym.
  pose proof (P0_n n ([1;0;0;0]*>l) (0inf)) as Hx'.
  cbn in Hx'.
  simpl_lpow_all0.
  follow' Hx'. clear Hx'.
  do 3 (er; sr).
  do 7 step1.
  follow' (P0_n n ([1;1;0;0]*>l) ([0;1]*>0inf)).
  do 3 (er; sr).
  do 4 step1.
  follow' (P1_n (2+n) ([1;1;0]*>l) ([1]*>0inf)).
  do 4 (er; sr).
  do 7 step1.
  pose proof (P0_n (2+n) ([1;1]*>[0;1]^^(5+n)*>[1]*>l) (0inf)) as Hx'.
  cbn in Hx'.
  simpl_lpow_all0.
  follow' Hx'. clear Hx'.
  do 3 (er; sr).
  do 4 step1.
  follow' (P1_n (3+n) ([1;0;1;1;1]*>[0;1]^^(4+n)*>[1]*>l) ([1]*>0inf)).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 ([1]^^3*>[0;1]^^3*>[1]^^4*>[0;1]^^3*>[1]*>0inf,1%nat)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [l n].
  apply BigStep.
Qed.

End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD0LC_1RF0RA_1RA---_0RD0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l <* <[1;0]^^n <* [0] {{A}}> [0;0]^^n *> r -->*
  l <* [1;1]^^n <* [0] <* [1;1]^^n {{A}}> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([0;1]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  step1.
  follow' (IHn ([1;1]*>l) ([1;0]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* [1] <* <[1;0]^^n <* [0] {{A}}> 0inf.

Lemma BigStep n:
  S0 (1+n) -->+ S0 (1+(1+n)*2).
Proof.
  unfold S0.
  replace (0inf) with (([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow (P0_n (1+n)).
  simpl_lpow_all0.
  do 4 (er; sr).
  rewrite lpow_add'.
  replace (n+n) with (n*2) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1+4)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S0 (1+x)).
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM19.


Module TM20.

Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LB_1RE1RD_1LE0RA_0RC0LF_1RA0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l <* <[0;1]^^n <* <[0;1] {{D}}> [0;0]^^n *> r -->*
  l <* [1;1]^^n <* <[0;1] <* [1;1]^^n {{D}}> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([1;0]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  step1.
  follow' (IHn ([1;1]*>l) ([1;0]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* [1;1] <* <[0;1]^^n <* <[0;1] {{D}}> 0inf.

Lemma BigStep n:
  S0 (1+n) -->+ S0 (1+(1+n)*2).
Proof.
  unfold S0.
  replace (0inf) with (([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow (P0_n (1+n)).
  simpl_lpow_all0.
  do 4 (er; sr).
  rewrite lpow_add'.
  replace (n+n) with (n*2) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1+4)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S0 (1+x)).
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM20.


Module TM21.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0LE_1RE0RD_1LA1RF_0RC0LB_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l <* <[1;0]^^n <* [0] {{D}}> [0;0]^^n *> r -->*
  l <* [1;1]^^n <* [0] <* [1;1]^^n {{D}}> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([0;1]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  step1.
  follow' (IHn ([1;1]*>l) ([1;0]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^n <* [0] {{D}}> 0inf.

Lemma BigStep n:
  S0 (1+n) -->+ S0 (1+(3+n*2)).
Proof.
  unfold S0.
  replace (0inf) with (([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow (P0_n (1+n)).
  simpl_lpow_all0.
  do 3 (er; sr).
  step1.
  follow (P0_n (1+n)).
  do 4 (er; sr).
  rewrite lpow_add'.
  replace (n+n) with (n*2) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1+3)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S0 (1+x)).
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM21.


Module TM22.

Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LB_1RF1RD_1LE0RA_1RA0LE_0RC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l <* <[0;1]^^n <* <[0;1] {{D}}> [0;0]^^n *> r -->*
  l <* [1;1]^^n <* <[0;1] <* [1;1]^^n {{D}}> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([1;0]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  step1.
  follow' (IHn ([1;1]*>l) ([1;0]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* [1;1] <* <[0;1]^^n <* <[0;1] {{D}}> 0inf.

Lemma BigStep n:
  S0 (1+n) -->+ S0 (1+(1+n)*2).
Proof.
  unfold S0.
  replace (0inf) with (([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow (P0_n (1+n)).
  simpl_lpow_all0.
  do 4 (er; sr).
  rewrite lpow_add'.
  replace (n+n) with (n*2) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1+3)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S0 (1+x)).
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM22.


Module TM23.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC0LB_1RE0RD_0RC---_1LA0RC_0LA1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma P0_n n:
  forall l r,
  l <* [1] {{C}}> [0;0]^^n *> r -->*
  l <* [1] <* <[1;0]^^n {{C}}> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (IHn l ([0;0]*>r)).
  er; sr.
  step1.
  follow' (IHn l ([0;1]*>r)).
  es.
Qed.

Lemma P1_n n:
  forall l r,
  l <* <[0;1]^^(n) <* [0;0;0] {{C}}> [0;0]^^(1+n) *> r -->*
  l <* [1;1]^^(n) <* <[1;0;0] {{C}}> [0;1]^^(1+n) *> r.
Proof.
  induction n.
  1: es.
  intros.
  follow' (IHn ([1;0]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  step1.
  follow' (P0_n (1+n) l ([1]*>[0;0]^^(2+n)*>[1]*>r)).
  do 2 step1.
  follow' (IHn ([1;1]*>l) ([0;1]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* [1;1] <* <[0;1]^^n <* [0;0;0] {{C}}> 0inf.

Lemma P2_n n m:
  forall l r,
  l <* [1] <* <[1;0]^^n {{C}}> [0;1] *> [0;0]^^m *> r -->*
  l <* [1] <* <[1;0]^^(m+n) {{C}}> [0;1] *> r.
Proof.
  gen n.
  induction m; intros.
  1: es.
  er; sr.
  step1.
  follow' (P0_n (1+n) l ([0;1]*>[0;0]^^m*>r)).
  follow (IHm (1+n)).
  es.
Qed.

Lemma BigStep n:
  S0 n -->+
  S0 (3+n+n).
Proof.
  unfold S0.
  replace (0inf) with ([0;0]^^(1+n)*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow P1_n.
  simpl_lpow_all0.
  do 3 (er; sr).
  step1.
  follow' (P0_n (1+n) (0inf) ([0;1]*>[0;0]^^(2+n)*>[1]*>0inf)).
  follow' (P2_n (1+n) (2+n) (0inf) ([1]*>0inf)).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros.
  eexists.
  apply BigStep.
Qed.

End TM23.


Module TM24.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1RD0LC_1RE1RE_0RD0RA_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 n :=
  forall l r,
  l <* <[1;0]^^n <* <[1;0] {{A}}> [0;0]^^n *> r -->*
  l <* [1;1]^^n <* <[1;0] <* [1;1]^^n {{A}}> r.

Lemma P0_n n:
  P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros l r.
  follow' (IHn ([0;1]*>l) ([0;0]*>r)).
  do 3 (er; sr).
  step1.
  follow' (IHn ([1;1]*>l) ([1;0]*>r)).
  es.
Qed.

Definition S0 n :=
  0inf <* [1] <* <[1;0]^^n <* <[1;0] {{A}}> 0inf.

Lemma BigStep n:
  S0 (1+n) -->+ S0 (1+(1+n)*2).
Proof.
  unfold S0.
  replace (0inf) with (([0;0]^^(1+n))*>0inf).
  2: rewrite lpow_all0; solve_const0_eq.
  follow (P0_n (1+n)).
  simpl_lpow_all0.
  do 4 (er; sr).
  rewrite lpow_add'.
  replace (n+n) with (n*2) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1+6)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple with (C:=fun x => S0 (1+x)).
  intros i.
  eexists.
  apply BigStep.
Qed.

End TM24.


Module TM25.

From BusyCoq Require Import Longitudinal ES_v2.
Require Import ZifyNat.

Ltac es_v2 := ES_v2.es.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RC_1LD0LC_1RA0LA_0RF---_0RE1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,<[1;1]).
Notation hL := (A,[0;1]).
Notation hRL := [(hR,hL)].

Lemma pow4_mod3 n:
  4^n mod 3 = 1%nat.
Proof.
  induction n; cbn[Nat.pow]; lia.
Qed.

Lemma RIncs k r:
  sideRLs tm (hRL^^((4^k*8-2)/3)) ([0;1;1;1]^^k*>[0;1;1;0]*>r) ([0;1;0;1]^^k*>[0;1;0;0]*>r).
Proof.
  induction k.
  1: esx.
  cbn[Nat.pow lpow].
  do 2 rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply IHk.
  pose proof (pow4_mod3 k).
  applys_eq (segRLs_addmul_v2 4 1 ((4^k*8-2)/3) 2 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Notation hL' := (C,[]).
Notation hR' := (E,[]).
Notation hLR' := [(hL',hR')].
Notation hRL' := [(hR',hL')].

Lemma RIncs' k r:
  sideRLs tm (hRL'^^((4^k*8-2)/3)) ([0;1;1]*>[0;1;1;1]^^k*>[0;1;1;0]*>r) ([0;1;1]*>[0;1;0;1]^^k*>[0;1;0;0]*>r).
Proof.
  eapply segRLs_sideRLs_concat.
  2: apply RIncs.
  apply segRLs_wall''.
  esx.
Qed.

Definition tm' := flip tm.

Lemma LIncs k:
  sideRLs tm' (hLR'^^((4^k-1)/3)) (0inf<*<[0;0;0;0]^^k) (0inf<*<[0;0;1;1]^^k).
Proof.
  induction k.
  1: esx.
  cbn[Nat.pow lpow].
  do 2 rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply IHk.
  pose proof (pow4_mod3 k).
  applys_eq (segRLs_addmul_v2 4 1 ((4^k-1)/3) 1 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Lemma LIncs' k:
  sideRLs tm' (hLR'^^((4^k*8-2)/3)) (0inf<*<[0;0;0;0]^^(S k)<*<[0;0]) (0inf<*<[0;0;1;1]^^(S k)<*<[0;0]).
Proof.
  eapply segRLs_sideRLs_concat.
  2: apply LIncs.
  cbn[Nat.pow].
  pose proof (pow4_mod3 k).
  applys_eq (segRLs_addmul_v2 2 1 ((4*4^k-1)/3) 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Definition S' '(k,r) := 0inf {{{ (hL',L) }}} [0;1;1]*>[0;1;1;1]^^k*>[0;1;1;0]*>r.

Lemma BigStep k r:
  exists r',
  S' (k,r) -->+ S' (S k,r').
Proof.
  eexists ([0;1;1;0]^^k*>1>>r).
  unfold S'.
  epose proof (sideRLs_concat_1L (RIncs' k r) (LIncs' k)) as I1.
  rewrite lpow_all0 in I1 by solve_const0_eq.
  replace ([0;0]*>0inf) with 0inf in I1 by solve_const0_eq.
  follow I1. clear I1.
  do 2 (er; sr).
  es_v2.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (1%nat,1>>0inf)).
  1: esx.
  eapply progress_nonhalt_simple; intros [k r].
  epose proof (BigStep k r) as [r' I1].
  eexists (_,_); apply I1.
Qed.

End TM25.


