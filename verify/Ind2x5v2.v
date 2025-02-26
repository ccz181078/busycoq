From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Inductive.

Module Inductive25 := Inductive BB25.
Import Inductive25.

Lemma progress_rw tm c1 c2:
  progress tm c1 c2 <->
  Compute.TM.progress tm c1 c2.
Proof.
  split; intro H.
  - induction H.
    + constructor.
      destruct H; auto.
    + eapply Compute.TM.progress_step; eauto.
      destruct H; auto.
  - induction H.
    + constructor.
      destruct H; auto.
    + eapply progress_step; eauto.
      destruct H; auto.
Qed.

Ltac solve_rule :=
  unfold Config_WF; cbn;
  repeat rewrite List.Forall_cons_iff;
  repeat rewrite List.Forall_nil_iff;
  cbn;
  repeat split;
  intros;
  unfold s0;
  rewrite progress_rw;
  try (es; fail).

Ltac solve_hlin_nonhalt_T cfg T :=
  apply (decide_hlin_nonhalt_spec cfg T);
  [ solve_rule
  | native_cast_no_check (eq_refl true)].

Ltac solve_hlin_nonhalt cfg :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    (solve_hlin_nonhalt_T cfg 1000000%N)
  end.


Lemma tm1: ~halts (TM_from_str "1RB3RA---4LB3RA_0LB2RB3LA4LA0RA") c0.
Proof.
  solve_hlin_nonhalt (config_exploop default_config).
Time Qed.

Lemma tm2: ~halts (TM_from_str "1LB3RB---3LA0RA_2RA3RB4LB1LB2LA") c0.
Proof.
  solve_hlin_nonhalt (config_BEC 400%N 1 B A [] [] [2]).
Time Qed.

