From BusyCoq Require Import Inductive33.

Ltac solve_hlin_nonhalt_T T :=
  apply (decide_hlin_nonhalt_spec default_config T);
  [ apply Config_WF_simple; reflexivity
  | native_cast_no_check (eq_refl true)].

Ltac solve_hlin_nonhalt :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    solve_hlin_nonhalt_T 1000000%N
  end.


Lemma tm1: ~halts (TM_from_str "1RB0LC0RB_1LA2LC1RB_2RA2LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB0LC0RB_1LA2LB1RB_2RA2LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB0RC---_2LA0LA1RA_2LB1RC1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB2RA1LA_2LA0RC---_2LC2RC0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB2RA1LA_2LA0RC0LA_2LB2RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB1LA0LC_2LA1RC---_1LA2RB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB---2RC_1LB2LC0LB_1RA2LB2RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB0RB---_0LC2RC1LC_2RA2LB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB---0LB_0RC2RC1LC_2LA2LB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB0LB0RC_1LC0RA---_1LA2LC1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB1LB---_1LC2RA0RB_1LA0LC0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB---0LC_1LC2RB0RB_1LA2LB2LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB2LA2RA_1LC1LB0RA_2RA0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB---0RC_1LC2LB1RA_2RC0LB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB2RA1RB_1LC0RC0LA_1RA0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB2LC0LA_1LC1RB0RA_2RB1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB---1LA_1RC0RC0LA_2LB2RC1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB0LC---_1RC2RB1RC_1LA0RA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB2RB---_2LC0RC0RC_2RA1LC0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB2RB---_2LC2LB0RC_2RA1LC0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB---2LB_2LC0RA2RC_1LA2LA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB---2RB_2LC2LB0RB_0LA1RA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB1LB0LC_2RC0LA1RC_2LA1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB2LC0RA_2RC2LB0LB_1LA---2RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

