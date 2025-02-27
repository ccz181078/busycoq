From BusyCoq Require Import Inductive33.

Ltac solve_hlin_nonhalt_T T :=
  apply (decide_hlin_nonhalt_spec (config_exploop default_config) T);
  [ apply Config_WF_simple; reflexivity
  | native_cast_no_check (eq_refl true)].

Ltac solve_hlin_nonhalt :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    solve_hlin_nonhalt_T 1000000%N
  end.

Lemma tm1: ~halts (TM_from_str "1RB2LC---_0LA0RC1LC_1RB2RC1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB2RA1LB_0LC0RA1LA_---2RB2LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB2RA1LB_0LC0RA1LA_2LA0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB2RA1LB_0LC0RA1LA_---2LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB2RB---_1LC2LB1RC_0RA0LB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB2LB---_1RC2RB1LC_0LA0RB1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB---0LC_2LC2RC1LB_0RA2RB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB---1RB_2LC2RC1LB_0RA2RB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

