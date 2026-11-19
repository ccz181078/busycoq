From BusyCoq Require Import Inductive25.

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

Lemma tm1: ~halts (TM_from_str "1RB0RB0LB4RB---_2LA1RA3LB2RB2LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB4RA3LA0RB3LA_2LB3LA1LB2RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB4LA1RA1LB1RA_2LB3LA---4RA4RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB3RA1LB1LA1LB_2LA4RB---4LA3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB4LA4RA1LB1RA_2LB3LA---1RA4RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB2RA3LA1RB---_2LB3LA4LA2RB1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB3RB0LA0LB2RA_2LA4RA3RB2LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB3LA0LB4RB---_2LA1RA3LB2RB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB0RB0LB4RB---_2LA1RA3LB2RB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB3LA1LB1RA1RB_1LB2LA1RA4RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB3LA0LB4RB---_2LA1RA3LB2RB2LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB2LA3LA4RA1RA_1LA0LB3RB0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB3LA4LA1RA1LB_0LB2LA1RA3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB4RB1LA2RB3RA_1LB2LA3RB0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB2RA1LA2RA2LB_2LB3RB4LA---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB2LA1LB4LB---_2LA2RB3LB4RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB3LA2LB1RA2LA_2LA4LA0LA3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB2RA3LA4RB1RB_2LB3LA1LB2RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB3RB2LA3LB3RB_2LA---4LA2RA1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB3LB2LA1RB---_2LA4RB3LB2RB2RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB3LB0RA0RB3RA_2LA4RA4LB3LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB3LA4RB0LB---_2LA1RA3RB2LB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB2RB0LB0LA2RA_2LA4RA3LB2RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB0LB1RB4RB---_2LA3LB3RA1RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB3LA2LB1RA0RA_2LA4LA0LA3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB2LA1RA1LB1RA_2LB3LA4RB4RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB3LB---3LA1RB_2LA2RA3RB4LB3RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB2LA1RA1LB1RA_2LB3LA4RB2RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB3LA4LA1RA2RA_2LB1LA---0RA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB3RA0RB2LA---_2LB1LA3RB4LA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB3LB4LA2LB---_2LA2LB4RB0RA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB3LA0LB1RB---_2LA4RB3LB2RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB2RA3LA4LA1RA_2LB2RA---0RA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB4RA0RB2LA3RB_2LB2LA3RB1LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB3LA2LB1RA3RB_1LB2LA1RB4RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB2LA1RA4LA3LB_1LA3LA2RB---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB4RB3RB1LA2RA_2LB3RB1LB2LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB3LA1LB1RA3RA_0LB2LA3RA4RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB3RA4LB1LA1LB_2LA4RB---4LA3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB3RA2LA4RB4LB_2LA---3LA3RB2RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB3LA4LB1RA3LA_2LA2LA4RA3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB3LA4LA1RA4LB_2LA0RA---0RA3RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB4RA---1LA3RB_2LB3RB1LA4LA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB3LB2LA4RB---_2LA2RA3LB2RB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB4LA0LB1LB1RA_2LB3LA---1RA4RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB4RB1RB2LA3RA_1LB2LA3RB0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB0RB0LB4LB---_2LA1RA3RB2LB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB2RA3RB1LA---_2LA3RB4LB0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB3RA4LA1LA1LB_2LA4RB---2LA3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB2RA1LA2RA2LB_2LB3RB4LA---3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB4RA1LA---2RB_2LB2RB3LA4LA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB3RB2LA1LB3LA_2LA2RA4RB1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB4RB1LA2RB3RA_1LB2RB3LA0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB2RA4RB4RA3LA_2LB3LA---1RA4LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB3LA1LB1RA2RB_2LB2LA3LA4RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB4RB0LB4RA3LA_2LB3LA---1RA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB4LA3RA1LB1RA_2LB3LA---4RA3RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB3RA4LA2RB0RA_2LA---1LA2RA3LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB3LA1LB1RA1RB_2LA2LA---4RA1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB3LA4LB1RA1LA_0LB2LA1LA0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB3RB2LA3LB3RB_2LA---4LA2RA4RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB2LA3RA4LA0LB_2LA1RA1RA4RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB3LA1LB1RA0RA_0LB2LA3LA4RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB0RB0LB4RB---_2LA1RA3LB2RB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB3RA4RB2LA1RB_1LB2LA3RB0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB3LA3LB1RA3RB_2LA2LA---4RA3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB3LA4LA1RA3LB_2LA2LA3RA3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB3LB---3LA1RA_2LA4LB1RB0LB2RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB3RA---4LA0RB_1LB2LA3RB0LA3RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB4RA0RB2LA2LA_1LB2LA3RB0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB3LA4LA1RA2LB_2LB2LA0LA3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB3RB---3LA1LB_2LA1RB1LA4LA4RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB3LA4LA1RA2LB_2LA2LA0LA3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB3LA4LA1RA4LB_2LA3RA---0RA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB4LA1RA1LB1RA_2LB3LA---2RA4RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB2LA3RA4LA1LB_2LA1RB1RA4RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB3RA1LA0LB2RB_2LA4LB1RA---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB3RA4LB1LA3RA_2LA2RB3RA2LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB3RA1LB4LA3RA_2LA---3RA2LA2RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB3RB---3LA1LB_2LA1RB3RB4LA4RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB3RA4LA1LA1LB_2LA1RB---2LA3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB2LA1RA1LB1RB_2LB3LA4RA2LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB3LA3LB1RA2LA_2LA4LA3RA3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB3LB1RB3LA---_2LA4RA3RB2LB3RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB3LB3LA2LB---_2LA2LB4RB0RA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB3LA0RB1RA0LB_2LA---4RB3RB2LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB3LA1LB4LA---_2LA1RB3RB2RB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm88: ~halts (TM_from_str "1RB3RA4LB4LA3RA_2LA---3RA2LA2RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm89: ~halts (TM_from_str "1RB3LA4LA1RA4LB_2LA3RA---0RA3RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm90: ~halts (TM_from_str "1RB3LA1LB1RA3RB_2LA1LB---4RA1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm91: ~halts (TM_from_str "1RB3RB---3LA1LB_2LA1RB3LB4LA4RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm92: ~halts (TM_from_str "1RB3LA4LA4RA1LB_2LA3RB---0RA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm93: ~halts (TM_from_str "1RB4LA3LA1LB1RA_2LB3LA---4RA3RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm94: ~halts (TM_from_str "1RB3LA3LB1RA2RB_0LB2LA1RA4RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm95: ~halts (TM_from_str "1RB3LA4RB0LB---_2LA1RA3RB2LB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm96: ~halts (TM_from_str "1RB3RB---2LA1LB_2LA1RB4LA4LA4RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm97: ~halts (TM_from_str "1RB3LA4LA1RA2LB_1LB2LA1RB3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm98: ~halts (TM_from_str "1RB3RA4LB1LA1LA_2LA1RB1RA2LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm99: ~halts (TM_from_str "1RB3LA4LB1RA3LA_0LB2LA3RA2RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm100: ~halts (TM_from_str "1RB0RB1RB4LB---_2LA1RA3RB2LB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm101: ~halts (TM_from_str "1RB2RB2LA1RB---_2LA4RA3LB2RB2RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm102: ~halts (TM_from_str "1RB3LA4LB1RA1LA_0LB2LA1RA0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm103: ~halts (TM_from_str "1RB2LA---4LA1LB_0LA1RB3RB4RA3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm104: ~halts (TM_from_str "1RB3LB1RB4LB---_2LA3RA3RB2LB3LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm105: ~halts (TM_from_str "1RB3LA2LA4RB4LB_2LA---3LA3RB2RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm106: ~halts (TM_from_str "1RB3RA1LB1LA2RB_2LA4RA3LA2LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm107: ~halts (TM_from_str "1RB2RA1LA4LA1LB_2LB1RB3LA---2RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm108: ~halts (TM_from_str "1RB3RA4LA1LA1LB_2LA4RB---4LA3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm109: ~halts (TM_from_str "1RB3LA1LB4RA3LA_2LA---1RA3RB2LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm110: ~halts (TM_from_str "1RB3LA4LA1RA4LB_2LA2LA---0RA3RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm111: ~halts (TM_from_str "1RB3LA3LB1RA2RB_1LB2LA1LA4RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm112: ~halts (TM_from_str "1RB3LA1LB4RA2LA_2LA1RB---1RA2RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm113: ~halts (TM_from_str "1RB3RA4LB1LA---_2LA0RA3RA0RB1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm114: ~halts (TM_from_str "1RB3LA4LB1RA3LA_2LA2LA1RA3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm115: ~halts (TM_from_str "1RB3RA3LB1LA3RB_2LA4RA1LA2LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm116: ~halts (TM_from_str "1RB3RA1LB1LA1RB_2LA4RA3RA2LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm117: ~halts (TM_from_str "1RB4LA1RB1LB1RA_2LB3LA---4RA3RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm118: ~halts (TM_from_str "1RB3LA4LA1RA2RA_2LB3LA---0RA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm119: ~halts (TM_from_str "1RB4LA3LA1LB1RA_2LB2LA1RA---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm120: ~halts (TM_from_str "1RB2LB4RA---2LA_2LA2RB3LB0RA4LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm121: ~halts (TM_from_str "1RB4LA1RA1LB1RA_2LB3LA---4RA2RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm122: ~halts (TM_from_str "1RB3RA1LB1LA2LA_2LA1RB---4LA1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm123: ~halts (TM_from_str "1RB2LA1RA2LB2RA_2LB3LA4RB4RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm124: ~halts (TM_from_str "1RB3RB---3LA1LB_2LA1RB4LA4LA4RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm125: ~halts (TM_from_str "1RB2RA3RB1LA---_2LB3RB4LA2LA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm126: ~halts (TM_from_str "1RB4LA1LB2LA1RA_2LB3LA---1RA4RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm127: ~halts (TM_from_str "1RB3LA4LB1RA3RB_2LA4LB---4RA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm128: ~halts (TM_from_str "1RB0LB1RB4RB---_2LA3LB3RA1RB2LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm129: ~halts (TM_from_str "1RB2RB3RA1LA---_2LB3RB4LA0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm130: ~halts (TM_from_str "1RB3RB1RB4LB---_2LA2RA3RB2LB2LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm131: ~halts (TM_from_str "1RB4LA1RA1LB1RA_2LB3LA---2RA2RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm132: ~halts (TM_from_str "1RB0RA3LB4RA3LA_2LA---4RA1RA4LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm133: ~halts (TM_from_str "1RB3LA4RB0LB---_2LA1RA3RB2LB3LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm134: ~halts (TM_from_str "1RB---1LB1LA2LA_2LB3RB4RB2RB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm135: ~halts (TM_from_str "1RB3RA1LA2RB---_2LB2RB3LA4LB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm136: ~halts (TM_from_str "1RB4RB3LB2LA3LA_2LB2LA1RA2RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm137: ~halts (TM_from_str "1RB3RA4RB1LA1LB_2LA4RB---4LA3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm138: ~halts (TM_from_str "1RB3LA4LB1RA1LA_2LB2LA3LA3RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm139: ~halts (TM_from_str "1RB3LA0LB4RB---_2LA1RA3LB2RB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm140: ~halts (TM_from_str "1RB3RA0RB2LA---_1LB2LA3RB4LA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm141: ~halts (TM_from_str "1RB2RB4LA2LB2RA_1LB2RA3LA---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm142: ~halts (TM_from_str "1RB3LA1RB0LB---_2LA4RB3RB2LB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm143: ~halts (TM_from_str "1RB3RA1LB2LB2RA_2LA---2LA4LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm144: ~halts (TM_from_str "1RB1RB---4RB0LB_2LA2RA3LB1RA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm145: ~halts (TM_from_str "1RB2LA1RA2LB2RB_2LB3LA4RA2RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm146: ~halts (TM_from_str "1RB3LA2LA1LA0LB_2LA2RA3RB4RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm147: ~halts (TM_from_str "1RB3RA3LB1LA1LB_2LA4RB---4LA3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm148: ~halts (TM_from_str "1RB3RA4LA2RB0RB_2LA4LA1LB---2RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm149: ~halts (TM_from_str "1RB2RA1LA4LB1LA_2LB1RB3LA1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm150: ~halts (TM_from_str "1RB2RB2LA4RB4LB_2LA---3LA3RB2RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm151: ~halts (TM_from_str "1RB2RB4LB1RB---_2LA2RA3LB2RB2LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm152: ~halts (TM_from_str "1RB3RB---4LB3LA_2LA4RB1LA1RA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm153: ~halts (TM_from_str "1RB4RB3LA1RB2RA_2LB3LA1LB2RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm154: ~halts (TM_from_str "1RB3LA3LB1RA3RB_2LA1LB---4RA3LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm155: ~halts (TM_from_str "1RB2RB4LA1LB2RA_2LA4RA3LA---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm156: ~halts (TM_from_str "1RB3RA0LB1LA1LB_2LA4RB---4LA3RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm157: ~halts (TM_from_str "1RB4RB1LA2LA2RA_2LB2RB3RB0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm158: ~halts (TM_from_str "1RB3RA1LB1LA1RA_2LA2RB4LA2LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm159: ~halts (TM_from_str "1RB4RB---1LA3RA_2LB3RB4LA0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm160: ~halts (TM_from_str "1RB4LA3LB1LA1RA_0LB2LA3LA---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm161: ~halts (TM_from_str "1RB0RB0LB1RB---_2LA4RB3LB2RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm162: ~halts (TM_from_str "1RB3LA1LB4RA3LA_2LA---4RA3RB2LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm163: ~halts (TM_from_str "1RB3RA3LB1LA0LA_2LA4RA1LA2LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm164: ~halts (TM_from_str "1RB3LA1RA4LA2RA_2LA---1LA4RB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm165: ~halts (TM_from_str "1RB2LA1RA4LB2LA_2LB3LA2RB2RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm166: ~halts (TM_from_str "1RB4LA4RA4LB1RA_2LB3LA---4RA2RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm167: ~halts (TM_from_str "1RB3RA4LA4LB2RA_2LA4LA2LB---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm168: ~halts (TM_from_str "1RB3LA1LB---2LA_2LA1RB4RA4RB2RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm169: ~halts (TM_from_str "1RB4LA0LA1LB1RA_2LB3LA---4RA3RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm170: ~halts (TM_from_str "1RB4RA---1RB3LA_2LB3LA1LA4RB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

