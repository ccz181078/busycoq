From BusyCoq Require Import Inductive25.

Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.

Ltac solve_halt' bsz maxT :=
  apply (decide_ubrrba_halt_spec (config_ubrrba bsz) maxT maxT);
  [ apply Config_WF_simple; reflexivity
  | native_check_eq ].

Ltac solve_halt bsz :=
  match goal with
  | |- halts_at_trans (TM_from_str ?x) c0 _ =>
    idtac x;
    solve_halt' bsz 50000%N
  end.


Lemma tm1: halts_at_trans (TM_from_str "1LB1RA0LB4RB2RA_2RA3LA4LB---0LB") c0 (B,3).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1LB2RB4LA0RB---_1RA2LB3LA0RA1RB") c0 (A,4).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB3LA4LA2RB1LA_2LA3RA---1RA4RB") c0 (B,2).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA2LA---0RA1LA") c0 (B,2).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB3LA0LB1LB---_2LA2RA4LA0RB3RA") c0 (A,4).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB3LA4RB3LB0LA_2LA---4RA2RA0LB") c0 (B,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB0LB4LB4RA---_2LA3LA3RB0RB2LB") c0 (A,4).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB3LA1RB2RA1LA_2LA4RA4LA0LB---") c0 (B,4).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1LB3LB---2LB2RB_2RA3RA3RB4LB0LB") c0 (A,2).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA2RB---0RA1LA") c0 (B,2).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB3LA3RB4LA1LB_2LA---0RA2RA0LA") c0 (B,1).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1LB2LB3LB---2RB_2RA3RA3RB4LB0LB") c0 (A,3).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1LB2RB2LA4RB1LA_1RA3LA3RA4RA---") c0 (B,4).
Proof. solve_halt 5%nat. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB0LB---4RA0LA_2LA3LA3LB0RA2LA") c0 (A,2).
Proof. solve_halt 6%nat. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1LB3LA3RA1RA---_2RA4RB3LB0LB3LB") c0 (A,4).
Proof. solve_halt 5%nat. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB3LA3LB0LA4LA_2LA---2RA4RB3RA") c0 (B,1).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB3RA1LA2RB3LA_2LA4LA---1RB2RA") c0 (B,2).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB0LB4LA0RA---_2LA0LB3RB2RB0RA") c0 (A,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1LB2LA3RA---0LB_2RA1RB4LA0RB1LB") c0 (A,3).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB3LA1LA2LA1RA_2LB3RA2RB4RB---") c0 (B,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB3LA1RB0RA1LA_2LA4RA4LA0LB---") c0 (B,4).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB3RA4LA2LA3RB_2LA3LA0RA---1LA") c0 (B,3).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB3RB1LB2LB0RA_2LA2RB4RB---0LB") c0 (B,3).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1LB2LA1RA---4RB_2RA3RB4RA1LB0LB") c0 (A,3).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB2LA3LA4LA---_1LB2RA0RB0LB2RB") c0 (A,4).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB3LA4RB4LB0LA_2LA---4RA2RA1LB") c0 (B,1).
Proof. solve_halt 5%nat. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB2LA4LB1RA0RB_1LA2RA3LB---0RA") c0 (B,3).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB3LA3RA0LA---_2LB1LA4RB2RA1RA") c0 (A,4).
Proof. solve_halt 8%nat. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1LB0RB---1RA3RB_2RA3LB1LB4LA0LA") c0 (A,2).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB3LA4RB2LB0LA_2LA---4RA2RA0LB") c0 (B,1).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB3LA1RA4LA0LA_2LA---1LA2RB3RA") c0 (B,1).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB3LA---4LA0LA_2LB3LA3RA4RB1RB") c0 (A,2).
Proof. solve_halt 6%nat. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB3LA1LB0RA1LA_2LA4RA2RA0LB---") c0 (B,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB3LB2RA2LA0RA_2LA4RB1LB0LA---") c0 (B,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1LB3RB---2LA1RB_2RA3RA4LB0LB2LA") c0 (A,2).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB3LA0RA0RA1LA_2LA4RA4LA0LB---") c0 (B,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1LB0RB3LB---2LB_2RA4LB3RB1LB3RA") c0 (A,3).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB3LA2RB0LA4LA_2LA---4LB3RA0RA") c0 (B,1).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB3LA4LB0LA---_2LA0LA2RB1RB3RA") c0 (A,4).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1LB2LB4RB0RB3LB_2RA3LA1RB1RA---") c0 (B,4).
Proof. solve_halt 12%nat. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1LB2LB4RB2RA3RA_2RA---3LB2LB4LB") c0 (B,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA1RA---0RA1LA") c0 (B,2).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1RB3LA1RA1LA1RA_2LA0LA4LA2RB---") c0 (B,4).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1RB3LA4RB0LB0LA_2LA---4RA2RA3RA") c0 (B,1).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm45: halts_at_trans (TM_from_str "1RB3RA3RB4LA2LA_2LA3LA1LA---0RA") c0 (B,3).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm46: halts_at_trans (TM_from_str "1RB3RB4LA1LA2RA_2LB3LA---2RA1RB") c0 (B,2).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm47: halts_at_trans (TM_from_str "1RB3LA4RB1LB0LA_2LA---4RA2RA1LB") c0 (B,1).
Proof. solve_halt 5%nat. Time Qed.

Lemma tm48: halts_at_trans (TM_from_str "1RB2RB---1LB4LB_2LA3LB3RB4RB0RB") c0 (A,2).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm49: halts_at_trans (TM_from_str "1RB3LA4RB4LB0LA_2LA---0RA4RA1RA") c0 (B,1).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm50: halts_at_trans (TM_from_str "1RB3RB---1LA0LB_2LA4LA3LB0RB4RA") c0 (A,2).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm51: halts_at_trans (TM_from_str "1RB3LA4RB4LB0LA_2LA---4RA2RA0LB") c0 (B,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm52: halts_at_trans (TM_from_str "1RB3LA1RA1LA1RA_2LA0LA4LA4RB---") c0 (B,4).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm53: halts_at_trans (TM_from_str "1RB3LA4RA0LA1RA_2LA4LA1LA4RB---") c0 (B,4).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm54: halts_at_trans (TM_from_str "1RB2RB4LB2LB---_2LA0LA3RB0LA2RA") c0 (A,4).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm55: halts_at_trans (TM_from_str "1RB3LA4RB0LB0LA_2LA---4RA2RA3RB") c0 (B,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm56: halts_at_trans (TM_from_str "1RB2LB4RB2RB---_1LA3RA4RA3LB1LB") c0 (A,4).
Proof. solve_halt 5%nat. Time Qed.

Lemma tm57: halts_at_trans (TM_from_str "1LB2RA0LA1RB---_0RA4RA3LB2LA0LB") c0 (A,4).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm58: halts_at_trans (TM_from_str "1RB0LB---3LB2LB_2LA4RB3RB0RB0RA") c0 (A,2).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm59: halts_at_trans (TM_from_str "1RB3LA4RA0LA1RA_2LA---4LA4RB1LA") c0 (B,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm60: halts_at_trans (TM_from_str "1RB0LB0RA4LA---_2LA3RA2LB1RB0RB") c0 (A,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm61: halts_at_trans (TM_from_str "1RB3RA4LA2LA3RB_1LB2LA0RA---1LA") c0 (B,3).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm62: halts_at_trans (TM_from_str "1RB3LA---1LA4LA_2LA4RA1LA1RB3RB") c0 (A,2).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm63: halts_at_trans (TM_from_str "1RB2RB1RA1LB---_2LA4RB3LB4RA2LB") c0 (A,4).
Proof. solve_halt 5%nat. Time Qed.

Lemma tm64: halts_at_trans (TM_from_str "1RB3LA1RA1LA2RB_2LA0LA4LA2RB---") c0 (B,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm65: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA4RA---0RA1LA") c0 (B,2).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm66: halts_at_trans (TM_from_str "1LB1RB2RA0RB0LB_1RA2LB3LB4LB---") c0 (B,4).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm67: halts_at_trans (TM_from_str "1LB3LA3LB0RB1LB_2RA---0LA4RB0LB") c0 (B,1).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm68: halts_at_trans (TM_from_str "1RB3LA0RA1LA0LB_2LA4RB0RA0LB---") c0 (B,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm69: halts_at_trans (TM_from_str "1RB3LA1RB0RA1LA_2LA4RA4LA2LB---") c0 (B,4).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm70: halts_at_trans (TM_from_str "1RB3LA4RA4RB1LA_1LB2RA---1RA2LA") c0 (B,2).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm71: halts_at_trans (TM_from_str "1RB3LA1RB2RA1LA_2LA4RA4LA2LB---") c0 (B,4).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm72: halts_at_trans (TM_from_str "1RB3LA1LA0RB---_2LA4LA4LA1RA2RA") c0 (A,4).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm73: halts_at_trans (TM_from_str "1RB3LA1RA4LA2RA_2LA---1LA2RB0LA") c0 (B,1).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm74: halts_at_trans (TM_from_str "1RB0LB2LB4RA---_2LA3LA3RB0RB3LB") c0 (A,4).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm75: halts_at_trans (TM_from_str "1RB2RB3LA4LA2RA_2LB3RA---1RA1LA") c0 (B,2).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm76: halts_at_trans (TM_from_str "1LB2LA1RB0LA1RA_2RA4LB3RB1RA---") c0 (B,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm77: halts_at_trans (TM_from_str "1LB2LA3RA---0LB_2RA1RB4LA0RB1RB") c0 (A,3).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm78: halts_at_trans (TM_from_str "1LB3LB0RA2LA---_2RB1RA0LB4RA1LB") c0 (A,4).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm79: halts_at_trans (TM_from_str "1RB3LA4LB0RA1LA_2LA4RA4RA0LB---") c0 (B,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm80: halts_at_trans (TM_from_str "1RB3LA1RA4LA2RB_2LA---1LA2RA0LA") c0 (B,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm81: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA3LA---0RA1LA") c0 (B,2).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm82: halts_at_trans (TM_from_str "1RB3RA4LB0LA1LB_2LA4RA---1LA0RB") c0 (B,2).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm83: halts_at_trans (TM_from_str "1LB3LB1RB0LA0LA_2RA2LB4LB---0RB") c0 (B,3).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm84: halts_at_trans (TM_from_str "1RB1RA3LB2LA0LA_2LA0LB0RA4RB---") c0 (B,4).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm85: halts_at_trans (TM_from_str "1RB3LA---4RB0LB_2LA3LB4LA1RB3RA") c0 (A,2).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm86: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA4RB---0RA1LA") c0 (B,2).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm87: halts_at_trans (TM_from_str "1RB3RA3RB4LA0LA_2LA3LA1LA---1RA") c0 (B,3).
Proof. solve_halt 5%nat. Time Qed.

Lemma tm88: halts_at_trans (TM_from_str "1RB3RA3LA4LA2RB_2LA1RA---1LA1RA") c0 (B,2).
Proof. solve_halt 4%nat. Time Qed.

Lemma tm89: halts_at_trans (TM_from_str "1RB3LB3LA2RA3RA_2LA4RB1LB4LA---") c0 (B,4).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm90: halts_at_trans (TM_from_str "1RB3RA4RB0LA4LB_2LA---3LA2RB0RA") c0 (B,1).
Proof. solve_halt 2%nat. Time Qed.

Lemma tm91: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA0LA---4RA1LA") c0 (B,2).
Proof. solve_halt 3%nat. Time Qed.

Lemma tm92: halts_at_trans (TM_from_str "1RB3LB2RA2RA0RA_2LA4RB1LB0LA---") c0 (B,4).
Proof. solve_halt 3%nat. Time Qed.

