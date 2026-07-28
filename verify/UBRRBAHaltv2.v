From BusyCoq Require Import Inductive62.

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


Lemma tm1: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0LB_0RA0RF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1LB1RF_1RC0LA_0RD0LD_1RA0RE_1RB1LC_0LB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1LB0RC_0LC0LB_1RD0RE_0RA1RF_0LA---_1RA1RE") c0 (E,1).
Proof. solve_halt 12. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1LB1LE_1RC0LC_1LE0RD_1RB1RF_0LE0LA_0LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_1LA0LC_0RA1RF_1RA0LA_0RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB0RD_1RC1LB_1RD0LC_1LE0RF_---1LC_1RA1LC") c0 (E,0).
Proof. solve_halt 5. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB---_1LC1RF_1RE0LD_1LB0LC_0RA0RD_1RE1LC") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LE_1RC0RE_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1LB1LF_0RC0LA_1LA1RD_1RE0RC_1LB1LC_1LE---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB0RE_0RC0LC_1LD1RA_1LE0LD_1LF0RB_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RF1RE_0RC---_0RA0LA") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1LB1RF_1RC0LA_0RD0LD_1RA0RE_1RB0RE_0LB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1LB0LA_1RC0RE_1LA1RD_0RB1RF_1RB0LB_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB---_0RC1RF_1LD0RE_0LE0LD_1RB1LD_1RC0RA") c0 (A,1).
Proof. solve_halt 12. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB0LD_1RC1RB_1LD0RF_---1LE_0LA1RA_0RE0RB") c0 (D,0).
Proof. solve_halt 3. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1LB0LA_1LC0LA_1RD0RC_0RE1RE_1RA1RF_0RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA1RF_1RA0RE_0LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1LB0LD_1RC0LA_0LD0RB_1LA0RE_1RF---_0RD0LD") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB1RF_1RC0LC_1LD1RE_1LB0LD_0RA0RD_1LE---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB0LD_0RC1RC_1LA1RA_---0LE_0RF1LE_0RA0LC") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1LB1RE_1RC0LB_0LD0RD_1RA1LB_0RD0RF_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1LB1RD_0LC0LB_1LD1LB_1LE1LF_0RA1RE_---0RA") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LA_1RC0RE_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB---_1RC1RF_1LD1LE_1RA0LE_1LB0LD_0RD1RD") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1LB0LF_0RC1RB_1LD1RA_0LE0LD_1LA1LD_---0RA") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1LB1RF_1RC0RB_0RD1RB_1RE1RA_1LA0LE_---1LE") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB0LD_1LC1RE_0LD0LC_1RE1RB_0RA0RF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1LB0RF_0LC0RC_1RD1LE_1LE1RA_1RB0LE_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB---_1RC0LE_1LD1RF_0LE0LD_1RF1RC_0RB0RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1LB0RD_1LC1LE_1RA0LE_0RA0RC_0LF0LA_0LB---") c0 (F,1).
Proof. solve_halt 7. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB1RD_0RC0RF_1RD0LA_1LE1RB_0LA0LE_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1LB0LE_1RC0RA_0RE0RD_1RB1LD_1LF---_1LD0LF") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1LB1LF_1LC1LE_0RD1RC_1LF1RB_---0RD_0LA0LF") c0 (E,0).
Proof. solve_halt 3. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1LB1RF_1RC0LA_0RE0LD_1RB0RD_1RA0RD_0LB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB---_1LB1RC_0RF0RD_0RB1RE_1RA1LF_0LE0LF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1LA1LC_1RA1RF_0LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1RB0RE_1RC0LE_0RD0LD_1RE0RA_1LB1RF_0LB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0RA_0RA0RF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1LB0LC_1RC0LA_1LA0RD_1RC0RE_1RF---_0RA0LA") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB1RE_1LC0RF_0RA0LD_1LE---_0LC0LE_0RB0RD") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1RB0RE_1LC0LB_0LD1LA_1RE1RF_0RA1RD_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB0LD_0RC0LE_1RD0RE_1LA1RF_1RA0RE_0LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1LB0RE_0LC0LA_1RD0LC_1RA---_1LA1RF_0RC1RE") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1LB1LA_1RC0LF_1LB0RD_1RE0RA_1LF---_1LA0LB") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm45: halts_at_trans (TM_from_str "1RB---_1RC1LD_1LD1RF_1RE0LD_0LB0RB_1LE0RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm46: halts_at_trans (TM_from_str "1RB1RC_1LC1RC_1RE1LD_0LC0LD_0RF---_1RA0LC") c0 (E,1).
Proof. solve_halt 20. Time Qed.

Lemma tm47: halts_at_trans (TM_from_str "1RB0LA_0LC0LD_1RD1LA_1LA1RE_0RC0RF_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm48: halts_at_trans (TM_from_str "1RB1LC_0RC1RD_1LD0LE_1RA1RE_1RF0LC_0RB---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm49: halts_at_trans (TM_from_str "1RB0LB_1RC0RA_1LD1RE_1LB0LD_0RB1RF_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm50: halts_at_trans (TM_from_str "1RB0RE_0RC1RF_1LD0RA_0LA0LD_0LC---_1RC1RE") c0 (E,1).
Proof. solve_halt 12. Time Qed.

Lemma tm51: halts_at_trans (TM_from_str "1LB0RC_0LC0LB_1RD1LB_0RA1RE_1RA0RF_1RD---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm52: halts_at_trans (TM_from_str "1RB0LA_1RC0RF_1RD1LD_1LE0RD_1RF1LA_---1RA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm53: halts_at_trans (TM_from_str "1LB0RD_0LC---_1LD1RC_0LE1LD_1RF0LF_0RA1LA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm54: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LA_1RC0RB_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm55: halts_at_trans (TM_from_str "1RB0LA_0RC1RE_0RD1RC_1LD1LA_1RF1RB_0RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm56: halts_at_trans (TM_from_str "1LB1RA_0LC1LE_1LD0LC_0RA0LB_1RF1LD_---0RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm57: halts_at_trans (TM_from_str "1LB1RE_1RC0LB_0LD0RD_1RA1LB_1LC0RF_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm58: halts_at_trans (TM_from_str "1RB0LA_0RC1RE_0RD1RC_1LD1LA_1RF1RB_0LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm59: halts_at_trans (TM_from_str "1LB0RC_0LC0LB_1RD1LB_0RA1RE_1RA1RF_0LA---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm60: halts_at_trans (TM_from_str "1RB0RE_0RC1RA_1LD1RF_1LA0LD_0LB0LC_1RE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm61: halts_at_trans (TM_from_str "1LB0LA_1RC0RE_1LA1RD_1RE1RF_0RC0LC_0RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm62: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA1RF_1RA1LB_0LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm63: halts_at_trans (TM_from_str "1LB0LA_1RC0LC_0RE0RD_1LA0RB_0LD1RF_---0RB") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm64: halts_at_trans (TM_from_str "1LB0LE_1RC0RB_0RD1RB_1RE1RF_1LA0LE_1LB---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm65: halts_at_trans (TM_from_str "1RB0RE_1RC---_1LD1LC_1RE0LC_0RA1RF_1RE0RD") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm66: halts_at_trans (TM_from_str "1RB1RF_0RC1RA_1RD0RB_1RE0RA_0LA0LE_1LE---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm67: halts_at_trans (TM_from_str "1RB1RF_0RC1RA_1RD0RB_1LE0LD_0LA1LC_1LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm68: halts_at_trans (TM_from_str "1RB---_0RC0RB_1RD0LF_0RE1RA_1RF1LC_1LC0LF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm69: halts_at_trans (TM_from_str "1RB0RE_1LC0LB_0LD1LA_1RE0RF_0RA1RD_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm70: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RE1RF_0RB0LB_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm71: halts_at_trans (TM_from_str "1LB1RD_0LC0LB_1RD1RA_0RE0RF_1RA0LC_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm72: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA1RF_1RA0RD_0LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm73: halts_at_trans (TM_from_str "1RB0RD_1LC0LC_1RD0LC_1LE0RF_---1LC_1RA0RB") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm74: halts_at_trans (TM_from_str "1RB1RE_1RC1LD_0RD1RA_1LA0LE_1RF0LD_0RC---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm75: halts_at_trans (TM_from_str "1RB1RF_1LC0LB_1LD0LB_1RE0RD_0RA1RA_0RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm76: halts_at_trans (TM_from_str "1LB0LA_0LC1LE_1RD0RF_0RE1RC_1RA0RD_1RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm77: halts_at_trans (TM_from_str "1LB0RD_0LC---_1RD0RA_0RE0LE_1LF1RC_1LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm78: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0RA_1LD0RF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm79: halts_at_trans (TM_from_str "1LB1RD_0LC0LB_1LD1LB_1LE0LF_0RA1RE_---0RD") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm80: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD1RB_1RE0RC_1LF0LE_0LB1LD") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm81: halts_at_trans (TM_from_str "1RB0RF_1RC1LB_1RD0LC_1LE0RE_1RA1LC_---0RE") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm82: halts_at_trans (TM_from_str "1RB0RF_0RC1RA_1RD0RB_1LE0LD_0LA1LC_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm83: halts_at_trans (TM_from_str "1LB1RE_0RC0LB_0LA1RD_1RC---_0RF0RB_1RA0LD") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm84: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LA_1RC1LD_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm85: halts_at_trans (TM_from_str "1LB1LA_1RC0LA_0RE1RD_1RC0RB_1RF0RC_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm86: halts_at_trans (TM_from_str "1LB0LE_1RC0RB_0RD1RB_1RE0RF_1LA0LE_0RB---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm87: halts_at_trans (TM_from_str "1RB---_1RC1LE_1LD0RF_1RC1LB_1LF0LD_0RD0LA") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm88: halts_at_trans (TM_from_str "1RB---_1RC1LD_1LD1RF_1RE0LD_0LB0RB_0RB0RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm89: halts_at_trans (TM_from_str "1LB0LA_1RC0LA_0RF1RD_1RE---_0RB0RE_1RA1LB") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm90: halts_at_trans (TM_from_str "1LB0LE_1RC0RB_0RD1RD_1RE1RF_1LA0LE_0RB---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm91: halts_at_trans (TM_from_str "1RB---_1RC1LD_1LD1RF_1RE0LD_0LB0LC_0RB0RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm92: halts_at_trans (TM_from_str "1RB---_1RC0RB_1RD0LC_1LE0RF_1LC0LE_0RB0RA") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm93: halts_at_trans (TM_from_str "1RB0LD_0RC1RE_1RD1LA_1LA0LD_1RF---_0RA0RF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm94: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1LD1RA_1LE0LD_1RC0RB_0RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm95: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1LE0RD_1RA1RC_1LA1LF_0LC---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm96: halts_at_trans (TM_from_str "1LB1LF_1RC0LC_1LE0RD_1RB1RF_0LE0LA_0LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm97: halts_at_trans (TM_from_str "1RB---_1RC1LD_1LB0RF_1RC1LE_1LF0LB_0RB0LA") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm98: halts_at_trans (TM_from_str "1RB1LA_1RC1LD_1LA0RF_---0LE_0RF0LB_1LB1RB") c0 (D,0).
Proof. solve_halt 3. Time Qed.

Lemma tm99: halts_at_trans (TM_from_str "1RB1LD_0RC1RE_1LD0RA_0LA0LD_1RC1RF_0LC---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm100: halts_at_trans (TM_from_str "1RB0RF_1RC0LC_1LD1RE_1LB0LD_0RA0RD_0LD---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm101: halts_at_trans (TM_from_str "1RB1LD_1RC0LA_1LB0RD_0LA1RE_0RF1LA_---0RB") c0 (F,0).
Proof. solve_halt 20. Time Qed.

Lemma tm102: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1LA1LF_1RA1RF_0LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm103: halts_at_trans (TM_from_str "1RB1RF_1LC0RD_0LD0LC_1RE0RF_0RB1RA_0LB---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm104: halts_at_trans (TM_from_str "1RB0RF_1RC0RD_0LD0LC_1RF1RE_1LC---_0RA1RD") c0 (E,1).
Proof. solve_halt 6. Time Qed.


