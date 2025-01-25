From BusyCoq Require Import RWLAcc62.

Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.

Ltac solve_halt' bsz bmaxT mnc T :=
  eapply (decide_halt_spec _ bsz bmaxT true mnc T);
  native_check_eq.

Ltac solve_halt bsz :=
  match goal with
  | |- halts_at_trans (TM_from_str ?x) c0 _ =>
    idtac x;
    solve_halt' bsz 3200 2%N 100000000%N
  end.


Lemma tm1: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD0LB_0RA1RE_1RE0RC_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB1RE_0LC1LB_1RE1LD_1LB0LF_0RA0RE_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_1RD0LD_1LE0RB_0LE0LA_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA1LD_1LD1LF_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB1LA_1LA1RC_1LD0RB_1RE0LD_1RF---_1RA1RE") c0 (E,1).
Proof. solve_halt 12. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB0LB_1RC---_0LD0RC_0RF1LE_0LA1RF_1LC0RD") c0 (B,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE---_1RA0RF_0RD1RE") c0 (D,1).
Proof. solve_halt 16. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB0RA_1LC1LE_1RA0LD_1RE---_1LF1LC_1LB0LF") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB1LC_0LA1RB_1LA0RD_0LE1RC_1LF1RB_---0LE") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB0LE_0RC0RD_1LA0LA_1RC0RE_0LA1RF_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB1RF_1LC1RE_0RD0LC_0LB1RD_1RF---_0RA0RC") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB0RA_1LC0RF_1RA1LD_0LE1RF_1LC0LC_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_0RF1LD_1RA0LE_1RA1LC_---0LE") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB1RF_0RC1RE_1LD0RB_0LE0LD_1RA1LD_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0LF1RF_---0RD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB0LF_0LC0RE_0LD1LD_1LA0RA_1RC1RE_1LB---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB0LE_0RC1LC_1RD0LA_1RE0RF_1LC0LB_1RB---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB---_1RC0LE_0RD1RF_1RE1RA_1LB1LE_1RF0RB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB---_0LC0RF_1RD0LD_1LE1RE_0LF0LE_0RA0RC") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RF0LD_0RE1LC_1LB0LF_---1RA") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1LD1RD_1RA0LB_1RC0LF_0LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB---_0LC1LF_1RE0LD_1LB1RE_0RD0RE_1LC0LA") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB---_1LC1RD_0LD0LC_1RE1RB_0RA1RF_0RE1RC") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB1LA_1RC0RD_0LD1RF_1LE1RD_1RE0LA_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LC1LD_1LE1RD_0LB0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1RD0RE_0LA---_1LA0LF_1LE0LB") c0 (D,1).
Proof. solve_halt 11. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB1RE_1LC---_1RF0LD_0LE1LF_0RF1LE_1LB0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB1RB_1RC0RA_1LD0RB_1RB1LE_0LC1LF_0RD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB1RE_1RC1LD_0LD0LB_1LE1LC_1RF0RA_---1RA") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB0RF_0RC0RB_1LD1LA_0LE0LA_1LA0RC_---1LC") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB1LA_1RC1LE_1LD0RC_1LF0LA_---1LC_0LB0LA") c0 (E,0).
Proof. solve_halt 5. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB1LA_1RC1RE_0LD0LA_1LC1RD_1RF0RD_---0RB") c0 (F,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB1RA_0RC1LF_1LD1RC_1LE0LE_0LF0LA_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_0LD0RD_0RA1LE_1LA---_0LA1LB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB---_0RC1RE_1LD1RA_1LE0LD_1RF0RF_0RC0LC") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1RB0LA_0RF0RE_1LD1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1RB0LF_1LC0RE_1LA1LD_0LB0RB_1LB1RB_1RB---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB1LA_1RC0LE_1RD0RB_1RE0RF_1LA1LB_0RC---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB1LD_1LC1RE_1LA1RA_1LF0LB_0RB0RC_---0LE") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1RD1LD_1LA1RD_1LF1LC_---1LB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1RB0RE_1LC0RD_0LD1LB_1LE1LD_1RF0LD_---0RA") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB1LE_0RC1RF_1LD0RA_0LE0LA_1RA0LC_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1RB---_1LC0LF_0LD1LC_1RE1LB_0RF0RE_0LA1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1RB0RC_0LC0RB_0RA1LD_1LE---_0LF0LD_1LA0RD") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm45: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD0LF_1LA---_0LC1LF_0RB0LA") c0 (D,1).
Proof. solve_halt 7. Time Qed.

Lemma tm46: halts_at_trans (TM_from_str "1RB0RD_1RC1RE_1LA0LC_0LC1LD_1RF---_0RA0LB") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm47: halts_at_trans (TM_from_str "1RB---_1LC0RB_1LD1LC_0LE1LF_1RA0LF_0RA1LB") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm48: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1LA1LC_1RA0RF_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm49: halts_at_trans (TM_from_str "1RB0LE_1RC---_1LD1RF_0LA0LE_0RC0LC_0RB1RA") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm50: halts_at_trans (TM_from_str "1RB0LD_1LC0LF_0LD0LC_1RE1RB_0RA0RB_---1RD") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm51: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RE_0LE1LE_1RA0LD_0RB---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm52: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1RD1RA_1LA1RF_0RD0LD_1LE---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm53: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_0RF1LD_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm54: halts_at_trans (TM_from_str "1RB0LD_1LC0RF_0LD0LC_1RE1RB_0RA---_1LE1RD") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm55: halts_at_trans (TM_from_str "1RB1LE_1RC1RD_1LD0RB_0LA0LB_0LC0LF_0LA---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm56: halts_at_trans (TM_from_str "1RB1LD_0RC0LC_1LD0RE_0LA0LD_0LF0RF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm57: halts_at_trans (TM_from_str "1RB---_1RC1RA_1LD1RE_1RE0LD_0RF0RB_1LD0LC") c0 (A,1).
Proof. solve_halt 12. Time Qed.

Lemma tm58: halts_at_trans (TM_from_str "1RB0LE_0RC0RF_1RD0LA_1LA1RB_1LC0LE_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm59: halts_at_trans (TM_from_str "1RB1LD_1RC0RD_0LD1RA_1RF1LE_1RE0LA_---1RC") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm60: halts_at_trans (TM_from_str "1RB0RA_1LC0RC_1LF0RD_1LC1LE_0LD---_1RA1LC") c0 (E,1).
Proof. solve_halt 14. Time Qed.

Lemma tm61: halts_at_trans (TM_from_str "1RB0LA_0RC0LE_1RD0RF_1LB1RC_1RA1LA_0LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm62: halts_at_trans (TM_from_str "1RB0LF_1RC0LA_1RD0RB_1LE0RC_0LA0LD_0RC---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm63: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_0LD0LF_1LA0RE_1LC---_1LD0RD") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm64: halts_at_trans (TM_from_str "1RB0RE_1RC---_0LD1RE_1RA1LD_1RF0LC_1LA0RC") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm65: halts_at_trans (TM_from_str "1RB1LF_0RC---_0RD1RC_1LD1RE_1LC0RA_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm66: halts_at_trans (TM_from_str "1RB---_1LC1RF_1RF1LD_1RE1LA_0RB0LB_1LE0RF") c0 (A,1).
Proof. solve_halt 15. Time Qed.

Lemma tm67: halts_at_trans (TM_from_str "1RB0LF_1LC0RC_0LF1LD_0RE0LE_0LB0RA_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm68: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_1LD0LB_0LE0LD_1LA1RC_0RB---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm69: halts_at_trans (TM_from_str "1RB---_1LC0RD_1LE1LD_0LC0LE_1RF1LB_0RB0RA") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm70: halts_at_trans (TM_from_str "1RB1LD_0RC0RE_1LC1RD_1RE0LA_1LF1RA_1LE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm71: halts_at_trans (TM_from_str "1RB0RF_1RC0LE_1RD0RA_1RE---_0LF1LF_1LB0LE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm72: halts_at_trans (TM_from_str "1RB0LD_0LC0RF_1LE0RD_1LB---_1LA0LC_0RB0RA") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm73: halts_at_trans (TM_from_str "1RB0LC_1RC0LF_1LD1LE_1LB0LC_0LA0RE_1RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm74: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LD0LC_1LA0LE_1LF---_0LC1LE") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm75: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_0RD0LD_1LE1RB_1RB0LA_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm76: halts_at_trans (TM_from_str "1RB1LC_1LA1RC_1RD0RF_1LF0RE_1LB1RA_---0LB") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm77: halts_at_trans (TM_from_str "1RB---_1RC1RF_0LD1RF_0LE1LD_1RA0RC_0RB0RE") c0 (A,1).
Proof. solve_halt 15. Time Qed.

Lemma tm78: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RE0LD_1LB0LF_0RE0RA_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm79: halts_at_trans (TM_from_str "1RB1RF_0LC1RE_1RD1LC_1RA1LB_---0LD_1RA0RF") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm80: halts_at_trans (TM_from_str "1RB0LC_0RC---_1RD0RE_1LE0RF_0LA0LE_1RB1RF") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm81: halts_at_trans (TM_from_str "1RB0LC_1LC1RF_1LE0RD_0LB1RC_1LA1LC_---1RB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm82: halts_at_trans (TM_from_str "1RB1LE_0RC0RF_1RD0LE_1LA0RB_1LF---_0LA0LF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm83: halts_at_trans (TM_from_str "1RB0RC_1LC1RF_0RD0LD_1RE0LF_1RA---_0LC1RA") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm84: halts_at_trans (TM_from_str "1RB0LE_1LC0RD_1RD0LC_0RE1RF_0LB1RA_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm85: halts_at_trans (TM_from_str "1RB---_1LC0RF_1RE0LD_0RE1RB_0LB1RA_1RB0RD") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm86: halts_at_trans (TM_from_str "1RB0LF_1LC0RD_1LA0LB_1LF0RE_1RC0RB_1LC---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm87: halts_at_trans (TM_from_str "1RB0LA_0RC---_1LC1RD_1RE1LA_1RC1RF_0RD0RE") c0 (B,1).
Proof. solve_halt 5. Time Qed.

Lemma tm88: halts_at_trans (TM_from_str "1RB0RA_1LC1RA_---0LD_1LA1LE_1LB1LF_0LD0LF") c0 (C,0).
Proof. solve_halt 3. Time Qed.

Lemma tm89: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_1RD0LC_0RE1RF_0LB0RD_1RA---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm90: halts_at_trans (TM_from_str "1RB0RA_1LC1RA_1LA1LD_0LE0LA_1LF0LA_1LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm91: halts_at_trans (TM_from_str "1RB---_0RC1RE_0LD0RF_1LE0LF_1RB0LC_1LC0RA") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm92: halts_at_trans (TM_from_str "1RB1RF_1RC1LC_1RD0LC_1LE0RE_1RA1LC_---0LD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm93: halts_at_trans (TM_from_str "1RB0RE_0RC0RD_1LA1LD_0LC0LA_1RF1LC_---1RE") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm94: halts_at_trans (TM_from_str "1RB1LD_1RC---_0RD1RF_1LE0LA_1RA0LE_1LA0RC") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm95: halts_at_trans (TM_from_str "1RB0RE_1RC0LB_1LD1RA_0RF1LB_0RC1RF_---1RB") c0 (F,0).
Proof. solve_halt 7. Time Qed.

Lemma tm96: halts_at_trans (TM_from_str "1RB---_1RC0RE_1LD0RF_0LE1LD_1RA0LD_0RD1RB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm97: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD0RF_0RA0LE_0LD0LC_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm98: halts_at_trans (TM_from_str "1RB1LD_0RC1RC_1LC1RD_1RE1LD_1RF0LE_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm99: halts_at_trans (TM_from_str "1RB---_1RC1RA_1LD0LF_1RE0LD_0RC0RB_1LD1RD") c0 (A,1).
Proof. solve_halt 12. Time Qed.

Lemma tm100: halts_at_trans (TM_from_str "1RB1LA_1LC1RF_0RD0LC_0LB1RE_1RD---_0RA1RC") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm101: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1RB1RD_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm102: halts_at_trans (TM_from_str "1RB0LE_0LC1LB_1RD1LA_0RE0RD_1LF1RD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm103: halts_at_trans (TM_from_str "1RB0LD_0LC1RE_0RA1LC_1LB---_0RF0LE_0RB1RA") c0 (D,1).
Proof. solve_halt 9. Time Qed.

Lemma tm104: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0RD0LE_1LE0LF_0LA0RA_1RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm105: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1LD0RA_1LE1LF_0LA1LC_0LB---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm106: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_0RD0RB_1LD1RA_1RC0LE_---0RD") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm107: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD1RB_0LA0RA_0RF0LF_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm108: halts_at_trans (TM_from_str "1RB0LF_0RC---_1RD0LA_1RE0RB_1LC1RD_0LE0RF") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm109: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_1RD0LB_---1RE_0RA1RC_1LA1LF") c0 (D,0).
Proof. solve_halt 4. Time Qed.

Lemma tm110: halts_at_trans (TM_from_str "1RB1RD_1LC1RA_1LD0RA_1LE0RB_0LF0LD_0RA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm111: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1LD0RA_1LE1LF_0LA1LC_0RE---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm112: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1LD1RF_1RD0LA_1LD1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm113: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LD0LC_0RA0RF_1RD---_1RA0LA") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm114: halts_at_trans (TM_from_str "1RB0LD_1LC1RE_1LA1RC_1LB1LD_---1RF_0LC0RC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm115: halts_at_trans (TM_from_str "1RB0RF_1RC0LB_0RD---_1LE1RA_1LB0RD_1RE0LC") c0 (C,1).
Proof. solve_halt 4. Time Qed.

Lemma tm116: halts_at_trans (TM_from_str "1RB0LC_1LC0RE_1RD1LC_0LF0RB_1LE1LA_---0LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm117: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_1LD0RE_1LB1LD_---1RC_0RA1LA") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm118: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA0LC_0RA0RE_1RF0LC_0LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm119: halts_at_trans (TM_from_str "1RB1LA_1LA1RC_0RC0RD_1LE1RD_1LF0LA_---0LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm120: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_1RD0LC_0LA0RA_1LC0RF_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm121: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_0RA1LD_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm122: halts_at_trans (TM_from_str "1RB1RE_0LC1LD_0LD1LB_1LE1LC_1RF0RA_---1RA") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm123: halts_at_trans (TM_from_str "1RB0RF_1RC1LC_1RD0LC_1LB0RE_1RA1LC_---1RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm124: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0LD1LC_1RE0LA_0RB0RE_0RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm125: halts_at_trans (TM_from_str "1RB---_1RC0RE_1LD0RF_0LE1LD_1RA0LD_1RA1RB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm126: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_0RD0RF_0LE---_1LF1LD_1LA0RE") c0 (D,1).
Proof. solve_halt 11. Time Qed.

Lemma tm127: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF0RC_---1RA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm128: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_0RF0LE_0LD1RF") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm129: halts_at_trans (TM_from_str "1RB1RF_1RC0LE_1RD1RF_1LB---_1LB1LE_1RA0RB") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm130: halts_at_trans (TM_from_str "1RB1LD_0RC1RD_1LA1RF_0LA0RE_---1RC_1LF1RA") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm131: halts_at_trans (TM_from_str "1RB1RC_1LA1RA_---0RD_1LE0RD_1LF1LA_0LE1LA") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm132: halts_at_trans (TM_from_str "1RB0RC_1RC1RF_1LD1RA_0LE0LD_1RE0RC_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm133: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_0LD1LB_1RA0LE_1LC1LF_1LB---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm134: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_0RD0LD_1LE1RB_1RB0LA_1RC---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm135: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LE0LD_0LB1LF_1RA0LC_1LE---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm136: halts_at_trans (TM_from_str "1RB0RF_1RC0RD_0LD1RA_---0LE_1RC1LE_1LC1RF") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm137: halts_at_trans (TM_from_str "1RB0LE_1RC0RE_1RD1RF_1LA0RB_0LA1RD_---1RB") c0 (F,0).
Proof. solve_halt 17. Time Qed.

Lemma tm138: halts_at_trans (TM_from_str "1RB1LF_1RC---_1RD0RB_0RE1RD_1LF1RC_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm139: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_1LE1LD_1LE0LC_1RA0RF_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm140: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LF0RB_---1RC") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm141: halts_at_trans (TM_from_str "1RB0RC_1LB1RA_1LD1RF_0LE0LD_1RA1LD_1RE---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm142: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD1RA_1LA0LB_1LD0LF_1RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm143: halts_at_trans (TM_from_str "1RB0LD_1RC0RA_1LA0RF_1RF0LE_1LB0LA_1RB---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm144: halts_at_trans (TM_from_str "1RB1RF_1LC0RA_1RA0RD_1RC0LE_1LD0LE_1LD---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm145: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1RE0LF_0LA1LE_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm146: halts_at_trans (TM_from_str "1RB1LF_1RC---_0RD0LD_1LD1RE_1RC0RA_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm147: halts_at_trans (TM_from_str "1RB0LF_0RC1RD_1LD0RE_0RE---_0RA1RF_1LA0LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm148: halts_at_trans (TM_from_str "1RB1RE_1LC1LD_0LD0LB_1LE1LC_1RF0RA_---1RA") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm149: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0LD1LC_1RE0LA_0RB0RE_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm150: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0RD0LB_---1LA_0RA1RC_1LA1LF") c0 (D,0).
Proof. solve_halt 4. Time Qed.

Lemma tm151: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_0RD0LD_1LE1RB_1RB0LA_0LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm152: halts_at_trans (TM_from_str "1RB0LD_1LC0RD_1RF0RA_0LE1RA_1RC1LE_1RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm153: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD0RD_1RA1LB_1LF0RD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm154: halts_at_trans (TM_from_str "1RB0RD_1LC1RA_1LA1LC_1RA1LE_0LF---_1LD1LA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm155: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_1RE1LF_1RA0LD_1RC---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm156: halts_at_trans (TM_from_str "1RB1LA_1LC0RC_1LD1RC_0RC1LE_1LF0LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm157: halts_at_trans (TM_from_str "1RB1LE_1LC1RF_0RD1RC_1LE1RB_0LA0LE_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm158: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA0RE_1LA0RF_1LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm159: halts_at_trans (TM_from_str "1RB0LC_1RC1RA_1LD0RE_0LA1LD_0RA1RF_---1RA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm160: halts_at_trans (TM_from_str "1RB1RE_1RC1LB_1LB1RD_1LE0RC_1RF0LE_1RA---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm161: halts_at_trans (TM_from_str "1RB---_1LC1RF_0LD0RD_1RF1LE_1LC1LA_0RB0RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm162: halts_at_trans (TM_from_str "1RB1LD_1RC0RC_0LA0RA_0LE1LC_1LB0LF_---0LD") c0 (F,0).
Proof. solve_halt 12. Time Qed.

Lemma tm163: halts_at_trans (TM_from_str "1RB1LD_0LC1LF_1RD1LB_1RE1RF_---0RA_1LB0RD") c0 (E,0).
Proof. solve_halt 16. Time Qed.

Lemma tm164: halts_at_trans (TM_from_str "1RB0LE_0LC1LB_1RD1LA_0RE0RD_1LF1RD_0RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm165: halts_at_trans (TM_from_str "1RB---_0RC0LE_1RD1RA_1LB1RC_1RA1LF_1RB0LF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm166: halts_at_trans (TM_from_str "1RB1LD_1RC1LB_1RD1RF_1LA0LE_---1LB_1RD0RC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm167: halts_at_trans (TM_from_str "1RB---_0RC1RB_1LD1RF_0LE0LD_0RA1LD_1RB1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm168: halts_at_trans (TM_from_str "1RB0LD_1RC1RF_1LA0RE_0LA1LD_1RE0RA_1LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm169: halts_at_trans (TM_from_str "1RB1RE_1LC---_1RF0LD_0LE1LD_0RF1LE_1LB0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm170: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_---1LA_1RA1LE_0RE0LF_1RA1LB") c0 (C,0).
Proof. solve_halt 14. Time Qed.

Lemma tm171: halts_at_trans (TM_from_str "1RB1RF_1LC1RF_1RD0LB_---1RE_0RA0RC_1LC0RE") c0 (D,0).
Proof. solve_halt 5. Time Qed.

Lemma tm172: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD0RE_0LA0LD_0LF0RF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm173: halts_at_trans (TM_from_str "1RB0RE_1LC1RB_0LF0LD_1RE1LD_1RA0RB_---1LB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm174: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RA1LD_0LB---_0LF1LD_1LF1LB") c0 (D,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm175: halts_at_trans (TM_from_str "1RB0LA_0RC0LD_0RD---_1RE0RE_0LF1RA_1RC1LE") c0 (C,1).
Proof. solve_halt 16. Time Qed.

Lemma tm176: halts_at_trans (TM_from_str "1RB0LE_1RC0LA_1RD0RB_1LB0RF_1LC0LB_1RC---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm177: halts_at_trans (TM_from_str "1RB0LC_0LC1RF_1RF1RD_1LE---_0LC0LE_0RA0RD") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm178: halts_at_trans (TM_from_str "1RB0LE_1RC0RD_1LD---_1RF1LA_0RC0LE_0RA1LD") c0 (C,1).
Proof. solve_halt 7. Time Qed.

Lemma tm179: halts_at_trans (TM_from_str "1RB0RC_1RC1RF_0LD1LE_1LA0RE_1LC---_0RB0RF") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm180: halts_at_trans (TM_from_str "1RB1RC_1LC0LC_1RD1LC_---0RE_1LF1RE_0LB0LA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm181: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0LD1RB_1RE---_1LF0LC_0LA0RA") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm182: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA0LC_0RA0RF_1RD0LC_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm183: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1RE_0RF---_0RA0LA") c0 (E,1).
Proof. solve_halt 12. Time Qed.

Lemma tm184: halts_at_trans (TM_from_str "1RB1LE_1RC---_0RD1RC_1LE1RF_0LA0LE_1RC0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm185: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_1LE1LD_1LB---_1RF0LC_0LB0RE") c0 (D,1).
Proof. solve_halt 16. Time Qed.

Lemma tm186: halts_at_trans (TM_from_str "1RB1RA_0RC0RD_1LD1RE_0LE0LD_1RA0RF_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm187: halts_at_trans (TM_from_str "1RB0LD_0RC1RA_1RD1RF_1LA1LE_0LA1RE_0RB---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm188: halts_at_trans (TM_from_str "1RB---_0RC1RE_1LD0RB_0LE0LD_1RF1LD_0LF1RA") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm189: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_1RD0LE_1LC0RB_0RA1LE_1RA---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm190: halts_at_trans (TM_from_str "1RB0LA_0LC0RD_1LA1LB_0RE1RF_---0RF_1RC0RA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm191: halts_at_trans (TM_from_str "1RB1LE_0RC0LA_1RD0RA_1LE1RF_0LA0LD_1RB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm192: halts_at_trans (TM_from_str "1RB---_1RC1LE_1LD0RD_0RE0LE_1RA0LF_0LD1RB") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm193: halts_at_trans (TM_from_str "1RB0LA_1LC0RC_1RD1LA_1RE0RF_1RA1LE_---0RC") c0 (F,0).
Proof. solve_halt 15. Time Qed.

Lemma tm194: halts_at_trans (TM_from_str "1RB---_1RC1RB_1LD0RB_1LF1LE_1LD0LC_1LA1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm195: halts_at_trans (TM_from_str "1RB0RE_0RC1RB_1LD1RA_0LE0LD_1RF1LD_0RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm196: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA1RE_0RD0LC_0RB0RF_1RE---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm197: halts_at_trans (TM_from_str "1RB1LD_0LC0RC_1LE0RD_0RB1LF_1RA---_1LA0LB") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm198: halts_at_trans (TM_from_str "1RB1LF_1LC1RD_1LD1LA_1LE0RD_1RA0LB_---0LE") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm199: halts_at_trans (TM_from_str "1RB0RA_1LC0LC_0LD0RD_1RA1LE_1LC0LF_1LE---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm200: halts_at_trans (TM_from_str "1RB0RC_1LC1RF_0RD1LB_1RE1RD_0RA0RE_---0LC") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm201: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1LE0LF_0LA1LE_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm202: halts_at_trans (TM_from_str "1RB0RE_1RC0LF_1RD0RA_1RE---_1LE1RB_0LA1LF") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm203: halts_at_trans (TM_from_str "1RB0RD_1RC1RE_1LA0LC_0LC1LD_1LF---_0RA1RF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm204: halts_at_trans (TM_from_str "1RB1RA_1LC1LD_1RA0RB_1LE1LB_1RA0LF_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm205: halts_at_trans (TM_from_str "1RB1RF_1LC1RD_1LA1LC_---0RE_1LC1RB_0LF1RA") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm206: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1RD1RB_1RE---_0LA0RA_1LE0LD") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm207: halts_at_trans (TM_from_str "1RB1LB_1RC0LB_1LD0RD_1RE1LB_1RA0RF_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm208: halts_at_trans (TM_from_str "1RB1RF_1RC0RE_1LD0LC_1LA1LC_---1RF_0RA1RA") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm209: halts_at_trans (TM_from_str "1RB1LB_0RC0LF_1LD0RB_1LE0LB_0LA0LC_1RB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm210: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_0LD1RB_1RE---_0LA1LE_1LE0LD") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm211: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD1RA_0RE1RC_1RF0RD_1LB0LF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm212: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_1LA0LC_1RE1RF_1LA1RB_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm213: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_0LD1LB_1LE0LF_0RA1RE_---0LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm214: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA1RE_0RC0RF_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm215: halts_at_trans (TM_from_str "1RB1RC_1RC0LE_1LD0RA_1LB1LD_1LF1RE_---0LA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm216: halts_at_trans (TM_from_str "1RB0LC_1RC0RE_1LD1LA_---1LC_1RF1RA_0RB1RF") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm217: halts_at_trans (TM_from_str "1RB0RE_1RC1RF_0RD0RA_0LE---_1LB0LF_0LE1LE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm218: halts_at_trans (TM_from_str "1RB1LC_0LC1RE_1LA0RD_1LB1RC_1RD0RF_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm219: halts_at_trans (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RA0LE_0LF1LD_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm220: halts_at_trans (TM_from_str "1RB1LC_1LC1LE_1RF1RD_1LB1RE_0LB0RC_---1RA") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm221: halts_at_trans (TM_from_str "1RB1LD_0LC---_1LE0RD_1LB1LE_1RF0LA_0RD0RF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm222: halts_at_trans (TM_from_str "1RB1LC_0RC1RD_1LD0LF_1LA0LE_---0RB_1RB1LF") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm223: halts_at_trans (TM_from_str "1RB1RD_0RC---_1RD0LF_1LE0RF_0LA0LE_0LF1RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm224: halts_at_trans (TM_from_str "1RB0LF_0LC0RE_1LD1RC_1LA0LC_0RB0RA_1LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm225: halts_at_trans (TM_from_str "1RB1RA_0RC1LE_1LD1RC_1RB0LF_---1LF_0LE0LA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm226: halts_at_trans (TM_from_str "1RB0RE_0RC0RB_1RD1LA_1LE1RF_1RA0LD_0LE---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm227: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_1LA1RC_1RE0RF_---0RF_1RC0RB") c0 (E,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm228: halts_at_trans (TM_from_str "1RB0RF_1RC1RA_1RD0LE_1LC---_1LF1LE_1RB0LE") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm229: halts_at_trans (TM_from_str "1RB1RA_1RC0LE_1LD1RF_0RD1RE_1LA1LB_0RD---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm230: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LD1RE_1RF1LC_0RB0LE_---0RA") c0 (F,0).
Proof. solve_halt 12. Time Qed.

Lemma tm231: halts_at_trans (TM_from_str "1RB0LA_0RC0RE_0RD1LD_0LD1LA_1RF---_1LA1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm232: halts_at_trans (TM_from_str "1RB0LE_1LC1RE_0RA0LD_0LB0LD_1RF---_0RC0LC") c0 (E,1).
Proof. solve_halt 5. Time Qed.

Lemma tm233: halts_at_trans (TM_from_str "1RB0LE_0RC---_1RD0LA_1LE1RF_1LC0LE_0RC0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm234: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD0LA_1RE0RF_1LB0RA_0LB0LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm235: halts_at_trans (TM_from_str "1RB0RA_0LC0RC_1LE1LD_0LB0LF_1RA1LB_0RB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm236: halts_at_trans (TM_from_str "1RB1LF_1LC1LE_0RD1RC_1LA1RD_---0LB_0RD0LA") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm237: halts_at_trans (TM_from_str "1RB---_0LC0RB_1RD1LB_1LE1RC_0LA0LF_1RC0LD") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm238: halts_at_trans (TM_from_str "1RB---_1LC1RF_0RD0LC_0LE1RF_1LC0RA_1RD1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm239: halts_at_trans (TM_from_str "1RB---_0RC0LB_1RD1LE_1LB1LD_1RF0RD_0RA0RE") c0 (A,1).
Proof. solve_halt 7. Time Qed.

Lemma tm240: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RD1LB_0RF1LE_0RA0LC_0LE1RD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm241: halts_at_trans (TM_from_str "1RB0LC_0RC0RF_1RD1LE_1LC---_1LA1RA_1RA0RE") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm242: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA0LC_0RA0RE_1RF0LC_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm243: halts_at_trans (TM_from_str "1RB0LF_1RC1LD_1RD0RB_0LE1RA_0LA1LD_---1LC") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm244: halts_at_trans (TM_from_str "1RB0RC_1LC1RD_1RF0RD_1LE1LD_1RA0LE_1RA---") c0 (F,1).
Proof. solve_halt 7. Time Qed.

Lemma tm245: halts_at_trans (TM_from_str "1RB0LC_1RC---_1LD1RE_1LE0LD_1RF0RA_0RC1RF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm246: halts_at_trans (TM_from_str "1RB---_0RC0RE_1LC0RD_1RA1LE_0LD0RF_1LA0LC") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm247: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_0LD1LB_1LA1LF_1LC0RB_0LA---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm248: halts_at_trans (TM_from_str "1RB0LC_1RC1RA_1LD1LA_1RE1LD_---1RF_0RE1RA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm249: halts_at_trans (TM_from_str "1RB1RD_1RC0RB_1RD1RA_1LE1RF_1LC0LE_0RB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm250: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LA0RB_0RD1LE_0LC---_1RB1RB") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm251: halts_at_trans (TM_from_str "1RB0LC_0RC0RF_1LD0LE_0LA1LD_0RA---_0RE0RA") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm252: halts_at_trans (TM_from_str "1RB0LF_1RC0RB_0LD0RD_1RB0RE_1RF---_1LA1LF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm253: halts_at_trans (TM_from_str "1RB1LB_1RC0LC_1LD0RF_---1LE_1LB1LA_0LA1RC") c0 (D,0).
Proof. solve_halt 16. Time Qed.

Lemma tm254: halts_at_trans (TM_from_str "1RB1LF_0LC---_1LF1RD_1RE0RA_0RC0LC_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm255: halts_at_trans (TM_from_str "1RB0LD_1RC---_0RD0LD_1LE1RF_1LF0LE_1RC0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm256: halts_at_trans (TM_from_str "1RB1RE_1RC1LA_1RD0RF_1LD0RA_1LB0LE_0RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm257: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_0LD1RF_1LD0LA_1LD1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm258: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RE1LD_1LB0LA_0RF0RE_0LD1RE") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm259: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA1LD_1LD0LF_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm260: halts_at_trans (TM_from_str "1RB0LF_1LC0RF_1RE1LD_1LE1LC_1RA0RD_---1RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm261: halts_at_trans (TM_from_str "1RB0RF_1LC0LB_0RD0LB_1RF1RE_1RC---_0RA1RD") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm262: halts_at_trans (TM_from_str "1RB0RE_0LC1RF_1LC0LD_1RA1LD_1LC1RE_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm263: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_1RB0LD_1LE0LF_0RE0LB_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm264: halts_at_trans (TM_from_str "1RB1RF_1LC---_1LD0LB_0LE0RE_1RF1LC_0RA0RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm265: halts_at_trans (TM_from_str "1RB---_1RC0RC_1RD0LE_1RE1RA_1LC1LF_0LC1LB") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm266: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD0RF_1RC1LE_---0LC_1LF0LA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm267: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1RD1RF_0LA0LA_1LD1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm268: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_1LD0LC_1RE0LB_1RC0RD_1RE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm269: halts_at_trans (TM_from_str "1RB0LD_0RC0RE_1RD0LF_1LA0RA_0RC---_1LC0LF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm270: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA0RE_1LF0RF_1LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm271: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0LD1RB_1RE---_1LF0LC_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm272: halts_at_trans (TM_from_str "1RB0LF_1LC1RB_1LA0LD_1RE1LD_1RE0RB_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm273: halts_at_trans (TM_from_str "1RB1RD_1RC1LD_1LB---_1RA0RE_1RA0LF_1LE1LF") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm274: halts_at_trans (TM_from_str "1RB0LA_0RC1RE_0LD0RB_1LA0RF_1RF---_1RD0LB") c0 (E,1).
Proof. solve_halt 12. Time Qed.

Lemma tm275: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_1RA1LD_1RA0LE_---1LC_1LD1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm276: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_0RD1LD_0RE0LF_---0LB_1RA1LC") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm277: halts_at_trans (TM_from_str "1RB0LE_0LC1LB_1RD1LA_0RE0RD_1LF0LF_0RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm278: halts_at_trans (TM_from_str "1RB0RB_1LC0RB_0RE0LD_0LC0LF_1LB1RA_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm279: halts_at_trans (TM_from_str "1RB0RB_1LC1LB_1RD0LB_1RF0RE_1RA0RD_---0RC") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm280: halts_at_trans (TM_from_str "1RB1LB_1LA0LC_1RD1LC_0LF1RE_1RB0RD_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm281: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RA1LD_0LB0LE_1LF0RA_0RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm282: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RE1LD_0LB1LA_1LF0RE_0RB0RC") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm283: halts_at_trans (TM_from_str "1RB0LC_1RC1LE_1LD1LA_1RE1LD_---1RF_0RE1RA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm284: halts_at_trans (TM_from_str "1RB0RA_0LC0RC_1RA0RD_1RE---_1LF1LE_1RA0LE") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm285: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RE1LD_1RE0LF_1RB1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm286: halts_at_trans (TM_from_str "1RB0LC_1LA0RE_1LD0LF_0RD0LB_1RB1RA_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm287: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA1LD_1RD0LF_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm288: halts_at_trans (TM_from_str "1RB0LB_1LC0RF_0RE0LD_0LB1LD_0RA1RA_1RC---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm289: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_1LD0LC_0RE0LE_1LC0LF_1LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm290: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD0RD_1LD1RE_0RF1LE_1RA0LF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm291: halts_at_trans (TM_from_str "1RB1RE_1RC1LB_1LD1LE_1RF1RB_1RA0LC_---0RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm292: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1RD1LB_0RA1LE_0RF0LC_0LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm293: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1LA_0LE---_1RF1LE_1RE0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm294: halts_at_trans (TM_from_str "1RB1LB_1LA1LC_---0LD_1RE0LD_1RF1RB_0RE1RB") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm295: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1RD1LD_1LA1RD_0LF1LC_---0LA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm296: halts_at_trans (TM_from_str "1RB0RD_1LC0RF_0RE0LD_0LC0LB_1RA1LE_1RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm297: halts_at_trans (TM_from_str "1RB---_1LC0RF_0LE0RD_1RE1LB_1RA0RC_1LD0LF") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm298: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RA1LD_1RE0LF_0LE1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm299: halts_at_trans (TM_from_str "1RB0LE_1RC0LA_1LD0RA_1LB1LD_1RB0LF_---0LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm300: halts_at_trans (TM_from_str "1RB0RE_1LC0LA_1RD1RC_1LB1RF_1LD1RD_---0RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm301: halts_at_trans (TM_from_str "1RB0LE_1RC---_1LD0LC_1RF0RA_1LC1RD_0RE1RF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm302: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_0RC1LD_1RA0LE_---1LC_1RE1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm303: halts_at_trans (TM_from_str "1RB1LD_1RC1RA_1LA0RC_---1LE_0LC1LF_1LB0LF") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm304: halts_at_trans (TM_from_str "1RB1RD_1RC1RB_1LD0RB_1LB0LE_0LF1LD_---1LA") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm305: halts_at_trans (TM_from_str "1RB---_1LC0RD_0RB1RC_1RE0LF_1LD0RA_0LE1LF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm306: halts_at_trans (TM_from_str "1RB0RD_1LC0LE_1LD1LB_1RB1RA_1RF1LE_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm307: halts_at_trans (TM_from_str "1RB1RA_0LC0LF_---1RD_1LE0LB_1RF1LD_0RA1RF") c0 (C,0).
Proof. solve_halt 3. Time Qed.

Lemma tm308: halts_at_trans (TM_from_str "1RB0RF_1RC1RE_1LD0LC_0RB1LC_1RA0RB_---0RB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm309: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD0LB_0RA1RE_1RE0RC_0RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm310: halts_at_trans (TM_from_str "1RB0LD_1RC0LE_1LA0LA_1RF0LC_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm311: halts_at_trans (TM_from_str "1RB0RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1LA---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm312: halts_at_trans (TM_from_str "1RB0LA_0RC1RF_0LD1RE_1LA0LA_1LC0RB_0RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm313: halts_at_trans (TM_from_str "1RB0RA_1LC1RA_1LD1LB_0LE0LD_1LA0LF_---0LC") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm314: halts_at_trans (TM_from_str "1RB0RC_1LC1RF_0LD0LC_1RE0LA_0RA---_1LD1RD") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm315: halts_at_trans (TM_from_str "1RB0LA_1RC---_1RD0RF_0RE0LF_1LC1RC_0RA1LA") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm316: halts_at_trans (TM_from_str "1RB1LA_1RC0LF_1RD0RA_1RE0LD_1LC---_1LA1LB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm317: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD1RB_1LE1LF_0LA1LC_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm318: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RA0RD_---1LE_1LF0RA_0LB0LC") c0 (D,0).
Proof. solve_halt 3. Time Qed.

Lemma tm319: halts_at_trans (TM_from_str "1RB0LC_1LA0RD_0RD1LE_1LB1RC_0LF1RD_---0LB") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm320: halts_at_trans (TM_from_str "1RB0RB_1LB1LC_1RD0LC_0RF1RE_---1RF_0RB0RA") c0 (E,0).
Proof. solve_halt 10. Time Qed.

Lemma tm321: halts_at_trans (TM_from_str "1RB1RB_1LC0RF_1RE1LD_1LE1LC_1RA0RD_---1RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm322: halts_at_trans (TM_from_str "1RB0LF_1LC1RF_0RE0LD_0LB0LD_0RA0LF_1RC---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm323: halts_at_trans (TM_from_str "1RB0LC_0LC1RE_1RA1LD_1RB0LA_1RF---_1LA0RC") c0 (E,1).
Proof. solve_halt 5. Time Qed.

Lemma tm324: halts_at_trans (TM_from_str "1RB0RE_0LC0LA_---1LD_0LE1LF_1RA1RE_1LD0LB") c0 (C,0).
Proof. solve_halt 6. Time Qed.

Lemma tm325: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_1LD1RC_0RA1LE_1LF0LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm326: halts_at_trans (TM_from_str "1RB---_0RC0RE_1RD0LA_1LE1RB_0RF0LE_0LD1RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm327: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_1LE0LD_0LA0RB_1LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm328: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RF0LD_1RE1LC_1LD1RB_---1RA") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm329: halts_at_trans (TM_from_str "1RB0LE_0RC1LD_1LA1RC_---1LE_0LD0LF_1RB1RF") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm330: halts_at_trans (TM_from_str "1RB---_0RC1LC_1RD1LC_0RE1RE_1LF0RD_0LF1LA") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm331: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_0LC---_0RA1RF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm332: halts_at_trans (TM_from_str "1RB1LD_0RC0LE_1LC1RA_0LE0LA_1RA1LF_---0LD") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm333: halts_at_trans (TM_from_str "1RB0LA_0RC0RA_1RD0LD_1LA0RE_1RF---_1RC0RA") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm334: halts_at_trans (TM_from_str "1RB1LD_1LC1RE_0RA0LB_1LA0LF_0RB0RC_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm335: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1LD0RA_1LB0LC_1LA1LF_0RD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm336: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_0LE1LD_0LC1LB_1RF0LA_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm337: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1RD1RE_1LE1RF_---0LA_0RA1RD") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm338: halts_at_trans (TM_from_str "1RB0LC_1RC1RD_1LA0RB_1RE0LA_1LD1RF_0RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm339: halts_at_trans (TM_from_str "1RB0RF_0RC1RA_1LD0RD_0LE0LD_1RA1LD_0RA---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm340: halts_at_trans (TM_from_str "1RB1LF_0RC---_0RD0LE_1RE1RC_1LA1LF_1RD1LC") c0 (B,1).
Proof. solve_halt 10. Time Qed.

Lemma tm341: halts_at_trans (TM_from_str "1RB1LE_1LC1RE_0LD1LB_1LA0LB_1RD0LF_---0RA") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm342: halts_at_trans (TM_from_str "1RB---_1RC1LD_1RD0RC_1LE0LF_0LB0RB_0LA0RB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm343: halts_at_trans (TM_from_str "1RB0LC_1LA0RE_1LD0LF_0RD0LB_1RB1RE_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm344: halts_at_trans (TM_from_str "1RB0RF_1LC0RE_1RD1LB_0LB1RC_1RA0LD_0RB---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm345: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm346: halts_at_trans (TM_from_str "1RB0RA_0LC0LE_1RA1LD_1LE0LF_0LC0RC_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm347: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RC1LD_1RB0LE_1LA1RF_0RE0RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm348: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LD1LD_1LE1RD_1LE0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm349: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_0RA1LD_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm350: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1RB0LD_0RF0RE_1RA1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm351: halts_at_trans (TM_from_str "1RB0RD_1RC1RF_1LD0LE_1RA0LC_0LD1LC_0RA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm352: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA1RF_1RA0LD_0RB---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm353: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_1LA---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm354: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA1LD_1RD1LF_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm355: halts_at_trans (TM_from_str "1RB1RD_0RC0RF_1RD0LA_1LE1RB_0LA0LE_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm356: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LD1LD_1LE1RD_0RC0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm357: halts_at_trans (TM_from_str "1RB1LA_1RC0LF_1RD0RA_1RE0LD_0LF---_1LA1LB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm358: halts_at_trans (TM_from_str "1RB---_1LC1RE_0LD1LC_1RE1LF_0RB0RE_1RC1LA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm359: halts_at_trans (TM_from_str "1RB0LC_0LA0RB_1RD1LE_0RE---_1LF1LA_1LA1LC") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm360: halts_at_trans (TM_from_str "1RB1LB_1LC0RE_0LD0RA_1LA1LF_1RB0RE_0LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm361: halts_at_trans (TM_from_str "1RB1LA_1LA1RC_0RC0RD_1LE1RE_1LF1RE_---0LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm362: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1LE0LA_---0LF_1RC1LC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm363: halts_at_trans (TM_from_str "1RB---_1RC0LA_1LD0RD_0LA1LE_0RF0LF_0LC0RB") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm364: halts_at_trans (TM_from_str "1RB1LE_1RC1LA_1RD1RF_1LB0RE_0LA0LB_---0RD") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm365: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_1LE0LD_0RC0RB_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm366: halts_at_trans (TM_from_str "1RB0LE_0RC0RD_1LA0LA_1RC0RE_0LA0RF_1RC---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm367: halts_at_trans (TM_from_str "1RB---_1LC0RA_1RD0LC_0LE0RE_1RF1LC_1LC0RB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm368: halts_at_trans (TM_from_str "1RB1LD_0RC1RE_1LD0RA_0LA0LD_1RC0RF_0RA---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm369: halts_at_trans (TM_from_str "1RB1RA_1RC0LB_0RD1RE_1LD1LB_0RF1RC_1RA---") c0 (F,1).
Proof. solve_halt 7. Time Qed.

Lemma tm370: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RE0RF_0RB0LB_1RD---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm371: halts_at_trans (TM_from_str "1RB0RA_1LC0RF_0LD1LC_1LE1RD_1LA0LA_---0RA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm372: halts_at_trans (TM_from_str "1RB0LA_0LC0LD_1RD1LA_1LA1RE_0RC0RF_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm373: halts_at_trans (TM_from_str "1RB0RF_1LC0LB_1RD0LB_0RA1RE_0RF---_0RC0LD") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm374: halts_at_trans (TM_from_str "1RB1LA_1LC1LD_1RE1RA_1RF0LB_---0RC_0LC1RD") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm375: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RF1LD_0LE0LC_1LC1RF_1RE1RA") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm376: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_0RD0LD_1LE1RB_0LA0LE_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm377: halts_at_trans (TM_from_str "1RB0LC_0RC0RE_1LD1RB_0LA1LD_0RF0LE_0RA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm378: halts_at_trans (TM_from_str "1RB1LE_1LC---_0RD1RC_1LE1RF_0LA0LE_1LC0RB") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm379: halts_at_trans (TM_from_str "1RB1RD_1RC0LF_1LD0RA_1RE0LD_0RF---_0LC1LB") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm380: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_0LD0RD_1LA1LE_0LC0LF_1LA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm381: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_0RD0LD_1LE1RB_0LA0LE_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm382: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1LD1RA_0LE0LD_0RA1LD_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm383: halts_at_trans (TM_from_str "1RB---_1RC1LE_0RD1LF_1RE1RC_1LB1RF_0RA0LB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm384: halts_at_trans (TM_from_str "1RB---_1LC0LE_0LD0RD_1RD1LB_0LA1RF_0RE0RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm385: halts_at_trans (TM_from_str "1RB1RE_0RC---_1LD1LC_1LE0LC_0RA1RF_1RE0RD") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm386: halts_at_trans (TM_from_str "1RB1RF_0RC1LB_1RD0RB_1LE0LD_0RA0LD_1RE---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm387: halts_at_trans (TM_from_str "1RB0RA_1LC1RA_0LD0LC_0RE1RB_1RD0RF_0RB---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm388: halts_at_trans (TM_from_str "1RB0LA_1LC0RC_1RD1LA_1LA1RE_---1RF_1LB1RA") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm389: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_1LD1RC_1RB1LE_0LF0LA_---0LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm390: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_0RF1LD_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm391: halts_at_trans (TM_from_str "1RB---_0RC1LF_1RD1RC_0RE0LE_1LF0LA_0LB0RD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm392: halts_at_trans (TM_from_str "1RB1LF_0LC1LD_1LA0RD_1RE1RC_1LC1LE_0LB---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm393: halts_at_trans (TM_from_str "1RB0LE_0RC1RE_1LD1RC_0LA1LA_1LF0RE_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm394: halts_at_trans (TM_from_str "1RB1RC_1LC0LC_1RD0LB_1RE0RE_0RA0RF_0LD---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm395: halts_at_trans (TM_from_str "1RB0RC_1LA1RB_0RF1RD_1LE1RA_0LC0LE_0RB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm396: halts_at_trans (TM_from_str "1RB0RD_1LC---_0RE0RA_1RC0LE_1LF1RC_0LD1LF") c0 (B,1).
Proof. solve_halt 16. Time Qed.

Lemma tm397: halts_at_trans (TM_from_str "1RB0LC_1LC0RB_0LD1LB_1RD1LE_---0LF_0LA1RA") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm398: halts_at_trans (TM_from_str "1RB1RC_1RC1RF_0LD0LA_0RA1LE_1RF1LC_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm399: halts_at_trans (TM_from_str "1RB0LD_1RC1RE_1LA1RC_1RB1LD_1RF0RC_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm400: halts_at_trans (TM_from_str "1RB1RF_1RC0RD_1LD0RA_0LE0LC_0RB1LC_1RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm401: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0RD0RA_1LE0LF_1LA0LD_1LD---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm402: halts_at_trans (TM_from_str "1RB1RF_1LC1RC_1RE0LD_1LC0LD_0RA0LB_0RB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm403: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0RE0LD_1RE0LE_1LA1LF_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm404: halts_at_trans (TM_from_str "1RB0RF_1RC0LD_0RD0RE_1LE1RA_0LA0LE_0LD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm405: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_1LF1LD_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm406: halts_at_trans (TM_from_str "1RB0RF_1LC0LE_0LD1LD_1RE0LC_0RE1RA_1LC---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm407: halts_at_trans (TM_from_str "1RB0RA_1LC0LB_1RD0LB_1RE0LE_0RA0RF_1RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm408: halts_at_trans (TM_from_str "1RB1LF_0LC---_1LF1RD_1LE0RA_0RC1RE_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm409: halts_at_trans (TM_from_str "1RB0LC_0RC---_1RD0RE_1LE0RF_0LA0LE_1LF1RA") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm410: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_---1LD_0LE0LB_1LA1LF_1RB0LD") c0 (C,0).
Proof. solve_halt 5. Time Qed.

Lemma tm411: halts_at_trans (TM_from_str "1RB1RE_0RC0LC_1LD1RA_0LE0LD_0RF1LD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm412: halts_at_trans (TM_from_str "1RB0LE_1LC0RB_1LD1LA_0RA0LF_0RA---_0LC1LF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm413: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD1RB_1LE0LF_0LA1LC_0LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm414: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_1LD0RE_1RB0LA_0LD0RA_---0LD") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm415: halts_at_trans (TM_from_str "1RB0LC_0RC0RB_1LD1RB_0LA1LE_1LA0LF_0LC---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm416: halts_at_trans (TM_from_str "1RB1LE_0LC---_1LF0LD_0RE0RD_1LB0RC_1RD0LA") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm417: halts_at_trans (TM_from_str "1RB1RA_1RC1LD_1LB0RA_---1LE_1LB0LF_0RE1LF") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm418: halts_at_trans (TM_from_str "1RB1LE_1LC0RB_0RD0LD_1LA1RB_1RC1LF_1RD---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm419: halts_at_trans (TM_from_str "1RB---_0RC0RB_1LC1LD_0RE0LF_1RA0LE_1LB1LE") c0 (A,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm420: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD0RD_1RA1LB_1LF0RD_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm421: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_1LD0LC_1LE0LA_0RB---_1RA0RC") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm422: halts_at_trans (TM_from_str "1RB0LF_0RC0LA_1RD0RA_1LE0RB_0LB1LD_1LE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm423: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1LD1RF_1LF1RE_0RA1RD_---0LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm424: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_0LC1LA_1RE1LB_1RF---_1LA0RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm425: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD1LB_1RA1LF_0RC0RD_1LE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm426: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA1LD_1LF0RA_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm427: halts_at_trans (TM_from_str "1RB0LA_0RC---_1RD0LD_1LA0RE_1RF1RB_1RC1RD") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm428: halts_at_trans (TM_from_str "1RB0RB_1LC1RF_0RD0LB_1LE1RC_1RE0RA_0LC---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm429: halts_at_trans (TM_from_str "1RB0RA_1RC0LB_1LD0RD_---1LE_1LF1LB_1RA1RF") c0 (D,0).
Proof. solve_halt 7. Time Qed.

Lemma tm430: halts_at_trans (TM_from_str "1RB---_0RC1RB_1RD0RF_1RE1RA_1LC0LE_0LE1LF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm431: halts_at_trans (TM_from_str "1RB---_1LC0RF_1RD0LC_0RE1RB_0LB1RA_0RB1RC") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm432: halts_at_trans (TM_from_str "1RB0RD_1RC1RD_1LD---_1RA1LE_1RE0LF_0LB1LD") c0 (C,1).
Proof. solve_halt 2. Time Qed.

Lemma tm433: halts_at_trans (TM_from_str "1RB0LF_1RC1LC_1LD0RD_1RE1LD_---1RA_0RB1LA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm434: halts_at_trans (TM_from_str "1RB0LC_1RC0LC_0LD1RF_---1LE_0RE1LB_0RA1RA") c0 (D,0).
Proof. solve_halt 10. Time Qed.

Lemma tm435: halts_at_trans (TM_from_str "1RB1LC_1LA1RB_1LA0RD_1RE1RC_0LF0LB_---1LE") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm436: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LD_1LE1RB_0LF0LE_1LC1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm437: halts_at_trans (TM_from_str "1RB0LF_1LC0RC_1RD0LB_0RA0RE_0RA---_1LA0LF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm438: halts_at_trans (TM_from_str "1RB1LD_0RC0RF_1LC1RD_1RE0LA_---1RA_1LF1RA") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm439: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD1RE_0LA0LD_1RB0RF_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm440: halts_at_trans (TM_from_str "1RB1RF_1RC0LE_0LD1LC_1RF1LB_1RC---_0RA0RF") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm441: halts_at_trans (TM_from_str "1RB1LA_1RC1RE_1LD1RC_0LD0LA_1RF0RC_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm442: halts_at_trans (TM_from_str "1RB0LF_1RC1LF_1RD0RC_1LE0LF_---1LD_1RA1LB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm443: halts_at_trans (TM_from_str "1RB0LC_1LC0RE_0RD1LC_1LA0LD_1RA1RF_0RD---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm444: halts_at_trans (TM_from_str "1RB1LF_1RC---_1LD0RB_0RE1RD_1LF1RC_0LA0LF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm445: halts_at_trans (TM_from_str "1RB0LA_1LC0RD_1RA1LA_1RE1LA_1RC0RF_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm446: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_1LD0LE_1LE1LD_0LA0RA_0LE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm447: halts_at_trans (TM_from_str "1RB0LB_0LC0RC_1LE0RD_0RB1LF_1LF---_1LA1RC") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm448: halts_at_trans (TM_from_str "1RB0LF_1LC1RC_1RE0LD_1LB0RA_1RD0RE_0LA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm449: halts_at_trans (TM_from_str "1RB0RD_1RC1RF_0LA1LE_0LE---_1LC0RB_1RA0LA") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm450: halts_at_trans (TM_from_str "1RB1RD_1RC1LD_1LB---_1RA0RE_0RB0LF_1LE1LF") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm451: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_1RF1LD_1RD0LE_0RB1LC_---1RB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm452: halts_at_trans (TM_from_str "1RB0LE_1LC0RB_0RD0LD_1LA1RB_1RB0LF_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm453: halts_at_trans (TM_from_str "1RB1RE_1RC0RF_0LD---_0LE1LD_1RA0LB_0RE0LF") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm454: halts_at_trans (TM_from_str "1RB1LE_1LC0RB_0RD0LD_1LA1RB_0LD1LF_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm455: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_0LF0LD_1RE---_1RF0RE_1LA0RB") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm456: halts_at_trans (TM_from_str "1RB0RE_1LC0LF_1LD1LB_1RE---_0RA1RE_1LE0LA") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm457: halts_at_trans (TM_from_str "1RB0LF_1RC0LC_1LD0LE_0LA1LB_1LC0RF_0RD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm458: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_---0LD_1LE0LB_1RF0LA_1LD1RE") c0 (C,0).
Proof. solve_halt 16. Time Qed.

Lemma tm459: halts_at_trans (TM_from_str "1RB1LF_1LC0LD_1RE1LA_---0RE_1RA0RA_1LC0LB") c0 (D,0).
Proof. solve_halt 10. Time Qed.

Lemma tm460: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_0RC1LD_1LA1LC_---0RF_1LC1RB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm461: halts_at_trans (TM_from_str "1RB0LF_0RC1RD_0LD0RA_0RE1LC_1RC1RB_0LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm462: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA1RF_1RA1RF_0LA---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm463: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0RA_0RA0RF_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm464: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD1LC_1RA1LB_1LF0RD_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm465: halts_at_trans (TM_from_str "1RB0RA_1LC1RF_1RA1LD_0LE1LD_1LC0LC_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm466: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LC---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm467: halts_at_trans (TM_from_str "1RB0LC_1LC1RE_1RE0LD_1LA0LD_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm468: halts_at_trans (TM_from_str "1RB0LF_1LC1RF_0RE0LD_0LB0LD_0RA1LE_1RC---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm469: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA1LD_1LD0LF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm470: halts_at_trans (TM_from_str "1RB1RF_0RC0LD_1RD0RB_1LE0LD_0RA0LD_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm471: halts_at_trans (TM_from_str "1RB0RE_1LC0LB_1RD0LB_1RA0RD_1RF---_0RD1RE") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm472: halts_at_trans (TM_from_str "1RB---_0RC1RA_0LD0RE_1RE0LE_0RF0LC_1LC1RB") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm473: halts_at_trans (TM_from_str "1RB1LC_0LA1RB_1LA0RD_0LE1RC_1LF0RB_---0LE") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm474: halts_at_trans (TM_from_str "1RB---_1LC0RD_0LD1LB_1RE0LF_1RB0RE_1LC0LA") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm475: halts_at_trans (TM_from_str "1RB0LA_1RC---_1LD1RE_1LF0RC_0RC1RA_0RC0LD") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm476: halts_at_trans (TM_from_str "1RB1RE_0LC0RC_1RE1LD_1LB0LF_0RA0RE_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm477: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_0RD1LD_1LA0LC_0RF0LD_1LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm478: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RF---_0RF0RB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm479: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA1LD_1RD1LF_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm480: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1RD1LD_1LE1RD_1LE0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm481: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD1RD_1RE1LB_0RF---_1LF1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm482: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1LA_1RE0LD_1RF1LE_---0LC") c0 (F,0).
Proof. solve_halt 15. Time Qed.

Lemma tm483: halts_at_trans (TM_from_str "1RB0LF_0RC---_1RD0LA_1RE0RB_1LC1RD_0LE1LC") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm484: halts_at_trans (TM_from_str "1RB0LB_1LC0RB_0LF0LD_1LE1RB_1LA---_0RF1RB") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm485: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RF1LD_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm486: halts_at_trans (TM_from_str "1RB1LE_1RC---_0RD1RC_1LE1RF_0LA0LE_1LC0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm487: halts_at_trans (TM_from_str "1RB1RD_1LC0RA_1RA0LB_1RE0LC_1LD1RF_0RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm488: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1RA0LD_0RE1LF_1LB1RB_0LA---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm489: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD1LC_1RA1LB_0LF0RD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm490: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA1LD_1RD0LF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm491: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RE_0LC0LE_1LF0RB_0LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm492: halts_at_trans (TM_from_str "1RB1LF_0LC1LB_1RD1LA_0RE0RD_1RB1RD_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm493: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0RA---_1RF0LC_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm494: halts_at_trans (TM_from_str "1RB0LF_1LC1RA_---1LD_1RE0LA_0RC1RF_0RE1LA") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm495: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RE0RF_0RB0LB_1LE---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm496: halts_at_trans (TM_from_str "1RB1RF_1RC0LA_1LD1RB_1LE0LD_1RA0LB_0RA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm497: halts_at_trans (TM_from_str "1RB0RC_1LC0RE_1RA0LD_1RE0LF_1RA---_1LA0LC") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm498: halts_at_trans (TM_from_str "1RB1RD_0RC1RA_1LC1RD_1RE1LD_1RF0LE_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm499: halts_at_trans (TM_from_str "1RB1LF_1RC0RA_1LD0LC_0LE1LC_1LA1LB_0RB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm500: halts_at_trans (TM_from_str "1RB---_1RC0RD_1LD1LF_0RE0LE_1RA0LF_0LD1RB") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm501: halts_at_trans (TM_from_str "1RB1LC_0LC0RA_1RC1LD_0LE0RB_1LB0LF_1LE---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm502: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD0LE_0LE0LD_0RF1LD_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm503: halts_at_trans (TM_from_str "1RB0LD_1LC1RE_0LD0LC_1RE1RB_0RA0RF_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm504: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LD0RD_0LF0LE_1LB---_1LA0LF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm505: halts_at_trans (TM_from_str "1RB1LD_1LC0RB_0RE0RA_0LE0LF_1LA1RB_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm506: halts_at_trans (TM_from_str "1RB1LD_1RC1RF_1LA1LC_---0LE_1LA1LA_1LC1RB") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm507: halts_at_trans (TM_from_str "1RB---_1RC0RD_1LD1RE_0LF0LC_0LE0RA_0RB1LC") c0 (A,1).
Proof. solve_halt 16. Time Qed.

Lemma tm508: halts_at_trans (TM_from_str "1RB1RE_1LC0RF_0RE0LD_0LC1LC_1RA0LA_0RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm509: halts_at_trans (TM_from_str "1RB0RD_0LC1RA_0RA1LB_1RE1LB_1LF0RD_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm510: halts_at_trans (TM_from_str "1RB0LA_0RC0LD_0RD---_1RE1RC_0LF1RA_1RC1LE") c0 (C,1).
Proof. solve_halt 16. Time Qed.

Lemma tm511: halts_at_trans (TM_from_str "1RB1RF_1LC---_1RD0LC_0LE1LD_1RF1LC_0RA0RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm512: halts_at_trans (TM_from_str "1RB1LA_1LC0RC_1LD1RC_0RC1LE_0LF0LA_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm513: halts_at_trans (TM_from_str "1RB0RA_1RC0LE_0RD0LA_1RE0RE_1LB1RF_0LB---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm514: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE0LF_0LA1LE_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm515: halts_at_trans (TM_from_str "1RB---_0RC0RE_1RD0LA_1LE1LB_0RF0LE_0LD1RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm516: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_0LD0RA_1LE0RF_1RA0LE_0RB---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm517: halts_at_trans (TM_from_str "1RB0LA_0RC---_1RD1LC_0RE1RF_1LE0LC_0RA0LF") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm518: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_1LD0RA_0RB1LE_---1LD_0RC1LA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm519: halts_at_trans (TM_from_str "1RB---_0RC0RB_1LD1LA_0LE0LA_1LF0RC_0RC1LD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm520: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1RB1RD_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm521: halts_at_trans (TM_from_str "1RB0LE_1LC1RE_0LA0LD_1LA---_0RB1LF_0LA0RF") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm522: halts_at_trans (TM_from_str "1RB0RA_0RC1RF_1LD---_1LE1RD_1RD0LB_0LA0LF") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm523: halts_at_trans (TM_from_str "1RB0RE_1LC0RB_0LA0LD_1LA1LF_1RB1LB_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm524: halts_at_trans (TM_from_str "1RB0RD_0RC0LD_1LA1RA_0RE1LE_1RF0LE_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm525: halts_at_trans (TM_from_str "1RB0LB_1LC1RD_1LA0LC_0RB1RE_1RB0RF_0RA---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm526: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_0LF1RB_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm527: halts_at_trans (TM_from_str "1RB1LC_1LC0LE_1RD0LC_0LA0RA_1LB0RF_0RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm528: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LE---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm529: halts_at_trans (TM_from_str "1RB0LC_1LC1RE_1RE0LD_1LA0LD_0RA0RF_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm530: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0LF0LD_1LE---_0LB0LE_1LA1LD") c0 (D,1).
Proof. solve_halt 10. Time Qed.

Lemma tm531: halts_at_trans (TM_from_str "1RB0LD_1LC1RE_0LD0LC_1RE1RB_0RA1RF_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm532: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_0RC1LD_1RA0LE_---1LC_1LD1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm533: halts_at_trans (TM_from_str "1RB---_0RC0LB_1LD1RB_1RE1LC_0RA0RF_1LC0RD") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm534: halts_at_trans (TM_from_str "1RB1RA_1LC0RC_0RF0LD_0LE1LB_1RA1LE_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm535: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD1RC_1LE1RB_0LF0LE_0RA1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm536: halts_at_trans (TM_from_str "1RB1LE_1LC0RF_0RD1RC_1LE1RB_0LA0LE_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm537: halts_at_trans (TM_from_str "1RB1RD_1RC0LE_0RD0LD_1RE0RA_1LB1RF_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm538: halts_at_trans (TM_from_str "1RB1LE_1RC0RA_1LD1LD_1LA1LC_0RF0LD_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm539: halts_at_trans (TM_from_str "1RB---_0RC0LE_1LD1RF_1LB0RD_0LB0LA_1RD0RD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm540: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_1LD0LC_0LE0LA_0RF---_1RA0RC") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm541: halts_at_trans (TM_from_str "1RB0RE_1LC1RB_1RA0LD_1LB1LD_---0RF_1LA0RB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm542: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RE1LD_1RE0LF_0LE1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm543: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_1LE---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm544: halts_at_trans (TM_from_str "1RB0LE_0RC0RF_1RD0LA_1LE1RB_1LC0LE_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm545: halts_at_trans (TM_from_str "1RB1LE_1RC0RA_1LD0RD_1LA1LC_0RF0LD_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm546: halts_at_trans (TM_from_str "1RB0RE_1LC0RD_---1RD_0RC1LE_1RA1LF_0LE0LA") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm547: halts_at_trans (TM_from_str "1RB0LE_1RC0RD_1LD---_1RF1LA_1RC0LE_0RA1LD") c0 (C,1).
Proof. solve_halt 7. Time Qed.

Lemma tm548: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LA0LD_0LB---_1LA0RF_0LF1RD") c0 (D,1).
Proof. solve_halt 16. Time Qed.

Lemma tm549: halts_at_trans (TM_from_str "1RB1RA_1RC1LE_1LD1LA_---0LC_1LB0RF_1LC1RE") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm550: halts_at_trans (TM_from_str "1RB1RF_1RC0RD_1LD1LF_1RE1LD_---1RA_1RA0LC") c0 (E,0).
Proof. solve_halt 16. Time Qed.

Lemma tm551: halts_at_trans (TM_from_str "1RB---_1LC0LC_0LE1LD_1LB1RF_1RF0LA_0RD0RF") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm552: halts_at_trans (TM_from_str "1RB0LE_1RC0LA_0RD0LD_1RE1RF_1LC1LA_1RB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm553: halts_at_trans (TM_from_str "1RB0LD_1LC---_0RD1RC_1LE1RF_1LF0LE_1RC0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm554: halts_at_trans (TM_from_str "1RB---_1RC1RF_1LD1RE_1LB0LD_1RA0RC_0RE0LE") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm555: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA1LD_0LF0RE_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm556: halts_at_trans (TM_from_str "1RB0LB_1LC1LB_1RE0RD_1LA1RD_---1RF_0LB0RC") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm557: halts_at_trans (TM_from_str "1RB1LB_0RC0LA_1RD0LA_0LE0RF_---1LC_1LD1RE") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm558: halts_at_trans (TM_from_str "1RB1LD_1RC1RE_1LA1RB_0LC0LA_1RF---_0LA0RA") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm559: halts_at_trans (TM_from_str "1RB---_0LC1LB_1LF0LD_0RE1RD_1RC0RE_1LE1LA") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm560: halts_at_trans (TM_from_str "1RB1RA_0RC1LD_1RD1RA_1LB1RE_1RF0LE_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm561: halts_at_trans (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RA0LE_0LF1LD_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm562: halts_at_trans (TM_from_str "1RB0LB_1RC1LB_1RD0RE_1LA0RF_0LC1RE_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm563: halts_at_trans (TM_from_str "1RB0LC_1RC1LE_1LD0RE_0LA1LD_0RA1RF_---1RA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm564: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD0LB_0RA1RE_1RD0RC_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm565: halts_at_trans (TM_from_str "1RB1LB_1RC0LC_1LD0RF_---1LE_1RE1LA_0LA1RC") c0 (D,0).
Proof. solve_halt 16. Time Qed.

Lemma tm566: halts_at_trans (TM_from_str "1RB0RD_0RC1RF_1LD---_0LE1LC_1LA0RC_0RB0RF") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm567: halts_at_trans (TM_from_str "1RB0LF_0LC0RE_1LD1RC_1LA0LE_0RB0RA_1LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm568: halts_at_trans (TM_from_str "1RB1LB_1LC0RB_0LA1LD_0LE1LF_0RA0LF_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm569: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1RD---_0LA1RE_1RF0LD_1LB0RD") c0 (C,1).
Proof. solve_halt 18. Time Qed.

Lemma tm570: halts_at_trans (TM_from_str "1RB---_1RC1LE_0RD1RC_1LE0RF_0LB0LE_1LB0RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm571: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_1LD0LB_1RE0LB_---1RF_1RC1RD") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm572: halts_at_trans (TM_from_str "1RB1RF_1LC1LF_1RE1RD_1LB1LD_---0RC_1RA0LB") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm573: halts_at_trans (TM_from_str "1RB1RE_1RC---_1LD0RD_1RE0LD_0RF0RA_0LF1LD") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm574: halts_at_trans (TM_from_str "1RB0RF_1LC0LD_1LA1LB_---1LE_1RF1LE_1RB1RA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm575: halts_at_trans (TM_from_str "1RB0RA_1LC0LD_1RD1LD_0LB0RE_1RA1LF_0LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm576: halts_at_trans (TM_from_str "1RB1LE_0LC1RD_---1LD_1LA0RD_1LD0LF_0LA1LC") c0 (C,0).
Proof. solve_halt 7. Time Qed.

Lemma tm577: halts_at_trans (TM_from_str "1RB---_1LC0RF_1LE1LD_1LC0LB_1LA1RD_1RB1RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm578: halts_at_trans (TM_from_str "1RB1RE_0RC1LD_0LD---_1LE0LB_1RA0RF_1LB1RF") c0 (C,1).
Proof. solve_halt 18. Time Qed.

Lemma tm579: halts_at_trans (TM_from_str "1RB1LF_1LC0RE_1LA1LD_0LB0RB_1LB1RB_1LD---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm580: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_1RF1LD_1RA0LE_0RB1LC_---1RB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm581: halts_at_trans (TM_from_str "1RB1LD_1LC1RF_1LD1LB_1RE0LB_---0RA_0LF0LE") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm582: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1RD1RB_1RE0LF_0LA1LE_1RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm583: halts_at_trans (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0LA_1RC1LF_0LC1LD") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm584: halts_at_trans (TM_from_str "1RB1RF_1LC1LF_1RD0LB_---1RE_1LA1RD_1LB0RA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm585: halts_at_trans (TM_from_str "1RB1RF_1LC1RD_1LA0LC_0RE---_1RC0RF_1RE1RB") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm586: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1LE0LF_0LA1LE_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm587: halts_at_trans (TM_from_str "1RB1LB_1RC1RE_1LD1RA_0LE0LD_1RF0RC_1RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm588: halts_at_trans (TM_from_str "1RB0RE_1LC0RF_---1LD_0LE0LA_1RA1LD_0RC1LE") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm589: halts_at_trans (TM_from_str "1RB0LD_0LC1LB_1RC1LA_0LF1RE_0RD0RE_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm590: halts_at_trans (TM_from_str "1RB0LE_0RC---_1RD0LA_1LA1RF_1LC0LE_0RC0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm591: halts_at_trans (TM_from_str "1RB0LC_1LC1RF_1RD1LC_1RA0RE_1LA1RE_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm592: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0LD1LC_1LE1LF_1RB1LB_0LE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm593: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_---1LD_1LE1LC_1RA0LF_0RA1LE") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm594: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RC1RF_---0RD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm595: halts_at_trans (TM_from_str "1RB---_1RC1RF_1LD0LC_1RE1LC_0RF1RE_1RA0RC") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm596: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA0LC_0RA0RF_1RD0LC_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm597: halts_at_trans (TM_from_str "1RB---_1LC0LF_0LD1LC_1RE1LB_1RB0RE_0LA0RD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm598: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC0LF_---0LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm599: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1RB_0LE---_0LA1LE_1LE0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm600: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1LE1LF_0LA0RA_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm601: halts_at_trans (TM_from_str "1RB0RE_1RC0RF_1LD0LA_1LE0LD_1RA0LD_0RD---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm602: halts_at_trans (TM_from_str "1RB0LE_0RC0RD_1RD0LA_1LE0LF_1LC0LE_---1RA") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm603: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD0RD_1RA1LB_0LF0RD_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm604: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RA1LD_0RE0LE_---1LC_0LF1RA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm605: halts_at_trans (TM_from_str "1RB0LE_1LB1RC_---1RD_1LA0RF_1RB1LF_0LA0RE") c0 (C,0).
Proof. solve_halt 6. Time Qed.

Lemma tm606: halts_at_trans (TM_from_str "1RB0LE_1LC0LD_1RD1LA_1LF1RA_---0RC_0LB1LD") c0 (E,0).
Proof. solve_halt 14. Time Qed.

Lemma tm607: halts_at_trans (TM_from_str "1RB1LA_0RC0RD_1LC0LA_0RE0RC_---1RF_1LD0RE") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm608: halts_at_trans (TM_from_str "1RB1LB_1LC0RF_0RC0LD_1LE---_1LA0LB_1RB0RF") c0 (D,1).
Proof. solve_halt 8. Time Qed.

Lemma tm609: halts_at_trans (TM_from_str "1RB1LA_0LC0RB_0RA1LD_0LE0LF_1LC0RF_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm610: halts_at_trans (TM_from_str "1RB1LD_0RC1RF_1LD---_0LE1LC_1LA0RC_0RB0RF") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm611: halts_at_trans (TM_from_str "1RB1LD_1LC0RE_1RA1LD_1LB1LA_1LF1RE_---0LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm612: halts_at_trans (TM_from_str "1RB0LF_1LC1LD_1LA0LB_0LE0RD_1RA0LB_1RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm613: halts_at_trans (TM_from_str "1RB1RE_0LC---_0LD1LC_1RE0LF_0RA0RE_1RA0LB") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm614: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA0LE_1LA1RF_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm615: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_1LA1LD_0RD1LC_---0RF_1LD1RB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm616: halts_at_trans (TM_from_str "1RB1LE_1LC---_0RD1RC_1LE1RF_0LA0LE_1LC0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm617: halts_at_trans (TM_from_str "1RB0LD_0RC1RE_1RD0RF_1LA0LD_0RF---_0RA0LB") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm618: halts_at_trans (TM_from_str "1RB1RE_0RC1LE_1RD0LF_0LB0RD_1LB1LC_0LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm619: halts_at_trans (TM_from_str "1RB0LF_0RC0LC_1RD1RE_1LB1LF_1RA---_1RA0LD") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm620: halts_at_trans (TM_from_str "1RB0RF_1LC1RB_1RA0LD_0RE1LD_0LC1LB_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm621: halts_at_trans (TM_from_str "1RB---_0RC0RB_1RD0LF_0RE0RA_1RF0LA_1LC0LF") c0 (A,1).
Proof. solve_halt 10. Time Qed.

Lemma tm622: halts_at_trans (TM_from_str "1RB0RC_1LC0LD_---1LD_1LE0LD_1RF1RE_1RA0RF") c0 (C,0).
Proof. solve_halt 6. Time Qed.

Lemma tm623: halts_at_trans (TM_from_str "1RB1LD_0LC0RC_1LE0RD_0RB1LF_1LF---_1LA0LB") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm624: halts_at_trans (TM_from_str "1RB1RA_1LC0RB_1RD0LD_1LE0LA_0LF1LC_0LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm625: halts_at_trans (TM_from_str "1RB1RA_1RC0LB_0RD1LB_0RE1RF_1LE0LA_---0RA") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm626: halts_at_trans (TM_from_str "1RB0RC_0LC1RA_---1RD_1LE1RD_1LA1LF_1LA0LE") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm627: halts_at_trans (TM_from_str "1RB1RD_1RC0RA_1LA0RF_0RE0LD_1LC0RA_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm628: halts_at_trans (TM_from_str "1RB1RD_1LC1RF_0RA1LB_---0RE_1RE0RF_1RC0LC") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm629: halts_at_trans (TM_from_str "1RB1LD_1RC0RD_0LD1RA_0RE1LE_1RF0LA_---0LA") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm630: halts_at_trans (TM_from_str "1RB0LC_1LC1RD_1LA0LC_1LE0RD_0LF1RE_---0RA") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm631: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD---_1LE1LA_1RF1LD_1RA1RB") c0 (C,1).
Proof. solve_halt 10. Time Qed.

Lemma tm632: halts_at_trans (TM_from_str "1RB1RF_0LC---_1RD0LC_0LE1LD_1RF1LC_0RA0RF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm633: halts_at_trans (TM_from_str "1RB0RA_0RC0RE_0LD---_1LE0LA_1LF0LD_1RA1LE") c0 (C,1).
Proof. solve_halt 13. Time Qed.

Lemma tm634: halts_at_trans (TM_from_str "1RB0RD_0RC0LB_1LD---_1RE1LE_1LB0RF_1LF1RA") c0 (C,1).
Proof. solve_halt 4. Time Qed.

Lemma tm635: halts_at_trans (TM_from_str "1RB0RE_0LC1RF_0LE0LD_1RA1LD_1LC1RE_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm636: halts_at_trans (TM_from_str "1RB1LB_1RC0LB_1LD0RD_1RE1LB_1RA1RF_---0LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm637: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_1RA1LD_0LE---_1LF0RB_0LB1LE") c0 (D,1).
Proof. solve_halt 7. Time Qed.

Lemma tm638: halts_at_trans (TM_from_str "1RB1RE_0LC1LB_1RE1LD_1RB0LF_0RA0RE_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm639: halts_at_trans (TM_from_str "1RB1LE_1RC1RA_0RD0RC_1RE0RF_1LA0LE_---0RB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm640: halts_at_trans (TM_from_str "1RB0RE_1RC0LB_0RD---_1LD1RA_1RF1LF_1LB0RD") c0 (C,1).
Proof. solve_halt 4. Time Qed.

Lemma tm641: halts_at_trans (TM_from_str "1RB---_1LC0LE_1LA1RD_1RF1LE_1LB0RD_1RE1RB") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm642: halts_at_trans (TM_from_str "1RB0LC_1LC1RE_1RF0LD_1LA0LD_0RA0RC_0LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm643: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LA1LD_1LA0LC_0LF1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm644: halts_at_trans (TM_from_str "1RB0RD_1LC0LB_1RE1RD_1RA1RE_1LB1RF_0RA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm645: halts_at_trans (TM_from_str "1RB1RD_0RC1LE_1LD1RC_1RB0LF_---1LF_0LE0LA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm646: halts_at_trans (TM_from_str "1RB1LD_1RC0LB_0LA0RE_1LB0LB_0RC0RF_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm647: halts_at_trans (TM_from_str "1RB0LD_1LC1RE_1LA1RC_1RB1LD_1RF0RC_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm648: halts_at_trans (TM_from_str "1RB0LB_1RC1LB_0RD0RD_1LE1RD_0LF1LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm649: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1RF1RD_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm650: halts_at_trans (TM_from_str "1RB1RC_1LA1RA_1LD0RC_1LE0RF_0LD1LA_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm651: halts_at_trans (TM_from_str "1RB0LC_0RC0RA_1LD0RE_1LA0LD_1RC1RF_0RA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm652: halts_at_trans (TM_from_str "1RB0LA_1LC0RC_1RD1LA_1RE1RF_1RA1LA_---0LB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm653: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1LB0LA_0RF0RE_1LD1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm654: halts_at_trans (TM_from_str "1RB0RE_0LC1LF_1LE0LD_1LB---_1RF0LF_1LC0RA") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm655: halts_at_trans (TM_from_str "1RB0LE_0RC1RB_0LD1RF_1LA1LF_1LD---_1LD0RC") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm656: halts_at_trans (TM_from_str "1RB1RD_0LC0RC_1LE0RD_0RB1LF_1LF---_1LA0LB") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm657: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_1RD0LD_1LE0RB_0LE0LA_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm658: halts_at_trans (TM_from_str "1RB0RA_1LC0LF_1RA1LD_1LE---_1RE1LB_1LB0RC") c0 (D,1).
Proof. solve_halt 10. Time Qed.

Lemma tm659: halts_at_trans (TM_from_str "1RB0RD_1LB1RC_0LD1LC_1RE0LC_0RF---_0RA1RF") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm660: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_1LE0LD_0RC0RB_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm661: halts_at_trans (TM_from_str "1RB0LA_1LC1RD_1RA1LA_1LE1RD_1RC0RF_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm662: halts_at_trans (TM_from_str "1RB0RE_0RC0LB_1LD1RC_1LB0RE_---1RF_1RA0RE") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm663: halts_at_trans (TM_from_str "1RB1RE_0RC---_1LD0LE_1RC0RA_1LF1RD_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm664: halts_at_trans (TM_from_str "1RB1RF_1LC0LA_1LD0LB_1LE0RD_1RA---_1RB0RD") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm665: halts_at_trans (TM_from_str "1RB0RF_1RC0RD_1LD0RA_0LE0LC_0RB1LC_0RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm666: halts_at_trans (TM_from_str "1RB0RC_0RC1RA_1RD0LF_1RE---_1LC1RA_0LC1LF") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm667: halts_at_trans (TM_from_str "1RB1RA_1LC0RF_0RE0LD_1RC1LC_---1LA_1LB1RE") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm668: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_0RF1LD_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm669: halts_at_trans (TM_from_str "1RB0RF_0RC1LE_1LC0LD_1RA1LD_1LC1RE_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm670: halts_at_trans (TM_from_str "1RB---_1LC0RF_1LD0LB_1LE1LA_1RC0LD_1RB0RF") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm671: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LE1LD_1LB---_0LF1RE_1LA0LE") c0 (D,1).
Proof. solve_halt 12. Time Qed.

Lemma tm672: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1RB_0LE---_0LA1LE_1RE0LC") c0 (D,1).
Proof. solve_halt 15. Time Qed.

Lemma tm673: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA1RE_1LB0RF_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm674: halts_at_trans (TM_from_str "1RB0RD_1LC0LF_1LD1LB_0LE1RA_0RA---_1RD1LF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm675: halts_at_trans (TM_from_str "1RB0RE_1LC0LD_1LA1LB_1RE1LD_0LF1RA_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm676: halts_at_trans (TM_from_str "1RB1RD_0RC---_0RD1RD_1LE0RF_0LA0LE_0LF1RA") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm677: halts_at_trans (TM_from_str "1RB0RF_0RC0LE_0LD1LA_1LE1LD_0LA0RA_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm678: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RF0LD_0RE1LC_1LB1RB_---1RA") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm679: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_0LD0RA_1LA1LE_1LD0LE_1RC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm680: halts_at_trans (TM_from_str "1RB0LD_1RC1LE_1LA1RF_0RC0LC_---0LA_0RB1RA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm681: halts_at_trans (TM_from_str "1RB1LF_1LC1RB_1RE1LD_1LB0LC_1LA0RE_0LB---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm682: halts_at_trans (TM_from_str "1RB1RE_0LC0RA_---1LD_1LE1LC_1RA0LF_0RA1LE") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm683: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LA1LD_1LA1LF_0RB1RB_0RB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm684: halts_at_trans (TM_from_str "1RB---_1LC0RC_1RD0LC_0RE0RF_0LE1LC_1RA1LC") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm685: halts_at_trans (TM_from_str "1RB0RC_1LC1RF_1RA0LD_1RC0LE_1LA0LC_0LA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm686: halts_at_trans (TM_from_str "1RB1RE_1LC0RF_---1LD_1LE0LD_1RF1RC_0RA1RF") c0 (C,0).
Proof. solve_halt 12. Time Qed.

Lemma tm687: halts_at_trans (TM_from_str "1RB0RA_0LC1RA_1RA1LD_1LE1LD_1RE0LF_---1LB") c0 (F,0).
Proof. solve_halt 7. Time Qed.

Lemma tm688: halts_at_trans (TM_from_str "1RB0LF_1RC---_1RD0RE_1LE0RB_1RC0LA_1LC0LE") c0 (B,1).
Proof. solve_halt 2. Time Qed.

Lemma tm689: halts_at_trans (TM_from_str "1RB0LA_1LC1RA_1LB0LD_1RE0RC_1RF---_0RC0RD") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm690: halts_at_trans (TM_from_str "1RB0RC_1LC1RF_1LD1RC_1LD0LE_1RA1LE_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm691: halts_at_trans (TM_from_str "1RB1RA_1RC0LE_1LD1RF_0RB1RE_1LA1LB_0RD---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm692: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_0RD0LD_1LE1RB_1RB0LA_1RD---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm693: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_0LF1RD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm694: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_0RD0LD_1LE1RB_1RB0RA_0LA---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm695: halts_at_trans (TM_from_str "1RB---_1LC0RE_1RA0LD_1LA1LF_0RF1RC_0LC1RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm696: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LD0LB_1LE1LF_1RC0LD_1RA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm697: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LD0LF_1LE1RD_1LC0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm698: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_1LA1LD_1RA1LC_0RD0RF_---1RB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm699: halts_at_trans (TM_from_str "1RB0RE_1LC---_0LD1LD_1RA0LA_0LC1RF_1RD0RA") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm700: halts_at_trans (TM_from_str "1RB1LE_1LC1RC_1RF1RD_1RE0RD_1LA0LE_1RB---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm701: halts_at_trans (TM_from_str "1RB0LA_0RC---_1RD1RE_1LA1LD_1RF1RA_1LA0RE") c0 (B,1).
Proof. solve_halt 14. Time Qed.

Lemma tm702: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_1RA1LD_0LB1LF_1LB0RB_1LE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm703: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_1RF1LD_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm704: halts_at_trans (TM_from_str "1RB0LE_1RC1LA_0LD0RA_1RF1LB_1LC---_0RF0RC") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm705: halts_at_trans (TM_from_str "1RB1LF_1RC0RE_1RD1RA_1LE1RC_0RF1LE_---0LA") c0 (F,0).
Proof. solve_halt 12. Time Qed.

Lemma tm706: halts_at_trans (TM_from_str "1RB---_1LC0LF_1RD0LD_1RE0RD_1LB0RC_1LE0LA") c0 (A,1).
Proof. solve_halt 10. Time Qed.

Lemma tm707: halts_at_trans (TM_from_str "1RB---_1LC1RF_0LE1LD_1LC0LB_1LA0LA_0RB0RF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm708: halts_at_trans (TM_from_str "1RB0RD_0LC---_1RE1LD_1LC0LF_1RA0RE_1LD0LE") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm709: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1LB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm710: halts_at_trans (TM_from_str "1RB1RC_1RC0LD_1RD0RA_1LE1LB_0LA0LF_---0LA") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm711: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD0LB_1RE1LE_0RF---_1LF1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm713: halts_at_trans (TM_from_str "1RB---_1LC1LD_1LA0LB_1LB1RE_1RF0RD_---0RC") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm714: halts_at_trans (TM_from_str "1RB1LE_1LC---_0RD1RC_1LE1RF_0LA0LE_1RC0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm715: halts_at_trans (TM_from_str "1RB0LC_1LA1RF_1RC0RD_1LE1RD_1LA0LA_---0RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm716: halts_at_trans (TM_from_str "1RB0RD_0LC0RF_0LA1LD_1LE1RD_1LA0LC_---0RA") c0 (F,0).
Proof. solve_halt 12. Time Qed.

Lemma tm717: halts_at_trans (TM_from_str "1RB1LC_1LA0RE_0LD---_0LB1LE_1RF1RB_1LB1LF") c0 (C,1).
Proof. solve_halt 8. Time Qed.

Lemma tm718: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1LD1RC_0RE0LB_0RF0RA_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm719: halts_at_trans (TM_from_str "1RB0RF_1RC1LC_1RD0LC_1LB1RE_1LA1RE_---1RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm720: halts_at_trans (TM_from_str "1RB1LA_1RC1RD_1LA0LA_1RF0RE_1LC1RE_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm721: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LC_1LC1RD") c0 (A,1).
Proof. solve_halt 12. Time Qed.

Lemma tm722: halts_at_trans (TM_from_str "1RB---_0LC0LE_1RF1LD_1LE0LA_0LC0RC_1RB0RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm723: halts_at_trans (TM_from_str "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_1RE---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm724: halts_at_trans (TM_from_str "1RB1LC_0LB1RC_1RD0LF_1LE0RA_---0LA_1LE1LD") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm725: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_0LD0RD_1LA1LE_0LC0LF_0RC---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm726: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD1RB_0LA1LD_0RF0LF_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm727: halts_at_trans (TM_from_str "1RB0LA_1LC0RC_1RC0LD_1LE0RA_1LA1LF_0LE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm728: halts_at_trans (TM_from_str "1RB0RE_0RC0RE_1LD1RF_0LA0LD_1LC1RA_---0RB") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm729: halts_at_trans (TM_from_str "1RB1RE_1RC0LF_1RD0RD_1LE0LA_0LC1LB_---1LE") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm730: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_1RB1LD_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm731: halts_at_trans (TM_from_str "1RB0RC_1LC0RE_1RA1LD_0LC0LA_1RF1LC_---1LA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm732: halts_at_trans (TM_from_str "1RB0LB_1LC1RA_---0LD_1LA1LE_1LD0RF_0LB1RE") c0 (C,0).
Proof. solve_halt 16. Time Qed.

Lemma tm733: halts_at_trans (TM_from_str "1RB0LE_1LC0RE_0LD1LC_1LA1LF_1RB0RE_0LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm734: halts_at_trans (TM_from_str "1RB0RA_1LC0RF_1RA1LD_0LE1LD_1LC0LC_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm735: halts_at_trans (TM_from_str "1RB---_0LC1RE_1RD1LC_1RA0RE_1RF0LB_1LD0RB") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm736: halts_at_trans (TM_from_str "1RB0RC_1RC0LD_1RD1RB_1LE1LF_---1LD_1LC1RA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm737: halts_at_trans (TM_from_str "1RB1LA_1LB0RC_1LD1RC_1LE0LA_---0LF_1RC1LC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm738: halts_at_trans (TM_from_str "1RB---_1RC0RF_1RD1RB_1RE0RA_1LF1LE_1RC0LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm739: halts_at_trans (TM_from_str "1RB0LE_0LC1LB_1RF0RD_0LE1RF_1LA---_0RD0RF") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm740: halts_at_trans (TM_from_str "1RB0RA_0RC1RA_1LC0LD_0LE1LF_1LA1LB_---1LD") c0 (F,0).
Proof. solve_halt 11. Time Qed.

Lemma tm741: halts_at_trans (TM_from_str "1RB1RE_1LC1LE_1RF1RD_1RB1LD_1RA0LB_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm742: halts_at_trans (TM_from_str "1RB1LD_1RC---_0LA0RC_1LC0LE_0LF1LE_1LD1LA") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm743: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_1LD0RD_1RE1LD_---0LB_1LD1LA") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm744: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_0LC1LA_1RE1LA_1RF---_1LA0RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm745: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_1LD1RC_1RB1LE_1LF0LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm746: halts_at_trans (TM_from_str "1RB1LC_1LA1RE_1LD0LB_0LE---_1RF0RE_1LC1LB") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm747: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD0RD_1RA1LB_1LF0RD_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm748: halts_at_trans (TM_from_str "1RB1RE_0LC1RF_---1LD_0RA1LD_1RA1LF_0RC0LE") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm749: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA0RE_1LA1RF_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm750: halts_at_trans (TM_from_str "1RB1LC_1LA1RE_1RD1LA_---0LC_0RA1RF_1RC0RB") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm751: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_1RD0RC_1LE0RA_---1LF_0LD0LA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm752: halts_at_trans (TM_from_str "1RB0LC_0RC1RA_0LD0RE_1LA0LE_1LC0RF_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm753: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RD1LB_0RF1LE_0RA0LC_1RB1RD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm754: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RA_0LE0LB_1LC0LF_0RB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm755: halts_at_trans (TM_from_str "1RB0LE_0RC1RE_1RD1RF_1LE1LA_1RB0LD_0RD---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm756: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1LD1LC_1RB1RA_---0RF_1LC1RB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm757: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0RD1RB_0LE---_1RF0LE_0LA1LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm758: halts_at_trans (TM_from_str "1RB1RF_0LC0RD_0LD1LC_0RE0LD_1LF---_1RA0RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm759: halts_at_trans (TM_from_str "1RB0LB_1LC1RD_1LA0LC_0RE0RC_1RA1RF_1LD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm760: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1LB0LA_0RF0RE_1LA1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm761: halts_at_trans (TM_from_str "1RB---_0RC1RE_1LD0RB_0LE0LD_1RF1LD_1RB1RA") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm762: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_---0LD_0RE1LB_0LF1RA_1LD1LE") c0 (C,0).
Proof. solve_halt 4. Time Qed.

Lemma tm763: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LC_1LC0LF") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm764: halts_at_trans (TM_from_str "1RB1RC_0LC1RA_1LF0RD_1RE---_1LF1RA_0RB0LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm765: halts_at_trans (TM_from_str "1RB1RA_1LC1RD_0LE1RD_1LF0RB_---0LD_1RA1LD") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm766: halts_at_trans (TM_from_str "1RB0RA_0LC0LE_1RA1LD_1LE0LF_0LC0RC_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm767: halts_at_trans (TM_from_str "1RB0RC_1LC1LD_1RF0RD_1LE1LD_1RA0LE_1RA---") c0 (F,1).
Proof. solve_halt 7. Time Qed.

Lemma tm768: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_1LA1LD_1RA1LC_1RA0RF_---1RB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm769: halts_at_trans (TM_from_str "1RB0LD_0RC1RE_1RD0RF_1LA0LD_0RF---_0RA1RD") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm770: halts_at_trans (TM_from_str "1RB0RD_1LC1RB_1RD0LB_0RF1RE_1RE0RA_---1LB") c0 (F,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm771: halts_at_trans (TM_from_str "1RB0LD_1LC0LE_1LA1RC_1RE0RC_1RF1LE_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm772: halts_at_trans (TM_from_str "1RB0RC_1LC0RF_1RA1RD_0RE0LD_1LB0RC_0RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm773: halts_at_trans (TM_from_str "1RB---_1LC0RD_1RA1LD_1LE1RB_0LF0LC_1RF1LB") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm774: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_0RA1LB_1RC1RD_1RF0LE_0RD---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm775: halts_at_trans (TM_from_str "1RB0RA_1LC0LC_0RE0RD_1RA1LB_0LE1LF_0LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm776: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0LD1RB_1LE---_1LF0LD_0LA0RA") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm777: halts_at_trans (TM_from_str "1RB0LE_0LC1LB_1RD1LA_0RE0RD_0LF1RD_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm778: halts_at_trans (TM_from_str "1RB0LF_1LC1LA_1RD1LB_0LC0RE_0RC0RD_0LA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm779: halts_at_trans (TM_from_str "1RB0LC_1RC1RD_1LA0LC_0RE1RF_0RF---_0RA1LC") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm780: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RA1LD_1RB0LF_1LB1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm781: halts_at_trans (TM_from_str "1RB0RD_1LC1RE_1LA0LD_0RC0LB_0RB1RF_1RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm782: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA1LD_1LC0RB_1LF---_0LC0LB") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm783: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_0LD---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm784: halts_at_trans (TM_from_str "1RB0LB_1LC0LA_1RD0LB_0RE0RD_1RF1RC_1LB---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm785: halts_at_trans (TM_from_str "1RB0LA_1RC1RE_0RD---_1LE1RF_1LA1RB_1RD0RF") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm786: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_0LA1LD_0LE1LB_1RA0LC_---0LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm787: halts_at_trans (TM_from_str "1RB1LD_0RC0LE_0LD0RF_1RE---_1LF0LE_0LA1LB") c0 (D,1).
Proof. solve_halt 10. Time Qed.

Lemma tm788: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_1LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm789: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1LB1RD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm790: halts_at_trans (TM_from_str "1RB1RE_0LC1LE_1LB1RD_0LB---_1RA1RF_1LC0RF") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm791: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA1RF_1RA0RB_0RB---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm792: halts_at_trans (TM_from_str "1RB1LB_1LC1RB_1LF0LD_1RE1LD_1LE0RB_---0LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm793: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_1RE0LD_1LE---_1LA1RE_1LE0LA") c0 (D,1).
Proof. solve_halt 14. Time Qed.

Lemma tm794: halts_at_trans (TM_from_str "1RB1RC_1RC0LC_1LD0RF_1RE0LD_0RB---_1RA1RE") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm795: halts_at_trans (TM_from_str "1RB1RE_1RC0LB_0RD---_1LD1RE_0RF1LF_1RA0LB") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm796: halts_at_trans (TM_from_str "1RB1LA_0RC1LD_1LA1RF_---1LE_1RC0LB_1RA1RC") c0 (D,0).
Proof. solve_halt 4. Time Qed.

Lemma tm797: halts_at_trans (TM_from_str "1RB1RC_0LC0RF_1LE0RD_0LC---_1RA0LE_0RA1RF") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm798: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_1RD0LC_0LA0RA_1LF0RF_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm799: halts_at_trans (TM_from_str "1RB0RA_1LC1RA_---0RD_1LB1LE_0LF0LE_1LA1LD") c0 (C,0).
Proof. solve_halt 3. Time Qed.

Lemma tm800: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE0LF_0LA0RA_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm801: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA0RA_0LF0RA_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm802: halts_at_trans (TM_from_str "1RB0LC_1LC1RB_1RD1LA_0RE---_0RB1RF_1LC0RA") c0 (D,1).
Proof. solve_halt 8. Time Qed.

Lemma tm803: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_0RD0LC_0LB1RE_1RD---_0RA0RF") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm804: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_0RD1RE_1LE0RF_1LB0RB_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm805: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1LD1RA_---0LA_0LA0RF_0RA0RC") c0 (D,0).
Proof. solve_halt 10. Time Qed.

Lemma tm806: halts_at_trans (TM_from_str "1RB1RC_1LC0LB_1RD0LB_1RE0RC_0RA0RF_0RA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm807: halts_at_trans (TM_from_str "1RB0RF_0LC0RC_1RE1LD_1LB0LB_0RA0RE_---1LC") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm808: halts_at_trans (TM_from_str "1RB1LC_1LC1RF_1LA0RD_0LD1LE_0LB---_0RB0RC") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm809: halts_at_trans (TM_from_str "1RB1LD_1RC0RD_0LD1RA_0RF1LE_1RE0LA_---0LA") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm810: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LA_1RC1RF_0LC---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm811: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---0LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm812: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD0RE_0LA0LD_1LA0RF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm813: halts_at_trans (TM_from_str "1RB0LB_1RC1LB_0RD0RD_1RE1RD_1LF0LA_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm814: halts_at_trans (TM_from_str "1RB---_1LC0LA_0LE1LD_1LC0RE_1RF0LB_1RD0RF") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm815: halts_at_trans (TM_from_str "1RB1LF_0LC1LB_0LD1LA_1RD0RE_1LA0RE_---1LC") c0 (F,0).
Proof. solve_halt 11. Time Qed.

Lemma tm816: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE1LF_0LB0LF_0LB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm817: halts_at_trans (TM_from_str "1RB1LB_0RC0LA_1RD0LA_1LE0RF_---1LA_1LD1RE") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm818: halts_at_trans (TM_from_str "1RB0LE_1LC0RB_0RD0LD_1LA1RB_1RB1LF_0LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm819: halts_at_trans (TM_from_str "1RB0LF_1LC0RC_0RF0LD_0LE1LB_1RA1LE_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm820: halts_at_trans (TM_from_str "1RB---_0RC0LE_0RD1RF_1RE0RF_1LB0LE_1RC0RA") c0 (A,1).
Proof. solve_halt 7. Time Qed.

Lemma tm821: halts_at_trans (TM_from_str "1RB1LD_0RC0RE_1LC1RD_1RE0LA_1LF1RA_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm822: halts_at_trans (TM_from_str "1RB---_1LC0RA_0RD1RC_1LE0LF_0LF0LE_0RA1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm823: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB") c0 (D,1).
Proof. solve_halt 10. Time Qed.

Lemma tm824: halts_at_trans (TM_from_str "1RB1RC_0RC1RA_1LD0RC_1LE---_0LF1LA_1LE1LA") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm825: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD0LA_1RE0RC_1LB0RA_0LB0LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm826: halts_at_trans (TM_from_str "1RB---_0RC0LE_1RD1RA_1LB1RC_1RF1LF_1RB0LF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm827: halts_at_trans (TM_from_str "1RB0LB_1RC0LB_0RD---_1LD1RE_0RF1LB_1RA0LB") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm828: halts_at_trans (TM_from_str "1RB0LC_0LC0LD_---1LA_1RD0RE_1LF1RE_0LD0LB") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm829: halts_at_trans (TM_from_str "1RB0LB_1RC0RA_1LD1RE_1LB0LD_0RB1RF_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm830: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RE0LD_1LB1LF_0RE0RA_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm831: halts_at_trans (TM_from_str "1RB0RC_0RC1RA_1LD1RF_0LE0LD_1RA1LD_1RE---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm832: halts_at_trans (TM_from_str "1RB0RD_1RC0LC_1LD0RF_1RE0LD_0RB0RD_1RA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm833: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_0LA0LD_1RE0LE_1LF0RB_---1LA") c0 (F,0).
Proof. solve_halt 12. Time Qed.

Lemma tm834: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LE1LD_1LB---_0LF0RF_1LA0LE") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm835: halts_at_trans (TM_from_str "1RB---_0RC0LF_1LD0RB_0LE0LD_1RA1LD_1RF1RA") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm836: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0RE0LD_0RB0LE_1LA1LF_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm837: halts_at_trans (TM_from_str "1RB1RA_1LC0LF_1LD0LB_1RD1RE_---0RA_1LD0RB") c0 (E,0).
Proof. solve_halt 10. Time Qed.

Lemma tm838: halts_at_trans (TM_from_str "1RB1RA_1LC1LD_1RA0RB_1LE1LB_0RF0LF_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm839: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD0LB_1RE1RA_0RF---_1LF1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm840: halts_at_trans (TM_from_str "1RB0LD_1LC1RE_1LA1RC_1LB1LD_---1RF_1LA0RC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm841: halts_at_trans (TM_from_str "1RB0RF_0RC0LE_0LD1LA_1LE1LF_0LA0RA_1LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm842: halts_at_trans (TM_from_str "1RB0RF_0LC---_0LD1LC_1RE0LA_1RA1RD_0RD0LF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm843: halts_at_trans (TM_from_str "1RB---_1RC0RC_1LD0RA_0RD0LE_0LF0LC_1LB1RF") c0 (A,1).
Proof. solve_halt 17. Time Qed.

Lemma tm844: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD0RE_1LD1RE_0RF1LE_1RA0LF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm845: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_1LA1LD_0RD1LC_---0RF_1LC1RB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm846: halts_at_trans (TM_from_str "1RB1RE_0LC1RF_0RD1LC_---1RE_1RA1LF_0RD0LE") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm847: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_0RC1LD_1RA0LE_---1LC_1LC1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm848: halts_at_trans (TM_from_str "1RB0LB_1RC0LB_0RD---_1LD1RE_0RF1LF_1RA0LB") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm849: halts_at_trans (TM_from_str "1RB1LC_1LC0RB_0LE0LD_1LA1LF_1RB0RE_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm850: halts_at_trans (TM_from_str "1RB1LB_1LA0LC_---0LD_1RE1LD_1RA1RF_0RA0RE") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm851: halts_at_trans (TM_from_str "1RB1RC_1LC0LF_1RA0RD_---1RE_1LF1RE_1LC1LB") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm852: halts_at_trans (TM_from_str "1RB0RA_1LC1LB_1RD0LB_0RF1RE_1RA0RD_---0LB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm853: halts_at_trans (TM_from_str "1RB---_1LC0RF_1RE1LD_0LB1LA_0RF0RE_1LD1LC") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm854: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LD1RD_1LE1RD_1LC0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm855: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_1RA0RD_1LA1RD_1RC1LE_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm856: halts_at_trans (TM_from_str "1RB---_1RC1RB_0RD0LE_1LE0RB_0LF0RF_1RA0LD") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm857: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA0RE_1LA0RF_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm858: halts_at_trans (TM_from_str "1RB1RE_1LC1LE_1RF1RD_1LB1RE_0LB0RC_---1RA") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm859: halts_at_trans (TM_from_str "1RB0RA_1RC0RB_1LD0LE_0LA0LC_0LF1RF_1LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm860: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE1LF_0LB0LE_0LB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm861: halts_at_trans (TM_from_str "1RB1LC_1RC0RE_1RD0LC_1LA0RA_---1RF_0RC1LA") c0 (E,0).
Proof. solve_halt 5. Time Qed.

Lemma tm862: halts_at_trans (TM_from_str "1RB0LF_1LC0RE_---0LD_1RA0LA_0LD1RD_0LB0RD") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm863: halts_at_trans (TM_from_str "1RB0RA_1RC0RE_0LD---_1RA1LE_1LD0LF_1LE0LA") c0 (C,1).
Proof. solve_halt 13. Time Qed.

Lemma tm864: halts_at_trans (TM_from_str "1RB0LA_1RC1RF_0RD0LD_0RE1RB_1LE0LA_---1RD") c0 (F,0).
Proof. solve_halt 11. Time Qed.

Lemma tm865: halts_at_trans (TM_from_str "1RB1LA_1LC1LD_1RE1LA_1RF0LB_---0RC_1RA1RD") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm866: halts_at_trans (TM_from_str "1RB0RC_1LC0RC_0RD0LD_1RE0LF_1RA---_0LC1RA") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm867: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC1RA") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm868: halts_at_trans (TM_from_str "1RB0LD_1RC1RA_1LD0RE_1RB1LA_1RF1RC_---0RD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm869: halts_at_trans (TM_from_str "1RB0LC_0LC0RA_1RA1LD_0LC1LE_1LF0RE_0LA---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm870: halts_at_trans (TM_from_str "1RB0LA_0RC0LC_0LD1RE_1LA0RF_1RD---_0RD1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm871: halts_at_trans (TM_from_str "1RB1RC_0LC1RA_1LF0RD_1RE---_0LA1RA_0RB0LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm872: halts_at_trans (TM_from_str "1RB1LA_1LC1LE_1RF0RD_1LA1RE_1RD0LB_---0RC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm873: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RE_1LF1LE_0LA0LA_1LA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm874: halts_at_trans (TM_from_str "1RB1RB_1LC1RB_1LC0LD_1RE1LD_1RA0RF_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm875: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE0LF_0LA0RA_1RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm876: halts_at_trans (TM_from_str "1RB1LC_1LA1LD_1LB---_1LE1RD_1RF0LB_0RD0RF") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm877: halts_at_trans (TM_from_str "1RB1LD_0RC0LE_1LC1RA_0LE0LA_1LB1LF_---0LD") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm878: halts_at_trans (TM_from_str "1RB0LD_1RC1RF_0RD1RA_1LE0RB_0LA0RA_0RE---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm879: halts_at_trans (TM_from_str "1RB0LB_1LB0RC_1RE0LD_1LA0RD_1RD1RF_0RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm880: halts_at_trans (TM_from_str "1RB0RF_1RC1RB_0RD0RE_1LE1RA_0LA0LE_0LD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm881: halts_at_trans (TM_from_str "1RB1LF_1RC0RE_0RD1RA_1LD1LE_0RF1LE_---0LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm882: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0LD1LC_1RE0LA_0RB0RE_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm883: halts_at_trans (TM_from_str "1RB1LB_1LA0LC_1RD1LC_---1RE_1RB0RF_1RB1RE") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm884: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RF1LD_0RE0LE_---1LC_1RB1RA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm885: halts_at_trans (TM_from_str "1RB1LC_1LC0RC_1LE1LD_1LE0LE_1RF0LA_---0RB") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm886: halts_at_trans (TM_from_str "1RB1RF_1LC0RF_1LD1LB_0LE---_1RA0LA_0RC1RA") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm887: halts_at_trans (TM_from_str "1RB1RF_0RC1RA_1LD0RC_1LE1LA_0LD1LA_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm888: halts_at_trans (TM_from_str "1RB1RB_0RC0LD_1RD0LC_1RE1LC_1LB0RF_1RA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm889: halts_at_trans (TM_from_str "1RB1LC_1LC0LE_1RD0LC_0LA0RA_1LC1RF_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm890: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_1RF0LD_1RA1LD_1RA0RB_---1RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm891: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_1RC0RC_---0RA") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm892: halts_at_trans (TM_from_str "1RB---_0RC0RD_1LD1RB_0LE0LA_1RA1LF_0LD0LE") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm893: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_0LD0LB_0LE1LD_1RA1LF_0RC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm894: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_0RD1LD_1RE0LF_---1RC_1RA1LC") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm895: halts_at_trans (TM_from_str "1RB0LA_1RC---_0RD0RC_1LD1LE_0RA0LF_1LC1LA") c0 (B,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm896: halts_at_trans (TM_from_str "1RB0RD_1LC0LB_0RA0LB_1RE---_0RF1RD_1RA0LC") c0 (D,1).
Proof. solve_halt 17. Time Qed.

Lemma tm897: halts_at_trans (TM_from_str "1RB1RF_1RC0RB_1LD0RA_0LE0LC_0LA1LE_0LD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm898: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_0RF0LE_0LD1RB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm899: halts_at_trans (TM_from_str "1RB0LD_1RC0LE_1LA1RC_1RE0RC_1RF1LE_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm900: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1RE1LF_0LA1LE_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm901: halts_at_trans (TM_from_str "1RB0RB_0RC1RF_1RD1RE_1LE0LE_1RA0LD_0RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm902: halts_at_trans (TM_from_str "1RB1LE_0LC1RD_---1LD_1LA0RD_1RF0LF_0LA1LC") c0 (C,0).
Proof. solve_halt 7. Time Qed.

Lemma tm903: halts_at_trans (TM_from_str "1RB1RA_0RC0RB_1RD0RE_1LE1RF_0RA1LD_---0LE") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm904: halts_at_trans (TM_from_str "1RB0LB_1RC0LC_1RD1RC_0LE0RD_1RA1LF_---1LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm905: halts_at_trans (TM_from_str "1RB---_1RC0RB_1LD0RB_1LE0LC_1LF1LA_1RD0LE") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm906: halts_at_trans (TM_from_str "1RB0LD_0RC0RE_1RD0RF_1LA0LD_1RF---_0RA0RF") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm907: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LA0RB_0LC1LE_0RA---_0LE1RB") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm908: halts_at_trans (TM_from_str "1RB1RE_1RC0RF_0LD---_0LE1LD_1RA0LB_0RE1RA") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm909: halts_at_trans (TM_from_str "1RB1RC_1LC1LF_1RA0RD_---1RE_1LB1RE_1LC0LB") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm910: halts_at_trans (TM_from_str "1RB1LF_1RC1RF_1LD1RE_---0LC_0RB1RE_1LA0LE") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm911: halts_at_trans (TM_from_str "1RB1LE_1RC---_1RD0LD_1LE0RF_0LE0LA_1RC1RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm912: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LE1LD_1LB---_0LF0RA_1LA0LE") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm913: halts_at_trans (TM_from_str "1RB1LC_0LA1RB_1LA0RD_1RE1RC_0LF1LB_---1LE") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm914: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LE1LD_1LB---_0LF1LC_1LA0LE") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm915: halts_at_trans (TM_from_str "1RB1LE_1RC1RA_1LD1LC_0RA0LC_1RF1RE_---0RD") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm916: halts_at_trans (TM_from_str "1RB0RF_1LC0LD_1RB1LB_---1LE_1RF1LE_1RB1RA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm917: halts_at_trans (TM_from_str "1RB1LC_1LA1RE_1LD0LB_0LE---_1RF0RE_1LC0RE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm918: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA1LD_1LD0LF_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm919: halts_at_trans (TM_from_str "1RB1LF_0LC1RA_1LD1LC_0LE0LD_1LA0LB_---0RB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm920: halts_at_trans (TM_from_str "1RB1RA_1RC1RE_1LD---_1LA1LD_0LF0RB_0LA1LF") c0 (C,1).
Proof. solve_halt 8. Time Qed.

Lemma tm921: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_0LE1RF_0RD---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm922: halts_at_trans (TM_from_str "1RB1LF_0LC1LB_1RD1LA_0RE0RD_1LB1RD_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm923: halts_at_trans (TM_from_str "1RB1RE_0RC0RE_1RD0LA_0LA1RB_1LF---_0LA0LF") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm924: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_1RE0LF_1RA0LD_0RA---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm925: halts_at_trans (TM_from_str "1RB0RE_1RC1LD_1LD0RF_0RE0LD_1LC1RE_---1RA") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm926: halts_at_trans (TM_from_str "1RB1LE_1LC0RF_0RD1RC_1LE1RB_0LA0LE_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm927: halts_at_trans (TM_from_str "1RB0LA_1LC---_1LE1LD_1LE0LA_1RF0RC_1RA0RE") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm928: halts_at_trans (TM_from_str "1RB1LC_1LA0RD_0LB---_1LE0RF_1LF1LB_1RD0LE") c0 (C,1).
Proof. solve_halt 2. Time Qed.

Lemma tm929: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_0RF1RE_1RC0LF_---0RB") c0 (F,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm930: halts_at_trans (TM_from_str "1RB1LE_1LC0RB_0LA1LD_0LE1LB_1RF0LC_1RB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm931: halts_at_trans (TM_from_str "1RB0RB_1LC1RA_0LE0LD_1LB0LB_1LF0RA_1RE---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm932: halts_at_trans (TM_from_str "1RB0LE_0LC1RE_1LD0RB_1LA0RF_0RB1LC_---1RD") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm933: halts_at_trans (TM_from_str "1RB0LE_1RC0LE_0RD0LD_1RE0RA_1LB1RF_0LA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm934: halts_at_trans (TM_from_str "1RB0LB_1RC1LB_0LB1RD_0RF0RE_1LA1RE_---0LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm935: halts_at_trans (TM_from_str "1RB0RC_1RC1RF_1LD1RC_0LC0LE_1RA1LE_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm936: halts_at_trans (TM_from_str "1RB---_1RC1RF_1LD0LC_1RB1LE_1LB1LE_1RA0RF") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm937: halts_at_trans (TM_from_str "1RB0RA_1LC0LF_1RA1LD_1LE---_0LF1LB_1LB0RC") c0 (D,1).
Proof. solve_halt 10. Time Qed.

Lemma tm938: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA0RA_0LF0RA_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm939: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_1LD0RB_0LE0LC_1RA0LF_0RB---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm940: halts_at_trans (TM_from_str "1RB0LA_1RC1LA_1LD0RE_0RA0LB_1RF---_1RD1RD") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm941: halts_at_trans (TM_from_str "1RB0LE_1LC0RB_0RD0LD_1LA1RB_1RB0LF_1RC---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm942: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1RD1LD_1LA1RD_1LF1LC_---0LA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm943: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1LB0LF_0RF0RE_1LA1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm944: halts_at_trans (TM_from_str "1RB1LF_0LC---_1LC1RD_1RE0RA_0RC0LC_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm945: halts_at_trans (TM_from_str "1RB1LA_1LC0LB_1RD0RD_1RE1RC_1LA0RF_---0RB") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm946: halts_at_trans (TM_from_str "1RB1RE_1LC1LE_1RF1LD_0RA1LC_1RA0LB_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm947: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_0LC1LA_1RE1RC_1RF---_1LD0RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm948: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1RE_0LB---_0RA1RF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm949: halts_at_trans (TM_from_str "1RB0RF_1LC0RD_0LA1LD_1RE1LC_---1RA_0LB1RA") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm950: halts_at_trans (TM_from_str "1RB1RA_0RC1LE_1LD1RC_1RE0LF_---1LF_0LE0LA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm951: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD1RB_0LA1LD_1RC0LF_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm952: halts_at_trans (TM_from_str "1RB0LB_0RC1RE_1LD---_1LA0RC_0LF0RF_0RA0LD") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm953: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_1LE0LD_0LA0RB_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm954: halts_at_trans (TM_from_str "1RB0LA_1LC0RC_1RD1LA_1RA0RE_1LF0RD_1LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm955: halts_at_trans (TM_from_str "1RB1LC_1RC1RB_1LA0LD_1LC1RE_0RF---_1RD1RC") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm956: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_0LC0RC_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm957: halts_at_trans (TM_from_str "1RB---_1RC1RB_0LD0RB_1LF0RE_1LE0LC_0LA0LD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm958: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1LD0RA_1LE0LF_0LA1LC_1LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm959: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_1RD0LC_0LA0RA_1LC0RF_1LA---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm960: halts_at_trans (TM_from_str "1RB1LD_1LB0LC_1LD1RF_1RE0LD_0LA0RA_0RC---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm961: halts_at_trans (TM_from_str "1RB---_1RC1LB_1RD0LF_0RE0RA_1LA0RB_0LB1LC") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm962: halts_at_trans (TM_from_str "1RB0RC_1LC0RF_1RA1RD_0RE0LD_1LB0RC_1LD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm963: halts_at_trans (TM_from_str "1RB1RD_1LB0LC_1LD1LC_0RE1LF_---1RA_1LD0LA") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm964: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD0LF_1RE1RA_0RF---_1LF1LC") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm965: halts_at_trans (TM_from_str "1RB1RD_0LC1LD_1LB1LD_1RA1RE_---0RF_1LC0RF") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm966: halts_at_trans (TM_from_str "1RB0RF_0RC1RE_1LC0LD_1RA1LD_1LC1RE_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm967: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LE1LD_0LE---_0LF0RF_1LA1LC") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm968: halts_at_trans (TM_from_str "1RB0LD_0RC0RD_1LD0RA_1LE1RC_0LA1LF_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm969: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_0LD0LA_1LE1LA_1RA0LC_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm970: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA0LF") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm971: halts_at_trans (TM_from_str "1RB0RA_1LC0LC_0LD0RD_1RA1LE_1LF---_0LD1LB") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm972: halts_at_trans (TM_from_str "1RB0LC_0LC---_1LF1RD_1RE0RA_0RC1RE_1LD0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm973: halts_at_trans (TM_from_str "1RB1LB_0LC1RF_1LD1LC_1RE0RA_1RA1RD_---0RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm974: halts_at_trans (TM_from_str "1RB---_1RC1LF_1RD0RD_0RE1RA_1LF1RB_0LB0LF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm975: halts_at_trans (TM_from_str "1RB0RD_1LC1RA_1LD1RA_1RE0LF_1RC---_0LD1LF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm976: halts_at_trans (TM_from_str "1RB0LD_1RC1RB_1LA1LE_---1LA_1LC0RF_0LF1RE") c0 (D,0).
Proof. solve_halt 16. Time Qed.

Lemma tm977: halts_at_trans (TM_from_str "1RB0LA_0RC---_0LD1LE_1LA0RF_1RD0LC_1RE1RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm978: halts_at_trans (TM_from_str "1RB0LD_0LC0RB_1RA1LC_---1LE_1LF0LD_1LB0LD") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm979: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_1LD0RA_1LE1LD_0LA0RA_0LE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm980: halts_at_trans (TM_from_str "1RB1LC_1LC0RD_0LF1LD_1RE0LD_0RB1LF_---1LA") c0 (F,0).
Proof. solve_halt 15. Time Qed.

Lemma tm981: halts_at_trans (TM_from_str "1RB1LA_0LC1RE_1LF1RD_0LE---_0RA1RC_0RB0LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm982: halts_at_trans (TM_from_str "1RB0LE_1LC0RF_1RA0LD_0RC1LF_---1LA_0LD1RC") c0 (E,0).
Proof. solve_halt 3. Time Qed.

Lemma tm983: halts_at_trans (TM_from_str "1RB0RD_1RC0LC_1LD0RF_---1LE_1LB1LA_0LA1RC") c0 (D,0).
Proof. solve_halt 16. Time Qed.

Lemma tm984: halts_at_trans (TM_from_str "1RB0LC_0RC0LE_1LD0RE_1LA0LD_1RC1RF_0RA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm985: halts_at_trans (TM_from_str "1RB0RD_1RC1LB_1LA0RF_1LE1RD_---1LF_1LD0LB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm986: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0RA_1LD0RF_1LB---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm987: halts_at_trans (TM_from_str "1RB0LE_1LC1RE_1RD1LB_0RA1LE_0RF0LC_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm988: halts_at_trans (TM_from_str "1RB0LA_0RC---_1LD0RE_0RE0LC_1LC1RF_0RE1RA") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm989: halts_at_trans (TM_from_str "1RB0RF_1LC1LD_1RD1LC_1RE0LB_1RA0RD_0RE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm990: halts_at_trans (TM_from_str "1RB1LE_1LC---_0RD1RC_1LE1RF_0LA0LE_1RC0RB") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm991: halts_at_trans (TM_from_str "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_1RD---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm992: halts_at_trans (TM_from_str "1RB0LB_1LC0RB_0LF0LD_1LE1RC_1LA---_0RF1RB") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm993: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_0RD0LD_1LE1RB_1RB0LA_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm994: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA1LD_1LD0LF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm995: halts_at_trans (TM_from_str "1RB1RA_1RC0LD_1LB1RE_1LA1LB_0RF---_0RB1RD") c0 (E,1).
Proof. solve_halt 8. Time Qed.

Lemma tm996: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0LD1LC_1RE0LA_0RB0RE_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm997: halts_at_trans (TM_from_str "1RB0LC_0RC0RB_1LD1LA_1LE---_0LF0LA_0LA0LB") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm998: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RA---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm999: halts_at_trans (TM_from_str "1RB1LE_1LC0RD_1LA1LD_1RA1RF_---0LF_0RF0LC") c0 (E,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1000: halts_at_trans (TM_from_str "1RB0RC_1RC1RF_1LD1RA_0LE0LD_1RE0RC_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1001: halts_at_trans (TM_from_str "1RB1LA_1LC0RD_1LA0LC_1RE1RF_---1RC_0RC1RA") c0 (E,0).
Proof. solve_halt 5. Time Qed.

Lemma tm1002: halts_at_trans (TM_from_str "1RB1LF_1LC1LD_1RD1LA_---0RE_0RC1RA_1LC0LB") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1003: halts_at_trans (TM_from_str "1RB0LA_0RC1RF_0LD1RE_1LA0LF_0RB---_1RD0RE") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1004: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0LA0LF_1LF0LE_1LD---_0LA0RA") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1005: halts_at_trans (TM_from_str "1RB0RF_1RC1RE_1RD0RA_1RE---_0LF1LF_1LB0LE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1006: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_1LD0RD_1RE1LD_---1RA_0RB1LA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1007: halts_at_trans (TM_from_str "1RB1RF_1LC1LE_---1LD_1LE1RB_1RA1LF_0RA0LB") c0 (C,0).
Proof. solve_halt 10. Time Qed.

Lemma tm1008: halts_at_trans (TM_from_str "1RB0RB_1LC1RF_1RD0LB_0RE1RD_1RA1LE_0LC---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1009: halts_at_trans (TM_from_str "1RB0RC_1LA1RA_---1RD_1LE0RD_1LF1LB_0LE0LB") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1010: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1RB_1RE---_0LA1LE_1LE0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1011: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1LA1RD_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1012: halts_at_trans (TM_from_str "1RB---_1RC1LD_1RD0RC_1LE0LF_0LB1LE_0LA0RB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1013: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_1RB0LD_1LE0LF_0RE0LB_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1014: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RF0LD_1RE0LA_1LB1RF_0RE0RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1015: halts_at_trans (TM_from_str "1RB0LD_0RC1RA_1LC0RA_1LE1LF_0LA0LE_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1016: halts_at_trans (TM_from_str "1RB---_1RC0RA_1LD0RB_0LE0LC_1RE0LF_1LD0RA") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1017: halts_at_trans (TM_from_str "1RB0LD_0LC0RB_1RA1LC_1LF1LE_1LA0LC_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1018: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1LD1RC_1RB0LA_1RF0RC_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1019: halts_at_trans (TM_from_str "1RB0RD_1RC0LF_1RD0RD_1LE0LA_0LC1LB_---1LE") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1020: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD0LA_1RE0LD_0RF---_1LF1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1021: halts_at_trans (TM_from_str "1RB0RF_1LC0RE_1RD1LB_---1RE_1RA0LB_1LB1RC") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1022: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LD0LB_0LE0LF_1LA1LB_0LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1023: halts_at_trans (TM_from_str "1RB1LF_1LC1LE_0RD1RC_1LA1RD_---1LB_0RD0LA") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm1024: halts_at_trans (TM_from_str "1RB1LD_0LC0RF_0LE0RD_1LB---_1LA1RB_0RA0RF") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1025: halts_at_trans (TM_from_str "1RB0RC_1LC0RE_1RA1LD_0LC0LA_0RF1LC_---1LD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1026: halts_at_trans (TM_from_str "1RB---_0RC1RB_1LD1RF_0LE0LD_0RA1LD_1LB1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1027: halts_at_trans (TM_from_str "1RB1LA_1LB0RC_1LD1RC_1LE0LA_---0LF_1RF1LC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1028: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RE---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1029: halts_at_trans (TM_from_str "1RB---_1RC0RB_1RD1RF_0LE1LD_0RB0LD_0RA1RE") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1030: halts_at_trans (TM_from_str "1RB0LD_1RC1RF_1LA0RE_1RB1LE_0LA0RD_---1RC") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1031: halts_at_trans (TM_from_str "1RB1RC_0RC0LE_1LD1RF_1LE---_1RA0LB_1RE0RB") c0 (D,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1032: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA1LD_1LD1LF_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1033: halts_at_trans (TM_from_str "1RB0RE_1LC0LB_1LD1LB_1RA1RF_---1LF_0RD1RD") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1034: halts_at_trans (TM_from_str "1RB1LE_1LC0RD_1LA0LB_1LE0RE_1LB0LF_1RA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1035: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0LF1LD_0LE---_0LB1LA_1RD0LE") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1036: halts_at_trans (TM_from_str "1RB0LA_0RC1LE_1RD---_1LE0RF_0LF1LF_0LB1RA") c0 (C,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1037: halts_at_trans (TM_from_str "1RB1LB_1RC1RF_1LD1RA_0LE0LD_1RE0RC_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1038: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_1LD1RC_0RA1LE_0LF0LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1039: halts_at_trans (TM_from_str "1RB0LA_0LC1LB_1RD1LA_0RE0RD_1RF1RD_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1040: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE0LF_0LB0LE_0RD---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1041: halts_at_trans (TM_from_str "1RB0RA_1LC1RC_1RE0LD_0LB0LC_1LA0RF_1RA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1042: halts_at_trans (TM_from_str "1RB1RD_0LC1RE_0RA1LC_1RA1LE_0RF0LD_---1RD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1043: halts_at_trans (TM_from_str "1RB0LF_1RC---_1RD0RE_1LE0RE_0RA0LA_0LE1RC") c0 (B,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1044: halts_at_trans (TM_from_str "1RB1RF_1RC0LA_1LD1RB_1LE0LD_0LF0LB_0RA---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1045: halts_at_trans (TM_from_str "1RB0RD_1LC0RE_0RD0LC_1LB1RD_1RF1RA_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1046: halts_at_trans (TM_from_str "1RB1RA_1RC1LD_1LD0LE_---1LC_1RF1LE_1LF0RA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1047: halts_at_trans (TM_from_str "1RB1RE_1RC0LB_0RD---_1LD1RE_0RF1LB_1RA0LB") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1048: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1LA_0LE1LF_1LA0RC_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1049: halts_at_trans (TM_from_str "1RB0RA_1LC1RF_0LD1LC_1LE1RD_1LA0LA_---1LA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1050: halts_at_trans (TM_from_str "1RB0LB_1RC1LB_1LD0RF_---0LE_0RC1LA_1LE1RF") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1051: halts_at_trans (TM_from_str "1RB0LA_1RC0RA_0RD0RF_1LE1RA_0LF---_1LA0RE") c0 (E,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1052: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_1RD1RC_1LE1RB_---0LF_1LE0LA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1053: halts_at_trans (TM_from_str "1RB0RD_1RC0LE_1LD0RB_1RF1LC_1LD1RA_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1054: halts_at_trans (TM_from_str "1RB0RC_1LA1RA_1LD1RC_0RF1LE_1LA0LD_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1055: halts_at_trans (TM_from_str "1RB1LA_1RC0LF_1LC0RD_1RF0LE_1LD0LA_---1RA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1056: halts_at_trans (TM_from_str "1RB0RD_0LC0LB_1RF1RD_1RE---_1LB0RA_1RF0LE") c0 (D,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm1057: halts_at_trans (TM_from_str "1RB0RD_1RC0RB_0LA0RA_1RE---_1LF1LE_1RB0LE") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1058: halts_at_trans (TM_from_str "1RB0LC_0RC0RD_1LD1RE_0LE0LD_1RA0RF_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1059: halts_at_trans (TM_from_str "1RB1RE_1RC1RA_0LD1LA_1LC1LA_---0RF_1LD0RF") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1060: halts_at_trans (TM_from_str "1RB0RF_0LC1LB_1RD1LA_0RE0RD_0LA1RD_---1LE") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1061: halts_at_trans (TM_from_str "1RB0RE_1LC0RD_---1LA_1LE1RD_0LF0LA_1RA0LC") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1062: halts_at_trans (TM_from_str "1RB---_0RC1RE_1RD1RA_0RE0LE_1LF0LA_0LB0RD") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1063: halts_at_trans (TM_from_str "1RB1LB_1RC1RE_1LD1RA_0LE0LD_0RF0RC_1LA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1064: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD1RA_0RE0LE_1RF0RD_1LB0LF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1065: halts_at_trans (TM_from_str "1RB0LE_1LC1RB_---0RD_0LB1RE_1LF0RD_1LA1LE") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1066: halts_at_trans (TM_from_str "1RB0LC_0RC---_1RD0RE_1LE0RF_0LA0LE_0RE1RA") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1067: halts_at_trans (TM_from_str "1RB---_0RC0RB_1LD1LA_0LE0LA_1LF0RC_1RB1LD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1068: halts_at_trans (TM_from_str "1RB0LE_0RC1RB_1LD0RA_1LA1LC_0LC0LF_---1RC") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1069: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD1RF_1RE0RF_1LF0LE_0LB0LE") c0 (A,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1070: halts_at_trans (TM_from_str "1RB0RC_1LC1RA_0LD1LC_1LE1LA_0RF0LC_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1071: halts_at_trans (TM_from_str "1RB1RA_1RC1LD_1LD0RA_---1LE_1LB0LF_0RE1LF") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1072: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF0RC_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1073: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_0LA1RD_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1074: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA1RE_0RC1RF_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1075: halts_at_trans (TM_from_str "1RB0LF_1LC1LB_1RD1LA_1RB1RE_1LB1RD_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1076: halts_at_trans (TM_from_str "1RB1LF_1LC0RE_1LA0LD_1RE---_0RB0LD_0LB1LC") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1077: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_1RA1LD_0RE0LE_---1LC_1LD1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1078: halts_at_trans (TM_from_str "1RB0LE_1RC---_1LD0LC_1RF0RA_1LC1RD_0RE0LE") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1079: halts_at_trans (TM_from_str "1RB0LA_1RC0RC_1LD---_1RE1LD_1LA1RF_1RE0RE") c0 (C,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1080: halts_at_trans (TM_from_str "1RB0RF_0RC1RE_1LD0RA_0LE0RE_1RA0LC_1RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1081: halts_at_trans (TM_from_str "1RB0LD_1RC1RE_1LA1RF_1LF0LC_1RB---_0RB1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1082: halts_at_trans (TM_from_str "1RB0LA_1RC0RE_0RD0RE_1LA1RF_1LD1RE_---1RA") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm1083: halts_at_trans (TM_from_str "1RB0LC_1LC0RB_0LF1LD_0LE---_1LA0RC_0RA1LE") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1084: halts_at_trans (TM_from_str "1RB1RD_1LC0LF_0RA0LB_0RE1RA_---1RF_1LB1RC") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm1085: halts_at_trans (TM_from_str "1RB0LA_1LC0RC_1RD1LA_1RE0RF_1RA1LA_---1RD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1086: halts_at_trans (TM_from_str "1RB---_0RC0LC_1RD0LF_1RE0LE_1LC1RA_1RC1LC") c0 (A,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1087: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA0RE_1LA1RF_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1088: halts_at_trans (TM_from_str "1RB1LE_1LC0RF_0RD1RC_1LE1RB_0LA0LE_1LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1089: halts_at_trans (TM_from_str "1RB1RF_1LC0RD_1RE0LD_1LC0LD_0RA1RE_0RB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1090: halts_at_trans (TM_from_str "1RB0RF_0LC1RD_0LD1LC_1RA0RE_1LA1RE_---1LB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1091: halts_at_trans (TM_from_str "1RB---_1RC1RF_1LD1RF_0LE0LD_1RE0RC_1RA0RC") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1092: halts_at_trans (TM_from_str "1RB1RD_1RC0LF_1LD0RA_1RA0LE_1LA1LD_---1LB") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm1093: halts_at_trans (TM_from_str "1RB0LF_1LC1LD_1LA0LB_0LE0RD_1RA0LB_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1094: halts_at_trans (TM_from_str "1RB1RC_1LC1RF_1LD0LB_1RE1LC_1RC1RE_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1095: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA0RF_1LE---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1096: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA0RA_1LF0RA_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1097: halts_at_trans (TM_from_str "1RB1RE_0RC---_1LD1RC_1LC0RA_1LF1RD_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1098: halts_at_trans (TM_from_str "1RB0LB_1RC0RB_0LD1RB_1LF1LE_0LA1LD_0RD---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1099: halts_at_trans (TM_from_str "1RB1RF_1RC0LA_1LD1RB_1LE0LD_1RB0LB_0RA---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1100: halts_at_trans (TM_from_str "1RB1RF_1LC1RD_1LA0LC_0RE---_1RA0RE_1RE1RB") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1101: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_0RC1LD_1LA1LC_---0RF_1LD1RB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1102: halts_at_trans (TM_from_str "1RB1LB_1LA0LC_1RD1LC_0LF1RE_1RB0RD_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1103: halts_at_trans (TM_from_str "1RB0LB_1RC0LE_0RD0RF_1LA0LA_0LA1RD_0RE---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1104: halts_at_trans (TM_from_str "1RB0LB_1LC0RB_1LF0LD_0LE0RA_1RA0RC_0LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1105: halts_at_trans (TM_from_str "1RB---_1RC1LE_0RD0LD_1LE0RF_0LB0LE_0LA0RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1106: halts_at_trans (TM_from_str "1RB1LF_1RC0LF_1RD0LA_0RE0RC_1LF---_1LA1LC") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1107: halts_at_trans (TM_from_str "1RB---_0LC0RD_1RE1LD_1RE0LC_1RF1RD_1LC0RA") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1108: halts_at_trans (TM_from_str "1RB0LC_0LC---_1LF1RD_1RE0RA_0RC0LC_1LD0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1109: halts_at_trans (TM_from_str "1RB---_1RC0RD_1LD1RF_0RE0LE_1RA0LF_0LD1RB") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1110: halts_at_trans (TM_from_str "1RB1RF_1RC1LF_1LD---_1RA0LE_1LD1LE_1RA0RD") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1111: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LE1LD_0LE---_1LF0LC_1RB1LB") c0 (D,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1112: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RA1LD_0LB0LF_1LD0RA_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1113: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_0RD0RF_0LE---_1LF0LB_1LA0LE") c0 (D,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1114: halts_at_trans (TM_from_str "1RB1LB_1RC0RF_1LD1RA_0LE0LD_1RE0RC_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1115: halts_at_trans (TM_from_str "1RB0LA_1RC0LC_1LD1RE_1LB0LD_0RA1RF_0LD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1116: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_0RD0RF_0LE---_1LF1LD_1LA0LE") c0 (D,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1117: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_---1LA_1RA1LE_0RA0LF_1RA1LB") c0 (C,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1118: halts_at_trans (TM_from_str "1RB0LA_1RC0RB_1LD0RF_---1LE_0LC0LF_1RA1LF") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1119: halts_at_trans (TM_from_str "1RB---_0RC1RE_1RD1RC_0RE0LE_1LF0LA_0LB0RD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1120: halts_at_trans (TM_from_str "1RB1RF_1RC1RD_1RD0LD_1LE0RA_1RF0LE_0RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1121: halts_at_trans (TM_from_str "1RB0RE_1RC0LD_1LD1RF_1RA1LD_1LB1RE_---0RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1122: halts_at_trans (TM_from_str "1RB0RA_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1123: halts_at_trans (TM_from_str "1RB---_1LC0LE_0LD1LC_1RD1LB_0LA1RF_0RE0RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1124: halts_at_trans (TM_from_str "1RB0RF_1LC0LA_1RD0LC_0RE1RA_0LB1RF_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1125: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RE0RF_0RB0LB_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1126: halts_at_trans (TM_from_str "1RB0RB_1LC0LE_0LD1LD_1RE0LC_0RF1RA_0RE---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1127: halts_at_trans (TM_from_str "1RB1LD_1RC1RD_1LA0RE_1RB0LA_1RF1RC_---0RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1128: halts_at_trans (TM_from_str "1RB0LB_1LC0LD_0LF1LA_1LB0RE_0RC---_1RA0LE") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1129: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1RB_1RE---_0LA1LE_1RE0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1130: halts_at_trans (TM_from_str "1RB1RE_0LC0RD_0RA1LB_1RE0LF_0RB1RC_0LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1131: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_0RB0LD_1LC0LC_0RA1RF_0LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1132: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LD0LA_0RF0LE_---0LC_0RC1RA") c0 (E,0).
Proof. solve_halt 12. Time Qed.

Lemma tm1133: halts_at_trans (TM_from_str "1RB1RD_1RC---_1LA0RE_0LD1LE_1RF0LE_0RD0RA") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1134: halts_at_trans (TM_from_str "1RB0LD_1LC1RA_1LD1LC_1LE1LA_1RF1RA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1135: halts_at_trans (TM_from_str "1RB1LA_0RC1LF_0RD1LE_1LD0RC_0LA1LB_---0LE") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm1136: halts_at_trans (TM_from_str "1RB0LD_0RC0RE_1RD1RF_1LA0LD_0RC---_1RA0LF") c0 (E,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1137: halts_at_trans (TM_from_str "1RB1RF_0LC0RB_1LA0LD_1LE---_1LF1LF_1LC0RA") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1138: halts_at_trans (TM_from_str "1RB0LD_0LC1LB_1RC1LA_1LF1RE_0RD0RE_0RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1139: halts_at_trans (TM_from_str "1RB1RE_1RC1RA_0LD1LA_1LC1LA_1LF0RE_1LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1140: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LA_1RC0LB_0LE---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1141: halts_at_trans (TM_from_str "1RB0LD_1LC1RE_0LD0LC_1RE1RB_0RA0RF_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1142: halts_at_trans (TM_from_str "1RB0RB_1LB0LC_1RD1LC_1RE0RF_1LE1RA_---0RB") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1143: halts_at_trans (TM_from_str "1RB---_0RC0RB_1RD0LF_1RE0LD_1LC0RA_1RA0RE") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1144: halts_at_trans (TM_from_str "1RB0LF_1LC0LA_1RD0LB_1RA1RE_1RC---_1LC0RC") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1145: halts_at_trans (TM_from_str "1RB---_1RC1RE_1RD0RA_1LE0RF_0LC0LF_1LB0LE") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1146: halts_at_trans (TM_from_str "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LE---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm1147: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RE1LD_1LB0LA_0RF0RE_0LA1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1148: halts_at_trans (TM_from_str "1RB0LE_0RC0RF_1RD0LF_1LE0LA_0RA0LD_1RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1149: halts_at_trans (TM_from_str "1RB1RF_1RC1LE_0RD1RA_1LD1RB_0RE0LB_---0RE") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm1150: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_---1LD_1LA0LF_1LC1RE_1LA1LD") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1151: halts_at_trans (TM_from_str "1RB0RF_1RC0LB_0RD---_1LE1RA_1LB0RD_1RE1LE") c0 (C,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1152: halts_at_trans (TM_from_str "1RB1LA_0RC0RD_1LA1LE_1LB1RF_1LC0LC_---1RA") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm1153: halts_at_trans (TM_from_str "1RB1LC_1RC1RF_0LD1LE_1LA0RE_1LC---_0RB0RF") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1154: halts_at_trans (TM_from_str "1RB0LD_0LC1LB_1RC1LA_1LF1RE_0RD0RE_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1155: halts_at_trans (TM_from_str "1RB0RA_1LC0LC_0LD0RD_1RA1LE_1LC0LF_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1156: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_0LB0RC_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1157: halts_at_trans (TM_from_str "1RB0RA_1LC1LB_1RD0LB_---1RE_1RA0RF_0RC1RE") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1158: halts_at_trans (TM_from_str "1RB1LC_1LA0RF_1RD0LC_0RE1LD_---0LB_1RB0RF") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1159: halts_at_trans (TM_from_str "1RB0RC_1LA---_1LE0LD_1LC0LF_1RF1LC_1RA0RF") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1160: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_1LF0LB_---1LE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1161: halts_at_trans (TM_from_str "1RB0RD_1LC1RE_1RD0LB_0RF1RA_1LC1LA_---0RE") c0 (F,0).
Proof. solve_halt 7. Time Qed.

Lemma tm1162: halts_at_trans (TM_from_str "1RB---_1RC0RF_0RD1RB_1RE1RA_1LF1LE_1RC0LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1163: halts_at_trans (TM_from_str "1RB1LF_1RC1LC_1RD0RB_1LE0RC_0LA0LD_1LE---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1164: halts_at_trans (TM_from_str "1RB---_1RC1LE_0LD0RD_1LA0RE_0RC1LF_1LB0LC") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1165: halts_at_trans (TM_from_str "1RB1RE_1LC0LB_1RD1LB_---0RA_1RC1RF_0RA0RF") c0 (D,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1166: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1RD1LB_0RA1LE_0RF0LC_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1167: halts_at_trans (TM_from_str "1RB0RB_1LC1RB_0LD1LD_1RE0LC_0RF1RA_0RE---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm1168: halts_at_trans (TM_from_str "1RB0LA_0RC1RD_0LD0RE_1LA0RF_0LF---_0RD1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1169: halts_at_trans (TM_from_str "1RB0RE_1LC0RB_0RD0LD_1LA1RB_1RB1LF_0LE---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1170: halts_at_trans (TM_from_str "1RB0RA_1LC1LF_1RA1LD_0LE---_1LB0LE_1LE1LC") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1171: halts_at_trans (TM_from_str "1RB0LD_1RC1RA_0RD0RB_1RE1LA_1LF---_0LA1LF") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1172: halts_at_trans (TM_from_str "1RB1LD_1RC1RF_1LA1LC_---0LE_0RC1LA_1LC1RB") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1173: halts_at_trans (TM_from_str "1RB1RA_1LC0LF_---1LD_1LE0LB_1RF1LD_0RA1RF") c0 (C,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1174: halts_at_trans (TM_from_str "1RB1LB_1LC0RD_1LF1LA_1LA0RE_1LB1RD_---0LA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1175: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_1RF---_0RA1RF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1176: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LE_1LE1RB_1RB0LF_1LC0LF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1177: halts_at_trans (TM_from_str "1RB0LB_1RC0RD_1LB1RA_0RA0LE_1LF---_0LA1LE") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1178: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_0LD1LA_0RE0LE_1RB---_0LA1LB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1179: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1RD0RF_0LA1RB_1LC1RE_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1180: halts_at_trans (TM_from_str "1RB0RD_1LC1LC_1LD1LB_1RA1LE_0RF0LC_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1181: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1RD1LD_1LE1RD_0RC0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1182: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA1RF_1RA0LE_0LA---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1183: halts_at_trans (TM_from_str "1RB---_1LC0LD_0RD1RC_1RE0RC_1LF0LB_0LA1LE") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1184: halts_at_trans (TM_from_str "1RB1RD_0RC1RF_1RD0LA_1LE1RB_0LA0LE_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1185: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_0RF1LD_1LE0LC_1RA0RB_0LD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1186: halts_at_trans (TM_from_str "1RB0LC_0RC0RA_1LD0RE_1LA0LD_1RC0RF_1LA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1187: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD0LC_1RF0LE_---0LC_0RA1RF") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1188: halts_at_trans (TM_from_str "1RB1LE_0RC0LA_1LD0RA_1LE---_1LF1LC_0RB0LE") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1189: halts_at_trans (TM_from_str "1RB1LB_0LC0RF_1LE1LD_0LE---_1LA0LC_1RB0RF") c0 (D,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1190: halts_at_trans (TM_from_str "1RB0RC_1LC0RF_1RA0LD_1RC0LE_1LA0LC_1RA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1191: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD0RD_1RA1LB_0LF0RD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1192: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_1LA0RE_1RB1LE_0LA0RD_---0LA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1193: halts_at_trans (TM_from_str "1RB0LC_1RC1LF_0LD1RF_---1LE_0RE1LB_0RA1RA") c0 (D,0).
Proof. solve_halt 10. Time Qed.

Lemma tm1194: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RA_0LE0LB_1LC1LF_1RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1195: halts_at_trans (TM_from_str "1RB1RE_0LC1LB_1RE1LD_1RB0LF_0RA0RE_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1196: halts_at_trans (TM_from_str "1RB1RE_1LC0LA_---1LD_1RE0LF_1LB1RA_1RA1LC") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1197: halts_at_trans (TM_from_str "1RB0LD_1RC1RE_1LA0RF_1RA1LA_0RA0LA_1LA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1198: halts_at_trans (TM_from_str "1RB---_1RC1RC_1RD1LF_1RE1RA_0RF0RD_1LB0LC") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1199: halts_at_trans (TM_from_str "1RB0RF_1LC1RC_0RA0LD_1LE0RF_0LC0RC_1RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1200: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_1RF1LD_1RD0LE_1RA1LC_---1RB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1201: halts_at_trans (TM_from_str "1RB1LB_1LC---_1LD1RC_1RF0LE_0LA1LC_0RC0RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1202: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA0RA_1LD0LF_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1203: halts_at_trans (TM_from_str "1RB0RE_1LC0RF_0RE0LD_0LC0LB_1RA1LE_1RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1204: halts_at_trans (TM_from_str "1RB1LB_1RC0LB_1LA1LD_1LE1RD_1RA0RF_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1205: halts_at_trans (TM_from_str "1RB1LC_0LA0RE_0LD0LF_1LA0RF_1RB0RE_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1206: halts_at_trans (TM_from_str "1RB---_1RC1RF_1LD0RB_0LE0LC_1LA0RC_1RE0RC") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1207: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_0LD1RB_0LA1LD_0LF1LC_0LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1208: halts_at_trans (TM_from_str "1RB0RD_1LC0LE_1LD1LB_1RB1RA_---1LF_1RD1LF") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1209: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD1LC_1RA1LB_1LF0RD_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1210: halts_at_trans (TM_from_str "1RB1LF_1LC0RD_0RE1LD_1LE0LC_0RA---_1LA0LD") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1211: halts_at_trans (TM_from_str "1RB0RF_0LC0RA_1LA0LD_0LE---_1LB0RE_0RE1LD") c0 (D,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1212: halts_at_trans (TM_from_str "1RB0RA_1LC0RF_0LD1LC_1LE0LE_1RA1LC_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1213: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE0LF_0LA1LE_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1214: halts_at_trans (TM_from_str "1RB1LF_1LC0RF_1RD0LC_0RE---_1RA1RC_0LA0RA") c0 (D,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1215: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RF1RB_---0RD") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm1216: halts_at_trans (TM_from_str "1RB0LD_0LC0RB_1RA1LC_---1LE_1LF0LD_1LB1RD") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1217: halts_at_trans (TM_from_str "1RB0LD_1LC0RF_0LD0LC_1RE1RB_0RA---_0LF1RD") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1218: halts_at_trans (TM_from_str "1RB---_0LC1RC_1RF1RD_1LE0RA_0RF0LE_0LD1RC") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1219: halts_at_trans (TM_from_str "1RB0RE_1LC0RB_1RA0LD_0LB0LF_0RC0RF_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1220: halts_at_trans (TM_from_str "1RB1LA_1RC0RA_1LD0RF_0RA0LE_0LD0LC_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1221: halts_at_trans (TM_from_str "1RB0RF_1LC1LF_1RD0LB_0RA0RE_1RF---_0RC0RF") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1222: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA0LD_1LC1LA_1RF---_1RA1LA") c0 (E,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1223: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1RB0LA_0RF0RE_1LB1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1224: halts_at_trans (TM_from_str "1RB1LB_1RC1LE_1RD0RD_1LA1RC_0LF0LC_---0LA") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm1225: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD1RE_0LA0LD_1LB0RF_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1226: halts_at_trans (TM_from_str "1RB0RB_0RC0LD_1RD1LA_1LE1RF_1LA0LE_0RA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1227: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_---0LD_1LE0LB_1RF0LA_1LA1RE") c0 (C,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1228: halts_at_trans (TM_from_str "1RB1RE_0LC1LB_1RE1LD_1RB1LF_0RA0RE_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1229: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_1RD1RF_1LB0RC_1LA0LE_1LA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1230: halts_at_trans (TM_from_str "1RB1RD_1LB0LC_1LD1LC_0RE1LF_---1RA_0RC0LA") c0 (E,0).
Proof. solve_halt 10. Time Qed.

Lemma tm1231: halts_at_trans (TM_from_str "1RB1RD_1RC1RE_1LA0LC_1LB1LD_1RF0RE_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1232: halts_at_trans (TM_from_str "1RB1RE_1RC0LF_1RD0RA_1LA1LE_1RA0LD_---1LB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1233: halts_at_trans (TM_from_str "1RB0LE_1LC1LA_1LB1RD_0RC0RD_1LF---_0LA1LD") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1234: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD0RD_1RA1LB_1LF0RD_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1235: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA0RA_1LD1LF_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1236: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_0LD0RA_1RE1LD_---0LF_0RD1LA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1237: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_1LE0LD_1RC0RB_1LB---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1238: halts_at_trans (TM_from_str "1RB1RA_1RC0RD_1LD0LE_---1LC_1RF1LE_1LF0RA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1239: halts_at_trans (TM_from_str "1RB0RC_1RC1RE_1LD0RB_---1LB_1RA1LF_1RB0LF") c0 (D,0).
Proof. solve_halt 8. Time Qed.

Lemma tm1240: halts_at_trans (TM_from_str "1RB0RD_1LC0LF_1LD0LB_1LE0RD_1RF---_1RB1RA") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1241: halts_at_trans (TM_from_str "1RB0RC_1LC---_1RA1LD_1RA0LE_1RF0LF_0LC0LE") c0 (B,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1242: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0LA0LF_1LF0LE_1RF---_0LA0RA") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1243: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_1LD1RC_0RA1LE_1LF0LA_---0LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1244: halts_at_trans (TM_from_str "1RB1LF_1RC0RE_0RD1RA_1LE0RC_0LA---_0LA0LF") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1245: halts_at_trans (TM_from_str "1RB1RF_1LC1LE_---1LD_1LE1LF_1RA1LF_0RA0LB") c0 (C,0).
Proof. solve_halt 10. Time Qed.

Lemma tm1246: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RA1LD_1RA0LF_1RB1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1247: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LF_1RE0LB_1LC0LC_1RA0LE") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1248: halts_at_trans (TM_from_str "1RB---_0RC0RF_1RD0LA_1LE1RB_1LB0LE_1RC0LC") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1249: halts_at_trans (TM_from_str "1RB1LF_0LB1RC_1RD---_0RE1RA_1LF0RD_0LA0LF") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1250: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1RB0LA_0RF0RE_1LA1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1251: halts_at_trans (TM_from_str "1RB0LE_1LC0RE_0RE1LD_1LA---_1LB1RF_1LC0RB") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1252: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_1LF0RB_---1LC") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1253: halts_at_trans (TM_from_str "1RB0RF_1LC1LB_1RD0LB_0RA1RE_1RD0RC_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1254: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_0RF1LD_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1255: halts_at_trans (TM_from_str "1RB0LD_1RC1RE_1LA1RF_1LF0LC_0LF---_0RB1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1256: halts_at_trans (TM_from_str "1RB0LE_1RC1RF_1LC0LD_1LE0RB_0LA1LD_---0RB") c0 (F,0).
Proof. solve_halt 11. Time Qed.

Lemma tm1257: halts_at_trans (TM_from_str "1RB0LF_1RC0LA_0RD1RF_0LE0RB_1LB---_1LC1LD") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1258: halts_at_trans (TM_from_str "1RB0RC_1LC1RC_1RE0LD_1LC0LD_0LE0RF_1RA---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1259: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LD_1LE1RB_0LF0LE_1RB1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1260: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1RB1LD_0LE0LF_1LC0RF_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1261: halts_at_trans (TM_from_str "1RB1RD_0RC1RF_1RD---_1LE1RA_0LA0LE_0RB1RD") c0 (C,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1262: halts_at_trans (TM_from_str "1RB---_1RC1RA_1LD1RE_1RE0LD_0RF0RB_1LD0LF") c0 (A,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1263: halts_at_trans (TM_from_str "1RB1RA_1RC0RA_1LD---_1LD1LE_0LF0RD_1LA0LE") c0 (C,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1264: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA0RA_1LD0LF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1265: halts_at_trans (TM_from_str "1RB0LA_0RC0LE_1RD1RF_1LB1RC_1LD1LA_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1266: halts_at_trans (TM_from_str "1RB0LC_1LC0RC_1RE0LD_1LA0LA_1RB0RF_0RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1267: halts_at_trans (TM_from_str "1RB1LC_1LC1RF_0RE0LD_0LB0LD_0RA0LF_1RC---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1268: halts_at_trans (TM_from_str "1RB1RC_1LC0LC_1RD0LB_1RE0RE_0RA1RF_0RA---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm1269: halts_at_trans (TM_from_str "1RB0LD_1LC1RC_1LA0RC_1LE1RC_1LB1LF_---0RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1270: halts_at_trans (TM_from_str "1RB1LF_1LC0RF_1RD0LC_0RE---_1RA1RC_1LE0RA") c0 (D,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1271: halts_at_trans (TM_from_str "1RB0LB_1RC1RE_0LD1RF_1LA1LD_0RA0LA_---1LE") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1272: halts_at_trans (TM_from_str "1RB---_1LC0RA_0RD1RC_1LE1RB_0LF0LE_0RA1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1273: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1RD1RB_1RE---_0LA1LE_1RE0LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1274: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA1LD_1LD0LF_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1275: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0LD1RB_1LE---_1RF0LD_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1276: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0RD1RF_1LE1RA_1LA0LD_0LB---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1277: halts_at_trans (TM_from_str "1RB0RD_1LC1RF_0LD0LB_1RE1LC_0RA0LD_0RC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1278: halts_at_trans (TM_from_str "1RB0LE_1RC0RD_1LD0RF_---0LE_1RB1LF_0LA0RE") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1279: halts_at_trans (TM_from_str "1RB0RB_1LC1RE_1RD0LB_0RA1LE_0LC0RF_---1RC") c0 (F,0).
Proof. solve_halt 12. Time Qed.

Lemma tm1280: halts_at_trans (TM_from_str "1RB0LA_1LC0RC_1RD1LA_1RE0RF_1RA0RA_---1RD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1281: halts_at_trans (TM_from_str "1RB1RF_0RC1RB_1LD0RE_0LE0LD_1RA1LD_0RD---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1282: halts_at_trans (TM_from_str "1RB1LB_1LC1RE_1RA1LD_0LC0LA_1RF0RC_---0RD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1283: halts_at_trans (TM_from_str "1RB1LD_1RC1RF_1LD0LB_---1LE_1RF0LA_1LC1RB") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1284: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_---1LA_0RA1LC_1LA1RF_0RE0RD") c0 (C,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1285: halts_at_trans (TM_from_str "1RB1RF_1LC0LD_1RB1LB_---1LE_1RA1LE_1RB0RA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1286: halts_at_trans (TM_from_str "1RB0RD_0RC0LB_1LD---_1RE1LE_1LB0RF_1LE1RA") c0 (C,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1287: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LD0LC_1RB1LE_0LD0LF_0LA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1288: halts_at_trans (TM_from_str "1RB0RF_0LC1RA_1LD1RC_1LA1LE_1LA0LD_---1RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1289: halts_at_trans (TM_from_str "1RB0LA_0LC1LB_1RD1LA_0RE0RD_0RF1RD_0LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1290: halts_at_trans (TM_from_str "1RB0RC_1RC0RF_1LD1RA_0LE0LD_1RE0RC_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1291: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0RA_1LD1RF_1LA---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1292: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LD1RD_1LE1RD_1LE0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1293: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LD0RD_1LA0LE_1LB1LF_0RB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1294: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LA0RB_0LC1LE_0RA---_1RB1RB") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1295: halts_at_trans (TM_from_str "1RB0RF_1LC0LB_0RD0LB_1RF1RE_1RC---_0RA0LA") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1296: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1RD1LB_0RA1LE_1RF0LC_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1297: halts_at_trans (TM_from_str "1RB1RF_0LC---_1RF1LD_1RE0LD_0LC1LE_0RA0RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1298: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1LA_0LE---_1RF0RA_1LE0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1299: halts_at_trans (TM_from_str "1RB1LE_1LC0RB_0RD0LD_1LA1RB_0LD0LF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1300: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1LA1LC_1RA1RF_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1301: halts_at_trans (TM_from_str "1RB0RE_1LC0LE_1RE0LD_1LB---_1LB0RF_1LD0RA") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1302: halts_at_trans (TM_from_str "1RB0RF_0RC0LE_1LC1RD_0RA0LB_1LB0LE_1RA---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1303: halts_at_trans (TM_from_str "1RB0LE_0LC0RA_1LE0RD_1RC1LB_1LA1LF_1LC---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1304: halts_at_trans (TM_from_str "1RB0LB_0RC---_1RD0RE_1LE0RA_0LF0LE_1RB0LC") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1305: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1RD1RB_1RE---_0LA1LE_1RE0LD") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1306: halts_at_trans (TM_from_str "1RB---_1RC0LE_1LD0RB_1RE0LD_0RF1RA_0LC0RE") c0 (A,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1307: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1LD1RA_0LE0LD_0RA1LD_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1308: halts_at_trans (TM_from_str "1RB0RA_1LC0LC_0LD0RD_1RA1LE_1LC0LF_1RC---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1309: halts_at_trans (TM_from_str "1RB0RB_0RC0LC_1LD1RE_1LA0LD_1RF---_0RC1RA") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1310: halts_at_trans (TM_from_str "1RB1LC_0LA1RB_1LA0RD_0LE1RC_1LF1LC_---0LE") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1311: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_0RA1LD_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1312: halts_at_trans (TM_from_str "1RB---_1LC1RA_1RD0LC_0LE0RE_1RF1LC_1LC0RB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1313: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_0RD0LD_1LE1RB_1RE0RA_0LA---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1314: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD0RA_0LE0RE_0RF0LC_1RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1315: halts_at_trans (TM_from_str "1RB0LC_1RC1LF_0LD1RF_---1LE_1RC1LB_0RA1RA") c0 (D,0).
Proof. solve_halt 10. Time Qed.

Lemma tm1316: halts_at_trans (TM_from_str "1RB1LD_1RC0LB_0RD0LB_1RE1LA_0RF---_1LF1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1317: halts_at_trans (TM_from_str "1RB---_1LC1RE_0LD1LC_1RE1LF_0RB0RE_1LC1LA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1318: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE0RF_1RA0RB_1LE---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1319: halts_at_trans (TM_from_str "1RB---_1LC0RC_1RD0LC_0RE0RF_0LE1LC_1RA1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1320: halts_at_trans (TM_from_str "1RB1LA_1RC1RD_1LA0LA_1RF0RE_1LC1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1321: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD1RE_0LA0LD_1RB0RF_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1322: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA0RA_1LD0LF_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1323: halts_at_trans (TM_from_str "1RB0RA_1LC0RC_1LF0LD_0RE1LE_0LB---_1RA1LC") c0 (E,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1324: halts_at_trans (TM_from_str "1RB1RF_1RC---_0LD1LC_1RF1LE_1RC0LB_0RA0RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1325: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LA0RB_0LC1LE_0RA---_1RB0LE") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1326: halts_at_trans (TM_from_str "1RB0RC_0LC1RF_0RD1LD_1RE0LF_---0LF_1RA1LC") c0 (E,0).
Proof. solve_halt 5. Time Qed.

Lemma tm1327: halts_at_trans (TM_from_str "1RB0LF_1RC0LB_0RD---_1LD1RE_0RF1LB_1RA0LB") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1328: halts_at_trans (TM_from_str "1RB0RA_1LC0RB_0LA0LD_1LE1LF_1RB1LC_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1329: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_1LD0RC_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1330: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LF1LD_---0LB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1331: halts_at_trans (TM_from_str "1RB---_1LC0LA_1LD0LB_1RE1LC_1RF0RE_1RC0RC") c0 (A,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1332: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_0LD1LA_0LE---_1RF1LE_1LE0LC") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1333: halts_at_trans (TM_from_str "1RB0LB_1RC1LB_1LC0RD_1LE1RD_0LF1LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1334: halts_at_trans (TM_from_str "1RB1RF_0RC---_1RD0RE_1LE0RA_0LF0LE_1RB0LC") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1335: halts_at_trans (TM_from_str "1RB0LD_1RC0LF_1LD0RE_0RA1LE_0LD1RA_---1LB") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1336: halts_at_trans (TM_from_str "1RB0RE_1RC1RA_0RD0RA_1LE1LF_0LF---_0LA0LD") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1337: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RF0LF_---1LB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1338: halts_at_trans (TM_from_str "1RB1LD_1LC1RF_0RA1LB_0RE---_1RC1RE_1RD0LF") c0 (D,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1339: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1LA1RD_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1340: halts_at_trans (TM_from_str "1RB0LC_0RC---_1RD0RE_1LE0RF_0LA0LE_1LB1RA") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1341: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA1RF_1RA0RB_1LB---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1342: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA1LD_1LF0RA_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1343: halts_at_trans (TM_from_str "1RB0LD_0LC0RF_1LE0RD_1LB---_1LA0LF_0RB0RA") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1344: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA1LD_1LF0RA_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1345: halts_at_trans (TM_from_str "1RB1RE_1LC0LA_1RA1LD_1LB0LF_1LB1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1346: halts_at_trans (TM_from_str "1RB0LA_1RC1RD_0RD0RA_1LE1RF_1LA---_1RA0RC") c0 (E,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1347: halts_at_trans (TM_from_str "1RB0RC_0LC1RA_1LD1RC_---1LE_1LA0LF_1LA1LE") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1348: halts_at_trans (TM_from_str "1RB1LE_1LB0LC_1LD0LD_1RE1LF_0LA0RD_0RE---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1349: halts_at_trans (TM_from_str "1RB0RE_1RC0LB_1LD0RD_1RA1LB_1LF0RA_1LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1350: halts_at_trans (TM_from_str "1RB1LB_1LC0RB_0LE0LD_1LE1LF_1RB0RA_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1351: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_0LD1RB_1LE---_0LA1LE_1RD0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1352: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0LD1LC_1RE0LA_0RB0RE_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1353: halts_at_trans (TM_from_str "1RB0RC_1RC1RF_1LD1RA_0LE0LD_1RE0RC_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1354: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD1RD_1RE0LE_1LB0RA_0LE1LF") c0 (A,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1355: halts_at_trans (TM_from_str "1RB0RD_1RC1RE_1LA0LC_0LC1LD_1RF---_0RA1RF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1356: halts_at_trans (TM_from_str "1RB0RC_1LB1RA_1RD0LF_1RE---_1LC1RA_0LC1LF") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1357: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD0RE_0LA0LD_1LA0RF_0RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1358: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_1RA1LD_0RE0LE_---1LC_1LC1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1359: halts_at_trans (TM_from_str "1RB1RD_1LC1RF_1RA0LD_1LB1LE_0LE0RA_---0RE") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1360: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RE1LD_1LB0LA_0RF0RE_1RA1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1361: halts_at_trans (TM_from_str "1RB1RE_0LC0RC_1RE1LD_1LB0LF_0RA0RE_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1362: halts_at_trans (TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC0LF_1RA1LC_1RB---") c0 (F,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1363: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LD0RD_1LA0LE_1LB0RA_0RE---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1364: halts_at_trans (TM_from_str "1RB1RC_1LC0LE_1RA0RD_1LE1RD_0RF1LB_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1365: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_---0LD_1RE0LF_1RA1RB_1LB1LF") c0 (C,0).
Proof. solve_halt 15. Time Qed.

Lemma tm1366: halts_at_trans (TM_from_str "1RB1LD_1LC1RF_1LD0LC_1RE0RE_0RA0LB_0RD---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1367: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1RD1RD_1LE1RD_1LE0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1368: halts_at_trans (TM_from_str "1RB1LC_1LC0LF_1RF0LD_1LE0RE_1LB1LD_---0RA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1369: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_1LD0RE_1RB0LA_0LD0RA_---1RC") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1370: halts_at_trans (TM_from_str "1RB0RC_1LC---_1RA1LD_1RA0LE_1LD0LF_0LC0LE") c0 (B,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1371: halts_at_trans (TM_from_str "1RB0LE_0RC1LD_1LA1RC_---1LE_0LD0LF_1RB1RA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1372: halts_at_trans (TM_from_str "1RB0LF_1RC---_1RD1LA_1LE0RE_0RA0LA_0LE1RC") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1373: halts_at_trans (TM_from_str "1RB1LD_0RC---_0LD1RF_1RE0LB_0LA1LE_0RC0RF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1374: halts_at_trans (TM_from_str "1RB1RF_0RC0LE_1RD1LF_1RE---_1LB1LE_1RA0RB") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1375: halts_at_trans (TM_from_str "1RB1LF_1RC0LB_0RD0LB_0RE1RA_1RF---_1LA1LB") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1376: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1LE0LF_0LA0RA_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1377: halts_at_trans (TM_from_str "1RB1RA_1RC0LD_1LB1RE_1LA1LB_0RF---_0RF1RD") c0 (E,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1378: halts_at_trans (TM_from_str "1RB0LA_0LC0LD_1RD1LA_1LA1RE_0RC1RF_1LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1379: halts_at_trans (TM_from_str "1RB1RF_1RC---_0LD0RD_1RF1LE_1LC0LB_0RA0RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1380: halts_at_trans (TM_from_str "1RB1LB_1RC1LF_1LD0RC_0LF1LE_---1LC_0RA0LA") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm1381: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LD0LB_1LE1LF_1RC0LD_1RB---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1382: halts_at_trans (TM_from_str "1RB0LB_1LC0RB_0LF0LD_1LE1LF_1LA---_0RF1RB") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1383: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_0LD1RB_1RE---_0LA1LE_1RE0LD") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1384: halts_at_trans (TM_from_str "1RB---_1RC1RD_0LD0RF_1RF1LE_1LB0LD_1RC1RA") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1385: halts_at_trans (TM_from_str "1RB0RF_1RC0LE_1RD0RB_1LB1RA_1RA0LA_1LD---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1386: halts_at_trans (TM_from_str "1RB0LF_0RC---_1LD1RA_1RE0LA_1RC0RD_1LF1LC") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1387: halts_at_trans (TM_from_str "1RB0LE_1LC1RB_---1RD_1LA1LE_1LD0RF_0LB1RE") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1388: halts_at_trans (TM_from_str "1RB0RE_1LC---_0LD1LD_1RE0LC_1RF1RD_1RA1RF") c0 (B,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1389: halts_at_trans (TM_from_str "1RB---_1RC1RF_1RD0LE_1LC0LB_0LD1LD_0RB0RA") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1390: halts_at_trans (TM_from_str "1RB0LB_1LC1RD_1RE1RD_0RC1LA_1LF1RC_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1391: halts_at_trans (TM_from_str "1RB1LE_0LC0RB_0RA1LD_1LC---_0LF0LD_1LA0RD") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1392: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LA_1RC0LE_0LC---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1393: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA1LD_1LC0RB_1LF---_0RB0LD") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1394: halts_at_trans (TM_from_str "1RB0LA_1LC1RF_0RD1RC_0RE1RB_1LE0LA_---1RD") c0 (F,0).
Proof. solve_halt 11. Time Qed.

Lemma tm1395: halts_at_trans (TM_from_str "1RB1RA_1LC0RC_1RD0LD_1LB0RE_0LB0RF_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1396: halts_at_trans (TM_from_str "1RB0RF_1LC1LB_1RD0LB_0RA1RE_1RD0RC_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1397: halts_at_trans (TM_from_str "1RB0RB_0LC---_1LF1RD_1LE0RA_0RC1RE_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1398: halts_at_trans (TM_from_str "1RB0RF_1LC1RB_1RA0LD_1RA1LE_1LC1LE_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1399: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_0LD1LB_1RA0LE_1LC0LF_1RD---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1400: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RF0RD_---1LB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1401: halts_at_trans (TM_from_str "1RB0LC_0RC0RB_0LD1RB_1LE---_0LF1LE_1RB0LA") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1402: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_1LA1LD_0RB0RC_1RB1RD_---0LB") c0 (F,0).
Proof. solve_halt 13. Time Qed.

Lemma tm1403: halts_at_trans (TM_from_str "1RB0RB_1LC1LB_0LD0LB_0RE---_1RF0RC_0RA1RE") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1404: halts_at_trans (TM_from_str "1RB1RD_1RC1LE_0LA0RC_1LB1LC_---0LF_0LD1LF") c0 (E,0).
Proof. solve_halt 9. Time Qed.

Lemma tm1405: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LD_1RC1RB_1LC0LF_---1LA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1406: halts_at_trans (TM_from_str "1RB0LA_1LC1RD_1LC1LA_1RE0RB_0RA1RF_---1RA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1407: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD0LB_1RE1LB_0RF---_1LF1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1408: halts_at_trans (TM_from_str "1RB1RF_0RC0LD_1LD---_1LE1LD_1RA0LD_1RA0RE") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1409: halts_at_trans (TM_from_str "1RB0LA_0RC1RD_1LA1RF_0RE1RA_1LC0RB_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1410: halts_at_trans (TM_from_str "1RB1LA_1RC0LD_0LA0RC_---1LE_1LF0LD_1LC1RD") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1411: halts_at_trans (TM_from_str "1RB0LF_1LC1RA_0RB1LD_1RE1LC_---0RD_0RD1LA") c0 (E,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1412: halts_at_trans (TM_from_str "1RB0RA_1LC1RC_1LA1LD_0LE1LF_0LF---_0LB1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1413: halts_at_trans (TM_from_str "1RB1RF_1RC0LB_1RD0RA_1LE0RB_1LB0LE_0RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1414: halts_at_trans (TM_from_str "1RB1RE_1LC0RD_1LA0LC_1LE---_1RF1RB_1RA0RF") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1415: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LD_1LE1RB_0LF0LE_1RC1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1416: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RE1LD_0LB0LE_1LF0RA_0LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1417: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_1LD1LB_1LE0RA_0LF0LC_1RA---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm1418: halts_at_trans (TM_from_str "1RB0LA_0RC0LE_1RD1RF_1LB1RC_1RA1LA_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1419: halts_at_trans (TM_from_str "1RB---_1LC0RA_0RD1RC_1LE1RB_0LF0LE_1LB1LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1420: halts_at_trans (TM_from_str "1RB0LC_1RC0RE_1LD1LA_0RB0LD_1RF---_1RA1RA") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1421: halts_at_trans (TM_from_str "1RB0LD_1RC---_1LA0RF_1LB1LE_0LA1RE_0RE1RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1422: halts_at_trans (TM_from_str "1RB1LF_1LC---_0RD1RC_1LD1RE_1LC0RA_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1423: halts_at_trans (TM_from_str "1RB0RE_1LC0LF_1LD1LB_1RE---_0RA1RE_0RE0LA") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1424: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1RB0LF_0RF0RE_1LA1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1425: halts_at_trans (TM_from_str "1RB1RF_1LB0LC_1LD0RA_0LE1LC_1RA0LD_---0RA") c0 (F,0).
Proof. solve_halt 11. Time Qed.

Lemma tm1426: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_1LE0LD_1RC0RB_1RA---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1427: halts_at_trans (TM_from_str "1RB1RF_0LC1LE_1RA0RD_0LE---_1LB0RA_1RC0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1428: halts_at_trans (TM_from_str "1RB0RC_1RC0LB_1RD1LB_1RE0RF_1LC1RA_---1RB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1429: halts_at_trans (TM_from_str "1RB1RE_1LB0LC_1RD1LC_1RA0RF_1RC0RB_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1430: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_1RA1LD_1RA0LE_---1LC_0RF1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1431: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_0LE1LD_1LC0LF_1LA0LD_1LB---") c0 (F,1).
Proof. solve_halt 7. Time Qed.

Lemma tm1432: halts_at_trans (TM_from_str "1RB1LE_1RC---_1LD0RC_0LE1LA_0LA1LF_1LC0LC") c0 (B,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1433: halts_at_trans (TM_from_str "1RB1LA_1RC0RD_0LD0RF_1LE1RD_0LD0LA_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1434: halts_at_trans (TM_from_str "1RB0LD_1RC0RE_1LA1LC_1LC0LC_0RF0RA_1RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1435: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_0RC1LD_1RA0LE_---1LC_0RF1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1436: halts_at_trans (TM_from_str "1RB0LF_1RC0RE_1LD0RF_0RA0LE_0LD0LC_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1437: halts_at_trans (TM_from_str "1RB---_0RC0RD_1RD1RC_1LE1RF_1LD0RB_1RA0LF") c0 (A,1).
Proof. solve_halt 14. Time Qed.

Lemma tm1438: halts_at_trans (TM_from_str "1RB0RF_1RC1LC_1RD0LC_1LE0RE_1RA1LC_---1RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1439: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_0LD1LA_0RA0LE_1RB---_0LA1LB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1440: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_1LF1LD_0LE0LD_1LA0LB_---1LA") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm1441: halts_at_trans (TM_from_str "1RB0RC_1LA0RA_1RF1LD_0LE---_1LF0LC_0LB0LA") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1442: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_1RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1443: halts_at_trans (TM_from_str "1RB1RE_1RC1LB_1LD1LE_1RF1LB_1RA0LC_---0RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1444: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1RB_1RE---_0LA1LE_1LE0LD") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1445: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LD_1LE1RB_0LF0LE_0RB1LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1446: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD1RC_1LE1RB_0LF0LE_1LC1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1447: halts_at_trans (TM_from_str "1RB1LB_1RC1LE_1RD0RF_1LB1LD_---0LA_1LC0LA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1448: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_1LD0LB_0LE0LA_1RF1LB_0RA---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1449: halts_at_trans (TM_from_str "1RB0RD_1RC0RA_1LD1RB_1LE0LD_1LF0LB_0RC---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1450: halts_at_trans (TM_from_str "1RB0RA_1LC1RE_1RD0LC_0LD0LB_1RF0RC_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1451: halts_at_trans (TM_from_str "1RB1LD_1RC0LB_0RD0LB_1RE1LB_0RF---_1LF1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1452: halts_at_trans (TM_from_str "1RB0LD_1RC1RA_1RD1LC_1LE1LA_0RF0LC_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1453: halts_at_trans (TM_from_str "1RB0LD_1RC---_0RD1RC_1LE1RF_1LF0LE_1RC0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1454: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LD0RD_1LA0LE_1LB1LD_0RB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1455: halts_at_trans (TM_from_str "1RB0RA_0LC0LE_1RA1LD_1LE0LF_0LC0RC_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1456: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_1RA1LD_1RA0LE_---1LC_1RE1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1457: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA0RA_1LF0RA_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1458: halts_at_trans (TM_from_str "1RB1LF_0RC0RA_1LD1RB_0LE0RC_1LA0LC_0LB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1459: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1RE0LF_0LA1LE_1RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1460: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_0LB0RC_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1461: halts_at_trans (TM_from_str "1RB1RD_0LC1RE_0RA1LC_1RA1LE_0RF0LD_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1462: halts_at_trans (TM_from_str "1RB0LD_1RC0RE_1LA0RF_---1LE_0RF0LF_1RB1LC") c0 (D,0).
Proof. solve_halt 15. Time Qed.

Lemma tm1463: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0LA1RB_1LE1LD_1RE0LF_---1LC") c0 (F,0).
Proof. solve_halt 7. Time Qed.

Lemma tm1464: halts_at_trans (TM_from_str "1RB1LC_1RC0RE_1RD0LC_1LA0RA_---0RF_0LB1RD") c0 (E,0).
Proof. solve_halt 12. Time Qed.

Lemma tm1465: halts_at_trans (TM_from_str "1RB1LB_1LA0RC_1LD1LC_1RE0LC_---0RF_1RB0RD") c0 (E,0).
Proof. solve_halt 16. Time Qed.

Lemma tm1466: halts_at_trans (TM_from_str "1RB0LD_1RC0RE_1LA1RF_0LA0RE_1LD---_0RA1RB") c0 (E,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1467: halts_at_trans (TM_from_str "1RB1LE_1LC1RF_1LD1LC_1RA1RD_---1LA_0LE0RB") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm1468: halts_at_trans (TM_from_str "1RB0LC_1LC0LF_1LA1LD_1RE---_1RF0RE_1LB0RE") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1469: halts_at_trans (TM_from_str "1RB0LF_0LC0RE_0LD1LD_1LA0RA_0RA1RE_1LB---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1470: halts_at_trans (TM_from_str "1RB1LE_1RC0RD_1LD0RE_---0LA_0LF0RA_1RB0LA") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1471: halts_at_trans (TM_from_str "1RB1RE_1LC---_1RE0LD_1LC1LD_0RA1RF_1RE0RC") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1472: halts_at_trans (TM_from_str "1RB1LB_0RC1RC_1LC1RD_1RE1LD_1RF0LE_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1473: halts_at_trans (TM_from_str "1RB1LA_0LC0RE_0LF0LD_1LE1LC_1RA1RE_---0LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1474: halts_at_trans (TM_from_str "1RB0RD_1LC0LB_0RA0LB_1RE---_0RF1RD_1RA1RB") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1475: halts_at_trans (TM_from_str "1RB0RA_0LC0LF_1LE1LD_0LC0LB_1RA1LC_---0RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1476: halts_at_trans (TM_from_str "1RB0LC_1RC1RF_1RD0LB_1LE1RC_1LA0LE_0RB---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm1477: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LB1LE_1LF0LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1478: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RB1LD_1RE0LD_0RF1LE_---0LB") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1479: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_1LF1RB_---1RC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1480: halts_at_trans (TM_from_str "1RB0RD_1LC1RB_1RD0LB_1LC1RE_1RF0RA_---0RA") c0 (F,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm1481: halts_at_trans (TM_from_str "1RB0LA_0RC1LE_1RD1RF_1LB0RB_0LA1RF_---1RA") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm1482: halts_at_trans (TM_from_str "1RB1LC_1LA0RE_1LD---_1LA0LF_1RF0RB_0LF1LB") c0 (C,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1483: halts_at_trans (TM_from_str "1RB0LA_0LC1LB_1RD1LA_0RE0RD_1RF1RD_0LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1484: halts_at_trans (TM_from_str "1RB---_1LC0LA_1LD0LB_1RE1LC_1RF0RE_1LC0RC") c0 (A,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1485: halts_at_trans (TM_from_str "1RB0RD_1LC1RB_1RD0LB_0RF1RE_0LA0RA_---1LB") c0 (F,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm1486: halts_at_trans (TM_from_str "1RB0LD_1LC1RF_1LD0LC_1RE0LB_0RA0RD_1RD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1487: halts_at_trans (TM_from_str "1RB0LC_1RC0RE_1LD1RB_1LA0LD_1RA0RF_0RB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1488: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_1LA0RC_0LC0LE_0RB---_0RA0RE") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1489: halts_at_trans (TM_from_str "1RB0RA_0LC0LE_1RA1LD_1LE1LF_0LC0RC_0LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1490: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_1LD1RE_1LA0LD_0RD1RF_0LD---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1491: halts_at_trans (TM_from_str "1RB0LB_1RC0RB_0LD1RB_1LF1LE_0LA1LD_0LA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1492: halts_at_trans (TM_from_str "1RB0LD_0RC1RA_1RD1RF_1LA1LE_1RB0LA_0RD---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1493: halts_at_trans (TM_from_str "1RB0RE_1LC0RB_0LA0LD_1LE1LF_1RB1LC_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1494: halts_at_trans (TM_from_str "1RB0LC_1RC1RF_0LD---_0LE1LD_1RF0LA_0RB0RF") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1495: halts_at_trans (TM_from_str "1RB1RA_0RC1LE_1LD1RC_0LA0LF_---1LF_0LE0LA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1496: halts_at_trans (TM_from_str "1RB1RF_0LC0RC_1RE1LD_1LB0LB_0RA0RE_---0RE") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1497: halts_at_trans (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1LA0LE_0LF1LD_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1498: halts_at_trans (TM_from_str "1RB1LD_1RC1LB_1LA0RF_---1LE_0RF0LB_1RA1RF") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1499: halts_at_trans (TM_from_str "1RB0RE_1RC0RB_1LD1LC_1RE0LC_0RF1RA_---0LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1500: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LE_0LF1LA_0RA---") c0 (F,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1501: halts_at_trans (TM_from_str "1RB0RE_1RC1RF_1RD0LB_1LE0RA_1LC0LE_1RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1502: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1RD1RE_1LD0LA_1LF0RD_---0LE") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm1503: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_0RF1LD_1RA0LE_0RB1LC_---0LD") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1504: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_0RE---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1505: halts_at_trans (TM_from_str "1RB0RD_0RC0RE_1LD1RD_0LE0RF_1RA0LD_1LD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1506: halts_at_trans (TM_from_str "1RB1LA_1RC1RB_1LC0RD_1RF0LE_1LD0LA_---1RA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1507: halts_at_trans (TM_from_str "1RB---_1LC0RB_0LE1LD_1RB0LF_0RD0LA_0LD1LB") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1508: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD1LF_1LD0RA_1LB0LF_1LA---") c0 (F,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm1509: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1RA---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1510: halts_at_trans (TM_from_str "1RB0RA_0LC0LE_1RA1LD_1LE0LF_0LC0RC_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1511: halts_at_trans (TM_from_str "1RB0LC_1RC---_0LD1RF_1LA1LE_0LA1RF_0RF1RD") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1512: halts_at_trans (TM_from_str "1RB0RE_1RC0RF_1LD0LD_1RA0LA_1LC1RE_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1513: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1LE0LF_0LA0RA_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1514: halts_at_trans (TM_from_str "1RB1LE_1LC0RD_1LA1LB_1RD1RC_0LB0LF_0LD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1515: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1RD1LB_0RA1LE_1RF0LC_0RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1516: halts_at_trans (TM_from_str "1RB0LE_1LC0RC_0RF0RD_1LA1RD_1LA1LE_---1LB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1517: halts_at_trans (TM_from_str "1RB0LE_0LC0RD_1LD0RC_1LA1RC_1LF---_1LB1LB") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1518: halts_at_trans (TM_from_str "1RB0LE_1LC0RB_0RD0LD_1LA1RB_1RB1LF_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1519: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1RE0LF_0LA1LE_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1520: halts_at_trans (TM_from_str "1RB---_1LC0RD_1RE0LD_1RC1LF_0LD1RA_1RE0LC") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1521: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1RD1LF_1LA0RD_0LD0LC_1LD---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1522: halts_at_trans (TM_from_str "1RB0LC_1RC1RD_1LA0RB_0RE---_1LE1RF_1LF0LA") c0 (D,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1523: halts_at_trans (TM_from_str "1RB1LC_1LA---_1LD1RD_1RE0LA_0RA0RF_1RD0RC") c0 (B,1).
Proof. solve_halt 17. Time Qed.

Lemma tm1524: halts_at_trans (TM_from_str "1RB---_1RC1LF_1RD0RD_0RE1RB_1LF1RA_0LB0LF") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1525: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_1RD0LC_0LA0RA_1LC0RF_1LD---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1526: halts_at_trans (TM_from_str "1RB1LD_1RC0LA_0LA0RB_0LA1LE_1LF0RE_0LB---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1527: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_0RA1LD_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1528: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_1LE0LD_1RA1LD_0LA0LD_---1LB") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm1529: halts_at_trans (TM_from_str "1RB0LD_1RC1RD_0RD1RC_1LA1LE_1RF0RB_---1RE") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1530: halts_at_trans (TM_from_str "1RB0LA_0LC1RC_1RD1LA_0RE---_1RF0LC_1LA0RB") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1531: halts_at_trans (TM_from_str "1RB1RC_1LC0RE_1LD1RA_0LF1LB_0RA0LC_0LE---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm1532: halts_at_trans (TM_from_str "1RB0RA_0RC1RD_1LD0LC_1LE1RF_1RA1LA_---1LC") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1533: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_0RD1LD_1RE0LF_---0LF_1RA1LC") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1534: halts_at_trans (TM_from_str "1RB---_0RC0LC_1LD1RF_0LE0LD_0RA1LD_1RB1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1535: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_0LD1LE_1LC1RF_1LA---_1LD0RF") c0 (E,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1536: halts_at_trans (TM_from_str "1RB0LA_1RC0RE_0RD---_1LA0RA_0RF0LD_1LD0LB") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1537: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_1RD0LD_1LE0RB_0LE0LA_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1538: halts_at_trans (TM_from_str "1RB0LD_0LB1RC_1RD---_1LE0RE_0LF0LA_0RA1LF") c0 (C,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1539: halts_at_trans (TM_from_str "1RB0RA_0RC0RE_0LD---_1LE1LC_1LF0LD_1RA1LE") c0 (C,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1540: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_0LF0LB_0RA---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1541: halts_at_trans (TM_from_str "1RB0RD_1RC1RF_0LD0LE_1LC1RD_1RA1LE_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1542: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_1LE---_1LF0LD_0LA1LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1543: halts_at_trans (TM_from_str "1RB0LD_1LC0RF_---1LD_0LE0LB_1LF1LA_1RB1LA") c0 (C,0).
Proof. solve_halt 5. Time Qed.

Lemma tm1544: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RE1LD_0LB0LF_1LD0RA_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1545: halts_at_trans (TM_from_str "1RB0LD_1RC---_1LA0RF_1LB1LE_0LA1RE_0RE0RD") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1546: halts_at_trans (TM_from_str "1RB1RD_1LC1RA_1LE1LD_0RB0RC_1RB0LF_---0LB") c0 (F,0).
Proof. solve_halt 13. Time Qed.

Lemma tm1547: halts_at_trans (TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1RE---") c0 (F,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1548: halts_at_trans (TM_from_str "1RB0RF_1RC1RA_1LD---_0LE1LD_1LA0LD_1RD0RE") c0 (C,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1549: halts_at_trans (TM_from_str "1RB---_1RC0RF_1LD0RB_0LA0LE_1LD1RC_0RE0RB") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1550: halts_at_trans (TM_from_str "1RB0LC_1RC0RF_1LD0RD_0LE0LA_0RA1LE_0LA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1551: halts_at_trans (TM_from_str "1RB0RD_1RC1RF_1LA0RB_1RA0LE_1LD0LE_1LD---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1552: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1RD1RE_1LD0LA_0LF0RD_---1LB") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm1553: halts_at_trans (TM_from_str "1RB0RF_0RC1RE_1LD0RB_0LE0LD_1RA1LD_0LE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1554: halts_at_trans (TM_from_str "1RB0RA_1LC0LF_1LA1LD_1LE---_0LB0RC_0RA1RF") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1555: halts_at_trans (TM_from_str "1RB1LD_1RC0RE_1RD1LC_1RE0LD_1LF0RA_---1LD") c0 (F,0).
Proof. solve_halt 15. Time Qed.

Lemma tm1556: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_1LE---_1RF0LE_0LA1LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1557: halts_at_trans (TM_from_str "1RB0RD_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1RE---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1558: halts_at_trans (TM_from_str "1RB0RF_0LC1RA_1RD1LC_0RC0RE_1LA1RE_---1LB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1559: halts_at_trans (TM_from_str "1RB0RF_0LC1RA_1RD1LC_1RD0RE_1LA1RE_---1LB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1560: halts_at_trans (TM_from_str "1RB---_1LC0RA_0RD1RC_1LE1RB_0LF0LE_1RC1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1561: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_1LA---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm1562: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA1LD_1RD0LF_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1563: halts_at_trans (TM_from_str "1RB0LE_0LC---_1RE1LD_1LC0LA_1RF0RE_1RB0RD") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1564: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA1LD_0LF0RA_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1565: halts_at_trans (TM_from_str "1RB0RA_0RC1RC_1RD1RF_1LE0LD_1LA0LD_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1566: halts_at_trans (TM_from_str "1RB1LB_1RC0RB_0RD1RE_1LE0LD_1LA1RF_---1LD") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1567: halts_at_trans (TM_from_str "1RB1LD_1LC1RE_0RA0LB_1LA0LF_0RB0RC_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1568: halts_at_trans (TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC0LF_1RA1LC_1RD---") c0 (F,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1569: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_---1LD_1LE1RA_1LF0RD_1RD0LB") c0 (C,0).
Proof. solve_halt 15. Time Qed.

Lemma tm1570: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1RA1RD_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1571: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LD_1LE1RB_0LF0LE_0RA1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1572: halts_at_trans (TM_from_str "1RB0LC_0LC---_0LE1LD_1RE0RD_1LF0RD_0LA1LB") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1573: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_1LC1RE_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1574: halts_at_trans (TM_from_str "1RB---_1LC0RC_1LE0LD_1LC0LA_1RF1LC_1RB0RF") c0 (A,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1575: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_0RD0LF_1LE0LF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1576: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0LB_0RA0RF_1LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1577: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LD_1LE1RB_1LF0LE_1RC0RC") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1578: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RA1LD_0LB0LF_1LD0RA_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1579: halts_at_trans (TM_from_str "1RB0LD_0RC0RE_1RD1LC_1LA1LF_1RF---_0RA0RF") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1580: halts_at_trans (TM_from_str "1RB1LB_1RC0LA_1RD1RE_1LB0RF_0RB0LB_1LB---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1581: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RA1LD_0RE0LE_---1LC_1RB1RA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1582: halts_at_trans (TM_from_str "1RB---_1RC1LF_1LD0RC_0RE0LE_1LB1RC_0LE0LA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1583: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA0RA_0LF0RE_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1584: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LC1LD_1LE1RD_0RC0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1585: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_---1LA_1RA1LE_1RF0LF_0RE1LB") c0 (C,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1586: halts_at_trans (TM_from_str "1RB---_1RC0LF_1RD0LD_0RE0RA_1RF0RE_1LB0LF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1587: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1LB0LA_0RF0RE_1RB1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1588: halts_at_trans (TM_from_str "1RB0LE_0RC1RD_1LA0RA_1RC1RF_0LA1LA_0LA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1589: halts_at_trans (TM_from_str "1RB0RF_1RC1RE_0RD0RA_1LA---_0LF1LF_1LB0LE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1590: halts_at_trans (TM_from_str "1RB0LA_1RC0LC_1LD1RE_1LB0LD_0RA1RF_0RD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1591: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD0RD_1RA1LB_1LF0RD_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1592: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_0LF1RF_0RA---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1593: halts_at_trans (TM_from_str "1RB1RF_0RC0RB_1RD0LE_1RE0RA_1LC0LE_0RC---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1594: halts_at_trans (TM_from_str "1RB0RC_1RC1RE_1LD1RA_0LE0LD_1RF0RC_1RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1595: halts_at_trans (TM_from_str "1RB0RA_0RC0LD_1LD0LF_0LE0RE_1RA1LC_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1596: halts_at_trans (TM_from_str "1RB0RF_0RC0LA_1LD1RA_0LE0LA_0RB0LD_1RB---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1597: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD1RB_0LA1LD_1RC0LF_0LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1598: halts_at_trans (TM_from_str "1RB0RF_1RC1LC_1RD0LC_1LB1LE_1LA1RE_---1RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1599: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1RD1LB_0RA1LE_0RF0LC_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1600: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1LD0LD_0LA0RA_1LD0LF_1RD---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1601: halts_at_trans (TM_from_str "1RB---_0LC0RB_1RF0LD_1LE1LB_1LF0LD_1RD0LA") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1602: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LF1LD_1LE---_1RF1LB_1LA0LF") c0 (D,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1603: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE1RF_1RA0RB_1LA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1604: halts_at_trans (TM_from_str "1RB1LD_0LC0RF_0LE0RD_1LB---_1LA0LF_0RA0RF") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1605: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_1LD0RA_0LE0LC_0LA1LE_0RD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1606: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD0RE_0LA0LD_1LA0RF_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1607: halts_at_trans (TM_from_str "1RB0LC_1LC0RA_1LA1LD_0LE---_1RE1LF_1RF0RB") c0 (D,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1608: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD1RA_0RE0RD_1RF0RD_1LB0LF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1609: halts_at_trans (TM_from_str "1RB0LF_1LC0RD_0RE1LD_0LC1RE_1RA0LC_---1LA") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1610: halts_at_trans (TM_from_str "1RB---_0RC0RB_1RD0LF_0RE0RA_1RF0RB_1LC0LF") c0 (A,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1611: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LA0RB_0LC1LE_0RA---_0LE0LE") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1612: halts_at_trans (TM_from_str "1RB1LD_0RC1RC_1LC1RD_1RE1LA_1RF0LE_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1613: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_0RD0RF_0LE0LA_1LD1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1614: halts_at_trans (TM_from_str "1RB0LE_1RC0LE_0RD0LD_1RE0RA_1LB1RF_0LB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1615: halts_at_trans (TM_from_str "1RB0LD_1RC1RF_1RD0LE_1LA0LC_1LA0RA_1RA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1616: halts_at_trans (TM_from_str "1RB0LD_1LB1LC_1RD0LC_0RF1RE_---1RF_0RB0RA") c0 (E,0).
Proof. solve_halt 10. Time Qed.

Lemma tm1617: halts_at_trans (TM_from_str "1RB0RC_1LC0RE_1RA1LD_0LC0LA_0RF1LC_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1618: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA1RF_1RA0LD_0LE---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1619: halts_at_trans (TM_from_str "1RB0LD_1LC1RF_0RA1RD_1LE1LA_1RA1RE_0RC---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1620: halts_at_trans (TM_from_str "1RB---_1LC0RE_0LD0LB_0RA0RF_0RD1RF_0LC0RB") c0 (A,1).
Proof. solve_halt 7. Time Qed.

Lemma tm1621: halts_at_trans (TM_from_str "1RB0LE_0LB0RC_1RD1RE_1LA1RF_1LD1LB_---0RB") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1622: halts_at_trans (TM_from_str "1RB0LC_1LA1RB_1RD1LC_0LC1RE_1RF0RB_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1623: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_1RD0LC_0LA0RA_1LC1RF_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1624: halts_at_trans (TM_from_str "1RB0LA_1LC1LE_1LA0LD_1LB0RF_---1RF_0RD1RF") c0 (E,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1625: halts_at_trans (TM_from_str "1RB1LC_1LC0RF_---1LD_0LE0LA_0LF0LE_1LA1RF") c0 (C,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm1626: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0RA_1RE0RF_1LF0LE_0LB0LE") c0 (A,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1627: halts_at_trans (TM_from_str "1RB1LB_1LA1LC_1RD0LC_1RE1LF_0RD1RB_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1628: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA0RA_1LD1LF_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1629: halts_at_trans (TM_from_str "1RB1RE_0RC0RF_1LD0RD_1LE1RE_1RA0LE_---1LB") c0 (F,0).
Proof. solve_halt 17. Time Qed.

Lemma tm1630: halts_at_trans (TM_from_str "1RB---_0RC0RF_0RD0RA_1LE1RF_1LF0LD_1RB0LE") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1631: halts_at_trans (TM_from_str "1RB0LF_1LC0RE_1LA1LD_0LC---_0RB1RE_1LF0LB") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1632: halts_at_trans (TM_from_str "1RB1LC_0RC---_1LD1LE_1LE1LA_1RF0LA_0LE0RF") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1633: halts_at_trans (TM_from_str "1RB0LF_1LC1RB_0LE1RD_1LE0RC_1LA1LD_1LE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1634: halts_at_trans (TM_from_str "1RB0LD_0RC0RF_1LC0RA_1LE---_1LF0LD_1RB0LE") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1635: halts_at_trans (TM_from_str "1RB0RF_0RC0LE_0LD1RB_1LE1LD_0LA0RA_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1636: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RE0LD_0LC0LF_1RA0RE_0LA1RA") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1637: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_1RD0LC_0LA0RA_1LC1RF_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1638: halts_at_trans (TM_from_str "1RB0RF_1LC0LB_0RD0LB_1RF1RE_1RC---_0RA1LF") c0 (E,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1639: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1LA0LF_1RA---_1LC0LA") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1640: halts_at_trans (TM_from_str "1RB0LA_0RC1RD_0LD0RE_1LA0RF_1LA---_0RD1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1641: halts_at_trans (TM_from_str "1RB1LD_1LC0LC_1RA1LB_1RE0RA_0RF0RD_1RA---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm1642: halts_at_trans (TM_from_str "1RB1RF_1RC0RE_1LD0LC_1LA1LC_---1LF_0RA1RA") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1643: halts_at_trans (TM_from_str "1RB1LF_1RC0LA_1RD1RB_1LE0RC_---1LD_1LC1RD") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1644: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_0LE1RF_0RA---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm1645: halts_at_trans (TM_from_str "1RB0LD_0RC1RA_1LD1RB_1LE1LA_---0LF_1LB1RD") c0 (E,0).
Proof. solve_halt 16. Time Qed.

Lemma tm1646: halts_at_trans (TM_from_str "1RB---_0RC0RB_1LD1RB_0LE1LD_1RB0LF_1RC0LA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1647: halts_at_trans (TM_from_str "1RB---_0RC0LE_1RD1RA_1LB1RC_1LD1LF_1RB0LF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1648: halts_at_trans (TM_from_str "1RB1LF_1RC0RD_1RD1RA_1LE0RC_---1LC_1RC0LF") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm1649: halts_at_trans (TM_from_str "1RB1RA_0RC0LC_1LD0LF_0LE0RB_0RA1LD_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1650: halts_at_trans (TM_from_str "1RB1LD_1RC0RD_0LD1RA_0RF1LE_1RF0LA_---0LA") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm1651: halts_at_trans (TM_from_str "1RB0LC_1LC0RE_1LD1LB_1LA1RA_1RF0RA_---1RE") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1652: halts_at_trans (TM_from_str "1RB1LA_1RC0RD_1LA0RF_1LE1RD_1LE0LA_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1653: halts_at_trans (TM_from_str "1RB1LC_1LC0RF_0LE0LD_0LC---_1LA0RB_1RE0RF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1654: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RF0LD_1RE1LC_1LD0LF_---1RA") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm1655: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD0RE_0LA0LD_1LA0RF_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1656: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD---_1LE1LA_1RF1LD_1RA0RD") c0 (C,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1657: halts_at_trans (TM_from_str "1RB0LC_1LC1RE_1RF0LD_1LA0LD_0RA0RC_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1658: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_0LD0LB_1LE0RB_1RA1LF_1LB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1659: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_1RA1LD_1LE0LF_0LC0RC_1RE---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1660: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RF_0LA0RA_1LD0LD_---0RB") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1661: halts_at_trans (TM_from_str "1RB0LB_1RC0LE_1LD1RB_1LA0LD_1RB1RF_0RE---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1662: halts_at_trans (TM_from_str "1RB1RB_1RC0RA_1LD0RB_1RB1LE_0RE1LF_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1663: halts_at_trans (TM_from_str "1RB1LE_0RC0LB_1LD1RC_1LB0RE_---1RF_1RA0RE") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1664: halts_at_trans (TM_from_str "1RB0LF_0RC---_0RD1RC_1LE0RE_0LA0LB_0RD1LE") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1665: halts_at_trans (TM_from_str "1RB0RF_1LC1LB_1RD0LB_0RA1RE_1RD0RC_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1666: halts_at_trans (TM_from_str "1RB1LA_1RC1RD_1LC0LA_1RE0RF_---0RB_1LC1RF") c0 (E,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm1667: halts_at_trans (TM_from_str "1RB1RD_0RC---_1RD0RE_1LE0RA_0LF0LE_1RB0LC") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1668: halts_at_trans (TM_from_str "1RB---_1LC0RB_0LE1LD_1RB0LF_0RA0LA_0LD1LB") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1669: halts_at_trans (TM_from_str "1RB1RE_1LC1RF_1RA0LD_1RC1LC_0RC0LC_1RE---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1670: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0RD0RF_1LE1RA_1LA0LD_1RB---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1671: halts_at_trans (TM_from_str "1RB1RE_1LC1RF_1RA0LD_1LC0LD_0RA0RD_0RB---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1672: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RD0LB_0RA0LA_1RF---_1RD0RC") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1673: halts_at_trans (TM_from_str "1RB1RF_1LC---_1LD0LB_0LE1LD_1RF1LC_0RA0RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1674: halts_at_trans (TM_from_str "1RB1RA_1LC0RD_1RA1LB_1RE1RB_0LF1RC_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1675: halts_at_trans (TM_from_str "1RB0RC_1RC---_1LD1RD_1LE0RA_1LF1LD_0LA0LE") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1676: halts_at_trans (TM_from_str "1RB0RE_1LC0LE_1RE0LD_1LB---_1LB0RF_1LE0RA") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1677: halts_at_trans (TM_from_str "1RB---_1LC0RF_1LE1LD_0LB0RB_1RB0LA_1LB1RB") c0 (A,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1678: halts_at_trans (TM_from_str "1RB0LF_0LC1RD_1RF1LA_1RE---_1LF0RC_1RB0LC") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1679: halts_at_trans (TM_from_str "1RB1RE_0RC0RF_1LD0RD_1LE1RE_1RA0LE_---0RD") c0 (F,0).
Proof. solve_halt 17. Time Qed.

Lemma tm1680: halts_at_trans (TM_from_str "1RB0LD_1RC0LF_1LA0RE_0RA1LE_0LD1RA_---1LB") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1681: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD0RD_1RA1LB_0LF0RD_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1682: halts_at_trans (TM_from_str "1RB0LB_1RC0LF_1LD1RE_1LE0LD_0RB0RA_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1683: halts_at_trans (TM_from_str "1RB0LC_1LA0RE_0RD1LB_1RA1RC_0RD1RF_0RA---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1684: halts_at_trans (TM_from_str "1RB0RD_1RC0RF_0LA1LF_0LE1RA_1LC---_1RD1LC") c0 (E,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1685: halts_at_trans (TM_from_str "1RB1LD_0LC0RF_1LA0RD_1LE---_0LB0RB_0RA0RF") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1686: halts_at_trans (TM_from_str "1RB0LE_1LC0RB_0RD0LD_1LA1RB_1RF0LF_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1687: halts_at_trans (TM_from_str "1RB---_0LC0LD_1RF1LA_1LB0RE_1RD0RF_1RE0LC") c0 (A,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1688: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA0RA_1LD0LF_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1689: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1RB0LA_0RF0RE_0LA1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1690: halts_at_trans (TM_from_str "1RB0LA_1RC---_1LD0RD_1RF0LE_1LA0RC_1RE0RD") c0 (B,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1691: halts_at_trans (TM_from_str "1RB1RD_0LC1RE_0RD1LC_1RA1LE_0RF0LD_---1RD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1692: halts_at_trans (TM_from_str "1RB0RB_1LC1RA_1LA1RD_1LE0LC_0LF0LD_1LC---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm1693: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1LB0LF_1RD0RE_1LA0RC") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1694: halts_at_trans (TM_from_str "1RB1RE_0LC1LB_1RE1LD_1LB0LF_0RA0RE_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1695: halts_at_trans (TM_from_str "1RB1LA_1LC0RD_1LA0LC_1RE1RF_---0RB_0RC1RA") c0 (E,0).
Proof. solve_halt 5. Time Qed.

Lemma tm1696: halts_at_trans (TM_from_str "1RB1RF_0RC0RF_1LD1LE_0LE---_0LF0LC_1RA0RD") c0 (D,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1697: halts_at_trans (TM_from_str "1RB1RF_1LC0RE_1RE0LD_0LC1RB_1RA0RD_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1698: halts_at_trans (TM_from_str "1RB---_1LC1LD_1RE0LD_0LB1LD_1RF0RC_0RA0RB") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1699: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1LB0LA_0RF0RE_1RA1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1700: halts_at_trans (TM_from_str "1RB1RA_1RC0RF_1LD0LC_0RA1LE_1RF1LC_---0RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1701: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RA0LD_0LC1LD_1RF0RC_1LF1RE") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1702: halts_at_trans (TM_from_str "1RB1LF_1LC---_0RD1RC_1LD1RE_1RC0RA_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1703: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_0RD0LC_0LB1RE_0RA1RF_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1704: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0LD1RB_0RE---_1RF0LC_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1705: halts_at_trans (TM_from_str "1RB0RE_0RC0RF_1RD1RE_1LE0LD_1RA0LD_0RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1706: halts_at_trans (TM_from_str "1RB0RB_1LC0RF_1LA0RD_0LB0LE_1LD---_1LE0RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1707: halts_at_trans (TM_from_str "1RB0LC_1RC1RD_1LA0LC_0RE---_0RF0LB_0RA1RF") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1708: halts_at_trans (TM_from_str "1RB1LC_0LA1RB_1LA0RD_1LE1RC_1LF1LB_---0LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1709: halts_at_trans (TM_from_str "1RB0LC_1RC0RD_1LA0LC_1RE0RE_0RA0RF_0RA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1710: halts_at_trans (TM_from_str "1RB0LB_1RC0LB_0RD---_1LD1RE_0RF1LA_1RA0LB") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1711: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_0RA---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1712: halts_at_trans (TM_from_str "1RB---_1LC0RF_1LE0LD_0LC0LE_1RB0LF_1RE0RA") c0 (A,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1713: halts_at_trans (TM_from_str "1RB0LD_1LC0RF_0LD0LC_1RE1RB_0RA---_0LD1RD") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1714: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_0RD1RA_1LE0RC_0LA0LE_1RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1715: halts_at_trans (TM_from_str "1RB0RE_1LC0RF_0RE0LD_0LC0LB_1RA0LF_1RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1716: halts_at_trans (TM_from_str "1RB---_1LC0LF_1RD0LC_0RE1RA_0LB1RF_0RD0RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1717: halts_at_trans (TM_from_str "1RB1RF_0RC1RA_1RD0RA_1LE0LD_0RB0LD_0RE---") c0 (F,1).
Proof. solve_halt 7. Time Qed.

Lemma tm1718: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD---_1RE1RD_0RF1LD_1LF1RA") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1719: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_1RD1RB_0LE---_0LA1LE_1RC0LD") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1720: halts_at_trans (TM_from_str "1RB---_1LC1LD_0LF1LA_1RE0LE_0RB0RE_1LD0LC") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1721: halts_at_trans (TM_from_str "1RB1RE_0LC0RC_1RE1LD_1LB0LF_0RA0RE_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1722: halts_at_trans (TM_from_str "1RB0LC_0RC0RE_1LD1RB_0LA1LD_0RF0RA_0RA---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1723: halts_at_trans (TM_from_str "1RB1RD_1RC1RA_1LA0LC_0LE0RD_1LF---_0LC1LF") c0 (E,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1724: halts_at_trans (TM_from_str "1RB0LD_1RC1RF_1LA0RE_1RB1LE_0LA0RD_---0LC") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1725: halts_at_trans (TM_from_str "1RB1LB_1LC0RB_1LD1LB_0LE0LF_1RA0LA_---1RD") c0 (F,0).
Proof. solve_halt 17. Time Qed.

Lemma tm1726: halts_at_trans (TM_from_str "1RB1RE_0LC0RA_0LE0RD_1LC1RA_1RF0LD_1RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1727: halts_at_trans (TM_from_str "1RB1RE_1LC0LB_1RD1LB_0RE1RD_1RF0RB_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1728: halts_at_trans (TM_from_str "1RB0LB_1LC0RD_1LA0RA_0LC0RE_0RF---_1RC1RF") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1729: halts_at_trans (TM_from_str "1RB0RC_1LA1RA_---0RD_1LE1RD_1LB1LF_0LB0LE") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1730: halts_at_trans (TM_from_str "1RB1LE_1RC1RE_1LD1LA_---0LA_0RB0LF_1LC1LA") c0 (D,0).
Proof. solve_halt 10. Time Qed.

Lemma tm1731: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_0LD1LA_0RA1LE_1LA---_0LA1LB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1732: halts_at_trans (TM_from_str "1RB1RA_0LC0RE_0LD1LC_1LE1LB_1LF0RD_0RA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1733: halts_at_trans (TM_from_str "1RB1RF_1RC0RD_1LD1LF_1RE1LD_---0LA_1RA0LC") c0 (E,0).
Proof. solve_halt 16. Time Qed.

Lemma tm1734: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_0LF1RB_---1RD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1735: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA0RA_1LD0LF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1736: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0RD---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1737: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_0LE1RB_1LF1RE_0RD0LF") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1738: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1LD0LD_0LA0RA_1LD0LF_1LE---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1739: halts_at_trans (TM_from_str "1RB1RD_0RC1RC_1LC1RD_1RE1LD_1RF0LE_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1740: halts_at_trans (TM_from_str "1RB1RF_0RC1RB_1LD1RA_0LE0LD_1RB1LD_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1741: halts_at_trans (TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_0LD---") c0 (F,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1742: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1RB1RD_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1743: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD1RA_1LA0LB_1LD1LF_1LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1744: halts_at_trans (TM_from_str "1RB0LF_1LC1RB_1LA0LD_1RE1LD_0RD0RB_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1745: halts_at_trans (TM_from_str "1RB1LE_1RC1RC_0RD0RB_1LE0LA_0LF1LA_---1LD") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1746: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_1RE1LD_0LB0LF_0LB0RF_1RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1747: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LC---_1LF0LA_1LA0LB") c0 (D,1).
Proof. solve_halt 17. Time Qed.

Lemma tm1748: halts_at_trans (TM_from_str "1RB0LC_1RC0LC_0LD1RF_---1LE_1RC1LB_0RA1RA") c0 (D,0).
Proof. solve_halt 10. Time Qed.

Lemma tm1749: halts_at_trans (TM_from_str "1RB1LB_0RC0LF_1LD0RB_1LE0LB_0LA0LC_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1750: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1RB_1LE---_0LA1LE_1LE0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1751: halts_at_trans (TM_from_str "1RB0RD_0RC1RA_1LD---_1RE0RF_0LF1LE_1LA0LE") c0 (C,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1752: halts_at_trans (TM_from_str "1RB0LC_1LC0RB_0RD1LD_1LE1RB_0LF---_1LA0RD") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1753: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_1RF1LD_1RA0LE_1RA1LC_---1RB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1754: halts_at_trans (TM_from_str "1RB0RF_0LC1RE_1LD1RC_0LE1LA_1RA0RC_---0LD") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm1755: halts_at_trans (TM_from_str "1RB0LB_1RC1LD_1RD0LF_1LE0RC_---1LC_1RC1LA") c0 (E,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1756: halts_at_trans (TM_from_str "1RB---_0RC1LC_1RD0LF_1RE0RA_1LC0LB_1RB0LE") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1757: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_0LF1RF_0RD---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1758: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE0LF_0RF0LE_0LD1RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1759: halts_at_trans (TM_from_str "1RB1LE_1RC1LB_0RD0RD_1LA1RD_1LF0LB_---0LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1760: halts_at_trans (TM_from_str "1RB1RA_0RC---_1RD0RE_1LE0RA_0LF0LE_1RB0LC") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1761: halts_at_trans (TM_from_str "1RB0RF_1LC0LB_0RD0LB_1RF1RE_1RC---_0RA0LB") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1762: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE1LF_0LA0RA_1RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1763: halts_at_trans (TM_from_str "1RB1LB_1LA0LC_---1LD_1RE0LD_1RF1RA_0RE0RA") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1764: halts_at_trans (TM_from_str "1RB1RC_1LC---_1RF1LD_1RD0LE_0LA1LC_1RA0RC") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1765: halts_at_trans (TM_from_str "1RB1LA_1RC0RD_1LA0RF_1LE1RD_0LD0LA_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1766: halts_at_trans (TM_from_str "1RB---_1LC0RE_1RA1RD_0LD1LE_1RF0LE_0RD0RC") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1767: halts_at_trans (TM_from_str "1RB0RA_1LC0LF_1LA1LD_1LE---_0LB1LE_0RA1RF") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1768: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA0RF_1LD---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1769: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD0LC_1RE0LD_0RF---_1LF1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1770: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_1LD0RD_0RE1LD_---1LA_0RB1LA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1771: halts_at_trans (TM_from_str "1RB0RC_0LC1RF_0RE1LD_1RE0LF_---0LF_1RA1LC") c0 (E,0).
Proof. solve_halt 5. Time Qed.

Lemma tm1772: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1RD1LD_1LA1RD_1LF1LC_---0LB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1773: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1LE0LF_0LA0RA_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1774: halts_at_trans (TM_from_str "1RB1LC_1LA0RF_1LD---_0RE0LE_0LE1LB_1RE0RB") c0 (C,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1775: halts_at_trans (TM_from_str "1RB0LD_1RC1RB_1LA1LE_---1LA_1LC0RF_0LE1RE") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1776: halts_at_trans (TM_from_str "1RB0RC_1LA1RA_1LD1RC_---1LE_1LA0LF_1LA1LE") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1777: halts_at_trans (TM_from_str "1RB1LC_1LA1RE_0RD1LA_---0LB_0RA1RF_1RC0RB") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1778: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_0RD---_1RE0RE_0LF1RA_1RC1LE") c0 (C,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1779: halts_at_trans (TM_from_str "1RB1RA_1RC1RE_1LD1LE_---0LC_1LF0RB_0RA1LE") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1780: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA0RA_1LF0RA_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1781: halts_at_trans (TM_from_str "1RB1LD_1RC---_1LD0RD_1RE0LD_0RF0RA_0LF1LD") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1782: halts_at_trans (TM_from_str "1RB1LE_1LC0RD_1RB1LC_1LA1RD_1LF0LC_---1LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1783: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_0RD0RF_1RE1RA_1LA0LE_0RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1784: halts_at_trans (TM_from_str "1RB0RC_1RC1LB_1LD1RA_0LF1LE_---1LF_1RF0LB") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1785: halts_at_trans (TM_from_str "1RB0LA_0RC1LA_1RD1RE_1LB0RB_---1RF_1RC0RA") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1786: halts_at_trans (TM_from_str "1RB0LA_0LC1RC_1RD1LA_0RE---_1RF0LC_1LB0RB") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1787: halts_at_trans (TM_from_str "1RB1RF_0LC0RC_1LA1LD_1LE---_1LB0RF_1LE0RA") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1788: halts_at_trans (TM_from_str "1RB0LA_0RC1RF_0RD---_0LD1LE_1LA0RB_1RB0RF") c0 (C,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1789: halts_at_trans (TM_from_str "1RB1LF_0LC---_1LC1RD_1LE0RA_0RC1RE_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1790: halts_at_trans (TM_from_str "1RB0RB_1LC---_0LD1LC_1LE1RF_1RA0LE_1RD0RD") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1791: halts_at_trans (TM_from_str "1RB1LA_1RC0LD_0LA0RC_---1LE_1LF0LD_1LC0LD") c0 (D,0).
Proof. solve_halt 16. Time Qed.

Lemma tm1792: halts_at_trans (TM_from_str "1RB1RD_0RC---_1RD0LA_1LE0RF_0LA0LE_0LA1RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1793: halts_at_trans (TM_from_str "1RB1RE_1RC1LF_1RD0RC_1LE0LF_---1LD_1RA1LB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1794: halts_at_trans (TM_from_str "1RB0RF_1LC0LB_1RD1LB_1RE1RC_0RA0RE_---0RD") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1795: halts_at_trans (TM_from_str "1RB0RF_1RC1RA_1LD---_0LE1LD_1LA0LD_0LD0RE") c0 (C,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1796: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LA0LD_1RE0RB_1LF0LC_---1LE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1797: halts_at_trans (TM_from_str "1RB1LE_1LC1LE_1RD1LB_1RC1RA_1RF0LE_0RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1798: halts_at_trans (TM_from_str "1RB1LC_0LA1RD_1LA1LD_1LE0RD_1LB0LF_---0LB") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm1799: halts_at_trans (TM_from_str "1RB---_1RC1RC_1RD1LF_1RE1RA_1RF0RD_1LB0LC") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1800: halts_at_trans (TM_from_str "1RB0RE_1RC0LF_0RD0RA_0LE---_1LB0LF_0LE1LE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1801: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_1RA1LC_1RF0RE_1LB1RE_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1802: halts_at_trans (TM_from_str "1RB0LD_0LC1LB_1RC1LA_1LF1RE_0RD0RE_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1803: halts_at_trans (TM_from_str "1RB0LC_0RC0RE_1LD1RB_0LA1LD_1RF0RA_1LB---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1804: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_0LA1RD_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1805: halts_at_trans (TM_from_str "1RB1RF_1LC1RD_1LA1LC_---0RE_1LC1RB_1RE1RA") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1806: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_0RD1LD_0RE0LF_---1LF_1RA1LC") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1807: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_1LA0RE_0LA1LD_1RE0RA_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1808: halts_at_trans (TM_from_str "1RB0RF_0RC0LE_1LC1RD_0RA0LB_1LB1RC_1RA---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1809: halts_at_trans (TM_from_str "1RB0RF_1RC0RC_1RD0LC_1LE0RE_1RA1LC_---1RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1810: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RA1LD_1RE0LF_1RB1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1811: halts_at_trans (TM_from_str "1RB1LF_1RC0RA_1LD0RF_---1LE_0LA0LB_0RD1RB") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1812: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RE_0LC0LE_1LF0RB_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1813: halts_at_trans (TM_from_str "1RB1LC_1LA1RF_1RD0LA_---1RE_1LE1RB_1LC0RC") c0 (D,0).
Proof. solve_halt 16. Time Qed.

Lemma tm1814: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA0LC_0RA0RF_1RD0LC_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1815: halts_at_trans (TM_from_str "1RB---_1LC0RF_0LE1LD_1RC1RE_0RA0LB_1LB0RD") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1816: halts_at_trans (TM_from_str "1RB1LA_1LB0RC_1LD1RC_1LE0LA_---0LF_0LA1LC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1817: halts_at_trans (TM_from_str "1RB1RD_0RC---_1RD0LA_1LE0RF_0LA0LE_0LF1RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1818: halts_at_trans (TM_from_str "1RB1LF_1RC0RE_1RD1RA_1LE1LB_0RF1LE_---0LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1819: halts_at_trans (TM_from_str "1RB0RA_1RC0RE_0LD---_1RA1LE_1LD0LF_1RC0LA") c0 (C,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1820: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_1LA0LC_1LE0RD_0LF1RE_---0RA") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm1821: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA0LE_1LD0RF_0RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1822: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LA0RB_0LC1LE_0LC---_1RB1RB") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1823: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LE---_1RF0LE_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1824: halts_at_trans (TM_from_str "1RB0LA_0RC1RF_0LD1RE_1LA0RB_1RD0LC_0RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1825: halts_at_trans (TM_from_str "1RB1LC_1LC1RD_1LA0LB_0RB1RE_0RF0RA_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1826: halts_at_trans (TM_from_str "1RB0LF_1RC1RC_1RD---_1LE1LD_0RA0LD_1RF0RE") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1827: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1RB1LD_0LE1LF_1LC1RE_0RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1828: halts_at_trans (TM_from_str "1RB1LD_0RC1RF_1RD1RA_1RE0LD_1LA0RA_---0RD") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1829: halts_at_trans (TM_from_str "1RB1RE_1LC0LB_1RD1LB_---0LE_1RC1RF_0RA0RF") c0 (D,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1830: halts_at_trans (TM_from_str "1RB0RA_0RC1RC_1LD1RF_1LE---_1RA0LE_1RA1RE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1831: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1RD1RB_1RE0LF_0LA1LE_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1832: halts_at_trans (TM_from_str "1RB1RF_1LC0LD_1RB1LB_1RE1LD_---1RF_1RB0RA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1833: halts_at_trans (TM_from_str "1RB1LF_0RC---_0RD1RC_1LD1RE_1RC0RA_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1834: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD0LA_1RE0LA_1LB1RA_0LE0LF") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1835: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1RE0RF_0LA1LE_---1LC") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1836: halts_at_trans (TM_from_str "1RB1LF_1RC---_0RD1RC_1LD1RE_1LC0RA_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1837: halts_at_trans (TM_from_str "1RB1LC_0RC1LE_1RD0LA_1LB1RC_1LA0LF_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1838: halts_at_trans (TM_from_str "1RB1LD_0LC0RB_0RA1LC_0LE0LF_1LA0RF_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1839: halts_at_trans (TM_from_str "1RB0RF_1RC0LE_1RD0RA_1LE---_0LA1LE_1LF1RB") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1840: halts_at_trans (TM_from_str "1RB---_1RC1RA_1LD1RF_1RB0LE_1LF0LC_0RB1RD") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1841: halts_at_trans (TM_from_str "1RB0RC_1RC1RF_1LD1RC_1LD0LE_1RA1LE_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1842: halts_at_trans (TM_from_str "1RB1RF_1RC0LE_0RD0LD_1RE0RA_1LB1RF_0LB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1843: halts_at_trans (TM_from_str "1RB0LF_1LC0RE_1RD1LC_---0RB_1LE1LA_0LD1LC") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1844: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD1RE_0LA0LD_1LB0RF_1LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1845: halts_at_trans (TM_from_str "1RB1RF_1RC0RD_1LD0RF_---0LE_1LB1RC_1RA0LA") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1846: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1847: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1LD0RA_0LA0LC_0LF---_0LB1LB") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1848: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_---1LA_1RA1LE_1RF0LF_1RA1LB") c0 (C,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1849: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_1LF1LD_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1850: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_1LD1RC_1RB1LE_1LF0LA_---0LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1851: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_0LE0LD_1LB1RB_0RF0LE_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1852: halts_at_trans (TM_from_str "1RB---_1RC1LB_0RD1RD_1LE0RC_0LF1LA_0LE1LE") c0 (A,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1853: halts_at_trans (TM_from_str "1RB1RC_0RC1RE_1LD0RA_0LE0LD_0RA0RF_0LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1854: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_0RE1LF_0LC---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm1855: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_1LA0LC_0RA1RF_1RA0LA_1RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1856: halts_at_trans (TM_from_str "1RB1LE_1RC0RA_1RD1RA_1LA---_1RE0LF_0LC1LA") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1857: halts_at_trans (TM_from_str "1RB0LA_0LC1LB_1RD1LA_0RE0RD_1RF1RD_0LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1858: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LA0LF_0LA1LE_1LF---_0LB0RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1859: halts_at_trans (TM_from_str "1RB0RC_0LC0RD_1RD0LD_0RE1LF_1RA1LA_0LB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1860: halts_at_trans (TM_from_str "1RB0LD_1LC1RA_0RA1LB_1LE0RC_1LA0LF_0LA---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1861: halts_at_trans (TM_from_str "1RB0RE_0RC1RD_1LD0RF_1LA0RA_1RA0LF_0LB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1862: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD1LC_1RA1LB_1LF0RD_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1863: halts_at_trans (TM_from_str "1RB1RF_1RC---_0LD1LC_1RF1LE_1RC0LE_0RA0RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1864: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_1RB1LD_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1865: halts_at_trans (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0LD_1RB1RF_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1866: halts_at_trans (TM_from_str "1RB0LC_1LA---_1LD0LD_1RE1LC_0RA0RF_1RD0RD") c0 (B,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1867: halts_at_trans (TM_from_str "1RB1LF_1LB1RC_---1RD_1LE0RF_1RB0LA_0LE0RA") c0 (C,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1868: halts_at_trans (TM_from_str "1RB1LA_1LA0LC_0LF1LD_1RE1LB_0RC0RE_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1869: halts_at_trans (TM_from_str "1RB1RF_1LC1LF_1RD0LB_---1RE_0RA1RD_1LB0RA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1870: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_0LD1RB_1RE---_0LA0RA_1LE0LD") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1871: halts_at_trans (TM_from_str "1RB0LF_0RC---_0RD0LA_1RE1RA_1LA1LC_1RE1LD") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1872: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD---_1RE1RD_0RF1RD_1LF1RA") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1873: halts_at_trans (TM_from_str "1RB1LF_0LC---_1LC1RD_1RE0RA_0RC1RE_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1874: halts_at_trans (TM_from_str "1RB1RD_1RC0RF_1LA1LC_1LE1RD_---0LC_1RE0RA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1875: halts_at_trans (TM_from_str "1RB0LE_1RC1RF_1RD0LE_1LC---_1LA1LE_1RB0RA") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1876: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_1LF1LD_1LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1877: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD1RE_0LA0LD_1LB1RF_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1878: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_1LC---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm1879: halts_at_trans (TM_from_str "1RB1LF_1LC0RE_1LA0LD_0RC1LD_1RA1RE_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1880: halts_at_trans (TM_from_str "1RB0LF_1LC1RD_1LA1LB_0RB1LE_0LC0RB_0LD---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1881: halts_at_trans (TM_from_str "1RB0RE_1LC0LB_1RD1LB_---0RE_1RF1RE_0RA1RC") c0 (D,0).
Proof. solve_halt 12. Time Qed.

Lemma tm1882: halts_at_trans (TM_from_str "1RB1RE_0RC---_1LD1RC_1RC0RA_1LF1RD_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1883: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1RE1LC_1RA1RF_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1884: halts_at_trans (TM_from_str "1RB0LE_0RC1RA_1RD1RB_1LA---_1LF1LA_1RC1LF") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1885: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1LD0RA_1LB0LC_1LA0LF_1LD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1886: halts_at_trans (TM_from_str "1RB0RE_0RC1RA_1LD1LC_1LE0LC_0RF0RD_---1RB") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1887: halts_at_trans (TM_from_str "1RB0LE_0RC0RF_1RD0LA_1LA1RB_1LC0LE_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1888: halts_at_trans (TM_from_str "1RB1RC_0RC---_1LD0RF_0LD0LE_1RE1RC_0RB1RA") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1889: halts_at_trans (TM_from_str "1RB0RF_1RC0LE_0RD0RA_1LA---_0LF1LF_1LB0LE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1890: halts_at_trans (TM_from_str "1RB0RB_1LC1RF_1LE0LD_1LC0LD_1RA---_0RA0LA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1891: halts_at_trans (TM_from_str "1RB---_1LC1LE_1LD0LC_1LE1LB_1RF0LA_1RD0RF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1892: halts_at_trans (TM_from_str "1RB0RE_0RC0RD_1RD---_1LE1LF_1RA0LF_0LD1LF") c0 (C,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1893: halts_at_trans (TM_from_str "1RB1LC_0RC0RF_0LD0RA_1LE---_1RA0LE_1LF1RE") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1894: halts_at_trans (TM_from_str "1RB1RA_1LC0RD_1RA1LB_1RE1RB_0LF0RD_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1895: halts_at_trans (TM_from_str "1RB---_1LC0RE_1RA0LD_1LA1LF_0RF0RD_0LC1RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1896: halts_at_trans (TM_from_str "1RB1LE_1RC1RE_1LD0RA_---0LA_1RC0LF_1LD1LC") c0 (D,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1897: halts_at_trans (TM_from_str "1RB0RA_0LC0LF_1LE0RD_1LB---_1RA1LB_1LC0RC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1898: halts_at_trans (TM_from_str "1RB0LD_1RC1RB_1LA0RE_---1LE_1RF0LE_0LD0RA") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1899: halts_at_trans (TM_from_str "1RB1LF_0RC0RA_1LD1RB_0LE0RC_1LA0LC_1LD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1900: halts_at_trans (TM_from_str "1RB0LD_1RC0RB_1LA1LC_1LE0LE_1RC1RF_---0LC") c0 (F,0).
Proof. solve_halt 12. Time Qed.

Lemma tm1901: halts_at_trans (TM_from_str "1RB0LA_1RC1LA_1RD0RA_0LB1RE_0RF---_1LD0RA") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1902: halts_at_trans (TM_from_str "1RB---_1LC0LA_1LD1RC_1RF0LE_1LB1LC_0RC0RF") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1903: halts_at_trans (TM_from_str "1RB0LE_1RC1RA_1RD0LF_1LA0RB_1LB1LA_---1LC") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm1904: halts_at_trans (TM_from_str "1RB---_0RC0RE_1RD1RB_1LE1RA_0RF0LE_0LD1RF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1905: halts_at_trans (TM_from_str "1RB1RF_0LC0RD_0LD1LC_1RE0LD_1RF---_1RA0RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1906: halts_at_trans (TM_from_str "1RB0LA_0RC1LE_1LD0RA_0LE1LA_---1LF_1RC1LD") c0 (E,0).
Proof. solve_halt 15. Time Qed.

Lemma tm1907: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_0RD0RA_1LE1LD_1LA1LF_1LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1908: halts_at_trans (TM_from_str "1RB0RB_1RC0LB_0RD1RE_0RE1RA_1LF1RD_1LB---") c0 (F,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1909: halts_at_trans (TM_from_str "1RB---_1LC0RC_1RD0LC_0RE0RF_0LE1LC_1RA1LD") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1910: halts_at_trans (TM_from_str "1RB0LC_1RC1RA_1LD0RE_0LA1LD_0RA0RF_---1LA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1911: halts_at_trans (TM_from_str "1RB---_1RC0LD_0RD0RE_1LE0RA_0LF0LE_1RA1LE") c0 (A,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1912: halts_at_trans (TM_from_str "1RB1RF_1RC0LE_0RD0RB_1RE1RA_1LB0LC_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1913: halts_at_trans (TM_from_str "1RB1RE_0LC1LB_1RE1LD_1LB0LF_0RA0RE_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1914: halts_at_trans (TM_from_str "1RB0LD_1RC0RE_1RD1LD_1LA1LD_0RF1RB_---1LD") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm1915: halts_at_trans (TM_from_str "1RB---_1LC1RC_1RE0LD_1RC1LF_0LA0RE_1LE0LB") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1916: halts_at_trans (TM_from_str "1RB0RF_0RC0RB_1RD0LE_1RE0RA_1LC0LE_0LA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1917: halts_at_trans (TM_from_str "1RB1LE_0LC0LD_1LD0RD_1RC0RA_0LF---_1LB0LA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1918: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1RD1RB_1RE---_0LA1LE_1LE0LD") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1919: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF0LC_---1RE") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1920: halts_at_trans (TM_from_str "1RB0RA_1RC1LF_1LD1RD_1LE0LD_0LA1LB_---1RA") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1921: halts_at_trans (TM_from_str "1RB0RC_0LC1LB_1LD0LB_1RE0RA_1RF1RD_1LB---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1922: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_1LD0RE_1RB0LA_0LD0RA_---0LC") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1923: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_---1LD_0RE1LC_1RA0LF_1LA1LE") c0 (C,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1924: halts_at_trans (TM_from_str "1RB0RA_0RC1RA_0RD---_0LD1LE_1LF0RB_1RB0LF") c0 (C,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1925: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1RD1LD_1LA1RD_1LF1LC_---1LC") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1926: halts_at_trans (TM_from_str "1RB0RD_1LC0RC_1LD1LB_1RA1LE_0RF0LC_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1927: halts_at_trans (TM_from_str "1RB---_1LC0RF_1RD1LC_1RE0LD_1RA1RB_1RD0RE") c0 (A,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1928: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_1LA1LD_1RA1LC_1LA0RF_---1RB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1929: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1RA1RD_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1930: halts_at_trans (TM_from_str "1RB0RB_1RC0LE_0LC0LD_---1LE_1RF1LB_1RA0RE") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1931: halts_at_trans (TM_from_str "1RB1RF_0RC1LF_1RD---_1LE1LD_0RB0LD_1RA0RE") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1932: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0LE0LD_0LE---_1LA1LF_1LB0RF") c0 (D,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1933: halts_at_trans (TM_from_str "1RB0RF_1LC1LA_1LD0LC_0RE0LB_0RF1RE_---1RB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm1934: halts_at_trans (TM_from_str "1RB0RD_1RC0RF_1LD0LA_1RA0LE_1LD0LE_0RE---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1935: halts_at_trans (TM_from_str "1RB0RA_1RC0RD_1LB---_1LF0LE_1LD0LA_1RA1LD") c0 (C,1).
Proof. solve_halt 13. Time Qed.

Lemma tm1936: halts_at_trans (TM_from_str "1RB1LA_0LC1RE_1LD1RC_0RB0LD_0RA1RF_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1937: halts_at_trans (TM_from_str "1RB0LD_1RC0RA_1LA1RF_1RA0LE_1LB0LA_0LB---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1938: halts_at_trans (TM_from_str "1RB0RC_0LC1RA_1LD1RC_0RF1LE_1LA0LD_0LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1939: halts_at_trans (TM_from_str "1RB1LF_0RC0RF_1LD0RE_1LE0LC_0RA0LD_1RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1940: halts_at_trans (TM_from_str "1RB1RE_1LC1LF_1LD1LC_1RA0LB_0LE0LF_---0RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1941: halts_at_trans (TM_from_str "1RB0LC_1LA---_1LD1LC_1RE0LC_0RA1RF_1RE0RD") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1942: halts_at_trans (TM_from_str "1RB0RF_1LC1RE_0LA0LD_1RE1LF_0RB0RE_1LB---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1943: halts_at_trans (TM_from_str "1RB1RF_1LC0RA_0RD0LB_1RA0LE_1LD1RC_1RD---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm1944: halts_at_trans (TM_from_str "1RB---_1RC1RF_1LD0LC_1RB1RE_1LB1LE_1RA0RF") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1945: halts_at_trans (TM_from_str "1RB---_1LC1LD_1LD1LA_1LE1RD_1RF0LB_0RD0RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1946: halts_at_trans (TM_from_str "1RB0LC_0RC0RD_1LA1RB_1RE1LC_1LF1RA_---1LE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm1947: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE0LF_0LA1LE_1RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1948: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LD_1LE1RB_1LF0LE_0LB0RC") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1949: halts_at_trans (TM_from_str "1RB---_1RC1LF_1LD0RC_0RE0LE_1LB1RC_1RD0LA") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1950: halts_at_trans (TM_from_str "1RB0LE_1LC0RF_1RD0RC_1LA1RA_0LD0LA_1RC---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1951: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA1RF_1RA0LD_0LA---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1952: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0LB_0RA1RF_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1953: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD0RF_1LE1RA_0LF0LD_1RB1LE") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1954: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_1LD0LC_0LE0LA_0RF---_1RA1RE") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1955: halts_at_trans (TM_from_str "1RB0LC_1RC1RF_1LD0RD_0LE0LA_0RA1LE_1LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1956: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RC1LD_1LB0LE_1LA1RF_0RE0RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1957: halts_at_trans (TM_from_str "1RB0RE_0LC1RD_0LD1LB_1RE0LF_1RA1RB_---1LA") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm1958: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD0LD_0RA---_1LF0LC_0LA0RA") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1959: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA1LD_1LC0RB_1LF---_1RC0LD") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1960: halts_at_trans (TM_from_str "1RB1RC_0LC1RA_1LF0RD_0RE---_1LB1LA_0RB0LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1961: halts_at_trans (TM_from_str "1RB1RD_1RC0RE_1RD0RA_0LE0RC_0LA0RF_1LD---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1962: halts_at_trans (TM_from_str "1RB0LF_0RC0RD_1LA1RC_1RE0RC_1RF---_0LA1LC") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1963: halts_at_trans (TM_from_str "1RB0LA_0RC1RE_0LD0RD_1LA---_1LA0RF_0RE1RA") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1964: halts_at_trans (TM_from_str "1RB1LE_0LC0RB_0RA1LD_0LE---_1LA0LF_1LE1LC") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm1965: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RE0LD_1LB0RE_1RF0RA_0RD1RC") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1966: halts_at_trans (TM_from_str "1RB---_1RC0RD_1LD0RA_1RB0LE_1RA0LF_1LB0LD") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1967: halts_at_trans (TM_from_str "1RB1RC_1LC0LD_1RE0LD_1LB0RF_---1RA_1RD0RA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm1968: halts_at_trans (TM_from_str "1RB0RF_1LC0LC_1RD0LB_0RE0RC_1RA---_0LE0RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1969: halts_at_trans (TM_from_str "1RB0RF_1LC0RE_1RD0LC_1RE---_1LF0RF_1RA0LB") c0 (D,1).
Proof. solve_halt 16. Time Qed.

Lemma tm1970: halts_at_trans (TM_from_str "1RB0LD_0RC1RA_1RD1RF_1LA1LE_0LA1RA_0RB---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1971: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD1RE_0LA0LD_1RB0RF_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1972: halts_at_trans (TM_from_str "1RB0RD_1RC1RF_1LA0RB_1RA0LE_1LD0LE_1LE---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1973: halts_at_trans (TM_from_str "1RB0RA_1RC1RA_1LD1LF_1LA0LE_---1RF_0LC1LC") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm1974: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1RB_1LE---_0LA1LE_1RE0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1975: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1LD1RA_0LE0LD_1RB1LD_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1976: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0RA_0RA1RF_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1977: halts_at_trans (TM_from_str "1RB1LB_1RC0RF_1RD0LC_1LE0RE_1RB1LC_---1RA") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm1978: halts_at_trans (TM_from_str "1RB0LC_1RC0RD_1LA0LC_1RE0RE_0RA1RF_0LD---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm1979: halts_at_trans (TM_from_str "1RB1RE_0LC0LB_1RC1RD_0LE0RA_1LF0RE_1LB---") c0 (F,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm1980: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_0RD1RA_1LE0RB_0LA0RA_1RE---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm1981: halts_at_trans (TM_from_str "1RB---_0RC0RB_1LD1LA_1LE0LC_0LF0LD_1RF0LB") c0 (A,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1982: halts_at_trans (TM_from_str "1RB0LA_0RC1RA_1LC1RD_---0RE_0RF1LF_1LA0RB") c0 (D,0).
Proof. solve_halt 8. Time Qed.

Lemma tm1983: halts_at_trans (TM_from_str "1RB1RE_0LC---_0LD1LC_1RE1LF_0RA0RE_1RC0LF") c0 (B,1).
Proof. solve_halt 9. Time Qed.

Lemma tm1984: halts_at_trans (TM_from_str "1RB1LE_0RC0RF_1RD0LE_1LC---_1LA0LA_1RA0RA") c0 (D,1).
Proof. solve_halt 12. Time Qed.

Lemma tm1985: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_1LE1LD_1LC0LB_1LF1RD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1986: halts_at_trans (TM_from_str "1RB0RC_1LC1RD_1RF1LD_1LA0RE_---0LB_0RA1RC") c0 (E,0).
Proof. solve_halt 14. Time Qed.

Lemma tm1987: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1LA_0LE0LF_1LA0RC_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1988: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD1RA_0RE0LF_1RF0RD_1LB0LF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1989: halts_at_trans (TM_from_str "1RB---_1RC1LE_0RD1RC_1LE0RF_0LB0LE_0LA0RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1990: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_1RB1LD_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1991: halts_at_trans (TM_from_str "1RB0RA_0RC1RC_1LD1RF_1LE---_1RA0LE_0LF1RE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1992: halts_at_trans (TM_from_str "1RB0LB_1LC1RF_1LF0LD_1RE0LC_1RD---_1LA0RF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1993: halts_at_trans (TM_from_str "1RB0LD_1RC0RA_1LA1RD_0RF1RE_0LF---_1LA0LF") c0 (E,1).
Proof. solve_halt 5. Time Qed.

Lemma tm1994: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_0LA1RD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1995: halts_at_trans (TM_from_str "1RB1LA_1RC0LD_0LA0RC_1LF1LE_1LB0LA_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm1996: halts_at_trans (TM_from_str "1RB---_1LC0RD_1LD0LB_0RE0LC_1RF1LA_1RC0RA") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm1997: halts_at_trans (TM_from_str "1RB0RB_1RC1RA_0LD1RE_0LE1LD_1RF0LE_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm1998: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LE0LD_0LB0LF_1RA0LC_0RB---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm1999: halts_at_trans (TM_from_str "1RB1LC_0RC---_1LD1LE_1RA1LA_1RF0LA_0LE0RF") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2000: halts_at_trans (TM_from_str "1RB1LE_0RC1RF_0RD---_0LE0RA_1LF1LA_1RA0LD") c0 (C,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2001: halts_at_trans (TM_from_str "1RB1RE_1LC1RA_1LE0RD_0LF0LE_1LD0RB_0RA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2002: halts_at_trans (TM_from_str "1RB1LA_0LC1RF_1LE1RD_1LE---_0RB0LE_0RA1RC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2003: halts_at_trans (TM_from_str "1RB1LB_1LA1LC_1RD0LC_1RE---_0RF1RB_1RE1RB") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2004: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD0RE_0LA0LD_1LA0RF_0LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2005: halts_at_trans (TM_from_str "1RB1RC_1LC1LF_1RA0RD_1LE1RD_---1LF_1LC0LB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2006: halts_at_trans (TM_from_str "1RB---_0RC0LF_1LB0RD_1LD1RE_0RF1LE_1RA0LF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2007: halts_at_trans (TM_from_str "1RB0RE_1RC0RF_1RD0LB_1LE0RA_1LC0LE_0LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2008: halts_at_trans (TM_from_str "1RB0RE_1RC1RF_1LC0LD_1RA1LD_1LC1RE_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2009: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_1RA1LD_1RA0LE_---1LC_1LC1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2010: halts_at_trans (TM_from_str "1RB1LB_1RC1RD_1LA0LC_0RF1RE_0RA1LC_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2011: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RE1LD_1RA0LF_0LE1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2012: halts_at_trans (TM_from_str "1RB0LD_1RC1RF_0RD1RA_1LE0RB_0LA0RA_1RB---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2013: halts_at_trans (TM_from_str "1RB1LA_1LA1RC_0RC0RD_1LE1RD_0LF0LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2014: halts_at_trans (TM_from_str "1RB1LE_1RC1RE_1LD1LF_---0LA_1RF0LC_1LD0RA") c0 (D,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2015: halts_at_trans (TM_from_str "1RB0RE_1LC1RB_1RA0LD_1LB1LD_---0RF_0LC0RB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2016: halts_at_trans (TM_from_str "1RB1LE_1RC1LB_0RD0RD_1LA1RD_1LF0LB_---1LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2017: halts_at_trans (TM_from_str "1RB1LF_0LC1LB_1RD1LA_0RE0RD_1LA1RD_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2018: halts_at_trans (TM_from_str "1RB0LD_1LC---_1RE0LD_1LC1LD_0RA1RF_1RE0RC") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2019: halts_at_trans (TM_from_str "1RB1LA_0RC0RD_1LA1LE_1LE1RF_1LC0LC_---1RA") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm2020: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_1LC1RE_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2021: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF0LC_---1RA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2022: halts_at_trans (TM_from_str "1RB0LD_1LC---_1LF1RD_0LF1RE_1RC0RF_0RA0LA") c0 (B,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2023: halts_at_trans (TM_from_str "1RB1RC_1RC1LD_1LB1RE_0LF1LE_0LA0RA_---0LB") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2024: halts_at_trans (TM_from_str "1RB1RB_1RC0RA_1LD0RB_1RB1LE_0LC1LF_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2025: halts_at_trans (TM_from_str "1RB1LD_0RC1RE_1LD0RA_0LA0LD_1RC0RF_1LB---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2026: halts_at_trans (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0LD_1RB0RF_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2027: halts_at_trans (TM_from_str "1RB---_1RC0LF_0RD0LD_1RE1RA_1LC1LF_1RB0LE") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2028: halts_at_trans (TM_from_str "1RB0LC_1RC1RA_1LD1LA_1RE1LD_---0RF_1RE1RA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2029: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1RE1LC_1RA0RF_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2030: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1LB0LA_0RF0RE_0LD1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2031: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD1LC_1RA1LB_1LF0RD_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2032: halts_at_trans (TM_from_str "1RB0RD_1LC0LF_0RA0LB_0RE---_1RC0LE_0LE1RD") c0 (D,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2033: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1RE0LF_0LA1LE_0RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2034: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1RD1RA_0LB1LF_0LF---_1LD0RC") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2035: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RE1LD_1LB0LA_0RF0RE_1LB1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2036: halts_at_trans (TM_from_str "1RB0RD_1LC0RE_0RA1LB_1RF0LE_1LD1LE_---0RA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2037: halts_at_trans (TM_from_str "1RB0LD_1RC0LC_1LA0RA_0RB0LE_0LF---_1LB1LF") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2038: halts_at_trans (TM_from_str "1RB1LF_0LC---_1LF1RD_1RE0RA_0RC1RE_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2039: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD0RF_0LA0RA_1LD0LD_---1LA") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2040: halts_at_trans (TM_from_str "1RB---_1LC0RA_0RD1RC_1LE1RB_0LF0LE_1RB1LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2041: halts_at_trans (TM_from_str "1RB0LD_1RC0RA_1LA0RF_1RA0LE_1LB0LA_1RB---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2042: halts_at_trans (TM_from_str "1RB1RF_1RC1LF_1LD---_0RB0LE_1LD1LE_1RA0RD") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2043: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_1LD0RE_1RB0LA_0LD0RA_---1RE") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2044: halts_at_trans (TM_from_str "1RB0LC_0LA0RB_1RD1LE_0RE---_1LF1LA_1RC1LC") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2045: halts_at_trans (TM_from_str "1RB1RD_0RC1RF_1RD---_1LE1RA_0LA0LE_0RB1LD") c0 (C,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2046: halts_at_trans (TM_from_str "1RB0RB_1RC1RA_0LD1RE_0LE1LD_0RF0LE_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2047: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1LE0LA_---0LF_1LB1LC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2048: halts_at_trans (TM_from_str "1RB1LD_1LC1RE_0RA0LB_1LA1LF_0RB0RC_---1RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2049: halts_at_trans (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0LD_1RB0RF_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2050: halts_at_trans (TM_from_str "1RB---_1LC1RC_0RF0LD_0RE0RB_0LB1RA_1LB1RD") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2051: halts_at_trans (TM_from_str "1RB0RE_1RC0RA_1RD0LC_1LE---_1LA1LF_1LA0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2052: halts_at_trans (TM_from_str "1RB1RF_1LC0RA_1RA0RD_1RC0LE_1LD0LE_1LE---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2053: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD0LC_1RF1LE_---1RC_0RA1RF") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2054: halts_at_trans (TM_from_str "1RB1RF_1RC0LE_0LD1LC_1RF1LB_1LB---_0RA0RF") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2055: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LE0RD_1LB0LD_1LA0LA_0RB---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2056: halts_at_trans (TM_from_str "1RB---_1RC0RD_1LD0RF_0LA0LE_0LC0LB_1LA0RF") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2057: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1RE0LD_0RE1RB_0LB1RF_1RB---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2058: halts_at_trans (TM_from_str "1RB1LB_1RC1LD_0RD0RA_0LE0RD_0LF---_1LB1LF") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2059: halts_at_trans (TM_from_str "1RB0LC_1RC0RE_1LA0LD_1LA0RB_1RD0RF_0RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2060: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_0LD0RA_1RE1LD_---1LB_0RD1LA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2061: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1LD0RF_0RA0LE_0LD0LC_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2062: halts_at_trans (TM_from_str "1RB0LC_1RC1RF_1LD0RD_0LE0LA_0RA1LE_1RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2063: halts_at_trans (TM_from_str "1RB1LE_1RC0LF_1LD0RC_0LA0RA_1LD0LB_---0LD") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm2064: halts_at_trans (TM_from_str "1RB1LA_0RC0RD_1LC0LA_0RE0RC_---1RF_0RC0RE") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2065: halts_at_trans (TM_from_str "1RB0LA_1LC0RC_1RD1LA_1RE1RF_1RA0RA_---0LB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2066: halts_at_trans (TM_from_str "1RB1LE_0LC0RF_0LD1RC_1LA0RE_1LB---_0RA0RF") c0 (E,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2067: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_0RD1RA_1LE0RC_0LA0LE_0LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2068: halts_at_trans (TM_from_str "1RB0LE_1LC1RE_0RA0LD_0LB0LD_1RF---_0RC0LD") c0 (E,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2069: halts_at_trans (TM_from_str "1RB1RD_1LC0RA_1RA0LB_1RE---_1LE0RF_1RC1LB") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2070: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LA1LD_1LA0LC_---1RF_1LC1RF") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2071: halts_at_trans (TM_from_str "1RB1RD_0LC---_0LF1LD_1RA1RE_1LF0RE_1LC1RB") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2072: halts_at_trans (TM_from_str "1RB1RD_1RC0RB_1RD1RA_1LE0RF_1LC0LE_1LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2073: halts_at_trans (TM_from_str "1RB0RF_0LC1LB_1LD0LB_1RE1LA_0RA1RD_---0RE") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm2074: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0LA0LF_1LF0LE_1RC---_0LA0RA") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2075: halts_at_trans (TM_from_str "1RB0RD_1RC1RF_0LD---_0RB1LE_1LA0LE_1RA0RB") c0 (C,1).
Proof. solve_halt 13. Time Qed.

Lemma tm2076: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE1LF_0LA1LE_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2077: halts_at_trans (TM_from_str "1RB---_1LC1LE_1RF0LD_0LE0RC_0LB0LA_0RD0RC") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2078: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0LD1RB_1LE---_1LF0LD_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2079: halts_at_trans (TM_from_str "1RB0RC_1LA1RA_1LD1RC_0RF1LE_1LA0LD_0LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2080: halts_at_trans (TM_from_str "1RB0RB_1LC0LF_0LD1LD_1RE0LC_0RE1RA_---1RA") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2081: halts_at_trans (TM_from_str "1RB---_1LB1LC_1RD1RF_0RE1RD_0RB1RF_0RA0LB") c0 (A,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2082: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LB1LE_1LF0LA_---0LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2083: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_0RF1LF_0LC---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm2084: halts_at_trans (TM_from_str "1RB0LE_1RC1RA_0RD0RB_1LE---_1LF1LA_0LA1LE") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2085: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA1LD_1RD0LF_1LE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2086: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_---0LD_1LE0LB_1RF0LA_0LD1RE") c0 (C,0).
Proof. solve_halt 16. Time Qed.

Lemma tm2087: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RA0LD_0LC1LD_1RF0RC_1LB1RE") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2088: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_1LD1LA_0LE---_1LA0RC_1RD1LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2089: halts_at_trans (TM_from_str "1RB0RC_1LC1RF_1LD1RC_0LC0LE_1RA1LE_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2090: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1LE1LD_0LC---_1LF0RC_1RA1LE") c0 (D,1).
Proof. solve_halt 14. Time Qed.

Lemma tm2091: halts_at_trans (TM_from_str "1RB---_0RC0LD_1RD0RF_1LE1RC_1LF0LE_0LA0RB") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2092: halts_at_trans (TM_from_str "1RB1RF_1RC0RC_1RD0LC_1LE0RE_1RA1LC_---0LD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2093: halts_at_trans (TM_from_str "1RB1RA_1RC1LE_1LD1RA_---0LC_1LB0RF_1RC1RE") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2094: halts_at_trans (TM_from_str "1RB0LA_1LC0RC_---1LD_1LE1LA_1RF1RE_1RA0RF") c0 (C,0).
Proof. solve_halt 7. Time Qed.

Lemma tm2095: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LF_1LC0LF") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2096: halts_at_trans (TM_from_str "1RB0RF_1LC1RB_0LD1LD_1RE0LC_0RE1RA_1LC---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm2097: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_1LC1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2098: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_1LD0RD_1RE1LB_1RA0RF_---0RD") c0 (F,0).
Proof. solve_halt 15. Time Qed.

Lemma tm2099: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE0LF_0LA0RA_1RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2100: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_0RA1LD_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2101: halts_at_trans (TM_from_str "1RB0RF_1LC0RB_1LD0LC_0LE1LB_1RA1LE_---0LC") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm2102: halts_at_trans (TM_from_str "1RB0LF_1LC1RA_1LD0LC_0LE0LA_0RF---_1RA1RE") c0 (E,1).
Proof. solve_halt 14. Time Qed.

Lemma tm2103: halts_at_trans (TM_from_str "1RB0RD_1LC1RB_1RD0LB_1LC1RE_1RF0RA_---1LD") c0 (F,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm2104: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_0RF0RE_0LC0RC_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2105: halts_at_trans (TM_from_str "1RB1LD_1RC0LB_1LD0RD_1RE1LB_1RA0RF_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2106: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_1RA1LD_1LE0LF_0LC0RC_1LD---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2107: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RF1LD_0RE0LE_---1LC_0LF1RA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2108: halts_at_trans (TM_from_str "1RB0RE_0LC0LE_0RA1RD_0RE---_1LF1RC_0LB0LF") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2109: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD0LF_1LE1LF_0LA1LC_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2110: halts_at_trans (TM_from_str "1RB1RF_1LC1LF_1RE1LD_1LB1LD_---0RC_1RA0LB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2111: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_1LD0LE_0LA1LC_0RD0RA_1LE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2112: halts_at_trans (TM_from_str "1RB0RC_1LC1RF_0RD0LC_1LE1RE_1LA---_1RA0RB") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2113: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LB_1RD0RF_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2114: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC0LF_---1RD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2115: halts_at_trans (TM_from_str "1RB---_1LC1LB_1RD0LB_1RE0RD_0LF0RF_1RD0RA") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2116: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RE1LD_0LB0LF_1LD0RA_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2117: halts_at_trans (TM_from_str "1RB0LD_1RC1RE_1LA1RF_1RA1LA_0RA0LA_1RE---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2118: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RE1LD_1LB0LA_0RF0RE_1RB1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2119: halts_at_trans (TM_from_str "1RB1RE_1LC---_1LE0LD_1LC1LD_0RA1RF_1RE0RC") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2120: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD1LC_1RE0LA_1LB1RA_0LE0LF") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2121: halts_at_trans (TM_from_str "1RB0LE_1LC0LD_1LA0LC_---1RE_1RF0LC_0RA0RB") c0 (D,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2122: halts_at_trans (TM_from_str "1RB0LB_1RC1LB_0LB1RD_1RF0RE_1LA1RE_---1RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2123: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1RD0RE_1LC---_1LA0LF_1LE0LB") c0 (D,1).
Proof. solve_halt 11. Time Qed.

Lemma tm2124: halts_at_trans (TM_from_str "1RB0RC_0LA1RF_0RD---_1RE1RA_1LF0LF_0RD0LE") c0 (C,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2125: halts_at_trans (TM_from_str "1RB1LB_1LC0RB_0LE0LD_1LA---_0LF1RF_0RF1RB") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2126: halts_at_trans (TM_from_str "1RB0RE_1LC0LB_1LD1LB_1RA1RF_---1RF_0RD1RD") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2127: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_1LD0RD_1RE1LD_---1RB_1LD1LA") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2128: halts_at_trans (TM_from_str "1RB1RE_1LC0RF_1RA0LD_1RC1LC_0RC0LC_1LC---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2129: halts_at_trans (TM_from_str "1RB0RD_0RC0RE_1LD0LD_0LE0RC_1RA1RF_0LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2130: halts_at_trans (TM_from_str "1RB1LF_0LC1RB_---0RD_1LE1RC_1LF0LB_1LA1LD") c0 (C,0).
Proof. solve_halt 12. Time Qed.

Lemma tm2131: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_0LD1RF_0LE0LA_1LD1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2132: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_0LD1LB_1RA0LE_1LC0LF_1RB---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2133: halts_at_trans (TM_from_str "1RB1LB_1LC1RB_1LC0LD_1RE1LD_1RA0RF_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2134: halts_at_trans (TM_from_str "1RB1LE_1LC0RD_1RB1LC_1LA1RD_0LF0LC_---1LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2135: halts_at_trans (TM_from_str "1RB---_1LC0LF_0LD0RD_1RE1LB_0RF0RE_0LA1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2136: halts_at_trans (TM_from_str "1RB0LA_0LC1LB_1RD1LA_0RE0RD_1RF1RD_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2137: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LD_1LE1RB_1LF0LE_0RD0RC") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2138: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_0LC---_0RA0LA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2139: halts_at_trans (TM_from_str "1RB0LF_0LC---_1LA1RD_0RE0RA_1RC0LA_1LE0LF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2140: halts_at_trans (TM_from_str "1RB0RA_1RC0RE_1LD0LC_1RA0LC_1RF---_0RA1RE") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2141: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_1RA1LD_0RE0LE_---1LC_0RF1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2142: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_1LF0LE_0RD0LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2143: halts_at_trans (TM_from_str "1RB1LE_1LC0RB_0RD0LD_1LA1RB_1RC0LF_1RA---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2144: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1LA1RD_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2145: halts_at_trans (TM_from_str "1RB1RD_1RC0RB_1LD0LC_1LE0RA_---0LF_0LA1RA") c0 (E,0).
Proof. solve_halt 7. Time Qed.

Lemma tm2146: halts_at_trans (TM_from_str "1RB1LA_1RC1RF_1RD1LD_1LC0LE_---0LA_0RC0RB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2147: halts_at_trans (TM_from_str "1RB---_1RC0RF_0RD0LD_1RE1RA_1LF1LE_1RC0LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2148: halts_at_trans (TM_from_str "1RB1LE_0RC0RF_0LD0RB_0LA1RD_1LD0LE_0RE---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2149: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD1RB_0LA1LD_1RC0LF_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2150: halts_at_trans (TM_from_str "1RB0LE_1LC0RE_1LA0LD_0LC0LA_1RA0RF_1RB---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2151: halts_at_trans (TM_from_str "1RB1LE_1RC0LA_1LD0RB_---1LB_1RF0LF_0RE1LC") c0 (D,0).
Proof. solve_halt 14. Time Qed.

Lemma tm2152: halts_at_trans (TM_from_str "1RB0RD_1LC0LC_1RE0LD_0LC1RF_0RB0RA_0LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2153: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_0LD0LB_1RD0LE_1LC0RF_1RA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2154: halts_at_trans (TM_from_str "1RB0LA_0RC---_1LD1RE_1LA0RC_1RA0RF_1RD0LB") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2155: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LA1LD_0LE1LF_0LF---_0LB1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2156: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1LF_---1RA") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2157: halts_at_trans (TM_from_str "1RB1RF_1LC1LF_1RE1RD_1LB1LE_---1RA_0LB0RC") c0 (E,0).
Proof. solve_halt 10. Time Qed.

Lemma tm2158: halts_at_trans (TM_from_str "1RB---_0RC1LB_1RD1LC_0RE1RE_1LF0RD_0LF1LA") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2159: halts_at_trans (TM_from_str "1RB1LB_1RC0LA_1RD0LD_1LB1RE_1RF---_0RB0LB") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2160: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RF0RD_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2161: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE0LF_0LA1LE_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2162: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_---1LD_1LA0LF_1RA1RE_0RD1LF") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2163: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_0LF1RD_---1LE_1RA1LC_1LE0LE") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2164: halts_at_trans (TM_from_str "1RB1LB_1LC1RB_0RA0LD_1RE1LD_1RA0RF_---0RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2165: halts_at_trans (TM_from_str "1RB1RE_1RC1LF_1LD0RA_1LB1LA_0RE0LD_---0LE") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2166: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_0RC1LD_1RA0LF_0LE1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2167: halts_at_trans (TM_from_str "1RB1RF_1RC---_0LD1LC_1RF1LE_1LC0LB_0RA0RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2168: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RA1LD_0LB0LF_1LD0RA_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2169: halts_at_trans (TM_from_str "1RB1LB_0LC0RD_1RA1LD_0LE0LA_0RA1LF_1LA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2170: halts_at_trans (TM_from_str "1RB1LD_0LC1RB_1LF1LD_1LA0RE_0LC1RD_---0LC") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm2171: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1RB0LA_0RF0RE_1RD1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2172: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA1LD_1LD0LF_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2173: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1LB1RD_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2174: halts_at_trans (TM_from_str "1RB1LA_1LC1RF_0RD0LC_1LE1RE_1LA---_1RA0RB") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2175: halts_at_trans (TM_from_str "1RB1LB_0RC1RE_1RD0LA_0LE0RF_---1LC_1LD1RE") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2176: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD1RC_1LE1RB_0LF0LE_1LA1LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2177: halts_at_trans (TM_from_str "1RB---_1RC0LD_0RD1RF_1LE1RA_0LB0LE_0RB0RE") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2178: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_1RF---_0RA0LA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2179: halts_at_trans (TM_from_str "1RB0RE_1LC0LB_0RD0LB_0RA1RE_1RD0RF_1RC---") c0 (F,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2180: halts_at_trans (TM_from_str "1RB---_1LC0RF_1RD0LC_0RE0LE_0LB1RA_0RB1RC") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2181: halts_at_trans (TM_from_str "1RB0RF_1RC1RE_1LD1LE_1RA0LE_1RD0LC_0RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2182: halts_at_trans (TM_from_str "1RB0LE_1RC1LC_1LD0RA_1LA0LD_1LB0RF_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2183: halts_at_trans (TM_from_str "1RB0LD_0RC0RA_0RD1RC_1LE1LF_1LA0LE_0RB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2184: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_0RE1LD_1RE0LF_---0LF_1RA1LC") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2185: halts_at_trans (TM_from_str "1RB0RA_1LC1LB_1RD0LB_---1RE_1RF0RC_0RA1RE") c0 (D,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2186: halts_at_trans (TM_from_str "1RB0RA_0RC0LD_1LD0LF_0LE0RE_1RA1LC_1LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2187: halts_at_trans (TM_from_str "1RB0LF_1LC0RD_1LA0LD_1LB1RE_0RB1RB_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2188: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1RE0LF_0LA1LE_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2189: halts_at_trans (TM_from_str "1RB0LE_1RC1RF_1RD1LF_1LE---_1LA1LE_1RB0RA") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2190: halts_at_trans (TM_from_str "1RB1LB_1LA0LC_---1LD_1RE1LD_1RB1RF_1RB0RE") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2191: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LD0RA_1LA0LE_1LC0LF_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2192: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_0RD1RC_1LE1RB_0LA0LE_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2193: halts_at_trans (TM_from_str "1RB---_0RC0LC_0RD0LF_1RE0LA_1LC1RA_0LE0LF") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2194: halts_at_trans (TM_from_str "1RB0LD_0RC---_1RD0LA_0RE1RC_1LF1RF_0LC1RA") c0 (B,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2195: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_0RD0RC_1RE1LB_1LA1RF_0LA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2196: halts_at_trans (TM_from_str "1RB0LF_1RC0RE_0RD---_1LA0RD_1RD0RC_0LA0LE") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2197: halts_at_trans (TM_from_str "1RB1RC_0RC1RA_1LD0RC_1LE1RF_0LD1LA_0LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2198: halts_at_trans (TM_from_str "1RB1LE_1LC0RD_1LA0LC_1RB0RD_0LA0LF_0LD---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2199: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_1RB1LD_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2200: halts_at_trans (TM_from_str "1RB1LE_1RC---_1LD0RD_1RE0LD_0RF0RA_0LF1LD") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2201: halts_at_trans (TM_from_str "1RB---_1RC1RA_1RD0LD_1LE0RB_0LE0LF_1RB1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2202: halts_at_trans (TM_from_str "1RB---_1LC1RC_1RF0LD_1RD1LE_1LF0LB_0LA0RF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2203: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_0RF1RA_---1LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2204: halts_at_trans (TM_from_str "1RB0LD_0RC0RE_1RD0RF_1LA1LF_1RF---_0RA0RF") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2205: halts_at_trans (TM_from_str "1RB---_1LC1RD_0LD0LC_1RE1RB_0RA1RF_0RE1RB") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2206: halts_at_trans (TM_from_str "1RB1LD_1RC1RB_0LA0RB_1LF0LE_1LA0LA_---0LB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2207: halts_at_trans (TM_from_str "1RB0LA_0RC1LF_0LD1RE_1LA0RB_0RD---_1RD1RF") c0 (E,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2208: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1RD1LB_0RA1LE_0RF0LC_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2209: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_1LD1LA_0LE---_0LA1LA_0RF1LC") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2210: halts_at_trans (TM_from_str "1RB0RC_0RC0RB_0LD1RB_1LE---_1LF0LD_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2211: halts_at_trans (TM_from_str "1RB1RC_1LC1LB_1LD0RA_1RC1LE_0LF---_0LC1LA") c0 (E,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2212: halts_at_trans (TM_from_str "1RB1LD_1RC0LB_1LD0RD_1RE1LB_1RA1RF_---0LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2213: halts_at_trans (TM_from_str "1RB1RF_0RC1RA_1RD0RB_1LE0LD_0RA0LD_1RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2214: halts_at_trans (TM_from_str "1RB1LF_1RC0RE_0RD0RB_1RE---_1LF0RA_1LA0LF") c0 (D,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2215: halts_at_trans (TM_from_str "1RB0LF_0RC0RD_0RD0RE_1LE1RB_1LF---_1LA0LC") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2216: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RE0LD_1RE0LA_1LF0RE_0RB0LB") c0 (A,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2217: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LD0RD_1LA0LE_1LB0RA_0RB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2218: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LC1RD_1LE1RD_1LE0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2219: halts_at_trans (TM_from_str "1RB0LF_1RC---_1RD0RE_1LE1RF_0RA0LA_0LE1RC") c0 (B,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2220: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_0LD1LC_1RA1LE_---1LA_1LD0LC") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2221: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_1RD0LC_0LA0RA_1LC1RF_0RE---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2222: halts_at_trans (TM_from_str "1RB0LE_1LC1LA_1LB1RD_0RC0RD_1LF---_0LA1RD") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2223: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_0LD1LB_1RA0LE_1LC0LF_1RE---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2224: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RE1LD_1LB0LA_1RF0RE_1LB0LB") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2225: halts_at_trans (TM_from_str "1RB0RE_1LC0LD_1RB1LB_1RE1LD_0LF1RA_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2226: halts_at_trans (TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_0LB---") c0 (F,1).
Proof. solve_halt 13. Time Qed.

Lemma tm2227: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1LD0LF_0LE0RB_0RA1RC_1RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2228: halts_at_trans (TM_from_str "1RB0LE_1RC0LC_0RD0RF_1RE0RD_1LA0LE_1RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2229: halts_at_trans (TM_from_str "1RB0LE_1RC1RF_1LD0RB_0RA0LC_1LA1RD_1RA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2230: halts_at_trans (TM_from_str "1RB1LF_1LC1LD_1RD1LA_---0RE_0RE1RA_1LC0LB") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2231: halts_at_trans (TM_from_str "1RB0LA_1RC0LC_1LD1RE_1LB0LD_0RA0RF_1RA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2232: halts_at_trans (TM_from_str "1RB0RE_1LC0RF_---1LD_1RA0LA_1RA1LF_0LE0RC") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2233: halts_at_trans (TM_from_str "1RB---_0LC1LE_1RD0LB_0RE0RF_1LC1RE_1RA0RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2234: halts_at_trans (TM_from_str "1RB0RC_1LA1RA_---1RD_1LE1RD_1LA1LF_1LA0LE") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2235: halts_at_trans (TM_from_str "1RB1LE_0RC1RB_1LD0RA_0LE---_1LA0LF_0RC0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2236: halts_at_trans (TM_from_str "1RB0RD_0RC0RA_1RD---_1LE0RF_1LF0LE_1RA1LE") c0 (C,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2237: halts_at_trans (TM_from_str "1RB1LD_1LC0RA_0LF1RD_0RB0LE_---1LB_1LA0LA") c0 (E,0).
Proof. solve_halt 12. Time Qed.

Lemma tm2238: halts_at_trans (TM_from_str "1RB0LF_1LC0RB_0LD1LA_0RA0LE_0RF---_0LA1LB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2239: halts_at_trans (TM_from_str "1RB1LD_1LC0LB_1RD0RC_0LE0RC_1LB1LF_1LA---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2240: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD0LB_1RE1RA_0RF---_1LF1LC") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2241: halts_at_trans (TM_from_str "1RB1RE_0LC1RF_---1LD_0RA1LC_1RA1LF_0RC0LE") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2242: halts_at_trans (TM_from_str "1RB1RF_1LC0RA_1LD0LC_1RE0LB_1RC0RD_0LE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2243: halts_at_trans (TM_from_str "1RB1LD_0RC1RE_1RD0RC_1LA0LD_1RF1RC_1RB---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2244: halts_at_trans (TM_from_str "1RB0LC_0RC---_1RD0RE_1LE0RF_0LA0LE_1RB1RD") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2245: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_1LF0RB_---1LE") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2246: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RE1LD_0LB0LE_1LF0RA_0RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2247: halts_at_trans (TM_from_str "1RB---_1LC0LF_0LD0RD_1RE1LB_1RB0RE_1LA0RD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2248: halts_at_trans (TM_from_str "1RB1LA_1LC1LF_1RD0LB_0RA0RE_1RF---_0RC0RF") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2249: halts_at_trans (TM_from_str "1RB0LC_1LC0RB_0LD1LA_0RA1LE_0LA1LF_0LE---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2250: halts_at_trans (TM_from_str "1RB0LA_0RC1RD_1LA1RA_0RE1RF_0LC0RF_1RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2251: halts_at_trans (TM_from_str "1RB0LC_1LC1RB_1RD1LA_0RE---_0RB1RF_0LB0RA") c0 (D,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2252: halts_at_trans (TM_from_str "1RB1RF_1RC---_1LD0RD_1RE0LD_0RF0RA_0LF1LD") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2253: halts_at_trans (TM_from_str "1RB1LC_1LC0RB_0LE0LD_1LA1LF_1RB0RA_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2254: halts_at_trans (TM_from_str "1RB---_0RC0RF_1LD1RD_1LE0RE_0LF0LE_0RA0LD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2255: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_0LC1LA_1RE1RB_1RF---_1LA0RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2256: halts_at_trans (TM_from_str "1RB0LF_1LC0RF_0LD0LC_1RE1RB_0RA---_0LF1RD") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2257: halts_at_trans (TM_from_str "1RB0LE_0RC0RF_1RD0LA_1LE1RB_1LC0LE_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2258: halts_at_trans (TM_from_str "1RB0RE_1RC1RA_1RD0LF_1LE---_1RB0LF_1LE1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2259: halts_at_trans (TM_from_str "1RB0LE_1LC1LE_1RF0LD_1LA---_1LB0RF_1LB1RE") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2260: halts_at_trans (TM_from_str "1RB0LD_1RC0RB_1RD0RE_1LA0LD_1RF---_0RB1RE") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2261: halts_at_trans (TM_from_str "1RB1LA_1LC0RB_0LD1RD_0RA1LE_0LC1LF_1RA---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2262: halts_at_trans (TM_from_str "1RB1LC_1RC0RA_1LD0RB_0LE0LC_0LA1LF_0RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2263: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE1LF_0RD0LF_0LB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2264: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RE1LD_0LB1LA_1LF0RE_0RB0LB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2265: halts_at_trans (TM_from_str "1RB0RF_1LC1LB_0LD0LB_0RE0LE_1RF---_0RA1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2266: halts_at_trans (TM_from_str "1RB0LE_1LC1RA_1LD0LC_1RE0LA_1RA1RF_0RE---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2267: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_---0LD_1LE0LB_1RF0LA_1RA1RE") c0 (C,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2268: halts_at_trans (TM_from_str "1RB1RA_1RC0RB_1RD0LC_1LE0RE_---1LF_1LA1LC") c0 (E,0).
Proof. solve_halt 7. Time Qed.

Lemma tm2269: halts_at_trans (TM_from_str "1RB---_1LC0RA_0RD1RC_1LE1RB_0LF0LE_1LA1LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2270: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD0RD_1RA1LB_0LF0RE_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2271: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1RF1RD_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2272: halts_at_trans (TM_from_str "1RB1RA_0RC0LC_1LD0LF_0LE0RB_0RA1RC_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2273: halts_at_trans (TM_from_str "1RB0RE_1LC0LE_1RE1LD_0RB---_1LB0RF_1LE0RA") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2274: halts_at_trans (TM_from_str "1RB0LE_1RC0LA_1RD0RB_1LB1RF_1LC0LB_0LC---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2275: halts_at_trans (TM_from_str "1RB1RE_0RC1RB_1LD1RA_0LE0LD_0RF1LD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2276: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE1RF_1RA0RB_0RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2277: halts_at_trans (TM_from_str "1RB0LD_1LC1RC_1LA0RC_1LE1RC_1LB0LF_---1LE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2278: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD0LB_1LD1RE_0RF1LE_1RA0LF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2279: halts_at_trans (TM_from_str "1RB1RE_0RC1RA_1LC1LD_0RA---_1RF1LE_1RD0LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2280: halts_at_trans (TM_from_str "1RB1LD_0LC0RF_0LE0RD_1LB---_1LA0RD_0RA0RF") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2281: halts_at_trans (TM_from_str "1RB---_1LC0RC_1RD0LC_0RE0RF_0LE1LC_1RA1RD") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2282: halts_at_trans (TM_from_str "1RB0LC_1RC1LD_1LA0RD_1LC0RE_1LF1RE_---0LA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2283: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1RD0RE_1LE0RA_0LA0LE_0LB---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2284: halts_at_trans (TM_from_str "1RB1RF_1LC---_1RD0LB_0LE1LD_1RF1LC_0RA0RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2285: halts_at_trans (TM_from_str "1RB1LD_1RC1LF_0LA0RC_1LC0LE_0LB1LE_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2286: halts_at_trans (TM_from_str "1RB0RF_1RC---_1LD1LF_1LE1LD_0RC0LE_1RA0RD") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2287: halts_at_trans (TM_from_str "1RB1LF_0LC1LB_1RD1LA_0RE0RD_0LA1RD_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2288: halts_at_trans (TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RB0LB_0RB1RA_0RD---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2289: halts_at_trans (TM_from_str "1RB1LF_1LC1RB_1LA0LD_1RE1LD_0RD0RB_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2290: halts_at_trans (TM_from_str "1RB0RB_1LC1RF_1RD0LB_0RA0LE_1RC0RE_0LC---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2291: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_1RA0LD_1LE1LF_1LB0RC_0LB---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm2292: halts_at_trans (TM_from_str "1RB0LE_1LC0RB_0RD0LD_1LA1RB_1RB0LF_1RD---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2293: halts_at_trans (TM_from_str "1RB1LE_1LC0RD_1RB1LC_1LA1RD_1LF0LC_---0LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2294: halts_at_trans (TM_from_str "1RB0RE_0RC0LF_1LD0RB_1LA0LD_---0LC_1RF1RA") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2295: halts_at_trans (TM_from_str "1RB---_1LC0LF_0LD0RD_1RE1LB_1RB0RE_0LA0RD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2296: halts_at_trans (TM_from_str "1RB0RD_1LC1RF_0LD0LB_1RE1LC_0RA0LD_1RE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2297: halts_at_trans (TM_from_str "1RB---_1RC1RF_0LD0RB_0LF0RE_1LD1RB_1RA0LE") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2298: halts_at_trans (TM_from_str "1RB0LA_0RC1LA_0RD1RF_1LD0LE_1RA1RE_---0RE") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2299: halts_at_trans (TM_from_str "1RB1RF_0RC0RF_1RD0LA_1LE1RB_0LA0LE_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2300: halts_at_trans (TM_from_str "1RB1RD_1RC0RF_1LD---_0RA1LE_0LD0LC_0RA1RA") c0 (C,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2301: halts_at_trans (TM_from_str "1RB0RF_1RC0LB_1LD---_1LF1LE_1LF0LB_1RA0RD") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2302: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RE1LD_1LB0LA_1RF0RE_0LC0LB") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2303: halts_at_trans (TM_from_str "1RB1RD_1RC1LF_1LD0RA_0RD0LE_1LB1LA_---0LD") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2304: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD0LA_1RE1LB_1LB1RA_0LE0LF") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2305: halts_at_trans (TM_from_str "1RB0LA_1LC0RD_---1LA_1RE1LA_1RF0RB_1RA1LF") c0 (C,0).
Proof. solve_halt 15. Time Qed.

Lemma tm2306: halts_at_trans (TM_from_str "1RB1RF_1LC0LD_1LA1LB_1RE1LD_---1RF_1RB0RA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2307: halts_at_trans (TM_from_str "1RB0LA_0RC---_0RD1RB_0RE1RA_0LE1LF_0LA0LE") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2308: halts_at_trans (TM_from_str "1RB0RA_1LB0LC_1LD0RD_1LE0LF_1RA1LD_1LB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2309: halts_at_trans (TM_from_str "1RB0LC_1RC1RA_1LD1LA_1RE1LD_---0RF_0RD1RA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2310: halts_at_trans (TM_from_str "1RB0RD_1RC0RA_0RD---_1RE1LA_1LF0LF_0RD1LE") c0 (C,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2311: halts_at_trans (TM_from_str "1RB0LA_1RC1RF_0RD1RC_0RE1RB_1LE0LA_---1RD") c0 (F,0).
Proof. solve_halt 11. Time Qed.

Lemma tm2312: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD1LC_1RE0RF_1LB0RA_0LB0LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2313: halts_at_trans (TM_from_str "1RB---_1LC0RF_0LD0LC_1RE1RA_1RE0LB_1RC0RA") c0 (A,1).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm2314: halts_at_trans (TM_from_str "1RB1RC_1LA1RA_1LD0RC_1LE1RF_0LD1LA_0LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2315: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RA1LD_1RE0LD_0RF1LE_---0LB") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2316: halts_at_trans (TM_from_str "1RB1RE_0LC1RB_---0RD_1LE1RC_1LF0LB_1LA1LD") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2317: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1LD0LD_0LF0RA_0LC---_1LA1RC") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2318: halts_at_trans (TM_from_str "1RB0LA_1RC0RD_1LD1RF_0LE0RB_1LF---_1LC0LA") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2319: halts_at_trans (TM_from_str "1RB0LD_1RC1RB_1LA0RD_1LC0RE_1LC0RF_---0RA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2320: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD1RC_1LE1RB_0LF0LE_0RB1LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2321: halts_at_trans (TM_from_str "1RB0LF_1RC0RB_1LD0RA_0LE0LC_0LA1LE_1LD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2322: halts_at_trans (TM_from_str "1RB---_0LC0LF_1RD1LB_0RE1RD_1LB0RC_1LA0LE") c0 (A,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2323: halts_at_trans (TM_from_str "1RB1RE_1LC---_1RF0LD_0LE0LA_0RF1LE_1LB0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2324: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LD1LD_1LE1RD_1LC0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2325: halts_at_trans (TM_from_str "1RB1LD_1LC0RF_1LA0RA_1LE---_0LB0RB_1LB1RB") c0 (D,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2326: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_---0LD_0LE1LF_1RA0RA_1LD0LB") c0 (C,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2327: halts_at_trans (TM_from_str "1RB1LF_1LC1LD_1RD1LA_---0RE_1RB1RA_1LC0LB") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2328: halts_at_trans (TM_from_str "1RB0RC_1RC1RE_1LD1RA_0LE0LD_0RF0RC_1LA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2329: halts_at_trans (TM_from_str "1RB0RD_0RC1RB_1LC1RA_1RF1LE_0LD0LE_0RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2330: halts_at_trans (TM_from_str "1RB0RA_0LC0RC_1LE1LD_0LB0LF_1RA1LB_1LE---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2331: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1RE0LF_0LA1LE_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2332: halts_at_trans (TM_from_str "1RB0RD_1LC1RF_0RE0LD_0LB0LD_0RA0LF_1RC---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2333: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD1RE_0LA0LD_1RB1RF_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2334: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_1LD1RC_0RC1LE_1LF0LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2335: halts_at_trans (TM_from_str "1RB1RC_1LA0LC_1RD1LC_---0RE_1LF1RE_0LB0LA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2336: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_1LE0LD_0RC0RB_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2337: halts_at_trans (TM_from_str "1RB---_0RC1RF_1RD0RC_1LE0LD_1RB1LD_1RA1RC") c0 (A,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2338: halts_at_trans (TM_from_str "1RB1LF_1RC1LD_1LD0RC_1LE1LB_0LA---_1LA0LF") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2339: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RE1LD_0LC0LE_0LF0RC_0LA1RA") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2340: halts_at_trans (TM_from_str "1RB0RB_1LC---_1RE0LD_1LC1LD_0RA1RF_1RE0RC") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2341: halts_at_trans (TM_from_str "1RB---_1RC0RC_1RD1RB_0LE0RF_0LF1LE_1RA0LF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2342: halts_at_trans (TM_from_str "1RB1LF_1LC0RD_1LA0LB_1LB0RE_1RC0RB_0RC---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2343: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RA0LB_1RE0RF_0LD1RC_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2344: halts_at_trans (TM_from_str "1RB0LF_0RC1RD_0LD0RA_0RE1LC_1RC0RF_0LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2345: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC1LF_---1RC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2346: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_0RF0LC_---1LA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2347: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD1RC_0LB1LE_1LA0LD_1LA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2348: halts_at_trans (TM_from_str "1RB0RE_0RC1RA_0RD0RC_1RE1LD_1LF1RB_---0LD") c0 (F,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm2349: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_0LD1RB_1LE---_0LA1LE_1RB0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2350: halts_at_trans (TM_from_str "1RB1LA_0RC0RE_1LD0LA_0LA1LC_1RD0RF_---1RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2351: halts_at_trans (TM_from_str "1RB0RE_1RC1RF_1LD0RA_1RA0LE_0LD1RC_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2352: halts_at_trans (TM_from_str "1RB0RC_1LC0RF_0LD0LC_1RE0LA_0RA---_1RE0LC") c0 (E,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2353: halts_at_trans (TM_from_str "1RB1RD_1LC0LE_1LD1LB_1RB0RA_1RF1LE_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2354: halts_at_trans (TM_from_str "1RB1LF_1LC0RE_0RC0LD_1LA1LE_1RA1RC_---0LC") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2355: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1LE1LF_0LA1LE_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2356: halts_at_trans (TM_from_str "1RB0LE_1RC1RF_1RD0LE_1LA---_1LA1LE_1RB0RA") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2357: halts_at_trans (TM_from_str "1RB1LD_1LC0LC_0RA1LB_1RE0RA_1RF0RD_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2358: halts_at_trans (TM_from_str "1RB1RD_1LC1RC_1LA0RC_1RE1LD_1LB0LF_---1LE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2359: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_1LD0LC_1LE0LA_0RB---_1LE0RC") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2360: halts_at_trans (TM_from_str "1RB0RF_0RC---_1LD0RD_0LD0LE_1RE1LF_0LA1RA") c0 (B,1).
Proof. solve_halt 17. Time Qed.

Lemma tm2361: halts_at_trans (TM_from_str "1RB0LC_1LC0LE_1LA1LD_1RE---_1LB0RF_1RE0RF") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2362: halts_at_trans (TM_from_str "1RB0RD_1LC0LC_1RE0LD_0LC0RF_0RB0RA_1RB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2363: halts_at_trans (TM_from_str "1RB1RD_0RC---_1RD0LA_1LE0RF_0LA0LE_1LB1RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2364: halts_at_trans (TM_from_str "1RB---_1RC1RC_1RD0LE_1RE0RA_1LF1LC_0RD0LF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2365: halts_at_trans (TM_from_str "1RB1LF_1RC---_1RD0RB_0RE0LE_1LF1RC_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2366: halts_at_trans (TM_from_str "1RB0RE_1LC---_1LD1LC_1RA0LC_1RE0RF_0RD1RF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2367: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_1LA0LE_1RE1RF_1LA1RB_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2368: halts_at_trans (TM_from_str "1RB0LC_0RC---_1RD0RE_1LE0RF_0LA0LE_1RB0LB") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2369: halts_at_trans (TM_from_str "1RB1LB_1RC0LB_1LA0RD_1RE1LB_1RA1RF_---0LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2370: halts_at_trans (TM_from_str "1RB0LC_0RC0RF_1LD0LE_0LA1LD_0RA---_0RE0LF") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2371: halts_at_trans (TM_from_str "1RB0RD_1LC0RC_1RF0LD_0RE1LC_1LB1RA_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2372: halts_at_trans (TM_from_str "1RB0LA_1LC1RD_---1LD_1LE0RD_1LF0LC_1LA1RA") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2373: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1RD0RE_0LA---_1LA0LF_1RD0LB") c0 (D,1).
Proof. solve_halt 11. Time Qed.

Lemma tm2374: halts_at_trans (TM_from_str "1RB0LA_0RC1RB_1LD1RE_1LA0RF_---1RD_1RC0RB") c0 (E,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2375: halts_at_trans (TM_from_str "1RB1LA_1LC0RB_0LD1RD_0RA1LE_0LC1LF_1LA---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm2376: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD0RF_1LD1RE_0RF1LE_1RA0LF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2377: halts_at_trans (TM_from_str "1RB0RE_1LC0LA_---1LD_1LA0LB_1RA1LF_0LE0LF") c0 (C,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2378: halts_at_trans (TM_from_str "1RB0LF_1RC1RD_1RD0RB_0LE1RA_0LA1LD_---1LC") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm2379: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD0LD_0RA---_1LF0LC_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2380: halts_at_trans (TM_from_str "1RB1LD_1LC0RC_0RD0LD_1RE0LF_1RA---_0LC1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2381: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1LB0LA_0RF0RE_0LA1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2382: halts_at_trans (TM_from_str "1RB0RB_0LC---_1LF1RD_1RE0RA_0RC1RE_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2383: halts_at_trans (TM_from_str "1RB0RE_0RC0RD_1LD0RF_1LE0LD_1RA0LC_0RA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2384: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RE1LD_1LB0LA_0RF0RE_1LD1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2385: halts_at_trans (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RF0LE_0LF1LD_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2386: halts_at_trans (TM_from_str "1RB1RF_1RC0RE_0RD0RA_1LE0LE_0LA0RD_0LD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2387: halts_at_trans (TM_from_str "1RB1RF_1RC1LC_1RD0LC_1LB0RE_1RA1LC_---0LD") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2388: halts_at_trans (TM_from_str "1RB1LD_1RC---_0LA0RC_1LC0LE_0LF1LE_1RC1LA") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2389: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_---1LD_1LE0LF_1RA0RB_1LE1LD") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2390: halts_at_trans (TM_from_str "1RB0LD_1RC1RF_0RD1RA_1LE0RB_0LA0RA_0LC---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2391: halts_at_trans (TM_from_str "1RB0LA_1RC1RE_1LD0RB_---1LB_1RF1LA_1RB0RC") c0 (D,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2392: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_0RD0LD_1LE1RB_1RB0LA_0LA---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2393: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD0RB_1RB1LE_0LC1LF_0RD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2394: halts_at_trans (TM_from_str "1RB0LC_0RC0RB_1LD1RB_0LA1LE_1LA0LF_1RD---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2395: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1LD0RA_1LE1LF_0LA1LC_1LD---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2396: halts_at_trans (TM_from_str "1RB0RD_1RC0LE_1LA1RF_1LB1RD_1RA1LE_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2397: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_---1LA_1RA1LE_0RA0LF_0RE1LB") c0 (C,0).
Proof. solve_halt 14. Time Qed.

Lemma tm2398: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LA_1RC0LB_0LC---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2399: halts_at_trans (TM_from_str "1RB0RF_0RC1RA_1LD0RC_1LE1LA_0LD1LA_---0LA") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm2400: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1RC1LD_0LE0RA_1LB0LF_1LE---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2401: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LF0LB_---1RC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2402: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RA_0LF0LE_1LF---_1LC0RF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2403: halts_at_trans (TM_from_str "1RB0RD_0LC---_1RE1LD_1LC0LF_1RA0RE_1RB0LE") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2404: halts_at_trans (TM_from_str "1RB1LC_1LA1RC_1RD0RF_0RE0RE_1LB1RA_---0LB") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2405: halts_at_trans (TM_from_str "1RB1RF_1LC0LD_1LA1LB_---1LE_1RA1LE_1RB0RA") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2406: halts_at_trans (TM_from_str "1RB0RD_1LC1RA_1RF0LD_1RE0RF_0LB---_0LE1RD") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2407: halts_at_trans (TM_from_str "1RB1RE_0LC1RF_0RD1LC_---1RE_1RA1LF_0RC0LE") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2408: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_0LF0LE_0RA1RD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2409: halts_at_trans (TM_from_str "1RB1LC_1LA1RF_1RD0LA_---1RE_1RF1RB_1LC0RC") c0 (D,0).
Proof. solve_halt 16. Time Qed.

Lemma tm2410: halts_at_trans (TM_from_str "1RB1RE_1LC0RD_1LA1LC_---1RA_1RA0LF_0RA1LF") c0 (D,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2411: halts_at_trans (TM_from_str "1RB0LC_1LC0RB_0LF1LD_0LE---_1LA0RF_0RA1LE") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2412: halts_at_trans (TM_from_str "1RB0LE_1RC1LF_0RD1RA_0RE---_0LF0RB_1LA1LB") c0 (D,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2413: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE0LF_0LA0RA_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2414: halts_at_trans (TM_from_str "1RB0LB_0RC0RF_1RD0RC_1LE0LD_1RA0LD_1RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2415: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1RB0LA_0RF0RE_1RB1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2416: halts_at_trans (TM_from_str "1RB1LC_1RC0RE_1RD0LC_1LA0RA_1LF0RB_1LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2417: halts_at_trans (TM_from_str "1RB1RF_0RC1RB_1LD1RA_0LE0LD_0RA1LD_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2418: halts_at_trans (TM_from_str "1RB0LC_1RC0RB_1LD0RC_1LA0LE_1LC1LF_0LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2419: halts_at_trans (TM_from_str "1RB1LE_0LC0RB_0RA1LD_1LE---_0LF0LD_1LA0RD") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2420: halts_at_trans (TM_from_str "1RB---_1LC0LD_1LD1LA_1RE1LB_1RF0RE_1LD1RF") c0 (A,1).
Proof. solve_halt 14. Time Qed.

Lemma tm2421: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD0LA_1RE0RF_1LB1RA_0LE0LF") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2422: halts_at_trans (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RE_0RC0LD_0RD0RB") c0 (B,1).
Proof. solve_halt 17. Time Qed.

Lemma tm2423: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_0LA1RD_0RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2424: halts_at_trans (TM_from_str "1RB1RD_1RC0RA_1LA0RF_0RE0LD_1LC0RA_1LD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2425: halts_at_trans (TM_from_str "1RB0LA_0RC1RF_0LD1RE_1LA0LE_0RB0RE_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2426: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1LD0RF_0LE0LA_1LD1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2427: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_1LF1LD_0LE0LA_1LA0LB_---1LA") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm2428: halts_at_trans (TM_from_str "1RB---_1LC0RE_0LD1LB_1LA1LC_1RF1RB_1LD1RF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2429: halts_at_trans (TM_from_str "1RB0RA_1LC0RC_1RA1LD_0LE0LF_1LB1RB_0LB---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2430: halts_at_trans (TM_from_str "1RB1LD_1RC---_1LA0RD_1LE1RC_0LF0LA_1RF1LC") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2431: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_0LF1RD_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2432: halts_at_trans (TM_from_str "1RB0LB_1LC1RF_1RD0LC_0LA0RE_0RD0RA_0RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2433: halts_at_trans (TM_from_str "1RB---_1LC0RA_0RD1RC_1LE1RB_0LF0LE_0RB1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2434: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA1LD_0LF0RA_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2435: halts_at_trans (TM_from_str "1RB0LC_1RC0LF_1LD1LE_1LB0LC_0LA0RE_0LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2436: halts_at_trans (TM_from_str "1RB0RA_1LC1RF_0LD1LC_1LE0LE_1RA1LC_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2437: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0RE---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2438: halts_at_trans (TM_from_str "1RB0LA_1RC0RE_1LD0RA_1LA0LD_1RA1RF_0RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2439: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_1LD1RC_1RB1LE_0LF0LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2440: halts_at_trans (TM_from_str "1RB0LD_1RC0LC_1LA1RE_1RA1LA_1RF---_0RA0LA") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2441: halts_at_trans (TM_from_str "1RB0LE_1LC0RB_0LD0LB_1LA0RA_1LF---_1LD0LB") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2442: halts_at_trans (TM_from_str "1RB1RA_1RC1RB_1LD0RC_0LA0LE_1LF0LB_1LD---") c0 (F,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2443: halts_at_trans (TM_from_str "1RB1RF_0LC---_0RD1RC_1LD1LE_1RF0LE_0RC1RA") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2444: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LD0RD_1LA0LE_1LB0RE_0RB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2445: halts_at_trans (TM_from_str "1RB0RF_1LC0LB_1RD0LB_0RA0RE_1RF---_0RC0RF") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2446: halts_at_trans (TM_from_str "1RB1LA_1LC1LD_1RE1RA_1RF0LB_---0RC_1RB1RD") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2447: halts_at_trans (TM_from_str "1RB1LD_0RC0LE_0RD1RC_1RE0LD_1LA1LF_---1LB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2448: halts_at_trans (TM_from_str "1RB1LC_0RC1RA_1RD0RF_0LE1LD_1LA0LD_---0RB") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm2449: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RA_1LD0RA_0LA0RF_---1RE") c0 (F,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm2450: halts_at_trans (TM_from_str "1RB1LE_1LC0RA_1RD1LB_---1RC_0LF0LB_1RC1LE") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2451: halts_at_trans (TM_from_str "1RB0LE_1LC0RB_0RD0LD_1LA1RB_1RB1LF_0LE---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2452: halts_at_trans (TM_from_str "1RB0RD_1LC1RA_1LD0LC_0LE0RF_1RF---_0RA0LB") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2453: halts_at_trans (TM_from_str "1RB0LA_0LC1LB_1RD1LA_0RE0RD_1RF1RD_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2454: halts_at_trans (TM_from_str "1RB0RF_1LC0LD_1LA1LB_1RE1LD_---1RA_1RB1RA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2455: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA0RA_1LD0LF_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2456: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_0RD1RA_1LD1RA_1RC0LE_---0RD") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm2457: halts_at_trans (TM_from_str "1RB0RD_0RC1RE_1LD0RB_0LE---_1RA1LF_0LE0LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2458: halts_at_trans (TM_from_str "1RB1LF_1LC0RE_1LD0LC_1LA1LB_0LA0RA_1RE---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2459: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_0RA1LD_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2460: halts_at_trans (TM_from_str "1RB0RC_1LC1RA_1RA1LD_0LC1LE_0LF0LB_---0LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2461: halts_at_trans (TM_from_str "1RB0RF_1LC0LD_1RB1LB_1RE1LD_---1RA_1RB1RA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2462: halts_at_trans (TM_from_str "1RB0RD_1LC1RD_1LD0LC_1RE0LC_0LE0RF_1RA---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2463: halts_at_trans (TM_from_str "1RB0LD_1RC---_1LA0RF_1LB1LE_0LA1RE_0RE1RF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2464: halts_at_trans (TM_from_str "1RB1RF_1LC0LE_0RA0LD_1LE0RF_1RC0LB_1RE---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2465: halts_at_trans (TM_from_str "1RB1RF_1LC1LE_1RD0LB_0RA1RC_1RD0LC_0RB---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2466: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1LF_0LE0LF_1LA0RC_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2467: halts_at_trans (TM_from_str "1RB1LA_1RC1RE_1LD1RC_1RB0LA_1RF0RC_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2468: halts_at_trans (TM_from_str "1RB---_0RC0RE_1LD0LE_1LC1RF_1RA0RC_1RD0LF") c0 (A,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2469: halts_at_trans (TM_from_str "1RB---_0RC0LF_1LD1RF_0LE0LF_0RB0LD_1RB0RA") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2470: halts_at_trans (TM_from_str "1RB---_0LC0RF_1LA1RD_1LE0LB_1LC1LD_1RB1RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2471: halts_at_trans (TM_from_str "1RB1RE_1LC0LA_---1LD_1RE0LF_1LB1RA_1LA1LC") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2472: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD1LC_1RA1LB_0LF0RE_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2473: halts_at_trans (TM_from_str "1RB1LF_1RC---_1RD0LD_1LE0RE_1RC1RA_0LF0LA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2474: halts_at_trans (TM_from_str "1RB0LA_1LC0RE_1LA0LD_0LB0LF_0RA0RF_0LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2475: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_0RF0RC_---1LA") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2476: halts_at_trans (TM_from_str "1RB1LC_1LC1RD_1LA0LB_0LE0RE_1RF0RA_---0RC") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2477: halts_at_trans (TM_from_str "1RB0RF_1LC0LE_0LD1LB_0RA---_1RF1LE_0LD1RA") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2478: halts_at_trans (TM_from_str "1RB1LC_0RC0RA_0LD0LB_1LE1LC_1RF1LD_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2479: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_0RD0LD_1LE1RB_0LA0LE_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2480: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_1LA0RE_1RB1LE_0LA0RD_---0LD") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2481: halts_at_trans (TM_from_str "1RB0RF_1RC1RA_1RD1LA_1LE---_1LF1LE_1RB0LE") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2482: halts_at_trans (TM_from_str "1RB0RA_1RC0RA_1LD0LC_0LE1LC_1LA1LF_1RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2483: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1LC---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm2484: halts_at_trans (TM_from_str "1RB1LB_1RC1LD_0LA0RC_0LE1LF_1LC0LE_---0RA") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2485: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_0RD0LD_1LE1RB_0LA0LE_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2486: halts_at_trans (TM_from_str "1RB0LB_1LC---_1RE0LD_1LC1LD_0RA1RF_1RE0RC") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2487: halts_at_trans (TM_from_str "1RB0LE_0RC1RA_1LD1RD_0LA1RE_1RF0LB_0RA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2488: halts_at_trans (TM_from_str "1RB0LC_1LA1RB_1RD1LC_1RE1RF_---1RA_1RD0RB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2489: halts_at_trans (TM_from_str "1RB0LB_1LC0RF_0LC0LD_1RE1LC_1RA---_1RA0RD") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2490: halts_at_trans (TM_from_str "1RB0RD_0RC---_1RD0LF_0RE1RA_1LE0LF_1RC0LC") c0 (B,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2491: halts_at_trans (TM_from_str "1RB1LB_0RC0RB_0LD0LF_1LE---_0RF0LC_1LA0RA") c0 (D,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2492: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD0LD_1LE1RB_0LF0LE_1LA1LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2493: halts_at_trans (TM_from_str "1RB0LB_1LC0RF_0RE0LD_1LE1LD_0RA1RA_1RC---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2494: halts_at_trans (TM_from_str "1RB0RB_1LB0LC_1RD1LC_1RE0RF_0RB1RA_---0RB") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2495: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LA_1RC1RA_0LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2496: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_1LA0RE_1RB1LE_0LA0RD_---1RE") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2497: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD1RB_0LA1LD_1RC0LF_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2498: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_0RC1LD_1RE0LF_0LE1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2499: halts_at_trans (TM_from_str "1RB---_0RC0LD_1RD0RF_1RE1RA_1LC0LE_0LE1LF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2500: halts_at_trans (TM_from_str "1RB0LA_1LC1RD_1LA1LC_---0RE_1RF1RE_0RA1RA") c0 (D,0).
Proof. solve_halt 16. Time Qed.

Lemma tm2501: halts_at_trans (TM_from_str "1RB1RD_0RC0RF_1RD0LA_1LE1RB_0LA0LE_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2502: halts_at_trans (TM_from_str "1RB0LF_1RC1RE_0LD0RF_0RA1LE_1RF0LE_1RD---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2503: halts_at_trans (TM_from_str "1RB1RE_1RC---_0LD0LC_1RD0RE_0RF1RA_1LF1RC") c0 (B,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2504: halts_at_trans (TM_from_str "1RB0LD_0RC1RA_1LD0LF_1LB1LE_1LC0RC_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2505: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1RE1LC_1RA0RF_1LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2506: halts_at_trans (TM_from_str "1RB1LC_1LC0RC_1LE1LD_0RA0LE_1RF0LA_---0RB") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2507: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD1LC_1RE0RC_1LB0RA_0LB0LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2508: halts_at_trans (TM_from_str "1RB---_1LC1RF_1LD0LC_0LE1RB_0RA1LC_0RE1RC") c0 (A,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2509: halts_at_trans (TM_from_str "1RB0RE_1LC0RB_0RD0LD_1LA1RB_1RA0LF_0LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2510: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_1LA1LD_1LA1LC_---0RF_1LC1RB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2511: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1RB_1LE---_0LA0RA_1LE0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2512: halts_at_trans (TM_from_str "1RB0LC_1LA0RE_0RD1LC_1RE0LB_1RA0RF_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2513: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD1RC_1LE1RB_0LF0LE_1RB1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2514: halts_at_trans (TM_from_str "1RB0LF_0RC0RD_1LD---_1RE1LA_0RA1LD_1RC0LF") c0 (C,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2515: halts_at_trans (TM_from_str "1RB1RA_0LC1LC_1LD0RD_1RE0LF_0LB0RA_1LE---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2516: halts_at_trans (TM_from_str "1RB1RF_0RC1LF_1RD---_1LE1LD_1RA0LD_1RA0RE") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2517: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1LB1RD_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2518: halts_at_trans (TM_from_str "1RB---_1LC0RB_0LF1LD_0LE1LB_1RA0LC_1RB1LE") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2519: halts_at_trans (TM_from_str "1RB1LE_1RC0RA_1LD1RD_1RF1LE_0LA0LB_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2520: halts_at_trans (TM_from_str "1RB1LB_1LC0RE_0LD1LC_1LA1LF_1RB0RE_0LA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2521: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RE1LD_1LB0LA_1RF0RE_0RD0LB") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2522: halts_at_trans (TM_from_str "1RB1LD_1LC1RF_1RD0LB_1RE0RC_0RA0RE_0LC---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2523: halts_at_trans (TM_from_str "1RB1LC_1LA1RE_0RD0LD_1LB1LA_0RF1RC_---0RB") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2524: halts_at_trans (TM_from_str "1RB0RE_1LC0RD_0LA1LD_1RE1LC_0LF1RA_1LC---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2525: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1LD0RF_1LD0LA_1LD1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2526: halts_at_trans (TM_from_str "1RB0RF_1RC0RB_1LD1LC_1RE0LC_---1RA_0RD1RA") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2527: halts_at_trans (TM_from_str "1RB---_1LC0RA_0RD1RC_1LE1RB_0LF0LE_1LC1LE") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2528: halts_at_trans (TM_from_str "1RB1LC_0LA1RF_0RD1LE_0RB1RD_1LA0LD_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2529: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_0RF1LD_1LA0LC_1LC1RE_0LD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2530: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_1LD0RA_0LE0LC_1LA0RC_1LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2531: halts_at_trans (TM_from_str "1RB1RD_0RC0RB_1LC1LD_1RE1LF_---0RA_1LA0LF") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2532: halts_at_trans (TM_from_str "1RB0LE_1RC1RA_1LD0RB_---1LC_1LA1LF_0LE1RC") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2533: halts_at_trans (TM_from_str "1RB0RC_1LC0RA_1LA1LD_0LE---_0RC0LF_1RC0LC") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2534: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1LD0LC_0RB0LC_0RA1RF_0RE---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2535: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_0RB0LD_1LC0LD_0RA1RF_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2536: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_---0LD_1RE1LB_0RA0LF_0RC1LF") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2537: halts_at_trans (TM_from_str "1RB0RA_1RC1RE_0LD1LC_0RA0LC_0RF1RD_1RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2538: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RA_1LD0LA_0LA0RF_---1RE") c0 (F,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm2539: halts_at_trans (TM_from_str "1RB---_1LC0LD_1LD1LA_1RE1LB_0RF0RE_1LF0LD") c0 (A,1).
Proof. solve_halt 13. Time Qed.

Lemma tm2540: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_0RF1LD_1RD0LE_1RA1LC_---0LE") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2541: halts_at_trans (TM_from_str "1RB0LC_0RC0RB_1LD1LF_0LE0RE_1LA0LB_0RD---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2542: halts_at_trans (TM_from_str "1RB1LB_1RC0LB_1LA1RD_1LE1RD_1RA0RF_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2543: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1LD1LC_1RE1RA_1LC1RF_---0RB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2544: halts_at_trans (TM_from_str "1RB1LC_1RC0RE_1RD0LC_1LA0RA_---1RF_0RC0LF") c0 (E,0).
Proof. solve_halt 5. Time Qed.

Lemma tm2545: halts_at_trans (TM_from_str "1RB1RE_0LC1LB_0RD0LB_1RA0RD_0RF1RC_1RD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2546: halts_at_trans (TM_from_str "1RB1RF_1LC1LD_1RE0LD_1LA0LC_1RA---_0RC1RC") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2547: halts_at_trans (TM_from_str "1RB0RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1LE---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm2548: halts_at_trans (TM_from_str "1RB0RD_1LC0RF_0RE0LD_0LC0LB_1RA0LF_1RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2549: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_1LC0RC_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2550: halts_at_trans (TM_from_str "1RB0RE_1LC0RD_1LD0LC_1RA0LD_1RD1RF_0RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2551: halts_at_trans (TM_from_str "1RB0RA_1LC0LF_1LA1LD_1RE---_0LB1LE_0RA1RF") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2552: halts_at_trans (TM_from_str "1RB1RF_0LC1RE_1RD1LC_0LA1LB_---0LD_1RA0RF") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2553: halts_at_trans (TM_from_str "1RB0RF_1RC0RD_1LD0RA_0LE0LC_0RB1LC_1LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2554: halts_at_trans (TM_from_str "1RB---_1LC0LE_1LA0RD_1RF1LE_1LB0RD_1RE1RB") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2555: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1LE0LF_0LA1LE_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2556: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1RD1LB_0RA1LE_0RF0LC_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2557: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_1LD1RC_0RA1LE_0LF0LA_---0LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2558: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1RE_0LB---_0RA0LA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2559: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1LA_0LE0LF_1LA0RC_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2560: halts_at_trans (TM_from_str "1RB1RC_1RC0LD_1RD0RA_1LE1LB_1LB0LF_---0LA") c0 (F,0).
Proof. solve_halt 9. Time Qed.

Lemma tm2561: halts_at_trans (TM_from_str "1RB---_1RC1LE_1LD0RC_0RF0RB_0LF0LA_1LB1RC") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2562: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE0RF_1RA0RB_0LC---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2563: halts_at_trans (TM_from_str "1RB0LD_0LC1LB_1RD1LA_0RE---_0LA1RF_0RE0RF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2564: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD1RE_0LA0LD_1LB0RF_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2565: halts_at_trans (TM_from_str "1RB0LA_1RC0LE_0RD0LD_1RE0RA_1LB1RF_0LB---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2566: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_1LA1LD_1LA1LC_---0RF_1LD1RB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2567: halts_at_trans (TM_from_str "1RB0RE_1LC1LD_0RA0LC_1RA0LB_1RF---_1RD1RD") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2568: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA1LD_1RD0LF_1LE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2569: halts_at_trans (TM_from_str "1RB---_0RC0RB_1RD0LF_0RE1RA_1RF0LA_1LC0LF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2570: halts_at_trans (TM_from_str "1RB1LB_1RC0LA_1RD1RE_1LB1RF_0RB0LB_1RE---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2571: halts_at_trans (TM_from_str "1RB0RB_0RC0RF_1RD1RE_1LE0LE_1RA0LD_0LA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2572: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RF_0LC0LE_1LD---_1LD0RB") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2573: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LA1LD_1LA0LC_1LF1RE_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2574: halts_at_trans (TM_from_str "1RB1LC_0LA1RB_1LA0RD_1LE1RC_0LF1LB_---1LE") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2575: halts_at_trans (TM_from_str "1RB0RF_1RC1RE_1RD0RA_0LE---_0LF1LF_1LB0LE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2576: halts_at_trans (TM_from_str "1RB1RE_1LC0RB_1LD1RC_---0RA_1LF1RB_0LA0LF") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2577: halts_at_trans (TM_from_str "1RB0LB_1LC0RC_1RA1RD_1RF1LE_0LE0LD_0RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2578: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1LF0LD_1LA1LB_1RA0RB_---0LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2579: halts_at_trans (TM_from_str "1RB---_0LC0RC_1RD1LA_1LE0RB_1LF0LE_1LC1LD") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2580: halts_at_trans (TM_from_str "1RB0LF_1LC1RF_1LD1RC_---0LE_1LA1LF_1LE0RB") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2581: halts_at_trans (TM_from_str "1RB1LC_0RC0RF_0LD0RC_0LE---_1LA1LE_1RA1LA") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2582: halts_at_trans (TM_from_str "1RB1LF_1LC1RA_---0LD_1LE1RB_1LA0LC_0LE0RF") c0 (C,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2583: halts_at_trans (TM_from_str "1RB0LC_1RC---_1LD1RE_1LE0LD_1RF0RA_0RC0LC") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2584: halts_at_trans (TM_from_str "1RB0LC_1LC1RE_1RE0LD_1LA0LD_0RA0RF_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2585: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1RD1LC_1RE0LD_1LA0RA_---0RA") c0 (F,0).
Proof. solve_halt 15. Time Qed.

Lemma tm2586: halts_at_trans (TM_from_str "1RB0LC_1LA1RB_1RD1LC_1RE1RF_---1RA_0RC0RB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2587: halts_at_trans (TM_from_str "1RB0LA_0RC---_1LD1RE_1LA0RC_1RA0RF_1RD1LD") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2588: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1RC1LD_0LE0RB_1LB0LF_1LE---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2589: halts_at_trans (TM_from_str "1RB1LC_1RC0RE_1RD0LC_1LE0RA_---1RF_0RC1LA") c0 (E,0).
Proof. solve_halt 5. Time Qed.

Lemma tm2590: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD0LF_1RC---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm2591: halts_at_trans (TM_from_str "1RB0RF_0LC1RE_0LD1LB_1RD1RA_---1LC_1RA0RF") c0 (E,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2592: halts_at_trans (TM_from_str "1RB1RF_1LC1RD_1LA1LC_---0RE_1LC1RB_1RB1RA") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2593: halts_at_trans (TM_from_str "1RB0RD_0RC1RF_1RD0LC_1LE1RA_1LE1LC_---1RC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2594: halts_at_trans (TM_from_str "1RB1RA_1RC1LE_1RD1LC_1LE0RA_---1LF_1LD0LC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2595: halts_at_trans (TM_from_str "1RB0LC_1RC0RB_1LD0RC_1LA0LE_1LC1LF_1RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2596: halts_at_trans (TM_from_str "1RB0LD_0RC1LE_1RD0RD_1LA1RE_0LA0RF_---1RA") c0 (F,0).
Proof. solve_halt 14. Time Qed.

Lemma tm2597: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0RC0LD_1LE---_1LF0LB_1RB1LB") c0 (D,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2598: halts_at_trans (TM_from_str "1RB0LC_0RC1RA_1RD1RC_1LE0RC_---0LF_1LA0LD") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2599: halts_at_trans (TM_from_str "1RB1RE_0LB1RC_0LD---_1RA1LD_0RF0RA_1LB0RE") c0 (C,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2600: halts_at_trans (TM_from_str "1RB---_1RC0RE_1RD0LD_1LE0RA_1RF0LE_0RC0RE") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2601: halts_at_trans (TM_from_str "1RB1LE_1RC0LA_1LD0RB_---1LB_0RB0LF_0RE1LC") c0 (D,0).
Proof. solve_halt 14. Time Qed.

Lemma tm2602: halts_at_trans (TM_from_str "1RB1RF_1LC1RC_1RE0LD_1LC0LD_0RA1RE_0RB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2603: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_0LD0LB_0LE1LD_1RA0LF_1LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2604: halts_at_trans (TM_from_str "1RB0RF_1RC0LE_1RD0RA_0LE---_0LF1LF_1LB0LE") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2605: halts_at_trans (TM_from_str "1RB0RC_1LC0RF_0LE0LD_0LB0LA_1RA---_1LE0RF") c0 (E,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2606: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_1RA1LC_1RF0RE_1LB1RE_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2607: halts_at_trans (TM_from_str "1RB1LE_1RC0RA_1LD1RD_0RF1LE_0LA0LB_---1LB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2608: halts_at_trans (TM_from_str "1RB---_1LC1RD_0LD0LC_1RE1RB_0RA1RF_0RE1LB") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2609: halts_at_trans (TM_from_str "1RB0RE_1RC0LB_1LD0RD_1RA1LB_---0RF_0LA1RC") c0 (E,0).
Proof. solve_halt 12. Time Qed.

Lemma tm2610: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_1RD1LB_---0RE_1RC1LF_0LE0LB") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2611: halts_at_trans (TM_from_str "1RB1LA_1RC0RD_1LA1RF_1LE1RD_0LA0LA_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2612: halts_at_trans (TM_from_str "1RB1LB_1LA1LC_1RD0LC_1RE0LF_0RD1RB_0RA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2613: halts_at_trans (TM_from_str "1RB0LB_0LC0RC_1LE0RD_0RB1LF_1LF---_1LA0LB") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2614: halts_at_trans (TM_from_str "1RB0LD_1LC1RA_1RD1LC_1LE1LA_1RF0LC_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2615: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_0RD0LE_1LE---_0LF0RA_1LA0LC") c0 (D,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2616: halts_at_trans (TM_from_str "1RB0LB_1LC1RD_1LA0LC_0RE0RC_1RA0RF_0LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2617: halts_at_trans (TM_from_str "1RB0LA_1LC0RD_1RA1LA_1RE1LA_1RC1RF_---0LB") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2618: halts_at_trans (TM_from_str "1RB1RF_1LC1LE_---1LD_1LE1LF_1RA1RC_0RA0LB") c0 (C,0).
Proof. solve_halt 10. Time Qed.

Lemma tm2619: halts_at_trans (TM_from_str "1RB1LD_1LC1RC_1LA0RC_1RE1LD_1LB0LF_---1LE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2620: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0RA---_1LF0LC_0LA0RA") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2621: halts_at_trans (TM_from_str "1RB0RC_0LC0RA_1LD0RB_0LE0LF_1LA0RF_1LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2622: halts_at_trans (TM_from_str "1RB0LF_0RC0RD_1LD---_1RE1LA_0RA1LD_0RC0LF") c0 (C,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2623: halts_at_trans (TM_from_str "1RB0RD_1LC1RD_1RA1LC_0RC1LE_0LF---_1LA0LF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2624: halts_at_trans (TM_from_str "1RB0LE_1LB1RC_0RA1LD_---1LA_1LA1RF_0RE0RC") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2625: halts_at_trans (TM_from_str "1RB1RA_1RC1LD_1LB0RA_---1LE_0RA0LF_1RC1LF") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2626: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA1RE_1LB1RF_1LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2627: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_0RD0LC_0LB1RD_0RA1RF_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2628: halts_at_trans (TM_from_str "1RB0RD_0RC0RA_1RD---_1RE1LA_1LF0LF_1RD1LE") c0 (C,1).
Proof. solve_halt 17. Time Qed.

Lemma tm2629: halts_at_trans (TM_from_str "1RB---_0RC0RE_1RD0LA_1LE0LF_0RF0LE_0LD1RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2630: halts_at_trans (TM_from_str "1RB0LF_0LC---_1LF1RD_0RE0RA_1RC0LA_1LE0LF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2631: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_1RA0LD_1RE1LE_0LA---_1LB1RB") c0 (E,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2632: halts_at_trans (TM_from_str "1RB---_1LC0RE_1RA0LD_1LA1LF_0RF1RE_0LC1RF") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2633: halts_at_trans (TM_from_str "1RB0RD_1LC1LB_1RA0LB_1RE0RC_1LF0RB_---1LE") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2634: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RA0LD_0LC1LD_1RF0RC_0RC1RE") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2635: halts_at_trans (TM_from_str "1RB---_1RC1RA_0RD1RF_1LE0RB_0LF0RF_1RB0LD") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2636: halts_at_trans (TM_from_str "1RB0LD_1LC1RE_0LD0LC_1RE1RF_0RA0RF_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2637: halts_at_trans (TM_from_str "1RB1LA_1RC0RD_0LA1RB_1LE1RD_1RE0RF_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2638: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RE1LD_1RA0LF_1RB1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2639: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_0RA1LD_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2640: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1LC1LD_1LE1RD_1LE0LA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2641: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0LF1LD_0LE---_0LB1LA_1LA0LE") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2642: halts_at_trans (TM_from_str "1RB0LF_1LC0LA_---0LD_1LE1RD_0LF1LB_1RF0RD") c0 (C,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2643: halts_at_trans (TM_from_str "1RB1LC_1RC0RA_1LD0RB_0LE0LC_0LA0LF_1LD---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2644: halts_at_trans (TM_from_str "1RB1RE_1LC0LA_---1LD_1RE0LF_1LB1RA_0LD1LC") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2645: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD0RB_1LD1RE_0RF1LE_1RA0LF") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2646: halts_at_trans (TM_from_str "1RB1LC_1LA0LD_1RD0LA_---1RE_1RF1RB_1LC0RC") c0 (D,0).
Proof. solve_halt 16. Time Qed.

Lemma tm2647: halts_at_trans (TM_from_str "1RB1LC_1LA1RB_1LA0RD_1LE1RC_0LF0LB_---1LE") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2648: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LF_1LE1RB_1LC0LE_1RB0LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2649: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_1LD0LC_1LE0LA_1RD---_1RA0RC") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2650: halts_at_trans (TM_from_str "1RB1LA_0RC0LF_0LD1RE_1LE0LA_1RF0LD_---1RA") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2651: halts_at_trans (TM_from_str "1RB1RE_0LC0RC_1RE1LD_1LB1LF_0RA0RE_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2652: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC1LF_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2653: halts_at_trans (TM_from_str "1RB1RE_1RC0RA_1LD0LC_1RE1RA_1LC1RF_0RB---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2654: halts_at_trans (TM_from_str "1RB0RA_1RC0RA_1LD---_1LE0LE_1RB1LF_0LD0RD") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2655: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_1LA0LE_1RC1RF_1LA1RA_1RD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2656: halts_at_trans (TM_from_str "1RB0LE_1LC0RF_1LA0RD_---1RC_0RF1LB_0LB1RE") c0 (D,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2657: halts_at_trans (TM_from_str "1RB0LD_1RC0RA_1LD1RE_0LE1LA_1RA0RF_1RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2658: halts_at_trans (TM_from_str "1RB1RE_0LC1LB_1RE1LD_1LB1LF_0RA0RE_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2659: halts_at_trans (TM_from_str "1RB0RF_1LC---_1LC1LD_0LE0RC_1LF0LD_1RA1RF") c0 (B,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2660: halts_at_trans (TM_from_str "1RB1LC_1RC0RF_1LD0RA_1RB0LE_---1LF_0RA0LA") c0 (E,0).
Proof. solve_halt 15. Time Qed.

Lemma tm2661: halts_at_trans (TM_from_str "1RB1RE_1LC---_0LD1LC_1LE0LC_1RA0RF_1RC0RD") c0 (B,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2662: halts_at_trans (TM_from_str "1RB0LF_1LC1RC_0RA0LD_0LE0RE_0RF0LC_1RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2663: halts_at_trans (TM_from_str "1RB0RA_1LC0RC_1LF0LD_0RD1LE_0LB---_1RA1LC") c0 (E,1).
Proof. solve_halt 14. Time Qed.

Lemma tm2664: halts_at_trans (TM_from_str "1RB1LB_1RC1LD_0LA0RC_0LE1LF_1LC0LE_---1RC") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2665: halts_at_trans (TM_from_str "1RB0LB_1LC0RB_0LF0LD_1LE1LC_1LA---_0RF1RB") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2666: halts_at_trans (TM_from_str "1RB0LC_1RC0RB_1LD0RE_1LA1RA_1RD0LF_0LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2667: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_0RA1LD_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2668: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_1LD1LA_0LE---_1LA0RC_0RC1LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2669: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1LD1RA_0LE0LD_1RB1LD_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2670: halts_at_trans (TM_from_str "1RB1RA_0RC1LD_1RD1LE_1LB1RF_0RA---_1RE0LF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2671: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA1RF_1RA1RC_0LA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2672: halts_at_trans (TM_from_str "1RB0RC_1LC1LE_1RA1LD_1LA---_1RF0LB_0RA1RE") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2673: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0RE_1LD1LF_0LE---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm2674: halts_at_trans (TM_from_str "1RB0RC_1LA1RB_1RF1RD_1LE1RA_0LC0LE_0RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2675: halts_at_trans (TM_from_str "1RB0RE_0RC0RE_1LD1RF_1RA0LD_1LC1RE_---1RD") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm2676: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD---_1LE1LA_1RF1LD_1RA0LB") c0 (C,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2677: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_1LA1RC_1RE0RF_---1LB_1RC0RB") c0 (E,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm2678: halts_at_trans (TM_from_str "1RB---_1LC1RC_1RA1RD_1RE0RD_1LF0LE_1RB1LE") c0 (A,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2679: halts_at_trans (TM_from_str "1RB0RC_1LC1LF_0RD0LD_1RE0LF_1RA---_0LC1RA") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2680: halts_at_trans (TM_from_str "1RB0LE_0RC0RF_1RD0LA_1LE1RB_1LC0LE_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2681: halts_at_trans (TM_from_str "1RB1LC_0LA0RE_0LD1LF_1LA1RD_1RB0RB_0RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2682: halts_at_trans (TM_from_str "1RB0LC_1RC1RF_1LA1LD_0LA1LE_1RA0RA_1RE---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2683: halts_at_trans (TM_from_str "1RB1LA_1LB0RC_1LD1RC_0LF1LE_1RA0LA_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2684: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_1LF1RF_---1LC") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2685: halts_at_trans (TM_from_str "1RB1LB_1RC0RD_0LD0RE_1RE0LE_0RA1LF_0LC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2686: halts_at_trans (TM_from_str "1RB0LB_1RC0RB_0LD0RF_1LE1LD_0LA0LB_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2687: halts_at_trans (TM_from_str "1RB1RD_1LC0LB_1RA1LA_0RE1RF_0RF---_0RC1LB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2688: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_1LD0RE_---1LB_1RF1LB_1RA0RC") c0 (D,0).
Proof. solve_halt 15. Time Qed.

Lemma tm2689: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0RA---_1LF0LC_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2690: halts_at_trans (TM_from_str "1RB1LE_1LC0RD_1RB1LC_1LA1RD_0LF0LC_---0LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2691: halts_at_trans (TM_from_str "1RB0LC_1RC0RA_1LD0RF_1RE0LD_1RF---_1LA0RA") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2692: halts_at_trans (TM_from_str "1RB0RF_1LC0LB_1RD0LB_0RA1RE_0RF---_0RC1RB") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2693: halts_at_trans (TM_from_str "1RB1RD_1LC1RA_1LD1LB_1LE0RB_0LF0LD_1RA---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2694: halts_at_trans (TM_from_str "1RB0RB_1RC1RB_1LD0RA_1LB0LE_0LF0LC_1LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2695: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_0LD1RB_1LE---_0LA1LE_0RE0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2696: halts_at_trans (TM_from_str "1RB0RB_1RC0LB_1LD0RD_1RE1LB_1RA0RF_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2697: halts_at_trans (TM_from_str "1RB1RE_0RC---_1LC1LD_1RE0LD_0RF1RA_0RC1RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2698: halts_at_trans (TM_from_str "1RB1RF_1RC1RA_0LD1LA_1LC1RE_0LC---_1LD0RF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2699: halts_at_trans (TM_from_str "1RB1RF_0RC0RF_1RD0LE_1RE0RA_1LC0LE_0RC---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2700: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1RD0RB_1LE0LD_0RA0LD_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2701: halts_at_trans (TM_from_str "1RB0LE_1LC0RF_1RD0LC_0RE---_0LB1LA_1RA1RC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2702: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0LF_0LC1LE_1LF---_1LC0RC") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2703: halts_at_trans (TM_from_str "1RB0LC_0RC---_1RD0RE_1LE1RF_0LA0LE_1LA0RA") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2704: halts_at_trans (TM_from_str "1RB---_0LC0LE_0RE1RD_1RC0RB_1LF1RA_1LD0LF") c0 (A,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2705: halts_at_trans (TM_from_str "1RB---_1LC1RD_1LE0RB_0RB1RF_0RB0LC_1RA0LF") c0 (A,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2706: halts_at_trans (TM_from_str "1RB1LD_0LC0RF_1LA0RD_1LE---_0LB0RF_0RA0RF") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2707: halts_at_trans (TM_from_str "1RB1LB_0RC1LE_1LD0RE_0LA1LC_1LF0RD_0LC---") c0 (F,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2708: halts_at_trans (TM_from_str "1RB0LD_0RC1RA_1LD0RB_1LE1LF_1RE0RA_---0LD") c0 (F,0).
Proof. solve_halt 11. Time Qed.

Lemma tm2709: halts_at_trans (TM_from_str "1RB0LD_0LC1RA_1LD1LC_1LE1LA_1RF1RA_---0RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2710: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD1RA_1LA0LB_1LD0LF_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2711: halts_at_trans (TM_from_str "1RB1LA_1RC0RD_0LD0RF_1LE1RD_1LE0LA_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2712: halts_at_trans (TM_from_str "1RB1LE_0RC0LA_1RD0RA_1LE1RF_0LA0LD_0RE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2713: halts_at_trans (TM_from_str "1RB0LC_1LC1RB_1RD1LA_1RE0RF_1LA0RB_---0RE") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2714: halts_at_trans (TM_from_str "1RB0RD_0RC0RE_1LD1RD_0LE0RF_1RA0LD_0LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2715: halts_at_trans (TM_from_str "1RB0RF_1LC1RB_1RA0LD_0RE1LD_1LA1LB_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2716: halts_at_trans (TM_from_str "1RB1LF_1RC0LB_0RD1RF_0RE1RA_1RF---_1LA1LB") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2717: halts_at_trans (TM_from_str "1RB0RC_0RC0RB_0LD1RB_1LE---_1RF0LD_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2718: halts_at_trans (TM_from_str "1RB0LC_0LC0RA_1RA1LD_0LC1LE_1LF0RE_1LC---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2719: halts_at_trans (TM_from_str "1RB---_1RC1LB_0RD1RD_1LE0RC_0LF1LA_0LE0LC") c0 (A,1).
Proof. solve_halt 13. Time Qed.

Lemma tm2720: halts_at_trans (TM_from_str "1RB1RF_0RC1RB_1LD1RA_0LE0LD_0RA1LD_1LE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2721: halts_at_trans (TM_from_str "1RB0LA_0RC---_1LC1RD_1RA0RE_1RF1LF_1LA0RC") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2722: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_1LE---_1LF0LD_0LA0RA") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2723: halts_at_trans (TM_from_str "1RB1RE_1LC0LA_---1LD_1RE0LF_1LB1RA_1RE1LC") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2724: halts_at_trans (TM_from_str "1RB0RC_1LC1RF_0RD0LD_1RE0LF_1LB---_0LC1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2725: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_0RC1LD_1RE0LF_1RB1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2726: halts_at_trans (TM_from_str "1RB0LB_1LC0RC_1RA0LD_0RA0LE_0LF---_1LA1LF") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2727: halts_at_trans (TM_from_str "1RB0LF_1LC---_0LD1LC_1RE0LA_0RF0RE_0LB1RE") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2728: halts_at_trans (TM_from_str "1RB0RE_1LC0RD_1RB1LB_1LE1LD_1RF0LD_---0RA") c0 (F,0).
Proof. solve_halt 16. Time Qed.

Lemma tm2729: halts_at_trans (TM_from_str "1RB---_0RC1LE_0LD1RC_1LB0RA_0LF0RE_0LB1LD") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2730: halts_at_trans (TM_from_str "1RB1LE_0RC0RA_0LD1RA_1LA0LB_0RE0LF_1LD---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2731: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1LD0RA_1LA0LD_1LD1LF_1RC---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2732: halts_at_trans (TM_from_str "1RB0RD_1RC0RA_1LD1RB_1LE0LD_0LF0LB_0RA---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm2733: halts_at_trans (TM_from_str "1RB---_1LC0LC_1RE0LD_0LC0RA_0RB0RF_1RB0RD") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2734: halts_at_trans (TM_from_str "1RB1RC_1LC1LB_1LD0RA_1RF1LE_0LF---_0LC1LA") c0 (E,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2735: halts_at_trans (TM_from_str "1RB---_0RC0RB_1LD1LF_0LE0LA_1LF0RC_1RB1LD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2736: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RF---_0RF0RA") c0 (E,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2737: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_1LD1RB_0LA1LD_1RC0LF_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2738: halts_at_trans (TM_from_str "1RB1LD_0LC0RB_0RA1LD_0LE0LF_1LA0RF_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2739: halts_at_trans (TM_from_str "1RB1LA_1LA1RC_0RC0RD_1LE1RD_0LF0LA_---1RD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2740: halts_at_trans (TM_from_str "1RB0LF_1LC0RE_0LA1LD_1LA1RD_---0RD_0RC1LF") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2741: halts_at_trans (TM_from_str "1RB0RF_1LC0RE_1LE0LD_0LC1LD_1RA0LC_0RA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2742: halts_at_trans (TM_from_str "1RB0LF_0RC0RA_1LC0RD_1RB0LE_1LF---_1LA0LE") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2743: halts_at_trans (TM_from_str "1RB1LA_0RC1RB_0LD1RE_1LE0LA_1RF0LD_---1RA") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2744: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_1LE---_1RF0LD_0LA1LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2745: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1LE0LA_---0LF_0RB1LC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2746: halts_at_trans (TM_from_str "1RB1LD_0RC1RF_1RD0LD_1RE0LD_1LA0RA_---0RD") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2747: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1RB0LA_0RF0RE_0LD1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2748: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_0RD1RC_1LE1RB_0LA0LE_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2749: halts_at_trans (TM_from_str "1RB1RA_1LC1LF_1RA1LD_0RE0LE_---1LC_1RE1LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2750: halts_at_trans (TM_from_str "1RB1RF_1LC0RC_1RE0LD_0LC1LC_0RB1RA_0LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2751: halts_at_trans (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RF_1RD---_0RD1RA") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2752: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD0LB_0RA1RE_1RE0RC_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2753: halts_at_trans (TM_from_str "1RB---_1LC0RD_1RF1RD_1RC0LE_1RC1LD_1LE0RA") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2754: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_0RD1RC_1LE1RB_0LA0LE_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2755: halts_at_trans (TM_from_str "1RB1LA_0RC0RE_1LD0LA_1RD1LC_1RD0RF_---1RC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2756: halts_at_trans (TM_from_str "1RB1RC_1LC1RA_1LD0RA_1LE1LC_0LF0LD_1RA---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2757: halts_at_trans (TM_from_str "1RB---_1RC1RA_0LD1RD_0RB1RE_1LE0LF_1LD0LC") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2758: halts_at_trans (TM_from_str "1RB0RA_1LC1RD_0RD1LB_0RF0LE_1LD1LE_---1RA") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm2759: halts_at_trans (TM_from_str "1RB0RB_0LC---_1LF1RD_1RE0RA_0RC0LC_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2760: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_1LD1LA_0LE---_1LA0RF_0RF1LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2761: halts_at_trans (TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE---_1RF0RE_0RA0RF") c0 (D,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2762: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD0LD_0RA---_1RF0LC_0LA1LF") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2763: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1LD0LD_0LA0RA_1LF---_0LA1LC") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2764: halts_at_trans (TM_from_str "1RB---_1RC0RD_1LD0RD_0RE0LE_1RA0LF_0LD1RB") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2765: halts_at_trans (TM_from_str "1RB1RA_1LC0RD_1RD0LC_0RE1LA_0LB1RF_0RB---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2766: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1LA_0LE---_1RF1LE_1LE0LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2767: halts_at_trans (TM_from_str "1RB0LD_1RC0RB_1LA1RB_1LB0LE_1LF1RB_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2768: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LD0LE_1LA1RF_0RE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2769: halts_at_trans (TM_from_str "1RB0RE_1LC0LD_1RB1LB_1RE1LD_0LF1RA_0RC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2770: halts_at_trans (TM_from_str "1RB0RF_0LC0RD_0RA1LB_1RE0LF_0RB1RC_0LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2771: halts_at_trans (TM_from_str "1RB1RA_1LC1LE_1RA0LD_1LB---_1LB0RF_0LB1RE") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2772: halts_at_trans (TM_from_str "1RB0LE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0RE---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm2773: halts_at_trans (TM_from_str "1RB---_1RC0RD_1LD0RA_1RB0LE_1RD0LF_1LB0LD") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2774: halts_at_trans (TM_from_str "1RB1LC_0LA0LE_0LD1LF_1RA0RF_---1RD_1LB0RF") c0 (E,0).
Proof. solve_halt 7. Time Qed.

Lemma tm2775: halts_at_trans (TM_from_str "1RB---_0RC0LC_1RD0LF_1RE1RB_1LC1RA_1RC1LC") c0 (A,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2776: halts_at_trans (TM_from_str "1RB0LC_1LC0RD_1LA0LC_1RE---_1RF0RE_0RA0RF") c0 (D,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2777: halts_at_trans (TM_from_str "1RB1LC_1RC0RE_1RD0LC_1LA0RA_---0RF_0RC1LD") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2778: halts_at_trans (TM_from_str "1RB0LA_0RC0LD_1RD0RE_1LB0LF_0RA---_0LA1RE") c0 (E,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2779: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_1LC0RC_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2780: halts_at_trans (TM_from_str "1RB0LE_0RC0RF_1RD0LA_1LA1RB_1LC0LE_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2781: halts_at_trans (TM_from_str "1RB1LF_0LC0RA_1RD1LB_1LD0LE_1LA0LA_0RB---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2782: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_1RA1LD_1LE0LF_0LC0RC_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2783: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_0LF1LD_1LE0LB_1LB1LD_1LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2784: halts_at_trans (TM_from_str "1RB1RD_0RC0LE_1LD1RC_1LE1LB_0RF0LA_1LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2785: halts_at_trans (TM_from_str "1RB1RC_1LC0LF_1RA0RD_1LE1RD_---1LB_1LC1LB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2786: halts_at_trans (TM_from_str "1RB0LA_0RC1RD_1LA1RE_0RE1RA_1LF0RB_1LA---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2787: halts_at_trans (TM_from_str "1RB1LD_1RC1RF_0LA0RB_1LE0LA_1RC1RA_1RE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2788: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_1RB1LD_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2789: halts_at_trans (TM_from_str "1RB1RF_0RC1RE_1LD0RB_0LE0LD_1RA0RF_0LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2790: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RA1LD_1LB0LF_1LB1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2791: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1RD1LB_0RA1LE_0RF0LC_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2792: halts_at_trans (TM_from_str "1RB0RA_0LC1RA_1LA1LD_0LE1LD_1LB1LF_---1LE") c0 (F,0).
Proof. solve_halt 7. Time Qed.

Lemma tm2793: halts_at_trans (TM_from_str "1RB0LD_0RC0LE_1RD0RD_1LA1RF_1RA0RE_0LA---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm2794: halts_at_trans (TM_from_str "1RB1RF_0RC1RE_1LD0RB_0LE0LD_1RA1LD_0LC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2795: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD0LF_1RE---") c0 (F,1).
Proof. solve_halt 11. Time Qed.

Lemma tm2796: halts_at_trans (TM_from_str "1RB1RD_1LC0RD_0RB0LC_1LF1RE_1RA1RB_0LE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2797: halts_at_trans (TM_from_str "1RB0LE_0RC---_1RD0RC_1RE1RB_1LF0RF_0LA0LF") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2798: halts_at_trans (TM_from_str "1RB1LC_1RC---_1RD1LF_1RE1RF_1LA1LC_0RD0LE") c0 (B,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2799: halts_at_trans (TM_from_str "1RB1LB_1LC0RB_1LD1LB_0LE0LF_1RA0LA_---0LA") c0 (F,0).
Proof. solve_halt 17. Time Qed.

Lemma tm2800: halts_at_trans (TM_from_str "1RB1LE_1RC---_0RD0LD_1LE1RF_0LA0LE_1RC0RA") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2801: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_0RC1LD_1RA0LF_1RB1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2802: halts_at_trans (TM_from_str "1RB0LB_1LC1RB_---1LD_1LE0RF_1LA1RA_0LE1RD") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2803: halts_at_trans (TM_from_str "1RB0RB_1RC0LB_1LD0RD_1RE1LB_1RA1RF_---0LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2804: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_1LF0LB_---1LC") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2805: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1LD1RA_1LE0LD_0RC0RB_0RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2806: halts_at_trans (TM_from_str "1RB1LD_1RC0LA_0LA0RB_0LA1LE_1LF0RE_1LA---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2807: halts_at_trans (TM_from_str "1RB0RA_1LC1LF_1RA1LD_0LE---_1LA0LF_1LE1LC") c0 (D,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2808: halts_at_trans (TM_from_str "1RB0LE_0RC1RB_1LD0RA_1LA1LC_0LC1LF_---1LC") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2809: halts_at_trans (TM_from_str "1RB1RC_0LA0RC_0RD---_1RE0LF_1RF0RA_1LD0LF") c0 (C,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2810: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1RD1LB_0RA1LE_0RF0LC_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2811: halts_at_trans (TM_from_str "1RB1RA_1LC0RD_1RA0LD_1LB0RE_1LB0RF_---0RC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2812: halts_at_trans (TM_from_str "1RB1RE_1LC---_0LD1LC_1LE0LC_1RA0RF_0LC0RD") c0 (B,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2813: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD0LF_1RE0LA_1LC1RA_0LE0LF") c0 (A,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2814: halts_at_trans (TM_from_str "1RB0RD_1LC1RC_0LD1LC_1RE0LC_0RF---_0RA1RF") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2815: halts_at_trans (TM_from_str "1RB0RC_0LC1RE_1RF1LD_1RD0LE_1RA1LC_---1RB") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm2816: halts_at_trans (TM_from_str "1RB---_1RC1RA_1RD0LD_1LE0RB_0LE1LF_1RD0RC") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2817: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1RB_1RE---_0LA1LE_1RE0LD") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2818: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1LB0LA_0RF0RE_1LB1RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2819: halts_at_trans (TM_from_str "1RB---_1RC1RF_0LD1RB_0RA1LE_1LC0LE_0RD1RE") c0 (A,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2820: halts_at_trans (TM_from_str "1RB1LF_1RC---_0RD1RC_1LD1RE_1RC0RA_0LA0LF") c0 (B,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2821: halts_at_trans (TM_from_str "1RB1LB_1RC0LB_1LA0RD_1RE1LB_1RA0RF_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2822: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1RD1LB_0RA1LE_0RF0LC_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2823: halts_at_trans (TM_from_str "1RB0RF_0RC1RE_1LD0RB_0LE0LD_1RA1LD_0RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2824: halts_at_trans (TM_from_str "1RB0LF_1RC0LB_0RD---_1LD1RE_0RF1LF_1RA0LB") c0 (C,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2825: halts_at_trans (TM_from_str "1RB0LB_1LC1RE_1RA0LD_1RC1LC_1RF---_0RC0LC") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2826: halts_at_trans (TM_from_str "1RB---_1LC0RB_0RD1RC_1LE1RB_0LF0LE_1LA1LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2827: halts_at_trans (TM_from_str "1RB0LC_1LA1RE_1LD1LA_1RA1RD_0RF---_0RA1RC") c0 (E,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2828: halts_at_trans (TM_from_str "1RB0LE_1RC1RF_1LD0RA_---1LA_1LB0LC_0RB0LD") c0 (D,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2829: halts_at_trans (TM_from_str "1RB1RD_0LC1LD_1LB1LD_1RA1RE_1LF0RE_1LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2830: halts_at_trans (TM_from_str "1RB0RE_0RC0RD_1LD1RB_1LE0LC_1RF1LD_---1RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2831: halts_at_trans (TM_from_str "1RB1LF_1LC1RB_1LA0LD_1RE1LD_1RE0RB_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2832: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA0RE_1LA1RF_0RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2833: halts_at_trans (TM_from_str "1RB1RA_0LC0RA_1LF1RD_1LE0LB_1LC1LD_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2834: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA---_1RF0LE_0LA1LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2835: halts_at_trans (TM_from_str "1RB0RE_0RC1RA_0LD---_1LA0LF_1LF1RE_0RC1LD") c0 (C,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2836: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_1LD---_1LA0LA_0LD0RD_1RB0RF") c0 (C,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2837: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD1RD_1RE0LE_1LB0RA_1LC1LF") c0 (A,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2838: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA1LD_1RD0LF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2839: halts_at_trans (TM_from_str "1RB0RF_0RC0LE_1LC1RD_0RA0LE_1LB0LE_1RA---") c0 (F,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2840: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD1LC_1RA1LB_0LF0RD_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2841: halts_at_trans (TM_from_str "1RB0LF_1LC0RD_1LA0LB_1LB0RE_1RC0RB_1LC---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2842: halts_at_trans (TM_from_str "1RB1RD_0RC0RD_1RD0LA_1LE0LF_0LA0LE_---1RA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2843: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RE0LD_1LB1LF_0RE0RA_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2844: halts_at_trans (TM_from_str "1RB0RC_1LC1LD_1RD0LC_0LB0RE_0RF1RA_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2845: halts_at_trans (TM_from_str "1RB1LA_0LC0RF_---1RD_0RE0RC_1LE0LA_0RC0RE") c0 (C,0).
Proof. solve_halt 1%nat. Time Qed.

Lemma tm2846: halts_at_trans (TM_from_str "1RB0LC_1RC1RE_1LD1LA_---1LC_1LE0RF_0RB1RF") c0 (D,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2847: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LD_0RE0RA_0LE1LF_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2848: halts_at_trans (TM_from_str "1RB0LA_0RC1LA_0LD0RE_1LE1LF_1RC0LD_1LB---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2849: halts_at_trans (TM_from_str "1RB1LE_1RC0RC_1RD1RB_0LA1LD_1LF0LD_---1LB") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2850: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA---_1RA0RF_1RD1RE") c0 (D,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2851: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_0RF0LE_0LD1RA") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2852: halts_at_trans (TM_from_str "1RB0RD_1RC1RB_1LD0RE_1RF1LC_1RC0LC_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2853: halts_at_trans (TM_from_str "1RB0RD_1LC1RF_1LE1RA_1RC1LD_0RB0LE_---0LD") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2854: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_0LD---_1LE1LD_0LF0RD_1LA0LA") c0 (C,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2855: halts_at_trans (TM_from_str "1RB1LD_1RC---_1RD0LA_0RE0RA_1LE0LF_1LC1RF") c0 (B,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2856: halts_at_trans (TM_from_str "1RB1RA_1LC0RC_1RF1LD_0RA0LE_1RD0LC_1LD---") c0 (F,1).
Proof. solve_halt 15. Time Qed.

Lemma tm2857: halts_at_trans (TM_from_str "1RB0LE_1LC0RB_0LF1LD_1LE---_1LA0RC_0RA0LC") c0 (D,1).
Proof. solve_halt 9. Time Qed.

Lemma tm2858: halts_at_trans (TM_from_str "1RB1LA_1RC0LF_1RD0RA_0RE0LD_1LA---_1LA1LB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2859: halts_at_trans (TM_from_str "1RB0RC_0LC1RE_0RF1LD_1RD0LE_1RA1LC_---0LE") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm2860: halts_at_trans (TM_from_str "1RB0LD_0RC0RB_0LD0LF_1LE1LA_0LA1LC_0RA---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2861: halts_at_trans (TM_from_str "1RB1LE_0RC0RD_1LD1RE_1LC1RA_1RF0LA_---1RA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2862: halts_at_trans (TM_from_str "1RB0RC_1LA0LD_1RF1RD_1LE1RA_0LC0LE_0RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2863: halts_at_trans (TM_from_str "1RB1RE_1RC1RA_0LD---_0LF1LA_1LF0RE_1LD1RC") c0 (C,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2864: halts_at_trans (TM_from_str "1RB1LA_1LB0RC_1LD1RC_1LE0LA_---0LF_1RA1LC") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2865: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0RC0LD_1LE---_1LF0LB_1RA1LB") c0 (D,1).
Proof. solve_halt 8. Time Qed.

Lemma tm2866: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD1RC_0RC1LE_1LF0LA_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2867: halts_at_trans (TM_from_str "1RB1RC_1LC0RA_0RF1LD_1RA0LE_1RA1LC_---0LD") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2868: halts_at_trans (TM_from_str "1RB0RC_0LC1LB_1LD0LB_1RE0RA_0RF1RD_1LA---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2869: halts_at_trans (TM_from_str "1RB1LD_1LC0RB_0RE0RA_0LE1LF_1LA1RB_1RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2870: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0RD0LE_1LE0LF_0LA0RA_1LD---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2871: halts_at_trans (TM_from_str "1RB1LF_1RC0LA_1RD0RB_1LE0RC_0LA0LD_1RE---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2872: halts_at_trans (TM_from_str "1RB0LA_1LC0RE_1RD0LD_1LA0LF_0RC---_1LB0RE") c0 (E,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2873: halts_at_trans (TM_from_str "1RB0RA_1RC0RA_1LD0LC_0LE1LC_1LA1LF_0LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2874: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LD0LA_1LE0LF_0RA1LC_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2875: halts_at_trans (TM_from_str "1RB0LF_1RC---_1RD0RE_1LE1LF_0RA0LA_0LE1RC") c0 (B,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2876: halts_at_trans (TM_from_str "1RB0RB_0LC1RA_1LA1RD_1LE0LC_1LF0LD_0LC---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2877: halts_at_trans (TM_from_str "1RB1RC_1LA1RA_1LD0RC_1LE---_0LF1LA_1LE1LA") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2878: halts_at_trans (TM_from_str "1RB0RA_1RC1RA_1LD1LF_1LA0LE_---1LF_0LC1LC") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2879: halts_at_trans (TM_from_str "1RB0LE_0LC1RF_1LA0RD_1RC0RE_0RB1RC_1RC---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2880: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA0RE_1LA0RF_1LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2881: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1LF1RD_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2882: halts_at_trans (TM_from_str "1RB0RE_0LC1RD_0LD1LB_1RE0LF_1RA1LB_---1LA") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm2883: halts_at_trans (TM_from_str "1RB0RA_0RC0RE_0LD---_1LE1LC_1LF0RD_1RA1LE") c0 (C,1).
Proof. solve_halt 14. Time Qed.

Lemma tm2884: halts_at_trans (TM_from_str "1RB0RF_0RC---_1RD1LF_1LE0LE_0RC1LD_1RA0RC") c0 (B,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2885: halts_at_trans (TM_from_str "1RB---_0RC1RA_1RD0RC_1RE0RA_1LF0LE_1RC0LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2886: halts_at_trans (TM_from_str "1RB1LC_1LC1RF_1LA0RD_1LD1LE_0LB---_0RB0RC") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2887: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_0LD0RA_1RA1LE_---1LD_0RD1LA") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2888: halts_at_trans (TM_from_str "1RB0RF_1LC0RC_1RA0LD_1LE0LE_1RB0LC_0RC---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2889: halts_at_trans (TM_from_str "1RB0LF_1RC0LE_1LD0RE_1LB1LD_1RB0LA_---0LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2890: halts_at_trans (TM_from_str "1RB0LD_1RC0RE_1LA1RF_1LC1LD_0LB1RE_---1RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2891: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_1LD0RE_1RB0LA_0LD0RA_---0LA") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2892: halts_at_trans (TM_from_str "1RB1LD_0RC1RD_1LA1RF_0LA0RE_---1RC_1LD1RA") c0 (E,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2893: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RA1LD_0LB0LE_1LF0RA_0LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2894: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1LA1LC_1RA1RF_0RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2895: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0LD1LC_1LE1LF_1RB0LA_0LE---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2896: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_1RE1LD_1LC1LF_---1RC_0LD0LB") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2897: halts_at_trans (TM_from_str "1RB---_0LC1LB_1RE1LD_1RB0LA_0RF0RE_1RA1RE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2898: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RE1LD_0LB0LF_1LD0RA_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2899: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_1RD1RF_1LB0RC_1LA0LE_1LE---") c0 (F,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2900: halts_at_trans (TM_from_str "1RB0RF_0LC0RD_1RA1LD_1RE0LF_---0RC_1RC0LC") c0 (E,0).
Proof. solve_halt 5. Time Qed.

Lemma tm2901: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_0RD---_1RE1RC_0LF1RA_1RC1LE") c0 (C,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2902: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD0RC_0RE0LE_1LB1RC_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2903: halts_at_trans (TM_from_str "1RB1LB_1RC1LE_1RD1RF_1LB1LD_---0LA_1LD1RC") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2904: halts_at_trans (TM_from_str "1RB1LC_1RC0RE_1RD0LC_1LA0RA_---1RF_1RB1LB") c0 (E,0).
Proof. solve_halt 9. Time Qed.

Lemma tm2905: halts_at_trans (TM_from_str "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LE---") c0 (F,1).
Proof. solve_halt 14. Time Qed.

Lemma tm2906: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_1LD1LA_0LE---_1LA0RC_0RF1LC") c0 (D,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2907: halts_at_trans (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1LA0LE_0LF1LD_---1LA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2908: halts_at_trans (TM_from_str "1RB1RA_0RC0LE_1RD0RD_1LE1RF_1RA0LD_0RE---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2909: halts_at_trans (TM_from_str "1RB1RE_1LC0RF_1RD1LC_---0RA_1RA0LF_0RC1LE") c0 (D,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2910: halts_at_trans (TM_from_str "1RB0RA_1LC1LB_0RD0LB_---1LE_1RF0RC_0RA1RE") c0 (D,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2911: halts_at_trans (TM_from_str "1RB1LD_1RC1RE_1LA0LC_1LB1LD_1RF0RE_1RB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2912: halts_at_trans (TM_from_str "1RB0RF_0RC1RA_1LD1RA_0LE0LD_1RA1LD_0RA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2913: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_0RD1RC_1LE1RB_0LA0LE_1LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2914: halts_at_trans (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0LB_0LF0LC_1RB1LB") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2915: halts_at_trans (TM_from_str "1RB0RF_0RC0RC_1LD1RE_1LE1RA_1RD1LA_---0LD") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2916: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_0LC1LA_1RE1RC_1RF---_1LA0RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2917: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_0RD0RA_1LE1LD_1LA0LF_0RD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2918: halts_at_trans (TM_from_str "1RB0RA_1LC1LD_1RD0LC_1LB1RE_---1RF_0RC1RA") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2919: halts_at_trans (TM_from_str "1RB1LA_0RC0RF_1LD0LA_1LE1LC_---1RC_1RD0RE") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2920: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_1LF1LD_1LB---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2921: halts_at_trans (TM_from_str "1RB0RF_1RC0LB_1RD1RE_1LE1LF_0RA1LB_---0RC") c0 (F,0).
Proof. solve_halt 5. Time Qed.

Lemma tm2922: halts_at_trans (TM_from_str "1RB0LA_1LC1LD_1RA1LA_1LE1RD_1RC0RF_---1RE") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2923: halts_at_trans (TM_from_str "1RB0RF_1LC1RD_0LD1LA_1RA0RE_1LC1RE_---0LC") c0 (F,0).
Proof. solve_halt 8. Time Qed.

Lemma tm2924: halts_at_trans (TM_from_str "1RB0RD_1LC0RC_1RF0LD_0LE0LD_1RF0LA_0RA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2925: halts_at_trans (TM_from_str "1RB1LC_0RC1RC_0RD0LE_1RE1RC_1LF1LA_---1LA") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm2926: halts_at_trans (TM_from_str "1RB---_1RC0LC_1RD0RB_1LE1RF_1LC0LE_0RC1RA") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2927: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0LE0RD_1RB1LB_1LD1LF_0LD---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2928: halts_at_trans (TM_from_str "1RB1RD_1LC1LE_1RE1LD_1RB1LF_---0RA_1LC0LB") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2929: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD1RC_1LE0LF_0LF0LE_0RA1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2930: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1LD0LD_0LA0RA_1LD0LF_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2931: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA1LD_1LF0RA_1RD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2932: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_1LA0LA_1LA0LE_1RC1LE_0RA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2933: halts_at_trans (TM_from_str "1RB1RD_0RC1RF_1RD---_1LE1RA_0LA0LE_0RB1RE") c0 (C,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2934: halts_at_trans (TM_from_str "1RB0LC_0RC---_1RD0RE_1LE0RF_0LA0LE_1RB1RA") c0 (B,1).
Proof. solve_halt 4. Time Qed.

Lemma tm2935: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_1LD0RB_0LE0LC_1RA1LF_1RD---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2936: halts_at_trans (TM_from_str "1RB---_0RC1RE_1RD0RA_1LE0RE_1RC0LF_1LB0LD") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2937: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1RA1LD_0LE0LF_1LC0RF_1LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2938: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LD0LA_1LE0LF_1RB1LC_---0RB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2939: halts_at_trans (TM_from_str "1RB0LA_1RC0RB_0RD1RA_1LE1RD_1LA0LF_---0RB") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm2940: halts_at_trans (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0LD_1RB0RF_1RE---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2941: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1RD1RB_0LE---_0LA1LE_1RE0LF") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2942: halts_at_trans (TM_from_str "1RB0LD_1LC0RE_1RA1LB_0LF1RC_1RD1RB_---1LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2943: halts_at_trans (TM_from_str "1RB0LE_1LC1RE_0RE0LD_1LA---_0RB1LF_0LA0RF") c0 (D,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2944: halts_at_trans (TM_from_str "1RB1LB_1LC1RE_---1LD_1LA0LF_0RF0RD_1LD1RE") c0 (C,0).
Proof. solve_halt 16. Time Qed.

Lemma tm2945: halts_at_trans (TM_from_str "1RB1RD_1LC1RF_1RE0LD_1LB1LE_0LE0RA_---0RE") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2946: halts_at_trans (TM_from_str "1RB0RF_1LC0LE_0LD1LB_1RE---_1LF0LA_0RA1RF") c0 (D,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2947: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RA1LD_1RA0LF_0LE1RA_---1LC") c0 (F,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2948: halts_at_trans (TM_from_str "1RB---_1LC0RB_1LE0RD_0RA1LB_0LF1LD_1RA0LD") c0 (A,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2949: halts_at_trans (TM_from_str "1RB1LA_1LC0RC_0RE1RD_1LF0LA_1LB1RA_---0LD") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2950: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RA_---1RE") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2951: halts_at_trans (TM_from_str "1RB0LD_1RC0RE_1RD1LF_1LA1LD_0RF1RB_---1LD") c0 (F,0).
Proof. solve_halt 3. Time Qed.

Lemma tm2952: halts_at_trans (TM_from_str "1RB0RF_1LC---_0RD0LC_1LB1LE_1RA1RC_0RE1RF") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2953: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RF1LD_---1LB") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2954: halts_at_trans (TM_from_str "1RB0LE_0LC1LB_1RD1LA_0RE0RD_1LF1RD_1LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2955: halts_at_trans (TM_from_str "1RB1LA_1LC0RF_0LC0LD_1RD1RE_1LA---_0RB1RF") c0 (E,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2956: halts_at_trans (TM_from_str "1RB0LA_0RC0LE_1RD1RF_1LB1RC_1RF1LA_1RB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2957: halts_at_trans (TM_from_str "1RB---_1LC0LB_0LF1LD_0RE0LB_0LA0RC_1RD1LA") c0 (A,1).
Proof. solve_halt 10. Time Qed.

Lemma tm2958: halts_at_trans (TM_from_str "1RB0LE_0RC1RB_1LD0RA_1LA1RE_0LC1LF_---1LC") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2959: halts_at_trans (TM_from_str "1RB0RA_0RC1RE_1LD1RC_1LE0LF_1RA0LE_---0RA") c0 (F,0).
Proof. solve_halt 10. Time Qed.

Lemma tm2960: halts_at_trans (TM_from_str "1RB1RD_1LC0LB_0RA1LB_0RE1RD_1RC1RF_---1RE") c0 (F,0).
Proof. solve_halt 7. Time Qed.

Lemma tm2961: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_0RD0LB_1RE1LA_0RF---_1LF1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2962: halts_at_trans (TM_from_str "1RB---_1RC0RA_1RD0RB_1LE0RC_0LF0LD_0LB0LD") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2963: halts_at_trans (TM_from_str "1RB1RD_1LC0LE_1LD1LB_1RB0RA_---1LF_1RA1LF") c0 (E,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2964: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0RC---") c0 (F,1).
Proof. solve_halt 17. Time Qed.

Lemma tm2965: halts_at_trans (TM_from_str "1RB1RE_0LC1LB_1RE1LD_1RB0LF_0RA0RE_1RC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2966: halts_at_trans (TM_from_str "1RB1LD_1RC0LB_0RD1RD_1RE1LB_0RF---_1LF1RA") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2967: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0LD_1RF1LD_1RA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2968: halts_at_trans (TM_from_str "1RB1LA_1LB0RC_1LD1RC_0LF1LE_1LA0LA_---1LC") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2969: halts_at_trans (TM_from_str "1RB0LB_1LC0RD_1LD0LB_1RE0LA_1LF0RE_1LA---") c0 (F,1).
Proof. solve_halt 12. Time Qed.

Lemma tm2970: halts_at_trans (TM_from_str "1RB1LF_1LC1LB_1RD0LB_---0RE_1RF0RC_1LA0RB") c0 (D,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2971: halts_at_trans (TM_from_str "1RB0LE_0RC0RD_1LA1RA_1RC1RE_0LA0RF_1LE---") c0 (F,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2972: halts_at_trans (TM_from_str "1RB0LC_1RC0RB_1LD1RB_1LE0LA_0LF0LD_1LA---") c0 (F,1).
Proof. solve_halt 7. Time Qed.

Lemma tm2973: halts_at_trans (TM_from_str "1RB---_1RC0RA_0RD1RC_1LE1RB_0LF0LE_1RC1LE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm2974: halts_at_trans (TM_from_str "1RB1RC_1RC0LE_1RD1LC_1LB0RF_---0LC_0LA1RF") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2975: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_1LD0RE_1LB1LD_---1RC_0RF1LA") c0 (E,0).
Proof. solve_halt 4. Time Qed.

Lemma tm2976: halts_at_trans (TM_from_str "1RB0RA_1LC0RF_0LF0RD_1LC1LE_1LB---_1RA0LD") c0 (E,1).
Proof. solve_halt 16. Time Qed.

Lemma tm2977: halts_at_trans (TM_from_str "1RB1LD_1RC1LC_1LA1RE_0LA0LB_0RF0RA_---0RA") c0 (F,0).
Proof. solve_halt 18. Time Qed.

Lemma tm2978: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0LF1LD_0LE---_0LB0RC_1LA0LE") c0 (D,1).
Proof. solve_halt 6. Time Qed.

Lemma tm2979: halts_at_trans (TM_from_str "1RB0RC_1LC0RE_---0LD_1LA1RB_1RF0LF_1RA1RE") c0 (C,0).
Proof. solve_halt 6. Time Qed.

Lemma tm2980: halts_at_trans (TM_from_str "1RB0RA_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA1LB") c0 (E,1).
Proof. solve_halt 18. Time Qed.

Lemma tm2981: halts_at_trans (TM_from_str "1RB1RF_0LC1LB_0RE1LD_1LC0LA_---0RA_0RA0RD") c0 (E,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2982: halts_at_trans (TM_from_str "1RB0RD_0LC1RA_---0LD_1LE1LF_0RB1RE_0LD0LA") c0 (C,0).
Proof. solve_halt 2. Time Qed.

Lemma tm2983: halts_at_trans (TM_from_str "1RB---_1LC1LD_1LA0LB_1LB1RE_1RF0RD_1LA0RC") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2984: halts_at_trans (TM_from_str "1RB---_1LC1LD_1LA0LB_1LB1RE_1RF0RD_1RC0RC") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2986: halts_at_trans (TM_from_str "1RB---_1LC1LD_1LA0LB_1LB1RE_1RF0RD_0RB0RC") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm2987: halts_at_trans (TM_from_str "1RB---_1LC1LD_1LA0LB_1LB1RE_1RF0RD_0LA0RC") c0 (A,1).
Proof. solve_halt 2. Time Qed.

