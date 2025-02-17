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

Lemma tm1: halts_at_trans (TM_from_str "1RB1LD_1RC0LB_0LA0RB_1RD1RE_0RA1RF_1LB---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB0LA_1RC---_1RD1RC_0RE1RF_0LF1RE_1LA0RB") c0 (B,1).
Proof. solve_halt 8. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1LB1RC_1RA1LD_0RB1RE_1LB0LB_0RF1RA_---0LC") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB1RA_1LB0RC_---1RD_0RE1LF_1LF1RA_1LD0LF") c0 (C,0).
Proof. solve_halt 7. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1LB0RB_0LC1RF_1RD1LD_1RE0LB_0RA1RE_0LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB0LA_0RC0RE_1LC1RD_1RB1LA_---0RF_0LF1RC") c0 (E,0).
Proof. solve_halt 20. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB---_1RC0RE_0RD0RB_1LE0RA_0LF0LE_1RB1LE") c0 (A,1).
Proof. solve_halt 16. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1LD0RD_0LE1RF_1RA1LA_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1LB---_0LC0LF_1RD0LD_0RE1LE_1LA0RB_0RA0LE") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1LB0LA_1RC0LD_0RF0RD_1RE0LA_0RB---_1LF1RA") c0 (E,1).
Proof. solve_halt 12. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1LB1RE_1LC1LF_0RD1RA_---1RA_0RB1RC_1LB0LB") c0 (D,0).
Proof. solve_halt 4. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB1RA_0RC1RD_0LD1RC_1LE0RF_1RF0LE_1RA---") c0 (F,1).
Proof. solve_halt 4. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB---_0RC0LF_0RD0LA_1LE1LB_1LF0LC_1LB0LD") c0 (A,1).
Proof. solve_halt 2. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1LB0RB_0LC1RF_1RD1LD_1LE0LB_0RA1RE_0LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1LB0LB_1RC1LA_1LB1RD_0RB1RE_0RF1RC_---1RC") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB0LD_0RC1RB_1LD0RD_0LE1RF_1RA1LA_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1LB0RD_1RC1LF_0RE0LD_---0LB_1RA1RC_0LB1RC") c0 (D,0).
Proof. solve_halt 4. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB0RD_0RC0RA_1LD0RF_0LE0LD_1RA1LD_1RA---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB0LE_1RC---_1LD0RF_0RA1LE_0LD1LF_0LA0RE") c0 (B,1).
Proof. solve_halt 6. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1LB1RF_0RC0LD_1LD1RA_1RE0LA_0RB1LD_0LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1LB0RF_0LC0LB_1RD1LB_1RE0RB_0RA0RD_1RD---") c0 (F,1).
Proof. solve_halt 16. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB0LA_0LC0RA_1RA1LD_1RD1RE_0RC1RF_1LA---") c0 (F,1).
Proof. solve_halt 5. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB---_0RC1RF_1RD0LE_1LC0LF_0LD1LE_0RB0RA") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB0LC_1LA0LD_0LB1LC_0RF0RE_1RF---_0RA1RD") c0 (E,1).
Proof. solve_halt 6. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB1LB_1LC0LE_0RD1RC_1LE0RE_0LA1RF_0LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB0RB_1RC0LF_1LD0RD_1RE0LD_0RF---_1LC1RA") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB1LB_1RC0LE_0RD1RC_1LE0RE_0LA1RF_0LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB1LC_1LC0LB_1RD0LB_0RA1RE_1RF---_0RC0RF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB0LA_0RC0RA_1LD1RF_1LE0LE_1RB0LD_---1RB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB---_0RC1RE_1RD0RA_1LE1LF_1RB0LD_1RB0LF") c0 (A,1).
Proof. solve_halt 9. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1LB---_0LC0LB_1RD1RA_0RE1RC_1RF0RD_1RB0RC") c0 (A,1).
Proof. solve_halt 6. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1LB0RB_0LC1RF_1RD1LD_1RE0LB_0RA0LA_0LD---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1LB0LA_1RC0LD_1LA0RD_1LE1RF_0RB1RE_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1LB0LA_1RC1LB_1RE0RD_1LC0LF_0RF0RB_1LA---") c0 (F,1).
Proof. solve_halt 6. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_1LD1RF_1LE0LE_1RB0LD_---1RB") c0 (F,0).
Proof. solve_halt 4. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB0LE_0RC1LA_0RD0LA_1LA1RE_1LC1RF_0LA---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1LB1RD_1RC0LD_0RE1LB_1LE1RF_0RA0LB_0LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB---_1LC1RE_0RB0LD_0LC0LF_1LD1RA_1RF0RE") c0 (A,1).
Proof. solve_halt 3. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB1LE_0RC1RF_1LD0RA_1LE0LD_1RC1LD_---0RD") c0 (F,0).
Proof. solve_halt 6. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB0RF_1LC1LE_1RD0LB_0RA1RC_1RD0LE_1RD---") c0 (F,1).
Proof. solve_halt 9. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1LB0LA_1RC0LD_0RF0RD_1RE1RF_0RB---_1LF1RA") c0 (E,1).
Proof. solve_halt 12. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB1RB_1LC0RC_0RE1LD_1RA1LF_1RD---_0LC0LF") c0 (E,1).
Proof. solve_halt 4. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1RB0LD_1LC0RD_1LA0LC_1LE1RF_0RA1RE_0LC---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1RB1LB_1RC0LE_0RD0LD_1LE0RE_0LA1RF_0LB---") c0 (F,1).
Proof. solve_halt 3. Time Qed.

Lemma tm45: halts_at_trans (TM_from_str "1RB0LB_0LC0RA_1RD1LB_0RE---_1RF1RD_1LA1RF") c0 (D,1).
Proof. solve_halt 2. Time Qed.

