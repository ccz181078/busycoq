From BusyCoq Require Import RWLAcc62.

Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.

Ltac solve_halt' bsz bmaxT use_acc mnc T :=
  eapply (decide_halt_spec _ bsz bmaxT use_acc mnc T);
  native_check_eq.

Ltac solve_halt'' bsz use_acc :=
  match goal with
  | |- halts_at_trans (TM_from_str ?x) c0 _ =>
    idtac x;
    solve_halt' bsz 3200 use_acc 2%N 100000000%N
  end.

Fixpoint get_len(ls:RWL):N :=
match ls with
| (w,_,n)::t => (N.of_nat (List.length w) * n + get_len t)%N
| _ => N0
end.

Definition chk tm bsz use_acc T :=
  match RWL_steps tm bsz 3200 use_acc 2%N T with
  | inr x => inr x
  | inl (c1,c2,l,r) =>
    let '(l0,r0,_,_):=c2 in
    inl (get_len l0 + get_len r0)%N
  end.

Ltac test_bsz bsz use_acc T :=
  match goal with
  | |- halts_at_trans (?x) c0 _ =>
    pose (chk x bsz use_acc T) as v;
    time native_compute in v;
    match goal with
    | _ := ?x : _ |- _ => idtac x
    end;
    clear v
  end.

Ltac test_bszs use_acc T :=
  test_bsz 1%nat use_acc T;
  test_bsz 2 use_acc T;
  test_bsz 3 use_acc T;
  test_bsz 4 use_acc T;
  test_bsz 5 use_acc T;
  test_bsz 6 use_acc T;
  test_bsz 7 use_acc T;
  test_bsz 8 use_acc T.

Fixpoint sel_bsz_0 tm bsz n T cur_bsz cur_sz :=
  match (chk tm bsz true T) with
  | inl x =>
    let (nxt_bsz,nxt_sz) := (if cur_sz <? x then (bsz,x) else (cur_bsz,cur_sz))%N in
    match n with
    | S n0 => sel_bsz_0 tm (S bsz) n0 T nxt_bsz nxt_sz
    | O => cur_bsz
    end
  | inr x => bsz
  end.

Definition sel_bsz tm := sel_bsz_0 tm 1%nat 6 (10^4)%N 1 N0.

Ltac solve_halt :=
  match goal with
  | |- halts_at_trans (?tm) c0 _ =>
    solve_halt'' (sel_bsz tm) true
  end.



Lemma tm1: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_0RD0LC_0LB1RE_0RA---_1RA0RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB0RE_1RC0RA_1LD1RB_0RE0LD_0LC1RF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB1LE_0RC0RF_1LD0RA_1LE---_0LA0LB_1RC1RC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB1LE_0RC0RF_1LD0RA_1LE---_0LA0LB_1RC0RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB1LD_1RC0LE_0RD0RC_1LA0LA_---1LF_1LB0LD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB1RE_0LC1RA_---1LD_0LE0LA_0RA1LF_1LC0LA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB1RE_0LC1RA_---1LD_0LE0LA_0RA1LF_1LC1RC") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB1LA_0RC1LF_0RD0RE_1LB---_1LF1RE_1LD0LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB0RE_0RC1RA_1LC0LD_1RB1LD_1RF0RC_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1LD1RC_0LC0LA_1RF0RC_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1LD1RC_1LD0LA_1RF0RC_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB1LE_1LC0RA_1RD1LB_---0RE_0LF1RB_1RC1LE") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RF1RD_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1LD1RF_1LD0LA_1LD1RE_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB1LA_1RC0RD_0LD1RF_1LE1RD_0LD0LA_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_0RD1RF_0LE0LA_1LD1RE_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB1LA_1RC0RD_0LD1RF_1LE1RD_1LE0LA_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB1LA_1RC0RE_1LD1RF_0LE0LA_1LD1RE_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB1LC_1LC0RD_---0LD_1LE1RD_1LA0LF_0RE1LF") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE1RC_1RF0LD_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC0LF_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB1LC_1LA1RB_1LA0RD_1LE1RC_1LF0LB_---0LD") c0 (F,0).
Proof. solve_halt'' 4 true. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RF0RD_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB0RD_1RC1RF_0LD1LA_0RE1LD_---0LF_1RA1LE") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB0RD_1RC1RF_0LD1RB_0RE1LD_---0LF_1RA1LE") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB1LE_1RC0RA_1LD1RD_1RF1LE_0LA0LB_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RF1LD_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB1LF_1LC1RB_---1LD_1LE1RF_1LA1LD_0LC0RD") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB1LE_1LC1RB_1LA1LD_1LC1RE_0LF0RD_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB1RE_1LC1RD_1RD1LC_0RF0LE_1RA1LD_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB0LD_0LC1RA_1RB1LC_1RE1LA_1RF0RC_---1RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB0RC_0RC1RA_0LD1LC_1LE1LA_1RF1RC_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB0RD_1LC1RA_1RF1RD_0LE1LD_1LC1LA_---0RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB0RC_1LB1RA_0LD1LC_1LE1LA_1RF1RC_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB0RC_1LC1RA_0LD1LC_1LE1LA_1RF1RC_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LD1LE_0LF0LA_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD1RC_0LC1LE_0LF0LA_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB0RC_1LC1RA_0LD1LC_1LE1LA_1RF1LA_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB1RF_1RC0RD_1LD1LF_1RE1LD_---0RA_1RA0LC") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB0RB_1RC1RB_1LD1RA_---0LE_1LD0LF_1RA1LF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1RB0LF_1LC0RD_1LA1LC_---0RE_1LA1RE_1RF1LC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB0LC_1LC0RF_0RD1LC_0LA1LE_1LA1RE_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1RB0LB_1LC1LB_1RD1LA_---0RE_1RD0RF_1LA1RF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1RB1RD_1LC0LF_0LA1RC_1RE1LD_1LB0RC_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm45: halts_at_trans (TM_from_str "1RB1RD_1RC0LF_0LA1RC_1RE1LD_1LB0RC_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm46: halts_at_trans (TM_from_str "1RB1LC_1LA0RE_1LD0RD_1RB0LA_---0RF_1LD1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm47: halts_at_trans (TM_from_str "1RB0LE_1LB1RC_1RD1RC_1LA0RB_---0LF_1RD1LF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm48: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_1LD1LC_1RB0LA_---0RF_1LD1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm49: halts_at_trans (TM_from_str "1RB1LC_1LA0RE_1LD1LC_1RB0LA_---0RF_1LD1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm50: halts_at_trans (TM_from_str "1RB0LE_1LC1RB_0LA0LD_1RA1RE_1RF1LE_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm51: halts_at_trans (TM_from_str "1RB1LA_1LA0RC_0RF0RD_1LE1LD_0LA1RF_---1RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm52: halts_at_trans (TM_from_str "1RB0LE_1LC0RC_0LA0LD_1RA1RE_1RF1LE_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm53: halts_at_trans (TM_from_str "1RB0LA_1RC1RA_1RD0RC_1LE0RD_0RB0LF_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm54: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RC0RF_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm55: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA0RE_0LA0LB_0LA1RF_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm56: halts_at_trans (TM_from_str "1RB0LF_1LC1RA_0RB1LD_1RE1LC_---0RD_1LD1LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm57: halts_at_trans (TM_from_str "1RB1RC_1LC1RE_1LD0LB_1RE1LC_0RA0RF_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm58: halts_at_trans (TM_from_str "1RB1RC_1LC1RE_1LD0LB_1RE1LC_0RA1RF_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm59: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_0RD1LE_1LE1RC_1LA0LD_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm60: halts_at_trans (TM_from_str "1RB0RF_0RC1RD_1LD1RC_1LE0RB_1RA0LE_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm61: halts_at_trans (TM_from_str "1RB0RF_1LC1RE_1RE0LD_1LB1LD_---1RA_0LA1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm62: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RA0LD_1LB1LD_0LA1RE_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm63: halts_at_trans (TM_from_str "1RB1RF_1LC1LF_1RD0LB_---1RE_1LF1RD_1LB0RA") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm64: halts_at_trans (TM_from_str "1RB0LF_1LC1RA_1RF1LD_1RE1LC_---0RD_1LD1LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm65: halts_at_trans (TM_from_str "1RB0LF_1LC1RA_0LF1LD_1RE1LC_---0RD_1LD1LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm66: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm67: halts_at_trans (TM_from_str "1RB0LF_1RC1RA_1LD0RD_1RE1LD_---0RB_1RC1LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm68: halts_at_trans (TM_from_str "1RB1LE_0RC---_1LD0RF_1LA1LC_0LA1RC_1RC1LE") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm69: halts_at_trans (TM_from_str "1RB1LE_1RC1RA_1LD1RE_1RC1LD_0RF0LA_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm70: halts_at_trans (TM_from_str "1RB1LF_0LC1RA_---1RD_1RE1LD_1LC1RF_0RB0LA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm71: halts_at_trans (TM_from_str "1RB1LF_0LC1RA_---1RD_1RE1LD_1LD1RF_0RB0LA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm72: halts_at_trans (TM_from_str "1RB0RB_1LC1RB_1LF0LD_1RE1LD_0RA1LC_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm73: halts_at_trans (TM_from_str "1RB1LA_0RC1LE_1LB0RD_1LE1RD_1LF0LA_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm74: halts_at_trans (TM_from_str "1RB1LA_0RC1LE_0RD0RD_1LE1RD_1LF0LA_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm75: halts_at_trans (TM_from_str "1RB1LA_0RC1LE_0LD0RD_1LE1RD_1LF0LA_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm76: halts_at_trans (TM_from_str "1RB0RF_1RC0RA_0LD1RA_---0LE_1RA1LE_1LC1RF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm77: halts_at_trans (TM_from_str "1RB0RF_1RC0RC_0LD1RA_---0LE_1RA1LE_1LC1RF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm78: halts_at_trans (TM_from_str "1RB0RF_1RC0RD_0LD1RA_---0LE_1RA1LE_1LC1RF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm80: halts_at_trans (TM_from_str "1RB0RF_1RC---_0LD1RA_---0LE_1RA1LE_1LC1RF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm81: halts_at_trans (TM_from_str "1RB0LE_1LC1RB_0LA1RD_1RF0RB_1RD1LE_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm82: halts_at_trans (TM_from_str "1RB0LD_1RC---_0LA1RE_1RE1LD_1RB0RF_1LC1RF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm83: halts_at_trans (TM_from_str "1RB1LA_0RC1LE_0RD0LB_1LE1RD_1LF0LA_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm84: halts_at_trans (TM_from_str "1RB0RF_1RC1RD_0LD1RA_---0LE_1RA1LE_1LC1RF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm85: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_0RB0LF_---0RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm86: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LA0LB_0RB0RC_0RB0LF_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm87: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_1LA0LF_---0RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm88: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_1LA0LF_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm89: halts_at_trans (TM_from_str "1RB1LB_1LA1LC_---1RD_1LF1RE_0RD0RF_1LA0LD") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm90: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_1LA1LF_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm91: halts_at_trans (TM_from_str "1RB1RE_1LC1LE_1RF0LD_0RE1LD_1RA0LB_---0RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm92: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RD1LC_---0LA_1RA0LF_1LC1LE") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm93: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RD1LC_---1RA_1RA0LF_1LC1LE") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm94: halts_at_trans (TM_from_str "1RB1LD_1LC1RE_1LA1RA_1LF0LB_0RB0RC_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm95: halts_at_trans (TM_from_str "1RB1RE_1LC1LF_0RD1LC_---0LE_1RF1LD_1RA0RC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm96: halts_at_trans (TM_from_str "1RB1RE_1LC1RA_0RD1LC_---0LE_1RF1LD_1RA0RC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm97: halts_at_trans (TM_from_str "1RB1RD_1RC0LD_1RD1RB_1LE1LB_1RF0LA_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm98: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC0LF_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm99: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC1LF_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm100: halts_at_trans (TM_from_str "1RB1LD_1LC1RF_1LA1RD_0LE1LE_---0LB_0RB0RC") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm101: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LF1LF_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm102: halts_at_trans (TM_from_str "1RB1LF_1RC1RF_1LD1LE_---0LC_0RB1RE_1LA0LE") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm103: halts_at_trans (TM_from_str "1RB1RF_1LC1LF_1RE1LD_0LB1LD_---0RC_1RA0RD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm104: halts_at_trans (TM_from_str "1RB1RA_0LC0RD_---1LD_1LE1RB_1LF1LD_0RA1LB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm105: halts_at_trans (TM_from_str "1RB0RE_1LC0RB_0LD0LC_1LE1LB_1RF1RA_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm106: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_0LB0LD_1RA1LD_0RF0RB_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm107: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_1LC0LD_1RA1LD_0RF0RB_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm108: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_0LB0LD_1RA1LD_1RF0RB_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm109: halts_at_trans (TM_from_str "1RB1LA_1LC0RC_1LD1RC_0LF1LE_0RA0LA_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm110: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_1LC0LD_1RA1LD_1RF0RB_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm111: halts_at_trans (TM_from_str "1RB0LE_1LC0RC_1LD1RC_0LF1LA_1RB1LE_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm112: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1RE1LF_---1RC_0LE0LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm113: halts_at_trans (TM_from_str "1RB1LA_1LC0RC_1LD1RC_1LF1LE_0RA0LA_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm114: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1RC1LE_0LF0LA_---1RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm115: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1LE1LF_---1RC_0LE0LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm116: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LF1LE_0RA0LA_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm117: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LF1LE_0RA0LA_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm118: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LF1LE_1RB0LA_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm119: halts_at_trans (TM_from_str "1RB1LA_1LC0RC_1LD1RC_1LF1LE_1RB0LA_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm120: halts_at_trans (TM_from_str "1RB0LE_1LC0RC_1LD1RC_1LF1LA_1RB1LE_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm121: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1LC1LE_0LF0LA_---1RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm122: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LF1LE_1RB0LA_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm123: halts_at_trans (TM_from_str "1RB1LA_1LC0RC_1LD1RC_1LF1LE_0RA0LA_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm124: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1LC1LE_1LF0LA_---1LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm125: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LC1RD_1LE1RD_---1LF_1LE0LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm126: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LC1RD_1LE1RD_---1LF_0LD0LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm127: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1RC1LE_1LF0LA_---1LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm128: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1LE1LF_---1RC_1LD0LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm129: halts_at_trans (TM_from_str "1RB1LA_0RC0RC_1LD1RC_1LE1LF_---1RC_0LC0LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm130: halts_at_trans (TM_from_str "1RB1LF_0LC0RA_0LD1RD_1RE---_1LA1RB_0LA0LB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm131: halts_at_trans (TM_from_str "1RB0RC_1LC0LF_0LD0LB_1RE---_1RA1LF_1LE0RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm132: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC0LF_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm133: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB0RF_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm134: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm135: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC1LF_---0RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm136: halts_at_trans (TM_from_str "1RB1LE_1LC1RA_---1LD_0LE1LB_1LA0LF_0LA0RA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm137: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_1RD1LB_---1RE_0RA1RC_0RB0LB") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm138: halts_at_trans (TM_from_str "1RB1LA_1LC0RE_---0LD_1LE0LF_1RA1RE_1LA0LB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm139: halts_at_trans (TM_from_str "1RB1LA_1LC0RF_---0LD_1LE0LE_1LA0LB_1RA1RF") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm140: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_0LA1RE_1LC1LD_---1RB_0RD1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm141: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC1LF_---1LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm142: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RF1LD_---0RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm143: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RF0RD_---0RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm144: halts_at_trans (TM_from_str "1RB1LB_1LC1RD_---0LD_0RE0RF_1LF1RD_1LA0LE") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm145: halts_at_trans (TM_from_str "1RB1LE_1RC0RA_1LD1RD_1RF1LE_0LA0LB_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm146: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RF0RD_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm147: halts_at_trans (TM_from_str "1RB0LC_1LC0RE_1RD1LC_1LF0RB_1LE1LA_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm148: halts_at_trans (TM_from_str "1RB0RE_1RC1LB_1LD0RA_---0LC_1LE1LF_1RA0LB") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm149: halts_at_trans (TM_from_str "1RB0LF_1RC1RE_1RD---_1LE1LD_0RA0LD_1RF0RE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm150: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LF1RB_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm151: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_1LD0RE_0LE---_1LA0LB_1LD0RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm152: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1LD0RE_1LA0LC_0LB1LF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm153: halts_at_trans (TM_from_str "1RB0RC_1LC1RD_1RA0LD_0RE1RF_1LC0LE_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm154: halts_at_trans (TM_from_str "1RB0LB_0RC1LC_1LD0RE_1LE---_0LA0LF_0RD0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm155: halts_at_trans (TM_from_str "1RB0LA_1LC1RD_1RE1LA_0RA0RC_1RA0RF_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm156: halts_at_trans (TM_from_str "1RB1LC_1RC0RF_1RD0LC_1LA1RE_0RC0RA_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm157: halts_at_trans (TM_from_str "1RB0LA_1LC1RD_1RE1LA_0RA0RC_1RA1RF_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm158: halts_at_trans (TM_from_str "1RB1LC_1RC1RF_1RD0LC_1LA1RE_0RC0RA_---0LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm159: halts_at_trans (TM_from_str "1RB0LF_1RC0LD_1LD---_1LE1LD_0RA0LD_1RF0RE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm160: halts_at_trans (TM_from_str "1RB0LA_0RC1RC_1RD1LA_0LE0RF_1LC1LE_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm161: halts_at_trans (TM_from_str "1RB0LD_0RC1RA_0LD1RE_1LE1LA_0RF1LE_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm162: halts_at_trans (TM_from_str "1RB0RF_1LC0RD_0LC1LA_1RF1RE_1RD---_1RB0LB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm163: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0LD1LA_1LE---_0LF0LD_1LA0RD") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm164: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0LA0RB_0LF0LE_1LD---_1LA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm165: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_0RD0LC_0LB1RE_1RF---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm166: halts_at_trans (TM_from_str "1RB0LE_1LC0LD_0RD0LC_0LB1RE_1RF---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm167: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0LA0LF_1LF1LE_0LD---_0LA0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm168: halts_at_trans (TM_from_str "1RB1LA_0RC0RF_1RD1RC_1LE0LA_---0LF_1LD1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm169: halts_at_trans (TM_from_str "1RB1LD_1RC0RD_1LD1RF_1LE0RA_0LA1LC_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm170: halts_at_trans (TM_from_str "1RB1LE_1LC0RF_1RC0LD_0LC0RE_1RF---_0RA1RE") c0 (E,1).
Proof. solve_halt'' 8 true. Time Qed.

Lemma tm171: halts_at_trans (TM_from_str "1RB1LC_1LA0RD_1LA1LE_---1RE_1RF0LE_0RA1RF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm172: halts_at_trans (TM_from_str "1RB1LC_1LA0RD_1LA1LE_---1RE_1RF0LE_0RA0LD") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm173: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm174: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_1LF0RB_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm175: halts_at_trans (TM_from_str "1RB---_1LC0RB_0RD0LB_1LB1RE_1LE1LF_0LD1LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm176: halts_at_trans (TM_from_str "1RB---_0RC0RD_0RD0RA_1LE0RE_0LF0LE_1RA1LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm177: halts_at_trans (TM_from_str "1RB0LB_0RC0RB_1LD1RB_1LE---_0LF0LA_0LA0LD") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm178: halts_at_trans (TM_from_str "1RB1LF_1RC---_0RD0RE_0RE0RB_1LF0RF_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm179: halts_at_trans (TM_from_str "1RB0LE_1RC---_1RD1RF_1LA1LE_1LC0LA_0RA1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm180: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF0RC_---0RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm181: halts_at_trans (TM_from_str "1RB0RD_1RC0RF_0LD0RB_0LF0RE_1LC---_1RA1RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm182: halts_at_trans (TM_from_str "1RB0RD_0LC1LB_1RF1LD_0RE0RB_1LF1RA_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm183: halts_at_trans (TM_from_str "1RB1RF_1LC1LF_1RD1LC_---0RE_1RD1LA_1RA0LB") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm184: halts_at_trans (TM_from_str "1RB1RF_1LC1LF_1RD1LC_---0RE_0RC1LA_1RA0LB") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm185: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_0LE1LD_1LC0LB_1LF0LC_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm186: halts_at_trans (TM_from_str "1RB0LE_1LC1RB_---1LD_1RE0LF_0RD1LB_0LD1LA") c0 (C,0).
Proof. solve_halt'' 8 false. Time Qed.

Lemma tm187: halts_at_trans (TM_from_str "1RB1LD_1LC0RE_---0LD_1LA0LE_0RF1RE_1LB1RF") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm188: halts_at_trans (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0LA_1RC1LF_0LC0LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm189: halts_at_trans (TM_from_str "1RB0LD_1RC0RE_1LA1RF_0LA0RE_1LD---_0RA0RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm190: halts_at_trans (TM_from_str "1RB0RD_1LC1LF_1RD1RA_1LE0RA_1LB---_0LD1LD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm191: halts_at_trans (TM_from_str "1RB1RF_0LC0RA_1LD1LB_1LE1LB_1RA---_0RB1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm192: halts_at_trans (TM_from_str "1RB---_1RC1RB_1RD0RA_1LE0RC_1RF0LD_1RB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm193: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA0RE_0LF1LE_0LA1RB_---1LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm194: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_1LD0RB_1RE0LC_1RA0LE_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm195: halts_at_trans (TM_from_str "1RB---_1RC0RE_1LD0RB_1LB0LC_1RF0LD_1LE1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm196: halts_at_trans (TM_from_str "1RB1RD_1LC0RA_1RD0LB_1RE0LD_1RA0RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm197: halts_at_trans (TM_from_str "1RB0LD_1RC1RD_1LA1RF_1RA0LE_0RC1LA_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm198: halts_at_trans (TM_from_str "1RB0RA_1LC0LF_1RD0LB_---1RE_1RA0RB_0RC1LB") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm199: halts_at_trans (TM_from_str "1RB---_1RC0LF_0RD0RB_0RE0RF_1LF0RA_1LB0LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm200: halts_at_trans (TM_from_str "1RB0LE_1RC0LB_1RD1RC_1RE0RF_1LA0RD_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm201: halts_at_trans (TM_from_str "1RB0RF_1RC0RB_1LD0RA_0LE0LC_1LB0RC_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm202: halts_at_trans (TM_from_str "1RB0LA_1RC0RF_1RD1RA_1LE0RC_1RA0LD_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm203: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE0LA_1RA0LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm204: halts_at_trans (TM_from_str "1RB0LA_1RC0RF_1RD1RA_1LE0RC_1LC0LD_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm205: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1LD0RC_1LE0LF_1LA0LC_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm206: halts_at_trans (TM_from_str "1RB0LA_1RC1RF_1RD0RA_1LE0RC_1RA0LD_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm207: halts_at_trans (TM_from_str "1RB0LF_1LC0RA_1LD0RC_0RD1LE_1LF---_1LA0LC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm208: halts_at_trans (TM_from_str "1RB0LA_1RC1RF_1RD0RA_1LE0RC_1RA0LD_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm209: halts_at_trans (TM_from_str "1RB0RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm210: halts_at_trans (TM_from_str "1RB---_1LC0LE_1RD0LB_1LE0RC_1LF0RE_1LB1LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm211: halts_at_trans (TM_from_str "1RB---_1RC0RE_1LD0RB_1RE0LC_1RF0LE_0LF1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm212: halts_at_trans (TM_from_str "1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm213: halts_at_trans (TM_from_str "1RB0LE_1RC0LB_1RD0RF_1RE0RB_1LA0RD_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm214: halts_at_trans (TM_from_str "1RB0LF_1RC0LB_0LC1RD_1RE---_1RF0RB_1LA0RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm215: halts_at_trans (TM_from_str "1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm216: halts_at_trans (TM_from_str "1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm217: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_0LD0LB_1LA0RB_1RA0RF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm218: halts_at_trans (TM_from_str "1RB0LE_1RC0LA_1RD1RA_1LB1RF_0RD1LB_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm219: halts_at_trans (TM_from_str "1RB0LF_0RC0RA_1LD0RC_1LE---_1LA0LD_1LA0LB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm220: halts_at_trans (TM_from_str "1RB0LF_0RC0RA_1LD0RC_1LE---_1LA0LD_1LA1LD") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm221: halts_at_trans (TM_from_str "1RB0RE_1LC0RF_0LD0LB_1RE0LD_1RA---_1RB0RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm222: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_0LD0LB_1RE0LD_1RF---_1RB0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm223: halts_at_trans (TM_from_str "1RB---_1RC0RA_1LD0RB_1LE0LC_0RE1RF_1RA0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm224: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_1RD0LA_1LA0LD_1LD0LF_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm225: halts_at_trans (TM_from_str "1RB1RF_1RC0LD_1LB0RE_1LB0LC_1RF---_0RA1RE") c0 (E,1).
Proof. solve_halt'' 2 true. Time Qed.

