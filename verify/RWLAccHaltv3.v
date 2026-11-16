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
  | inr Unknown =>
    match n with
    | S n0 => sel_bsz_0 tm (S bsz) n0 T cur_bsz cur_sz
    | O => cur_bsz
    end
  | inr _ => bsz
  end.

Definition sel_bsz tm := sel_bsz_0 tm 1%nat 12 (10^4)%N 1 N0.

Ltac solve_halt :=
  match goal with
  | |- halts_at_trans (?tm) c0 _ =>
    solve_halt'' (sel_bsz tm) true
  end.


Lemma tm1: halts_at_trans (TM_from_str "1RB1RC_0LC---_1LF1RD_0RE0RA_1RC0LA_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB0RB_0LC1RA_1LA1RD_1LE0LC_0LF0LD_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB---_0RC1RF_1LD0LB_0LE1LE_1RF0LD_0RB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LE0LD_0LE---_1LF1RE_1RB0LB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0LD1LA_1RE0RF_1LD0LC_---1LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_0RF0LD_0RE1LE_1LA0LC_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB1RA_1LC0RE_1LF1LD_1LA0LC_1LC1RE_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LD0LC_0RA0RE_1RF0LA_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1LD0LB_1RA0LA_0LF0RA_---0LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB1RD_1RC0RF_0RD0LC_1LE1RB_1LC---_0RA1RF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB0RC_1RC0RF_0LD0RE_1LB1LD_0LA1RA_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA1LD_1LD1LF_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB0LF_1RC0RB_1LD0RB_1LE0LD_0LA0LB_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB0LF_0RC0LD_1LA1RA_1RA1LE_0LA1LD_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB1LB_0LC0RE_1RA1LD_1LA0LA_0RF1RC_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA1LD_1LD1LF_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB0LF_1RC---_1LD0RC_1LE1LC_0LA1LF_0RB1LC") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB---_1LC0LE_1RB0RD_1RA1RE_1LF1RC_0LD0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB0LC_1RC1RF_1RD0RA_0LE---_1LF0LF_1RA1LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1LD0LD_0LA0RA_1LD1LF_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE1LF_0LA1LE_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB0RF_1RC1LF_0RD0LC_1LE1RD_1LC0RF_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_0RF0LE_0LD0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB0LE_0RC---_1LD1RA_1RE0RE_0LA1RF_1LA0RD") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB0LC_1RC1RE_1LD1LF_1LA1LD_0RA1RA_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB0RE_0RC0LC_1RD0RF_0LA0LF_1LF---_0LD0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD1RF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB0RF_0LC---_0RE1LD_1LC0LC_1RD1LF_1RA0RE") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB1RC_0RC0LB_1LD0RA_0LE0RB_1RB1LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB1LE_1LC0RC_1RD1LA_1RB0RF_1LA0LE_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB---_1LC0LD_1RB1LC_0LA1LE_1RF1LB_0RD0RF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB1LD_0LC0RB_0RA1RD_0LE0LF_1LA0RF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LE0LD_0LE---_1LF1RE_1RA0LB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB1RD_1LC0LB_0RA0LB_1RE0RF_0LD1RC_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB0LA_0RC---_1RD1RC_0RE1LF_1RF1RC_1LD1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RB0LE_1RA1LD_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1RB1RE_1RC---_1LD0LE_1RC0RA_1LF1RD_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB1RA_0LC0RC_1LD1RC_1LF1LE_1LA0LD_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB0RF_1RC1LB_1LD0RD_1RA0LE_1LD0LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RE0RA_1RA0RC_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1RB1LC_0RC0RE_0LD0LF_1LA0RF_1RB0RE_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB1RF_0LC0RF_1LE1LD_1LB---_1RA0LF_1LE0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0RD1RB_0LE---_1LF1LD_0LA0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0RD0LC_0LB1RE_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm45: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_0LD1RB_1LE---_0LA1LE_1RE1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm46: halts_at_trans (TM_from_str "1RB1LE_0LC0RB_0RA0RD_1LC---_0LF0LD_1LA0RD") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm47: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0LE0LD_1LC0LD_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm48: halts_at_trans (TM_from_str "1RB1RF_0LC0RE_1LD1LC_1LE0LC_0RA1RE_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm49: halts_at_trans (TM_from_str "1RB0LB_1RC0RE_1RD0RC_0RE0RF_1LF0LF_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm50: halts_at_trans (TM_from_str "1RB0RC_1LA0LD_1RE1LB_1LF1LC_0RD0RE_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm51: halts_at_trans (TM_from_str "1RB0RD_1RC0RF_1LD---_1LE1RD_0RA0LF_1LA0LE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm52: halts_at_trans (TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0RF_1RC0RC_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm53: halts_at_trans (TM_from_str "1RB0RF_1RC1LB_1LB1RD_1LE0RC_1RF0LE_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm54: halts_at_trans (TM_from_str "1RB1LE_1LC1RD_1LA0RB_1RC0RB_1LF0LC_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm55: halts_at_trans (TM_from_str "1RB0RE_1RC1LA_1RD0RC_1LE1RF_1LB0LE_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm56: halts_at_trans (TM_from_str "1RB1RD_0RC---_1RD0LA_1LE1RF_0LA0LE_0RC0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm57: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0LD1LA_1RE---_1LF0LC_1RE0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm58: halts_at_trans (TM_from_str "1RB1LC_1LC1RF_0RD0LC_0LB0LE_1RD---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm59: halts_at_trans (TM_from_str "1RB1RD_1LC1RE_1LD0LB_1RA1RA_0LF0RA_---0LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm60: halts_at_trans (TM_from_str "1RB1RD_1LC1RF_1RA0LD_1RE0LB_0RC---_1RB0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm61: halts_at_trans (TM_from_str "1RB---_1LC1RE_1RD0RD_0LB1RC_1LF0LB_0LA0LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm62: halts_at_trans (TM_from_str "1RB1LE_0LC0RF_1LA0RD_1LE---_0LC0LD_1RB0RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm63: halts_at_trans (TM_from_str "1RB0RD_0RC0RA_1LD---_1RE1LA_1LF0LF_0RD1LE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm64: halts_at_trans (TM_from_str "1RB0LF_0LC1RE_1LD1RC_0RB0LD_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm65: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_0RD0RF_1LE0RB_0LE1LA_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm66: halts_at_trans (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1LA1LA_1RA0RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm67: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD1RF_1LE0LE_0RF0LD_1RB1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm68: halts_at_trans (TM_from_str "1RB0RA_1RC1RA_1LD0RF_1RA0LE_1LD0LC_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm69: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LF1LD_0RE---_1LA1LC_0LE0RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm70: halts_at_trans (TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LF_1LB1LE_1RE1RB") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm71: halts_at_trans (TM_from_str "1RB0RA_1LC1RE_1RA0LD_1LC0LD_0RB0RF_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm72: halts_at_trans (TM_from_str "1RB1LD_1RC0RE_1RD---_1LE0RF_0LB0RA_1LA0LF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm73: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_0LD1LC_1RA1LB_1LF0RD_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm74: halts_at_trans (TM_from_str "1RB0RE_1RC1RF_1LD0RD_0RB1LE_1RD0LE_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm75: halts_at_trans (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0LF1LA_1RA0RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm76: halts_at_trans (TM_from_str "1RB1LA_1RC0LC_0LA1RD_0RE---_1RB1RF_1LB1RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm77: halts_at_trans (TM_from_str "1RB0RF_1RC0RA_0LD---_1LE0LE_0RF1LD_1RD1LA") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm78: halts_at_trans (TM_from_str "1RB0LE_0LC---_1LF1RD_0RE0RA_1RC0LA_1LD0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm79: halts_at_trans (TM_from_str "1RB1RC_0RC0LB_1LD0RA_0LE0LE_1RB1LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm80: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_0LF0LD_1LE---_0LB0LE_1LA0RD") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm81: halts_at_trans (TM_from_str "1RB---_0LC0LA_1LF1RD_0RE0RA_1RC0LA_0RB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm82: halts_at_trans (TM_from_str "1RB1LA_1RC0LD_0LA1RE_---1LE_0RF0LB_0LA0RC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm83: halts_at_trans (TM_from_str "1RB0RB_1LC1RB_0LF1LD_1LE0LC_1RA1RE_---0RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm84: halts_at_trans (TM_from_str "1RB1RE_1LC---_1LD1RC_1RC0RA_1LF1RD_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm85: halts_at_trans (TM_from_str "1RB0LF_1RC---_1LD0RC_1LE1RE_0LA1LF_0RB1LC") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm86: halts_at_trans (TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RE0RB_1RA0RC_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm87: halts_at_trans (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_0RF1RC_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm88: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1LA_0RA---_0LF0LC_1LA0RC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm89: halts_at_trans (TM_from_str "1RB1LE_0RC0LB_1LD0RF_0LA0RB_1LA---_1RB1RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm90: halts_at_trans (TM_from_str "1RB---_0RC1RB_1RD1RF_1LE0LE_0RF0LD_1RB1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm91: halts_at_trans (TM_from_str "1RB0RE_0RC0LB_1LD1RA_1LB---_0RF1RE_1LB1RC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm92: halts_at_trans (TM_from_str "1RB---_0RC0RD_1LB1LD_0LE1LE_1RF0LD_0RB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm93: halts_at_trans (TM_from_str "1RB1RA_1RC0LE_1LD1RF_1LA0LB_0LD1LB_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm94: halts_at_trans (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA0LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm95: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_0RD0RF_1LE0RB_0LE1LA_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm96: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_---1LA_1RA1LE_1RF0LF_1RE1LB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm97: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_0RD0LC_0LB0LE_1RF---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm98: halts_at_trans (TM_from_str "1RB0RA_0RC0LD_1LA1RE_0LA1LD_1RB1RF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm99: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm100: halts_at_trans (TM_from_str "1RB1RF_1LC1RA_0LD0LC_1RE0RB_1LB---_0RD0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm101: halts_at_trans (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0LD_1RB1RF_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm102: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_0RC0LF_1LE0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm103: halts_at_trans (TM_from_str "1RB1RF_0LC0RE_1LD1LC_1LE0LF_0RA1RE_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm104: halts_at_trans (TM_from_str "1RB---_0RC1RF_1LD0RB_1RE0LD_1RB1LE_1RA1RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm105: halts_at_trans (TM_from_str "1RB---_1LC0LA_0LD1LC_1LE1LB_1RF0RF_0LB0RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm106: halts_at_trans (TM_from_str "1RB1LF_1RC1RB_1LD0LE_---1LE_0LA0RA_1LE0LC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm107: halts_at_trans (TM_from_str "1RB0RB_1LC0LE_0RD0LB_0RA1RD_0LF0LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm108: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1LA_0RA---_1LF0LC_1RE0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm109: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0RD0LC_0LB1LE_0RA0RF_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm110: halts_at_trans (TM_from_str "1RB1LA_1RC1LF_1LD0RC_0LE1LE_1LB0LA_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm111: halts_at_trans (TM_from_str "1RB1RE_1LC0RF_1LD0LC_1RE0RB_1RA0RC_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm112: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LA1LD_1LE0LF_0RD1LB_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm113: halts_at_trans (TM_from_str "1RB1RF_0RC0LD_1LA1RA_0LE1LD_1RB0RA_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm114: halts_at_trans (TM_from_str "1RB1LE_1RC1RB_1LD0LF_---0RA_1LF0LC_0LA0RA") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm115: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LE0LD_1RC---_0LF0RF_1LA1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm116: halts_at_trans (TM_from_str "1RB0RF_0LC0RE_0LD1LC_1LA0LE_1RB1RD_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm117: halts_at_trans (TM_from_str "1RB0LA_1RC1RA_0RD1RF_1LE0RF_1LA---_0LE1RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm118: halts_at_trans (TM_from_str "1RB0RB_0RC0LA_1LD1LF_1LE0LB_0LA0LC_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm119: halts_at_trans (TM_from_str "1RB0RE_0LC0RA_0LD1LC_1LA0LA_0RF0RF_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm120: halts_at_trans (TM_from_str "1RB---_0RC0RB_1RD0LF_0RE0RA_1RF1RA_1LC0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm121: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RE1LD_1RC0LD_0LB1RF_---1RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm122: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LE1LD_1LE---_0LF1LE_1LA1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm123: halts_at_trans (TM_from_str "1RB---_0LC0LA_1LF1RD_0RE0RA_1RC1LF_0RB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm124: halts_at_trans (TM_from_str "1RB1LF_1LC0RD_1LA1LD_1LE0RA_0LB---_1LA0LC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm125: halts_at_trans (TM_from_str "1RB0RB_1LC0RE_0LA0LD_1LA0LE_0RB1LF_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm126: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LF0RD_1LE---_0LC0LD_1RB1LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm127: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_---1LA_1RA1LE_0RA0LF_1RF1LB") c0 (C,0).
Proof. solve_halt'' 14 false. Time Qed.

Lemma tm128: halts_at_trans (TM_from_str "1RB1RF_0RC1RB_1LD1RA_0LE0LD_0LF1LD_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm129: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_1LD0LD_1RC1LE_0LF0LC_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm130: halts_at_trans (TM_from_str "1RB1LA_0RC0RE_1LD0RA_0LE1LD_1LF0LC_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm131: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm132: halts_at_trans (TM_from_str "1RB1RF_0RC1RB_1LD1RA_0LE0LD_1RB1LD_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm133: halts_at_trans (TM_from_str "1RB0RF_0RC0LC_1RD1RA_1LE0LE_0RA0LD_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm134: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1LA_1LE---_1RF1LE_1LE0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm135: halts_at_trans (TM_from_str "1RB1RE_1RC0RF_0LD---_1LE0LE_1RF1LD_1RA0LB") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm136: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_0LD1LB_1RA0LE_1LC0LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm137: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD1RE_0LA0LD_1RB1RF_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm138: halts_at_trans (TM_from_str "1RB0RC_1LB1RA_1LD1LE_0LE0LF_0RA0LC_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm139: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1LA_1RE---_1RF1LE_1LE0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm140: halts_at_trans (TM_from_str "1RB0LE_1RC0RF_1RD1LC_1LA0RA_1LA0LE_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm141: halts_at_trans (TM_from_str "1RB---_1LC0RE_0LD0RD_1RE0LB_1RF1RA_0RB1RD") c0 (A,1).
Proof. solve_halt'' 20 false. Time Qed.

Lemma tm142: halts_at_trans (TM_from_str "1RB0RC_1LA0LD_1RF1RD_1LE1RA_0LC0LE_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm143: halts_at_trans (TM_from_str "1RB0LC_0LC1RD_1RA1LA_1RE---_1LF0RA_1RC0LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm144: halts_at_trans (TM_from_str "1RB0LD_1RC1RD_1LA1RF_1RE0LC_0RA---_1RC0RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm145: halts_at_trans (TM_from_str "1RB---_1LC1RE_1LD0LB_1LA1LB_1LE0RF_0RD1RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm146: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LF_1LE1RB_0LF0LE_1RB1RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm147: halts_at_trans (TM_from_str "1RB0RC_0LA1RF_0RD---_1RE1RA_1LF0LE_0RD0LE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm148: halts_at_trans (TM_from_str "1RB---_0RC0RB_1RD0LF_0RE0RA_1RF1LE_1LC1LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm149: halts_at_trans (TM_from_str "1RB1LD_1LC0RB_0RE0RA_0LE0LF_1LA1RB_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm150: halts_at_trans (TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RE0RA_0LB0RC_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm151: halts_at_trans (TM_from_str "1RB0LA_0RC0RE_0RD1LD_0LD1LA_1RF---_1RC1RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm152: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RE1LD_1RC0LD_0LA1RF_---1RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm153: halts_at_trans (TM_from_str "1RB---_1LC1RD_0LB0LD_0LE1RE_0RF0LF_1RA0RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm154: halts_at_trans (TM_from_str "1RB---_1RC1RB_1LD0RB_1LE0LE_1RD1LF_0LA0LD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm155: halts_at_trans (TM_from_str "1RB0RF_1RC1LB_1LD0RE_1LE0LD_1RA0LD_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm156: halts_at_trans (TM_from_str "1RB0RE_0RC0LC_1LD1RA_1LE1LD_1RF0RB_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm157: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1LD1RA_0LE0LD_0LF1LD_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm158: halts_at_trans (TM_from_str "1RB---_1RC0LE_1RD0RB_1LE0RC_0LF0LD_1LB1LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm159: halts_at_trans (TM_from_str "1RB---_1LC0LE_1RB0RD_1RF1LB_0LA1LD_0RE0RF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm160: halts_at_trans (TM_from_str "1RB1LE_0LC0RD_1LA1LC_1RA1LA_---0LF_1RF0LC") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm161: halts_at_trans (TM_from_str "1RB0RD_1LC0LA_1RD1LB_0LF0RE_0LA1RA_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm162: halts_at_trans (TM_from_str "1RB1RC_0RC0LB_1LD0RA_0LE0LA_1RB1LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm163: halts_at_trans (TM_from_str "1RB0RF_1RC1LC_1LD0RC_1RF1LE_1RA0LE_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm164: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD1LE_1LE1RB_0RF0LE_0LD0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm165: halts_at_trans (TM_from_str "1RB0RB_1LC0RD_1RE0LD_0RE1RF_0LB0RA_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm166: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_0LD0LE_1LA0RE_1LF0RD_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm167: halts_at_trans (TM_from_str "1RB1LE_0LC0RB_0RA1LD_0LE---_1LA0LF_1LE1LB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm168: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RE_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm169: halts_at_trans (TM_from_str "1RB---_1RC0LD_0RD0RF_1LE1LB_0LB0LE_1RC0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm170: halts_at_trans (TM_from_str "1RB1RF_0RC1RB_1RD1RA_1LE0LE_0RA0LD_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm171: halts_at_trans (TM_from_str "1RB1LF_1LC0RE_0LC1LD_1LA0RB_0RB0RD_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm172: halts_at_trans (TM_from_str "1RB0LD_1LC1RD_1LA0LC_1RE1LA_1RB0RF_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm173: halts_at_trans (TM_from_str "1RB0RE_1RC0RA_1RD0LF_1RE---_1LF1RB_0LC1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm174: halts_at_trans (TM_from_str "1RB0RC_1LA0LF_0RB1RD_1LE1RA_0LC0LE_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm175: halts_at_trans (TM_from_str "1RB0RE_0LC0RA_0LD1LC_1LA0LA_1RF1RF_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm176: halts_at_trans (TM_from_str "1RB0LA_0LC0LD_1RD1LA_1LA1RE_0RC0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm177: halts_at_trans (TM_from_str "1RB1LD_1LC0LC_0RA1LB_1RE0RA_0RF0RD_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm178: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LD1LC_0LE1LF_1RE0LB_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm179: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1LA1LC_1RA1RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm180: halts_at_trans (TM_from_str "1RB---_0LC0RB_1RA1LD_1LB0LE_0LF1LE_1RB1LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm181: halts_at_trans (TM_from_str "1RB0LE_1RC0RE_0RD0RA_1LE1RE_0LA0RF_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm182: halts_at_trans (TM_from_str "1RB1RF_0RC0LE_1LD1RA_1RB0RA_0LD1LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm183: halts_at_trans (TM_from_str "1RB0LD_0RC1RE_1LC0LD_1RA0LA_1RF0RB_0RA---") c0 (F,1).
Proof. solve_halt'' 32 true. Time Qed.

Lemma tm184: halts_at_trans (TM_from_str "1RB0LD_0RC0RE_1RD1RE_1LA0LD_1RF---_0RA0RF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm185: halts_at_trans (TM_from_str "1RB1RF_1LC1RE_0RE0LD_0LC0LB_0RA1RE_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm186: halts_at_trans (TM_from_str "1RB0RC_1LA0LD_0RF1RD_1LE1RA_0LC0LE_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm187: halts_at_trans (TM_from_str "1RB1LA_1LA0LC_0LF1LD_1RE1LB_0RC0RE_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm188: halts_at_trans (TM_from_str "1RB1RA_1LC0LF_---0RD_1RA1LE_1LF0LB_0LD0RD") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm189: halts_at_trans (TM_from_str "1RB1RE_1RC---_0RD0RB_1RE0LB_1LF1RC_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm190: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_0RE1LD_0RE---_1LA1RE_1LE0LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm191: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_1LD0LC_0RA0RE_1RF0LA_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm192: halts_at_trans (TM_from_str "1RB0RE_0RC0LD_1LA1RE_0LA1LD_1RB1RF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm193: halts_at_trans (TM_from_str "1RB1LA_1LC1RF_1RD0LC_0LD1RE_0LA---_1RA0RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm194: halts_at_trans (TM_from_str "1RB0RA_0RC0LE_0LD---_1LE1LC_0LF0RF_1RA1LD") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm195: halts_at_trans (TM_from_str "1RB1RF_1LB1RC_1LD0RB_1RE0LC_---0RF_1RA1RD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm196: halts_at_trans (TM_from_str "1RB1LE_1LC0RB_0RD0LD_1LA1RB_0LD0LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm197: halts_at_trans (TM_from_str "1RB0RF_1RC0RA_0LD---_0RF1LE_1LD0LD_1RE1LA") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm198: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1LA_1LE---_1RF0RA_1LE0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm199: halts_at_trans (TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0LA_0LC0LF_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm200: halts_at_trans (TM_from_str "1RB---_1LC1RE_0RE0LD_0LC0LB_0RF1RE_1RB1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm201: halts_at_trans (TM_from_str "1RB0RC_1LA1RB_1RF1RD_1LE1RA_0LC0LE_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm202: halts_at_trans (TM_from_str "1RB1LF_0LC0RB_1RA1LD_1LB0LE_0LA1LE_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm203: halts_at_trans (TM_from_str "1RB---_0LC0RE_0LD1LC_1LE0LE_1RB0RF_0RE0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm204: halts_at_trans (TM_from_str "1RB0LD_1LC1RF_0LD0LC_1RE1RB_0RA---_0RA0RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm205: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_0RA1LD_1RC0LD_---1RF_1RA0RD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm206: halts_at_trans (TM_from_str "1RB0RB_1LA1RC_0RD0RA_1LE---_1LF1LE_1RA0LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm207: halts_at_trans (TM_from_str "1RB0LA_1RC1LA_0LD1RF_1LB0RE_1RD0RE_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm208: halts_at_trans (TM_from_str "1RB---_1LC1RB_1RB0RD_1RA1RE_1LF1RC_0LD0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm209: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0LD0LC_1RE1RB_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm210: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LF1LD_0RE---_1LA1LC_0LE0RC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm211: halts_at_trans (TM_from_str "1RB1RC_0LC---_1LF1RD_1RE0RA_1LD0LC_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm212: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_1LD0LE_0LA1LD_1LF0RA_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm213: halts_at_trans (TM_from_str "1RB1LA_1LA0LC_1LF1LD_1RE1LB_0RC0RE_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm214: halts_at_trans (TM_from_str "1RB1LE_1RC1RB_1RD0RB_0LA1LD_---1LF_0RB0LD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm215: halts_at_trans (TM_from_str "1RB---_1LC0RE_0LD1LC_1LA0LB_1RF1LE_0RB0RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm216: halts_at_trans (TM_from_str "1RB0RC_1LA0LD_0RB1RD_1LE1RA_---0LF_0LC0LF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm217: halts_at_trans (TM_from_str "1RB1LF_1RC0RD_1LD1LC_1LA0RE_0RB1RD_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm218: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RA1LD_0LE0LF_1LC0RF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm219: halts_at_trans (TM_from_str "1RB1RA_1LC0LD_---1LD_0LE0RE_1RA1LF_1LD0LB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm220: halts_at_trans (TM_from_str "1RB1RE_1RC---_1LD1RC_1RC0RA_1LF1RD_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm221: halts_at_trans (TM_from_str "1RB1RB_0LC---_0LE0RD_1RC0RA_0LF1LE_1LD0LD") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm222: halts_at_trans (TM_from_str "1RB0RE_0RC0RD_1RD0LD_1LC0LE_1LB1RF_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm223: halts_at_trans (TM_from_str "1RB0RB_0LC1RA_1LA1RD_1LE0LC_1LF0LD_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm224: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_1LD0LC_0RA0LC_1RF---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm225: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_0RE0LD_0RB---_1LA1RE_1LE0LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm226: halts_at_trans (TM_from_str "1RB0LC_1LC1RD_1LA0LC_0RE0RF_1RB0LF_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm227: halts_at_trans (TM_from_str "1RB1LE_0RC0LB_1LD0RF_0LA0LF_1LA---_1RB1RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm228: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_0RD1RC_1LE1RB_0LA0LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm229: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE0LF_1LC0RF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm230: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LE1LD_1RE---_0LF1LE_1LA1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm231: halts_at_trans (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RA0RE_0RF1RD_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm232: halts_at_trans (TM_from_str "1RB0RD_0RC0LE_1LD1RD_1RB1RF_0LA1LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm233: halts_at_trans (TM_from_str "1RB1LA_1LC0RD_1LD0LC_1RE0LC_1RA0RF_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm234: halts_at_trans (TM_from_str "1RB---_1LC1RD_0LD0RB_1RE0LC_1RF0RA_0RB1RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm235: halts_at_trans (TM_from_str "1RB0RC_1LA1RB_0RF1RD_1LE1RA_0LC0LE_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm236: halts_at_trans (TM_from_str "1RB0LA_1RC1RA_0LD---_1RE1LD_1LA1RF_1RD0RE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm237: halts_at_trans (TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB1RF_1RC0RC_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm238: halts_at_trans (TM_from_str "1RB1RE_1LC0LB_1RA0LD_1RE1LF_0RC---_0LD0LB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm239: halts_at_trans (TM_from_str "1RB0LF_1LC0RC_1RD1LC_---1RE_0RA1RA_0RE1LF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm240: halts_at_trans (TM_from_str "1RB0RB_1LC1RA_1LE0RD_1LF0LC_1LD1LB_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm241: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_0RD0LC_0LB0LE_1RD---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm242: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0RD0LC_0LB1LA_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm243: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_0RF0LE_0LD1LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm244: halts_at_trans (TM_from_str "1RB1LB_1LC0RB_1RF1LD_1RE0LD_1RA0RF_---1RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm245: halts_at_trans (TM_from_str "1RB0LB_1LC0RF_0LC0LD_0LE1LC_1RF---_1RA1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm246: halts_at_trans (TM_from_str "1RB0LD_1LC1RD_1LA0LC_1RE0RF_1RB0RA_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm247: halts_at_trans (TM_from_str "1RB---_0RC1RF_1LD1LD_0LE1LE_1RF0LD_0RB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm248: halts_at_trans (TM_from_str "1RB0LA_1RC1LC_0RD1RF_1LE0RF_1LA---_0LE1RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm249: halts_at_trans (TM_from_str "1RB0RC_1LA0LD_1RE1LB_1LF1LC_0RD0RE_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm250: halts_at_trans (TM_from_str "1RB1LC_0LC0RB_1RE1LD_1LB0LF_1RB---_0LA1LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm251: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0RA_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm252: halts_at_trans (TM_from_str "1RB0RB_0LC1RF_1RD0LB_0RE---_1LA1RC_1LC0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm253: halts_at_trans (TM_from_str "1RB0LA_0RC1RC_1RD0RE_1LA1RF_1LD1RE_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm254: halts_at_trans (TM_from_str "1RB1RF_0RC1RB_1RD1RA_1LE0LE_0RA0LD_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm255: halts_at_trans (TM_from_str "1RB---_1RC0LF_1RD0RB_0RE0LE_1RF0RA_1LB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm256: halts_at_trans (TM_from_str "1RB1LE_0LC1RF_1LA0RD_1RC0RD_1RA0LE_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm257: halts_at_trans (TM_from_str "1RB0RA_1LC0LE_1RA1LD_1LE1LF_0LC0RC_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm258: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_0RD0LC_0LB1RE_0RA---_1RA1RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm259: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_---1LA_1RA1LE_1RF0LF_1RF1LB") c0 (C,0).
Proof. solve_halt'' 14 false. Time Qed.

Lemma tm260: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1RD0LC_0LA1RF_1RA0RB_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm261: halts_at_trans (TM_from_str "1RB0LF_1RC0RC_1LB1RD_0RE0RB_1LF---_1LA1LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm262: halts_at_trans (TM_from_str "1RB0RB_1LC0LE_0RD0LB_0RA1RD_0LB0LF_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm263: halts_at_trans (TM_from_str "1RB0RE_0LC0RA_0LD1LC_1LA0LA_0RA0RF_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm264: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LE1LD_1LE---_0LF0RF_1LA1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm265: halts_at_trans (TM_from_str "1RB1LD_0LC0RB_0RA1RD_0LE0LF_1LA0RF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm266: halts_at_trans (TM_from_str "1RB0RC_1LA1RB_1RF1RD_1LE1RA_0LC0LE_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm267: halts_at_trans (TM_from_str "1RB1LE_1RC1RB_0LD0LF_---1RE_1LF0LC_0LA0RA") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm268: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_1LF0LE_0RC0LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm269: halts_at_trans (TM_from_str "1RB1LA_1LA0LC_1LF1LD_1RE1LB_0RC0RE_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm270: halts_at_trans (TM_from_str "1RB1RA_0LC0LE_---1RD_1LE0LB_0LF0RF_1RA1LD") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm271: halts_at_trans (TM_from_str "1RB0LC_0RC1RA_1LD0RA_0LE0RB_---1LF_0LA1LF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm272: halts_at_trans (TM_from_str "1RB---_1LC0RF_0LC1LD_1LE0RB_1RB0LA_0RB0RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm273: halts_at_trans (TM_from_str "1RB---_1RC1RA_1RD0LD_1LE0RB_0LE0LF_0LA1LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm274: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1LA1LD_0LB---_1LD1RF_0RE0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm275: halts_at_trans (TM_from_str "1RB0RA_1LC1RF_1LE0LD_0RC0LB_1LF---_1RD0LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm276: halts_at_trans (TM_from_str "1RB0LE_0RC---_1RD0LA_1RE1RA_1LC1RF_1RE0RD") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm277: halts_at_trans (TM_from_str "1RB1RA_1RC0RF_0RD---_1LE1LF_1LF1LE_1RA0LD") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm278: halts_at_trans (TM_from_str "1RB1LE_0LC0RB_0RA1RD_1LA0RF_0LD0LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm279: halts_at_trans (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1RB0LB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm280: halts_at_trans (TM_from_str "1RB0RA_0RC0RD_1LD0RF_1LE0LD_1RA0LD_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm281: halts_at_trans (TM_from_str "1RB0LA_1RC1LA_0LD1RF_1RE0RD_1LB0RD_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm282: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1LA_0LE0LF_1LA0RF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm283: halts_at_trans (TM_from_str "1RB---_0LC1LB_1LE1LD_1LB1LA_1RF0RF_0LD0RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm284: halts_at_trans (TM_from_str "1RB1RD_0RC1LC_0LC1LD_1RE0LD_0RB0RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm285: halts_at_trans (TM_from_str "1RB0LE_0RC0RF_0LD0RA_1LA1LC_0LC---_1LA1RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm286: halts_at_trans (TM_from_str "1RB0LE_0RC0RB_0LD1RB_1LA1LF_0LD0RF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm287: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1RD1RB_0LA0RA_1LD1LF_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm288: halts_at_trans (TM_from_str "1RB0RE_0LC0RA_0LD1LC_1LA0LA_0RA0RF_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm289: halts_at_trans (TM_from_str "1RB0RE_0RC0LB_1LD1RA_1LB1RF_0RD1RE_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm290: halts_at_trans (TM_from_str "1RB0RE_0RC0LC_1LD1RA_1LE1LD_1RF0RB_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm291: halts_at_trans (TM_from_str "1RB0RD_1LC0LF_0RE0LD_1LC1LA_0RA1RE_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm292: halts_at_trans (TM_from_str "1RB0LE_0RC1RF_0LD0RA_1LA1LC_0LC---_1RF0LC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm293: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_0LD0LB_1RA0LE_0LF---_0LA1LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm294: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1LD1RF_1LA0LD_1RA0RD_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm295: halts_at_trans (TM_from_str "1RB---_0RC1LC_1RD1RE_1LB0LD_0RA0RF_1RA0RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm296: halts_at_trans (TM_from_str "1RB0RC_1LA0LD_1RF1RD_1LE1RA_0LC0LE_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm297: halts_at_trans (TM_from_str "1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm298: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1LE1LF_0LA0RA_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm299: halts_at_trans (TM_from_str "1RB1RC_1LC1LB_1LD0RA_1RF1LE_0LF---_0LB1LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm300: halts_at_trans (TM_from_str "1RB---_1RC1RB_0RD1RA_1LD0RE_0RB0LF_1LE0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm301: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_1LE1LF_1RA0LC_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm302: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0LD1LA_1RE---_1LF0LC_1RE1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm303: halts_at_trans (TM_from_str "1RB1LB_1LC0RF_1RE0LD_1LE---_1LA0LE_0RA0RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm304: halts_at_trans (TM_from_str "1RB---_0RC1RF_1LB1LD_0LE1LE_1RF0LD_0RB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm305: halts_at_trans (TM_from_str "1RB---_0RC0RB_1RD0LF_0RE0RA_1RF0RB_1LC1LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm306: halts_at_trans (TM_from_str "1RB0RC_1LA0LD_1RE1LB_0LF1LC_0RD0RE_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm307: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA0RA_1LD1LF_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm308: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_0RD0LC_0LB1RE_0RA---_1RA1RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm309: halts_at_trans (TM_from_str "1RB0RE_0RC0LB_1LD1RA_1LB---_0RF1RE_1RA1RC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm310: halts_at_trans (TM_from_str "1RB0RB_1LC0LE_0RD0LB_0RA1RD_0LB1LF_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm311: halts_at_trans (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm312: halts_at_trans (TM_from_str "1RB0RC_1RC1RF_0LD0RE_1LB1LD_0LA1RA_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm313: halts_at_trans (TM_from_str "1RB1LC_0LC0RE_0LD1LC_1LA1LF_0RB0RA_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm314: halts_at_trans (TM_from_str "1RB0RC_1LA0LD_1RE1LB_0LA1LC_---0RF_0RD0RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm315: halts_at_trans (TM_from_str "1RB0RA_1LC0LC_0LD0RD_1RA1LE_1LC1LF_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm316: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_0LD0LC_0RE1RB_1RF---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm317: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_0RA0LD_1LC0LD_1RF---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm318: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_0LD0RB_1LA0RE_1LF---_0LD0LE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm319: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RD_1LF0LE_0RB---_1LA0LC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm320: halts_at_trans (TM_from_str "1RB0RF_1LC0RC_1RA1LD_1RB1LE_1LD0LE_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm321: halts_at_trans (TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RE0RA_1RA0RC_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm322: halts_at_trans (TM_from_str "1RB1RE_1LC0LB_1RD0LB_0RA0RE_1RF---_0RC0RF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm323: halts_at_trans (TM_from_str "1RB0LA_0RC---_1RD1RC_0RE1LF_1RF1LB_1LD1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm324: halts_at_trans (TM_from_str "1RB0RB_1LC0LE_0RD0LB_0RA1RD_1LF1LF_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm325: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1LD1RA_0LE0LD_1RB1LD_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm326: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0RD0LC_0LB1RD_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm327: halts_at_trans (TM_from_str "1RB0RA_1LC1RE_1LD0LC_1RB0LE_1RA0RF_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm328: halts_at_trans (TM_from_str "1RB0LE_1RC0RE_0RD0RA_1LE1RE_0LA0RF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm329: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RD_1LF0LE_0RB---_1LA0LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm330: halts_at_trans (TM_from_str "1RB1RF_1RC0LC_0LD1RE_1RB1LD_0RA---_1LB1RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm331: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_1LD0LC_0RB0LC_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm332: halts_at_trans (TM_from_str "1RB0RB_1LC0LE_0RD0LB_0RA1RD_0LB0LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm333: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_0LD1RB_1LE1LF_0LA0RA_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm334: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1LD0RA_1LE1LF_0LA1LC_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm335: halts_at_trans (TM_from_str "1RB0RA_1LC1RE_1LD0LC_1RA1LF_1LB0LA_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm336: halts_at_trans (TM_from_str "1RB---_0RC0RD_1LD0LB_0LE1LE_1RF0LD_0RB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm337: halts_at_trans (TM_from_str "1RB0LF_1LC0RE_1RA0LD_1LA0LA_0RC---_1LA1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm338: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LA_1LE1RB_0LF0LE_1RB1RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm339: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_1LE0LF_1RA0LC_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm340: halts_at_trans (TM_from_str "1RB1RF_1LC1RA_0LD0LC_1RE0RB_1RF---_0RD0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm341: halts_at_trans (TM_from_str "1RB1RE_1LC0RF_1LD0LC_1RE0RA_1RA0RC_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm342: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0RB0LD_1LC0LD_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm343: halts_at_trans (TM_from_str "1RB1LD_1LC0LC_0RA1LB_1RE0RA_1RF0RD_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm344: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1RD0LC_0LA0RF_1RA0RB_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm345: halts_at_trans (TM_from_str "1RB1LB_1LC0RD_0LE1LA_1RF1RA_1LE0LA_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm346: halts_at_trans (TM_from_str "1RB0LF_0RC1RB_1LD1RE_0LC1LA_1LC0RE_---1LA") c0 (F,0).
Proof. solve_halt'' 8 false. Time Qed.

Lemma tm347: halts_at_trans (TM_from_str "1RB0RC_1RC1LB_1LD1RA_1RE0LD_1RF1RD_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm348: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1LA_0LE---_1LA0RC_0LE0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm349: halts_at_trans (TM_from_str "1RB0LB_0RC0RB_1LD0LF_1LE---_1LA0LF_1RB1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm350: halts_at_trans (TM_from_str "1RB0RC_0RC1RA_1LD1LE_0LE0LF_0RA0LC_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm351: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1RE1LC_1RA1RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm352: halts_at_trans (TM_from_str "1RB1LE_0LC0RB_0RA0RD_1LC---_0LF0LD_1LA1RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm353: halts_at_trans (TM_from_str "1RB0LB_1LC0RF_0LC0LD_1RE1LC_1RA---_1RA1RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm354: halts_at_trans (TM_from_str "1RB0RA_0RC0RA_0LD0LF_1LE0RF_1RA1LC_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm355: halts_at_trans (TM_from_str "1RB0RB_0LC1RA_1LA1RD_1LE0LC_1LF0LD_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm356: halts_at_trans (TM_from_str "1RB---_0LC0RE_0LD1LC_1LE0LE_1RB0RF_0RA0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm357: halts_at_trans (TM_from_str "1RB0LF_1LB0RC_1RA1RD_1LE0RA_---1LC_1LE1LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm358: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_0RD0LF_0LE---_1LF1LD_0LA0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm359: halts_at_trans (TM_from_str "1RB1LC_1LA0RE_0LD0LF_1LA0RF_1RB0RE_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm360: halts_at_trans (TM_from_str "1RB1RF_0RC0LA_1RD1RA_1LE0LE_0RA0LD_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm361: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_1RE0LD_0LB0LA_0RA0RE_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm362: halts_at_trans (TM_from_str "1RB0RD_1RC0RF_1RD---_1LE1RD_0RA0LF_1LA0LE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm363: halts_at_trans (TM_from_str "1RB0LB_0RC0RB_1LD0LF_1LE---_1LA1RF_1RB1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm364: halts_at_trans (TM_from_str "1RB1RF_0RC0LA_1RD1RA_1LE0LE_0RA0LD_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm365: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LE0LD_1RC---_0LF1LE_1LA1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm366: halts_at_trans (TM_from_str "1RB1LE_1RC1RB_1RD0RE_0LA1LD_---1LF_0RB0LD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm367: halts_at_trans (TM_from_str "1RB---_0LC1RD_1LB1LD_1RE0LD_1RF0RD_0RC1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm368: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_0RD0LC_0LB1LE_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm369: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LC0LE_0LF1LD_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm370: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1RD1RA_1LE0LE_0RA0LD_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm371: halts_at_trans (TM_from_str "1RB1LA_1LC0RC_1RE0LD_1LC0LD_1RA0RF_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm372: halts_at_trans (TM_from_str "1RB1LE_1LC0LC_0RE1LD_1RE0LB_1LF0RC_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm373: halts_at_trans (TM_from_str "1RB---_0RC0LD_0RD0RB_1LE0LA_0LF0RF_1LC0LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm374: halts_at_trans (TM_from_str "1RB0RC_1RC1RA_1RD0LF_1RE1RA_1RF---_1LC1LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm375: halts_at_trans (TM_from_str "1RB0RF_0LC---_1LD0LD_0RE1LC_1RC1LF_1RA0RE") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm376: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RD_1LE1RC_1LA0LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm377: halts_at_trans (TM_from_str "1RB0LE_1RC0RF_1RD1LC_1LE0RA_1LA0LE_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm378: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LE1LD_1LE---_0LF0RC_1LA1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm379: halts_at_trans (TM_from_str "1RB---_1RC1LB_1LB0LD_1LA1LE_1RF1LC_0RD0RF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm380: halts_at_trans (TM_from_str "1RB1LC_1LC1RF_0RD0LC_0LB0LE_1RF---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm381: halts_at_trans (TM_from_str "1RB---_0LC1LD_1LF1RD_0RE0RA_1RC0LA_0RB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm382: halts_at_trans (TM_from_str "1RB1LE_0LC0RB_0RA0RD_1LE---_0LF0LD_1LA1RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm383: halts_at_trans (TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LC0RE_0RF---_0RB1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm384: halts_at_trans (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm385: halts_at_trans (TM_from_str "1RB---_0RC0LC_1RD1RF_1LE0LE_0RF0LD_1RB1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm386: halts_at_trans (TM_from_str "1RB0RA_0LC0LD_1LF0RD_1LE0RC_0RF---_1RA1LB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm387: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_1LD0LC_1RB0LC_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm388: halts_at_trans (TM_from_str "1RB0RC_1LA1RB_1RF1RD_1LE1RA_0LC0LE_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm389: halts_at_trans (TM_from_str "1RB1LC_1RC0RB_0LD0LE_1LA0RE_1LF0RD_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm390: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_0LD1LB_1RA0LE_1LC1LF_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm391: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LA1LD_1LE0LF_0RD1LB_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm392: halts_at_trans (TM_from_str "1RB0LC_0RC---_1RD0LA_1LE1RF_1LF0LE_0RC0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm393: halts_at_trans (TM_from_str "1RB1RC_0LC---_1LF1RD_1RE0RA_1LD1RE_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm394: halts_at_trans (TM_from_str "1RB0LC_1LC1RE_1RA1LD_1LA0LC_1RF0RA_---0RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm395: halts_at_trans (TM_from_str "1RB0LD_1RC1RF_0RD1RA_1LE0RB_0LA0RA_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm396: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RE1RF_0RB0LB_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm397: halts_at_trans (TM_from_str "1RB0RF_1RC---_0RD1LD_1RE1RF_1LC0LE_0RB0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm398: halts_at_trans (TM_from_str "1RB0RA_0RC0LE_1LD1RD_1RB1RF_0LA1LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm399: halts_at_trans (TM_from_str "1RB1RE_0LC1LB_1RE1LD_1LB1LF_0RA0RE_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm400: halts_at_trans (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1RB0LB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm401: halts_at_trans (TM_from_str "1RB0RC_1LA0LD_---1LB_0LA1LE_1RF1LB_0RD0RF") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm402: halts_at_trans (TM_from_str "1RB0RE_1RC1RA_1LD0RC_0RB0LC_1LF0RF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm403: halts_at_trans (TM_from_str "1RB---_1LC1RE_1LD0LC_1RB0LE_1RF1LD_1RB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm404: halts_at_trans (TM_from_str "1RB1RF_0RC0LE_1LD1RA_1RB0RD_0LD1LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm405: halts_at_trans (TM_from_str "1RB1LD_1LC0LC_0RA1LB_1RE0RA_1RF0RD_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm406: halts_at_trans (TM_from_str "1RB1LA_1LA0LC_1LF1LD_1RE1LB_0RC0RE_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm407: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_1LA0LC_0RE0RF_1RB0LF_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm408: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_0LD0LC_1RE1RB_1RF---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm409: halts_at_trans (TM_from_str "1RB0LB_1LA0LC_1LF1RD_0RE---_1RF0RC_0RA0RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm410: halts_at_trans (TM_from_str "1RB1LE_0RC0LB_1LD0RF_0LA0LA_1LA---_1RB1RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm411: halts_at_trans (TM_from_str "1RB0RD_1RC0LF_1LD0RF_0LE0RE_0RB1LC_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm412: halts_at_trans (TM_from_str "1RB0RF_0RC1RB_1RD1RA_1LE0LE_0RA0LD_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm413: halts_at_trans (TM_from_str "1RB0LD_1LC1RE_0LD0LC_1RE1RB_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm414: halts_at_trans (TM_from_str "1RB0LB_1LC0RF_0LC1LD_0LE0RA_1RF---_1RA1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm415: halts_at_trans (TM_from_str "1RB1RF_1LC1RA_1LF0LD_0LE0LF_1RA---_1LD0RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm416: halts_at_trans (TM_from_str "1RB---_0RC0RD_1LD1LD_0LE1LE_1RF0LD_0RB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm417: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1RD1RA_1LE0LE_0RA0LD_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm418: halts_at_trans (TM_from_str "1RB0LC_1RC0RB_1LD0RA_0LE0LC_0LA1LF_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm419: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1LA_0LE0LF_1LA0RC_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm420: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_0LD1RB_1LE---_0LA0RA_1LE1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm421: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_0LD1LB_1RA0LE_1LC1LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm422: halts_at_trans (TM_from_str "1RB1LF_1LC0RB_0RC1LD_0RE---_1LA1RE_1LE0LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm423: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_0RD0LD_1LE1RB_0LA0LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm424: halts_at_trans (TM_from_str "1RB1RC_1LC1LB_1LD0RA_1RC1LE_0LF---_0LB1LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm425: halts_at_trans (TM_from_str "1RB0RF_1RC0RF_0RD0LC_1LE1RD_1LC0RF_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm426: halts_at_trans (TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RE0RB_1RA0RC_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm427: halts_at_trans (TM_from_str "1RB0RE_0RC1RB_1LD1RC_1RA1LF_1LC---_0LB0LD") c0 (E,1).
Proof. solve_halt'' 8 false. Time Qed.

Lemma tm428: halts_at_trans (TM_from_str "1RB0RE_0RC0LC_1LD1RA_1LE1LD_0RF0RB_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm429: halts_at_trans (TM_from_str "1RB0LD_1LC1RF_0LD0LC_1RE1RB_0LB---_0RA0RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm430: halts_at_trans (TM_from_str "1RB0LD_1LC1RA_---1LD_1LE0RA_1LA0LF_1RA1LB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm431: halts_at_trans (TM_from_str "1RB---_0LC0RB_1RA1LD_1LB0LE_0LF1LE_1LD1LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm432: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD1LE_1LE1RB_1RF0LE_0LC0LD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm433: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_0LD0LB_0LE1LD_1RA1RF_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm434: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1LA_0RA---_1LF0LC_1RE1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm435: halts_at_trans (TM_from_str "1RB1LB_0RC0RD_1LD0RA_0LA1LE_0LF---_0LD1LC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm436: halts_at_trans (TM_from_str "1RB1RF_0RC1RB_1RD1RA_1LE0LE_0RA0LD_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm437: halts_at_trans (TM_from_str "1RB---_1RC0RC_1RD0LE_1RE1RA_1LF1LC_0LC1LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm438: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RE0LD_1LB1LF_0RE0RA_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm439: halts_at_trans (TM_from_str "1RB0RF_1LC1RA_1RF0LD_1RE0LB_0RC---_1RB1RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm440: halts_at_trans (TM_from_str "1RB1RD_0LC0RA_0LD1LC_1LE0LA_1RB0RF_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm441: halts_at_trans (TM_from_str "1RB0LD_1LC1RD_1LA0LC_1RE0RF_1RB0RE_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm442: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0LB_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm443: halts_at_trans (TM_from_str "1RB1RF_1LC0RE_1LD0LB_1RE0LC_0RA0RD_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm444: halts_at_trans (TM_from_str "1RB1RF_0RC1RE_1LD0RA_0LE0RE_1RA0LC_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm445: halts_at_trans (TM_from_str "1RB0RA_0RC0RA_0LD0LF_1LE0RF_1RB1LC_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm446: halts_at_trans (TM_from_str "1RB1LE_0LC1RF_1RD0RC_1LA0RC_1RA0LE_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm447: halts_at_trans (TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RE0RB_0LB0RC_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm448: halts_at_trans (TM_from_str "1RB1RD_0RC0RF_1RD0LA_1LE1RB_0LA0LE_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm449: halts_at_trans (TM_from_str "1RB0LF_1LC0RE_0LC1LD_1LA0RB_0RB0RD_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm450: halts_at_trans (TM_from_str "1RB1LE_0LC1LB_1RD1LA_0RE0RD_0LF1RD_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm451: halts_at_trans (TM_from_str "1RB0RE_0LC0LE_1RF0RD_1LE---_0LB0RC_0RA0LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm452: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LF0RD_1LE---_0LC0LD_1RA1LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm453: halts_at_trans (TM_from_str "1RB0RB_1LC0RD_1RE0LD_0RE0RF_0LB0RA_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm454: halts_at_trans (TM_from_str "1RB0LD_0LC1RE_1RA1LC_---1LE_0RF0LA_0LC0RB") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm455: halts_at_trans (TM_from_str "1RB1RF_0RC0LD_1LA1RA_0LE1LD_1RB0RE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm456: halts_at_trans (TM_from_str "1RB0RF_1LC0RE_1LD0LB_1RE0LC_0RA0RD_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm457: halts_at_trans (TM_from_str "1RB1LD_0RC0RB_1LD1RB_1LE1LF_0LA1LE_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm458: halts_at_trans (TM_from_str "1RB0LA_1LC0RE_0LD0LC_1LA1RF_0RA0RD_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm459: halts_at_trans (TM_from_str "1RB0LA_0RC1RC_0RD1RF_0LE1RA_1LA1LE_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm460: halts_at_trans (TM_from_str "1RB0LB_1LC0RC_1RA1RD_1RF1LE_0LE0LD_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm461: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_---1LA_1RA1LE_0RA0LF_1RE1LB") c0 (C,0).
Proof. solve_halt'' 14 false. Time Qed.

Lemma tm462: halts_at_trans (TM_from_str "1RB0RB_0LC0RA_1LF1LD_0RE---_1LA1LC_0LE1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm463: halts_at_trans (TM_from_str "1RB1RC_1LC1RB_1RE0LD_1LB1RF_---0RA_0RF0RB") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm464: halts_at_trans (TM_from_str "1RB0RB_1LC1RB_1LF1LD_1LE0LC_1RA1RE_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm465: halts_at_trans (TM_from_str "1RB0RA_0LC0LD_1LF0RD_1LE0RC_0LC---_1RA1LB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm466: halts_at_trans (TM_from_str "1RB0RA_0LC0RA_1LD1LC_0LE1LF_1RE0LB_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm467: halts_at_trans (TM_from_str "1RB1LE_0LC0RB_0RA0RD_1LE---_0LF0LD_1LA0RD") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm468: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm469: halts_at_trans (TM_from_str "1RB0RE_0LC0RA_0LD1LC_1LA0LA_0RA1RF_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm470: halts_at_trans (TM_from_str "1RB0RB_1LC0RE_0LA0LD_1LA0LE_0RB0LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm471: halts_at_trans (TM_from_str "1RB0RF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm472: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm473: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD1LE_1LE1RB_1RF0LE_0LC0RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm474: halts_at_trans (TM_from_str "1RB0LF_1LC1RE_1RB0LD_1LC0LD_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm475: halts_at_trans (TM_from_str "1RB0LB_1LC0RF_1LE0LD_0LE---_1LA1RE_1RB0RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm476: halts_at_trans (TM_from_str "1RB1RD_0RC0RF_1RD0LF_1LE1RB_0LA0LE_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm477: halts_at_trans (TM_from_str "1RB0LB_0RC0RB_0LD0RA_1LE---_0LF0LC_1RA1LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm478: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA1RE_0RC0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm479: halts_at_trans (TM_from_str "1RB1RD_1RC0RA_1LD1RB_0RE0LD_0LC1RF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm480: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_0LD1RB_1LE---_0LA1LE_1LE1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm481: halts_at_trans (TM_from_str "1RB---_1LC0LA_0LD0RD_1LE1LB_1RF0RF_0LB0RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm482: halts_at_trans (TM_from_str "1RB---_1RC0LB_1LD0RF_0LE0LD_1LB1RA_0RB0RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm483: halts_at_trans (TM_from_str "1RB0RD_1LC1RE_1LD0LC_1RB0LE_1RA0RF_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm484: halts_at_trans (TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0LA_0LC1LF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm485: halts_at_trans (TM_from_str "1RB1LE_1LC0RE_1RA0LD_1LA0LA_0RC1RF_---0RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm486: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_0RD1RB_0LE---_1LF1LD_0LA1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm487: halts_at_trans (TM_from_str "1RB1RE_0LC0RC_1RE1LD_1LB1LF_0RA0RE_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm488: halts_at_trans (TM_from_str "1RB1RB_1RC0LE_0RD1LD_1RE0RA_1LB1RF_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm489: halts_at_trans (TM_from_str "1RB1LC_1LC0RF_1RD0LC_0RE---_0LB1RA_1RA1RC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm490: halts_at_trans (TM_from_str "1RB---_1LC0RA_1LD0LB_1RE1LD_0RC1RF_0LB0RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm491: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LD0RD_1LA0LE_1LB1RB_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm492: halts_at_trans (TM_from_str "1RB---_1RC1LE_0RD0RC_1LE1RC_1LF0LA_0LB0RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm493: halts_at_trans (TM_from_str "1RB1LA_1LB1RC_0LD0RD_0RE0LF_1LC---_1RA0LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm494: halts_at_trans (TM_from_str "1RB0LD_0RC1LC_1RD0RE_1LA1RF_1RA1RA_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm495: halts_at_trans (TM_from_str "1RB0RA_0RC1RA_0LD1LC_1LE1LF_0RB0LC_---1LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm496: halts_at_trans (TM_from_str "1RB0LE_0RC0LD_1LD1RF_0LA0RD_1LD1LA_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm497: halts_at_trans (TM_from_str "1RB---_0LC0LE_0LD1LC_1RA0LF_1LD0RF_0RC1LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm498: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1LA_0RA---_1RF0LC_1RE1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm499: halts_at_trans (TM_from_str "1RB0RF_1LC0RD_1LA0LC_1RE1LA_0RB1RA_---1LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm500: halts_at_trans (TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA1RE_1LB0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm501: halts_at_trans (TM_from_str "1RB0RC_1LC0RE_0LD1LB_1RA---_1RF0LB_1RA0RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm502: halts_at_trans (TM_from_str "1RB0RE_1LC1RB_0LA1LD_1LE0LC_1RA0LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm503: halts_at_trans (TM_from_str "1RB0LA_0LC0RF_1LE1LD_1LC0RD_1LA0LE_---1RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm504: halts_at_trans (TM_from_str "1RB---_1LC1LB_1RD0LB_1RF1RE_1RD0RC_0RA0LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm505: halts_at_trans (TM_from_str "1RB0LA_1RC1RB_0RD1RF_1LE0RF_1LA---_1LE1RA") c0 (E,1).
Proof. solve_halt'' 23 false. Time Qed.

Lemma tm506: halts_at_trans (TM_from_str "1RB1LA_1LC0LC_1RE0LD_1LC0LA_1RB0RF_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm507: halts_at_trans (TM_from_str "1RB1LF_1LC1RD_1LA0LC_0RE1RD_1RB0RB_---0LC") c0 (F,0).
Proof. solve_halt'' 36 false. Time Qed.

Lemma tm508: halts_at_trans (TM_from_str "1RB0LF_1LC1RD_1LA0LC_0RE1RD_1RB0RB_---1RB") c0 (F,0).
Proof. solve_halt'' 36 false. Time Qed.

Lemma tm509: halts_at_trans (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0RA_1LD0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm510: halts_at_trans (TM_from_str "1RB0RD_1LC1RB_1RD0LB_1RF1RE_1RE0RA_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm511: halts_at_trans (TM_from_str "1RB1LB_0RC---_1RD0RF_1LE0LE_0LA0LD_1RC1LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm512: halts_at_trans (TM_from_str "1RB1LF_0LC---_0RE1LD_1LE1RF_1RC0LA_1LB0RF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm513: halts_at_trans (TM_from_str "1RB---_1LC0RB_1LD1RD_0LF1LE_0RA1LB_1RA0LE") c0 (A,1).
Proof. solve_halt'' 23 false. Time Qed.

Lemma tm514: halts_at_trans (TM_from_str "1RB0RF_1LC1RB_0LD1LD_1RE0LC_0RE1RA_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm515: halts_at_trans (TM_from_str "1RB1RA_0RC0LC_1LD1LE_0LC1RF_1RD0LE_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm516: halts_at_trans (TM_from_str "1RB0RB_1LC1RE_1LD0LC_1RB0LF_0RA1LF_---1RB") c0 (F,0).
Proof. solve_halt'' 36 false. Time Qed.

Lemma tm517: halts_at_trans (TM_from_str "1RB0LF_1RC---_0LD0LE_0LA1LD_1LA0RF_0RD1LC") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm518: halts_at_trans (TM_from_str "1RB1RC_0LC---_1LF1RD_1LE0RA_1LD1RE_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm519: halts_at_trans (TM_from_str "1RB0RF_1LC1RB_0RD0LB_---0LE_1RE0RA_1RC1RE") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm520: halts_at_trans (TM_from_str "1RB0LF_0LC1LB_1RD1LA_0RE0RD_1LB1RD_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm521: halts_at_trans (TM_from_str "1RB1RF_1LC0LB_1LD0LB_1RE0RD_0RA1RD_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm522: halts_at_trans (TM_from_str "1RB1LE_0LC0RD_0RD0LB_1LE1RC_1LA1LF_---0RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm523: halts_at_trans (TM_from_str "1RB0LC_0LC1RD_1LA1RC_1RE0RF_---1LB_1RC0RB") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm524: halts_at_trans (TM_from_str "1RB---_1RC1LF_0RD0RC_1RE1RC_0LB1LE_1RE0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm525: halts_at_trans (TM_from_str "1RB---_1LC1LD_1RC0LB_0LE0RD_1RA1LF_0LC1LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm526: halts_at_trans (TM_from_str "1RB0LE_0RC1RF_1RD0RF_1LA---_1LA1LE_0RA1RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm527: halts_at_trans (TM_from_str "1RB1RB_1RC0LE_0RD0LD_1RE0RA_1LB1RF_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm528: halts_at_trans (TM_from_str "1RB---_1LC1LE_1LD1LC_0RB0LD_1RF0RC_1RA0RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm529: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_1LE---_1LF0LD_0LA1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm530: halts_at_trans (TM_from_str "1RB0LA_0RC1RC_1LD0RE_0RD0LE_1LA1RF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm531: halts_at_trans (TM_from_str "1RB1LA_0RC1RE_0RD0LF_1LE---_0LC0RC_1RA0LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm532: halts_at_trans (TM_from_str "1RB1LC_1LC0RE_0LF0LD_1RA---_1RF0RE_1LA0RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm533: halts_at_trans (TM_from_str "1RB1LF_1RC---_0RD0LA_1RE0RB_1LF0RC_0LC0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm534: halts_at_trans (TM_from_str "1RB1LE_1LC0RB_0RD0LD_1LA1RB_1RC0LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm535: halts_at_trans (TM_from_str "1RB0LE_1LC0RD_1LA1LC_---1RE_1LF0RE_0RD0LB") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm536: halts_at_trans (TM_from_str "1RB---_1RC1LF_0RD0RC_1RE1RC_0LB0RB_1LE0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm537: halts_at_trans (TM_from_str "1RB---_0LC1RA_1LF1RD_0RE0RD_1RC0LA_0RB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm538: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LD0RD_1LA0LE_1LB1LB_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm539: halts_at_trans (TM_from_str "1RB1LB_0RC1RF_1LD0RF_1LE---_1RA0LE_0LD1RE") c0 (D,1).
Proof. solve_halt'' 23 false. Time Qed.

Lemma tm540: halts_at_trans (TM_from_str "1RB0LF_1LC1RD_1LA0LC_0RE1LF_1RB0RB_---1RB") c0 (F,0).
Proof. solve_halt'' 36 false. Time Qed.

Lemma tm541: halts_at_trans (TM_from_str "1RB0LA_1RC---_0LD0LE_1RE1LA_1LA0RF_1RD1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm542: halts_at_trans (TM_from_str "1RB---_1LC1RB_1LB0RD_1RA1RE_1LF1RC_0LD0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm543: halts_at_trans (TM_from_str "1RB---_1RC1LE_0RD0RC_1LE1RC_1RF0LA_0LB1LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm544: halts_at_trans (TM_from_str "1RB1RE_0RC1RF_1LD0RF_1LE---_1RA0LE_0LD1RE") c0 (D,1).
Proof. solve_halt'' 23 false. Time Qed.

Lemma tm545: halts_at_trans (TM_from_str "1RB1RE_1LC---_1LD1RC_1LC0RA_1LF1RD_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm546: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA1RF_1RA1LA_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm547: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1LA_1RE---_1RF1LE_1RE0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm548: halts_at_trans (TM_from_str "1RB0LC_0RC1RE_1LD1RD_0LA0LB_0RF---_0RB1RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm549: halts_at_trans (TM_from_str "1RB---_0RC1LF_1RD0RA_0RE0LE_1LF1RC_0LB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm550: halts_at_trans (TM_from_str "1RB1LF_0LC---_0RE1LD_1LE1RF_1RF0LA_1LB0RF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm551: halts_at_trans (TM_from_str "1RB1RC_1LC1LE_0RF1LD_1RA0LD_---0RA_1RD0RE") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm552: halts_at_trans (TM_from_str "1RB---_1RC1LF_0RD0RC_1RE1RC_0LB1LE_1LE0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm553: halts_at_trans (TM_from_str "1RB1LC_1LC0RF_1RD0LC_0RE---_0LB1RA_1LD1RC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm554: halts_at_trans (TM_from_str "1RB1LD_0RC1RB_1LD1RE_0LA0LD_1LB0RF_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm555: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0LF_1LF0LE_1LD---_0LA0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm556: halts_at_trans (TM_from_str "1RB1LB_1RC0LE_0RD0LD_1RE0RA_1LB1RF_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm557: halts_at_trans (TM_from_str "1RB---_1RC0RC_0RD0RB_0LE0RF_1LF1RE_0LA0LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm558: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RE0LD_1LB0LF_0RE0RA_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm559: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LA_1RC1RC_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm560: halts_at_trans (TM_from_str "1RB1LC_1LC0RF_1RD0LC_1RE---_0LA0LB_1RA1RC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm561: halts_at_trans (TM_from_str "1RB1LE_0LC0RD_0RD0LB_1LE1RC_1LA0LF_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm562: halts_at_trans (TM_from_str "1RB0LA_1RC0LF_0RD1RF_1LE0RF_1LA---_1LE1RA") c0 (E,1).
Proof. solve_halt'' 23 false. Time Qed.

Lemma tm563: halts_at_trans (TM_from_str "1RB1RA_0LC0RB_1RA1RD_1LE0LA_1LF0LD_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm564: halts_at_trans (TM_from_str "1RB1RC_1LB0RA_0RD0LC_1LE1RF_1LA---_0RB1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm565: halts_at_trans (TM_from_str "1RB0LE_0RC0RC_1LD1RF_0LA0RD_1LD1LA_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm566: halts_at_trans (TM_from_str "1RB1LB_1LC0RE_0LD1RD_1LE0LA_1RB1LF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm567: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LD1RD_1LA0LE_1LB1LB_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm568: halts_at_trans (TM_from_str "1RB1LF_1RC---_1LD1LE_1RD0LC_0LA0RE_0LD1LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm569: halts_at_trans (TM_from_str "1RB0RD_1LC1RB_1RD0LB_0LB1RE_1RF0RA_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm570: halts_at_trans (TM_from_str "1RB0LD_1RC0RD_1LA0RE_0LA1LD_1RF---_1RF0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm571: halts_at_trans (TM_from_str "1RB---_1LC0RA_0LD0RD_1RF1LE_1RC0LE_1LE1RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm572: halts_at_trans (TM_from_str "1RB0RB_1LC1RE_1LD0LC_1RE0LF_0RA1RE_---1RB") c0 (F,0).
Proof. solve_halt'' 36 false. Time Qed.

Lemma tm573: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LA0RA_1RC1LE_1LD0LE_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm575: halts_at_trans (TM_from_str "1RB1RE_1RC1LE_1LD0RA_0LC1RB_1RF0LE_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm576: halts_at_trans (TM_from_str "1RB1RD_1LC0LB_1RA1LB_0RE0RB_1RF0RB_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm577: halts_at_trans (TM_from_str "1RB---_1LC0RB_1LD1LB_0LE1LF_1RA0LF_0RA1LB") c0 (A,1).
Proof. solve_halt'' 23 false. Time Qed.

Lemma tm578: halts_at_trans (TM_from_str "1RB0LD_1RC0RB_1LA1RB_1LE1RC_0LA1LF_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm579: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LD1LC_1LE1RD_1LA0LA_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm580: halts_at_trans (TM_from_str "1RB0RF_1RC1RA_0RD0LA_1RE---_1LF1LE_1RB0LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm581: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_0LD1RD_1LA0LE_1RB1LB_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm582: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1LA1LC_1RA0RF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm583: halts_at_trans (TM_from_str "1RB1RD_1RC1LD_1LD0RA_1RE0LD_0RF---_0LC1RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm584: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_---0LD_0LE1LD_1RE1LF_1LB0LA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm585: halts_at_trans (TM_from_str "1RB0LC_0LC1RD_1LA1RC_1RE0RF_---0RF_1RC0RB") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm586: halts_at_trans (TM_from_str "1RB0RB_1LC1RE_1LD0LC_1RB0LF_0RA1RE_---1RB") c0 (F,0).
Proof. solve_halt'' 36 false. Time Qed.

Lemma tm587: halts_at_trans (TM_from_str "1RB0RE_0LC---_1LD1LC_1RA0LF_0RA1RE_1LF0LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm588: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_1LD1RB_1LE0LB_0LA1LC_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm589: halts_at_trans (TM_from_str "1RB---_1RC1LE_0RD0RC_1LE1LB_0LF0LA_1LB0RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm590: halts_at_trans (TM_from_str "1RB---_1LC0RC_1RE0LD_1LB0LA_0RE0RF_1RB1RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm591: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD1LA_1LE---_1RF1LE_1RE0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm592: halts_at_trans (TM_from_str "1RB0RB_1LC1RE_1LD0LC_1RE1LF_0RA1RE_---0LC") c0 (F,0).
Proof. solve_halt'' 36 false. Time Qed.

Lemma tm593: halts_at_trans (TM_from_str "1RB0RB_1LC1RE_1LD0LC_1RB1LF_0RA1RE_---0LC") c0 (F,0).
Proof. solve_halt'' 36 false. Time Qed.

Lemma tm594: halts_at_trans (TM_from_str "1RB0RD_1LC1RB_1RD0LB_1RF1RE_1RE0RA_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm595: halts_at_trans (TM_from_str "1RB1RD_1RC1LD_1LD0RA_1RE0LD_1RF---_0LB0LC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm596: halts_at_trans (TM_from_str "1RB0LD_0RC---_0RD1RC_1LE1RF_1LF0LE_1RC0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm597: halts_at_trans (TM_from_str "1RB1RD_1RC---_0LA0RC_1LE1LC_1LB0LF_0LD1LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm598: halts_at_trans (TM_from_str "1RB0RD_1LC1RE_1LD0LC_1RA0LE_0RC1RF_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm599: halts_at_trans (TM_from_str "1RB0RE_1LC0LC_1RA0LD_1LC0LF_0RC---_1RB1LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm600: halts_at_trans (TM_from_str "1RB1LC_1RC1RD_1LA0LC_0RE0RC_1RF0RC_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm601: halts_at_trans (TM_from_str "1RB0RD_1LC1RB_1RD0LB_0RF1RE_1RE0RA_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm602: halts_at_trans (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA1RF_1RA1RA_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm603: halts_at_trans (TM_from_str "1RB1RD_0RC0RB_1LD1LE_0LC0LF_1LA0RF_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm604: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_1LD1RB_0RE0LA_0LA0RD_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm605: halts_at_trans (TM_from_str "1RB0RE_1LC1RB_1RD0LB_---0LE_1RC1RF_1RF0RA") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm606: halts_at_trans (TM_from_str "1RB---_1RC1LF_1RD0RC_1LE0LE_0LB0RB_1LE0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm607: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA1LA_1RC1RC_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm608: halts_at_trans (TM_from_str "1RB0LF_1LC1RD_---1LD_1RE1LF_1LA0RA_1LB0LE") c0 (C,0).
Proof. solve_halt'' 28 false. Time Qed.

Lemma tm609: halts_at_trans (TM_from_str "1RB0RE_1LC1RB_1RE0RD_---1LE_0LB1RF_1RD0RA") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm610: halts_at_trans (TM_from_str "1RB0LE_1RC1RF_0RD0LF_1RE---_1LA1LE_1RB0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm611: halts_at_trans (TM_from_str "1RB0RB_1LC1RE_1LD0LC_1RE0LF_0RA1LF_---1RB") c0 (F,0).
Proof. solve_halt'' 36 false. Time Qed.

Lemma tm612: halts_at_trans (TM_from_str "1RB0RD_0LC1RE_1LA1RC_---1LB_1RD0RF_1RC0RB") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm613: halts_at_trans (TM_from_str "1RB1RF_1LB1RC_1RA1LD_1RE0LD_0RB---_0RC0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm614: halts_at_trans (TM_from_str "1RB1LB_0RC---_1RD0RF_1LE0LE_0LA0LD_1RC0RF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm615: halts_at_trans (TM_from_str "1RB0LA_1LC1RD_---1LA_1RF0RE_1LB0RC_1RA0RF") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm616: halts_at_trans (TM_from_str "1RB1RF_0RC0LC_1LD1RA_1LE0LD_1RC0RB_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm617: halts_at_trans (TM_from_str "1RB0RB_1LC0RA_1LE0LD_1LC1LF_1RA0LB_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm618: halts_at_trans (TM_from_str "1RB---_0RC1LF_1RD0RA_0RE1RD_1LF1RC_0LB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm619: halts_at_trans (TM_from_str "1RB1LD_1LC0RF_0LB1RA_1RE0LD_0RC---_1RA1RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm620: halts_at_trans (TM_from_str "1RB0RF_1LC1RB_1RD0LB_---1RE_1RE0RA_1RC1RE") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm621: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_1LE---_1LF0LD_0LA0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm622: halts_at_trans (TM_from_str "1RB0LE_0RC0RE_1LD1RF_0LA0RD_1LD1LA_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm624: halts_at_trans (TM_from_str "1RB0RA_0RC1RA_1RD1RE_1LE1RF_1LA0LD_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm625: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0LF_1LF0LE_1RF---_0LA0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm626: halts_at_trans (TM_from_str "1RB0LD_1RC1RB_1LA0RE_0LA1LD_1RF---_1RF0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm627: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0RB_1RE0LD_0RF1LE_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm628: halts_at_trans (TM_from_str "1RB0LA_0RC---_0LD1RE_1LA0RF_1RD1LA_1RE1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm629: halts_at_trans (TM_from_str "1RB0LA_0RC---_0LD1RE_1LC0RF_1RD1LA_1RE1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm630: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_0LC0LD_1LA1LC_1RA1RF_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm631: halts_at_trans (TM_from_str "1RB1LD_1LC0RF_0LB1RA_1RE0LD_0RC---_1LE1RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm632: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA1LA_1LC1RC_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm633: halts_at_trans (TM_from_str "1RB0RF_1LC0LB_1LD0LB_1RE0RD_0RA1RD_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm634: halts_at_trans (TM_from_str "1RB0LD_0RC1LC_1RD0RE_1LA1RF_1LA1RA_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm635: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1RF0LD_0RE1RB_0LB0RC_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm636: halts_at_trans (TM_from_str "1RB1LA_1RC0RC_1LD1RE_1RF0LC_0LD---_0RA1RF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm637: halts_at_trans (TM_from_str "1RB0RF_1LC0LE_0LD1LD_1RE0LC_0RE1RA_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm638: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0LF_0LF0LE_0LD---_1LC0RF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm639: halts_at_trans (TM_from_str "1RB---_1RC1RE_1LD0LC_1RB1LC_0RF0RC_1RA0RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm640: halts_at_trans (TM_from_str "1RB1RE_1LC0RC_1RE0LD_1LB1LF_0RE0RA_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm641: halts_at_trans (TM_from_str "1RB1LE_1RC1RF_1LD1RB_0RE0LA_0LA0RD_---0LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm642: halts_at_trans (TM_from_str "1RB0RD_1LC1RB_1RD0LB_0LB1RE_1RF0RA_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm643: halts_at_trans (TM_from_str "1RB0RF_1LC0LE_0LD1LD_1RE0LC_0RE1RA_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm644: halts_at_trans (TM_from_str "1RB1RE_1RC---_1LD1RC_1LC0RA_1LF1RD_0LA0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm645: halts_at_trans (TM_from_str "1RB---_1RC1LE_0RD0RC_1LE1RC_1LF0LA_0LB1LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm646: halts_at_trans (TM_from_str "1RB1RD_1RC0LE_1LD0RB_1LE0RA_1LB1LF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm647: halts_at_trans (TM_from_str "1RB0RF_1LC1RB_0LD1LD_1RE0LC_0RE1RA_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm648: halts_at_trans (TM_from_str "1RB0LA_0RC---_0LD1RE_1LA0RF_1RD1LA_1LB1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm649: halts_at_trans (TM_from_str "1RB1RF_0RC0LF_1RD---_1LE1LD_1RA0LD_1RA0RE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm650: halts_at_trans (TM_from_str "1RB1RC_1LC0LB_1LE1RD_---1LB_1RF0RE_0RA1RE") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm651: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_1RD0LB_0RA0LA_1RC1LC_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm652: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA1LD_1RD0LF_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm653: halts_at_trans (TM_from_str "1RB1LA_1RC0RD_1LA1RD_0RA1LE_0LF---_1LB0LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm654: halts_at_trans (TM_from_str "1RB1LF_1LC1RC_1LD0LC_0LE1LA_1RA0RE_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm655: halts_at_trans (TM_from_str "1RB1RF_1RC0LE_1RD1RF_1RE---_1LB1LE_1RA0RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm656: halts_at_trans (TM_from_str "1RB---_1RC0RF_1LD1LE_1RE0LC_1RF0RD_1LE1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm657: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LD1RB_1LE---_1RF0LD_0LA1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm658: halts_at_trans (TM_from_str "1RB0LA_0RC---_0LD1RE_1LC0RF_1RD1LA_1LB1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm659: halts_at_trans (TM_from_str "1RB---_0LC0LF_1RF1LD_0LE0RA_1LC0LF_0LD0RC") c0 (A,1).
Proof. solve_halt' 72 10000 false 0%N (10^8)%N. Time Qed.

Lemma tm660: halts_at_trans (TM_from_str "1RB1RF_1LC0LA_---1LD_1LE0LB_1RF0LB_0RA1RA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm661: halts_at_trans (TM_from_str "1RB1LA_0RC1LE_0RD1RF_1RE0LB_0LA1RD_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm662: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_1LA0LC_0RE---_1RF0RE_0RA1RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm663: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_1LD0LE_---1LA_0LB1LC_1RB1RF") c0 (D,0).
Proof. solve_halt' 6 3200 false 0%N (10^9)%N. Time Qed.

Lemma tm664: halts_at_trans (TM_from_str "1RB0LE_0LC0RE_1LA0RD_1LB0RB_0RD1LF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm665: halts_at_trans (TM_from_str "1RB0LE_1RC0RE_0LD1LB_1LA1RD_1RF0LC_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm666: halts_at_trans (TM_from_str "1RB1LC_1RC1RE_1LA0LD_0RD0LA_0RF0RE_1RA---") c0 (F,1).
Proof. solve_halt' 40 10000 true 0%N (10^8)%N. Time Qed.

Lemma tm667: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_0LE1LD_0LB1LC_1LF0LD_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm668: halts_at_trans (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_0RF1RC_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm670: halts_at_trans (TM_from_str "1RB0RC_1LC---_1RF0LD_1LE1RD_0LC0LA_0RA1RF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm671: halts_at_trans (TM_from_str "1RB0LE_1RC---_1LD0RC_1LF0RE_1RB1LC_0LA1LE") c0 (B,1).
Proof. solve_halt'' 23 false. Time Qed.

Lemma tm672: halts_at_trans (TM_from_str "1RB0LE_0RC1RB_1RD0RA_1LA---_1LF1RE_0LA0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm673: halts_at_trans (TM_from_str "1RB1RC_1LA1RF_---0RD_1LE0RB_1LE0LF_1RA0LF") c0 (C,0).
Proof. solve_halt' 228 1000000 false 0%N (10^9)%N. Time Qed.

Lemma tm674: halts_at_trans (TM_from_str "1RB---_0RC0LF_1RD1RA_0RE1LD_1RF0RD_1LB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm675: halts_at_trans (TM_from_str "1RB0LD_1RC0RE_1RD---_1LE1RF_1LC0LF_1LA0RA") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm676: halts_at_trans (TM_from_str "1RB1LE_0RC1RB_1RD1RF_0LA0LB_1LA0LD_---1RA") c0 (F,0).
Proof. solve_halt'' 7 false. Time Qed.

Lemma tm677: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1LD0LB_1RA1LE_0LA0LF_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm678: halts_at_trans (TM_from_str "1RB0LE_1RC---_1LD0RC_1LF1LA_1RB0LF_1RD1LC") c0 (B,1).
Proof. solve_halt' 228 1000000 false 0%N (10^9)%N. Time Qed.

Lemma tm679: halts_at_trans (TM_from_str "1RB1LE_0RC1RB_1LD0RB_1LA---_1LC0LF_1LA0LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm681: halts_at_trans (TM_from_str "1RB0LA_0RC0RD_1LC1LA_---1RE_0RB1RF_1RA1RE") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm682: halts_at_trans (TM_from_str "1RB0LD_0LC0RF_1LE0RD_1LB---_1LA0LD_0RB0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm683: halts_at_trans (TM_from_str "1RB1LE_1RC0RF_1LD1RD_1RC1RA_0LB0LA_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm684: halts_at_trans (TM_from_str "1RB0LE_0RC0RD_1LD0RF_0LA---_1LA0RC_1RA1RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm685: halts_at_trans (TM_from_str "1RB0RF_1LC1RC_1RB1RD_1RA1LE_0LA0LD_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm686: halts_at_trans (TM_from_str "1RB0LE_0RC1RF_1RD0RF_1RE---_1LA1LE_0RA1RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm687: halts_at_trans (TM_from_str "1RB0LA_1RC1RD_1LB1RA_---0RE_1LF0RC_1LA---") c0 (D,0).
Proof. solve_halt' 228 1000000 false 0%N (10^9)%N. Time Qed.

Lemma tm689: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA0LD_1LC0LD_0RD0RF_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm690: halts_at_trans (TM_from_str "1RB1LE_1LC0RD_1LA0LB_1RB0RD_0LD0LF_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm691: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_1LA0LC_1LE---_0RA1RF_1RE0RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm692: halts_at_trans (TM_from_str "1RB0LF_1RC0RF_1LD0RF_0RA0LE_0LD0LC_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm693: halts_at_trans (TM_from_str "1RB0LC_1LC1LF_0RD0LB_1LB1RE_0RD1RD_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm694: halts_at_trans (TM_from_str "1RB1LF_1LC0RE_1RC0LD_1LA1LD_1RA1LA_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm695: halts_at_trans (TM_from_str "1RB---_1LB1RC_1RD0LC_0RE0RF_1RF1RA_0RB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm696: halts_at_trans (TM_from_str "1RB---_1LC0LF_1RD0RC_0RE1RB_1LF1LA_0LB1LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm697: halts_at_trans (TM_from_str "1RB0RD_1LC1RE_1LD0LC_1RA0LC_0RC0RF_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm699: halts_at_trans (TM_from_str "1RB0LD_1RC0RA_1LD1RE_1LA0LD_0RD0RF_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm700: halts_at_trans (TM_from_str "1RB0LC_1LA1RE_0LD0LB_1LB1LE_1LF0RB_---1LB") c0 (F,0).
Proof. solve_halt'' 14 false. Time Qed.

Lemma tm701: halts_at_trans (TM_from_str "1RB1LC_1RC---_1LD0RC_1LE1LD_0LF1LA_1RB0LA") c0 (B,1).
Proof. solve_halt'' 23 false. Time Qed.

Lemma tm702: halts_at_trans (TM_from_str "1RB1RF_1LC0RD_0LD0LC_1RE1LC_0RB1RA_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm703: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1LD0LC_0RA0LB_0RF---_1RD1LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm704: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1LD0LC_0RA0LB_0RF---_1RD1LD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm705: halts_at_trans (TM_from_str "1RB0LD_1LC0RE_---1LD_1LA0LE_0LF1LA_0RA0LB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm706: halts_at_trans (TM_from_str "1RB0LF_1RC0RD_1LD0RA_0LE0LC_0RB0LA_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm707: halts_at_trans (TM_from_str "1RB1LB_1RC0RD_0LD1RB_0RA1RE_1LF---_1LC0LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm708: halts_at_trans (TM_from_str "1RB0LD_1RC0RA_1LA1RE_1LA0LD_0RD0RF_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm709: halts_at_trans (TM_from_str "1RB0LB_1RC0LA_0LD0RE_1RF1LB_1RD---_1LB0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm710: halts_at_trans (TM_from_str "1RB0LD_1LC1RF_0RE1RD_1LE1LA_1RA1RE_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm711: halts_at_trans (TM_from_str "1RB1RF_1LC0LA_---1LD_1LE0LB_1LF0LB_0RA1RA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm712: halts_at_trans (TM_from_str "1RB1LC_1LA1LD_1LB0RC_---0LE_1RF0LA_1RF1RA") c0 (D,0).
Proof. solve_halt' 228 1000000 false 0%N (10^9)%N. Time Qed.

Lemma tm713: halts_at_trans (TM_from_str "1RB1RF_1LC0LA_---1LD_1LE0LB_1RF1RC_0RA1RA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm714: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_0RD---_1LE1RE_0LA0LE_0RE1LC") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm715: halts_at_trans (TM_from_str "1RB---_1RC1LD_1LD0RE_1RF0LE_1RD0LD_0LB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm716: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_0RD---_1LE1RE_0LA0LE_0RE1RE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm717: halts_at_trans (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm718: halts_at_trans (TM_from_str "1RB0LA_0LC1RD_1LB1LA_0RE---_1RF1RE_0RC0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm719: halts_at_trans (TM_from_str "1RB0RF_1LC0RF_0RE0LD_0LC0LB_1RA0LF_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm720: halts_at_trans (TM_from_str "1RB0RF_1LC0RD_0LD0LC_1RE1LC_0RB1RA_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm721: halts_at_trans (TM_from_str "1RB0LC_1LA1RE_1LD1LA_1RA1RD_0RF---_0RD1RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm722: halts_at_trans (TM_from_str "1RB1RF_1RC0LB_0RD0RE_1LD1LB_---1RF_0RC1RA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm723: halts_at_trans (TM_from_str "1RB1LF_0LC1LE_1LD1LC_1LA0RE_1RC1RD_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm724: halts_at_trans (TM_from_str "1RB0LC_1LC1RD_1LA0LC_1LE---_0RA1RF_1RE0RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm726: halts_at_trans (TM_from_str "1RB0LC_1LC1RD_1LA0LC_0RE---_1RF0RE_0RA1RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm727: halts_at_trans (TM_from_str "1RB0RE_1LC0LF_---1LD_1RA1LF_1RA1RE_0LA1LB") c0 (C,0).
Proof. solve_halt'' 12 false. Time Qed.

Lemma tm728: halts_at_trans (TM_from_str "1RB0LF_1LC0RF_0RE0LD_1LE---_1LA1RB_1LB0RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm729: halts_at_trans (TM_from_str "1RB1LE_1LC1RE_1LD0LC_0RA0LB_0RF---_1RD1LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm730: halts_at_trans (TM_from_str "1RB1RF_1LC0LA_---1LD_1LE0LB_1LF1RC_0RA1RA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm731: halts_at_trans (TM_from_str "1RB0RB_1LC0RC_1LE0RD_0RB1LA_0LA0LF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm732: halts_at_trans (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_0RF1RC_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm733: halts_at_trans (TM_from_str "1RB0LA_1RC1RD_1LB1RA_0LF0RE_1LF0RC_1LA---") c0 (F,1).
Proof. solve_halt' 228 1000000 false 0%N (10^9)%N. Time Qed.

Lemma tm734: halts_at_trans (TM_from_str "1RB0LA_1RC1RD_1LB1RA_0RF0RE_1LF0RC_1LA---") c0 (F,1).
Proof. solve_halt' 228 1000000 false 0%N (10^9)%N. Time Qed.

Lemma tm735: halts_at_trans (TM_from_str "1RB0LA_1RC1RD_1LB1RA_1LF0RE_1LF0RC_1LA---") c0 (F,1).
Proof. solve_halt' 228 1000000 false 0%N (10^9)%N. Time Qed.

Lemma tm736: halts_at_trans (TM_from_str "1RB0LA_1RC1RD_1LB1RA_1RF0RE_1LF0RC_1LA---") c0 (F,1).
Proof. solve_halt' 228 1000000 false 0%N (10^9)%N. Time Qed.

Lemma tm737: halts_at_trans (TM_from_str "1RB0LB_1LC0RA_---1LD_1RE1RF_1RA0RE_0LA0LF") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm738: halts_at_trans (TM_from_str "1RB0RA_1RC0LC_1LD0RB_---1LE_1RA1RF_0LB0LF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm739: halts_at_trans (TM_from_str "1RB0RB_1LC1RA_1LA1RD_1LE0LC_0LF0LD_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm740: halts_at_trans (TM_from_str "1RB---_1LC1RF_1LF1RD_1LE0LC_1LA0LD_1RB0RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm741: halts_at_trans (TM_from_str "1RB0RF_1LC---_1RE1LD_1LC0LC_1RD1LF_1RA0RE") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm742: halts_at_trans (TM_from_str "1RB1LD_1LC0LC_1RA1LB_1RE0RA_0RF0RD_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm743: halts_at_trans (TM_from_str "1RB1RF_1RC0RB_1RD0LD_1LE0RC_---1LA_0LC0LF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm744: halts_at_trans (TM_from_str "1RB0RA_0LC1RE_1LD1RC_---1LE_0LF0LA_1RF1LC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm745: halts_at_trans (TM_from_str "1RB0RF_1RC0LE_0RD0RB_1RE1RA_1LB0LC_1LB---") c0 (F,1).
Proof. solve_halt'' 24 false. Time Qed.

Lemma tm746: halts_at_trans (TM_from_str "1RB1RF_1RC0LE_0RD0RB_1RE1RA_1LB0LC_0RB---") c0 (F,1).
Proof. solve_halt'' 24 false. Time Qed.

Lemma tm747: halts_at_trans (TM_from_str "1RB0RA_1LC1RD_---1LD_0LE0LA_1RE1LF_1LC1RF") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm750: halts_at_trans (TM_from_str "1RB0LC_1RC0LD_1LD1RB_---0RE_1RA1LF_0LE0LA") c0 (D,0).
Proof. solve_halt'' 12 false. Time Qed.

Lemma tm754: halts_at_trans (TM_from_str "1RB0RE_1LC1RC_0RE0LD_1LC0LD_1RA1RF_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm755: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_1LD0LC_0RE0LC_1RA1RF_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm756: halts_at_trans (TM_from_str "1RB1LD_1RC0LE_1LC0LA_0LB1RE_1LF0RA_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm761: halts_at_trans (TM_from_str "1RB0LE_1LB0LC_1RA1LD_0LA1RE_1LF0RC_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm765: halts_at_trans (TM_from_str "1RB---_0RC1LF_1LD0RF_1RD0RE_1LC1RB_1RA0LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm770: halts_at_trans (TM_from_str "1RB0RC_1LC0RE_1RE0LD_0LB---_0RA1LF_0LF1LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm771: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD0RE_1LA0LB_1LD0RF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm748: halts_at_trans (TM_from_str "1RB1LE_1RC1RB_1LD0RB_0LF1LA_1RE0LD_---1LD") c0 (F,0).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm749: halts_at_trans (TM_from_str "1RB1RA_1LC0RA_0LF1LD_1RA1LE_1RE0LC_---1LC") c0 (F,0).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm751: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1RE_1LF---_0RA1RF") c0 (E,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm752: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_1LD---_0RA0LA") c0 (E,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm753: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1RE_0LA---_0RA0LA") c0 (E,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm757: halts_at_trans (TM_from_str "1RB1LE_1RC0RC_1RD0RB_1RE1RF_1LA0LE_---0RB") c0 (F,0).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm758: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1RE_0LA---_0RA0LD") c0 (E,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm759: halts_at_trans (TM_from_str "1RB1LE_1RC0RC_1RD0RB_1RE0RF_1LA0LE_---1LB") c0 (F,0).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm760: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1RE_0LA---_0RA1RF") c0 (E,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm762: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1RE_1RF---_0RA1RF") c0 (E,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm763: halts_at_trans (TM_from_str "1RB1RF_1RC0LE_0RD0RB_1RE1RA_1LB0LC_1LE---") c0 (F,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm764: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1RE_1RF---_0RA0LD") c0 (E,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm766: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_1LD---_0RA1RF") c0 (E,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm767: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1RE_1RF---_0RA0LA") c0 (E,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm768: halts_at_trans (TM_from_str "1RB---_1RC1RE_1LD0LD_0RE0LC_1RF0RA_0RB0LB") c0 (A,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm769: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_1RA---_0RA1RF") c0 (E,1).
Proof. solve_halt' 24 100000 false 0%N (10^10)%N. Time Qed.

Lemma tm698: halts_at_trans (TM_from_str "1RB0LC_1RC1RF_1LD1LA_0LA1LE_1RA0RA_1RE---") c0 (F,1).
Proof. solve_halt' 16 3200 false 0%N (10^10)%N. Time Qed.

