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

Definition sel_bsz tm := sel_bsz_0 tm 1%nat 12 (10^4)%N 1 N0.

Ltac solve_halt :=
  match goal with
  | |- halts_at_trans (?tm) c0 _ =>
    solve_halt'' (sel_bsz tm) true
  end.


Lemma tm1: halts_at_trans (TM_from_str "1RB1RE_0LC1RA_---1LD_0LE1RE_0RA1LF_1LC0LA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB0LD_1RC0RA_1LA1RE_1RE0LE_1RA0RF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB0RF_1RC0LA_1LD0RA_1LB0LE_0LD0LB_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB0RD_1LC0RE_1LD0LC_1RA0LB_1RB1RF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB0LE_1RC0LD_1RD1RE_0LA0RF_1LA0LC_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB1RC_1LC1RB_1LD0RA_1LE0LC_1LA0LF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB1RE_1LC0LB_1LD1LC_0RA0LB_---1LF_1RD1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RB0RE_1RF0RC_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB0RE_1LC1LB_1RA0LD_1RA1LF_---0RF_0LC0RB") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB1LC_0RC0LD_1RD1RF_1LE0LD_1LB1LE_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB0RE_1LC1RB_1RA1LD_1LE0LC_0RF1RC_---1RA") c0 (F,0).
Proof. solve_halt' 60 10000 true 2%N (10^8)%N. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB0LD_0RC0RB_1RD0LA_1LA0LE_0LA1LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA0LD_1RE0LE_1RC0RF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB0RF_0LC1LF_---1LD_1LE0LB_1RF1LE_1LD1RA") c0 (C,0).
Proof. solve_halt' 60 10000 true 2%N (10^8)%N. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB1LD_0RC0RE_1LC0LA_1LE0LA_0RF1RA_---1RB") c0 (F,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0LA0LE_1LC1LA_---1LF_1RB1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB0RF_1LC1LB_1RD1LA_1LA0RE_1RA0RB_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB1RA_1RC0LD_0LB1RE_1LB1LD_---1RF_1RA0RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB0RE_1RC1RA_1LD0RB_1RE1LD_1RF0LE_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB---_0RC0LC_0RD1LF_1LE0RA_1LA1RB_1RE0LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB1RE_1LC0LB_1LD1LC_0RA0LB_---1RF_1RD1LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB1RA_0RC0LD_1RD1RF_1LE0LD_1LB1LE_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1LD0RA_1LA0LC_1LA1LF_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB---_0RC0LC_0RD0LF_1LE0RA_1LA0LB_1RA1RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB1LD_1RC0RE_1LA1RC_1LE0LA_0RF1RA_---1RB") c0 (F,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB0LA_0LB1RC_1RD---_1RE0RA_1LF0RD_1RA0LE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB0RF_1LC1LB_1RA0LD_0RE1LE_0LC0RB_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1RB0RE_1RC0RF_1LD1LE_1RE1LD_1RA0LC_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB0LE_1RC0LD_0LB1RE_1LB1LD_---1RF_1RA0RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1RB0RF_1LC1LB_1RD1LA_0LC0RE_1RA0RB_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm46: halts_at_trans (TM_from_str "1RB0RE_1LC0LF_1RA1LD_1LE0LC_0RF1RC_---1RA") c0 (F,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm49: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD0LC_1LB0RE_1RA0RB_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm51: halts_at_trans (TM_from_str "1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm52: halts_at_trans (TM_from_str "1RB0LA_1RC1RB_1RD0RF_1LE0RC_1RA0LD_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm53: halts_at_trans (TM_from_str "1RB---_1RC0RF_1RD1RB_1LE0RC_1RF1LE_1RA0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm56: halts_at_trans (TM_from_str "1RB1LD_0RC0RE_1LD0LA_1LE0LA_0RF1RA_---1RB") c0 (F,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm57: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_1LA0RD_1LC0LE_1LA---_0RB0RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm59: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD1LA_---0RE_1RA0RB_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm60: halts_at_trans (TM_from_str "1RB---_1RC0RE_1LD0RB_1RE0LC_1RF0LE_1RB1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm62: halts_at_trans (TM_from_str "1RB0RF_0LC1LF_---1LD_1RE0LB_1RF1LE_1LD1RA") c0 (C,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm64: halts_at_trans (TM_from_str "1RB0LD_1RC1LB_1LA1RE_0LF1LC_1RD0RC_---1LA") c0 (F,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm65: halts_at_trans (TM_from_str "1RB1LD_1LC0RE_1LA1RC_1LE0LA_0RF1RA_---1RB") c0 (F,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm66: halts_at_trans (TM_from_str "1RB0RE_1LC1LB_1RA1LD_1RB1RF_1RD0RB_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm67: halts_at_trans (TM_from_str "1RB0RC_1LC---_0LD0RD_0LF0RE_1LB1LF_1RA0LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm69: halts_at_trans (TM_from_str "1RB1LC_1LC---_0LD0RD_0LF1RE_1LA0RC_1RA0LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm71: halts_at_trans (TM_from_str "1RB1RE_1LC0LB_1LD1LC_0RA0LB_---1RF_1RD1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm72: halts_at_trans (TM_from_str "1RB0RE_1LC0RD_0LD1LB_0RA0LE_1RD0LF_1LC---") c0 (F,1).
Proof. solve_halt'' 12 true. Time Qed.

Lemma tm74: halts_at_trans (TM_from_str "1RB1RA_0RC0LD_1RD1RF_1LE0LD_1LB1LE_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm76: halts_at_trans (TM_from_str "1RB0RC_1LC0RA_0LD0LB_1RE0LD_1RF---_1RB0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm77: halts_at_trans (TM_from_str "1RB1RA_1RC0RB_0LD0LF_1RB1LE_1LC1LD_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm79: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1LD0RC_1LE0LF_1LA1LC_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm80: halts_at_trans (TM_from_str "1RB0RF_0LC1LF_---1LD_1LE0LB_1RF0RC_1LD1RA") c0 (C,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm81: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LA0LE_1LF0LA_---1RB_0RE1RA") c0 (E,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm82: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm83: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1LD0RC_1LE1LD_1LA0LF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm86: halts_at_trans (TM_from_str "1RB0RF_0LC1LF_---1LD_0LE0LB_1RA0RF_1LD1RA") c0 (C,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm87: halts_at_trans (TM_from_str "1RB0LA_1RC0RF_1RD0RA_1LE0RC_1RA0LD_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm88: halts_at_trans (TM_from_str "1RB0LD_1RC0RA_1RD0RF_1LE1LA_1RA1LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm89: halts_at_trans (TM_from_str "1RB0RE_1RC1RA_1LD0RB_1RE1LD_0RF0LE_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm91: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0LA0LE_1LC1LA_---1LF_0RD1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm93: halts_at_trans (TM_from_str "1RB---_0LC0LB_1LE0RD_1LB0RE_1RD0RF_0RD1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm94: halts_at_trans (TM_from_str "1RB0RF_0LC1LF_---1LD_0LE0LB_1RE0RF_1LD1RA") c0 (C,0).
Proof. solve_halt' 60 20000 true 2%N (10^8)%N. Time Qed.

Lemma tm96: halts_at_trans (TM_from_str "1RB0RE_1LC0RD_1RA0LD_1LB0LF_0RA0RB_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm97: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm100: halts_at_trans (TM_from_str "1RB1RE_1RC1LB_1LD0RA_0LE0LD_1RF0LB_1RA---") c0 (F,1).
Proof. solve_halt'' 6 true. Time Qed.

Lemma tm101: halts_at_trans (TM_from_str "1RB0LE_1LC0LC_0LD1LB_1RE0LF_1RA0RD_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm102: halts_at_trans (TM_from_str "1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm103: halts_at_trans (TM_from_str "1RB0LB_1RC0RF_1RD0LA_1RE0RC_1LC1RB_1LE---") c0 (F,1).
Proof. solve_halt'' 30 true. Time Qed.

Lemma tm104: halts_at_trans (TM_from_str "1RB1RE_1RC---_0RD0LD_0RE0LA_1LF0RB_1LB0LC") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm105: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_---1LD_1LE0LA_1LA0LE_0LB1RA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm107: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LC_1LA0RB_0RB1RF_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm108: halts_at_trans (TM_from_str "1RB0RE_1LC0RF_0LD0LB_1RE0LD_1RA---_1RB1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm110: halts_at_trans (TM_from_str "1RB0LF_1RC0RB_1LD0RA_0LE0LC_1RA1LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm111: halts_at_trans (TM_from_str "1RB1RD_1LC1RF_1RA0LD_1RC0LE_0RB1LC_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm112: halts_at_trans (TM_from_str "1RB1LC_1LA0RE_1RD1RF_1LA1LD_1RC0RD_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm113: halts_at_trans (TM_from_str "1RB0RE_1RC0LA_1LD0LD_0LE1LC_1RA0LF_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm114: halts_at_trans (TM_from_str "1RB0RB_0RC1RA_1LD0RF_1LE0LC_1LA0RD_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm115: halts_at_trans (TM_from_str "1RB---_1RC1LF_1LD0RE_1LB0LC_1LF0RF_1LC0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm116: halts_at_trans (TM_from_str "1RB1RC_1LC1LB_1RE0LD_1RA1LA_---0RF_1RA0RB") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm117: halts_at_trans (TM_from_str "1RB1RF_1LC0RA_1LD0LC_1RE0LB_1RB0RD_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm119: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD1LA_---0RE_1RA0RB_0RC0LC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm120: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD1LA_---0RE_1RA0RB_1RC0LC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm121: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD1LA_---0RE_1RA0RB_0RD0LC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm122: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD1LA_---0RE_1RA0RB_1RD0LC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm123: halts_at_trans (TM_from_str "1RB1RF_1LC1LB_1RD1LA_---0RE_1RA0RB_0RF0LC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm124: halts_at_trans (TM_from_str "1RB1RA_1LC0RE_0LF1LD_1LA1LC_1RA1RB_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm125: halts_at_trans (TM_from_str "1RB1LC_1LA1RC_1RD0LA_0RF0RE_0RB1LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm126: halts_at_trans (TM_from_str "1RB0RA_1LC0LC_0LF0RD_1RA1LE_0LB---_1LD1RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm127: halts_at_trans (TM_from_str "1RB0RA_1RC0RB_1LD0RA_1LE0LC_0LA0LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm128: halts_at_trans (TM_from_str "1RB0RC_1LC0RA_0LE1LD_1LE0LF_0RD0LB_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm129: halts_at_trans (TM_from_str "1RB1RF_0LC---_1LD0RD_1LE0LB_0RA1LC_0RC0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm130: halts_at_trans (TM_from_str "1RB0LF_0RC0RB_1LC0LD_1LE0RA_1LA0LD_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm131: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LC0LD_1LE0RA_1LA0LD_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm132: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1RE0LD_1LB1LC_0RF1RA_---0RA") c0 (F,0).
Proof. solve_halt'' 6 true. Time Qed.

Lemma tm133: halts_at_trans (TM_from_str "1RB---_0RC1RE_1LD1RA_0RE0LF_1RC0RD_1LE1LD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm134: halts_at_trans (TM_from_str "1RB0LE_0RC---_0LD0RF_1LA0LF_1LF1LD_0LA1LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm135: halts_at_trans (TM_from_str "1RB1RF_1RC1RB_1LD0RA_1RC1LE_0LC1LC_---0LD") c0 (F,0).
Proof. solve_halt'' 21 true. Time Qed.

Lemma tm136: halts_at_trans (TM_from_str "1RB0LC_1LA1RE_1LD1LF_1LA1LD_0RA1RA_---0RB") c0 (F,0).
Proof. solve_halt'' 21 true. Time Qed.

Lemma tm137: halts_at_trans (TM_from_str "1RB1RA_1LC0RE_1RB1LD_0LB1LB_1RA1RF_---0LC") c0 (F,0).
Proof. solve_halt'' 21 true. Time Qed.

Lemma tm138: halts_at_trans (TM_from_str "1RB0LB_1RC0LA_0RD---_1LE0RF_1LA1LA_0RA1RD") c0 (C,1).
Proof. solve_halt'' 36 true. Time Qed.

Lemma tm139: halts_at_trans (TM_from_str "1RB1LA_1RC1RE_1LD1RC_0LC0LA_1RF0RC_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm140: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_1LC0LD_1RA1LD_1RF0RB_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm141: halts_at_trans (TM_from_str "1RB1LA_1RC1RE_1LD1RC_1LD0LA_1RF0RC_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm142: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_0LB0LD_1RA1LD_1RF0RB_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm143: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RF1RB_---0RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm144: halts_at_trans (TM_from_str "1RB0RD_1RC1RA_1LD1LA_0RE0LC_1RC1RF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm145: halts_at_trans (TM_from_str "1RB0RD_1RC1RA_1LD1LA_0RE0LC_0LF1RF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm146: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE1LF_1RA1LB_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm147: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE0LF_1RA1LB_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm148: halts_at_trans (TM_from_str "1RB0LD_0RC0RB_1RD0LA_1LA0LE_1LB1LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm149: halts_at_trans (TM_from_str "1RB0RD_1RC0RA_1LC1LD_1LA0LE_1LA1LF_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm150: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LC_1LA0RB_1RC1RF_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm151: halts_at_trans (TM_from_str "1RB1RA_0RC1RF_1RD1RA_1LE0LD_1LB0RF_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm152: halts_at_trans (TM_from_str "1RB1RA_0RC1RF_1RD1RA_1LE0LD_1LB1LE_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm153: halts_at_trans (TM_from_str "1RB0LC_0RC1RE_1LD0RF_1LA0RB_1RD1RA_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

