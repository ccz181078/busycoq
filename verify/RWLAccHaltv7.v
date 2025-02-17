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
    solve_halt' bsz 3200 use_acc 2%N (10^12)%N
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


Lemma tm1: halts_at_trans (TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC0RD_0LF---_0LB1LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB1LC_1LA0RF_0LD---_0LE0RE_0LB0RA_1RB0RF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB1LF_1LC0RE_1LA0LD_1RE---_0RB0LD_0LB0LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1LD0RA_0LA0LC_0LF---_1RC0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB---_0RC0RB_1LD1LA_0LE1LC_1LF0LE_1LB0LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB---_0RC1LD_1RD0LE_0RE0RC_1LF0RA_1LC0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB1RA_1LB0RC_1LF1RD_1RE0RA_1RC0LE_---1LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RA1LD_0LE---_0LF1LC_0LB1RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RA1LD_0LE---_0LF0RF_0LB0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB1LC_1LA0RF_0LD---_0LE0RE_0LB0RF_1RB0RF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LA_0LB0RF_1RB0RF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB1LC_1LA0RF_0LD---_0LE0RE_0LB1RE_1RB0RF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB1RF_1RC---_0RD0LC_1LE1RD_1LC0RA_1RE0RD") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB0LC_1RC0RF_1LD0RA_1RE1LC_---1RA_1LC1RD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB0RE_1RC0LB_1LD1RA_---1LB_1RF1RE_1LF0RC") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RA1LD_0LE---_0LF1LC_0LB0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB1LE_0LC1RB_1LA0RD_1RC0RD_0LF---_0LB1LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RF1LD_0LE---_0LF0RF_0LB1RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LA_0LB0RA_1RB0RF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RF1LD_0LE---_0LF0RF_0LB0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD1RD_0RA0LE_1LD0LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD1RE_1LE0LD_0RA0LD_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_0LD0LB_1RA0LE_0LF---_1RB0RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB1RF_0RC1RA_1RD0RC_1RE0RA_0LA0LE_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LC_0LB1RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RA1LD_0LE---_0LF0RF_0LB1RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1LD0RA_0LA0LC_1LF---_0LC1RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RE1LD_0LE---_0LF1LF_0LB1RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB0LC_0RC0LE_1RD1RF_0LB1RA_1LD0RA_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1RB0LD_1LC1RE_0RA1LC_1LA0LD_0RF---_0RC1RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RA1LD_0LE---_0LF1LF_0LB1RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB0LC_1LC1RD_1LA0LC_0RE---_0RF1RF_0RA1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_0RD1RD_0RA1LD_1LA0LE_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB---_1RC0RD_1LD0RE_0LF0LC_1RB1LA_0RB0LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_1LD0LB_1LE1LA_1RC0LD_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB0LC_1LC0LE_1LA1LD_1RE1LF_1LB0RD_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB1RD_1RC---_0LA0RC_1LE1RE_0RA0LF_1LC1LD") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB1RC_0RC0RB_1LD0RA_0LA0LE_1LD0LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB1LB_1LA1LC_1LE1RD_0RE0RC_1LA0LF_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB0RD_1RC1RE_1LA0RB_1RA0LE_1LD1RF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB0RC_1LC0LB_1RA1RD_1RC1LE_1LF0LD_---1LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB0LE_1RC1RA_1RD1RC_1LA0RB_1LF0LD_---1LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD0RE_1LA0LB_1LD1RF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.


