From BusyCoq Require Import RWLAcc25.

Open Scope list.

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



Lemma tm1: halts_at_trans (TM_from_str "1RB3LA4RA4LA2LA_2LA3LA3LB2RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB3RB4LA4RA3LA_2LA2RB3RB2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB1LA2LA---2RA_2LA3LB4RB1RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB3RB1RA---2LB_2LA2LB4RB4LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB2LA2LB3RA---_1LA2RA3LB4RB3LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB3LA3LA2RA1RA_1LB2LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB2LA1RA1RA4LB_1LB1LA3RB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB0LB4RA4RA0LB_2LA0RA3RB---0LA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB0LB2LA---3LB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB4RA4LB4LA3RA_2LB3LA---4LA1RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB2RB2RB3LA---_2LA4RB3RB2LB0LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RA_2LA1LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB0RB3LA4LA3RA_2LA3RB1LB---4RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB2RA4RA4LA2LA_2LB3LA1RB4LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB3RB0RB3LA---_2LA4RB3RB2LB2RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB2RB1LA4LA2RA_2LA2RA3LB---0RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA3LB1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB3LA3LA1RA1RA_2LB2LA3LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB3RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB3LA4RB---0LA_2LA0LB4RA4LB2LB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB3LA3LA2RA1RA_2LB1LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB3LA---1RB4RA_2LA4LB1RA1LB1RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA1LB1RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB3LA1LB1RA3RA_2LB1LA0RA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB2LB3RB---4RA_1LA3RA1LB4LB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB3RB4LA4RA3LA_2LA---3LB2RB3RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB3LA1LA1RA---_2LA4LA3LB4LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA4RB4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB2LA1RA---0RA_0LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB4RA---0LA1LA_2LB3RB0RB4RB4LA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB1LA2LB---3RA_2LA3RA4LB4RB2RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB4LA4LA4RA1RA_1LB2LA3RA---3RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB3LB4RA2LA1RB_2LA---3RB2RA3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB4LA3LA1RA1LB_2LB1RA---1LB3RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB3LB3RA2LA3LA_2LA---2RB4LB2RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB2RA3LA4LA3RA_2LB2RA---1RB4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1RB3RB2LB4RB4LB_2LA---3LA3RB2RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB3LB---1LA1LA_2LA4RB3LB4RA3LB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB1RA1LB0RA3RA_2LA3RB4RA3LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB3LA2LB---3RA_2LA3RA4LB4RB2RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1RB3RA2RB1LA1RA_2LA4RA3LB2RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB3LA3LA2RA2RA_2LB2LA3LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1RB0LA---1RA0LA_2LB3RB0RB4RB3LA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1RB0RB3LA2RA---_2LA4RB3RB2LB1RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm45: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA2LB1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm46: halts_at_trans (TM_from_str "1RB3LA3LA1RA3RA_2LB1LA---4RB4LB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm47: halts_at_trans (TM_from_str "1RB3LA1LB1RA3RA_2LB3LA3RA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm48: halts_at_trans (TM_from_str "1RB2LB3LA4RB2LB_1LA2RB1LB0RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm49: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA4RA4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm50: halts_at_trans (TM_from_str "1RB1LB0RB2LA---_2LA2RB3RB4RA0LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm51: halts_at_trans (TM_from_str "1RB4LA4LB1LA1RA_2LB3RA---3LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm52: halts_at_trans (TM_from_str "1RB3LA4LA1RA1LA_2LA---4RA3RB1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm53: halts_at_trans (TM_from_str "1RB1LA2RB4LA---_2LA2RA3RB2LB2LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm54: halts_at_trans (TM_from_str "1RB2RB1RA3LA---_2LA4RB3RB2LB0LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm55: halts_at_trans (TM_from_str "1RB2LB1RA4LA2LB_2LA2LA3RB---2RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm56: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB2LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm57: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RB_2LA2LA1LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm58: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_1LB2RB2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm59: halts_at_trans (TM_from_str "1RB1LA3RA2LB4LB_0LA2RA4RB---0RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm60: halts_at_trans (TM_from_str "1RB2RB3LA2RA3LB_1LA3RB---4RB2RA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm61: halts_at_trans (TM_from_str "1RB2LB2LA0RB---_2LA4RB3LB2RB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm62: halts_at_trans (TM_from_str "1RB3LA4LA1RA1RA_2LB1LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm63: halts_at_trans (TM_from_str "1RB3LA3LA1RA1RA_2LB1LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm64: halts_at_trans (TM_from_str "1RB4LA3LB4LA---_2LB1RA2RA1LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm65: halts_at_trans (TM_from_str "1RB0RB2LA---3LB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm66: halts_at_trans (TM_from_str "1RB2LA3LA2RA---_2LA3RB0LB4RB1LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm67: halts_at_trans (TM_from_str "1RB0RB4RA2LB2LA_2LA1LB3RB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm68: halts_at_trans (TM_from_str "1RB3LB1LB---3RA_2LA4LB4RB0LB1RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm69: halts_at_trans (TM_from_str "1RB3LB4LB4LA2RA_2LA---3RB4RA3RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm70: halts_at_trans (TM_from_str "1RB3RA4LA1LA1LB_2LA4RB---1LA3RA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm71: halts_at_trans (TM_from_str "1RB3LA3LA1RA2RA_2LB2LA3LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm72: halts_at_trans (TM_from_str "1RB2RA2RB3LA---_2LA4RA3RB2LB3RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm73: halts_at_trans (TM_from_str "1RB3LA4LB1RA3RB_2LB1LA1LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm74: halts_at_trans (TM_from_str "1RB2RA1LA1RB---_2LA3LB4RB1RB1LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm75: halts_at_trans (TM_from_str "1RB0LB2LA---4RB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm76: halts_at_trans (TM_from_str "1RB2LA1RA0RB---_2LA4RB3LB2RB3RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm77: halts_at_trans (TM_from_str "1RB4LA3LA1RA1RA_1LB2LA3RA---4RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm78: halts_at_trans (TM_from_str "1RB2LB4RB4RA3LA_2LA2RB3RB2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm79: halts_at_trans (TM_from_str "1RB3RA3LB4LA3RA_2LB3RA---3LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm80: halts_at_trans (TM_from_str "1RB3LA3LA1RA1RA_2LB1LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm81: halts_at_trans (TM_from_str "1RB2LB4RA2RA2LA_2LA---3RB3RA4LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm82: halts_at_trans (TM_from_str "1RB2LA1RA4LB---_2LB2RB3RB1LA1RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm83: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA2LB1RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm84: halts_at_trans (TM_from_str "1RB2LB3RA2LA2LB_1LA2RA4RA3LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm85: halts_at_trans (TM_from_str "1RB3LA1RA4LA1RA_2LA---1LA2RB0LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm86: halts_at_trans (TM_from_str "1RB3LA3LA1RA2RA_2LB2LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm87: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA1RB4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm88: halts_at_trans (TM_from_str "1RB3LA1LB0LB1RA_2LA4LB4LA1RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm89: halts_at_trans (TM_from_str "1RB3RB1LB---4LB_2LA3RA4RB2RA2LB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm90: halts_at_trans (TM_from_str "1RB3RB---2LA3LA_2LA2RB4RB4LB2LB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm91: halts_at_trans (TM_from_str "1RB2LA1RA1RA0LB_1LB1LA3RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm92: halts_at_trans (TM_from_str "1RB4LA1LA4RA1RA_2LB2LA3RA---3RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm93: halts_at_trans (TM_from_str "1RB2RB3LB---4LA_2LA3RB3LA4RB3LB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm94: halts_at_trans (TM_from_str "1RB3LA4LA1RA1RA_2LA3RB1RB1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm95: halts_at_trans (TM_from_str "1RB3LA1RA0LA0LB_2LA4RB1RA4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm96: halts_at_trans (TM_from_str "1RB0RA4LA4RA2RA_2LB2LA3LA---3RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm97: halts_at_trans (TM_from_str "1RB2LA1RA1RA0RA_1LB1LA3RB4LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm98: halts_at_trans (TM_from_str "1RB1LA---4LA1LB_2LA3RB3LA1LB3RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm99: halts_at_trans (TM_from_str "1RB3LB3LA2LA---_2LA4LA1RA4LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm100: halts_at_trans (TM_from_str "1RB0RB4RA4LA2LA_2LA3LA3LB2RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm101: halts_at_trans (TM_from_str "1RB2RB3LA4LA1LA_2LB3RA---4RA2RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm102: halts_at_trans (TM_from_str "1RB2RB3LA2RA---_1LA3RB4RB1LB2LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm103: halts_at_trans (TM_from_str "1RB3LB3RA4RB2LA_2LA---4RB0RA1LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm104: halts_at_trans (TM_from_str "1RB3RB4LA0LA0LB_2LA---2RB1LA3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm105: halts_at_trans (TM_from_str "1RB3LA0LB1RA---_2LA1RA4LA2RB3RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm106: halts_at_trans (TM_from_str "1RB3RA4RB3LA0LB_2LA2RB3RB2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm107: halts_at_trans (TM_from_str "1RB3LB4LA---4RA_2LA2RA2LB4LB0LB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm108: halts_at_trans (TM_from_str "1RB3LA1LA1RA1RA_2LB3LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm109: halts_at_trans (TM_from_str "1RB3RB---1LA1LA_2LB3RB4LB2LA4RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm110: halts_at_trans (TM_from_str "1RB2RB3LB4LA2RA_2LA---3RB4LA4RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm111: halts_at_trans (TM_from_str "1RB3LA1LB1RA1LA_2LA4LA4RB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm112: halts_at_trans (TM_from_str "1RB2LA1RA4RB---_2LA4RA3LB2RB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm113: halts_at_trans (TM_from_str "1RB3LB4RA1LA---_2LA3RA1RB0LB2LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm114: halts_at_trans (TM_from_str "1RB2RA1LA3RB---_2LA3LB4RB1RB3RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm115: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA2LA4RB2LB1RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm116: halts_at_trans (TM_from_str "1RB3RA4LB4RA3LA_2LB3LA---3RA2LA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm117: halts_at_trans (TM_from_str "1RB3LA4LA1RA3LA_2LA3RB3RB1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm118: halts_at_trans (TM_from_str "1RB3LA4LA1RA1RA_1LB2LA3RA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm119: halts_at_trans (TM_from_str "1RB3LA4LA1RA3LA_2LA3RB1LA1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm120: halts_at_trans (TM_from_str "1RB2LA4RA4RA2LA_1LB1LA3RB4LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm121: halts_at_trans (TM_from_str "1RB3LA4LA1RA1LA_2LA---3LA3RB4LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm122: halts_at_trans (TM_from_str "1RB3LA2LB1RA1LA_2LA0LA4RA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm123: halts_at_trans (TM_from_str "1RB3LB---0RB1LA_2LA4RB1RA0LB1LB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm124: halts_at_trans (TM_from_str "1RB3LA4LB1RA1LB_2LA2RA4LA3RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm125: halts_at_trans (TM_from_str "1RB4LA3LA4LA---_2LB3RA2RA1LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm126: halts_at_trans (TM_from_str "1RB2RB4LA2LA2RA_1LA3LA---2LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm127: halts_at_trans (TM_from_str "1RB3LA---4LA3LB_2LA0LB4RA1RB1RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm128: halts_at_trans (TM_from_str "1RB1LA---4LA1LB_2LA3RB4LA1LB4RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm129: halts_at_trans (TM_from_str "1RB2LB2RB4LA---_1LA3RA3LB0LB0LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm130: halts_at_trans (TM_from_str "1RB2LA3LB2RA---_2LA3LA3LB4RB2RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm131: halts_at_trans (TM_from_str "1RB3RB2LA3LA---_2LA4RB3LB2RB1RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm132: halts_at_trans (TM_from_str "1RB1LA---4LA1LB_2LA3RB4LA4RA4RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm133: halts_at_trans (TM_from_str "1RB3LA---4RB0LA_1LB2LA3RB4RA3RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm134: halts_at_trans (TM_from_str "1RB3LA4LA---3LB_2LA0RB3LB2RB2RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm135: halts_at_trans (TM_from_str "1RB2RB4LA3RA2RA_2LA3RA3LB1LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm136: halts_at_trans (TM_from_str "1RB3LB1RB4RA3LA_2LA---3RB3RA4LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm137: halts_at_trans (TM_from_str "1RB3LA3LA2RA2RA_1LB2LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm138: halts_at_trans (TM_from_str "1RB2LB4RA1LA2LB_2LA2RB3RB---2LA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm139: halts_at_trans (TM_from_str "1RB4RA0RB---1LA_2LB1RB3RB4LB4LA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm140: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA---1LB1RA3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm141: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA---2LB1RA3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm142: halts_at_trans (TM_from_str "1RB2LA4LA2RB2RA_1LB1LA3RB---1RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm143: halts_at_trans (TM_from_str "1RB4LA3LA4LA---_2LB1RA4LB1LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm144: halts_at_trans (TM_from_str "1RB3LB3LA1RA---_2LA2RB4RA2RB1RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm145: halts_at_trans (TM_from_str "1RB3RA3LA4LA3RA_2LB2RA---2LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm146: halts_at_trans (TM_from_str "1RB2LB4RB0LB---_2LA4RA3RB2LB2RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm147: halts_at_trans (TM_from_str "1RB2RA1LB1RA---_2LA3RB3LA4RA2LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm148: halts_at_trans (TM_from_str "1RB3LA4LA4RA3LA_2LA3RB1LA1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm149: halts_at_trans (TM_from_str "1RB3LA4LA1RA3RB_2LB1LA1LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm150: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB4LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm151: halts_at_trans (TM_from_str "1RB2RB4LA1LA2RA_2LA---3LA4LA4RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm152: halts_at_trans (TM_from_str "1RB3LA0LA1RA3RA_2LB1LA---4RB4RA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm153: halts_at_trans (TM_from_str "1RB2LA1RA4LA2RA_1LB1LA3RB---2RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm154: halts_at_trans (TM_from_str "1RB2RB3RB4LA3RA_0LA4RB---0RB1LB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm155: halts_at_trans (TM_from_str "1RB3LA4RA2RB0LB_2LA---3LA3RB2LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm156: halts_at_trans (TM_from_str "1RB3LA1LA0RA3RB_2LA2RA4LA0LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm157: halts_at_trans (TM_from_str "1RB2LB4RA2RA2LA_2LA---3RB0RB4LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm158: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA---2LB4RB4LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm159: halts_at_trans (TM_from_str "1RB3RA3LB4LA1LB_2LA3RA1RB1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm160: halts_at_trans (TM_from_str "1RB4RB0LB4LA3RA_2LB3LA---1LA1RA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm161: halts_at_trans (TM_from_str "1RB4LA1LA2LA1RA_2LB3RB2LA---4RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm162: halts_at_trans (TM_from_str "1RB2LA3LA2RA2RA_1LB1RA2RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm163: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_0LA4RB3LB4LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm164: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA---1LB4RB0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm165: halts_at_trans (TM_from_str "1RB2LB2LA3LA---_2LA4RB3LB2RB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm166: halts_at_trans (TM_from_str "1RB3LA3LA1RA2RA_2LB1LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm167: halts_at_trans (TM_from_str "1RB3RB---3LA1LB_2LA4RB1LA4LA4RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm168: halts_at_trans (TM_from_str "1RB3LB4RA2LA1RB_2LA---3RB2RB3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm169: halts_at_trans (TM_from_str "1RB3LA3LA1RA2RA_1LB2LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm170: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA0LB1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm171: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RB_2LA3RB1RB1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm172: halts_at_trans (TM_from_str "1RB3LA4RA0LA0RB_2LA2LB3RA3LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm173: halts_at_trans (TM_from_str "1RB2LA3RA4LA1LB_0LA3RB2RA4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm174: halts_at_trans (TM_from_str "1RB3LB3LB4RA3LA_2LA---3RB3RA4LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm175: halts_at_trans (TM_from_str "1RB3LA3LA2RA1RA_2LB2LA3LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm176: halts_at_trans (TM_from_str "1RB3LA0RB1RA---_2LB1LA4LB3RB1RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm177: halts_at_trans (TM_from_str "1RB3LA3RA4LB2LB_2LA---2RB0RA0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm178: halts_at_trans (TM_from_str "1RB2RA4RA4LA2LA_2LB3LA1RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm179: halts_at_trans (TM_from_str "1RB3LA1LB1RA3RA_2LB3LA3LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm180: halts_at_trans (TM_from_str "1RB0RB3LA2RA---_2LA4RB3RB2LB2LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm181: halts_at_trans (TM_from_str "1RB3RA4LA1LA3RB_2LA4RB---2RA3LA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm182: halts_at_trans (TM_from_str "1RB3LA4RB4LB0LA_2LA---4RA2RA3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm183: halts_at_trans (TM_from_str "1RB3LA4LA---3LB_2LA3LA3LB2RB2RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm184: halts_at_trans (TM_from_str "1RB3RA4LA4RA3LA_2LB3LA4LB1RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm185: halts_at_trans (TM_from_str "1RB2RA1LA4RB---_2LA3LB3LA1RB2RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm186: halts_at_trans (TM_from_str "1RB4RA3LA4LA3RA_2LB2RA---2LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm187: halts_at_trans (TM_from_str "1RB0RB3LA2RA3LB_2LA---3RB4RB2RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm188: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA---3LB4RB1RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm189: halts_at_trans (TM_from_str "1RB3LA4LA1RA1LA_2LA---3LA3RB1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm190: halts_at_trans (TM_from_str "1RB3RA4LA1LA3LA_2LA4LB4RB---1RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm191: halts_at_trans (TM_from_str "1RB3RA3LB1LB1LA_2LA4RB4RA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm192: halts_at_trans (TM_from_str "1RB3LA4LB1RA0LA_2LB1LA3RA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm193: halts_at_trans (TM_from_str "1RB4RB---1LA1LA_2LB3RB4LB2LA3RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm194: halts_at_trans (TM_from_str "1RB3RA3RB1LA1LB_2LA4RB2LA---3RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm195: halts_at_trans (TM_from_str "1RB2RA1LA1LB3LB_2LA3RB---4RA1LA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm196: halts_at_trans (TM_from_str "1RB1LA---4LA1LB_2LA3RB3LA4RA3RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm197: halts_at_trans (TM_from_str "1RB3LA---3LB1LA_2LA3RA4LA4RB3LB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm198: halts_at_trans (TM_from_str "1RB3LA3LB0LB1RA_2LA4LB4LA1RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm199: halts_at_trans (TM_from_str "1RB2LB3RA2LA3LA_2LA1RA0LB4LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm200: halts_at_trans (TM_from_str "1RB4LA3LA0RA3LA_2LB1RA---1LB3RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm201: halts_at_trans (TM_from_str "1RB3LA0RB1RA1LB_2LB1LA4RA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm202: halts_at_trans (TM_from_str "1RB2LA1RA2LB3RA_0LA2RB3RB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm203: halts_at_trans (TM_from_str "1RB2LB3RA2LA2LA_1LA2RB2RA4LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm204: halts_at_trans (TM_from_str "1RB3RA3LA4LA3RA_2LB1LA---3LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm205: halts_at_trans (TM_from_str "1RB3LB3LB---0RA_2LA3RA4RB2RB0LB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm206: halts_at_trans (TM_from_str "1RB3RB4LA3LA---_2LA4RB3RB2LB2RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm207: halts_at_trans (TM_from_str "1RB4RA4LA4LA2RA_2LB3LA---4LA1RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm208: halts_at_trans (TM_from_str "1RB0RA3LB3RA1RA_2LA1LB4RA1RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm209: halts_at_trans (TM_from_str "1RB2LB---3LA4LB_2LA4RB3RB2LB2RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm210: halts_at_trans (TM_from_str "1RB2RB4RB1LA3RA_2LA3RB1LB0LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm211: halts_at_trans (TM_from_str "1RB3RA1LB---3LA_2LA2RB4RB4LB2LB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm212: halts_at_trans (TM_from_str "1RB3RA4LA1LA2RB_2LA2LB1RB---3RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm213: halts_at_trans (TM_from_str "1RB3LA4RB4LB0LA_2LA---4RA2RA2LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm214: halts_at_trans (TM_from_str "1RB3RB2LA4LA4LA_2LA2RB4RB---2LB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm215: halts_at_trans (TM_from_str "1RB3LA3RA4LA0LA_2LA4LB2RA2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm216: halts_at_trans (TM_from_str "1RB3LA4LB1RA3LB_2LA1LA4LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm217: halts_at_trans (TM_from_str "1RB1LA4RB2LA3LA_2LA3LB0RA0LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm218: halts_at_trans (TM_from_str "1RB3RA3LB4LA1LB_2LA3RA1RA1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm219: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB4RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm220: halts_at_trans (TM_from_str "1RB3LA4RB1RA0LA_2LA1LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm221: halts_at_trans (TM_from_str "1RB2LA1RA1RA4LB_1LB1LA3RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm222: halts_at_trans (TM_from_str "1RB2LA---4LA1LB_0LA3RB3RB4RA3RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm223: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB4RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm224: halts_at_trans (TM_from_str "1RB3RB4LA3LA0RB_1LB2RA---0LA0RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm225: halts_at_trans (TM_from_str "1RB2RA1LA3LA2RA_2LA3RB4LA1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm226: halts_at_trans (TM_from_str "1RB3LA2LA---3LB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm227: halts_at_trans (TM_from_str "1RB3RA4LB1LA---_2LA1LA3LB2RB2LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm228: halts_at_trans (TM_from_str "1RB2LA1RA1RA4LB_1LB1LA3RB4LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm229: halts_at_trans (TM_from_str "1RB4RB3RA0RB4LA_1LB2LA3RA---0LA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm230: halts_at_trans (TM_from_str "1RB3LB4RA0LA0LB_2LA---3RB2RA4LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm231: halts_at_trans (TM_from_str "1RB2LA3LA2RA---_2LA4RB3RB2LB2RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm232: halts_at_trans (TM_from_str "1RB4RA4LB4RA1LA_2LB3RB2LA---4LA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm233: halts_at_trans (TM_from_str "1RB2LB4RA2RA2LA_2LA---3RB2RA4LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm234: halts_at_trans (TM_from_str "1RB2RB1LB3LA---_2LA4RB3RB2LB0LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm235: halts_at_trans (TM_from_str "1RB3LA4LB1RA---_2LA0LA1LA3RB0RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm236: halts_at_trans (TM_from_str "1RB3LB4LB1LA---_2LA3RA1RB0LB2RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm237: halts_at_trans (TM_from_str "1RB3LA4LA1RA1LB_2LA0RB1LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm238: halts_at_trans (TM_from_str "1RB3RA3LB1LA3LA_2LB1RB3RB4LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm239: halts_at_trans (TM_from_str "1RB4RA4LA4LA3RA_2LB3LA---4LA1RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm240: halts_at_trans (TM_from_str "1RB3LA4LA1RA1LA_2LA---1LA3RB3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm241: halts_at_trans (TM_from_str "1RB1RA4LB4RA0LB_1LB2LA3LA---0RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm242: halts_at_trans (TM_from_str "1RB3LA4LB2RB2LA_2LA---0RA4RA2RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm243: halts_at_trans (TM_from_str "1RB3RB4LA---2RA_2LA2RB1LB2LB4RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm244: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB1LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm245: halts_at_trans (TM_from_str "1RB0LB3RA0RB---_2LA4LA2RB1RB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm246: halts_at_trans (TM_from_str "1RB3LB1LA---4LA_2LA3RB4RB2RB2LB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm247: halts_at_trans (TM_from_str "1RB2LA1RA---0RB_2LA4RB3LB2RB1LA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm248: halts_at_trans (TM_from_str "1RB3LA4RA4LA2LA_2LA1RB2RB1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm249: halts_at_trans (TM_from_str "1RB2RA3LB0LB3LA_2LA---3RA4RB3LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm250: halts_at_trans (TM_from_str "1RB4LA4LB0RA3LB_2LB3RA---1LA1RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm251: halts_at_trans (TM_from_str "1RB3LA4LB1RA3LB_2LA1LA3LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm252: halts_at_trans (TM_from_str "1RB3RA4RB2RA3LB_2LA---3LA4RB3LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm253: halts_at_trans (TM_from_str "1RB3LA---4RB4RA_2LA4LB1RA1LB1RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm254: halts_at_trans (TM_from_str "1RB3RA3LA1LA0RB_2LA4LA---3RA1RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm255: halts_at_trans (TM_from_str "1RB3LA3LA1RA1RA_1LB2LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm256: halts_at_trans (TM_from_str "1RB3RB2LB2LA2RB_2LA---3LA4RB3RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm257: halts_at_trans (TM_from_str "1RB3RA1LA1LB3LB_2LA4LB3RA2RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm258: halts_at_trans (TM_from_str "1RB1LA---2RA2LA_2LA3LB4RB1RB3RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm259: halts_at_trans (TM_from_str "1RB2LA1RA---2LB_0LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm260: halts_at_trans (TM_from_str "1RB1LB3RA4LB---_2LA2RB3LB1LA0RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm261: halts_at_trans (TM_from_str "1RB4LA3LB4LA3RA_2LB3RA---3LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm262: halts_at_trans (TM_from_str "1RB1LA---4LA1LB_2LA3RB3LA1LB4RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm263: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB0RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm264: halts_at_trans (TM_from_str "1RB3LA4RA4LA2LA_2LA---2RB1RB1LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm265: halts_at_trans (TM_from_str "1RB2RA3LA0RB---_2LA4LA1LA2RB3LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm266: halts_at_trans (TM_from_str "1RB3LA4LB1RA1LA_2LB1LA1LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm267: halts_at_trans (TM_from_str "1RB3LA4LA1RA1RA_2LB1LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm268: halts_at_trans (TM_from_str "1RB---0RB0LA0LB_2LB3LA3RA4RA3LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm269: halts_at_trans (TM_from_str "1RB0LB2LA---2RB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm270: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA---0LB1RA3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm271: halts_at_trans (TM_from_str "1RB2LA4LA4RA3LA_2LA3RB3RB2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm272: halts_at_trans (TM_from_str "1RB3LB0RA1RA3LA_2LA---4RB2RB0RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm273: halts_at_trans (TM_from_str "1RB2LA1RA---3LA_2LA4RB3LB2RB1LA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm274: halts_at_trans (TM_from_str "1RB3RA3LA1LA1LB_2LA4RB---3RA3RA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm275: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RA_2LB1LA1LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm276: halts_at_trans (TM_from_str "1RB3LA3LA2RA2RA_1LB2LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm277: halts_at_trans (TM_from_str "1RB3LA3LA1RA1RA_2LB2LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm278: halts_at_trans (TM_from_str "1RB3LA3LA1RA3RA_1LB2LA1RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm279: halts_at_trans (TM_from_str "1RB2LA4RA1RA2LA_1LB1LA3RB4LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm280: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA---4LB1RA3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm281: halts_at_trans (TM_from_str "1RB3RB---1LA1LA_2LA3RA1LB4LB1LA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm282: halts_at_trans (TM_from_str "1RB3LA4LB1RA0RA_2LA3LA1LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm283: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA4LB1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm284: halts_at_trans (TM_from_str "1RB3RB3RB1LA3LB_2LA3RA4LB2RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm285: halts_at_trans (TM_from_str "1RB3LA3LA2RA2RA_2LB2LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm286: halts_at_trans (TM_from_str "1RB1RA3LB2LA---_2LA3RB4RA1LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm287: halts_at_trans (TM_from_str "1RB3RA4LA4LB3RA_2LA---3RA2RB2RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm288: halts_at_trans (TM_from_str "1RB3LA2LA---2RB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm289: halts_at_trans (TM_from_str "1RB3LA1LB1RA3RA_2LB3LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm290: halts_at_trans (TM_from_str "1RB2LB4RA2RA2LA_2LA---3RB2LA4LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm291: halts_at_trans (TM_from_str "1RB3LA2LA---0LA_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm292: halts_at_trans (TM_from_str "1RB3LA1LA1RA1RA_2LA---4LB4RB4LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm293: halts_at_trans (TM_from_str "1RB3LA0RB1RA2LA_2LB1LA4RA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm294: halts_at_trans (TM_from_str "1RB3LB0LA---1RA_2LA0LA4RB2RB3LA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm295: halts_at_trans (TM_from_str "1RB3RA1LB2RB1LA_2LA4RB4RA1LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm296: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA---2LB4RB4RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm297: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA---0LB4RB4RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm298: halts_at_trans (TM_from_str "1RB4LA3LA4LA1RA_2LB2RA---4LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm299: halts_at_trans (TM_from_str "1RB3LA2RB4RA3LA_2LA---4LB3RB1LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm300: halts_at_trans (TM_from_str "1RB3RB2LA3LA---_2LA4RB3LB2RB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm301: halts_at_trans (TM_from_str "1RB3LA3LA1RA1RA_2LB2LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm302: halts_at_trans (TM_from_str "1RB2RA3LA---4LA_2LA4RB1RB2LB1LB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm303: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA0LB1RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm304: halts_at_trans (TM_from_str "1RB3RB4RA4LB2LA_2LA0LA4RB---1RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm305: halts_at_trans (TM_from_str "1RB2RB4LA2LA2RA_1LA3LA---4LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm306: halts_at_trans (TM_from_str "1RB2RB3RA4LA2LB_2LA---3LA4RA2RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm307: halts_at_trans (TM_from_str "1RB2LB3RA2LA3LA_2LA1RA1RB4LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm308: halts_at_trans (TM_from_str "1RB3LA4RB1LB0LA_2LA2LB1RB1RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm309: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA3RA4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm310: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA4LB1RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm311: halts_at_trans (TM_from_str "1RB2LA1RA---1RA_0LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm312: halts_at_trans (TM_from_str "1RB3LB---0RB1LB_2LA4RB1RA0LA1LA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm313: halts_at_trans (TM_from_str "1RB3LA1LA1RA---_2LA4LA1RA4LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm314: halts_at_trans (TM_from_str "1RB1RA4LA0LB3LB_1LB2LA3RA0RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm315: halts_at_trans (TM_from_str "1RB1LA---2RB4LA_2LA3RB4RB0LB2LB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm316: halts_at_trans (TM_from_str "1RB2LB---3LA0LB_2LA4RB3RB2LB2RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm317: halts_at_trans (TM_from_str "1RB3LA4LB1RA1LB_2LA1LA4LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm318: halts_at_trans (TM_from_str "1RB0RB3LA4RB2LA_2LA2RB1LB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm319: halts_at_trans (TM_from_str "1RB3LA4LA1RA1LA_2LB1LA1RA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm320: halts_at_trans (TM_from_str "1RB3RA4LB1LA---_2LA1LA3LB2RB3LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm321: halts_at_trans (TM_from_str "1RB3LA4LA1RA0LA_2LA3RB1RB1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm322: halts_at_trans (TM_from_str "1RB3RA1LA2RB2RA_2LA3LA4LA1RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm323: halts_at_trans (TM_from_str "1RB3LA---0RB0LB_2LA4LB4RA1RB3LA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm324: halts_at_trans (TM_from_str "1RB3LA---3LA4LB_2LA4RB3RB2LB2RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm325: halts_at_trans (TM_from_str "1RB0LB2LA---4LB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm326: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA2LA4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm327: halts_at_trans (TM_from_str "1RB3RB3LA3LB3RB_2LA---4LA2RA1RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm328: halts_at_trans (TM_from_str "1RB2LB4LA---1RB_2LA3LA3LB2RB1RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm329: halts_at_trans (TM_from_str "1RB4LA3LA4LA3RA_2LB2RA---3LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm330: halts_at_trans (TM_from_str "1RB3LA---0LA1LA_2LA0LB4RA4RB2LB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm331: halts_at_trans (TM_from_str "1RB3LA4LB1RA3RB_2LB1LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm332: halts_at_trans (TM_from_str "1RB2RA3LA4LA1LA_2LA4RB---3RB1RA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm333: halts_at_trans (TM_from_str "1RB2LA3LB4RA2LA_1LB1LA3RB---1RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm334: halts_at_trans (TM_from_str "1RB2LA3LB4RA2LA_1LB1LA3RB---4RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm335: halts_at_trans (TM_from_str "1RB3LB---0RA1LB_2LA3LA4RB0RB4RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm336: halts_at_trans (TM_from_str "1RB---4LA4LB2RA_2LB2RB3RB2RA0RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm337: halts_at_trans (TM_from_str "1RB3RB2LA4LA3RA_2LA2RB4RB---2LB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm338: halts_at_trans (TM_from_str "1RB3LA4LB1RA1LA_2LB1LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm339: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LB3LA2RA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm340: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA2RA4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm341: halts_at_trans (TM_from_str "1RB2LA1LB4LA2LB_0LA3LB3RA1RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm342: halts_at_trans (TM_from_str "1RB3LA1LB1RA3RA_2LB1LA3LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm343: halts_at_trans (TM_from_str "1RB3RB4LA---2RA_2LA2RB1LB1LB4RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm344: halts_at_trans (TM_from_str "1RB3RA1LA1LB---_2LA3LB4RA2RB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm345: halts_at_trans (TM_from_str "1RB2RB3LA2RA3RA_2LB2LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm346: halts_at_trans (TM_from_str "1RB3LA4LA2LB---_2LA2LB1RB3RA1RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm347: halts_at_trans (TM_from_str "1RB3LA1LB1RA3RA_2LB1LA1RA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm348: halts_at_trans (TM_from_str "1RB0RB4RA4LB2LA_2LA---3RB2RA1LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm349: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA3LB1RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm350: halts_at_trans (TM_from_str "1RB3LA1LB1RA1LA_2LA4LA0LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm351: halts_at_trans (TM_from_str "1RB4RB---1RA0LA_2LB3RB0RB4RB3LA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm352: halts_at_trans (TM_from_str "1RB2RA1LA3LB1LB_2LA3RB4RB2RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm353: halts_at_trans (TM_from_str "1RB3LA3RA0LA2RB_2LA---4LA4RB1LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm354: halts_at_trans (TM_from_str "1RB3RA1LA1LB---_2LA2RB4RA2RB2RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm355: halts_at_trans (TM_from_str "1RB3RA4LB---1RB_2LA4LA2RB1LB0RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm356: halts_at_trans (TM_from_str "1RB0RB3LA2RA3RA_2LB2LA3RA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm357: halts_at_trans (TM_from_str "1RB2LA1RA4RA2LB_0LA3RB3RB2RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm358: halts_at_trans (TM_from_str "1RB3LA3LA2RA1RA_2LB2LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm359: halts_at_trans (TM_from_str "1RB2LB1RA4LB---_2LA2LA3RB0RB2RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm360: halts_at_trans (TM_from_str "1RB3LA4LA1RA0LB_2LB1LA4LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm361: halts_at_trans (TM_from_str "1RB3LA4LA1RA1RA_2LB1LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm362: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA---3LB4RB1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm363: halts_at_trans (TM_from_str "1RB1LA3RB0LA2RA_2LA3RA4LB2LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm364: halts_at_trans (TM_from_str "1RB3LA4LA1RA3LA_2LA3RB3RB2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm365: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RA_2LA---1LA3RB1LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm366: halts_at_trans (TM_from_str "1RB3RB2LA4RA4LA_2LA2RB4RB---2LB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm367: halts_at_trans (TM_from_str "1RB3LA3RA4LB2LB_2LA---2RB0RA3LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm368: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB2RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm369: halts_at_trans (TM_from_str "1RB3LA---3LA3RB_2LA4RB3RB2LB2RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm370: halts_at_trans (TM_from_str "1RB3LA3RA2LA---_2LA3RB4LB4RB2RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm371: halts_at_trans (TM_from_str "1RB3LA3LA2RA3RA_2LB1LA---4RB4LB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm372: halts_at_trans (TM_from_str "1RB3LB---1LA1LA_2LA3RB4LB4LB3RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm373: halts_at_trans (TM_from_str "1RB3RA1LB1LA---_2LA4RB1LB3LB2RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm374: halts_at_trans (TM_from_str "1RB3RB2LA---1LA_2LA3RB4LB4RB2RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm375: halts_at_trans (TM_from_str "1RB2LA1RA4RA2LA_1LB1LA3RB4LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm376: halts_at_trans (TM_from_str "1RB2RA1LA0LB---_2LB3RB0RB4RB1RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm377: halts_at_trans (TM_from_str "1RB3LA2LB1RA---_2LA0LA4LB3RB3LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm378: halts_at_trans (TM_from_str "1RB3LA4LA1RA1RA_2LB1LA2LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm379: halts_at_trans (TM_from_str "1RB2LA---4LA2LB_1LA3RB3LB1LB3RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm380: halts_at_trans (TM_from_str "1RB3LA3LA2RA1RA_1LB2LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm381: halts_at_trans (TM_from_str "1RB3RA1LB1LB1LA_2LA4RB4RA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm382: halts_at_trans (TM_from_str "1RB4RA4LA2LB2RA_2LB2RB3LA---4RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm383: halts_at_trans (TM_from_str "1RB3RA3LB4LA1LB_2LA2RA3RA1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm384: halts_at_trans (TM_from_str "1RB3LA2RB1RA3LA_2LA4LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm385: halts_at_trans (TM_from_str "1RB0RB2LA---2RB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm386: halts_at_trans (TM_from_str "1RB3LA1LA0LB1RA_2LA4LB4LA1RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm387: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA0RA4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm388: halts_at_trans (TM_from_str "1RB0RB2LA---0LA_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm389: halts_at_trans (TM_from_str "1RB3LB---4RB2LA_2LA4LB3RA1LB1RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm390: halts_at_trans (TM_from_str "1RB2LA4LA4LB2RA_0LA4RB3RA---2RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm391: halts_at_trans (TM_from_str "1RB4LA1LA1RA1RA_2LB3LA---1RA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm392: halts_at_trans (TM_from_str "1RB3LA---4LA2LA_1LB2LA1RA0RA3RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm393: halts_at_trans (TM_from_str "1RB3RB3LA3LB3RB_2LA---4LA2RA4RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm394: halts_at_trans (TM_from_str "1RB3LA3LA1RA2RA_2LB2LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm395: halts_at_trans (TM_from_str "1RB4LA3LA4LA3RA_2LB2RA---4LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm396: halts_at_trans (TM_from_str "1RB3LA---4LB3LA_2LA4RA3RA4RB1LB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm397: halts_at_trans (TM_from_str "1RB3RB3RA2LA1LA_1LB2LA2RB4LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm398: halts_at_trans (TM_from_str "1RB4LA3LB4LA1RA_2LB3RA---3LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm399: halts_at_trans (TM_from_str "1RB2LA3LA4LA---_1LA1RA2RB0RA0LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm400: halts_at_trans (TM_from_str "1RB3LA4LA0LB0RB_2LA0RB1RA3RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm401: halts_at_trans (TM_from_str "1RB3RB2LA0RB---_2LA4RB3LB2RB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm402: halts_at_trans (TM_from_str "1RB3LA3LA2RA1RA_2LB2LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm403: halts_at_trans (TM_from_str "1RB3RB4LA2LA2LB_2LA---4RB0LA1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm404: halts_at_trans (TM_from_str "1RB4LA3LA1LA1RA_2LB2RA---0RA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm405: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA3LB4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm406: halts_at_trans (TM_from_str "1RB3LA---0LA4RA_2LA4LB1RA1LB1RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm407: halts_at_trans (TM_from_str "1RB0RA3LB2RB4RB_2LA---4LA3RA2RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm408: halts_at_trans (TM_from_str "1RB4LA3LA4LA1RA_2LB2RA---3LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm409: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA---1LB4RB3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm410: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB3LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm411: halts_at_trans (TM_from_str "1RB3LA3LA2RA2RA_2LB1LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm412: halts_at_trans (TM_from_str "1RB3LB3LA---2RB_2LA2RA4LB2RB1LA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm413: halts_at_trans (TM_from_str "1RB2LB3RA2LA3LA_2LA---2RB4LA1LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm414: halts_at_trans (TM_from_str "1RB3RB---4LB4LA_2LA2RB4RB2LA2LB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm415: halts_at_trans (TM_from_str "1RB3RA4RB---2LB_2LA4RB0RA1LA4LA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm416: halts_at_trans (TM_from_str "1RB3LB1RA3RA---_2LA4LB3RB0RB0LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm417: halts_at_trans (TM_from_str "1RB4RA3RB1LA3LA_1LB2LA3RA2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm418: halts_at_trans (TM_from_str "1RB3RA3RB1LA1LB_2LA4RB0LA---3RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm419: halts_at_trans (TM_from_str "1RB3LA4LA0LB---_2LA2RB3RB2LB0RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm420: halts_at_trans (TM_from_str "1RB3LA3LA1RA1RA_1LB2LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm421: halts_at_trans (TM_from_str "1RB3LA0RB1RA---_2LB1LA4LB3RB1LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm422: halts_at_trans (TM_from_str "1RB2LA---4LA1LB_1LA3RB3LB1LB3RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm423: halts_at_trans (TM_from_str "1RB4LA3LA1LA1RA_2LB1RA---1RA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm424: halts_at_trans (TM_from_str "1RB3LA0RB2LB---_2LA3LB4LA1RB3RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm425: halts_at_trans (TM_from_str "1RB3RA4LB2RA3LA_2LA---4RB4RB3LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm426: halts_at_trans (TM_from_str "1RB1RB3LA2RA3RA_2LB2LA3RA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm427: halts_at_trans (TM_from_str "1RB3RA4LB1LA1LB_2LA4RB---1LA3RA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm428: halts_at_trans (TM_from_str "1RB4LA3RA1LA1RA_2LB3LA---4RA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm429: halts_at_trans (TM_from_str "1RB1RB4LA---3LB_2LA0RB3LB2RB2RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm430: halts_at_trans (TM_from_str "1RB3LA2RB1RA1LA_2LA4LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm431: halts_at_trans (TM_from_str "1RB2LB3LA1LB4RA_2LA4LB1RA---1RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm432: halts_at_trans (TM_from_str "1RB2LA1RA1RA4LA_1LB1LA3RB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm433: halts_at_trans (TM_from_str "1RB0LB3LA4RA2LB_2LA4RA3RB0RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm434: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB0RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm435: halts_at_trans (TM_from_str "1RB1LB---3LA3LB_2LA4RB3RB2LB2RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm436: halts_at_trans (TM_from_str "1RB3RB4LA0RB2RA_2LA2RB4RB---2LB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm437: halts_at_trans (TM_from_str "1RB3RA3LB1LA0RA_2LA4RA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm438: halts_at_trans (TM_from_str "1RB3LA1LA4LB0RA_2LA0LA2RA1RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm439: halts_at_trans (TM_from_str "1RB3LA3LA2RA3RA_1LB2LA1RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm440: halts_at_trans (TM_from_str "1RB2LA4LA4RA3LA_2LA3RB3RB1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm441: halts_at_trans (TM_from_str "1RB3LA1RA4LA3RA_2LA4RA---4LB0LB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm442: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RA_2LB1LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm443: halts_at_trans (TM_from_str "1RB2LB---3LA3RB_2LA4RB3RB2LB2RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm444: halts_at_trans (TM_from_str "1RB2LB3LB3RA2RB_1LA3RA4LA2RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm445: halts_at_trans (TM_from_str "1RB3LA1LA1RA1RA_2LA---3LB4RB4LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm446: halts_at_trans (TM_from_str "1RB3LA4LA1RA1RA_2LB1LA1LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm447: halts_at_trans (TM_from_str "1RB4LA3LA4LA---_2LB3RA4LB1LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm448: halts_at_trans (TM_from_str "1RB2RA3LA1LA---_2LA3LB4RB1RB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm449: halts_at_trans (TM_from_str "1RB3RA4LA1LA3LA_2LA1RB4RB---2RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm450: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RA_2LA3RA1LA0LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm451: halts_at_trans (TM_from_str "1RB3LB0RA1RA3RA_2LA3LA4RB0RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm452: halts_at_trans (TM_from_str "1RB3RA4LB---1LB_2LA4LA4LA4RA2RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm453: halts_at_trans (TM_from_str "1RB2RA3LA2RA2RA_2LB2LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm454: halts_at_trans (TM_from_str "1RB3LA1LA2RB2RA_2LA4RA4LA1RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm455: halts_at_trans (TM_from_str "1RB3LB2RA---2LA_2LA4RA0LB2LB4LB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm456: halts_at_trans (TM_from_str "1RB2RB4LA2LA2RA_1LA3LA---3RA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm457: halts_at_trans (TM_from_str "1RB2LB---4LA3LB_2LA1RA3RB0RB4RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm458: halts_at_trans (TM_from_str "1RB3RA4LA4LB3RA_2LA---4RA2RB2RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm459: halts_at_trans (TM_from_str "1RB3LA4LA4RA3LA_2LA3RB3RB2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm460: halts_at_trans (TM_from_str "1RB2LA1LB4LA1RA_0LA3LB3RA1RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm461: halts_at_trans (TM_from_str "1RB3RB1LB4LA2RA_2LA4LA3RB---4RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm462: halts_at_trans (TM_from_str "1RB3LA3LA2RA2RA_2LB1LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm463: halts_at_trans (TM_from_str "1RB2LA3RA1LA---_0LA2RB1LB4RB3LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm464: halts_at_trans (TM_from_str "1RB3LB1LB3RA3LA_2LA0LA4RA1RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm465: halts_at_trans (TM_from_str "1RB3LA0RB4RB1LA_2LA0RB4RA2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm466: halts_at_trans (TM_from_str "1RB3RB4LA2LA2RA_2LA2RB4RB---2LB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm467: halts_at_trans (TM_from_str "1RB0RB2LA---4LB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm468: halts_at_trans (TM_from_str "1RB4RA---4RA1LA_2LB3RB4LB4LA4LA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm469: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LB3LA3LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm470: halts_at_trans (TM_from_str "1RB3LA4LA1RA1LA_2LA---1LA3RB1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm471: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA0LA4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm472: halts_at_trans (TM_from_str "1RB3LA1LB1RA1RA_2LB3LA2LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm473: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RA_2LB1LA2LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm474: halts_at_trans (TM_from_str "1RB2RB3LA2RA2RA_1LB2LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm475: halts_at_trans (TM_from_str "1RB2LB---3LA1LA_2LA4RB3RB2LB2RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm476: halts_at_trans (TM_from_str "1RB3RA4LA4RA3LA_2LB3LA1RA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm477: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA1LB1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm478: halts_at_trans (TM_from_str "1RB3LA1LA1RA---_2LA4LA1LA4LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm479: halts_at_trans (TM_from_str "1RB1LB3RA2LA3LA_1LA2RB3RA4LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm480: halts_at_trans (TM_from_str "1RB2LB4RA2RA2LA_2LA---3RB4LA4LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm481: halts_at_trans (TM_from_str "1RB3LB4LA4RA2RA_2LA4RA2LB---1RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm482: halts_at_trans (TM_from_str "1RB3RB2RA0RB---_2LB3LA0RB4RA1LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm483: halts_at_trans (TM_from_str "1RB1RB4LA---3LB_2LA3LA3LB2RB2RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm484: halts_at_trans (TM_from_str "1RB3RB---1LA1LA_2LB3RB4LB2LA3RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm485: halts_at_trans (TM_from_str "1RB2LB1RA4LB---_2LA2LB3RB0RB1RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm486: halts_at_trans (TM_from_str "1RB2LA1RA1RA3LB_1LB1LA3RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm487: halts_at_trans (TM_from_str "1RB3LA3LB4LA0RA_2LB1RA---4RB1LB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm488: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RB_2LA1LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm489: halts_at_trans (TM_from_str "1RB3LA---4LA3LB_2LA3RB1RB1LB1RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm490: halts_at_trans (TM_from_str "1RB3LA4LA1RA1LA_2LB1LA0RA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm491: halts_at_trans (TM_from_str "1RB3RA4LA1LA2RB_2LA2LB1RB---0LA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm492: halts_at_trans (TM_from_str "1RB4RB---1LA1LA_2LB3RB4LB2LA4RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm493: halts_at_trans (TM_from_str "1RB2LA1RA1RA4LA_1LB1LA3RB4LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm494: halts_at_trans (TM_from_str "1RB2LB4LA4LB---_2LA2LB3RB0RB0RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm495: halts_at_trans (TM_from_str "1RB3LA1RA0LA0LB_2LA4RB2RB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm496: halts_at_trans (TM_from_str "1RB3LA1LA4LA3RA_2LA4RB---0RA2RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm497: halts_at_trans (TM_from_str "1RB3LA2LA---4RB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm498: halts_at_trans (TM_from_str "1RB3LA4LA1RA1LA_2LA---4RA3RB4LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm499: halts_at_trans (TM_from_str "1RB1LA---0RB4RB_2LA3LB4RA4LB0LB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm500: halts_at_trans (TM_from_str "1RB0LA---4RA0LA_2LB3RB0RB4RB3LA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm501: halts_at_trans (TM_from_str "1RB3LA0LB1RA0RA_2LA1LB---4RA1RA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm502: halts_at_trans (TM_from_str "1RB3LA4LA4RA3LA_2LA3RB3RB1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm503: halts_at_trans (TM_from_str "1RB3RA1LA1LB---_2LA2RB4RA2RB1LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm504: halts_at_trans (TM_from_str "1RB3LA2RB1RA3RA_2LA0LB1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm505: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LA---4LB4RB3RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm506: halts_at_trans (TM_from_str "1RB2LB3RA4LA3RA_1LA2RB2RA3LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm507: halts_at_trans (TM_from_str "1RB3LA3LA2RA1RA_2LB1LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm508: halts_at_trans (TM_from_str "1RB3RA3RB1LA1LB_2LA4RB3RB---3RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm509: halts_at_trans (TM_from_str "1RB2LB4RB3LA---_1LA3RA3LB0LB3LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm510: halts_at_trans (TM_from_str "1RB3LA---2RB0LB_2LA4LB4RA1RB3LA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm511: halts_at_trans (TM_from_str "1RB2LB3RA2LA2LA_2LA---2RB4LB3RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm512: halts_at_trans (TM_from_str "1RB2RA1LA1RB---_2LA3LB4RA1RB1LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm513: halts_at_trans (TM_from_str "1RB2LA---4LA1LB_0LA3RB1LB1LB3RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm514: halts_at_trans (TM_from_str "1RB3LA0RB1RA---_2LB1LA4LB3RB1LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm515: halts_at_trans (TM_from_str "1RB3LA3LA2RA2RA_2LB2LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm516: halts_at_trans (TM_from_str "1RB2RA2RB---4LA_2LA4RB3LA1LA1LB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm517: halts_at_trans (TM_from_str "1RB2RB3LA4RA3LA_0LA3RB---1LB0RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm518: halts_at_trans (TM_from_str "1RB3LA3LA1RA2RA_1LB2LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm519: halts_at_trans (TM_from_str "1RB0RB2LA---4RB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm520: halts_at_trans (TM_from_str "1RB0LB4LA3LA---_2LA2RB3RA1LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm521: halts_at_trans (TM_from_str "1RB3LA4LA1RA2LB_2LA3RB1LA1LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm522: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RB_2LB1LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm523: halts_at_trans (TM_from_str "1RB3LA4LA1RA0LA_2LA2LA3RB2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm524: halts_at_trans (TM_from_str "1RB3RB0RB3LA2RB_2LA4RA3RB2LB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm525: halts_at_trans (TM_from_str "1RB4LA4LA4RA2RA_1LB2LA3RA---3RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm526: halts_at_trans (TM_from_str "1RB3LA4LA1RA1LB_2LB1LA3RA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm527: halts_at_trans (TM_from_str "1RB3LA4LB4LA3RA_2LA---3RA4RB2RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm528: halts_at_trans (TM_from_str "1RB3LB4LA---2RA_2LA3RB3LB2RB4RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm529: halts_at_trans (TM_from_str "1RB3RA3LA4LA3RA_2LB2RA---3LA4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm530: halts_at_trans (TM_from_str "1RB3LB1LA1LA1LA_2LA2RB4LB---2RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm531: halts_at_trans (TM_from_str "1RB0RB4LA---3LB_2LA3LA3LB2RB2RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm532: halts_at_trans (TM_from_str "1RB3LA1LA1RA3RA_2LB3LA3RA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm533: halts_at_trans (TM_from_str "1RB2LA1RA2LB2RA_1LA4RB3RB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm534: halts_at_trans (TM_from_str "1RB2LB3RA2LA2LA_2LA---2RB4LB4RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm535: halts_at_trans (TM_from_str "1RB2LB3LA1RB---_1LA2RB1LB4RA1LA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm536: halts_at_trans (TM_from_str "1RB0RB4LA---3LB_2LA0RB3LB2RB2RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm537: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA2RB4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm538: halts_at_trans (TM_from_str "1RB3RA3RB1LA2LB_2LA4RB1LA---1RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm539: halts_at_trans (TM_from_str "1RB2LB4LA---2LA_2LA0RB3LB2RB1RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm540: halts_at_trans (TM_from_str "1RB3LA4LA1RA3RB_2LB1LA1LB3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm541: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RB_2LA0LB1LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm542: halts_at_trans (TM_from_str "1RB3LB3RA4RB2LA_2LA---4RB0RA0LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm543: halts_at_trans (TM_from_str "1RB4LA3LA1LA1RA_2LB1RA---1LB4RB") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm544: halts_at_trans (TM_from_str "1RB3RA0LA1LA1LB_2LA4RB2LA---3RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm545: halts_at_trans (TM_from_str "1RB3LB1LA2LB---_2LA2RB3LB4RA2RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm546: halts_at_trans (TM_from_str "1RB3LA2LA---4LB_2LA4RB3LB2RB3RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm547: halts_at_trans (TM_from_str "1RB3LA4LA1RA0RB_2LA2RA1LA3RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm548: halts_at_trans (TM_from_str "1RB3LA3LA1RA2RA_2LB1LA1LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm549: halts_at_trans (TM_from_str "1RB3RB3RA---2LB_2LA0RB4RB2LB0RA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm550: halts_at_trans (TM_from_str "1RB3RA4LB2RA3LA_2LA---4RB4RB2LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm551: halts_at_trans (TM_from_str "1RB3LA1LB1RA3RA_2LB1LA4LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm552: halts_at_trans (TM_from_str "1RB2LA1RA1RA---_1LB1LA3RB4LB1RA") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm553: halts_at_trans (TM_from_str "1RB3LA1RA0LA2LB_2LA2LB1RA4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm554: halts_at_trans (TM_from_str "1RB2LA1RA1RA4LA_1LB1LA3RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm555: halts_at_trans (TM_from_str "1RB0RA3LA2RA3RA_2LB2LA2RA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm556: halts_at_trans (TM_from_str "1RB3LA1RB1LA1RA_2LA2LA4LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm557: halts_at_trans (TM_from_str "1RB4LA3LA4LA---_2LB1RA2RA1LB3RB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm558: halts_at_trans (TM_from_str "1RB3LB---1RA1LB_2LA3LA4RB0RB1RA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm559: halts_at_trans (TM_from_str "1RB2RB3LA2RA3RA_2LB2LA3LA4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm560: halts_at_trans (TM_from_str "1RB3LA1RA4LA1RA_2LA---1LA4RB0LA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm561: halts_at_trans (TM_from_str "1RB4RB1LA2RB2LA_2LB3LA3RA2RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm562: halts_at_trans (TM_from_str "1RB3LA1LA2RB0LA_2LA0RA4LA4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm563: halts_at_trans (TM_from_str "1RB2RA3LA4LA2RB_2LA0LA---0RA1LA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm564: halts_at_trans (TM_from_str "1RB3LA4LA2LB3RA_2LA---2RA1RB4RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm565: halts_at_trans (TM_from_str "1RB0RA3LB4RB2RA_2LA---4LA2RB3LA") c0 (B,1).
Proof. solve_halt'' 8 false. Time Qed.

Lemma tm566: halts_at_trans (TM_from_str "1RB3LB2RA1LA---_2LA4RA3RB2LB2LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm567: halts_at_trans (TM_from_str "1RB3RB---4RA1LA_2LA4RB3LB1LB3LA") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm568: halts_at_trans (TM_from_str "1RB4LA1LA2RA3LA_2LB3RA---0RB0RA") c0 (B,2).
Proof. solve_halt'' 8 false. Time Qed.

Lemma tm569: halts_at_trans (TM_from_str "1RB3RB4LB1RA---_1LB2RA3LA1LB0LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm570: halts_at_trans (TM_from_str "1RB3LB4LA4LA2RA_2LA4RA2LB---1RB") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm571: halts_at_trans (TM_from_str "1RB1RA3LB2LA---_2LA3RB4RA1LB3LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm572: halts_at_trans (TM_from_str "1RB3RB4LB1RA---_1LB2RA3LA1LB3LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm573: halts_at_trans (TM_from_str "1RB1RA3LB2LA---_2LA3RB4RA1LB1LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm574: halts_at_trans (TM_from_str "1RB3LB2RA1LA---_2LA4RA3RB2LB3LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm575: halts_at_trans (TM_from_str "1RB3LA1LA0RB1LB_2LA4RB0RA1RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm576: halts_at_trans (TM_from_str "1RB0LB4LA3RA1LB_2LA2RA3LB2RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm577: halts_at_trans (TM_from_str "1RB3LA1LA2LA3RA_2LB1RA2RB4RB---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm578: halts_at_trans (TM_from_str "1RB2LA0RB4LA3LA_1LA3RA1RA---0LA") c0 (B,3).
Proof. solve_halt'' 8 false. Time Qed.

Lemma tm579: halts_at_trans (TM_from_str "1RB3LB4LB---0LB_2LA3RB1LB4RA2RB") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm580: halts_at_trans (TM_from_str "1RB3RB0LB---3LB_2LA2RB4RB0RB1LA") c0 (A,3).
Proof. solve_halt. Time Qed.

Lemma tm581: halts_at_trans (TM_from_str "1RB---3RA0LB0RB_2LB3LA4LB2RB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm582: halts_at_trans (TM_from_str "1RB1LB---2LA4LA_2LA4RB3RB1RA3LB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm583: halts_at_trans (TM_from_str "1RB2RA3LA4RB---_1LB2LA0RA0LB0LB") c0 (A,4).
Proof. solve_halt. Time Qed.

Lemma tm584: halts_at_trans (TM_from_str "1RB2LA0LB1RA1LB_0LA4RA3LB---2RA") c0 (B,3).
Proof. solve_halt. Time Qed.

Lemma tm585: halts_at_trans (TM_from_str "1RB4LA---1LA3RB_1LB2LA3RA1LB0RB") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm586: halts_at_trans (TM_from_str "1RB2LA0RB4RA1LA_1LA3LB1RA0LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm587: halts_at_trans (TM_from_str "1RB3RA4LA1LA1LB_2LA4RB---4LB4RA") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm588: halts_at_trans (TM_from_str "1RB2LA1RA2LB2RB_0LA4RA3RB1RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm589: halts_at_trans (TM_from_str "1RB2LA1RA2LB2RA_0LA2RB3RB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm590: halts_at_trans (TM_from_str "1RB2LA1RA2LB2RA_0LA3RB3RB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm591: halts_at_trans (TM_from_str "1RB2LA1RA2LB2LA_0LA2RB3RB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm592: halts_at_trans (TM_from_str "1RB2LA4RA1LB2LA_0LA2RB3RB2RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm593: halts_at_trans (TM_from_str "1RB2LA4RA2LB2LA_0LA2RB3RB4RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm594: halts_at_trans (TM_from_str "1RB2LA1RA4RA2LB_0LA2RB3RB2LA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm595: halts_at_trans (TM_from_str "1RB2LA1RA4RA2LB_0LA2RB3RB2RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm596: halts_at_trans (TM_from_str "1RB2LA4RA2LB2LA_0LA2RB3RB1RA---") c0 (B,4).
Proof. solve_halt. Time Qed.

Lemma tm597: halts_at_trans (TM_from_str "1RB2LB4LB3LA---_1LA3RA3LB0LB0RA") c0 (A,4).
Proof. solve_halt'' 3%nat true. Time Qed.

Lemma tm598: halts_at_trans (TM_from_str "1RB0RA3LB1LB---_2LA3RB4RB3RA0LA") c0 (A,4).
Proof. solve_halt'' 13%nat false. Time Qed.

