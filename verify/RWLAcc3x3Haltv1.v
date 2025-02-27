From BusyCoq Require Import RWLAcc33.

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


Lemma tm1: halts_at_trans (TM_from_str "1RB2LA1LC_0LA2RB1LB_---1RA1RC") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB1LB2LA_1LA1RC---_0LA2RC1LC") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB2RC1LA_2LA1RB---_2RB2RA1LC") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB2RA1LA_2LA2LB2RC_---2RB1RB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB2LA1LA_2LA1RC2RB_---0LC0RA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB1LA2LC_2LA2RB1RB_---0LB0RC") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB1LA2LA_1LB1RC---_1LA2RC1LC") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB2LA1RA_1LB1LA2RC_---1LC2RB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB2LA1RA_1LB1LA2RC_---1LA2RB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB2LA1RA_1LB1LA1RC_---2LA2RB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB2LA---_0LC2RB1LB_1RA1LC2LC") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB1LA---_0LC2RB1LB_1RA1LC2LC") c0 (A,2).
Proof. solve_halt. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB2RA1LA_0RC1RC2LA_2LC1RB---") c0 (C,2).
Proof. solve_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB---2LC_1LC2RB1LB_1LA2RC2LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB---2RB_1LC0LB1RA_1RA2LC1RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB2RA2RC_1LC---1LA_1RA2LB1LC") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB---2LC_1LC2RB1LB_1LA0RB2LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB2LA1RA_1LC1LA2RC_---1LA2RB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB2LA1RA_1LC2RB1RC_---1LA1LB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB2LA1RA_1RC2RB0RC_1LA---1LA") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB2RA1LA_2LC0RC1RB_---2LA1RB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB1LA2LA_2RC1RC---_1LA2RC1LC") c0 (B,2).
Proof. solve_halt. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB0LA1LA_2RC1RC---_2LC1RA0RC") c0 (B,2).
Proof. solve_halt. Time Qed.

