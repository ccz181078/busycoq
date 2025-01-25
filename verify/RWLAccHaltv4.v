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




Lemma tm226: halts_at_trans (TM_from_str "1RB1LF_1RC1LE_0RD0RE_1LE0RD_0LA0LB_---0LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm227: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE1LD_1RA0LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm228: halts_at_trans (TM_from_str "1RB0RF_1LC0LE_1RD0LB_0RE0RC_0LA0RA_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm229: halts_at_trans (TM_from_str "1RB1RE_1LC0LF_1RD0LB_0LA0RC_0RF---_0LA0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm230: halts_at_trans (TM_from_str "1RB1RF_1LC0LE_1RD0LB_0RE0RC_0LA0RA_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm231: halts_at_trans (TM_from_str "1RB0RC_1LC1LD_1RA0LB_1LE0RD_1LB0LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm232: halts_at_trans (TM_from_str "1RB1RD_1LC0RA_1LA0LB_1RE0LD_1RA0RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm233: halts_at_trans (TM_from_str "1RB1LB_1LC---_1LE1LD_0RA0RE_1RD0RF_0LC0LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm234: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0RD0RF_1LE0RF_1LA0LD_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm235: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0RD0RF_1LE1LB_1LA0LD_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm236: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0RD1LC_1LE0RF_1LA0LD_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm237: halts_at_trans (TM_from_str "1RB1RC_1LC0LF_0LD0LB_1LE1RE_1RA---_0RA0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm238: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD0RD_1RE1RF_1LA0LC_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm239: halts_at_trans (TM_from_str "1RB0RC_1LC0RA_1RB0LD_1LE---_0LF1LD_1LB1LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm240: halts_at_trans (TM_from_str "1RB---_0RC0RB_1LD0RA_1LE0LC_1RF0LD_0RB0RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm241: halts_at_trans (TM_from_str "1RB0LC_1LC0LB_1RE0LD_1LB0LF_0RA0RC_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm242: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD0RD_1RE0RF_1LA0LC_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm243: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_0LD0LB_0RE0LE_1LA1LF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm244: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_0RD0LB_1LA1LE_0LF---_0RD0LD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm245: halts_at_trans (TM_from_str "1RB0LC_1RC0RA_1LA1LD_1LE0RD_1LC0LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm246: halts_at_trans (TM_from_str "1RB1RD_1LC0LE_1RA0LB_1RA0RF_0RA0RC_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm247: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LA1LD_1LC0LF_0LC0LB_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm248: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_0LD0LB_0RE0LE_1LA1LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm249: halts_at_trans (TM_from_str "1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB0RF_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.


