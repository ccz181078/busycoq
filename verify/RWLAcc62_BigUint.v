Require Export String.
Require Export NArith.
From BusyCoq Require Export Individual62.
From BusyCoq Require Export RWLAcc_BigUint.

Module RWLAcc62 := RWLAcc BB62.
Export RWLAcc62.

Open Scope string.


Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.

Ltac solve_halt' bsz bmaxT use_acc mnc T :=
  eapply (decide_halt_spec _ bsz bmaxT use_acc (of_nat (N.to_nat mnc)) T);
  native_check_eq.

Ltac solve_halt'' bsz use_acc :=
  match goal with
  | |- halts_at_trans (TM_from_str ?x) c0 _ =>
    idtac x;
    solve_halt' bsz 3200 use_acc 2%N (10^12)%N
  end.

Fixpoint get_len(ls:RWL):N' :=
match ls with
| (w,_,n)::t => (of_nat (List.length w) * n + get_len t)%N'
| _ => N0
end.

Definition chk tm bsz use_acc T :=
  match RWL_steps tm bsz 3200 use_acc (of_nat 2) T with
  | inr x => inr x
  | inl (c1,c2,l,r) =>
    let '(l0,r0,_,_):=c2 in
    inl (get_len l0 + get_len r0)%N'
  end.

Fixpoint size(x:N'):N' :=
match x with
| BigUintNil => N0
| BigUintCons a0 a1 => succ (size a1)
end.

Definition chk' tm bsz use_acc T :=
match chk tm bsz use_acc T with
| inl x => inl (toZ (size x))
| inr x => inr x
end.

Ltac test_bsz bsz use_acc T :=
  match goal with
  | |- halts_at_trans (?x) c0 _ =>
    pose (chk' x bsz use_acc T) as v;
    time native_compute in v;
    match goal with
    | _ := ?x : _ |- _ => idtac x
    end;
    clear v
  end.

Fixpoint sel_bsz_0 tm bsz n T cur_bsz cur_sz :=
  match (chk tm bsz true T) with
  | inl x =>
    let (nxt_bsz,nxt_sz) := (if cur_sz <? x then (bsz,x) else (cur_bsz,cur_sz))%N' in
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

Open Scope sym.
