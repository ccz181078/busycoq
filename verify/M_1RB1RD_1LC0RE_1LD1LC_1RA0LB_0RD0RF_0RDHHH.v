From BusyCoq Require Import Individual62 PR93PairEngine.
From Coq Require Import String.
Local Open Scope string_scope.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---").

Lemma valid : Perm (flip (src_tm false)) tm rename93.
Proof. check_literal_perm. Qed.

Lemma cert_ok : checker false 22 C = true.
Proof. native_check_eq. Qed.

Theorem halt : halts tm c0.
Proof. exact (checker_target_halt false tm 22 valid cert_ok). Qed.
End TM1.

Print Assumptions TM1.halt.
