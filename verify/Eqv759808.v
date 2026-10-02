(** Exact original815 rows759/808 blank-halting equivalence. *)
From BusyCoq Require Import Individual62 RegularInvariant62.
From BusyCoq.Eqv759808 Require Import Frozen759 Pair759.
From Coq Require Import String.
Open Scope string_scope.
Definition tm := Eval compute in (TM_from_str
 "1RB1LD_0RC1LE_1RD0LA_1RE0RC_1LF0LC_---1LB").
Definition tm' := Eval compute in (TM_from_str
 "1RB1LD_0RC1LE_1RD0LA_1RE0RF_1LF0LC_---1LB").
Lemma source_binding : tm = frozen759.
Proof. reflexivity. Qed.
Lemma target_binding : tm' = frozen808.
Proof. reflexivity. Qed.
Theorem eqv : halts tm c0 <-> halts tm' c0.
Proof. rewrite source_binding,target_binding. exact original759_808_halting_equivalence. Qed.
Print Assumptions source_binding.
Print Assumptions target_binding.
Print Assumptions eqv.
