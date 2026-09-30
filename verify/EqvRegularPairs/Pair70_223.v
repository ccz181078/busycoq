(** Native blank halting equivalence of the two literal BB(6) tables. *)
From BusyCoq Require Import Individual62 RegularInvariant62.
From BusyCoq.EqvRegularPairs.Pair70 Require Import Frozen70 Pair70.
From Coq Require Import String.
Open Scope string_scope.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1LC1RE_1LD1RD_1LA0LB_0RC---_1RC0LD").
Definition tm' := Eval compute in (TM_from_str "1RB1LE_0RC1RF_1LD1RD_1LA0LB_1RC0LD_0RC---").
Lemma source_binding : tm = frozen70.
Proof. reflexivity. Qed.
Lemma target_binding : tm' = original223.
Proof. reflexivity. Qed.
Theorem eqv : halts tm c0 <-> halts tm' c0.
Proof. rewrite source_binding,target_binding. exact original70_223_halting_equivalence. Qed.
Print Assumptions source_binding.
Print Assumptions target_binding.
Print Assumptions eqv.
