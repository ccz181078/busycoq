(** Native blank halting equivalence of the two literal BB(6) tables. *)
From BusyCoq Require Import Individual62 RegularInvariant62.
From BusyCoq.EqvRegularPairs.Pair728 Require Import Frozen728 Pair728.
From Coq Require Import String.
Open Scope string_scope.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0RC1RD_0LD---_1LE1RA_1LA0LF_0RD0RC").
Definition tm' := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LE---").
Lemma source_binding : tm = frozen728.
Proof. reflexivity. Qed.
Lemma target_binding : tm' = original772.
Proof. reflexivity. Qed.
Theorem eqv : halts tm c0 <-> halts tm' c0.
Proof. rewrite source_binding,target_binding. exact original728_772_halting_equivalence. Qed.
Print Assumptions source_binding.
Print Assumptions target_binding.
Print Assumptions eqv.
