(** Exact original-row blank halting equivalence, standard native BB62 context. *)
From BusyCoq Require Import Individual62 RegularInvariant62.
From BusyCoq.Eqv464572 Require Import Frozen464Indexed Pair464.
From Coq Require Import String.
Open Scope string_scope.
Definition tm := Eval compute in (TM_from_str
  "1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB0RC").
Definition tm' := Eval compute in (TM_from_str
  "1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD").
Lemma source_binding : tm = frozen464.
Proof. reflexivity. Qed.
Lemma target_binding : tm' = frozen572.
Proof. reflexivity. Qed.
Theorem eqv : halts tm c0 <-> halts tm' c0.
Proof. rewrite source_binding,target_binding. exact original464_572_halting_equivalence. Qed.
Print Assumptions source_binding.
Print Assumptions target_binding.
Print Assumptions eqv.
