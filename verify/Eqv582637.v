(** Exact original815 rows582/637 blank-halting equivalence. *)
From BusyCoq Require Import Individual62 RegularInvariant62.
From BusyCoq.Eqv582637 Require Import Frozen582 Pair582.
From Coq Require Import String.
Open Scope string_scope.
Definition tm := Eval compute in (TM_from_str
 "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC").
Definition tm' := Eval compute in (TM_from_str
 "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA").
Lemma source_binding : tm = frozen582.
Proof. reflexivity. Qed.
Lemma target_binding : tm' = frozen637.
Proof. reflexivity. Qed.
Theorem eqv : halts tm c0 <-> halts tm' c0.
Proof. rewrite source_binding,target_binding. exact original582_637_halting_equivalence. Qed.
Print Assumptions source_binding.
Print Assumptions target_binding.
Print Assumptions eqv.
