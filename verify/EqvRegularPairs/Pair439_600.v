(** Native blank halting equivalence of the two literal BB(6) tables. *)
From BusyCoq Require Import Individual62 RegularInvariant62.
From BusyCoq.EqvRegularPairs.Pair439 Require Import Frozen439 Pair439.
From Coq Require Import String.
Open Scope string_scope.
Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC0RF_0LD---_1RF1LE_0LF1LC_1LD0RA").
Definition tm' := Eval compute in (TM_from_str "1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA").
Lemma source_binding : tm = frozen439.
Proof. reflexivity. Qed.
Lemma target_binding : tm' = original600.
Proof. reflexivity. Qed.
Theorem eqv : halts tm c0 <-> halts tm' c0.
Proof. rewrite source_binding,target_binding. exact original439_600_halting_equivalence. Qed.
Print Assumptions source_binding.
Print Assumptions target_binding.
Print Assumptions eqv.
