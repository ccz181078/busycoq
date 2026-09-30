(** Halting equivalence of two BB(6) partial machines.
    The numerical labels 363/470 refer only to the public815 snapshot.
    This theorem concerns the literal tables below, on the blank tape.
    It does not decide either machine or assert a step-count/score theorem. *)
From BusyCoq Require Import Individual62.
From Coq Require Import String.
Open Scope string_scope.
From BusyCoq.Eqv363470 Require Import SourceSafety TerminalCoupling.

Definition tm := Eval compute in (TM_from_str
  "1RB1LC_1LC0RD_0LE1LA_0RF1RA_1RD0LA_---0RB").
Definition tm' := Eval compute in (TM_from_str
  "1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB").

Lemma source_binding : tm = source363.
Proof. reflexivity. Qed.
Lemma target_binding : tm' = target470.
Proof. reflexivity. Qed.

Theorem eqv : halts tm c0 <-> halts tm' c0.
Proof.
  rewrite source_binding,target_binding.
  exact original363_470_halting_equivalence.
Qed.

Print Assumptions source_binding.
Print Assumptions target_binding.
Print Assumptions eqv.
