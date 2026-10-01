(* Executable positive and mutation controls, checked by Coq and coqchk. *)
From Coq Require Import Lists.List.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.

Import ListNotations.
Close Scope sym_scope.
Open Scope nat_scope.

Definition one_state : DFA := fun _ _ => 0.
Definition immediate_halter : RI.TM := fun _ => None.
Definition blank_only := [initial_entry].

Example immediate_halter_check : check immediate_halter 1 one_state blank_only = true.
Proof. vm_compute. reflexivity. Qed.

Theorem immediate_halter_reachable c : RI.evstep immediate_halter RI.c0 c ->
  represented one_state blank_only c.
Proof. apply (check_reachable_invariant _ _ _ _ immediate_halter_check). Qed.

Theorem immediate_halter_really_halts : RI.halts immediate_halter RI.c0.
Proof. apply RI.halted_halts. reflexivity. Qed.

Definition drift : RI.TM := fun _ => Some (S092, R, A6).
Definition drift_invariant := [E A6 S092 0 0; E A6 S192 0 0].

Example drift_check : check drift 1 one_state drift_invariant = true.
Proof. vm_compute. reflexivity. Qed.

Theorem drift_reachable c : RI.evstep drift RI.c0 c ->
  represented one_state drift_invariant c.
Proof. apply (check_reachable_invariant _ _ _ _ drift_check). Qed.

Example missing_initial_rejected : check immediate_halter 1 one_state [] = false.
Proof. vm_compute. reflexivity. Qed.

Example malformed_initial_rejected :
  check immediate_halter 1 one_state [E B6 S092 0 0] = false.
Proof. vm_compute. reflexivity. Qed.

Example malformed_bound_rejected :
  check immediate_halter 1 one_state [initial_entry; E A6 S092 1 0] = false.
Proof. vm_compute. reflexivity. Qed.

Definition bad_blank : DFA := fun _ _ => 1.
Example bad_blank_loop_rejected :
  check immediate_halter 2 bad_blank blank_only = false.
Proof. vm_compute. reflexivity. Qed.

Definition out_of_range : DFA := fun _ b => match b with S092 => 0 | S192 => 1 end.
Example out_of_range_delta_rejected :
  check immediate_halter 1 out_of_range blank_only = false.
Proof. vm_compute. reflexivity. Qed.

Example empty_dfa_rejected : check immediate_halter 0 one_state blank_only = false.
Proof. vm_compute. reflexivity. Qed.

(* The missing symbol-1 successor is required even though the actual blank
   drifting execution only reads zero. This exercises exhaustive inverse edges. *)
Example missing_inverse_pop_rejected : check drift 1 one_state blank_only = false.
Proof. vm_compute. reflexivity. Qed.

(* Distinct predecessor states may share the same edge target. *)
Definition ambiguous_dfa : DFA := fun _ _ => 0.
Definition ambiguous_invariant :=
  [E A6 S092 0 0; E A6 S192 0 0; E A6 S092 0 1; E A6 S192 0 1].
Example ambiguous_pop_check : check drift 2 ambiguous_dfa ambiguous_invariant = true.
Proof. vm_compute. reflexivity. Qed.
Example missing_other_predecessor_rejected :
  check drift 2 ambiguous_dfa drift_invariant = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions immediate_halter_check.
Print Assumptions immediate_halter_reachable.
Print Assumptions immediate_halter_really_halts.
Print Assumptions drift_reachable.
Print Assumptions missing_inverse_pop_rejected.
Print Assumptions missing_other_predecessor_rejected.
