(** Blank halting equivalence of two literal BB(6) partial machines. *)
From BusyCoq Require Import Individual62 RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Frozen220 Pair220.
From Coq Require Import String.
Open Scope string_scope.

Definition tm := Eval compute in (TM_from_str
  "1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RE0RA").
Definition tm' := Eval compute in (TM_from_str
  "1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA").
Lemma source_binding : tm = frozen220.
Proof. reflexivity. Qed.
Lemma target_binding : tm' = frozen723.
Proof. reflexivity. Qed.
Theorem eqv : halts tm c0 <-> halts tm' c0.
Proof.
  rewrite source_binding,target_binding.
  exact original220_723_halting_equivalence.
Qed.
Print Assumptions source_binding.
Print Assumptions target_binding.
Print Assumptions eqv.
