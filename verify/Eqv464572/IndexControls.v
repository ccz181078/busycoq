From Coq Require Import Lists.List.
From BusyCoq Require Import TM RegularInvariant62 IndexedRegularInvariant62.
Import ListNotations.
Close Scope sym_scope.
Open Scope nat_scope.

Definition halt_tm : RI.TM := fun _ => None.
Definition drift_tm : RI.TM := fun qs => match qs with
  | (A6,S092) => Some(S092,R,A6) | _ => None end.
Definition zero_dfa : DFA := fun _ _ => 0.
Definition empty_table : buckets := fun _ _ _ => [].
Definition blank_table : buckets := fun q s l => match q,s,l with
  | A6,S092,0 => [0] | _,_,_ => [] end.
Definition duplicate_blank_table : buckets := fun q s l => match q,s,l with
  | A6,S092,0 => [0;0] | _,_,_ => [] end.
Definition out_of_range_table : buckets := fun q s l => match q,s,l with
  | A6,S092,0 => [0;1] | _,_,_ => [] end.
Definition drift_table : buckets := fun q s l => match q,l with
  | A6,0 => [0] | _,_ => [] end.

Example halted_source_allowed : indexed_check halt_tm 1 zero_dfa blank_table = true.
Proof. vm_compute. reflexivity. Qed.
Example duplicate_values_preserved : indexed_entries 1 duplicate_blank_table =
  [E A6 S092 0 0; E A6 S092 0 0].
Proof. reflexivity. Qed.
Example duplicate_values_semantically_safe : indexed_check halt_tm 1 zero_dfa duplicate_blank_table = true.
Proof. vm_compute. reflexivity. Qed.
Example missing_initial_rejected : indexed_check halt_tm 1 zero_dfa empty_table = false.
Proof. vm_compute. reflexivity. Qed.
Example out_of_range_right_rejected : indexed_check halt_tm 1 zero_dfa out_of_range_table = false.
Proof. vm_compute. reflexivity. Qed.
Example empty_state_domain_rejected : indexed_check halt_tm 0 zero_dfa blank_table = false.
Proof. vm_compute. reflexivity. Qed.
Example missing_pop_rejected : indexed_check drift_tm 1 zero_dfa blank_table = false.
Proof. vm_compute. reflexivity. Qed.
Example both_pop_symbols_retained : indexed_check drift_tm 1 zero_dfa drift_table = true.
Proof. vm_compute. reflexivity. Qed.
Example ignored_left_key_not_a_member : indexed_member 1 blank_table (E A6 S092 1 0) = false.
Proof. vm_compute. reflexivity. Qed.
Example duplicate_old_new_agree : indexed_check halt_tm 1 zero_dfa duplicate_blank_table =
  check halt_tm 1 zero_dfa (indexed_entries 1 duplicate_blank_table).
Proof. apply indexed_check_same. Qed.

Print Assumptions halted_source_allowed.
Print Assumptions duplicate_values_preserved.
Print Assumptions duplicate_values_semantically_safe.
Print Assumptions missing_initial_rejected.
Print Assumptions out_of_range_right_rejected.
Print Assumptions empty_state_domain_rejected.
Print Assumptions missing_pop_rejected.
Print Assumptions both_pop_symbols_retained.
Print Assumptions ignored_left_key_not_a_member.
Print Assumptions duplicate_old_new_agree.
