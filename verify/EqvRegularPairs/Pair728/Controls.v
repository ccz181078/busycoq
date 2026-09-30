(* Pair728-specific false data and kernel-checked rejection statements. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Projection.
From BusyCoq.EqvRegularPairs.Pair728 Require Import Frozen728 Projection Pair728.
From BusyCoq.EqvRegularPairs Require Import StateTransport.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.

Definition wrong_target : RI.TM := fun qs =>
  match qs with (B6,S092) => Some (S192,L,D6) | _ => mapped772 qs end.
Theorem wrong_target_diamond_rejected : forall l r,
  ~RI.step wrong_target (diamond_start l r) (diamond_end l r).
Proof. intros l r H. apply RI.step_c_spec in H. discriminate. Qed.

Definition wrong_label p := if Nat.eqb p 0 then S192 else bit_label p.
Example wrong_projection_rejected : projection_check 10 frozen728_delta wrong_label = false.
Proof. vm_compute. reflexivity. Qed.

Definition wrong_guard a : bool :=
  match control a,scanned a with
  | B6,S092 => Nat.eqb (rightD a) 1
  | _,_ => true
  end.
Example wrong_guard_rejected : forallb wrong_guard frozen728_invariant = false.
Proof. vm_compute. reflexivity. Qed.

Definition right_one_start := (B6,(const S092,S092,Cons S192 (const S092))).
Definition right_one_halt := (C6,(Cons S092 (const S092),S192,const S092)).
Theorem right_one_halts_after_one :
  RI.step frozen728 right_one_start right_one_halt /\ RI.halted frozen728 right_one_halt.
Proof. split; [apply RI.step_c_spec |]; reflexivity. Qed.
Theorem missing_right_zero_rejected :
  ~RI.multistep frozen728 3 right_one_start (diamond_end (const S092) (const S092)).
Proof. intro H. apply RI.multistep_c_spec in H. discriminate. Qed.

Theorem identity_permutation_rejected : ~renames original772 mapped772 (fun q => q).
Proof.
  intros [_ H]. specialize (H A6 S192 S092 R D6 eq_refl). discriminate.
Qed.
Theorem wrong_inverse_direction_rejected :
  ~renames mapped772 original772 original_to_mapped_state.
Proof.
  intros [_ H]. specialize (H C6 S092 S092 L D6 eq_refl). discriminate.
Qed.
Theorem not_an_involution :
  original_to_mapped_state (original_to_mapped_state C6) <> C6.
Proof. discriminate. Qed.

Definition without_initial := filter (fun a => negb (entry_eqb a initial_entry)) frozen728_invariant.
Example missing_initial_rejected : check frozen728 10 frozen728_delta without_initial = false.
Proof. vm_compute. reflexivity. Qed.
Definition without_terminal := filter (fun a =>
  match frozen728 (control a,scanned a) with None => false | Some _ => true end)
  frozen728_invariant.
Example missing_terminal_rejected : check frozen728 10 frozen728_delta without_terminal = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions wrong_target_diamond_rejected.
Print Assumptions wrong_projection_rejected.
Print Assumptions wrong_guard_rejected.
Print Assumptions right_one_halts_after_one.
Print Assumptions missing_right_zero_rejected.
Print Assumptions identity_permutation_rejected.
Print Assumptions wrong_inverse_direction_rejected.
Print Assumptions not_an_involution.
Print Assumptions missing_initial_rejected.
Print Assumptions missing_terminal_rejected.
