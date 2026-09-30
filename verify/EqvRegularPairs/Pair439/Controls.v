(* Deliberate wrong data; all rejection statements concern the exact RI instance. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Projection.
From BusyCoq.EqvRegularPairs.Pair439 Require Import Frozen439 Projection Pair439.
From BusyCoq.EqvRegularPairs Require Import StateTransport.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.
Definition wrong_target : RI.TM := fun qs =>
  match qs with (B6,S092) => Some (S192,L,F6) | _ => mapped600 qs end.
Theorem wrong_target_diamond_rejected : forall l r,
  ~RI.step wrong_target (diamond_start l r) (diamond_end l r).
Proof. intros l r H. apply RI.step_c_spec in H. discriminate. Qed.
Definition wrong_label p := if Nat.eqb p 0 then S192 else bit_label p.
Example wrong_projection_rejected : projection_check 10 frozen439_delta wrong_label = false.
Proof. vm_compute. reflexivity. Qed.
Definition wrong_guard a : bool :=
  match control a,scanned a with
  | B6,S092 => SourceCtx.sym_eqb (bit_label (rightD a)) S192
  | _,_ => true
  end.
Example wrong_guard_rejected : forallb wrong_guard frozen439_invariant = false.
Proof. vm_compute. reflexivity. Qed.
Definition right_one_start := (B6,(const S092,S092,Cons S192 (const S092))).
Theorem missing_right_zero_rejected :
  ~RI.multistep frozen439 3 right_one_start (diamond_end (const S092) (const S092)).
Proof. intro H. apply RI.multistep_c_spec in H. discriminate. Qed.
Theorem identity_permutation_rejected : ~renames original600 mapped600 (fun q => q).
Proof.
  intros [_ H]. specialize (H C6 S092 S092 L F6 eq_refl). discriminate.
Qed.
Definition without_initial := filter (fun a => negb (entry_eqb a initial_entry)) frozen439_invariant.
Example missing_initial_rejected : check frozen439 10 frozen439_delta without_initial = false.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions wrong_target_diamond_rejected.
Print Assumptions wrong_projection_rejected.
Print Assumptions wrong_guard_rejected.
Print Assumptions missing_right_zero_rejected.
Print Assumptions identity_permutation_rejected.
Print Assumptions missing_initial_rejected.
