(* Deliberate wrong data, with kernel-checked rejection statements. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Projection.
From BusyCoq.EqvRegularPairs.Pair3 Require Import Frozen3 Projection Pair3.
From BusyCoq.EqvRegularPairs Require Import StateTransport.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.

Definition wrong_target : RI.TM := fun qs =>
  match qs with (D6,S092) => Some (S192,R,E6) | _ => mapped751 qs end.
Theorem wrong_target_diamond_rejected : forall l r,
  ~RI.step wrong_target (diamond_start l r) (diamond_end l r).
Proof. intros l r H. apply RI.step_c_spec in H. discriminate. Qed.
Definition wrong_label p := if Nat.eqb p 0 then S192 else bit_label p.
Example wrong_projection_rejected : projection_check 10 frozen3_delta wrong_label = false.
Proof. vm_compute. reflexivity. Qed.
Definition wrong_guard a : bool :=
  match control a,scanned a with
  | D6,S092 => SourceCtx.sym_eqb (bit_label (leftD a)) S192
  | _,_ => true
  end.
Example wrong_guard_rejected : forallb wrong_guard frozen3_invariant = false.
Proof. vm_compute. reflexivity. Qed.
Definition left_one_start := (D6,(Cons S192 (const S092),S092,const S092)).
Theorem missing_left_zero_rejected :
  ~RI.multistep frozen3 3 left_one_start (diamond_end (const S092) (const S092)).
Proof. intro H. apply RI.multistep_c_spec in H. discriminate. Qed.
Theorem identity_permutation_rejected : ~renames original751 mapped751 (fun q => q).
Proof.
  intros [_ H]. specialize (H E6 S092 S092 R A6 eq_refl). discriminate.
Qed.
Definition without_initial := filter (fun a => negb (entry_eqb a initial_entry)) frozen3_invariant.
Example missing_initial_rejected : check frozen3 10 frozen3_delta without_initial = false.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions wrong_target_diamond_rejected.
Print Assumptions wrong_projection_rejected.
Print Assumptions wrong_guard_rejected.
Print Assumptions missing_left_zero_rejected.
Print Assumptions identity_permutation_rejected.
Print Assumptions missing_initial_rejected.
