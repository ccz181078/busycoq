(* Kernel-checked controls for exact local transition and observation data. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Frozen220.
From BusyCoq.Eqv220723 Require Import Projection Pair220.
Import ListNotations.
Close Scope sym_scope.
Open Scope nat_scope.

(* One target-cell state edit: F0's next state F becomes E. *)
Definition wrong_target : RI.TM := fun qs =>
  match qs with (F6,S092) => Some (S192,R,E6) | _ => frozen723 qs end.

Example wrong_target_state :
  RI.step_c wrong_target (diamond_start (const S092) (const S092)) =
  Some (E6, (Cons S192 (const S092), S192, const S092)).
Proof. reflexivity. Qed.

Theorem wrong_target_diamond_rejected : forall l r,
  ~RI.step wrong_target (diamond_start l r) (diamond_end l r).
Proof. intros l r H. apply RI.step_c_spec in H. discriminate. Qed.

(* One DFA-label edit: state 3 is labeled zero rather than one. *)
Definition wrong_label p := if Nat.eqb p 3 then S092 else bit_label p.
Example wrong_projection_rejected : projection_check 16 frozen220_delta wrong_label = false.
Proof. vm_compute. reflexivity. Qed.

(* One guard-label edit: require right zero rather than right one at F0. *)
Definition wrong_guard a : bool :=
  match control a, scanned a with
  | F6,S092 => SourceCtx.sym_eqb (bit_label (rightD a)) S092
  | _,_ => true
  end.
Example wrong_guard_rejected : forallb wrong_guard frozen220_invariant = false.
Proof. vm_compute. reflexivity. Qed.

(* One right-cell edit also breaks the exact three-step local identity. *)
Definition right_zero_start := (F6, (const S092, S092, Cons S092 (const S092))).
Theorem missing_right_one_rejected :
  ~ RI.multistep frozen220 3 right_zero_start (diamond_end (const S092) (const S092)).
Proof. intros H. apply RI.multistep_c_spec in H. discriminate. Qed.

Print Assumptions wrong_target_diamond_rejected.
Print Assumptions wrong_projection_rejected.
Print Assumptions wrong_guard_rejected.
Print Assumptions missing_right_one_rejected.
