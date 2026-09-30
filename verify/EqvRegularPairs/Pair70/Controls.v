(* New controls distinguish the paired terminal branch from a shared endpoint. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Projection.
From BusyCoq.EqvRegularPairs.Pair70 Require Import Frozen70 Projection Pair70.
From BusyCoq.EqvRegularPairs Require Import StateTransport.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.
Definition wrong_target : RI.TM := fun qs =>
  match qs with (B6,S092) => Some (S192,R,C6) | _ => mapped223 qs end.
Theorem wrong_target_diamond_rejected : forall l r,
  ~RI.step wrong_target (diamond_start l r) (diamond_end l r).
Proof. intros l r H. apply RI.step_c_spec in H. discriminate. Qed.
Definition wrong_label p := if Nat.eqb p 0 then S192 else bit_label p.
Example wrong_projection_rejected : projection_check 17 frozen70_delta wrong_label = false.
Proof. vm_compute. reflexivity. Qed.
Definition bad_zero_delta p b :=
  match p,b with 1,S092 => 0 | _,_ => frozen70_delta p b end.
Example extra_zero_predecessor_rejected : zero_class_check 17 bad_zero_delta = false.
Proof. vm_compute. reflexivity. Qed.
Example one_bit_observer_is_insufficient : projection_check 17 bad_zero_delta bit_label = true.
Proof. vm_compute. reflexivity. Qed.
Example bad_zero_finite_word : classify bad_zero_delta [S092;S192] = 0.
Proof. reflexivity. Qed.
Definition left_one_only_guard a := match control a,scanned a with
  | B6,S092 => SourceCtx.sym_eqb (bit_label (leftD a)) S192 | _,_ => true end.
Example deleting_terminal_domain_rejected : forallb left_one_only_guard frozen70_invariant = false.
Proof. vm_compute. reflexivity. Qed.
Definition config_right_head (c : state6 * RI.tape) : sym92 :=
  match c with (_,((_,_),r)) => Streams.hd r end.
Theorem terminal_configurations_differ :
  source_terminal_end (const S092) <> target_terminal_end (const S092).
Proof.
  intro H. pose proof (f_equal config_right_head H) as E.
  cbn [config_right_head source_terminal_end target_terminal_end] in E. discriminate.
Qed.
Definition terminal_right_one := (B6,(const S092,S092,Cons S192 (const S092))).
Theorem missing_right_zero_rejected :
  ~RI.multistep mapped223 5 terminal_right_one (target_terminal_end (const S092)).
Proof. intro H. apply RI.multistep_c_spec in H. discriminate. Qed.
Theorem zero_progress_rejected :
  ~RI.multistep frozen70 0 (diamond_start (const S092) (const S092))
    (diamond_end (const S092) (const S092)).
Proof. intro H. apply RI.multistep_c_spec in H. discriminate. Qed.
Theorem identity_permutation_rejected : ~renames original223 mapped223 (fun q => q).
Proof. intros [_ H]. specialize (H E6 S192 S092 L D6 eq_refl). discriminate. Qed.
Definition without_initial := filter (fun a => negb (entry_eqb a initial_entry)) frozen70_invariant.
Example missing_initial_rejected : check frozen70 17 frozen70_delta without_initial = false.
Proof. vm_compute. reflexivity. Qed.
Theorem zero_head_is_not_blank : finite_side [S092;S192] <> const S092.
Proof.
  intro H. pose proof (f_equal (fun s => Streams.hd (Streams.tl s)) H) as E.
  cbn [finite_side] in E. discriminate.
Qed.
Print Assumptions wrong_target_diamond_rejected.
Print Assumptions wrong_projection_rejected.
Print Assumptions extra_zero_predecessor_rejected.
Print Assumptions one_bit_observer_is_insufficient.
Print Assumptions bad_zero_finite_word.
Print Assumptions deleting_terminal_domain_rejected.
Print Assumptions terminal_configurations_differ.
Print Assumptions missing_right_zero_rejected.
Print Assumptions zero_progress_rejected.
Print Assumptions identity_permutation_rejected.
Print Assumptions missing_initial_rejected.
Print Assumptions zero_head_is_not_blank.
