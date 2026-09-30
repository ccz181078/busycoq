(* Constructive membership indexing only. The existing certificate_ok and
   reachable-configuration theorem are reused without modification. *)
From Coq Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From BusyCoq Require Import TM RegularInvariant62.
Import ListNotations.
Close Scope sym_scope.
Open Scope nat_scope.

Definition controls := [A6;B6;C6;D6;E6;F6].
Definition buckets := state6 -> sym92 -> nat -> list nat.
Definition indexed_entries n (table : buckets) : list entry :=
  flat_map (fun q => flat_map (fun s => flat_map
    (fun l => map (fun r => E q s l r) (table q s l)) (seq 0 n)) alphabet) controls.

Lemma controls_all q : In q controls.
Proof. destruct q; cbn; intuition congruence. Qed.

Lemma indexed_entries_member n table q s l r :
  In (E q s l r) (indexed_entries n table) <-> l < n /\ In r (table q s l).
Proof.
  unfold indexed_entries. rewrite in_flat_map. split.
  - intros [q0 [Hq H]]. apply in_flat_map in H as [s0 [Hs H]].
    apply in_flat_map in H as [l0 [Hl H]].
    apply in_map_iff in H as [r0 [Heq Hr]].
    inversion Heq; subst. split; [apply in_seq in Hl; lia | exact Hr].
  - intros [Hl Hr]. exists q. split; [apply controls_all |].
    apply in_flat_map. exists s. split; [apply alphabet_all |].
    apply in_flat_map. exists l. split; [apply in_seq; lia |].
    apply in_map. exact Hr.
Qed.

Definition indexed_member n table a : bool :=
  (leftD a <? n) && existsb (Nat.eqb (rightD a)) (table (control a) (scanned a) (leftD a)).

Lemma nat_existsb_true r xs : existsb (Nat.eqb r) xs = true <-> In r xs.
Proof.
  rewrite existsb_exists. split.
  - intros [x [Hx H]]. apply Nat.eqb_eq in H. now subst.
  - intros H. exists r. split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma indexed_member_true n table a :
  indexed_member n table a = true <-> In a (indexed_entries n table).
Proof.
  destruct a as [q s l r]. unfold indexed_member; cbn [leftD rightD control scanned].
  rewrite andb_true_iff, Nat.ltb_lt, nat_existsb_true, indexed_entries_member.
  reflexivity.
Qed.

Definition indexed_entry_check (tm : RI.TM) n d table a : bool :=
  match tm (control a, scanned a) with
  | None => true
  | Some (w,dir,q') => forallb (fun p => forallb (fun b =>
      negb (Nat.eqb (d p b) (pop_side a dir)) ||
      indexed_member n table (successor d a w dir q' b p)) alphabet) (seq 0 n)
  end.

Lemma indexed_entry_check_true tm n d table a :
  indexed_entry_check tm n d table a = true <->
  entry_ok tm n d (indexed_entries n table) a.
Proof.
  unfold indexed_entry_check, entry_ok.
  destruct (tm (control a, scanned a)) as [[[w dir] q']|] eqn:Htr.
  - rewrite forall_states_true. split.
    + intros H w' dir' q'' Heq p b Hp Hpop. inversion Heq; subst.
      specialize (H p Hp). apply forall_symbols_true with (b:=b) in H.
      apply implication_check in H. apply indexed_member_true. apply H. exact Hpop.
    + intros H p Hp. apply forall_symbols_true. intros b.
      apply implication_check. intros Hpop. apply indexed_member_true.
      eapply H; eauto.
  - split; [intros _ w dir q' H; discriminate | reflexivity].
Qed.

Definition indexed_check (tm : RI.TM) n d table : bool :=
  dfa_check n d && forallb (bounded_check n) (indexed_entries n table) &&
  indexed_member n table initial_entry &&
  forallb (indexed_entry_check tm n d table) (indexed_entries n table).

Theorem indexed_check_true tm n d table :
  indexed_check tm n d table = true <->
  certificate_ok tm n d (indexed_entries n table).
Proof.
  unfold indexed_check, certificate_ok. repeat rewrite andb_true_iff.
  rewrite dfa_check_true, indexed_member_true, !forallb_forall.
  setoid_rewrite bounded_check_true. setoid_rewrite indexed_entry_check_true. tauto.
Qed.

Theorem indexed_check_reachable tm n d table : indexed_check tm n d table = true ->
  forall c, RI.evstep tm RI.c0 c -> represented d (indexed_entries n table) c.
Proof.
  intros H. apply (check_reachable_invariant tm n d (indexed_entries n table)).
  apply (proj2 (check_true _ _ _ _)). apply (proj1 (indexed_check_true _ _ _ _)). exact H.
Qed.

Theorem indexed_check_same tm n d table :
  indexed_check tm n d table = check tm n d (indexed_entries n table).
Proof.
  destruct (indexed_check tm n d table) eqn:HX;
  destruct (check tm n d (indexed_entries n table)) eqn:HY; try reflexivity.
  - apply (proj1 (indexed_check_true _ _ _ _)) in HX.
    apply (proj2 (check_true _ _ _ _)) in HX. rewrite HY in HX. discriminate.
  - apply (proj1 (check_true _ _ _ _)) in HY.
    apply (proj2 (indexed_check_true _ _ _ _)) in HY. rewrite HX in HY. discriminate.
Qed.

Print Assumptions indexed_entries_member.
Print Assumptions indexed_member_true.
Print Assumptions indexed_entry_check_true.
Print Assumptions indexed_check_true.
Print Assumptions indexed_check_reachable.
Print Assumptions indexed_check_same.
