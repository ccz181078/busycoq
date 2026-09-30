(* Halt-tolerant finite regular invariants for the standard raw TM semantics.
   This unit proves reachability containment, never nonhalting or equivalence. *)
From Coq Require Import Bool.Bool Lists.List Lists.Streams Arith.PeanoNat Lia.
From BusyCoq Require Import Individual62.
Notation state6 := BB62.state.
Notation sym92 := BB62.sym.
Notation A6 := BB62.A.
Notation B6 := BB62.B.
Notation C6 := BB62.C.
Notation D6 := BB62.D.
Notation E6 := BB62.E.
Notation F6 := BB62.F.
Notation S092 := BB62.S0.
Notation S192 := BB62.S1.
Module SourceCtx := BB62.BB62.
Import ListNotations.
Close Scope sym_scope.
Open Scope nat_scope.

Module RI := Individual62.Enumerate.Permute.Flip.Compute.TM.

Record entry := E { control : state6; scanned : sym92; leftD : nat; rightD : nat }.
Definition DFA := nat -> sym92 -> nat.
Definition alphabet := [S092; S192].

Definition entry_eqb (a b : entry) : bool :=
  SourceCtx.q_eqb (control a) (control b) &&
  SourceCtx.sym_eqb (scanned a) (scanned b) &&
  Nat.eqb (leftD a) (leftD b) && Nat.eqb (rightD a) (rightD b).

Lemma entry_eqb_true a b : entry_eqb a b = true <-> a = b.
Proof.
  destruct a as [q s l r], b as [q' s' l' r']; unfold entry_eqb; cbn.
  repeat rewrite andb_true_iff. repeat rewrite Nat.eqb_eq.
  destruct (SourceCtx.q_eqb_spec q q'); destruct (SourceCtx.sym_eqb_spec s s');
    cbn; split; intros H; try discriminate; intuition congruence.
Qed.

Definition member (a : entry) (I : list entry) := existsb (entry_eqb a) I.
Lemma member_true a I : member a I = true <-> In a I.
Proof.
  unfold member; rewrite existsb_exists. split.
  - intros [x [Hx Heq]]. apply entry_eqb_true in Heq. now subst.
  - intros Ha. exists a. split; [exact Ha | apply entry_eqb_true; reflexivity].
Qed.

Lemma alphabet_all b : In b alphabet.
Proof. destruct b; cbn; auto. Qed.

Lemma forall_states_true n f :
  forallb f (seq 0 n) = true <-> forall p, p < n -> f p = true.
Proof.
  rewrite forallb_forall. split; intros H p Hp; apply H.
  - apply in_seq. lia.
  - apply in_seq in Hp. lia.
Qed.

Lemma forall_symbols_true f :
  forallb f alphabet = true <-> forall b, f b = true.
Proof.
  rewrite forallb_forall. split.
  - intros H b. apply H, alphabet_all.
  - intros H b _. apply H.
Qed.

Definition dfa_check (n : nat) (d : DFA) : bool :=
  (0 <? n) && Nat.eqb (d 0 S092) 0 &&
  forallb (fun p => forallb (fun b => d p b <? n) alphabet) (seq 0 n).

Definition dfa_ok (n : nat) (d : DFA) : Prop :=
  0 < n /\ d 0 S092 = 0 /\ forall p b, p < n -> d p b < n.

Lemma dfa_check_true n d : dfa_check n d = true <-> dfa_ok n d.
Proof.
  unfold dfa_check, dfa_ok.
  repeat rewrite andb_true_iff. rewrite Nat.ltb_lt, Nat.eqb_eq.
  rewrite forall_states_true. split.
  - intros [[Hn Hz] Hd]. repeat split; try assumption.
    intros p b Hp. apply Nat.ltb_lt. pose proof (Hd p Hp) as Hpb.
    apply forall_symbols_true with (b:=b) in Hpb. exact Hpb.
  - intros [Hn [Hz Hd]]. repeat split; try assumption.
    intros p Hp. apply forall_symbols_true. intros b. apply Nat.ltb_lt, Hd, Hp.
Qed.

Definition bounded (n : nat) (a : entry) := leftD a < n /\ rightD a < n.
Definition bounded_check n a : bool := (leftD a <? n) && (rightD a <? n).
Lemma bounded_check_true n a : bounded_check n a = true <-> bounded n a.
Proof. unfold bounded_check, bounded. rewrite andb_true_iff, !Nat.ltb_lt. reflexivity. Qed.

Definition successor (d : DFA) (a : entry) (w : sym92) (dir : dir)
  (q' : state6) (b : sym92) (p : nat) : entry :=
  match dir with
  | L => E q' b p (d (rightD a) w)
  | R => E q' b (d (leftD a) w) p
  end.
Definition pop_side (a : entry) (dir : dir) :=
  match dir with L => leftD a | R => rightD a end.

Definition entry_check (tm : RI.TM) n d I a : bool :=
  match tm (control a, scanned a) with
  | None => true
  | Some (w, dir, q') =>
    forallb (fun p => forallb (fun b =>
      negb (Nat.eqb (d p b) (pop_side a dir)) ||
      member (successor d a w dir q' b p) I) alphabet) (seq 0 n)
  end.

Definition entry_ok (tm : RI.TM) n d I a : Prop :=
  forall w dir q', tm (control a, scanned a) = Some (w, dir, q') ->
    forall p b, p < n -> d p b = pop_side a dir ->
      In (successor d a w dir q' b p) I.

Lemma implication_check x y z :
  (negb (Nat.eqb x y) || z) = true <-> (x = y -> z = true).
Proof.
  destruct (Nat.eqb_spec x y); subst; cbn; intuition congruence.
Qed.

Lemma entry_check_true tm n d I a : entry_check tm n d I a = true <-> entry_ok tm n d I a.
Proof.
  unfold entry_check, entry_ok.
  destruct (tm (control a, scanned a)) as [[[w dir] q'] |] eqn:Htr.
  - rewrite forall_states_true. split.
    + intros H w' dir' q'' Heq p b Hp Hpop. inversion Heq; subst.
      specialize (H p Hp). apply forall_symbols_true with (b:=b) in H.
      apply implication_check in H. apply member_true. apply H. exact Hpop.
    + intros H p Hp. apply forall_symbols_true. intros b.
      apply implication_check. intros Hpop. apply member_true.
      eapply H; eauto.
  - split; [intros _ w dir q' H; discriminate | reflexivity].
Qed.

Definition initial_entry := E A6 S092 0 0.
Definition check (tm : RI.TM) n d I : bool :=
  dfa_check n d && forallb (bounded_check n) I && member initial_entry I &&
  forallb (entry_check tm n d I) I.

Definition certificate_ok (tm : RI.TM) n d I : Prop :=
  dfa_ok n d /\ (forall a, In a I -> bounded n a) /\
  In initial_entry I /\ (forall a, In a I -> entry_ok tm n d I a).

Theorem check_true tm n d I : check tm n d I = true <-> certificate_ok tm n d I.
Proof.
  unfold check, certificate_ok. repeat rewrite andb_true_iff.
  rewrite dfa_check_true, member_true, !forallb_forall.
  setoid_rewrite bounded_check_true. setoid_rewrite entry_check_true. tauto.
Qed.

Theorem check_reflect tm n d I : Bool.reflect (certificate_ok tm n d I) (check tm n d I).
Proof.
  destruct (check tm n d I) eqn:H; constructor.
  - now apply check_true.
  - intros Hok. apply check_true in Hok. congruence.
Qed.

(* Lists are nearest-first; DFA evaluation is remote-to-near. *)
Fixpoint classify (d : DFA) (xs : list sym92) : nat :=
  match xs with [] => 0 | b :: tail => d (classify d tail) b end.
Fixpoint finite_side (xs : list sym92) : Stream sym92 :=
  match xs with [] => const S092 | b :: tail => Cons b (finite_side tail) end.

Lemma classify_bound n d : dfa_ok n d -> forall xs, classify d xs < n.
Proof.
  intros [Hn [Hz Hd]] xs. induction xs; cbn; auto.
Qed.

Lemma classify_padding d : d 0 S092 = 0 -> forall xs k,
  classify d (xs ++ repeat S092 k) = classify d xs.
Proof.
  intros Hz xs; induction xs as [|b xs IH]; intros k; cbn.
  - induction k; cbn; [reflexivity | now rewrite IHk].
  - now rewrite IH.
Qed.

Lemma finite_side_padding xs k :
  finite_side (xs ++ repeat S092 k) = finite_side xs.
Proof.
  induction xs as [|b xs IH]; cbn.
  - induction k; cbn; [reflexivity | rewrite IHk; symmetry; apply const_unfold].
  - now rewrite IH.
Qed.

Definition popped (xs : list sym92) := List.hd S092 xs.
Definition remainder (xs : list sym92) := List.tl xs.

Lemma finite_pop d xs : d 0 S092 = 0 ->
  Streams.hd (finite_side xs) = popped xs /\
  Streams.tl (finite_side xs) = finite_side (remainder xs) /\
  d (classify d (remainder xs)) (popped xs) = classify d xs.
Proof. destruct xs; cbn; intros H; repeat split; assumption || reflexivity. Qed.

Definition represented d I (c : state6 * RI.tape) : Prop :=
  exists q s l r, c = (q, (finite_side l, s, finite_side r)) /\
    In (E q s (classify d l) (classify d r)) I.

Theorem represented_step tm n d I : certificate_ok tm n d I ->
  forall c c', represented d I c -> RI.step tm c c' -> represented d I c'.
Proof.
  intros [HD [HB [HI HC]]] c c' [q [s [l [r [Heq Hin]]]]] Hstep.
  subst c. destruct HD as [Hn [Hz Hd]]. inversion Hstep; subst.
  - destruct (finite_pop d l Hz) as [Hhead [Htail Hpop]].
    exists q', (popped l), (remainder l), (s' :: r).
    split.
    + destruct l; reflexivity.
    + specialize (HC _ Hin). unfold entry_ok in HC.
      specialize (HC s' L q'). cbn in HC.
      apply (HC H4 (classify d (remainder l)) (popped l)).
      * apply classify_bound with (n:=n). repeat split; assumption.
      * exact Hpop.
  - destruct (finite_pop d r Hz) as [Hhead [Htail Hpop]].
    exists q', (popped r), (s' :: l), (remainder r).
    split.
    + destruct r; reflexivity.
    + specialize (HC _ Hin). unfold entry_ok in HC.
      specialize (HC s' R q'). cbn in HC.
      apply (HC H4 (classify d (remainder r)) (popped r)).
      * apply classify_bound with (n:=n). repeat split; assumption.
      * exact Hpop.
Qed.

Theorem check_reachable_invariant tm n d I : check tm n d I = true ->
  forall c, RI.evstep tm RI.c0 c -> represented d I c.
Proof.
  intros Hcheck. apply check_true in Hcheck.
  assert (Hstart : represented d I RI.c0).
  { exists A6, S092, (@nil sym92), (@nil sym92). split; [reflexivity | exact (proj1 (proj2 (proj2 Hcheck)))]. }
  assert (Hpres : forall c c', RI.evstep tm c c' -> represented d I c -> represented d I c').
  { intros c c' Hev. induction Hev; intros HP; [exact HP |].
    apply IHHev. eapply represented_step; eauto. }
  intros c Hreach. eapply Hpres; eauto.
Qed.

Print Assumptions check_reflect.
Print Assumptions finite_side_padding.
Print Assumptions represented_step.
Print Assumptions check_reachable_invariant.
