(** * The orbit: computing dip_iter over the counting eras.

    The regime-3 zone spells v in 4-bit groups of three cells
    [bit; win(1..2); win(2..3)]; a dip increments v. The increment
    lemma recurses on v/16 through all-ones groups and terminates in
    one of eight concrete byte patterns. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip.
From Coq Require Import Lia NArith.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".

Open Scope N_scope.

(** One 4-bit group as three cells, walk order: bit cell, low window
    ((b/2) mod 4), high window ((b/4) mod 4) — tabulated so reduction
    is a single match. *)
Definition gcells (b : N) : list glyph :=
  match b with
  | 0 => [gO; gO; gO] | 1 => [gf; gO; gO]
  | 2 => [gO; ge; gO] | 3 => [gf; ge; gO]
  | 4 => [gO; ga; ge] | 5 => [gf; ga; ge]
  | 6 => [gO; gf; ge] | 7 => [gf; gf; ge]
  | 8 => [gO; gO; ga] | 9 => [gf; gO; ga]
  | 10 => [gO; ge; ga] | 11 => [gf; ge; ga]
  | 12 => [gO; ga; gf] | 13 => [gf; ga; gf]
  | 14 => [gO; gf; gf] | _ => [gf; gf; gf]
  end.

(** G groups from v's low bits, shallowest first. *)
Fixpoint zgroups (G : nat) (v : N) : list glyph :=
  match G with
  | O => []
  | S G' => gcells (v mod 16) ++ zgroups G' (v / 16)
  end.

(** Fuel monotonicity. *)
Lemma dip_go_mono : forall fuel fuel' s deep shallow W',
  dip_go fuel s deep shallow = Some W' ->
  (fuel <= fuel')%nat ->
  dip_go fuel' s deep shallow = Some W'.
Proof.
  induction fuel; introv H Hle. { discriminate. }
  destruct fuel' as [| fuel']; [lia |].
  cbn in H; cbn.
  destruct s.
  1-4:
    destruct deep as [| g deep']; [discriminate |];
    destruct (instep _ g) as [[g' s'] |]; [| discriminate];
    destruct (is_inward s'); eapply IHfuel; try exact H; lia.
  - destruct shallow as [| g sh]; [discriminate |].
    destruct g; try discriminate.
    eapply IHfuel; [exact H | lia].
  - exact H.
Qed.

(** * Arithmetic helpers for 4-bit groups. *)

Lemma byte_lt : forall v : N, v mod 16 < 16.
Proof. intros. apply N.mod_lt. discriminate. Qed.

Lemma byte_S : forall v b, v mod 16 = b -> b < 15 ->
  (v + 1) mod 16 = b + 1 /\ (v + 1) / 16 = v / 16.
Proof.
  intros v b Hb Hlt.
  pose proof (N.div_mod v 16 ltac:(discriminate)) as Hd.
  assert (E : v + 1 = 16 * (v / 16) + (b + 1)) by lia.
  split.
  - symmetry. apply (N.mod_unique (v + 1) 16 (v / 16) (b + 1)); lia.
  - symmetry. apply (N.div_unique (v + 1) 16 (v / 16) (b + 1)); lia.
Qed.

Lemma byte_C : forall v, v mod 16 = 15 ->
  (v + 1) mod 16 = 0 /\ (v + 1) / 16 = v / 16 + 1.
Proof.
  intros v Hb.
  pose proof (N.div_mod v 16 ltac:(discriminate)) as Hd.
  assert (E : v + 1 = 16 * (v / 16 + 1) + 0) by lia.
  split.
  - symmetry. apply (N.mod_unique (v + 1) 16 (v / 16 + 1) 0); lia.
  - symmetry. apply (N.div_unique (v + 1) 16 (v / 16 + 1) 0); lia.
Qed.

Lemma pow16_S : forall G : nat, 16 ^ N.of_nat (S G) = 16 * 16 ^ N.of_nat G.
Proof.
  intros. rewrite Nat2N.inj_succ. rewrite N.pow_succ_r by lia. reflexivity.
Qed.

Lemma mod_split16 : forall v M, M <> 0 ->
  v mod (16 * M) = v mod 16 + 16 * ((v / 16) mod M).
Proof.
  intros v M HM.
  rewrite N.Div0.mod_mul_r. lia.
Qed.

Lemma carry_desc : forall v (G : nat),
  v mod 16 ^ N.of_nat (S G) <> 16 ^ N.of_nat (S G) - 1 ->
  v mod 16 = 15 ->
  (v / 16) mod 16 ^ N.of_nat G <> 16 ^ N.of_nat G - 1.
Proof.
  intros v G Hne Hb Heq.
  apply Hne.
  rewrite pow16_S.
  rewrite mod_split16 by (apply N.pow_nonzero; discriminate).
  rewrite Hb, Heq.
  pose proof (N.pow_nonzero 16 (N.of_nat G) ltac:(discriminate)).
  lia.
Qed.

(** * The increment walk, small-step.

    Profiling (P-2026-08-15-t): the memory pathology was the carry
    case asking cbn to bulldoze dip_go through symbolic fuel in one
    reduction. Split: crossing a full group is a 3-step lemma
    (zcross15); each non-full byte is its own lemma with its own Qed,
    so the checker frees each case before the next. Statements and the
    final zwalk interface are unchanged. *)

(** Crossing an all-ones group from C: three inward steps, three
    glyphs pushed, state C again. *)
Lemma zcross15 : forall fuel rest sh,
  dip_go (S (S (S fuel))) wC (gcells 15 ++ rest) sh
  = dip_go fuel wC rest (gf :: gf :: gf :: sh).
Proof.
  intros. cbn [gcells app dip_go instep is_inward]. reflexivity.
Qed.

Lemma zwalk_byte_0 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 0 ->
  (v + 1) mod 16 = 0 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_1 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 1 ->
  (v + 1) mod 16 = 1 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_2 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 2 ->
  (v + 1) mod 16 = 2 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_3 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 3 ->
  (v + 1) mod 16 = 3 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_4 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 4 ->
  (v + 1) mod 16 = 4 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_5 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 5 ->
  (v + 1) mod 16 = 5 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_6 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 6 ->
  (v + 1) mod 16 = 6 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_7 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 7 ->
  (v + 1) mod 16 = 7 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_8 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 8 ->
  (v + 1) mod 16 = 8 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_9 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 9 ->
  (v + 1) mod 16 = 9 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_10 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 10 ->
  (v + 1) mod 16 = 10 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_11 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 11 ->
  (v + 1) mod 16 = 11 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_12 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 12 ->
  (v + 1) mod 16 = 12 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_13 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 13 ->
  (v + 1) mod 16 = 13 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk_byte_14 : forall (G' : nat) (v : N) T sh,
  v mod 16 = 14 ->
  (v + 1) mod 16 = 14 + 1 ->
  (v + 1) / 16 = v / 16 ->
  dip_go (60 + (12 * S G' + length sh))%nat wC (zgroups (S G') v ++ T) sh
  = Some (unwind sh (zgroups (S G') (v + 1) ++ T)).
Proof.
  intros G' v T sh Hb Hm Hd.
  cbn [zgroups]. rewrite Hb, Hm, Hd.
  cbn [dip_go instep is_inward unwind toggle app gcells
       N.add Pos.add Pos.succ Nat.add Nat.mul length].
  reflexivity.
Qed.

Lemma zwalk : forall G v T sh,
  v mod 16 ^ N.of_nat G <> 16 ^ N.of_nat G - 1 ->
  dip_go (60 + (12 * G + length sh))%nat wC (zgroups G v ++ T) sh
  = Some (unwind sh (zgroups G (v + 1) ++ T)).
Proof.
  induction G as [| G' IHG']; intros v T sh Hne.
  { exfalso. apply Hne. cbn. rewrite N.mod_1_r. reflexivity. }
  assert (Hc : v mod 16 = 0 \/ v mod 16 = 1 \/ v mod 16 = 2 \/
               v mod 16 = 3 \/ v mod 16 = 4 \/ v mod 16 = 5 \/
               v mod 16 = 6 \/ v mod 16 = 7 \/ v mod 16 = 8 \/
               v mod 16 = 9 \/ v mod 16 = 10 \/ v mod 16 = 11 \/
               v mod 16 = 12 \/ v mod 16 = 13 \/ v mod 16 = 14 \/
               v mod 16 = 15)
    by (pose proof (byte_lt v); lia).
  destruct Hc as
    [Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|Hb]]]]]]]]]]]]]]].

  - destruct (byte_S v 0 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_0 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 1 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_1 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 2 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_2 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 3 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_3 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 4 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_4 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 5 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_5 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 6 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_6 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 7 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_7 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 8 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_8 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 9 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_9 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 10 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_10 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 11 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_11 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 12 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_12 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 13 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_13 G' v T sh Hb Hm Hd).
  - destruct (byte_S v 14 Hb ltac:(lia)) as [Hm Hd].
    exact (zwalk_byte_14 G' v T sh Hb Hm Hd).
  - (* the carry: byte 15, cross in three steps, recurse on v/16 *)
    destruct (byte_C v Hb) as [Hm Hd].
    cbn [zgroups]. rewrite Hb, Hm, Hd.
    replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (69 + (12 * G' + length sh)))))%nat by lia.
    rewrite <- app_assoc.
    rewrite zcross15.
    cbn [gcells app].
    eapply dip_go_mono.
    + apply (IHG' (v / 16) T (gf :: gf :: gf :: sh)).
      eapply carry_desc; eauto.
    + cbn [length]. lia.
Qed.

(** * From walk to sweeps: the counting run. *)

Lemma gcells_len : forall b, length (gcells b) = 3%nat.
Proof.
  intros b. unfold gcells.
  destruct b as [| p]; [reflexivity |].
  repeat (destruct p; try reflexivity).
Qed.

Lemma zgroups_len : forall G v, length (zgroups G v) = (3 * G)%nat.
Proof.
  induction G; intros; cbn [zgroups].
  - reflexivity.
  - rewrite app_length, gcells_len, IHG. lia.
Qed.

(** The counting anchor string: separator, cell 0, the groups, then an
    arbitrary deeper suffix T (top cells + boundary, untouched while
    the carry stays inside the groups). *)
Definition spellW (G : nat) (v : N) (T : list glyph) : list glyph :=
  gf :: gO :: zgroups G v ++ T.

(** Entering the dip: F eats the separator, A eats the head cell,
    hand off to the group walk in C. Two steps, stated small. *)
Lemma dip_enter : forall fuel rest,
  dip_go (S (S fuel)) wF (gf :: gO :: rest) []
  = dip_go fuel wC rest [gf; gf].
Proof.
  intros. cbn [dip_go instep is_inward]. reflexivity.
Qed.

Lemma dip_spell : forall G v T,
  v mod 16 ^ N.of_nat G <> 16 ^ N.of_nat G - 1 ->
  dip (spellW G v T) = Some (gO :: gO :: zgroups G (v + 1) ++ T).
Proof.
  intros G v T Hne.
  unfold dip, spellW.
  eapply dip_go_mono.
  - instantiate (1 := (S (S (60 + (12 * G + length [gf; gf]))))%nat).
    rewrite dip_enter.
    rewrite (zwalk G v T [gf; gf] Hne).
    reflexivity.
  - cbn [length]. rewrite app_length, zgroups_len. lia.
Qed.

Lemma dip_iter_spell : forall n G v T,
  v + N.of_nat n < 16 ^ N.of_nat G ->
  dip_iter n (spellW G v T) = Some (spellW G (v + N.of_nat n) T).
Proof.
  induction n; intros G v T Hlt.
  - cbn. rewrite N.add_0_r. reflexivity.
  - cbn [dip_iter].
    assert (Hv : v < 16 ^ N.of_nat G) by lia.
    assert (Hne : v mod 16 ^ N.of_nat G <> 16 ^ N.of_nat G - 1).
    { rewrite N.mod_small by exact Hv. lia. }
    rewrite (dip_spell G v T Hne).
    replace (v + N.of_nat (S n)) with (v + 1 + N.of_nat n) by lia.
    apply IHn. lia.
Qed.
