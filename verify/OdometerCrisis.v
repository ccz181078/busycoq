(** * The idealized crisis ladder — MECHANICS-ONLY (see OdometerLedger).

    Historical: this file proves the eight-rung [bit; win; a; a]-top
    ladder that the crisis-era design predicted. The ledger enumeration
    (tools/ledger.mjs) later showed the real orbit NEVER enters this
    family — the third counterfeit-seed lesson. The theorems are
    correct statements about an unreachable string family; they are
    kept because (a) dies7's string IS the real dying string (reproved
    as dies_final in OdometerLedger.v) and (b) rung3 documents the
    inner-a-spending mechanism in isolation. The real base-to-death
    chain lives in OdometerLedger.v. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip OdometerOrbit.
From Coq Require Import Lia NArith.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".

Open Scope N_scope.

Definition CAP : N := 16 ^ N.of_nat 70.
Definition NSPAN : nat := N.to_nat (CAP - 1).

Lemma CAP_nonzero : CAP <> 0.
Proof. apply N.pow_nonzero. discriminate. Qed.

Lemma dip_iter_add : forall m n W W' W'',
  dip_iter m W = Some W' ->
  dip_iter n W' = Some W'' ->
  dip_iter (m + n)%nat W = Some W''.
Proof.
  induction m; introv Hm Hn.
  - cbn [dip_iter] in Hm. injection Hm as <-. exact Hn.
  - cbn [Nat.add]. cbn [dip_iter] in Hm |- *.
    destruct (dip W) as [[| g Z1] |]; try discriminate.
    destruct g; try discriminate.
    eapply IHm; eassumption.
Qed.

Lemma span_iter : forall T,
  dip_iter NSPAN (spellW 70 0 T) = Some (spellW 70 (CAP - 1) T).
Proof.
  intro T.
  pose proof CAP_nonzero.
  replace (CAP - 1) with (0 + N.of_nat NSPAN)
    by (unfold NSPAN; rewrite N2Nat.id; lia).
  apply dip_iter_spell.
  unfold NSPAN. rewrite N2Nat.id.
  change (16 ^ N.of_nat 70) with CAP.
  lia.
Qed.

(** The eight rungs, tops [bit; win; inner; outer]. *)

Lemma rung0 : dip_iter 1 (spellW 70 (CAP - 1) [gO; gO; ga; ga])
            = Some (spellW 70 0 [gf; gO; ga; ga]).
Proof. vm_compute. reflexivity. Qed.

Lemma rung1 : dip_iter 1 (spellW 70 (CAP - 1) [gf; gO; ga; ga])
            = Some (spellW 70 0 [gO; ge; ga; ga]).
Proof. vm_compute. reflexivity. Qed.

Lemma rung2 : dip_iter 1 (spellW 70 (CAP - 1) [gO; ge; ga; ga])
            = Some (spellW 70 0 [gf; ge; ga; ga]).
Proof. vm_compute. reflexivity. Qed.

(** The exception: the carry probes past the full top and spends the
    inner boundary a (raw: `a f a O^212 f`). *)
Lemma rung3 : dip_iter 1 (spellW 70 (CAP - 1) [gf; ge; ga; ga])
            = Some (spellW 70 0 [gO; ga; gf; ga]).
Proof. vm_compute. reflexivity. Qed.

Lemma rung4 : dip_iter 1 (spellW 70 (CAP - 1) [gO; ga; gf; ga])
            = Some (spellW 70 0 [gf; ga; gf; ga]).
Proof. vm_compute. reflexivity. Qed.

Lemma rung5 : dip_iter 1 (spellW 70 (CAP - 1) [gf; ga; gf; ga])
            = Some (spellW 70 0 [gO; gf; gf; ga]).
Proof. vm_compute. reflexivity. Qed.

Lemma rung6 : dip_iter 1 (spellW 70 (CAP - 1) [gO; gf; gf; ga])
            = Some (spellW 70 0 [gf; gf; gf; ga]).
Proof. vm_compute. reflexivity. Qed.

(** Rung 7->8: the carry crosses the full top and the last boundary a;
    the walk falls off the written tape in state C — death. *)
Lemma dies7 : dip_dies (spellW 70 (CAP - 1) [gf; gf; gf; ga]) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ladder_step : forall T T',
  dip_iter 1 (spellW 70 (CAP - 1) T) = Some (spellW 70 0 T') ->
  dip_iter (NSPAN + 1)%nat (spellW 70 0 T) = Some (spellW 70 0 T').
Proof.
  introv H.
  eapply dip_iter_add.
  - apply span_iter.
  - exact H.
Qed.

Definition NCRISIS : nat := (7 * (NSPAN + 1) + NSPAN)%nat.

Lemma NCRISIS_val : N.of_nat NCRISIS = 8 * CAP - 1.
Proof.
  unfold NCRISIS, NSPAN.
  pose proof CAP_nonzero.
  rewrite Nat2N.inj_add, Nat2N.inj_mul, Nat2N.inj_add, !N2Nat.id.
  change (N.of_nat 7) with 7. change (N.of_nat 1) with 1.
  lia.
Qed.

(** 8*CAP - 1 sweeps from the crisis entry reach the dying string. *)
Theorem crisis_ladder :
  dip_iter NCRISIS (spellW 70 0 [gO; gO; ga; ga])
  = Some (spellW 70 (CAP - 1) [gf; gf; gf; ga]).
Proof.
  unfold NCRISIS.
  replace (7 * (NSPAN + 1) + NSPAN)%nat
    with ((NSPAN + 1) + ((NSPAN + 1) + ((NSPAN + 1) + ((NSPAN + 1) +
         ((NSPAN + 1) + ((NSPAN + 1) + ((NSPAN + 1) + NSPAN)))))))%nat
    by lia.
  eapply dip_iter_add. { exact (ladder_step _ _ rung0). }
  eapply dip_iter_add. { exact (ladder_step _ _ rung1). }
  eapply dip_iter_add. { exact (ladder_step _ _ rung2). }
  eapply dip_iter_add. { exact (ladder_step _ _ rung3). }
  eapply dip_iter_add. { exact (ladder_step _ _ rung4). }
  eapply dip_iter_add. { exact (ladder_step _ _ rung5). }
  eapply dip_iter_add. { exact (ladder_step _ _ rung6). }
  apply span_iter.
Qed.

(** Any anchor carrying the crisis-entry string halts. The structured
    era owes exactly one fact: c0 reaches such an anchor. *)
Theorem crisis_halts : forall m,
  halts tm (anchor (spellW 70 0 [gO; gO; ga; ga]) m).
Proof.
  intro m.
  unfold spellW.
  eapply halts_of_orbit_death.
  - exact crisis_ladder.
  - exact dies7.
Qed.
