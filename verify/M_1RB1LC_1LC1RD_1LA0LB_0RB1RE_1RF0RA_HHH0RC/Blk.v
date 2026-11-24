(** Soundness of a block of Check.v. *)
From Coq Require Import ZArith Lia List Uint63 PArray Bool PeanoNat.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check Visits Block Tab Arith.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).
Opaque TP.

Lemma chunk_spec Q sh st off E st' off' E' Ai Bi :
  φ sh <= 62 -> φ st = Ai mod 2 + 2 * ((Ai + Bi) mod 2) ->
  chunk TP Q sh st off E = (st', off', E') ->
  let bt := (φ Q / 2 ^ φ sh) mod 4096 in
  exists q ds,
    (let '(A, B) := drun (bits12 bt) (Ai, Bi) in
     B - A = 4096 * (Bi - Ai) - (Ai + Bi) * (2 * bt - 4095) + q /\ A + B = Ai + Bi + ds /\
     φ st' = A mod 2 + 2 * ((A + B) mod 2)) /\
    - 2 ^ 20 < q < 2 ^ 20 /\ 0 <= ds <= 48 /\
    cg φ off' (φ off + ds) /\ cg φ E' (φ E + (φ off * (2 * bt - 4095) - q) * 2 ^ φ sh).
Proof.
  intros Hsh Hst C bt. unfold chunk in C.
  remember (TP.[(st << 12) + (Q >> sh) land 4095]) as v eqn:Hv.
  injection C as <- <- <-.
  assert (Hbt : φ ((Q >> sh) land 4095) = bt) by (rewrite land_4095, lsr_spec; reflexivity).
  assert (Hbt' : 0 <= bt < 4096) by (unfold bt; apply Z.mod_pos_bound; lia).
  set (k := φ st * 4096 + bt).
  assert (Hk : φ ((st << 12) + (Q >> sh) land 4095) = k).
  { rewrite add_spec, lsl_spec, Hbt. change φ 12 with 12. unfold k. change wB with (2 ^ 63).
    clear Hv. lia. }
  assert (Hk' : 0 <= k < 16384) by (unfold k; lia).
  pose proof (TP_spec k Hk') as T. unfold ent_ok in T.
  replace (k / 4096) with (φ st) in T by (unfold k; lia).
  replace (k mod 4096) with bt in T by (unfold k; lia).
  rewrite <- Hk, of_to_Z in T.
  replace (φ st mod 2) with (Ai mod 2) in T by lia.
  replace (φ st / 2) with ((Ai + Bi) mod 2) in T by lia.
  pose proof (chunk_inv (bits12 bt) Ai Bi) as CI.
  destruct (zfold (bits12 bt) (Ai mod 2) ((Ai + Bi) mod 2)) as [[[q ds] ap] sp].
  rewrite !andb_true_iff in T. rewrite <- Hv in T.
  destruct T as [[[[[[[T1 T2] T3] T4] T5] T6] T7] T8].
  apply Z.eqb_eq in T1, T2, T3, T8. apply Z.ltb_lt in T4, T5. apply Z.leb_le in T6, T7.
  rewrite bits12_length, T8 in CI. change (2 ^ Z.of_nat 12) with 4096 in CI.
  exists q, ds. destruct (drun (bits12 bt) (Ai, Bi)) as [A B]. destruct CI as (C1 & C2 & C3 & C4).
  split; [split; [lia | split; [lia | rewrite T1; lia]]|].
  split; [lia|]. split; [lia|]. split.
  - eapply cg_trans; [apply cg_phi_add|]. rewrite T2. apply cg_refl.
  - eapply cg_trans; [apply cg_phi_add|]. apply cg_add; [apply cg_refl|].
    eapply cg_trans; [apply cg_phi_lsl|]. apply cg_mul; [|apply cg_refl].
    eapply cg_trans; [apply cg_phi_sub|]. apply cg_sub.
    + eapply cg_trans; [apply cg_phi_mul|]. apply cg_mul; [apply cg_refl|].
      eapply cg_trans; [apply cg_phi_sub|]. apply cg_sub; [|apply cg_refl].
      eapply cg_trans; [apply cg_phi_mul|]. rewrite Hbt. apply cg_refl.
    + apply (cg_trans _ (q mod wB)); [unfold cg; f_equal; exact T3|apply cg_mod].
Qed.
