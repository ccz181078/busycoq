(** Soundness of [blk]: an accepted block of K visits is K visits of [op]. *)
From Coq Require Import ZArith Lia List Uint63 PArray Bool PeanoNat.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check Visits Block Tab Arith Cmp Blk.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).
Opaque TP.

(** After the chunks of the digits of Q above bit sh (n digits, the list L): the formal run from (a, b) is
    tracked exactly up to an error e, known modulo 2^63 as E / 2^sh. *)
Definition inv (a b s : Z) (Q : int) (sh n : Z) (L : list bool) (st off E : int) (e : Z) : Prop :=
  let '(A, B) := drun L (a, b) in
  B - A = 2 ^ n * (b - a) - s * (2 * (φ Q / 2 ^ sh) - 2 ^ n + 1) - e /\
  A + B = s + φ off /\ φ st = A mod 2 + 2 * ((A + B) mod 2) /\ cg φ E (e * 2 ^ sh) /\
  Z.of_nat (List.length L) = n.

Lemma inv_init a b Q K st : 0 <= K -> 0 <= φ Q < 2 ^ K -> φ st = a mod 2 + 2 * ((a + b) mod 2) ->
  inv a b (a + b) Q K 0 [] st 0 0 0.
Proof.
  intros HK HQ Hst. unfold inv. cbn [drun List.length]. rewrite Z.div_small by lia.
  split; [rewrite Z.pow_0_r; ring|]. split; [change φ 0 with 0; ring|]. split; [exact Hst|].
  split; [apply cg_refl|reflexivity].
Qed.

Lemma inv_step a b s Q sh n L st off E e sh' st' off' E' :
  φ sh' + 12 = sh -> φ sh' <= 62 -> 0 <= n -> 0 <= φ off <= 96 ->
  inv a b s Q sh n L st off E e -> chunk TP Q sh' st off E = (st', off', E') ->
  exists e', inv a b s Q (φ sh') (n + 12) (L ++ bits12 ((φ Q / 2 ^ φ sh') mod 4096)) st' off' E' e' /\
    Z.abs e' <= 4096 * Z.abs e + 2 ^ 21 /\ φ off <= φ off' <= φ off + 48.
Proof.
  intros Hsh Hsh62 Hn Hoff I C. unfold inv in *. rewrite drun_app.
  destruct (drun L (a, b)) as [A B] eqn:HL. destruct I as (D & S & Hst & CE & Len).
  destruct (chunk_spec Q sh' st off E st' off' E' A B Hsh62 Hst C) as (q & ds & R & Hq & Hds & Coff & CE').
  set (bt := (φ Q / 2 ^ φ sh') mod 4096) in *.
  destruct (drun (bits12 bt) (A, B)) as [A' B']. destruct R as (D' & S' & Hst').
  assert (Ho : φ off' = φ off + ds) by (apply cg_phi; [exact Coff|change wB with (2 ^ 63); lia]).
  pose proof (to_Z_bounded sh') as Bsh.
  assert (HP : φ Q / 2 ^ φ sh' = 4096 * (φ Q / 2 ^ sh) + bt).
  { unfold bt. subst sh. rewrite Z.pow_add_r, <- Z.div_div by lia. change (2 ^ 12) with 4096.
    apply Z.div_mod. lia. }
  assert (Hbt : 0 <= bt < 4096) by (unfold bt; apply Z.mod_pos_bound; lia).
  exists (4096 * e + φ off * (2 * bt - 4095) - q). split; [|split].
  - split; [|split; [|split; [|split]]].
    + rewrite D', S, D, HP, Z.pow_add_r by lia. change (2 ^ 12) with 4096. ring.
    + lia.
    + exact Hst'.
    + eapply cg_trans; [exact CE'|].
      replace ((4096 * e + φ off * (2 * bt - 4095) - q) * 2 ^ φ sh')
        with (e * 2 ^ sh + (φ off * (2 * bt - 4095) - q) * 2 ^ φ sh')
        by (subst sh; rewrite Z.pow_add_r by lia; change (2 ^ 12) with 4096; ring).
      apply cg_add; [exact CE|apply cg_refl].
    + rewrite List.length_app, bits12_length. lia.
  - assert (- (96 * 4095) <= φ off * (2 * bt - 4095) <= 96 * 4095) by nia. lia.
  - lia.
Qed.

Lemma phi_lsl_small x k : φ x * 2 ^ φ k < wB -> φ (x << k) = φ x * 2 ^ φ k.
Proof.
  intros. rewrite lsl_spec. apply Z.mod_small. pose proof (to_Z_bounded x). pose proof (to_Z_bounded k).
  split; [|lia]. apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia].
Qed.

Lemma split_mul x k : 0 <= k <= 63 -> x * 2 ^ k = (x / 2 ^ (63 - k)) * 2 ^ 63 + (x * 2 ^ k) mod 2 ^ 63.
Proof.
  intros Hk. rewrite Z.mod_eq by (apply Z.pow_nonzero; lia).
  replace (2 ^ 63) with (2 ^ (63 - k) * 2 ^ k) at 3 by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.div_mul_cancel_r by (apply Z.pow_nonzero; lia). ring.
Qed.

(** The end of an accepted block: the two final coordinates are the formal run's. *)
Lemma fin_ok (a b s Q K st off E rem a' b' : int) L e :
  inv φ a φ b (φ a + φ b) Q 0 φ K L st off E e -> φ s = φ a + φ b ->
  φ rem = φ b * 2 ^ φ K - (φ a + φ b) * φ Q -> 0 <= φ rem < φ a + φ b ->
  Z.abs e < 2 ^ 47 -> φ off <= 144 -> φ a < 2 ^ 56 -> φ b < 2 ^ 56 -> φ K <= 36 ->
  (let sK := (s + off)%uint63 in
   let b2 := (sK + 2 * rem - s - E)%uint63 in
   let a2 := (2 * sK - b2)%uint63 in
   let G := (32 << K)%uint63 in
   if ((G <=? a2) && (G <=? b2) && (a2 <? 1 << 62) && (b2 <? 1 << 62))%uint63 then ((a2 >> 1)%uint63, (b2 >> 1)%uint63)
   else (0%uint63, 0%uint63)) = (a', b') -> φ a' <> 0 ->
  opIter (Z.to_nat φ K) (nat_of a, nat_of b) = Some (nat_of a', nat_of b') /\ 0 < φ a' /\
  φ a' + φ b' <= φ a + φ b + 144.
Proof.
  intros I Hs Hrem Br Be Ho Ha Hb HK H Ha'.
  assert (LL : Z.to_nat φ K = List.length L) by (unfold inv in I; destruct (drun L _); lia). rewrite LL.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). pose proof (to_Z_bounded off). pose proof (to_Z_bounded K).
  pose proof (to_Z_bounded rem).
  unfold inv in I. destruct (drun L (φ a, φ b)) as [A B] eqn:HL. destruct I as (D & S & _ & CE & Len).
  rewrite Z.pow_0_r, Z.div_1_r in D. rewrite Z.pow_0_r, Z.mul_1_r in CE.
  cbv zeta in H.
  set (b2 := (s + off + 2 * rem - s - E)%uint63) in H. set (a2 := (2 * (s + off) - b2)%uint63) in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|injection H as <- <-; elim Ha'; reflexivity] end.
  injection H as <- <-.
  rewrite !andb_true_iff, !leb_Z, !ltb_Z in Hc. destruct Hc as [[[G1 G2] G3] G4].
  apply Z.leb_le in G1, G2. apply Z.ltb_lt in G3, G4.
  assert (HG : φ (32 << K) = 32 * 2 ^ φ K).
  { rewrite phi_lsl_small; [reflexivity|]. change (φ 32) with 32. change wB with (2 ^ 63).
    assert (2 ^ φ K <= 2 ^ 36) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite HG in G1, G2. change (φ (1 << 62)) with (2 ^ 62) in G3, G4.
  assert (Hso : φ (s + off) = φ s + φ off) by (apply phi_add_small; change wB with (2 ^ 63); lia).
  assert (Cb : cg φ b2 (φ (s + off) + φ 2 * φ rem - φ s - e)).
  { unfold b2. eapply cg_trans; [apply cg_phi_sub|]. apply cg_sub; [|exact CE].
    eapply cg_trans; [apply cg_phi_sub|]. apply cg_sub; [|apply cg_refl].
    eapply cg_trans; [apply cg_phi_add|]. apply cg_add; [apply cg_refl|]. apply cg_phi_mul. }
  change (φ 2) with 2 in Cb. rewrite Hso in Cb.
  assert (E2 : 2 * B = φ s + φ off + 2 * φ rem - φ s - e).
  { replace (2 * B) with ((A + B) + (B - A)) by ring. rewrite S, D, Hrem, Hs. ring. }
  assert (Hb2 : φ b2 = 2 * B).
  { rewrite E2. apply cg_eq; [exact Cb|lia|]. split; lia. }
  assert (Ca : cg φ a2 (φ 2 * φ (s + off) - φ b2)).
  { unfold a2. eapply cg_trans; [apply cg_phi_sub|]. apply cg_sub; [apply cg_phi_mul|apply cg_refl]. }
  change (φ 2) with 2 in Ca. rewrite Hso, Hb2 in Ca.
  assert (Ha2 : φ a2 = 2 * A).
  { replace (2 * A) with (2 * (φ s + φ off) - 2 * B) by lia. apply cg_eq; [exact Ca|lia|]. split; lia. }
  assert (R1 : φ (a2 >> 1) = A) by (rewrite lsr_spec, Ha2; change (2 ^ φ 1) with 2; lia).
  assert (R2 : φ (b2 >> 1) = B) by (rewrite lsr_spec, Hb2; change (2 ^ φ 1) with 2; lia).
  rewrite R1, R2. split; [|lia].
  assert (Na : Z.of_nat (nat_of a) = φ a) by (unfold nat_of; apply Z2Nat.id; lia).
  assert (Nb : Z.of_nat (nat_of b) = φ b) by (unfold nat_of; apply Z2Nat.id; lia).
  pose proof (block_ok L (nat_of a) (nat_of b)) as BO. rewrite Na, Nb, HL, Len in BO. cbn [fst snd] in BO.
  unfold nat_of at 3 4. rewrite R1, R2. apply BO; lia.
Qed.

Theorem blk_ok K a b a' b' : φ K = 12 \/ φ K = 24 \/ φ K = 36 -> φ a < 2 ^ 56 -> φ b < 2 ^ 56 ->
  blk TP K a b = (a', b') -> φ a' <> 0 ->
  opIter (knat K) (nat_of a, nat_of b) = Some (nat_of a', nat_of b') /\ 0 < φ a' /\
  φ a' + φ b' <= φ a + φ b + 144.
Proof.
  intros HK Ha Hb H Ha'. pose proof (to_Z_bounded a) as Ba. pose proof (to_Z_bounded b) as Bb.
  change wB with (2 ^ 63) in Ba, Bb.
  assert (HKn : knat K = Z.to_nat (φ K)) by (unfold knat; rewrite !eqb_Z; destruct HK as [E|[E|E]]; rewrite E; reflexivity).
  unfold blk in H. cbv zeta in H.
  match type of H with context [mulc _ ?q] => set (Q := q) in H end. clearbody Q.
  assert (Hs : φ ((a + b)%uint63) = φ a + φ b) by (apply phi_add_small; change wB with (2 ^ 63); lia).
  set (s := (a + b)%uint63) in *. clearbody s.
  destruct (mulc s Q) as [h l] eqn:Hm.
  pose proof (mulc_spec s Q) as Mq. rewrite Hm in Mq. cbn [fst snd] in Mq.
  match type of H with context [if ?c then _ else _] =>
    lazymatch c with ((Q <? _)%uint63 && _ && _ && _)%bool => destruct c eqn:Hc; [|injection H as <- <-; elim Ha'; reflexivity] end end.
  rewrite !andb_true_iff, ltb_Z, eqb_Z, leb_Z, ltb_Z in Hc.
  destruct Hc as [[[Q1 Q2] Q3] Q4]. apply Z.ltb_lt in Q1, Q4. apply Z.eqb_eq in Q2. apply Z.leb_le in Q3.
  pose proof (to_Z_bounded Q) as BQ. pose proof (to_Z_bounded h) as Bh. pose proof (to_Z_bounded l) as Bl.
  assert (P2K : φ (1 << K) = 2 ^ φ K) by (rewrite phi_lsl_small; change (φ 1) with 1; try change wB with (2 ^ 63); destruct HK as [E|[E|E]]; rewrite E; lia).
  rewrite P2K in Q1.
  (* the remainder b 2^K - s Q *)
  assert (Hnl : φ (b << K) = φ b * 2 ^ φ K mod 2 ^ 63) by (rewrite lsl_spec; reflexivity).
  assert (Hh : φ (b >> (63 - K)) = φ b / 2 ^ (63 - φ K)).
  { rewrite lsr_spec, phi_sub_small; [reflexivity|]. change φ 63 with 63. lia. }
  rewrite Hh in Q2. rewrite Hnl in Q3.
  set (rem := (b << K - l)%uint63) in *.
  assert (Hrem : φ rem = φ b * 2 ^ φ K - φ s * φ Q).
  { unfold rem. rewrite phi_sub_small by (rewrite Hnl; lia). rewrite Hnl. change wB with (2 ^ 63) in Mq.
    pose proof (split_mul φ b φ K ltac:(lia)). lia. }
  clearbody rem. clear Hnl Hh Q2 Q3 Mq Hm P2K Bh Bl h l. pose proof (to_Z_bounded rem).
  pose proof (Z.mod_pos_bound φ a 2 ltac:(lia)). pose proof (Z.mod_pos_bound φ s 2 ltac:(lia)).
  set (st0 := ((a land 1) + ((s land 1) << 1))%uint63) in H.
  assert (Hst0 : φ st0 = φ a mod 2 + 2 * ((φ a + φ b) mod 2)).
  { assert (L1 : φ ((s land 1) << 1) = 2 * (φ s mod 2)).
    { rewrite phi_lsl_small; rewrite land_1; change (φ 1) with 1; try change wB with (2 ^ 63); lia. }
    unfold st0. rewrite phi_add_small; rewrite ?land_1, L1, ?Hs; try change wB with (2 ^ 63); lia. }
  clearbody st0. revert H. clear H1 H2.
  assert (S1 : φ (K - 12) = φ K - 12) by (rewrite phi_sub_small; change (φ 12) with 12; lia).
  destruct (chunk TP Q (K - 12) st0 0 0) as [[st1 off1] E1] eqn:C1.
  pose proof (inv_init φ a φ b Q φ K st0 ltac:(lia) ltac:(lia) Hst0) as I0.
  pose proof (fun H1 H2 H3 H4 => inv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 I0 C1) as X.
  change (φ 0) with 0 in X. specialize (X ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct X as (e1 & I1 & Be1 & Bo1).
  destruct (K =? 12)%uint63 eqn:K12.
  - rewrite eqb_Z in K12. apply Z.eqb_eq in K12. change (φ 12) with 12 in K12.
    assert (K36 : (K =? 36)%uint63 = false) by (rewrite eqb_Z, K12; reflexivity). rewrite K36.
    intros H. cbv beta iota in H. rewrite HKn.
    rewrite S1 in I1. replace (φ K - 12) with 0 in I1 by (clear - K12; lia). replace (0 + 12) with (φ K) in I1 by (clear - K12; lia).
    eapply (fin_ok a b s Q K st1 off1 E1 rem a' b'); [exact I1|exact Hs|rewrite Hrem, Hs; reflexivity|clear - Q4 Hs H0; lia|clear - Be1; lia|clear - Bo1; lia|clear - Ha; lia|clear - Hb; lia|clear - HK; lia|exact H|exact Ha'].
  - assert (K12' : φ K <> 12) by (intro E; rewrite eqb_Z, E in K12; discriminate).
    assert (S2 : φ (K - 24) = φ K - 24) by (destruct HK as [E|[E|E]]; [lia|..]; rewrite phi_sub_small; change (φ 24) with 24; lia).
    destruct (chunk TP Q (K - 24) st1 off1 E1) as [[st2 off2] E2] eqn:C2.
    pose proof (fun H1 H2 H3 H4 => inv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 I1 C2) as X.
    specialize (X ltac:(clear - S1 S2; lia) ltac:(clear - S2 HK; lia) ltac:(clear - S1; lia) ltac:(clear - Bo1; lia)).
    destruct X as (e2 & I2 & Be2 & Bo2).
    destruct (K =? 36)%uint63 eqn:K36.
    + rewrite eqb_Z in K36. apply Z.eqb_eq in K36. change (φ 36) with 36 in K36.
      destruct (chunk TP Q 0 st2 off2 E2) as [[st3 off3] E3] eqn:C3.
      pose proof (fun H1 H2 H3 H4 => inv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 I2 C3) as X.
      change (φ 0) with 0 in X. specialize (X ltac:(clear - S2 K36; lia) ltac:(clear - S2; lia) ltac:(clear - S2; lia) ltac:(clear - Bo1 Bo2; lia)).
      destruct X as (e3 & I3 & Be3 & Bo3).
      intros H. cbv beta iota in H. rewrite HKn.
      change (φ 0) with 0 in I3. replace (0 + 12 + 12 + 12) with (φ K) in I3 by (clear - K36; lia).
      eapply (fin_ok a b s Q K st3 off3 E3 rem a' b'); [exact I3|exact Hs|rewrite Hrem, Hs; reflexivity|clear - Q4 Hs H0; lia|clear - Be1 Be2 Be3; lia|clear - Bo1 Bo2 Bo3; lia|clear - Ha; lia|clear - Hb; lia|clear - HK; lia|exact H|exact Ha'].
    + assert (K24 : φ K = 24) by (destruct HK as [E|[E|E]]; [exfalso; exact (K12' E)|exact E|rewrite eqb_Z, E in K36; discriminate]).
      intros H. cbv beta iota in H. rewrite HKn.
      rewrite S2 in I2. replace (φ K - 24) with 0 in I2 by (clear - K24; lia). replace (0 + 12 + 12) with (φ K) in I2 by (clear - K24; lia).
      eapply (fin_ok a b s Q K st2 off2 E2 rem a' b'); [exact I2|exact Hs|rewrite Hrem, Hs; reflexivity|clear - Q4 Hs H0; lia|clear - Be1 Be2; lia|clear - Bo1 Bo2; lia|clear - Ha; lia|clear - Hb; lia|clear - HK; lia|exact H|exact Ha'].
Qed.
