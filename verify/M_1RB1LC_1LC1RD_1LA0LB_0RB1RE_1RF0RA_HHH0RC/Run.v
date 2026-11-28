(** Soundness of the runner of Check.v: [seg] and [seg_halt] are statements about [opIter]. *)
From Coq Require Import ZArith Lia Uint63 PArray Bool PeanoNat PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check Visits Arith Cmp Ex1 BlkOk.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).
Opaque TP.

Lemma exn_ok k : forall i a b, φ a + φ b + 7 * Z.of_nat k < 2 ^ 58 -> φ i + Z.of_nat k < wB ->
  let '(i', a', b') := exn k i a b in
  exists j, (j <= k)%nat /\ φ i' = φ i + Z.of_nat j /\ opIter j (nat_of a, nat_of b) = Some (nat_of a', nat_of b').
Proof.
  induction k as [|k IH]; intros i a b Hab Hi.
  - exists O. cbn. split; [lia|split; [lia|reflexivity]].
  - pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). pose proof (to_Z_bounded i).
    cbn [exn]. rewrite eqb_Z. change (φ 3) with 3. destruct (Z.eqb_spec φ b 3).
    { exists O. cbn. split; [lia|split; [lia|reflexivity]]. }
    destruct (ex1 a b) as [a1 b1] eqn:E. pose proof (ex1_ok a b ltac:(lia) ltac:(lia) ltac:(lia)) as [O Sb].
    rewrite E in O, Sb. cbn [fst snd] in O, Sb.
    assert (Hi1 : φ (i + 1) = φ i + 1) by (apply phi_add_small; change (φ 1) with 1; lia).
    specialize (IH (i + 1)%uint63 a1 b1 ltac:(lia) ltac:(lia)).
    destruct (exn k (i + 1) a1 b1) as [[i' a'] b']. destruct IH as (j & J1 & J2 & J3).
    exists (S j). split; [lia|split; [lia|]]. cbn [opIter]. rewrite O. exact J3.
Qed.

Lemma kof_cases s : φ (kof s) = 0 \/ φ (kof s) = 12 \/ φ (kof s) = 24 \/ φ (kof s) = 36.
Proof. unfold kof. destruct (_ <=? s)%uint63; [|destruct (_ <=? s)%uint63; [|destruct (_ <=? s)%uint63]]; cbv; auto. Qed.

Lemma knat_eq K : φ K = 12 \/ φ K = 24 \/ φ K = 36 -> knat K = Z.to_nat φ K.
Proof. unfold knat. rewrite !eqb_Z. intros [E|[E|E]]; rewrite E; reflexivity. Qed.

(** The invariant: visit i of the segment from (a0, b0) is (a, b). *)
Definition P (a0 b0 n : int) (t : int * int * int) : Prop :=
  let '(i, a, b) := t in φ i <= φ n /\ opIter (Z.to_nat φ i) (nat_of a0, nat_of b0) = Some (nat_of a, nat_of b).

Lemma P_after a0 b0 n i a b j i' a' b' : P a0 b0 n (i, a, b) -> φ i' = φ i + Z.of_nat j -> φ i' <= φ n ->
  opIter j (nat_of a, nat_of b) = Some (nat_of a', nat_of b') -> P a0 b0 n (i', a', b').
Proof.
  intros [_ H] E L O. split; [exact L|]. pose proof (to_Z_bounded i).
  replace (Z.to_nat φ i') with (Z.to_nat φ i + j)%nat by lia. rewrite opIter_add, H. exact O.
Qed.

Lemma one_ok a0 b0 n i a b : P a0 b0 n (i, a, b) -> P a0 b0 n (one TP n i a b).
Proof.
  intros HP. pose proof HP as [Hin _].
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). pose proof (to_Z_bounded i). pose proof (to_Z_bounded n).
  unfold one. destruct (stop n i a b) eqn:St; [exact HP|].
  unfold stop in St. rewrite !orb_false_iff, eqb_Z, eqb_Z, !leb_Z in St.
  destruct St as [[[S1 S2] S3] S4]. apply Z.eqb_neq in S1, S2. apply Z.leb_gt in S3, S4.
  change (φ 3) with 3 in S2. change (φ (1 << 56)) with (2 ^ 56) in S3, S4.
  assert (Hs : φ (a + b) = φ a + φ b) by (apply phi_add_small; change wB with (2 ^ 63) in *; lia).
  set (K := kof (a + b)). pose proof (kof_cases (a + b)) as HK. fold K in HK.
  assert (Hni : φ (n - i) = φ n - φ i) by (apply phi_sub_small; lia).
  destruct ((K =? 0) || (n - i <? K))%uint63 eqn:C.
  - pose proof (exn_ok 1 i a b ltac:(lia) ltac:(change wB with (2 ^ 63) in *; lia)) as X.
    destruct (exn 1 i a b) as [[i' a'] b']. destruct X as (j & J1 & J2 & J3).
    apply (P_after a0 b0 n i a b j); [exact HP|exact J2|lia|exact J3].
  - rewrite orb_false_iff, eqb_Z, ltb_Z, Hni in C. destruct C as [C1 C2]. apply Z.eqb_neq in C1.
    apply Z.ltb_ge in C2. change (φ 0) with 0 in C1.
    assert (HK' : φ K = 12 \/ φ K = 24 \/ φ K = 36) by lia.
    destruct (blk TP K a b) as [a' b'] eqn:B. rewrite eqb_Z. change (φ 0) with 0.
    destruct (Z.eqb_spec φ a' 0).
    + rewrite knat_eq by exact HK'.
      pose proof (exn_ok (Z.to_nat φ K) i a b ltac:(lia) ltac:(change wB with (2 ^ 63) in *; lia)) as X.
      destruct (exn _ i a b) as [[i' a''] b'']. destruct X as (j & J1 & J2 & J3).
      apply (P_after a0 b0 n i a b j); [exact HP|exact J2|lia|exact J3].
    + destruct (blk_ok K a b a' b' HK' ltac:(lia) ltac:(lia) B n0) as (O & _ & _).
      rewrite knat_eq in O by exact HK'.
      assert (Hik : φ (i + K) = φ i + φ K) by (apply phi_add_small; change wB with (2 ^ 63) in *; lia).
      apply (P_after a0 b0 n i a b (Z.to_nat φ K)); [exact HP|lia|lia|exact O].
Qed.

Lemma run_ok a0 b0 n p : forall i a b, P a0 b0 n (i, a, b) -> P a0 b0 n (run TP p n i a b).
Proof.
  induction p as [p IH|p IH|]; intros i a b HP; cbn [run]; destruct (stop n i a b); try exact HP.
  - pose proof (IH i a b HP) as H1. destruct (run TP p n i a b) as [[i1 a1] b1].
    pose proof (IH i1 a1 b1 H1) as H2. destruct (run TP p n i1 a1 b1) as [[i2 a2] b2].
    apply one_ok, H2.
  - pose proof (IH i a b HP) as H1. destruct (run TP p n i a b) as [[i1 a1] b1]. apply IH, H1.
  - apply one_ok, HP.
Qed.

Lemma P_start a b n : P a b n (0%uint63, a, b).
Proof. split; [change (φ 0) with 0; pose proof (to_Z_bounded n); lia|reflexivity]. Qed.

Theorem seg_ok p n a b a' b' : seg p n a b a' b' = true ->
  opIter (Z.to_nat φ n) (nat_of a, nat_of b) = Some (nat_of a', nat_of b').
Proof.
  unfold seg. pose proof (run_ok a b n p 0 a b (P_start a b n)) as R.
  destruct (run TP p n 0 a b) as [[i x] y]. rewrite !andb_true_iff. intros [[E1 E2] E3].
  apply Uint63.eqb_spec in E1, E2, E3. subst. apply R.
Qed.

Theorem seg_halt_ok p h a b a' : seg_halt p h a b a' = true ->
  opIter (Z.to_nat φ h) (nat_of a, nat_of b) = Some (nat_of a', 3%nat).
Proof.
  unfold seg_halt. pose proof (run_ok a b h p 0 a b (P_start a b h)) as R.
  destruct (run TP p h 0 a b) as [[i x] y]. rewrite !andb_true_iff. intros [[E1 E2] E3].
  apply Uint63.eqb_spec in E1, E2, E3. subst. apply R.
Qed.
