(** Nonhalting from blank tape for
    1RB0LE_1RC---_0RD0RB_1RE0LA_1RF0LF_1LD1RF.

    Counter overflows with a tail lead to a translated cycle. The file
    includes the SOBCv10 counter rules and proves the exact blank opening,
    the finite sequence of tail-aware rounds, and the eventual escape.

    AI assistance: this proof sketch, the scripts and the checks were
    produced with the help of Claude (Anthropic) and GPT-6 Astra (OpenAI).
*)
From BusyCoq Require Import Individual62 Longitudinal.
Require Import ZifyNat Lia Arith Ring ZArith String List Bool.
Require Import ZifyNat Lia Arith List.
From BusyCoq Require Import Individual62 Longitudinal Flip Permute.
Require Import ZifyNat Lia Arith ZArith String List.
Require Import ZifyNat Lia Arith ZArith List Bool.
Require Import Lia Arith NArith List.
Require Import ZifyNat Lia Arith Ring ZArith List Bool.
Require Import ZifyNat Lia Arith ZArith NArith List Bool.
Require Import Lia Arith List.
Require Import Lia ZArith NArith List.
Require Import Lia List.
Require Import String List.

Module SOBCv10.
From BusyCoq Require Import Individual62 Longitudinal.
Require Import ZifyNat Lia Arith Ring ZArith String List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Definition source_tm := Eval compute in (TM_from_str "1LB0RD_1LC0RC_1RA1LC_1LE0RB_1LF---_0LA0LE").

Notation U := [1;0;1;1].
Notation A8 := [1;1;1;1;1;0;1;1].
Notation B8 := [1;1;1;0;1;1;1;1].
Notation C8 := [1;1;1;1;1;1;1;0].
Notation D8 := [1;1;1;0;1;1;1;0].
Notation E8 := [1;1;1;1;1;0;1;0].
Definition hash : DH0 * DH0 := ((B, []), (F, [])).
Notation hashes := [hash].
Ltac sobc12_esc :=
  apply BoundedConfig.segRLs_c_spec with (T := 1000); reflexivity.

Lemma hash_U : segRLs source_tm hashes hashes U U.
Proof.
  sobc12_esc.
Qed.

Lemma hash_A : segRLs source_tm hashes [] A8 B8.
Proof.
  sobc12_esc.
Qed.

Lemma hash_B : segRLs source_tm hashes hashes B8 A8.
Proof.
  sobc12_esc.
Qed.

Lemma hash_CAUU :
  segRLs source_tm hashes [] (C8 ++ A8 ++ U ++ U) (D8 ++ C8 ++ A8).
Proof.
  sobc12_esc.
Qed.

Lemma hash_E : segRLs source_tm hashes [] E8 D8.
Proof.
  sobc12_esc.
Qed.

Lemma hash_D : segRLs source_tm hashes [] D8 A8.
Proof.
  sobc12_esc.
Qed.
Inductive BDigit := BA | BB.
Definition digit_word (d : BDigit) : list Sym :=
  match d with BA => A8 | BB => B8 end.
Fixpoint digits_word (ds : list BDigit) : list Sym :=
  match ds with
  | [] => []
  | d :: ds' => digit_word d ++ digits_word ds'
  end.
Fixpoint digits_value (ds : list BDigit) : nat :=
  match ds with
  | [] => 0
  | BA :: ds' => 2 * digits_value ds'
  | BB :: ds' => 1 + 2 * digits_value ds'
  end.
(** Closed signal counts for finishing a word at the all-[B] phase while
    requesting an arbitrary number of carries from its high end.  These are
    recursive common formulas over the digit list, not iterations over the
    (possibly enormous) number of input signals. *)
Fixpoint bfinish_count (ds : list BDigit) (out : nat) : nat :=
  match ds with
  | [] => out
  | BA :: ds' => 2 * bfinish_count ds' out + 1
  | BB :: ds' => 2 * bfinish_count ds' out
  end.

Lemma bfinish_repeat_BA_formula w out :
  bfinish_count (repeat BA w) out = (out + 1) * 2^w - 1.
Proof.
  induction w as [|w IH].
  - cbn. lia.
  - cbn [repeat bfinish_count]; rewrite IH, Nat.pow_succ_r by lia; flia.
Qed.

Lemma hash_A_cycle : segRLs source_tm (hashes^^2) hashes A8 A8.
Proof.
  applys_eq (segRLs_trans hash_A hash_B).
Qed.

Lemma hash_B_cycle : segRLs source_tm (hashes^^2) hashes B8 B8.
Proof.
  applys_eq (segRLs_trans hash_B hash_A).
Qed.

Lemma hash_A_finish k :
  segRLs source_tm (hashes^^(2*k+1)) (hashes^^k) A8 B8.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 1 0 source_tm hashes A8 B8); unfold DH0.
  1,2: flia.
  - apply hash_A.
  - apply hash_B_cycle.
Qed.

Lemma hash_B_finish k :
  segRLs source_tm (hashes^^(2*k)) (hashes^^k) B8 B8.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0 source_tm hashes B8 B8); unfold DH0.
  1,2: flia.
  - constructor.
  - apply hash_B_cycle.
Qed.

Lemma hash_A_cycles k :
  segRLs source_tm (hashes^^(2*k)) (hashes^^k) A8 A8.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0 source_tm hashes A8 A8);
    unfold DH0.
  1,2: flia.
  - constructor.
  - apply hash_A_cycle.
Qed.

Lemma hash_E_even n :
  segRLs source_tm (hashes^^(2*n+2)) (hashes^^n) E8 A8.
Proof.
  applys_eq (segRLs_trans hash_E
    (segRLs_trans hash_D (hash_A_cycles n)));
    replace (2*n+2) with (2+2*n) by lia;
    rewrite lpow_add; cbn [lpow]; repeat rewrite app_assoc; reflexivity.
Qed.

Lemma hash_E_odd n :
  segRLs source_tm (hashes^^(2*n+3)) (hashes^^n) E8 B8.
Proof.
  applys_eq (segRLs_trans hash_E
    (segRLs_trans hash_D (hash_A_finish n)));
    replace (2*n+3) with (3+2*n) by lia;
    rewrite !lpow_add; cbn [lpow]; rewrite lpow_shift;
    repeat rewrite app_assoc; reflexivity.
Qed.

Lemma bfinish_spec ds out :
  segRLs source_tm (hashes^^(bfinish_count ds out)) (hashes^^out)
    (digits_word ds) (B8^^length ds).
Proof.
  induction ds as [|[] ds IH]; cbn [bfinish_count digits_word List.length lpow].
  - apply segRLs_nil.
  - eapply segRLs_concat; [apply hash_A_finish|apply IH].
  - eapply segRLs_concat; [apply hash_B_finish|apply IH].
Qed.

Lemma hashes_U n : segRLs source_tm (hashes^^n) (hashes^^n) U U.
Proof.
  induction n; cbn [lpow]; [constructor|].
  eapply segRLs_trans; eauto using hash_U.
Qed.

Lemma hashes_U_run signals width :
  segRLs source_tm (hashes^^signals) (hashes^^signals) (U^^width) (U^^width).
Proof.
  induction width; cbn [lpow]; [apply segRLs_nil|].
  eapply segRLs_concat; eauto using hashes_U.
Qed.

Lemma segRLs_0inf {hs input output} :
  segRLs source_tm hs [] input output ->
  sideRLs source_tm hs (input *> 0inf) (output *> 0inf).
Proof.
  intro H; exact (segRLs_sideRLs_concat H (sideRLseq_O source_tm 0inf)).
Qed.
Definition common_left_wall : side :=
  0inf <* <[1;0;1;0;0;1;0;0].

Lemma sobc1_emit_hash r :
  common_left_wall {{{((F, []), L)}}} r -[source_tm]->+
  common_left_wall {{{((B, []), R)}}} (U *> r).
Proof.
  unfold common_left_wall, source_tm.
  eapply multistep_progress with (n := 32).
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma sobc1_hash_CABAD k :
  segRLs source_tm hashes []
    (C8 ++ A8^^k ++ B8 ++ A8 ++ D8)
    (D8 ++ C8^^k ++ B8 ++ U^^2 ++ A8).
Proof.
  ut; esx.
Qed.

Lemma sobc1_hash_CAB1110 k :
  segRLs source_tm hashes []
    (C8 ++ A8^^k ++ B8 ++ [1;1;1;0])
    (D8 ++ C8^^k ++ B8 ++ U).
Proof.
  ut; esx.
Qed.

Lemma sobc1_extra_CC :
  segRLs source_tm hashes []
    (C8 ++ C8) (D8 ++ A8).
Proof.
  apply BoundedConfig.segRLs_c_spec with (T := 1000); reflexivity.
Qed.
Definition sobc12_left_wall : side :=
  0inf <* <[1;0;1;0;0;1;0;0].
(** First emitted [#] in the SOBC1 run: raw step 24396. *)
Definition sobc1_first_word : list Sym :=
  U^^22 ++ A8^^3 ++ D8 ++ C8 ++ A8 ++ U^^28 ++
  A8 ++ A8 ++ B8 ++ A8.
Definition sobc1_first_call : Q * tape :=
  sobc12_left_wall {{{((B, []), R)}}} (sobc1_first_word *> 0inf).

Lemma sobc1_first_call_reachable :
  c0 -[source_tm]->> 24396 / sobc1_first_call.
Proof.
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.
Local Open Scope Z_scope.
Definition centered_step (d : Z) : Z := - ((d + 1) / 2).

Lemma centered_step_twice d :
  centered_step (centered_step d) = (d + 1) / 4.
Proof.
  unfold centered_step; flia.
Qed.
Definition pow4 (k : nat) : Z := Z.of_nat (Nat.pow 4 k).
Definition pow2 (k : nat) : Z := Z.of_nat (Nat.pow 2 k).

Lemma pow4_succ k : pow4 (S k) = 4 * pow4 k.
Proof.
  unfold pow4. rewrite Nat.pow_succ_r by lia.
  rewrite Nat2Z.inj_mul. reflexivity.
Qed.

Lemma pow2_pos k : 0 < pow2 k.
Proof.
  unfold pow2; lia.
Qed.

Lemma pow2_succ k : pow2 (S k) = 2 * pow2 k.
Proof.
  unfold pow2. rewrite Nat.pow_succ_r by lia.
  rewrite Nat2Z.inj_mul. reflexivity.
Qed.

Theorem centered_converges_2w w d :
  (2 <= w)%nat ->
  (- pow2 w < d < pow2 w)%Z ->
  Nat.iter (2 * w) centered_step d = 0.
Proof.
  intros _. revert d; induction w; intros d Hd.
  - change (-1<d<1)%Z in Hd; change (d=0)%Z; lia.
  - replace (2*S w)%nat with (S (S (2*w))) by lia.
    rewrite !Nat.iter_succ_r, centered_step_twice.
    apply IHw; rewrite pow2_succ in Hd; generalize (pow2_pos w); flia.
Qed.
Definition stable_column_step (half v : Z) : Z := half - v / 2.
(** If [p] is the odd fixed point characterised by [2*half=3*p-1],
    translation by [p] conjugates the stable column map to
    [centered_step]. *)

Lemma stable_column_centered half p d :
  (2 * half = 3 * p - 1)%Z ->
  (p mod 2 = 1)%Z ->
  stable_column_step half (p + d) = p + centered_step d.
Proof.
  unfold stable_column_step, centered_step; flia.
Qed.

Lemma stable_column_iter_centered half p n d :
  (2 * half = 3 * p - 1)%Z ->
  (p mod 2 = 1)%Z ->
  Nat.iter n (stable_column_step half) (p + d) =
    p + Nat.iter n centered_step d.
Proof.
  intros Hhalf Hpodd; symmetry; eapply Nat.iter_swap_gen.
  intro d'; symmetry; apply stable_column_centered; assumption.
Qed.

Theorem stable_column_converges_2w half p w v :
  (2 <= w)%nat ->
  (2 * half = 3 * p - 1)%Z ->
  (p mod 2 = 1)%Z ->
  (- pow2 w < v - p < pow2 w)%Z ->
  Nat.iter (2 * w) (stable_column_step half) v = p.
Proof.
  intros Hw Hhalf Hpodd Hrange.
  replace v with (p + (v - p)) by ring.
  rewrite stable_column_iter_centered by assumption.
  rewrite centered_converges_2w by assumption.
  ring.
Qed.
Definition odd_column_width (k : nat) : nat := (2 * k + 1)%nat.
Definition odd_column_half (k : nat) : Z := pow4 k.
Fixpoint odd_column_fixed (k : nat) : Z :=
  match k with O => 1 | S k' => 4 * odd_column_fixed k' - 1 end.

Lemma odd_column_fixed_pos k : 0 < odd_column_fixed k.
Proof.
  induction k; cbn [odd_column_fixed] in *; lia.
Qed.

Lemma pow2_even_width k : pow2 (2 * k) = pow4 k.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - replace (2 * S k)%nat with (S (S (2 * k))) by lia.
    rewrite !pow2_succ, pow4_succ, IH. ring.
Qed.

Lemma pow2_odd_width k :
  pow2 (odd_column_width k) = 2 * odd_column_half k.
Proof.
  unfold odd_column_width, odd_column_half.
  replace (2 * k + 1)%nat with (S (2 * k)) by lia.
  rewrite pow2_succ, pow2_even_width. reflexivity.
Qed.

Lemma odd_column_fixed_equation k :
  2 * odd_column_half k = 3 * odd_column_fixed k - 1.
Proof.
  unfold odd_column_half. induction k; [reflexivity|].
  cbn [odd_column_fixed]. rewrite pow4_succ. nia.
Qed.

Lemma odd_column_fixed_odd k : odd_column_fixed k mod 2 = 1.
Proof.
  induction k; cbn [odd_column_fixed]; flia.
Qed.

Theorem odd_column_converges k v :
  (1 <= k)%nat ->
  (- pow2 (odd_column_width k) < v - odd_column_fixed k <
     pow2 (odd_column_width k))%Z ->
  Nat.iter (2 * odd_column_width k) (stable_column_step (odd_column_half k))
    v = odd_column_fixed k.
Proof.
  intros Hk Hrange.
  apply stable_column_converges_2w.
  - unfold odd_column_width. lia.
  - apply odd_column_fixed_equation.
  - apply odd_column_fixed_odd.
  - exact Hrange.
Qed.
Local Close Scope Z_scope.
Fixpoint initial_u_pair_calls (primary pairs : nat) : nat :=
  match pairs with
  | O => O
  | S pairs' => 2 * 2^primary + initial_u_pair_calls (S primary) pairs'
  end.
Definition sobc1_initial_pre_calls : nat :=
  2^3 + (initial_u_pair_calls 4 14 +
  (2^18 + (2^18 + (2^19 + (2^19 +
  (2^21 + (2^21 + 2^22))))))).

Lemma initial_u_pair_calls_formula primary pairs :
  initial_u_pair_calls primary pairs =
    2^(primary+1) * (2^pairs-1).
Proof.
  induction pairs as [|pairs IH] in primary |- *; [cbn; lia|].
  cbn [initial_u_pair_calls]; rewrite IH.
    replace (primary+1) with (S primary) by lia.
    replace (S primary+1) with (S (S primary)) by lia.
    rewrite !Nat.pow_succ_r by lia.
    replace (2*2^pairs-1) with (1+2*(2^pairs-1)) by
      (generalize (Nat.pow_nonzero 2 pairs ltac:(lia)); lia).
    ring.
Qed.
Definition sobc1_first_half : nat := 2^23 + 2^22 + 2^20 - 2.
(** From this point on the concrete exponents are parameters of the symbolic
    execution, not computations to be expanded by the arithmetic tactics. *)
Opaque Nat.pow.

Lemma sobc1_initial_total_half :
  22 + sobc1_initial_pre_calls + (2^24-1) =
    2*sobc1_first_half+1.
Proof.
  unfold sobc1_initial_pre_calls, sobc1_first_half.
  rewrite initial_u_pair_calls_formula; flia.
Qed.

Theorem standard_mixed_to_binary_out_spec e ds out :
  length ds = S e ->
  segRLs source_tm
    (hashes ^^ ((out + 1) * 2 ^ (S e) - 2 + digits_value ds))
    (hashes ^^ out)
    (E8^^e ++ A8)
    (digits_word ds).
Proof.
  revert ds.
  induction e as [|e IH]; intros ds Hlen.
  - destruct ds as [|d ds]; [discriminate|].
    destruct ds; [|cbn in Hlen; discriminate].
    destruct d; cbn [lpow digits_word digit_word digits_value Nat.pow].
    + applys_eq (hash_A_cycles out); unfold DH0; flia.
    + applys_eq (hash_A_finish out); unfold DH0; flia.
  - destruct ds as [|d ds]; [discriminate|].
    cbn in Hlen.
    assert (Htail : length ds = S e) by lia.
    pose proof (IH ds Htail) as Hrun.
    cbn [lpow digits_word digit_word digits_value].
    rewrite Nat.pow_succ_r by lia.
    assert (Hpow : 2 <= 2^S e) by
      (rewrite Nat.pow_succ_r by lia;
       generalize (Nat.pow_nonzero 2 e ltac:(lia)); lia).
    destruct d; repeat rewrite app_assoc.
    + eapply @segRLs_concat with (w1:=E8) (w2:=A8)
        (w3:=E8^^e++A8) (w4:=digits_word ds).
      * applys_eq (hash_E_even
        ((out+1)*2^(S e)-2+digits_value ds)); unfold DH0; flia.
      * exact Hrun.
    + eapply @segRLs_concat with (w1:=E8) (w2:=B8)
        (w3:=E8^^e++A8) (w4:=digits_word ds).
      * applys_eq (hash_E_odd
        ((out+1)*2^(S e)-2+digits_value ds)); unfold DH0; flia.
      * exact Hrun.
Qed.
Corollary standard_mixed_to_binary_spec e ds :
  length ds = S e ->
  segRLs source_tm (hashes ^^ (2 ^ (S e) - 2 + digits_value ds)) []
    (E8^^e ++ A8) (digits_word ds).
Proof.
  intro Hlen.
  applys_eq (standard_mixed_to_binary_out_spec e ds 0 Hlen);
    unfold DH0; flia.
Qed.

Lemma prefix_E_even k n input output carries :
  segRLs source_tm (hashes^^n) (hashes^^carries) input output ->
  segRLs source_tm (hashes^^(2^k*n+2*(2^k-1))) (hashes^^carries)
    (E8^^k ++ input) (A8^^k ++ output).
Proof.
  intro Hrun. induction k as [|k IH].
  - cbn [lpow Nat.pow]. applys_eq Hrun; unfold DH0; flia.
  - cbn [lpow]. rewrite Nat.pow_succ_r by lia.
    repeat rewrite <- app_assoc.
    eapply segRLs_concat.
    + applys_eq (hash_E_even (2^k*n+2*(2^k-1))); flia.
    + exact IH.
Qed.
Notation X4 := [0;0;1;0].
Notation V4 := [0;1;0;0].
Definition exception_pre_left (n : nat) : side :=
  ([1;0;1;0] ++ V4^^(2*n+2) ++ [1;0;1]) *> 0inf.
Definition exception_call_left (remaining finished : nat) : side :=
  (X4^^(2*finished+5) ++ V4^^(2*remaining) ++ [1;0;1]) *> 0inf.
Definition exception_raw_source (n w : nat) : Q * tape :=
  common_left_wall {{{((B, []), R)}}}
    ((U^^(2*n+1) ++ B8^^(S w) ++ [1;1]) *> 0inf).
Definition exception_pre (n w : nat) : Q * tape :=
  exception_pre_left n {{{((F, []), L)}}}
    ((E8^^w ++ A8) *> 0inf).

Lemma raw_U_to_X :
  segRR source_tm (B, []) (B, []) U X4.
Proof.
  unfold segRR, source_tm. intros l r.
  eapply without_counter with (n:=4).
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma segRR_lpow_same h w v k :
  segRR source_tm h h w v -> segRR source_tm h h (w^^k) (v^^k).
Proof.
  unfold segRR. intros H. induction k as [|k IH]; intros l r.
  - finish.
  - cbn [lpow]. eapply evstep_trans.
    + applys_eq (H l ((w^^k) *> r)); repeat rewrite Str_app_assoc; reflexivity.
    + applys_eq (IH (v *> l) r); repeat rewrite <- Str_app_assoc;
        rewrite <- lpow_shift; reflexivity.
Qed.

Lemma raw_Us_to_Xs k :
  segRR source_tm (B, []) (B, []) (U^^k) (X4^^k).
Proof.
  apply segRR_lpow_same, raw_U_to_X.
Qed.
Notation Q8 := [0;0;1;0;0;1;0;1].

Lemma raw_B_forward :
  segRR source_tm (B, []) (B, []) B8 Q8.
Proof.
  unfold segRR, source_tm. intros l r.
  eapply without_counter with (n:=14).
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma raw_B_return l r :
  ([1;0;1] *> Q8 *> l) {{{((F, []), L)}}} r -[source_tm]->+
  ([1;0;1] *> l) {{{((F, []), L)}}} (E8 *> r).
Proof.
  unfold source_tm.
  eapply multistep_progress with (n:=15).
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma raw_exception_tail_base l :
  l {{{((B, []), R)}}} ((B8 ++ [1;1]) *> 0inf) -[source_tm]->+
  ([1;0;1] *> l) {{{((F, []), L)}}} (A8 *> 0inf).
Proof.
  unfold source_tm.
  eapply multistep_progress with (n:=33).
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma raw_exception_tail w l :
  l {{{((B, []), R)}}}
      ((B8^^(S w) ++ [1;1]) *> 0inf) -[source_tm]->+
  ([1;0;1] *> l) {{{((F, []), L)}}}
      ((E8^^w ++ A8) *> 0inf).
Proof.
  induction w as [|w IH] in l |- *.
  - cbn [lpow]. exact (raw_exception_tail_base l).
  - cbn [lpow].
    eapply evstep_progress_trans.
    + applys_eq (raw_B_forward l
        ((B8^^(S w) ++ [1;1]) *> 0inf)).
    + eapply progress_trans.
      * applys_eq (IH (Q8 *> l)).
      * applys_eq (raw_B_return l ((E8^^w ++ A8) *> 0inf)).
Qed.

Lemma exception_pre_left_direct n :
  ([1;0;1] *> X4^^(2*n+1) *> Q8 *> 0inf) = exception_pre_left n.
Proof.
  unfold exception_pre_left; simpl_rotate.
  replace (n+(n+0)+2) with (S (n+(n+0)+1)) by lia.
  cbn [lpow]; simpl_rotate; repeat rewrite Str_app_assoc; reflexivity.
Qed.

Lemma exception_raw_to_pre n w :
  exception_raw_source n w -[source_tm]->* exception_pre n w.
Proof.
  unfold exception_raw_source, exception_pre.
  apply progress_evstep.
  eapply evstep_progress_trans.
  - applys_eq (raw_Us_to_Xs (2*n+1) common_left_wall
      ((B8^^(S w) ++ [1;1]) *> 0inf));
      repeat rewrite Str_app_assoc; reflexivity.
  - applys_eq (raw_exception_tail w
      (common_left_wall <* (X4^^(2*n+1)))).
    unfold common_left_wall.
    rewrite exception_pre_left_direct; repeat rewrite Str_app_assoc; reflexivity.
Qed.
Definition left_hash : DH0 * DH0 := ((F, []), (B, [])).

Lemma left_hash_XX :
  segRLs (flip source_tm) [left_hash] [left_hash]
    (X4^^2) (X4^^2).
Proof.
  apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.
Qed.

Lemma left_relaunch_base :
  segRLs (flip source_tm) [left_hash] []
    (X4^^5 ++ V4^^2) (X4^^7).
Proof.
  apply BoundedConfig.segRLs_c_spec with (T:=10000); reflexivity.
Qed.

Lemma left_hash_X_pairs k :
  segRLs (flip source_tm) [left_hash] [left_hash]
    (X4^^(2*k)) (X4^^(2*k)).
Proof.
  induction k as [|k IH].
  - cbn [lpow]. apply segRLs_nil.
  - applys_eq (segRLs_concat IH left_hash_XX);
      replace (2*S k) with (2*k+2) by lia; rewrite lpow_add; reflexivity.
Qed.

Lemma left_launch_segment :
  segRLs (flip source_tm) [left_hash] []
    ([1;0;1;0] ++ V4^^4) (X4^^5).
Proof.
  apply BoundedConfig.segRLs_c_spec with (T:=10000); reflexivity.
Qed.

Lemma exception_launch k :
  sideRLs (flip source_tm) [left_hash]
    (exception_pre_left (S k)) (exception_call_left k 0).
Proof.
  unfold exception_pre_left, exception_call_left.
  replace (2*S k+2) with (4+2*k) by lia; rewrite lpow_add.
  cbn [Nat.mul Nat.add].
  applys_eq (segRLs_sideRLs_concat left_launch_segment
    (sideRLseq_O (flip source_tm)
      ((V4^^(2*k) ++ [1;0;1]) *> 0inf)));
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Lemma exception_relaunch_side remaining finished :
  sideRLs (flip source_tm) [left_hash]
    (exception_call_left (S remaining) finished)
    (exception_call_left remaining (S finished)).
Proof.
  pose proof (segRLs_concat
    (left_hash_X_pairs finished) left_relaunch_base) as Hseg.
  unfold exception_call_left.
  replace (2*S remaining) with (2+2*remaining) by lia.
  replace (2*S finished+5) with (2*finished+7) by lia.
  repeat rewrite Str_app_assoc.
  rewrite <- (lpow_add' X4 (2*finished) 5).
  rewrite <- (lpow_add' X4 (2*finished) 7).
  rewrite <- (lpow_add' V4 2 (2*remaining)).
  applys_eq (segRLs_sideRLs_concat Hseg
    (sideRLseq_O (flip source_tm)
      ((V4^^(2*remaining) ++ [1;0;1]) *> 0inf)));
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Lemma exception_relaunches k finished :
  sideRLs (flip source_tm) ([left_hash]^^k)
    (exception_call_left k finished)
    (exception_call_left 0 (finished+k)).
Proof.
  induction k as [|k IH] in finished |- *.
  - cbn [lpow]. replace (finished + 0) with finished by lia. constructor.
  - cbn [lpow]; eapply sideRLs_trans.
    + apply exception_relaunch_side.
    + applys_eq (IH (S finished)); flia.
Qed.

Lemma exception_calls k input output :
  segRLs source_tm (hashes^^(S k)) [] input output ->
  exception_call_left k 0 {{{((B, []), R)}}} (input *> 0inf)
    -[source_tm]->+
  exception_call_left 0 k {{{((F, []), L)}}} (output *> 0inf).
Proof.
  intro Hseg.
  pose proof (segRLs_0inf Hseg) as Hright.
  eapply sideRLs_concat.
  - applys_eq (exception_relaunches k 0); flia.
  - applys_eq Hright.
    unfold left_hash; cbn.
    pose proof (lrcons_lpow1 (B, []) (F, []) (S k) ltac:(lia)) as Hl.
    replace (S k - 1) with k in Hl by lia.
    exact Hl.
Qed.
Definition exception_done (n : nat) (output : list Sym) : Q * tape :=
  common_left_wall {{{((B, []), R)}}}
    ((C8 ++ A8 ++ U^^(2*n) ++ output) *> 0inf).

Lemma exception_exit k output :
  exception_call_left 0 k {{{((F, []), L)}}} (output *> 0inf)
    -[source_tm]->+ exception_done (S k) output.
Proof.
  unfold exception_call_left, exception_done, common_left_wall, source_tm.
  induction k as [|k IH].
  - ut; esx.
  - ut; esx.
Qed.

Lemma exception_launch_progress k r :
  exception_pre_left (S k) {{{((F, []), L)}}} r -[source_tm]->+
  exception_call_left k 0 {{{((B, []), R)}}} r.
Proof.
  exact (sideRLs_1L _ _ _ _ _ (exception_launch k) r).
Qed.

Lemma exception_exit_zero output :
  exception_pre_left 0 {{{((F, []), L)}}} (output *> 0inf)
    -[source_tm]->+ exception_done 0 output.
Proof.
  unfold exception_pre_left, exception_done, common_left_wall, source_tm.
  ut; esx.
Qed.

Lemma exception_pre_from_seg n input output :
  segRLs source_tm (hashes^^n) [] input output ->
  exception_pre_left n {{{((F, []), L)}}} (input *> 0inf)
    -[source_tm]->+ exception_done n output.
Proof.
  destruct n as [|k].
  - cbn [lpow]; intro Hseg; inversion Hseg; subst; apply exception_exit_zero.
  - intro Hseg; eapply progress_trans;
      [apply exception_launch_progress|].
    eapply progress_trans; [exact (exception_calls k input output Hseg)|
      apply exception_exit].
Qed.

Theorem sobc1_exception_from_seg n w output :
  segRLs source_tm (hashes^^n) []
    (E8^^w ++ A8) output ->
  exception_raw_source n w -[source_tm]->* exception_done n output.
Proof.
  intro Hseg.
  eapply evstep_trans.
  - exact (exception_raw_to_pre n w).
  - apply progress_evstep.
    exact (exception_pre_from_seg n (E8^^w ++ A8) output Hseg).
Qed.
Local Open Scope Z_scope.
(** The low, input-independent part of a freshly born [Z] column alternates
    between these two families as one high bit per round becomes exposed to
    the right-hand signal stream.  Index [n] represents widths [2n+4] and
    [2n+5], respectively. *)
Fixpoint even_residue (n : nat) : Z :=
  match n with
  | O => 3
  | S n' => 4 * even_residue n' + 1
  end.
Fixpoint odd_residue (n : nat) : Z :=
  match n with
  | O => 26
  | S n' => 4 * odd_residue n' - 2
  end.
Definition even_residue_width (n : nat) : nat := (2 * n + 4)%nat.
Definition odd_residue_width (n : nat) : nat := (2 * n + 5)%nat.

Lemma even_residue_bounds n :
  3 <= even_residue n <= pow2 (even_residue_width n) - 6.
Proof.
  induction n as [|n IH].
  - change (3 <= 3 <= 16 - 6). lia.
  - cbn [even_residue]; unfold even_residue_width in *.
    replace (2*S n+4)%nat with (S (S (2*n+4))) by lia.
    rewrite !pow2_succ; flia.
Qed.

Lemma even_residue_S_lower n : 13 <= even_residue (S n).
Proof.
  cbn [even_residue].
  generalize (even_residue_bounds n); lia.
Qed.

Lemma odd_residue_bounds n :
  3 <= odd_residue n <= pow2 (odd_residue_width n) - 6.
Proof.
  induction n as [|n IH].
  - change (3 <= 26 <= 32 - 6). lia.
  - cbn [odd_residue]; unfold odd_residue_width in *.
    replace (2*S n+5)%nat with (S (S (2*n+5))) by lia.
    rewrite !pow2_succ; flia.
Qed.
(** These division-free identities are the two alternating low-bit
    transitions. *)

Lemma odd_residue_complement n :
  odd_residue n =
    2 * (pow2 (even_residue_width n) - even_residue n).
Proof.
  induction n as [|n IH].
  - change (26 = 2 * (16 - 3)). lia.
  - cbn [odd_residue even_residue]; unfold even_residue_width in *.
    replace (2*S n+4)%nat with (S (S (2*n+4))) by lia.
    rewrite !pow2_succ; flia.
Qed.

Lemma even_residue_complement n :
  even_residue (S n) =
    2 * (pow2 (odd_residue_width n) - odd_residue n) + 1.
Proof.
  pose proof (odd_residue_complement n) as Hodd.
  cbn [even_residue]; unfold odd_residue_width, even_residue_width in *.
  replace (2*n+5)%nat with (S (2*n+4)) by lia.
  rewrite pow2_succ; flia.
Qed.

Lemma low_step_odd_to_even n :
  pow2 (even_residue_width n) - odd_residue n / 2 =
    even_residue n.
Proof.
  rewrite odd_residue_complement; flia.
Qed.

Lemma low_step_even_to_odd n :
  pow2 (odd_residue_width n) - even_residue (S n) / 2 =
    odd_residue n.
Proof.
  rewrite even_residue_complement; flia.
Qed.
(** Width [2n+7] is the actual [Z] birth family
    [B^3 (A B)^n A A B B]. *)
Definition z_birth_value (n : nat) : Z :=
  2 * (pow2 (even_residue_width (S n)) - even_residue (S n)) + 1.
Definition z_birth_width (n : nat) : nat := (2 * n + 7)%nat.

Lemma z_birth_complement n :
  z_birth_value n =
    2 * (pow2 (even_residue_width (S n)) - even_residue (S n)) + 1.
Proof.
  reflexivity.
Qed.

Lemma z_birth_zero : z_birth_value O = 103.
Proof.
  reflexivity.
Qed.

Lemma z_birth_succ n :
  z_birth_value (S n) = 4 * z_birth_value n - 5.
Proof.
  unfold z_birth_value, even_residue_width.
  cbn [even_residue].
  replace (2*S (S n)+4)%nat with (S (S (2*S n+4))) by lia.
  rewrite !pow2_succ; flia.
Qed.

Lemma z_birth_bounds n :
  3 <= z_birth_value n <= pow2 (z_birth_width n) - 6.
Proof.
  pose proof (z_birth_complement n) as Hz.
  pose proof (even_residue_bounds (S n)) as He.
  pose proof (even_residue_S_lower n) as He13.
  unfold z_birth_width, even_residue_width in *.
  replace (2*n+7)%nat with (S (2*S n+4)) by lia.
  rewrite pow2_succ; flia.
Qed.

Lemma z_birth_first_low_step n :
  pow2 (even_residue_width (S n)) - z_birth_value n / 2 =
    even_residue (S n).
Proof.
  rewrite z_birth_complement; flia.
Qed.
(** [low_slice total m r v] says that [r] is exactly the low [m]-bit
    block of [v], while [v] still lies in the [total]-sized column.  The
    quotient form avoids any appeal to machine-sized modular arithmetic. *)
Definition low_slice (total : Z) (m : nat) (r v : Z) : Prop :=
  exists high capacity,
    total = capacity * pow2 m /\
    v = high * pow2 m + r /\
    (0 <= high < capacity)%Z.

Lemma low_slice_safe total m r v :
  low_slice total m r v ->
  (3 <= r <= pow2 m - 6)%Z ->
  (3 <= v <= total - 6)%Z.
Proof.
  intros (high & capacity & Htotal & Hv & Hhigh) Hr.
  generalize (pow2_pos m); nia.
Qed.
(** One arbitrary right-hand bit chooses either [total/2] or [total] as
    the high-bit contribution.  In both cases the low slice evolves by the
    same negative-binary quotient, and exactly one high bit becomes
    signal-dependent. *)

Lemma low_slice_step total m r v (right_odd : bool) :
  low_slice total (S m) r v ->
  (3 <= r < pow2 (S m))%Z ->
  low_slice total m (pow2 m - r / 2)
    ((if right_odd then total / 2 else total) - v / 2).
Proof.
  intros (high & capacity & Htotal & Hv & Hhigh) Hr.
  rewrite pow2_succ in Htotal, Hv, Hr.
  assert (Htotal_half : total / 2 = capacity * pow2 m).
  { flia. }
  assert (Hv_half : v / 2 = high * pow2 m + r / 2).
  { flia. }
  assert (Hrhalf : (1 <= r / 2 < pow2 m)%Z).
  { generalize (pow2_pos m); flia. }
  destruct right_odd.
  - exists (capacity-high-1), (2*capacity); repeat split; flia.
  - exists (2*capacity-high-1), (2*capacity); repeat split; flia.
Qed.

Lemma z_birth_low_slice n :
  low_slice (pow2 (z_birth_width n)) (z_birth_width n)
    (z_birth_value n) (z_birth_value n).
Proof.
  exists 0, 1. split; [ring|]. split; [ring|]. lia.
Qed.
Inductive LineagePhase :=
| LBirth (n : nat)
| LEven (n : nat)
| LOdd (n : nat).
Definition lineage_width (p : LineagePhase) : nat :=
  match p with
  | LBirth n => z_birth_width n
  | LEven n => even_residue_width n
  | LOdd n => odd_residue_width n
  end.
Definition lineage_residue (p : LineagePhase) : Z :=
  match p with
  | LBirth n => z_birth_value n
  | LEven n => even_residue n
  | LOdd n => odd_residue n
  end.
Inductive lineage_next : LineagePhase -> LineagePhase -> Prop :=
| lineage_birth n : lineage_next (LBirth n) (LEven (S n))
| lineage_even n : lineage_next (LEven (S n)) (LOdd n)
| lineage_odd n : lineage_next (LOdd n) (LEven n).
Definition arbitrary_column_step (total : Z) (right_odd : bool) (v : Z) : Z :=
  (if right_odd then total / 2 else total) - v / 2.

Lemma lineage_residue_bounds p :
  (3 <= lineage_residue p <= pow2 (lineage_width p) - 6)%Z.
Proof.
  destruct p as [n|n|n]; cbn [lineage_residue lineage_width].
  - apply z_birth_bounds.
  - apply even_residue_bounds.
  - apply odd_residue_bounds.
Qed.

Lemma lineage_next_width p p' :
  lineage_next p p' -> lineage_width p = S (lineage_width p').
Proof.
  intro H; destruct H; cbn [lineage_width];
    unfold z_birth_width, even_residue_width, odd_residue_width; lia.
Qed.

Lemma lineage_next_low_step p p' :
  lineage_next p p' ->
  pow2 (lineage_width p') - lineage_residue p / 2 =
    lineage_residue p'.
Proof.
  intro H; destruct H; cbn [lineage_width lineage_residue].
  - apply z_birth_first_low_step.
  - apply low_step_even_to_odd.
  - apply low_step_odd_to_even.
Qed.

Lemma lineage_step_preserves_slice total p p' v right_odd :
  lineage_next p p' ->
  low_slice total (lineage_width p) (lineage_residue p) v ->
  low_slice total (lineage_width p') (lineage_residue p')
    (arbitrary_column_step total right_odd v).
Proof.
  intros Hnext Hslice.
  pose proof (lineage_next_width _ _ Hnext) as Hwidth.
  pose proof (lineage_next_low_step _ _ Hnext) as Hresidue.
  pose proof (lineage_residue_bounds p) as Hbounds.
  unfold arbitrary_column_step.
  rewrite Hwidth in Hslice, Hbounds.
  rewrite <- Hresidue.
  apply low_slice_step.
  - exact Hslice.
  - generalize (pow2_pos (S (lineage_width p'))); lia.
Qed.
Definition lineage_fuel (p : LineagePhase) : nat :=
  match p with
  | LBirth n => 2 * n + 3
  | LEven n => 2 * n
  | LOdd n => 2 * n + 1
  end.
Fixpoint zinputs (total : Z) (inputs : list bool) (v : Z) : Z :=
  match inputs with
  | [] => v
  | b::inputs' => zinputs total inputs' (arbitrary_column_step total b v)
  end.

Theorem lineage_inputs_safe total p v inputs :
  (length inputs <= lineage_fuel p)%nat ->
  low_slice total (lineage_width p) (lineage_residue p) v ->
  (3 <= zinputs total inputs v <= total-6)%Z.
Proof.
  revert p v. induction inputs as [|b inputs IH]; intros p v Hlength Hslice.
  - exact (low_slice_safe _ _ _ _ Hslice (lineage_residue_bounds p)).
  - cbn [zinputs] in *; destruct p as [n|[|n]|n].
    + eapply IH with (p:=LEven (S n)); [cbn [lineage_fuel length] in *; lia|].
      eapply lineage_step_preserves_slice; [constructor|exact Hslice].
    + cbn [lineage_fuel length] in Hlength; lia.
    + eapply IH with (p:=LOdd n); [cbn [lineage_fuel length] in *; lia|].
      eapply lineage_step_preserves_slice; [constructor|exact Hslice].
    + eapply IH with (p:=LEven n); [cbn [lineage_fuel length] in *; lia|].
      eapply lineage_step_preserves_slice; [constructor|exact Hslice].
Qed.
Local Close Scope Z_scope.
Definition ordinary_left (u : nat) : side := X4^^u *> common_left_wall.

Lemma left_emit_zero :
  sideRLs (flip source_tm) [left_hash]
    (ordinary_left 0) (ordinary_left 1).
Proof.
  unfold ordinary_left, common_left_wall.
  simpl_rotate.
  change (sideRLs (flip source_tm) [left_hash]
    (Q8 *> 0inf) ((X4 ++ Q8) *> 0inf)).
  apply BoundedConfig.sideRLs_c_spec with (T:=10000); reflexivity.
Qed.

Lemma left_emit_one :
  sideRLs (flip source_tm) [left_hash]
    (ordinary_left 1) (ordinary_left 2).
Proof.
  unfold ordinary_left, common_left_wall.
  simpl_rotate.
  change (sideRLs (flip source_tm) [left_hash]
    ((X4 ++ Q8) *> 0inf) ((X4 ++ X4 ++ Q8) *> 0inf)).
  apply BoundedConfig.sideRLs_c_spec with (T:=10000); reflexivity.
Qed.

Lemma nat_ind2 (P : nat -> Prop) :
  P 0%nat -> P 1%nat ->
  (forall n, P n -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros H0 H1 HS.
  fix IH 1. intro n.
  destruct n as [|[|n]]; [exact H0|exact H1|].
  apply HS, IH.
Qed.

Lemma left_emit_call u :
  sideRLs (flip source_tm) [left_hash]
    (ordinary_left u) (ordinary_left (S u)).
Proof.
  induction u as [| |u IH] using nat_ind2.
  - exact left_emit_zero.
  - exact left_emit_one.
  - pose proof (segRLs_sideRLs_concat left_hash_XX IH) as H.
    unfold ordinary_left in *.
    repeat rewrite <- Str_app_assoc in H |- *.
    repeat rewrite <- lpow_add in H |- *.
    applys_eq H; flia.
Qed.

Lemma left_emit_calls k u :
  sideRLs (flip source_tm) ([left_hash]^^k)
    (ordinary_left u) (ordinary_left (u+k)).
Proof.
  induction k as [|k IH] in u |- *.
  - cbn [lpow]. replace (u + 0) with u by flia. constructor.
  - cbn [lpow]; eapply sideRLs_trans.
    + apply left_emit_call.
    + applys_eq (IH (S u)); flia.
Qed.

Lemma ordinary_emit_progress u r :
  ordinary_left u {{{((F, []), L)}}} r -[source_tm]->+
  ordinary_left (S u) {{{((B, []), R)}}} r.
Proof.
  exact (sideRLs_1L _ _ _ _ _ (left_emit_call u) r).
Qed.

Lemma ordinary_seg_return k u input output r :
  segRLs source_tm (hashes^^(S k)) [] input output ->
  ordinary_left u {{{((B, []), R)}}} (input *> r) -[source_tm]->+
  ordinary_left (u + k) {{{((F, []), L)}}} (output *> r).
Proof.
  intro Hseg.
  pose proof (segRLs_sideRLs_concat Hseg
    (sideRLseq_O source_tm r)) as Hright.
  eapply sideRLs_concat.
  - applys_eq (left_emit_calls k u); flia.
  - applys_eq Hright.
    unfold left_hash; cbn.
    pose proof (lrcons_lpow1 (B, []) (F, []) (S k) ltac:(lia)) as Hl.
    replace (S k - 1) with k in Hl by lia.
    exact Hl.
Qed.

Lemma ordinary_seg_run k u input output r :
  segRLs source_tm (hashes^^(S k)) [] input output ->
  ordinary_left u {{{((B, []), R)}}} (input *> r) -[source_tm]->+
  ordinary_left (u + S k) {{{((B, []), R)}}} (output *> r).
Proof.
  intro Hseg.
  eapply progress_trans.
  - exact (ordinary_seg_return k u input output r Hseg).
  - applys_eq (ordinary_emit_progress (u+k) (output *> r)); flia.
Qed.

Lemma ordinary_seg_run_pos calls u input output r :
  1 <= calls -> segRLs source_tm (hashes^^calls) [] input output ->
  ordinary_left u {{{((B, []), R)}}} (input *> r) -[source_tm]->+
  ordinary_left (u + calls) {{{((B, []), R)}}} (output *> r).
Proof.
  intros Hcalls Hseg.
  replace calls with (S (calls-1)) in Hseg |- * by lia.
  apply ordinary_seg_run, Hseg.
Qed.

Lemma raw_X_return l r :
  (X4 *> l) {{{((F, []), L)}}} r -[source_tm]->+
  l {{{((F, []), L)}}} (U *> r).
Proof.
  unfold source_tm.
  ut; esx.
Qed.

Lemma raw_X_returns u l r :
  (X4^^u *> l) {{{((F, []), L)}}} r -[source_tm]->*
  l {{{((F, []), L)}}} (U^^u *> r).
Proof.
  induction u as [|u IH] in l, r |- *.
  - cbn [lpow]. finish.
  - cbn [lpow].
    eapply evstep_trans.
    + apply progress_evstep.
      exact (raw_X_return (X4^^u *> l) r).
    + applys_eq (IH l (U *> r)); repeat rewrite <- Str_app_assoc;
        rewrite <- lpow_shift; reflexivity.
Qed.

Lemma ordinary_return_wall u r :
  ordinary_left u {{{((F, []), L)}}} r -[source_tm]->*
  common_left_wall {{{((F, []), L)}}} (U^^u *> r).
Proof.
  unfold ordinary_left.
  exact (raw_X_returns u common_left_wall r).
Qed.

Lemma ordinary_seg_to_wall k u input output r :
  segRLs source_tm (hashes^^(S k)) [] input output ->
  ordinary_left u {{{((B, []), R)}}} (input *> r) -[source_tm]->+
  common_left_wall {{{((B, []), R)}}}
    ((U^^(u + S k) ++ output) *> r).
Proof.
  intro Hseg.
  eapply progress_trans.
  - eapply progress_evstep_trans.
    + exact (ordinary_seg_return k u input output r Hseg).
    + applys_eq (ordinary_return_wall (u+k) (output *> r)).
  - replace (u+S k) with (S (u+k)) by lia; cbn [lpow].
    applys_eq (sobc1_emit_hash ((U^^(u+k) ++ output) *> r));
      repeat rewrite Str_app_assoc; reflexivity.
Qed.
Fixpoint z_tail_digits (n : nat) : list BDigit :=
  match n with
  | O => [BA; BA; BB; BB]
  | S n' => BA :: BB :: z_tail_digits n'
  end.
Definition z_digits (n : nat) : list BDigit :=
  BB :: BB :: BB :: z_tail_digits n.

Lemma z_tail_digits_length n : length (z_tail_digits n) = 2 * n + 4.
Proof.
  induction n; cbn; lia.
Qed.

Lemma z_digits_length n : length (z_digits n) = z_birth_width n.
Proof.
  unfold z_digits, z_birth_width.
  change (3 + length (z_tail_digits n) = 2 * n + 7)%nat.
  rewrite z_tail_digits_length. lia.
Qed.

Lemma z_digits_value_zero : digits_value (z_digits O) = 103.
Proof.
  reflexivity.
Qed.

Lemma z_digits_value_succ n :
  digits_value (z_digits (S n)) + 5 = 4 * digits_value (z_digits n).
Proof.
  unfold z_digits. cbn [z_tail_digits digits_value]. lia.
Qed.

Theorem z_digits_value n :
  Z.of_nat (digits_value (z_digits n)) = z_birth_value n.
Proof.
  induction n as [|n IH].
  - rewrite z_digits_value_zero. apply z_birth_zero.
  - pose proof (z_digits_value_succ n) as Hstep.
    rewrite z_birth_succ.
    zify. lia.
Qed.

Theorem digits_exist width value :
  value < 2 ^ width ->
  exists ds, length ds = width /\ digits_value ds = value.
Proof.
  revert value.
  induction width as [|width IH]; intros value Hvalue.
  - cbn [Nat.pow] in Hvalue. assert (value = 0%nat) by lia.
    subst value. exists (@nil BDigit); split; reflexivity.
  - rewrite Nat.pow_succ_r in Hvalue by lia.
    set (q := value / 2).
    set (r := value mod 2).
    assert (Hq : q < 2 ^ width).
    { unfold q. apply Nat.Div0.div_lt_upper_bound; lia. }
    destruct (IH q Hq) as [ds [Hlen Hdigits]].
    pose proof (Nat.div_mod value 2 ltac:(lia)) as Hsplit.
    pose proof (Nat.mod_upper_bound value 2 ltac:(lia)) as Hr.
    fold q r in Hsplit, Hr.
    destruct r as [|[|r]].
    + exists (BA :: ds). split.
      * cbn. lia.
      * cbn [digits_value]. rewrite Hdigits. lia.
    + exists (BB :: ds). split.
      * cbn. lia.
      * cbn [digits_value]. rewrite Hdigits. lia.
    + lia.
Qed.

Lemma cd_start :
  segRLs source_tm (hashes^^2) []
    (C8 ++ A8 ++ U^^2) (A8 ++ C8 ++ A8).
Proof.
  apply BoundedConfig.segRLs_c_spec with (T:=10000); reflexivity.
Qed.
Definition cd_calls (n : nat) : nat := 2 * (2^n - 1).
Definition cd_input (n : nat) : list Sym := C8 ++ A8 ++ U^^(2*n).
Definition cd_output (n : nat) : list Sym := A8^^n ++ C8 ++ A8.

Lemma cd_batch n :
  segRLs source_tm (hashes^^cd_calls n) []
    (cd_input n) (cd_output n).
Proof.
  induction n as [|n IH].
  - unfold cd_calls, cd_input, cd_output.
    cbn [Nat.pow lpow]. constructor.
  - pose proof (segRLs_concat cd_start
      (segRLs_O source_tm (U^^(2*n)))) as Hstart.
    pose proof (segRLs_concat (hash_A_cycles (cd_calls n)) IH) as Hrest.
    unfold cd_calls, cd_input, cd_output in *.
    rewrite Nat.pow_succ_r by lia.
    replace (2*S n) with (2+2*n) by lia; rewrite lpow_add.
    cbn [lpow]; repeat rewrite app_assoc in Hstart, Hrest |- *.
    applys_eq (segRLs_trans Hstart Hrest);
      rewrite <- lpow_add; f_equal; flia.
Qed.
Definition after_cd (n : nat) (tail : list Sym) : Q * tape :=
  ordinary_left (cd_calls n) {{{((B, []), R)}}}
    ((cd_output n ++ tail) *> 0inf).

Lemma cd_calls_positive n :
  1 <= n -> 1 <= cd_calls n.
Proof.
  unfold cd_calls; destruct n; [lia|].
  rewrite Nat.pow_succ_r by lia.
  generalize (Nat.pow_nonzero 2 n ltac:(lia)); lia.
Qed.

Lemma exception_done_cd n tail :
  1 <= n ->
  exception_done n tail -[source_tm]->+ after_cd n tail.
Proof.
  intro Hn; unfold exception_done, after_cd, ordinary_left.
  applys_eq (ordinary_seg_run_pos (cd_calls n) 0
    (cd_input n ++ tail) (cd_output n ++ tail) 0inf
    (cd_calls_positive n Hn)
    (segRLs_concat (cd_batch n) (segRLs_O source_tm tail))); flia.
Qed.

Lemma all_A_cycles width signals :
  segRLs source_tm
    (hashes^^(signals * 2^width))
    (hashes^^signals)
    (A8^^width) (A8^^width).
Proof.
  induction width as [|width IH] in signals |- *.
  - cbn [Nat.pow lpow]. replace (signals * 1) with signals by flia.
    apply segRLs_nil.
  - rewrite Nat.pow_succ_r by lia.
    applys_eq (segRLs_concat
      (hash_A_cycles (signals * 2^width)) (IH signals)); flia.
Qed.

Lemma primary_lift signals width input output :
  segRLs source_tm (hashes^^signals) [] input output ->
  segRLs source_tm (hashes^^(signals*2^width)) []
    (A8^^width ++ input) (A8^^width ++ output).
Proof.
  intro H. applys_eq (segRLs_concat (all_A_cycles width signals) H).
Qed.

Lemma primary_one_rule p w1 w2 :
  segRLs source_tm hashes [] w1 w2 ->
  segRLs source_tm (hashes^^(2^p)) []
    (A8^^p ++ w1) (A8^^p ++ w2).
Proof.
  intro Hrule.
  pose proof (segRLs_concat (all_A_cycles p 1) Hrule) as H.
  cbn [Nat.mul] in H.
  applys_eq H; flia.
Qed.
Definition ca_pair_calls (width : nat) : nat := 2 * 2^width.

Lemma ca_pair0 : segRLs source_tm (hashes^^2) [] (C8 ++ C8) (A8^^2).
Proof.
  apply BoundedConfig.segRLs_c_spec with (T:=10000); reflexivity.
Qed.

Lemma ca_pair width rest :
  segRLs source_tm (hashes^^ca_pair_calls width) []
    (A8^^width ++ C8 ++ C8 ++ rest)
    (A8^^(width+2) ++ rest).
Proof.
  unfold ca_pair_calls; rewrite lpow_add.
  applys_eq (segRLs_concat (primary_lift 2 width _ _ ca_pair0)
    (segRLs_O source_tm rest)); repeat rewrite app_assoc; reflexivity.
Qed.
Fixpoint c_sweep_calls (width pairs : nat) : nat :=
  match pairs with
  | O => O
  | S pairs' => ca_pair_calls width + c_sweep_calls (width+2) pairs'
  end.

Lemma c_sweep width pairs rest :
  segRLs source_tm
    (hashes^^c_sweep_calls width pairs) []
    (A8^^width ++ C8^^(2*pairs+1) ++ rest)
    (A8^^(width+2*pairs) ++ C8 ++ rest).
Proof.
  induction pairs as [|pairs IH] in width |- *.
  - cbn [c_sweep_calls]. applys_eq (segRLs_O source_tm
      (A8^^width ++ C8 ++ rest)); flia.
  - cbn [c_sweep_calls].
    pose proof (ca_pair width
      (C8^^(2*pairs+1) ++ rest)) as Hpair.
    pose proof (IH (width+2)) as Htail.
    replace (2*S pairs+1) with (2+(2*pairs+1)) by lia; rewrite lpow_add.
    replace (width+2*S pairs) with ((width+2)+2*pairs) by lia.
    repeat rewrite <- app_assoc in Hpair, Htail |- *.
    applys_eq (segRLs_trans Hpair Htail); rewrite <- lpow_add; reflexivity.
Qed.
Definition ca_finish_calls (width : nat) : nat := 4 * 2^width.

Lemma ca_finish0 :
  segRLs source_tm (hashes^^4) []
    (C8 ++ B8 ++ U ++ [1;1;1;1] ++ A8 ++ B8 ++ A8)
    (A8^^3 ++ U^^2 ++ B8 ++ B8).
Proof.
  apply BoundedConfig.segRLs_c_spec with (T:=10000); reflexivity.
Qed.

Lemma ca_finish width rest :
  segRLs source_tm
    (hashes^^ca_finish_calls width) []
    (A8^^width ++ C8 ++ B8 ++ U ++ [1;1;1;1] ++
      A8 ++ B8 ++ A8 ++ rest)
    (A8^^(width+3) ++ U^^2 ++ B8 ++ B8 ++ rest).
Proof.
  unfold ca_finish_calls; rewrite lpow_add.
  applys_eq (segRLs_concat (primary_lift 4 width _ _ ca_finish0)
    (segRLs_O source_tm rest)); repeat rewrite <- app_assoc; reflexivity.
Qed.
Definition ca_start_calls (width : nat) : nat := 2 * 2^width.

Lemma ca_start0 k :
  segRLs source_tm (hashes^^2) []
    (C8 ++ A8^^k ++ B8 ++ B8 ++ A8 ++ B8 ++ A8)
    (A8 ++ C8^^k ++ B8 ++ U ++ [1;1;1;1] ++ A8 ++ B8 ++ A8).
Proof.
  pose proof (segRLs_concat (sobc1_hash_CAB1110 k)
    (segRLs_O source_tm ([1;1;1;1] ++ A8 ++ B8 ++ A8))) as H1.
  pose proof (segRLs_concat hash_D
    (segRLs_O source_tm (C8^^k ++ B8 ++ U ++ [1;1;1;1] ++ A8 ++ B8 ++ A8))) as H2.
  assert (H2' : segRLs source_tm hashes []
      ((D8++C8^^k++B8++U) ++ [1;1;1;1]++A8++B8++A8)
      (A8++C8^^k++B8++U++[1;1;1;1]++A8++B8++A8)).
  { applys_eq H2; repeat rewrite <- app_assoc; reflexivity. }
  applys_eq (segRLs_trans H1 H2'); cbn [lpow];
    repeat rewrite app_nil_r; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma ca_start width k rest :
  segRLs source_tm
    (hashes^^ca_start_calls width) []
    (A8^^width ++ C8 ++ A8^^k ++ B8 ++ B8 ++
      A8 ++ B8 ++ A8 ++ rest)
    (A8^^(width+1) ++ C8^^k ++ B8 ++ U ++ [1;1;1;1] ++
      A8 ++ B8 ++ A8 ++ rest).
Proof.
  unfold ca_start_calls; rewrite lpow_add.
  applys_eq (segRLs_concat (primary_lift 2 width _ _ (ca_start0 k))
    (segRLs_O source_tm rest)); repeat rewrite <- app_assoc; reflexivity.
Qed.
Definition ca_calls (primary pairs : nat) : nat :=
  ca_start_calls primary +
  (c_sweep_calls (primary+1) pairs +
   ca_finish_calls (primary+1+2*pairs)).

Lemma ca_batch primary pairs rest :
  segRLs source_tm
    (hashes^^ca_calls primary pairs) []
    (A8^^primary ++ C8 ++ A8^^(2*pairs+1) ++
      B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ rest)
    (A8^^(primary+2*pairs+4) ++ U^^2 ++ B8 ++ B8 ++ rest).
Proof.
  pose proof (ca_start primary (2*pairs+1) rest) as Hstart.
  pose proof (c_sweep (primary+1) pairs
    (B8 ++ U ++ [1;1;1;1] ++ A8 ++ B8 ++ A8 ++ rest)) as Hsweep.
  pose proof (ca_finish (primary+1+2*pairs) rest) as Hfinish.
  unfold ca_calls.
  applys_eq (segRLs_trans Hstart (segRLs_trans Hsweep Hfinish)).
  - rewrite !lpow_add; reflexivity.
  - replace (primary+2*pairs+4) with (primary+1+2*pairs+3) by lia;
      reflexivity.
Qed.
Record BinaryColumn := mkBinaryColumn {
  column_e : nat;
  column_digits : list BDigit;
  column_length : length column_digits = S column_e
}.
Definition mixed_column_word (c : BinaryColumn) : list Sym :=
  E8^^column_e c ++ A8.
Definition binary_column_word (c : BinaryColumn) : list Sym :=
  digits_word (column_digits c).
Definition column_required (out : nat) (c : BinaryColumn) : nat :=
  (out + 1) * 2 ^ S (column_e c) - 2 +
    digits_value (column_digits c).
Fixpoint mixed_columns_required (columns : list BinaryColumn) : nat :=
  match columns with
  | [] => 0
  | c :: columns' => column_required (mixed_columns_required columns') c
  end.
Fixpoint spaced_words (words : list (list Sym)) : list Sym :=
  match words with
  | [] => []
  | [word] => word
  | word :: words' => word ++ U^^2 ++ spaced_words words'
  end.
Definition mixed_columns_word columns :=
  spaced_words (map mixed_column_word columns).
Definition binary_columns_word columns :=
  spaced_words (map binary_column_word columns).

Lemma mixed_column_spec c out :
  segRLs source_tm (hashes ^^ column_required out c) (hashes ^^ out)
    (mixed_column_word c) (binary_column_word c).
Proof.
  destruct c as [e ds Hlen].
  unfold column_required, mixed_column_word, binary_column_word; cbn.
  exact (standard_mixed_to_binary_out_spec e ds out Hlen).
Qed.
(** Exact arbitrary-length odometer composition.  Each separator is handled
    as a column-local identity carrying the emitted stream into the next
    column, so no global phase synchronization is assumed. *)

Theorem mixed_columns_spec columns :
  segRLs source_tm (hashes ^^ mixed_columns_required columns) []
    (mixed_columns_word columns) (binary_columns_word columns).
Proof.
  induction columns as [|c columns IH].
  - cbn [mixed_columns_required mixed_columns_word binary_columns_word lpow].
    constructor.
  - destruct columns as [|c' columns].
    + cbn [mixed_columns_required mixed_columns_word binary_columns_word].
      change (segRLs source_tm (hashes ^^ column_required 0 c) (hashes ^^ 0)
        (mixed_column_word c) (binary_column_word c)).
      exact (mixed_column_spec c 0).
    + cbn [mixed_columns_required mixed_columns_word binary_columns_word] in IH |- *.
      eapply segRLs_concat.
      * exact (mixed_column_spec c
          (column_required (mixed_columns_required columns) c')).
      * eapply segRLs_concat.
        -- exact (hashes_U_run
             (column_required (mixed_columns_required columns) c') 2).
        -- exact IH.
Qed.
Definition widths_sum (es : list nat) : nat :=
  fold_right (fun e n => S e+n) 0%nat es.

Lemma widths_sum_nil : widths_sum [] = 0%nat.
Proof.
  reflexivity.
Qed.

Lemma widths_sum_cons e es : widths_sum (e::es) = S e + widths_sum es.
Proof.
  reflexivity.
Qed.
Definition columns_widths columns := map S (map column_e columns).
Definition columns_width_sum columns :=
  fold_right Nat.add 0%nat (columns_widths columns).

Lemma columns_width_sum_cons c columns :
  columns_width_sum (c :: columns) = S (column_e c) + columns_width_sum columns.
Proof.
  reflexivity.
Qed.

Lemma columns_width_sum_singleton c :
  columns_width_sum [c] = S (column_e c).
Proof.
  unfold columns_width_sum, columns_widths; cbn; lia.
Qed.

Lemma widths_sum_column_es columns :
  widths_sum (map column_e columns) = columns_width_sum columns.
Proof.
  induction columns; unfold widths_sum, columns_width_sum, columns_widths in *;
    cbn in *; [reflexivity|now rewrite IHcolumns].
Qed.

Lemma map_S_injective xs ys : map S xs = map S ys -> xs = ys.
Proof.
  induction xs as [|x xs IH] in ys |- *; destruct ys as [|y ys];
    cbn; intro H; try discriminate; [reflexivity|].
  inversion H; subst; f_equal; auto.
Qed.

Lemma columns_width_sum_positive columns :
  columns <> [] -> 1 <= columns_width_sum columns.
Proof.
  destruct columns; cbn; [contradiction|lia].
Qed.
Fixpoint geom4n (n : nat) : nat :=
  match n with
  | O => O
  | S n' => 1 + 4 * geom4n n'
  end.
Definition half_parameter (n : nat) : nat := 2*n+6.
Definition round_primary_width (current previous : nat) : nat :=
  half_parameter current + half_parameter previous + 6.
Definition round_outer_suffix (previous : nat) : list BDigit :=
  [BB; BB; BA; BB; BA; BB] ++ z_tail_digits previous.
Definition round_outer_digits (current previous : nat) : list BDigit :=
  repeat BA (half_parameter current + 2) ++
    round_outer_suffix previous.
Definition round_post_unary (current previous : nat) : nat :=
  cd_calls (half_parameter current) +
    ca_calls (half_parameter current) (previous+4).

Lemma geom4n_succ n : geom4n (S n) = 1 + 4 * geom4n n.
Proof.
  reflexivity.
Qed.

Lemma c_sweep_calls_formula width pairs :
  c_sweep_calls width pairs = 2^(width+1) * geom4n pairs.
Proof.
  induction pairs as [|pairs IH] in width |- *.
  - cbn [c_sweep_calls geom4n]. lia.
  - cbn [c_sweep_calls geom4n].
    unfold ca_pair_calls; rewrite IH.
    replace (2^(width+2+1)) with (2^(width+1)*2^2).
    2: { rewrite <- Nat.pow_add_r; f_equal; lia. }
    rewrite (Nat.pow_add_r 2 width 1); cbn [Nat.pow]; ring.
Qed.

Lemma ca_calls_formula primary pairs :
  ca_calls primary pairs =
    2^(primary+1) +
    (2^(primary+2) * geom4n pairs + 2^(primary+2*pairs+3)).
Proof.
  unfold ca_calls, ca_start_calls, ca_finish_calls.
  rewrite c_sweep_calls_formula.
  replace (2*2^primary) with (2^(primary+1)).
  2: { rewrite Nat.pow_add_r; cbn [Nat.pow]; ring. }
  replace (4*2^(primary+1+2*pairs)) with (2^(primary+2*pairs+3)).
  2: {
    replace (primary+2*pairs+3) with ((primary+1+2*pairs)+2) by lia.
    rewrite Nat.pow_add_r; cbn [Nat.pow]; lia. }
  replace (primary+1+1) with (primary+2) by lia.
  reflexivity.
Qed.

Lemma cd_calls_formula n :
  1 <= n -> cd_calls n = 2^(n+1)-2.
Proof.
  intro; unfold cd_calls; rewrite Nat.pow_add_r; cbn [Nat.pow].
  generalize (pow2_pos n); unfold pow2; lia.
Qed.

Lemma round_post_unary_formula current previous :
  round_post_unary current previous =
    2^(half_parameter current+2) *
      (1 + geom4n (previous+4) + 2^(2*(previous+4)+1)) - 2.
Proof.
  unfold round_post_unary.
  rewrite cd_calls_formula by (unfold half_parameter; lia).
  rewrite ca_calls_formula.
  assert (Hstep : 2^(half_parameter current+2) =
      2*2^(half_parameter current+1)).
  {
    replace (half_parameter current+2)
      with (S (half_parameter current+1)) by lia.
    rewrite Nat.pow_succ_r'; lia. }
  rewrite Hstep.
  replace (2^(half_parameter current+2*(previous+4)+3))
    with ((2*2^(half_parameter current+1))*2^(2*(previous+4)+1)).
  2: { rewrite <- Hstep, <- Nat.pow_add_r; f_equal; lia. }
  assert (2 <= 2^(half_parameter current+1)).
  { rewrite Nat.pow_add_r; cbn [Nat.pow].
    generalize (pow2_pos (half_parameter current)); unfold pow2; lia. }
  nia.
Qed.

Lemma digits_value_app ds1 ds2 :
  digits_value (ds1 ++ ds2) =
    digits_value ds1 + 2^(length ds1) * digits_value ds2.
Proof.
  induction ds1 as [|d ds1 IH].
  - cbn [List.app digits_value List.length Nat.pow]. lia.
  - destruct d; cbn [List.app digits_value List.length];
      rewrite IH, Nat.pow_succ_r'; ring.
Qed.

Lemma digits_value_repeat_BA n : digits_value (repeat BA n) = 0%nat.
Proof.
  induction n; cbn [repeat digits_value]; lia.
Qed.

Lemma round_outer_suffix_length previous :
  length (round_outer_suffix previous) = 2*previous+10.
Proof.
  unfold round_outer_suffix. rewrite length_app, z_tail_digits_length.
  cbn. lia.
Qed.

Lemma round_outer_digits_length current previous :
  length (round_outer_digits current previous) =
    round_primary_width current previous.
Proof.
  unfold round_outer_digits, round_primary_width, half_parameter.
  rewrite length_app, repeat_length, round_outer_suffix_length. lia.
Qed.

Lemma round_outer_suffix_zero : digits_value (round_outer_suffix 0) = 811.
Proof.
  reflexivity.
Qed.

Lemma round_outer_suffix_succ previous :
  digits_value (round_outer_suffix (S previous)) + 1 =
    4 * digits_value (round_outer_suffix previous).
Proof.
  unfold round_outer_suffix.
  rewrite !digits_value_app.
  cbn [z_tail_digits digits_value List.length Nat.pow]. lia.
Qed.

Lemma round_outer_suffix_formula previous :
  2 * digits_value (round_outer_suffix previous) =
    1 + geom4n (previous+4) +
      2^(2*(previous+4)+1) + 2^(2*(previous+4)+2).
Proof.
  induction previous as [|previous IH].
  - rewrite round_outer_suffix_zero. reflexivity.
  - pose proof (round_outer_suffix_succ previous) as Hstep.
    replace (S previous+4) with (S (previous+4)) by lia.
    rewrite geom4n_succ.
    replace (2^(2*S (previous+4)+1))
      with (4*2^(2*(previous+4)+1)).
    2: {
      replace (2*S (previous+4)+1)
        with ((2*(previous+4)+1)+2) by lia.
      rewrite (Nat.pow_add_r 2 (2*(previous+4)+1) 2).
      cbn [Nat.pow]; lia. }
    replace (2^(2*S (previous+4)+2))
      with (4*2^(2*(previous+4)+2)).
    2: {
      replace (2*S (previous+4)+2)
        with ((2*(previous+4)+2)+2) by lia.
      rewrite (Nat.pow_add_r 2 (2*(previous+4)+2) 2).
      cbn [Nat.pow]; lia. }
    nia.
Qed.

Lemma round_outer_digits_value current previous :
  digits_value (round_outer_digits current previous) =
    2^(half_parameter current+1) *
      (1 + geom4n (previous+4) +
        2^(2*(previous+4)+1) + 2^(2*(previous+4)+2)).
Proof.
  unfold round_outer_digits.
  rewrite digits_value_app, digits_value_repeat_BA, repeat_length.
  assert (Hstep : 2^(half_parameter current+2) =
      2*2^(half_parameter current+1)).
  { replace (half_parameter current+2)
      with (S (half_parameter current+1)) by lia.
    rewrite Nat.pow_succ_r'; lia. }
  rewrite Hstep.
  pose proof (round_outer_suffix_formula previous); nia.
Qed.

Theorem round_unary_decodes_outer current previous :
  round_post_unary current previous / 2 + 1 +
      2^(round_primary_width current previous-1) =
    digits_value (round_outer_digits current previous).
Proof.
  rewrite round_post_unary_formula, round_outer_digits_value.
  assert (Hhalf : forall n q, 1 <= q ->
      (2^(n+2)*q-2)/2+1 = 2^(n+1)*q).
  { intros n q Hq.
    assert (Hpow : 2^(n+2) = 2*2^(n+1)).
    { replace (n+2) with (S (n+1)) by lia.
      rewrite Nat.pow_succ_r'; lia. }
    rewrite Hpow.
    pose proof (Nat.pow_nonzero 2 (n+1) ltac:(lia)).
    replace (2*2^(n+1)*q-2) with (2*(2^(n+1)*q-1)) by nia.
    replace (2*(2^(n+1)*q-1)) with ((2^(n+1)*q-1)*2) by ring.
    rewrite Nat.div_mul by lia; nia. }
  rewrite Hhalf by lia.
  replace (2^(round_primary_width current previous-1))
    with (2^(half_parameter current+1)*2^(2*(previous+4)+2)).
  2: {
    rewrite <- Nat.pow_add_r; f_equal.
    unfold round_primary_width, half_parameter; lia. }
  ring.
Qed.

Lemma digits_word_repeat_BA n : digits_word (repeat BA n) = A8^^(n).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [repeat digits_word digit_word lpow]. rewrite IH. reflexivity.
Qed.

Lemma digits_word_app ds1 ds2 :
  digits_word (ds1 ++ ds2) = digits_word ds1 ++ digits_word ds2.
Proof.
  induction ds1 as [|d ds1 IH].
  - reflexivity.
  - destruct d; cbn [List.app digits_word digit_word].
    all: rewrite IH; reflexivity.
Qed.

Lemma round_outer_digits_word current previous :
  digits_word (round_outer_digits current previous) =
    A8^^(half_parameter current+2) ++
    B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ B8 ++
    digits_word (z_tail_digits previous).
Proof.
  unfold round_outer_digits, round_outer_suffix.
  rewrite !digits_word_app, digits_word_repeat_BA.
  cbn [digits_word digit_word].
  repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma z_digits_word_split previous :
  digits_word (z_digits previous) =
    B8 ++ B8 ++ B8 ++ digits_word (z_tail_digits previous).
Proof.
  reflexivity.
Qed.
(** The physical dotted edge is a genuine column.  The first carry into its
    last [B] word creates [E 11]; the two following full low-word sweeps turn
    [E] into [D] and then [A]. *)

Lemma sobc1_B_blank :
  sideRLs source_tm hashes
    (B8 *> 0inf) ((E8 ++ [1;1]) *> 0inf).
Proof.
  unfold source_tm.
  ut; esx.
Qed.

Lemma sobc1_Bs_blank w :
  sideRLs source_tm hashes
    ((B8^^(S w)) *> 0inf)
    ((A8^^w ++ E8 ++ [1;1]) *> 0inf).
Proof.
  induction w as [|w IH].
  - exact sobc1_B_blank.
  - cbn [lpow].
    eapply @segRLs_sideRLs_concat with (w1:=B8) (w2:=A8).
    + exact (hash_B).
    + applys_eq IH.
Qed.

Lemma sobc1_As_E w :
  sideRLs source_tm (hashes^^(2^w))
    ((A8^^w ++ E8 ++ [1;1]) *> 0inf)
    ((A8^^w ++ D8 ++ [1;1]) *> 0inf).
Proof.
  applys_eq (segRLs_sideRLs_concat
    (segRLs_concat (all_A_cycles w 1) hash_E)
    (sideRLseq_O source_tm ([1;1] *> 0inf))).
  all: cbn [Nat.mul]; rewrite ?Nat.add_0_r;
    repeat rewrite Str_app_assoc; repeat rewrite app_assoc;
    rewrite ?lpow_S, ?lpow_shift, ?lpow_shift'; reflexivity.
Qed.

Lemma sobc1_As_D w :
  sideRLs source_tm (hashes^^(2^w))
    ((A8^^w ++ D8 ++ [1;1]) *> 0inf)
    ((A8^^(S w) ++ [1;1]) *> 0inf).
Proof.
  applys_eq (segRLs_sideRLs_concat
    (segRLs_concat (all_A_cycles w 1) hash_D)
    (sideRLseq_O source_tm ([1;1] *> 0inf))).
  all: cbn [Nat.mul]; rewrite ?Nat.add_0_r;
    repeat rewrite Str_app_assoc; repeat rewrite app_assoc;
    rewrite ?lpow_S, ?lpow_shift, ?lpow_shift'; reflexivity.
Qed.

Lemma sobc1_B_edge w :
  sideRLs source_tm (hashes^^((2^(S w))+1))
    ((B8^^(S w)) *> 0inf) ((A8^^(S w) ++ [1;1]) *> 0inf).
Proof.
  applys_eq (sideRLs_trans (sobc1_Bs_blank w)
    (sideRLs_trans (sobc1_As_E w) (sobc1_As_D w))).
  rewrite Nat.pow_succ_r'.
  replace (2*2^w+1) with (1+2^w+2^w) by lia.
  rewrite !lpow_add; cbn [lpow]; reflexivity.
Qed.

Lemma all_B_carry w :
  segRLs source_tm hashes hashes (B8^^S w) (A8^^S w).
Proof.
  induction w; cbn [lpow]; [exact hash_B|].
  exact (segRLs_concat hash_B IHw).
Qed.

Lemma binary_column_carry_to_zero c out :
  segRLs source_tm
    (hashes^^S (bfinish_count (column_digits c) out))
    (hashes^^S out)
    (binary_column_word c) (A8^^S (column_e c)).
Proof.
  destruct c as [e ds Hlen].
  unfold binary_column_word; cbn.
  pose proof (bfinish_spec ds out) as Hfinish.
  rewrite Hlen in Hfinish.
  applys_eq (segRLs_trans Hfinish (all_B_carry e));
    cbn [lpow]; rewrite ?lpow_shift; reflexivity.
Qed.
Definition all_A_columns_word columns :=
  spaced_words (map (fun c => A8^^S (column_e c)) columns).

Lemma binary_columns_word_cons2 c c' columns :
  binary_columns_word (c::c'::columns) =
    binary_column_word c ++ U^^2 ++ binary_columns_word (c'::columns).
Proof.
  reflexivity.
Qed.

Lemma all_A_columns_word_cons2 c c' columns :
  all_A_columns_word (c::c'::columns) =
    A8^^S (column_e c) ++ U^^2 ++ all_A_columns_word (c'::columns).
Proof.
  reflexivity.
Qed.
Fixpoint columns_frontier_count (columns : list BinaryColumn) : nat :=
  match columns with
  | [] => 0
  | [c] => bfinish_count (column_digits c) 0 +
      2^S (column_e c) + 1
  | c :: columns' =>
      S (bfinish_count (column_digits c)
        (columns_frontier_count columns' - 1))
  end.

Lemma columns_frontier_count_positive columns :
  columns <> [] -> 1 <= columns_frontier_count columns.
Proof.
  destruct columns as [|c columns]; [contradiction|].
  destruct columns; cbn [columns_frontier_count]; lia.
Qed.

Theorem binary_columns_to_frontier columns :
  columns <> [] ->
  sideRLs source_tm
    (hashes^^columns_frontier_count columns)
    ((binary_columns_word columns) *> 0inf)
    ((all_A_columns_word columns ++ [1;1]) *> 0inf).
Proof.
  induction columns as [|c columns IH]; intro Hnonempty.
  - contradiction.
  - destruct columns as [|c' columns].
    + cbn [binary_columns_word all_A_columns_word columns_frontier_count].
      pose proof (bfinish_spec (column_digits c) 0) as Hfinish.
      rewrite (column_length c) in Hfinish.
      applys_eq (sideRLs_trans (segRLs_0inf
        Hfinish)
        (sobc1_B_edge (column_e c)));
        repeat rewrite <- lpow_add; flia.
    + pose proof (IH ltac:(discriminate)) as Htail.
      set (n := columns_frontier_count (c' :: columns)).
      cbn [binary_columns_word all_A_columns_word
        columns_frontier_count].
      fold n in Htail.
      assert (Hn : n = S (n-1)).
      { unfold n; generalize (columns_frontier_count_positive
          (c'::columns) ltac:(discriminate)); lia. }
      rewrite Hn in Htail.
      applys_eq (segRLs_sideRLs_concat
        (segRLs_concat (binary_column_carry_to_zero c (n-1))
          (hashes_U_run (S (n-1)) 2)) Htail);
        unfold n; generalize (columns_frontier_count_positive
          (c'::columns) ltac:(discriminate)); flia.
      all: intro; rewrite ?binary_columns_word_cons2, ?all_A_columns_word_cons2;
        repeat rewrite Str_app_assoc; repeat rewrite app_assoc; reflexivity.
Qed.

Lemma raw_separator_return l r :
  ([1;0;1] *> X4^^2 *> Q8 *> l) {{{((F, []), L)}}} r
    -[source_tm]->+
  ([1;0;1] *> l) {{{((F, []), L)}}}
    ((A8 ++ U^^2) *> r).
Proof.
  unfold source_tm.
  ut; esx.
Qed.

Lemma raw_Bs_to_Qs k :
  segRR source_tm (B, []) (B, []) (B8^^k) (Q8^^k).
Proof.
  apply segRR_lpow_same, raw_B_forward.
Qed.

Lemma raw_B_returns k l r :
  ([1;0;1] *> Q8^^k *> l) {{{((F, []), L)}}} r
    -[source_tm]->*
  ([1;0;1] *> l) {{{((F, []), L)}}} (E8^^k *> r).
Proof.
  induction k as [|k IH] in l, r |- *.
  - cbn [lpow]. finish.
  - cbn [lpow].
    eapply evstep_trans.
    + apply progress_evstep.
      applys_eq (raw_B_return (Q8^^k *> l) r).
    + applys_eq (IH l (E8 *> r)).
      repeat rewrite <- Str_app_assoc.
      rewrite <- lpow_shift. reflexivity.
Qed.
Definition full_exception_columns es :=
  spaced_words (map (fun e => B8^^S e) es) ++ [1;1].
Definition initialized_mixed_columns es :=
  spaced_words (map (fun e => E8^^e ++ A8) es).

Lemma full_exception_columns_cons2 e e' es :
  full_exception_columns (e::e'::es) =
    B8^^S e ++ U^^2 ++ full_exception_columns (e'::es).
Proof.
  unfold full_exception_columns; cbn [List.map spaced_words].
  repeat rewrite app_assoc; reflexivity.
Qed.

Lemma initialized_mixed_columns_cons2 e e' es :
  initialized_mixed_columns (e::e'::es) =
    (E8^^e ++ A8) ++ U^^2 ++ initialized_mixed_columns (e'::es).
Proof.
  unfold initialized_mixed_columns; cbn [List.map spaced_words].
  repeat rewrite app_assoc; reflexivity.
Qed.

Lemma raw_exception_columns es l :
  es <> [] ->
  l {{{((B, []), R)}}} (full_exception_columns es *> 0inf)
    -[source_tm]->+
  ([1;0;1] *> l) {{{((F, []), L)}}}
    (initialized_mixed_columns es *> 0inf).
Proof.
  induction es as [|e es IH] in l |- *; intro Hnonempty.
  - contradiction.
  - destruct es as [|e' es].
    + cbn [full_exception_columns initialized_mixed_columns].
      exact (raw_exception_tail e l).
    + cbn [full_exception_columns initialized_mixed_columns].
      eapply evstep_progress_trans.
      * applys_eq (raw_Bs_to_Qs (S e) l
          ((U^^2 ++ full_exception_columns (e' :: es)) *> 0inf));
          rewrite ?full_exception_columns_cons2;
          repeat rewrite Str_app_assoc; repeat rewrite app_assoc; reflexivity.
      * eapply evstep_progress_trans.
        -- applys_eq (raw_Us_to_Xs 2 (Q8^^(S e) *> l)
             (full_exception_columns (e' :: es) *> 0inf)).
        -- eapply progress_trans.
           ++ exact (IH (X4^^2 *> Q8^^(S e) *> l) ltac:(discriminate)).
           ++ eapply progress_evstep_trans.
              ** applys_eq (raw_separator_return (Q8^^e *> l)
                   (initialized_mixed_columns (e' :: es) *> 0inf)).
              ** applys_eq (raw_B_returns e l
                   ((A8 ++ U^^2 ++ initialized_mixed_columns (e' :: es)) *>
                     0inf)); rewrite ?initialized_mixed_columns_cons2;
                   repeat rewrite Str_app_assoc;
                   repeat rewrite app_assoc; reflexivity.
Qed.
Definition exception_columns_raw_source (n : nat) (es : list nat) : Q * tape :=
  common_left_wall {{{((B, []), R)}}}
    ((U^^(2*n+1) ++ full_exception_columns es) *> 0inf).
Definition exception_columns_pre (n : nat) (es : list nat) : Q * tape :=
  exception_pre_left n {{{((F, []), L)}}}
    (initialized_mixed_columns es *> 0inf).

Lemma exception_columns_raw_to_pre n es :
  es <> [] ->
  exception_columns_raw_source n es -[source_tm]->*
    exception_columns_pre n es.
Proof.
  intro Hnonempty.
  unfold exception_columns_raw_source, exception_columns_pre.
  apply progress_evstep.
  eapply evstep_progress_trans.
  - applys_eq (raw_Us_to_Xs (2*n+1) common_left_wall
      (full_exception_columns es *> 0inf)).
    repeat rewrite Str_app_assoc. reflexivity.
  - applys_eq (raw_exception_columns es
      (common_left_wall <* (X4^^(2*n+1))) Hnonempty).
    unfold common_left_wall.
    repeat rewrite Str_app_assoc.
    rewrite exception_pre_left_direct.
    reflexivity.
Qed.

Theorem sobc1_exception_columns_from_seg n es output :
  es <> [] ->
  segRLs source_tm (hashes^^n) []
    (initialized_mixed_columns es) output ->
  exception_columns_raw_source n es -[source_tm]->*
    exception_done n output.
Proof.
  intros Hnonempty Hseg.
  eapply evstep_trans.
  - exact (exception_columns_raw_to_pre n es Hnonempty).
  - apply progress_evstep.
    exact (exception_pre_from_seg n (initialized_mixed_columns es) output Hseg).
Qed.

Lemma initialized_mixed_columns_eq es columns :
  columns_widths columns = map S es ->
  initialized_mixed_columns es = mixed_columns_word columns.
Proof.
  unfold columns_widths; intro H; apply map_S_injective in H; subst es.
  unfold initialized_mixed_columns, mixed_columns_word, mixed_column_word.
  rewrite map_map. reflexivity.
Qed.

Lemma digits_value_BBBA_pairs k :
  digits_value ([BB; BA]^^k) = geom4n k.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - cbn [lpow geom4n]. rewrite digits_value_app, IH.
    cbn [digits_value List.length Nat.pow]. ring.
Qed.
Definition sobc1_second_tail_digits : list BDigit :=
  [BB] ++ ([BB; BA]^^9) ++ [BA; BB; BB; BB; BA].

Lemma sobc1_second_tail_length :
  length sobc1_second_tail_digits = 24.
Proof.
  unfold sobc1_second_tail_digits.
  rewrite !length_app, lpow_length. reflexivity.
Qed.

Lemma sobc1_second_tail_value :
  2 * digits_value sobc1_second_tail_digits =
    1 + geom4n 10 + 7 * 2^21.
Proof.
  unfold sobc1_second_tail_digits.
  rewrite !digits_value_app, digits_value_BBBA_pairs.
  rewrite lpow_length.
  cbn [digits_value List.length].
  rewrite (geom4n_succ 9).
  replace (9*2) with 18 by lia.
  replace 21 with (18+3) by lia.
  rewrite Nat.pow_add_r.
  replace (2^3) with 8 by reflexivity.
  replace (2^1) with 2 by reflexivity.
  ring.
Qed.

Lemma primary_D_absorb primary rest :
  segRLs source_tm (hashes^^(2^primary)) []
    (A8^^primary ++ D8 ++ rest)
    (A8^^(S primary) ++ rest).
Proof.
  applys_eq (primary_one_rule primary
    (D8 ++ rest) (A8 ++ rest)
    (segRLs_concat hash_D (segRLs_O source_tm rest))).
  rewrite lpow_S, <- lpow_shift, app_assoc; reflexivity.
Qed.

Lemma initial_u_pairs primary pairs rest :
  segRLs source_tm
    (hashes^^initial_u_pair_calls primary pairs) []
    (A8^^primary ++ C8 ++ A8 ++ U^^(2*pairs) ++ rest)
    (A8^^(primary+pairs) ++ C8 ++ A8 ++ rest).
Proof.
  induction pairs as [|pairs IH] in primary |- *.
  - cbn [initial_u_pair_calls lpow].
    replace (primary + 0) with primary by lia.
    apply segRLs_O.
  - cbn [initial_u_pair_calls].
    replace (2 * S pairs) with (2 + 2*pairs) by lia.
    rewrite lpow_add.
    pose proof (primary_one_rule primary
      (C8 ++ A8 ++ U^^2 ++ U^^(2*pairs) ++ rest)
      (D8 ++ C8 ++ A8 ++ U^^(2*pairs) ++ rest)
      (segRLs_concat (hash_CAUU)
        (segRLs_O source_tm (U^^(2*pairs) ++ rest)))) as Hca.
    pose proof (primary_D_absorb primary
      (C8 ++ A8 ++ U^^(2*pairs) ++ rest)) as Hd.
    applys_eq (segRLs_trans Hca (segRLs_trans Hd (IH (S primary)))).
    + replace (2*2^primary) with (2^primary+2^primary) by lia.
      rewrite lpow_add, app_assoc; reflexivity.
    + replace (primary+S pairs) with (S primary+pairs) by lia.
      reflexivity.
Qed.
Opaque Nat.pow.

Lemma primary_one_side_rule primary input output :
  sideRLs source_tm hashes input output ->
  sideRLs source_tm (hashes^^(2^primary))
    ((A8^^primary) *> input) ((A8^^primary) *> output).
Proof.
  intro Htail.
  pose proof (segRLs_sideRLs_concat
    (all_A_cycles primary 1) Htail) as H.
  cbn [Nat.mul] in H.
  applys_eq H.
  - replace (2^primary+0) with (2^primary) by lia. reflexivity.
Qed.

Lemma bfinish_count_app ds1 ds2 out :
  bfinish_count (ds1 ++ ds2) out =
    bfinish_count ds1 (bfinish_count ds2 out).
Proof.
  induction ds1 as [|d ds1 IH]; [reflexivity|].
  destruct d; cbn [List.app bfinish_count]; congruence.
Qed.

Lemma primary_single_B_D low :
  segRLs source_tm (hashes^^(2^low)) []
    (A8^^low ++ B8 ++ D8 ++ [1;1])
    (A8^^(low+2) ++ [1;1]).
Proof.
  set (ds := repeat BA low ++ [BB]).
  set (c := mkBinaryColumn low ds ltac:(
    unfold ds; rewrite length_app, repeat_length; cbn; lia)).
  pose proof (binary_column_carry_to_zero c 0) as Hcarry.
  pose proof (segRLs_concat Hcarry
    (segRLs_concat (hash_D)
      (segRLs_O source_tm [1;1]))) as H.
  unfold c, ds, binary_column_word in H.
  cbn [column_e column_digits] in H.
  rewrite bfinish_count_app, bfinish_repeat_BA_formula in H.
  cbn [bfinish_count] in H.
  rewrite digits_word_app, digits_word_repeat_BA in H.
  cbn [digits_word digit_word List.length] in H.
  applys_eq H.
  - f_equal. generalize (Nat.pow_nonzero 2 low ltac:(lia)); lia.
  - rewrite app_nil_r; repeat rewrite app_assoc; reflexivity.
  - replace (low+2) with (S low+1) by lia.
    rewrite lpow_add; cbn [lpow]; rewrite app_nil_r;
      repeat rewrite app_assoc; reflexivity.
Qed.

Lemma sobc1_initial_pre_side :
  sideRLs source_tm
    (hashes^^sobc1_initial_pre_calls)
    ((A8^^3 ++ D8 ++ C8 ++ A8 ++ U^^28 ++
      A8 ++ A8 ++ B8 ++ A8) *> 0inf)
    ((A8^^24 ++ [1;1]) *> 0inf).
Proof.
  unfold sobc1_initial_pre_calls.
  assert (Hb1 : sideRLs source_tm hashes
      ((C8++A8++A8++A8++B8++A8) *> 0inf)
      ((D8++C8++C8++C8++B8++U++[1;0]++U) *> 0inf)).
  { apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. }
  assert (Hb3 : sideRLs source_tm hashes
      ((C8++B8++U++[1;0]++U) *> 0inf)
      ((D8++B8++D8++[1;1]) *> 0inf)).
  { apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. }
  pose proof (sideRLs_trans
    (segRLs_0inf (primary_D_absorb 3
      (C8++A8++U^^28++A8++A8++B8++A8)))
    (sideRLs_trans
    (segRLs_0inf (initial_u_pairs 4 14 (A8++A8++B8++A8)))
    (sideRLs_trans (primary_one_side_rule 18 _ _ Hb1)
    (sideRLs_trans (segRLs_0inf (primary_D_absorb 18
      (C8++C8++C8++B8++U++[1;0]++U)))
    (sideRLs_trans (segRLs_0inf (primary_one_rule 19 _ _
      (segRLs_concat sobc1_extra_CC
        (segRLs_O source_tm (C8++B8++U++[1;0]++U)))))
    (sideRLs_trans (segRLs_0inf ltac:(applys_eq (primary_D_absorb 19
      (A8++C8++B8++U++[1;0]++U))))
    (sideRLs_trans (primary_one_side_rule 21 _ _ Hb3)
    (sideRLs_trans (segRLs_0inf (primary_D_absorb 21
      (B8++D8++[1;1]))) (segRLs_0inf (primary_single_B_D 22)))))))))) as H.
  repeat rewrite <- lpow_add in H. exact H.
Qed.

Lemma zero_primary_finish_seg width rest :
  segRLs source_tm (hashes^^(2^width-1)) []
    (A8^^width ++ rest) (B8^^width ++ rest).
Proof.
  applys_eq (segRLs_concat (bfinish_spec (repeat BA width) 0)
    (segRLs_O source_tm rest)).
  - rewrite bfinish_repeat_BA_formula; cbn [Nat.mul Nat.add].
    rewrite Nat.add_0_r; reflexivity.
  - rewrite digits_word_repeat_BA; reflexivity.
  - rewrite repeat_length; reflexivity.
Qed.

Lemma ordinary_all_A_to_exception width u n :
  1 <= width -> u+(2^width-1) = 2*n+1 ->
  ordinary_left u {{{((B, []), R)}}}
    ((A8^^width ++ [1;1]) *> 0inf) -[source_tm]->+
  exception_raw_source n (width-1).
Proof.
  intros Hwidth Htotal.
  assert (Hpow : 2 <= 2^width).
  { destruct width as [|width]; [lia|].
    rewrite Nat.pow_succ_r';
      generalize (Nat.pow_nonzero 2 width ltac:(lia)); lia. }
  pose proof (ordinary_seg_to_wall (2^width-2) u
    (A8^^width++[1;1]) (B8^^width++[1;1]) 0inf) as Hrun.
  replace (S (2^width-2)) with (2^width-1) in Hrun by lia.
  specialize (Hrun (zero_primary_finish_seg width [1;1])).
  rewrite Htotal in Hrun; unfold exception_raw_source.
  replace (S (width-1)) with width by lia; exact Hrun.
Qed.

Lemma sobc1_first_call_to_exception :
  sobc1_first_call -[source_tm]->*
    exception_raw_source sobc1_first_half 23.
Proof.
  unfold sobc1_first_call, sobc1_first_word, sobc12_left_wall.
  change (common_left_wall {{{((B, []), R)}}}
      ((U^^22 ++ (A8^^3 ++ D8 ++ C8 ++ A8 ++ U^^28 ++
        A8 ++ A8 ++ B8 ++ A8)) *> 0inf) -[source_tm]->*
    exception_raw_source sobc1_first_half 23).
  eapply evstep_trans.
  - applys_eq (raw_Us_to_Xs 22 common_left_wall
      ((A8^^3 ++ D8 ++ C8 ++ A8 ++ U^^28 ++
        A8 ++ A8 ++ B8 ++ A8) *> 0inf)).
  - eapply evstep_trans.
    + exact (sideRLs_concat_1 sobc1_initial_pre_side
        (left_emit_calls sobc1_initial_pre_calls 22)).
    + apply progress_evstep, ordinary_all_A_to_exception; [lia|].
      exact sobc1_initial_total_half.
Qed.

Lemma bfinish_count_value ds out :
  bfinish_count ds out + digits_value ds + 1 =
    (out+1) * 2^(length ds).
Proof.
  induction ds as [|d ds IH] in out |- *.
  - cbn [bfinish_count digits_value List.length Nat.pow]. lia.
  - destruct d; cbn [bfinish_count digits_value List.length].
    all: rewrite Nat.pow_succ_r by lia.
    all: specialize (IH out); nia.
Qed.

Lemma digits_value_bound ds :
  digits_value ds < 2^(length ds).
Proof.
  induction ds as [|d ds IH].
  - cbn [digits_value List.length Nat.pow]. lia.
  - destruct d; cbn [digits_value List.length Nat.pow] in *; nia.
Qed.

Lemma digits_value_BB_BB_lower ds : 3 <= digits_value (BB :: BB :: ds).
Proof.
  cbn [digits_value]; lia.
Qed.

Lemma digits_value_BB_odd ds : Nat.odd (digits_value (BB :: ds)) = true.
Proof.
  cbn [digits_value]; rewrite Nat.odd_succ, Nat.even_mul; reflexivity.
Qed.

Lemma digits_value_msb_BA_safe ds :
  3 <= length ds ->
  digits_value (ds ++ [BA]) <= 2^(length (ds ++ [BA]))-6.
Proof.
  intro Hlen; rewrite digits_value_app; cbn [digits_value List.length].
  rewrite Nat.mul_0_r, Nat.add_0_r, length_app; cbn [List.length].
  pose proof (digits_value_bound ds).
  assert (8 <= 2^length ds).
  { change (2^3 <= 2^length ds); apply Nat.pow_le_mono_r; lia. }
  replace (length ds+1) with (S (length ds)) by lia.
  cbn [Nat.pow].
  set (p := 2^length ds) in *; set (v := digits_value ds) in *;
    clearbody p v.
  assert (v+6 <= p*2) by lia.
  pose proof (Nat.sub_le_mono_r _ _ 6 H1) as Hsub.
  replace (v+6-6) with v in Hsub by lia.
  rewrite (Nat.mul_comm p 2) in Hsub.
  exact Hsub.
Qed.

Lemma binary_column_value_bound c :
  digits_value (column_digits c) < 2^S (column_e c).
Proof.
  pose proof (digits_value_bound (column_digits c)) as H.
  rewrite (column_length c) in H. exact H.
Qed.
Definition columns_frontier_next (columns : list BinaryColumn) : nat :=
  match columns with
  | [] => 2
  | _ => columns_frontier_count columns
  end.

Lemma columns_frontier_head_equation c columns :
  columns_frontier_count (c :: columns) +
      digits_value (column_digits c) =
    columns_frontier_next columns * 2^S (column_e c).
Proof.
  destruct columns as [|c' columns].
  - cbn [columns_frontier_count columns_frontier_next].
    pose proof (bfinish_count_value (column_digits c) 0) as H.
    rewrite (column_length c) in H. nia.
  - cbn [columns_frontier_count columns_frontier_next].
    pose proof (columns_frontier_count_positive (c' :: columns)
      ltac:(discriminate)) as Hpositive.
    pose proof (bfinish_count_value (column_digits c)
      (columns_frontier_count (c' :: columns)-1)) as H.
    rewrite (column_length c) in H.
    replace (columns_frontier_count (c' :: columns)-1+1)
      with (columns_frontier_count (c' :: columns)) in H by lia.
    change (S (bfinish_count (column_digits c)
      (columns_frontier_count (c' :: columns)-1)) +
      digits_value (column_digits c) =
      columns_frontier_count (c' :: columns) * 2^S (column_e c)).
    lia.
Qed.

Lemma pow2_S_odd_false n : Nat.odd (2^S n) = false.
Proof.
  rewrite Nat.pow_succ_r by lia.
  rewrite Nat.odd_mul. reflexivity.
Qed.

Lemma columns_frontier_head_parity c columns :
  Nat.odd (columns_frontier_count (c :: columns)) =
  Nat.odd (digits_value (column_digits c)).
Proof.
  pose proof (columns_frontier_head_equation c columns) as H.
  apply (f_equal Nat.odd) in H.
  rewrite (Nat.odd_add (columns_frontier_count (c :: columns))
    (digits_value (column_digits c))) in H.
  rewrite (Nat.odd_mul (columns_frontier_next columns)
    (2^S (column_e c))) in H.
  rewrite (pow2_S_odd_false (column_e c)) in H.
  rewrite andb_false_r in H.
  exact (xorb_eq _ _ H).
Qed.
Definition post_ca_side (primary : nat) (columns : list BinaryColumn) : side :=
  ((A8^^primary ++ U^^2 ++ binary_columns_word columns) *> 0inf).
Definition all_A_frontier_side
    (primary : nat) (columns : list BinaryColumn) : side :=
  ((A8^^primary ++ U^^2 ++ all_A_columns_word columns ++ [1;1]) *>
    0inf).
Definition post_ca_state
    (unary primary : nat) (columns : list BinaryColumn) : Q * tape :=
  ordinary_left unary {{{((B, []), R)}}} (post_ca_side primary columns).
Definition all_A_frontier_state
    (unary primary : nat) (columns : list BinaryColumn) : Q * tape :=
  ordinary_left unary {{{((B, []), R)}}}
    (all_A_frontier_side primary columns).
Definition post_to_frontier_calls
    (primary : nat) (columns : list BinaryColumn) : nat :=
  columns_frontier_count columns * 2^primary.

Lemma post_ca_to_frontier_side primary columns :
  columns <> [] ->
  sideRLs source_tm
    (hashes^^post_to_frontier_calls primary columns)
    (post_ca_side primary columns)
    (all_A_frontier_side primary columns).
Proof.
  intro Hnonempty.
  set (n := columns_frontier_count columns).
  pose proof (segRLs_concat
    (all_A_cycles primary n)
    (hashes_U_run n 2)) as Hprefix.
  pose proof (binary_columns_to_frontier columns Hnonempty) as Htail.
  fold n in Htail.
  pose proof (segRLs_sideRLs_concat Hprefix Htail) as H.
  unfold post_to_frontier_calls, post_ca_side, all_A_frontier_side.
  fold n.
  applys_eq H.
  all: repeat rewrite Str_app_assoc; reflexivity.
Qed.

Theorem post_ca_to_frontier unary primary columns :
  columns <> [] ->
  post_ca_state unary primary columns -[source_tm]->*
  all_A_frontier_state
    (unary + post_to_frontier_calls primary columns) primary columns.
Proof.
  intro Hnonempty.
  pose proof (post_ca_to_frontier_side primary columns Hnonempty) as Hright.
  pose proof (left_emit_calls
    (post_to_frontier_calls primary columns) unary) as Hleft.
  exact (sideRLs_concat_1 Hright Hleft).
Qed.
Definition all_A_widths_word es :=
  spaced_words (map (fun e => A8^^S e) es).

Lemma all_A_widths_word_cons2 e e' es :
  all_A_widths_word (e::e'::es) =
    A8^^S e ++ U^^2 ++ all_A_widths_word (e'::es).
Proof.
  reflexivity.
Qed.

Lemma all_A_width_finish e out :
  segRLs source_tm (hashes^^((out+1)*2^(S e)-1)) (hashes^^out)
    (A8^^S e) (B8^^S e).
Proof.
  pose proof (bfinish_spec (repeat BA (S e)) out) as H.
  rewrite bfinish_repeat_BA_formula, digits_word_repeat_BA,
    repeat_length in H; exact H.
Qed.

Lemma all_A_widths_finish es :
  es <> [] -> segRLs source_tm (hashes^^(2^(widths_sum es)-1)) []
    (all_A_widths_word es ++ [1;1]) (full_exception_columns es).
Proof.
  induction es as [|e es IH]; [contradiction|].
  destruct es as [|e' es].
  - intros _; cbn [widths_sum all_A_widths_word full_exception_columns].
    applys_eq (segRLs_concat (all_A_width_finish e 0)
      (segRLs_O source_tm [1;1])).
    + rewrite !widths_sum_cons, widths_sum_nil.
      cbn [Nat.add Nat.mul]; repeat rewrite Nat.add_0_r; reflexivity.
    all: cbn [widths_sum all_A_widths_word full_exception_columns
      List.map spaced_words Nat.add Nat.mul lpow]; rewrite ?Nat.add_0_r;
      repeat rewrite app_nil_r; repeat rewrite app_assoc; reflexivity.
  - intros _; specialize (IH ltac:(discriminate)).
    rewrite widths_sum_cons.
    replace (2^(S e+widths_sum (e'::es))-1)
      with ((2^(widths_sum (e'::es))-1+1)*2^S e-1).
    2: { rewrite Nat.pow_add_r.
      generalize (Nat.pow_nonzero 2 (widths_sum (e'::es)) ltac:(lia)); nia. }
    rewrite all_A_widths_word_cons2, full_exception_columns_cons2.
    applys_eq (segRLs_concat
      (all_A_width_finish e (2^(widths_sum (e'::es))-1))
      (segRLs_concat (hashes_U_run (2^(widths_sum (e'::es))-1) 2) IH)).
    all: repeat rewrite app_assoc; reflexivity.
Qed.

Lemma all_A_widths_to_exception es u n r :
  es <> [] -> u + (2^(widths_sum es)-1) = 2*n+1 ->
  ordinary_left u {{{((B, []), R)}}}
      ((all_A_widths_word es ++ [1;1]) *> r) -[source_tm]->+
  common_left_wall {{{((B, []), R)}}}
      ((U^^(2*n+1) ++ full_exception_columns es) *> r).
Proof.
  intros Hne Htotal.
  pose proof (all_A_widths_finish es Hne) as Hseg.
  assert (Hwidths : 1 <= widths_sum es).
  { destruct es; [contradiction|rewrite widths_sum_cons; lia]. }
  assert (Hpow : 2 <= 2^(widths_sum es)).
  { destruct (widths_sum es) as [|width] eqn:Hwidth; [lia|].
    rewrite Nat.pow_succ_r';
      generalize (Nat.pow_nonzero 2 width ltac:(lia)); lia. }
  replace (2^(widths_sum es)-1) with (S (2^(widths_sum es)-2))
    in Hseg by lia.
  pose proof (ordinary_seg_to_wall (2^(widths_sum es)-2) u
    (all_A_widths_word es++[1;1])
    (full_exception_columns es) r Hseg) as Hrun.
  replace (S (2^(widths_sum es)-2)) with (2^(widths_sum es)-1)
    in Hrun by lia.
  rewrite Htotal in Hrun. exact Hrun.
Qed.
Definition sobc1_middle_width (n : nat) : nat := n+26.
Definition sobc1_before_second_finish_calls (n : nat) : nat :=
  2^n + (2^n + (c_sweep_calls (n+1) 10 +
  (2^(n+21) + (2^(n+21) +
  ((13*2^(n+22)-1) + (2^(n+26)+1)))))).
Definition sobc1_middle_index : nat :=
  2^22 + 2^21 + 2^19 - 4.

Lemma sobc1_middle_index_half :
  half_parameter sobc1_middle_index = sobc1_first_half.
Proof.
  unfold half_parameter, sobc1_middle_index, sobc1_first_half.
  replace 23 with (19+4) by lia.
  replace 22 with (19+3) at 1 2 by lia.
  replace 21 with (19+2) by lia.
  replace 20 with (19+1) by lia.
  rewrite !Nat.pow_add_r.
  replace (2^4) with 16 by reflexivity.
  replace (2^3) with 8 by reflexivity.
  replace (2^2) with 4 by reflexivity.
  replace (2^1) with 2 by reflexivity.
  generalize (Nat.pow_nonzero 2 19 ltac:(lia)); nia.
Qed.
Definition sobc1_second_digits_at (n : nat) : list BDigit :=
  repeat BA (n+2) ++ sobc1_second_tail_digits.

Lemma sobc1_second_digits_at_length n :
  length (sobc1_second_digits_at n) = sobc1_middle_width n.
Proof.
  unfold sobc1_second_digits_at, sobc1_middle_width.
  rewrite length_app, repeat_length, sobc1_second_tail_length. lia.
Qed.

Lemma sobc1_second_digits_at_value n :
  digits_value (sobc1_second_digits_at n) =
    2^(n+2) * digits_value sobc1_second_tail_digits.
Proof.
  unfold sobc1_second_digits_at.
  rewrite digits_value_app, digits_value_repeat_BA, repeat_length.
  reflexivity.
Qed.
Definition sobc1_second_digits : list BDigit :=
  sobc1_second_digits_at sobc1_first_half.
Definition sobc1_second_half : nat :=
  2^sobc1_middle_width sobc1_first_half - 2 +
    digits_value sobc1_second_digits.

Lemma sobc1_second_digits_length :
  length sobc1_second_digits = sobc1_middle_width sobc1_first_half.
Proof.
  unfold sobc1_second_digits.
  apply sobc1_second_digits_at_length.
Qed.

Lemma sobc1_second_total_general n :
  1 <= n ->
  cd_calls n + sobc1_before_second_finish_calls n +
      (2^sobc1_middle_width n-1) =
    2*(2^sobc1_middle_width n-2 +
      digits_value (sobc1_second_digits_at n))+1.
Proof.
  intro Hn.
  rewrite cd_calls_formula by exact Hn.
  unfold sobc1_before_second_finish_calls, sobc1_middle_width.
  rewrite c_sweep_calls_formula, sobc1_second_digits_at_value.
  set (x := 2^n); set (y := 2^21); set (z := 2^(n+21));
  set (g := geom4n 10).
  set (v := digits_value sobc1_second_tail_digits).
  assert (Hx : 1 <= x) by
    (unfold x; apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  assert (Hz : 1 <= z) by
    (unfold z; apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  assert (Hzx : z = x*y) by
    (unfold x, y, z; rewrite Nat.pow_add_r; reflexivity).
  assert (Hp1 : 2^(n+1) = x*2) by
    (unfold x; rewrite Nat.pow_add_r; reflexivity).
  assert (Hp2a : 2^(n+1+1) = x*4) by
    (unfold x; rewrite <- Nat.add_assoc, Nat.pow_add_r; reflexivity).
  assert (Hp2b : 2^(n+2) = x*4) by
    (unfold x; rewrite Nat.pow_add_r; reflexivity).
  assert (Hp22 : 2^(n+22) = z*2) by
    (unfold z; replace (n+22) with (n+21+1) by
       (rewrite <- Nat.add_assoc; reflexivity);
     rewrite Nat.pow_add_r; reflexivity).
  assert (Hp26 : 2^(n+26) = z*32) by
    (unfold z; replace (n+26) with (n+21+5) by
       (rewrite <- Nat.add_assoc; reflexivity);
     rewrite Nat.pow_add_r; reflexivity).
  fold z; rewrite Hp1, Hp2a, Hp2b, Hp22, Hp26.
  pose proof sobc1_second_tail_value as Hv; fold y g v in Hv.
  clear Hn Hp1 Hp2a Hp2b Hp22 Hp26; clearbody x y z g v.
  assert (Hcoef :
    x*2+x+x+x*4*g+z+z+13*(z*2)+z*32+z*32 =
    2*(z*32+x*4*v)) by nia.
  assert (Ha : x*2-2+2 = x*2) by nia.
  assert (Hb : 13*(z*2)-1+1 = 13*(z*2)) by nia.
  assert (Hc1 : z*32-1+1 = z*32) by nia.
  assert (Hc2 : z*32-2+2 = z*32) by nia.
  lia.
Qed.

Lemma sobc1_second_total_half :
  cd_calls sobc1_first_half +
      sobc1_before_second_finish_calls sobc1_first_half +
      (2^sobc1_middle_width sobc1_first_half-1) =
    2*sobc1_second_half+1.
Proof.
  unfold sobc1_second_half, sobc1_second_digits.
  apply sobc1_second_total_general.
  rewrite <- sobc1_middle_index_half.
  unfold half_parameter. lia.
Qed.
Definition column_value (c : BinaryColumn) : nat :=
  digits_value (column_digits c).
Definition column_width (c : BinaryColumn) : nat := S (column_e c).
Definition column_safe (c : BinaryColumn) : Prop :=
  3 <= column_value c /\ column_value c <= 2^(column_width c)-6.

Lemma column_safe_lower c : column_safe c -> 3 <= column_value c.
Proof.
  unfold column_safe; lia.
Qed.
Definition column_next_value (right_odd : bool) (c : BinaryColumn) : nat :=
  (if right_odd then 2^(column_e c) else 2^(S (column_e c))) -
    column_value c / 2.
Definition column_step
    (right_odd : bool) (c c' : BinaryColumn) : Prop :=
  column_e c' = column_e c /\
  column_value c' = column_next_value right_odd c.
Fixpoint columns_step
    (columns columns' : list BinaryColumn) : Prop :=
  match columns, columns' with
  | [c], [c'] => column_step true c c'
  | c :: d :: tail, c' :: rest' =>
      column_step (Nat.odd (column_value d)) c c' /\
      columns_step (d :: tail) rest'
  | _, _ => False
  end.

Lemma column_next_value_bound right_odd c :
  3 <= column_value c ->
  column_next_value right_odd c < 2^(column_width c).
Proof.
  unfold column_next_value, column_width; destruct right_odd;
    rewrite ?Nat.pow_succ_r by lia; nia.
Qed.

Lemma column_step_exists right_odd c :
  3 <= column_value c ->
  exists c', column_step right_odd c c'.
Proof.
  intro Hlower.
  pose proof (column_next_value_bound right_odd c Hlower) as Hbound.
  destruct (digits_exist (column_width c)
    (column_next_value right_odd c) Hbound) as [ds [Hlen Hvalue]].
  assert (Hrecord : length ds = S (column_e c)).
  { unfold column_width in Hlen. exact Hlen. }
  exists (mkBinaryColumn (column_e c) ds Hrecord).
  split; [reflexivity|].
  unfold column_value; cbn. exact Hvalue.
Qed.

Theorem columns_step_exists columns :
  columns <> [] ->
  Forall column_safe columns ->
  exists columns', columns_step columns columns'.
Proof.
  induction columns as [|c columns IH]; intros Hnonempty Hsafe.
  - contradiction.
  - inversion Hsafe as [|? ? Hc Htail]; subst.
    destruct columns as [|d tail].
    + destruct (column_step_exists true c (column_safe_lower c Hc)) as [c' Hstep].
      exists [c']. exact Hstep.
    + destruct (column_step_exists (Nat.odd (column_value d)) c
        (column_safe_lower c Hc))
        as [c' Hstep].
      destruct (IH ltac:(discriminate) Htail) as [rest' Hrest].
      destruct rest' as [|d' tail'].
      * cbn [columns_step] in Hrest.
        exfalso. destruct tail; exact Hrest.
      * exists (c' :: d' :: tail'). cbn. split.
        -- exact Hstep.
        -- exact Hrest.
Qed.

Lemma columns_step_nonempty columns columns' :
  columns_step columns columns' -> columns <> [] /\ columns' <> [].
Proof.
  intro H; split; intro E; subst.
  - destruct columns'; cbn [columns_step] in H; contradiction.
  - destruct columns as [|c [|d ds]]; cbn [columns_step] in H;
      contradiction.
Qed.

Lemma columns_step_widths columns columns' :
  columns_step columns columns' ->
  columns_widths columns' = columns_widths columns.
Proof.
  induction columns as [|c columns IH] in columns' |- *.
  - destruct columns'; cbn [columns_step]; contradiction.
  - destruct columns' as [|c' rest'];
      [destruct columns; cbn [columns_step]; contradiction|].
    destruct columns as [|d tail].
    + destruct rest' as [|d' tail']; cbn [columns_step]; try contradiction.
      intros [He _]. unfold columns_widths; cbn. rewrite He. reflexivity.
    + cbn [columns_step]. intros [Hhead Htail].
      destruct Hhead as [He _]. unfold columns_widths; cbn.
      specialize (IH _ Htail); unfold columns_widths in IH.
      rewrite He, IH. reflexivity.
Qed.
Definition ceil_half (n : nat) : nat := (n+1)/2.

Lemma odd_true_witness n :
  Nat.odd n = true -> exists q, n = 2*q+1.
Proof.
  intro Hodd. apply Nat.odd_spec in Hodd. exact Hodd.
Qed.

Lemma ceil_half_odd q : ceil_half (2*q+1) = q+1.
Proof.
  unfold ceil_half; flia.
Qed.

Lemma ceil_half_scaled_sub t w v :
  1 <= t -> 1 <= w -> v < 2^w ->
  ceil_half (t*2^w-v) = t*2^(w-1)-v/2.
Proof.
  intros Ht Hw Hv.
  assert (Hpow : 2^w = 2*2^(w-1)).
  { replace w with (S (w-1)) at 1 by lia.
    rewrite Nat.pow_succ_r by lia; ring. }
  rewrite Hpow in Hv |- *; unfold ceil_half; flia.
Qed.

Lemma frontier_ceil_half c columns :
  ceil_half (columns_frontier_count (c :: columns)) +
      column_value c / 2 =
    columns_frontier_next columns * 2^(column_e c).
Proof.
  pose proof (columns_frontier_head_equation c columns) as Heq.
  pose proof (columns_frontier_head_parity c columns) as Hparity.
  unfold column_value in *.
  destruct (Nat.odd (digits_value (column_digits c))) eqn:Hodd.
  - apply Nat.odd_spec in Hodd, Hparity.
    destruct Hodd as [p Hp], Hparity as [q Hq].
    rewrite Nat.pow_succ_r in Heq by lia; rewrite Hp, Hq in Heq |- *.
    unfold ceil_half; flia.
  - assert (Hp : Nat.even (digits_value (column_digits c)) = true) by
      (rewrite <- Nat.negb_odd, Hodd; reflexivity).
    assert (Hq : Nat.even (columns_frontier_count (c::columns)) = true) by
      (rewrite <- Nat.negb_odd, Hparity; reflexivity).
    apply Nat.even_spec in Hp, Hq.
    destruct Hp as [p Hp], Hq as [q Hq].
    rewrite Nat.pow_succ_r in Heq by lia; rewrite Hp, Hq in Heq |- *.
    unfold ceil_half; flia.
Qed.

Lemma odometer_cons_arith e s tailF tailR v v' :
  1 <= s -> 1 <= tailF -> v < 2^(S e) ->
  tailR+2 = 2^(s-1)+ceil_half tailF ->
  v' = (if Nat.odd tailF then 2^e else 2^(S e))-v/2 ->
  (tailR+1)*2^(S e)-2+v'+2 =
    2^(S e+s-1)+ceil_half (tailF*2^(S e)-v).
Proof.
  intros Hs HtailF Hv Htail Hnext.
  rewrite (ceil_half_scaled_sub tailF (S e) v) by lia.
  rewrite Nat.pow_succ_r in Hv, Hnext |- * by lia.
  replace (S e-1) with e by lia.
  replace (S e+s-1) with (e+s) by lia; rewrite Nat.pow_add_r.
  assert (Hpow : 2^s = 2*2^(s-1)).
  { replace s with (S (s-1)) at 1 by lia.
    rewrite Nat.pow_succ_r by lia; ring. }
  rewrite Hpow.
  set (a := 2^(s-1)) in *; set (b := 2^e) in *.
  assert (Ha : 1 <= a) by
    (unfold a; apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  assert (Hb : 1 <= b) by
    (unfold b; apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  clearbody a b.
  destruct (Nat.odd tailF) eqn:Hodd.
  - destruct (odd_true_witness _ Hodd) as [q ->].
    rewrite ceil_half_odd in Htail.
    replace (tailR+1) with (a+q) by lia; rewrite Hnext.
    assert (Hvb0 : v < 2*b) by lia.
    pose proof (Nat.Div0.div_lt_upper_bound v 2 b Hvb0) as Hvb.
    assert (Hlarge : 2 <= (a+q)*(2*b)) by nia.
    apply (proj1 (Nat.add_cancel_r _ _ (v/2))).
    replace (((a+q)*(2*b)-2+(b-v/2)+2)+v/2)
      with ((a+q)*(2*b)+b) by lia.
    replace (b*(2*a)+((2*q+1)*b-v/2)+v/2)
      with (b*(2*a)+(2*q+1)*b) by
      (rewrite <- Nat.add_assoc; f_equal; symmetry; apply Nat.sub_add; nia).
    ring.
  - assert (Heven : Nat.even tailF = true) by
      (rewrite <- Nat.negb_odd, Hodd; reflexivity).
    apply Nat.even_spec in Heven; destruct Heven as [q ->].
    replace (ceil_half (2*q)) with q in Htail by
      (unfold ceil_half; flia).
    replace (tailR+1) with (a+q-1) by lia; rewrite Hnext.
    assert (Hvb0 : v < 2*b) by lia.
    pose proof (Nat.Div0.div_lt_upper_bound v 2 b Hvb0) as Hvb.
    assert (Hlarge : 2 <= (a+q-1)*(2*b)) by nia.
    apply (proj1 (Nat.add_cancel_r _ _ (v/2))).
    replace (((a+q-1)*(2*b)-2+(2*b-v/2)+2)+v/2)
      with ((a+q-1)*(2*b)+2*b) by lia.
    replace ((b*(2*a)+((2*q)*b-v/2))+v/2)
      with (b*(2*a)+(2*q)*b) by
      (rewrite <- Nat.add_assoc; f_equal; symmetry; apply Nat.sub_add; nia).
    replace ((a+q-1)*(2*b)+2*b) with ((a+q-1+1)*(2*b)) by ring.
    replace (a+q-1+1) with (a+q) by lia; ring.
Qed.

Lemma columns_step_width_sum columns columns' :
  columns_step columns columns' ->
  columns_width_sum columns' = columns_width_sum columns.
Proof.
  intro H; unfold columns_width_sum; now rewrite (columns_step_widths _ _ H).
Qed.
(** The exact mixed-odometer input represented by the transformed old
    suffix.  This is the arbitrary-list version of the fixed-depth formulas
    used by the exploratory simulator. *)

Theorem columns_step_required columns columns' :
  columns_step columns columns' ->
  mixed_columns_required columns' + 2 =
    2^(columns_width_sum columns - 1) +
      ceil_half (columns_frontier_count columns).
Proof.
  induction columns as [|c columns IH] in columns' |- *.
  - destruct columns'; cbn [columns_step]; contradiction.
  - destruct columns' as [|c' rest'], columns as [|d tail];
      try (cbn [columns_step]; contradiction).
    + destruct rest'; cbn [columns_step]; try contradiction.
      intros [He Hv]; cbn [mixed_columns_required].
      unfold column_required, columns_width_sum, columns_widths; cbn.
      unfold column_next_value, column_width, column_value in Hv |- *.
      rewrite He, Hv.
      pose proof (frontier_ceil_half c []) as Hceil.
      cbn [columns_frontier_next] in Hceil; unfold column_value in Hceil.
      rewrite Nat.pow_succ_r by lia.
      replace (S (column_e c)+0-1) with (column_e c) by lia.
      set (b := 2^(column_e c)) in *.
      replace (column_e c+0-0) with (column_e c) by lia.
      fold b; fold (ceil_half (columns_frontier_count [c])).
      repeat rewrite Nat.add_0_r.
      change (2*b-2+(b-digits_value (column_digits c)/2)+2 =
        b+ceil_half (columns_frontier_count [c])).
      assert (Hb : 1 <= b) by
        (unfold b; apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
      pose proof (binary_column_value_bound c) as Hvbound.
      rewrite Nat.pow_succ_r in Hvbound by lia; fold b in Hvbound.
      clearbody b.
      assert (Hvb0 : digits_value (column_digits c) < 2*b) by lia.
      pose proof (Nat.Div0.div_lt_upper_bound _ 2 b Hvb0) as Hvb.
      apply (proj1 (Nat.add_cancel_r _ _
        (digits_value (column_digits c)/2))).
      replace ((2*b-2+(b-digits_value (column_digits c)/2)+2)+
          digits_value (column_digits c)/2)
        with (3*b) by lia.
      rewrite <- Nat.add_assoc, Hceil; ring.
    + cbn [columns_step]. intros [[He Hv] Htail].
      destruct rest' as [|d' tail'];
        [destruct tail; cbn [columns_step] in Htail; contradiction|].
      specialize (IH (d'::tail') Htail).
      unfold column_value in Hv.
      rewrite <- (columns_frontier_head_parity d tail) in Hv.
      pose proof (odometer_cons_arith (column_e c)
        (columns_width_sum (d::tail)) (columns_frontier_count (d::tail))
        (mixed_columns_required (d'::tail')) (column_value c) (column_value c')
        (columns_width_sum_positive (d::tail) ltac:(discriminate))
        (columns_frontier_count_positive (d::tail) ltac:(discriminate))
        (binary_column_value_bound c) IH Hv) as Hcalc.
      pose proof (columns_frontier_head_equation c (d::tail)) as Hfront.
      unfold columns_frontier_next in Hfront.
      cbn [mixed_columns_required column_required columns_width_sum].
      unfold column_required, column_value in Hcalc, Hfront |- *.
      rewrite He.
      change ((mixed_columns_required (d'::tail')+1)*
          2^S (column_e c)-2+digits_value (column_digits c')+2 =
        2^(S (column_e c)+columns_width_sum (d::tail)-1)+
          ceil_half (columns_frontier_count (c::d::tail))).
      assert (Hfront' : columns_frontier_count (c::d::tail) =
        columns_frontier_count (d::tail)*2^S (column_e c)-
          digits_value (column_digits c)) by lia.
      rewrite Hfront'; exact Hcalc.
Qed.

Lemma round_primary_width_positive current previous :
  1 <= round_primary_width current previous.
Proof.
  unfold round_primary_width, half_parameter; lia.
Qed.
Definition round_outer_column (current previous : nat) : BinaryColumn.
Proof.
  refine (mkBinaryColumn
    (round_primary_width current previous - 1)
    (round_outer_digits current previous) _).
  rewrite round_outer_digits_length.
  generalize (round_primary_width_positive current previous); lia. Defined.

Lemma round_outer_column_word current previous :
  binary_column_word (round_outer_column current previous) =
    A8^^(half_parameter current+2) ++
    B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ B8 ++
    digits_word (z_tail_digits previous).
Proof.
  unfold binary_column_word; cbn [round_outer_column].
  apply round_outer_digits_word.
Qed.

Lemma round_post_unary_half_formula current previous :
  round_post_unary current previous / 2 =
    2^(half_parameter current+1) *
      (1 + geom4n (previous+4) + 2^(2*(previous+4)+1)) - 1.
Proof.
  rewrite round_post_unary_formula.
  set (h := half_parameter current).
  set (body := 1 + geom4n (previous+4) + 2^(2*(previous+4)+1)).
  assert (Hbody : 1 <= body) by (unfold body; lia).
  assert (Hpow : 1 <= 2^(h+1)) by
    (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  clearbody h body.
  replace (h+2) with (S (h+1)) by lia.
  rewrite Nat.pow_succ_r by lia.
  replace (2*2^(h+1)*body-2) with ((2^(h+1)*body-1)*2) by nia.
  rewrite Nat.div_mul by lia; reflexivity.
Qed.
Definition round_frontier_unary
    (current previous : nat) (columns : list BinaryColumn) : nat :=
  round_post_unary current previous +
    columns_frontier_count columns *
      2^(round_primary_width current previous).
Definition round_next_half
    (current previous : nat) (columns : list BinaryColumn) : nat :=
  round_frontier_unary current previous columns / 2 +
    2^(round_primary_width current previous +
      columns_width_sum columns - 1) - 1.

Lemma round_frontier_unary_half current previous columns :
  round_frontier_unary current previous columns / 2 =
  round_post_unary current previous / 2 +
    columns_frontier_count columns *
      2^(round_primary_width current previous-1).
Proof.
  unfold round_frontier_unary.
  set (P := round_primary_width current previous).
  assert (HP : 1 <= P) by
    (unfold P; apply round_primary_width_positive).
  assert (Hpow : 2^P = 2*2^(P-1)).
  { replace P with (S (P-1)) at 1 by lia.
    rewrite Nat.pow_succ_r by lia; reflexivity. }
  fold P; rewrite Hpow.
  replace (columns_frontier_count columns*(2*2^(P-1))) with
    ((columns_frontier_count columns*2^(P-1))*2) by ring.
  replace (round_post_unary current previous+
      (columns_frontier_count columns*2^(P-1))*2) with
    ((columns_frontier_count columns*2^(P-1))*2+
      round_post_unary current previous) by ring.
  rewrite Nat.div_add_l by lia; ring.
Qed.
Definition round_next_index current previous columns : nat :=
  (round_next_half current previous columns - 6) / 2.

Lemma round_next_half_even_ge6 current previous columns :
  columns <> [] ->
  exists k, round_next_half current previous columns = 2*k /\ 6 <= 2*k.
Proof.
  intro Hnonempty.
  set (P := round_primary_width current previous).
  set (Suf := columns_width_sum columns).
  assert (HP : 18 <= P).
  { unfold P, round_primary_width, half_parameter. lia. }
  assert (HSuf : 1 <= Suf).
  { unfold Suf. apply columns_width_sum_positive. exact Hnonempty. }
  assert (HTotal : 2^(P+Suf-1) = 2^P*2^(Suf-1)).
  { replace (P+Suf-1) with (P+(Suf-1)) by lia.
    apply Nat.pow_add_r. }
  assert (HPsplit : 2^P = 8*2^(P-3)).
  { replace P with (3+(P-3)) at 1 by lia.
    rewrite Nat.pow_add_r; reflexivity. }
  assert (Htotal_lower : 8 <= 2^(P+Suf-1)).
  { rewrite HTotal, HPsplit.
    assert (Ha : 1 <= 2^(P-3)) by
      (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
    assert (Hb : 1 <= 2^(Suf-1)) by
      (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
    nia. }
  pose proof (round_frontier_unary_half current previous columns) as Hfront.
  rewrite round_post_unary_half_formula in Hfront.
  fold P in Hfront.
  set (body := 1 + geom4n (previous+4) + 2^(2*(previous+4)+1)).
  assert (Hcurrent : 1 <= half_parameter current) by
    (unfold half_parameter; lia).
  assert (Hpow_current : 2^(half_parameter current+1) =
      2*2^(half_parameter current)).
  { replace (half_parameter current+1) with
      (S (half_parameter current)) by lia.
    rewrite Nat.pow_succ_r by lia; reflexivity. }
  assert (Hbody : 1 <= body) by (unfold body; lia).
  assert (Hbase : 1 <= 2^(half_parameter current)*body).
  { assert (Hpow : 1 <= 2^(half_parameter current)) by
      (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
    nia. }
  assert (Hfront_form : exists a,
      round_frontier_unary current previous columns/2 = 2*a+1).
  { rewrite Hfront, Hpow_current; fold body.
    assert (HPowEven : 2^(P-1) = 2*2^(P-2)).
    { replace (P-1) with (S (P-2)) by lia.
      rewrite Nat.pow_succ_r by lia; reflexivity. }
    rewrite HPowEven.
    exists ((2^(half_parameter current)*body-1)+
      columns_frontier_count columns*2^(P-2)).
    replace (columns_frontier_count columns*(2*2^(P-2))) with
      (2*(columns_frontier_count columns*2^(P-2))) by ring.
    lia. }
  destruct Hfront_form as [a Ha].
  assert (HTotalEven : exists b, 2^(P+Suf-1) = 2*b).
  { exists (2^(P+Suf-2)).
    replace (P+Suf-1) with (S (P+Suf-2)) by lia.
    rewrite Nat.pow_succ_r by lia; reflexivity. }
  destruct HTotalEven as [b Hb].
  unfold round_next_half; fold P Suf; rewrite Ha, Hb.
  exists (a+b); split; [lia|nia].
Qed.

Lemma round_next_half_parameter current previous columns :
  columns <> [] ->
  round_next_half current previous columns =
    half_parameter (round_next_index current previous columns).
Proof.
  intro Hnonempty.
  destruct (round_next_half_even_ge6 current previous columns Hnonempty)
    as [k [Hk Hge]].
  unfold round_next_index, half_parameter; rewrite Hk; flia.
Qed.
Definition columns_head_odd (columns : list BinaryColumn) : Prop :=
  match columns with
  | [] => False
  | c :: _ => Nat.odd (column_value c) = true
  end.

Theorem round_output_required current previous columns columns' :
  columns <> [] ->
  columns_step columns columns' ->
  columns_head_odd columns ->
  mixed_columns_required
      (round_outer_column current previous :: columns') =
    round_next_half current previous columns.
Proof.
  intros Hnonempty Hstep Hfirst_odd.
  destruct columns as [|first rest]; [contradiction|].
  cbn [columns_head_odd] in Hfirst_odd.
  pose proof (columns_step_required (first :: rest) columns' Hstep) as Hrequired.
  pose proof (columns_frontier_head_parity first rest) as Hparity.
  unfold column_value in Hfirst_odd.
  rewrite Hfirst_odd in Hparity.
  destruct (odd_true_witness _ Hparity) as [q Hq].
  rewrite Hq, ceil_half_odd in Hrequired.
  pose proof (round_unary_decodes_outer current previous) as Houter.
  pose proof (round_frontier_unary_half current previous (first::rest)) as Hfront.
  set (P := round_primary_width current previous).
  set (Suf := columns_width_sum (first :: rest)).
  assert (HP : 1 <= P) by
    (unfold P; apply round_primary_width_positive).
  assert (HSuf : 1 <= Suf) by
    (unfold Suf; apply columns_width_sum_positive; discriminate).
  unfold round_next_half; rewrite Hfront.
  cbn [mixed_columns_required column_required].
  fold P Suf in Hrequired, Houter, Hfront |- *.
  fold (mixed_columns_required columns') in Hrequired |- *.
  rewrite Hq.
  assert (Htail_one : mixed_columns_required columns'+1 =
      2^(Suf-1)+q) by lia.
  assert (HPow : 2^P = 2*2^(P-1)).
  { replace P with (S (P-1)) at 1 by lia.
    rewrite Nat.pow_succ_r by lia; reflexivity. }
  assert (HTotal : 2^(P+Suf-1) = 2^P*2^(Suf-1)).
  { replace (P+Suf-1) with (P+(Suf-1)) by lia.
    apply Nat.pow_add_r. }
  unfold column_required.
  change ((mixed_columns_required columns'+1)*2^S (P-1)-2+
    digits_value (round_outer_digits current previous) =
    round_post_unary current previous/2+(2*q+1)*2^(P-1)+
      2^(P+Suf-1)-1).
  replace (S (P-1)) with P by lia.
  rewrite Htail_one, <- Houter, HTotal, HPow.
  set (a := 2^(Suf-1)) in *; set (b := 2^(P-1)) in *.
  set (r := round_post_unary current previous/2) in *.
  assert (Ha : 1 <= a) by
    (unfold a; apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  assert (Hb : 1 <= b) by
    (unfold b; apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  clearbody a b r; nia.
Qed.
Definition frontier_es
    (current previous : nat) (columns : list BinaryColumn) : list nat :=
  (round_primary_width current previous-1) :: map column_e columns.
Definition round_output_columns current previous columns' :=
  round_outer_column current previous :: columns'.

Lemma round_frontier_exception_equation current previous columns :
  columns <> [] ->
  round_frontier_unary current previous columns+
      (2^(round_primary_width current previous+
        columns_width_sum columns)-1) =
    2*round_next_half current previous columns+1.
Proof.
  intro Hnonempty.
  set (P := round_primary_width current previous).
  set (Suf := columns_width_sum columns).
  assert (HP : 1 <= P) by
    (unfold P; apply round_primary_width_positive).
  assert (HSuf : 1 <= Suf) by
    (unfold Suf; apply columns_width_sum_positive; exact Hnonempty).
  assert (Hpost : round_post_unary current previous =
      2*(round_post_unary current previous/2)).
  { rewrite round_post_unary_formula at 1.
    rewrite round_post_unary_half_formula.
    set (h := half_parameter current).
    set (body := 1+geom4n (previous+4)+2^(2*(previous+4)+1)).
    replace (h+2) with (S (h+1)) by lia.
    rewrite Nat.pow_succ_r by lia.
    assert (Hbase : 1 <= 2^(h+1)*body).
    { assert (Hpow : 1 <= 2^(h+1)) by
        (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
      unfold body; nia. }
    clearbody h body; nia. }
  assert (HPow : 2^P = 2*2^(P-1)).
  { replace P with (S (P-1)) at 1 by lia.
    rewrite Nat.pow_succ_r by lia; reflexivity. }
  assert (Hfront : round_frontier_unary current previous columns =
      2*(round_frontier_unary current previous columns/2)).
  { rewrite round_frontier_unary_half.
    unfold round_frontier_unary; fold P; rewrite Hpost at 1.
    rewrite HPow; ring. }
  assert (HTotal : 2^(P+Suf) = 2*2^(P+Suf-1)).
  { replace (P+Suf) with (S (P+Suf-1)) at 1 by lia.
    rewrite Nat.pow_succ_r by lia; reflexivity. }
  unfold round_next_half; fold P Suf; rewrite Hfront, HTotal.
  assert (Hpow : 1 <= 2^(P+Suf-1)) by
    (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  lia.
Qed.

Theorem all_A_frontier_to_exception_done
    current previous columns columns' :
  columns <> [] ->
  columns_step columns columns' ->
  columns_head_odd columns ->
  all_A_frontier_state
      (round_frontier_unary current previous columns)
      (round_primary_width current previous) columns
    -[source_tm]->*
  exception_done (round_next_half current previous columns)
    (binary_columns_word
      (round_output_columns current previous columns')).
Proof.
  intros Hnonempty Hstep Hodd.
  eapply evstep_trans with (c':=exception_columns_raw_source
    (round_next_half current previous columns)
    (frontier_es current previous columns)).
  - apply progress_evstep.
    unfold all_A_frontier_state, all_A_frontier_side,
      exception_columns_raw_source.
    replace (A8^^round_primary_width current previous ++ U^^2 ++
      all_A_columns_word columns ++ [1;1]%sym) with
      (all_A_widths_word (frontier_es current previous columns) ++
        [1;1]%sym).
    2:{ destruct columns as [|c columns]; [contradiction|].
        unfold frontier_es, all_A_widths_word, all_A_columns_word;
        cbn [map spaced_words]; rewrite map_map;
        replace (S (round_primary_width current previous-1)) with
          (round_primary_width current previous) by
          (generalize (round_primary_width_positive current previous); lia);
        repeat rewrite app_assoc; reflexivity. }
    apply all_A_widths_to_exception; [discriminate|].
    unfold frontier_es; rewrite widths_sum_cons, widths_sum_column_es.
    replace (S (round_primary_width current previous-1)) with
      (round_primary_width current previous) by
      (generalize (round_primary_width_positive current previous); lia).
    exact (round_frontier_exception_equation current previous columns Hnonempty).
  - applys_eq (sobc1_exception_columns_from_seg
      (round_next_half current previous columns)
      (frontier_es current previous columns)
      (binary_columns_word (round_output_columns current previous columns'))).
    + unfold frontier_es; discriminate.
    + rewrite (initialized_mixed_columns_eq
        (frontier_es current previous columns)
        (round_output_columns current previous columns')).
      * applys_eq (mixed_columns_spec
          (round_output_columns current previous columns')).
        f_equal; symmetry; unfold round_output_columns;
          exact (round_output_required current previous columns columns'
            Hnonempty Hstep Hodd).
      * unfold frontier_es, round_output_columns.
        change (S (column_e (round_outer_column current previous)) ::
          columns_widths columns' =
          S (round_primary_width current previous-1) :: columns_widths columns).
        rewrite (columns_step_widths _ _ Hstep); f_equal;
          cbn [round_outer_column].
Qed.
Definition z_column (previous : nat) : BinaryColumn.
Proof.
  refine (mkBinaryColumn (half_parameter previous) (z_digits previous) _).
  rewrite z_digits_length.
  unfold z_birth_width, half_parameter. lia. Defined.

Lemma z_column_word previous :
  binary_column_word (z_column previous) = digits_word (z_digits previous).
Proof.
  reflexivity.
Qed.

Lemma z_column_e previous : column_e (z_column previous) =
  half_parameter previous.
Proof.
  reflexivity.
Qed.

Lemma binary_columns_word_cons c columns :
  columns <> [] ->
  binary_columns_word (c :: columns) =
    binary_column_word c ++ U^^2 ++ binary_columns_word columns.
Proof.
  destruct columns; [contradiction|reflexivity].
Qed.

Lemma ca_calls_positive primary pairs : 1 <= ca_calls primary pairs.
Proof.
  unfold ca_calls, ca_start_calls; flia.
Qed.

Lemma exception_done_ca n pairs rest :
  1 <= n ->
  exception_done n
    (A8^^(2*pairs) ++ B8++B8++A8++B8++A8++rest) -[source_tm]->+
  ordinary_left (cd_calls n + ca_calls n pairs) {{{((B, []), R)}}}
    ((A8^^(n+2*pairs+4) ++ U^^2 ++ B8++B8++rest) *> 0inf).
Proof.
  intro Hn; eapply progress_trans.
  - apply exception_done_cd, Hn.
  - unfold after_cd.
    replace (cd_output n ++
      (A8^^(2*pairs)++B8++B8++A8++B8++A8++rest)) with
      (A8^^n++C8++A8^^(2*pairs+1)++B8++B8++A8++B8++A8++rest).
    2:{ unfold cd_output; replace (2*pairs+1) with (S (2*pairs)) by lia;
        cbn [lpow]; repeat rewrite app_assoc; reflexivity. }
    exact (ordinary_seg_run_pos (ca_calls n pairs) (cd_calls n)
      (A8^^n++C8++A8^^(2*pairs+1)++B8++B8++A8++B8++A8++rest)
      (A8^^(n+2*pairs+4)++U^^2++B8++B8++rest) 0inf
      (ca_calls_positive n pairs) (ca_batch n pairs rest)).
Qed.
(** This is the physical second half of a round.  Its source is the decoded
    exceptional call.  The [C/D] batch and then the [C/A] batch rebuild the
    canonical post-[C/A] state, prepend the newly born Z column belonging to
    the previous generation, and shift the two generation parameters. *)

Theorem exception_done_to_next_post
    current previous columns columns' :
  columns <> [] ->
  columns_step columns columns' ->
  exception_done (round_next_half current previous columns)
      (binary_columns_word
        (round_output_columns current previous columns'))
    -[source_tm]->+
  post_ca_state
    (round_post_unary
      (round_next_index current previous columns) current)
    (round_primary_width
      (round_next_index current previous columns) current)
    (z_column previous :: columns').
Proof.
  intros Hnonempty Hstep.
  set (n:=round_next_half current previous columns).
  set (next:=round_next_index current previous columns).
  assert (Hn:n=half_parameter next)
    by (unfold n,next; apply round_next_half_parameter, Hnonempty).
  assert (Hnpos:1<=n).
  { destruct (round_next_half_even_ge6 current previous columns Hnonempty)
      as [k [E L]]; unfold n; lia. }
  destruct (columns_step_nonempty _ _ Hstep) as [_ Hout].
  set (rest:=B8++digits_word (z_tail_digits previous)++U^^2++
    binary_columns_word columns').
  applys_eq (exception_done_ca n (current+4) rest Hnpos).
  - unfold round_output_columns, exception_done.
    rewrite binary_columns_word_cons by exact Hout.
    rewrite round_outer_column_word.
    unfold rest, half_parameter; repeat rewrite app_assoc; flia.
  - unfold post_ca_state, post_ca_side, round_post_unary,
      round_primary_width.
    rewrite Hn, binary_columns_word_cons by exact Hout.
    rewrite z_column_word, z_digits_word_split.
    unfold rest, half_parameter; repeat rewrite Str_app_assoc;
      repeat rewrite app_assoc; flia.
Qed.

Theorem sobc1_canonical_round
    current previous columns columns' :
  columns <> [] ->
  columns_head_odd columns ->
  columns_step columns columns' ->
  post_ca_state (round_post_unary current previous)
      (round_primary_width current previous) columns
    -[source_tm]->+
  post_ca_state
    (round_post_unary
      (round_next_index current previous columns) current)
    (round_primary_width
      (round_next_index current previous columns) current)
    (z_column previous :: columns').
Proof.
  intros Hnonempty Hodd Hstep.
  eapply evstep_progress_trans;
    [apply post_ca_to_frontier, Hnonempty|].
  eapply evstep_progress_trans;
    [eapply all_A_frontier_to_exception_done|eapply exception_done_to_next_post];
    eassumption.
Qed.
(** The two inequalities are deliberately staggered by one generation.
    The first pays for the column born in the current round; after the
    parameter shift it is exactly the first inequality of the successor.
    The second is paid by the exponential term in [round_next_half]. *)
Definition round_width_dominance
    (current previous : nat) (columns : list BinaryColumn) : Prop :=
  2 * columns_width_sum columns + 4 <= half_parameter previous + 1 /\
  2 * (half_parameter previous + 1 + columns_width_sum columns) + 4 <=
    half_parameter current + 1.

Lemma pow2_linear_margin n : 2*n+8 <= 2^(n+5).
Proof.
  induction n; [cbn; lia|].
  replace (S n+5) with (S (n+5)) by lia.
  rewrite Nat.pow_succ_r by lia; lia.
Qed.

Lemma output_columns_width_sum previous columns columns' :
  columns_step columns columns' ->
  columns_width_sum (z_column previous :: columns') =
    half_parameter previous + 1 + columns_width_sum columns.
Proof.
  intro Hstep. rewrite columns_width_sum_cons.
  rewrite z_column_e, (columns_step_width_sum columns columns' Hstep).
  lia.
Qed.

Lemma round_next_half_growth current previous columns :
  columns <> [] ->
  2 * (half_parameter current + 1 +
      (half_parameter previous + 1 + columns_width_sum columns)) + 4 <=
    round_next_half current previous columns + 1.
Proof.
  intro Hnonempty.
  set (x := half_parameter current + half_parameter previous +
    columns_width_sum columns).
  assert (Hpow : 2*x+8 <= 2^(x+5)) by apply pow2_linear_margin.
  unfold round_next_half.
  replace (round_primary_width current previous +
      columns_width_sum columns-1) with (x+5) by
    (unfold x, round_primary_width; lia).
  assert (1 <= 2^(x+5)) by
    (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  lia.
Qed.

Theorem round_width_dominance_step
    current previous columns columns' :
  columns <> [] ->
  columns_step columns columns' ->
  round_width_dominance current previous columns ->
  round_width_dominance
    (round_next_index current previous columns) current
    (z_column previous :: columns').
Proof.
  intros Hnonempty Hstep [Hprevious Hcurrent].
  unfold round_width_dominance.
  rewrite (output_columns_width_sum previous columns columns' Hstep).
  split.
  - exact Hcurrent.
  - rewrite <- (round_next_half_parameter current previous columns Hnonempty).
    exact (round_next_half_growth current previous columns Hnonempty).
Qed.

Lemma z_column_width previous :
  column_width (z_column previous) = z_birth_width previous.
Proof.
  unfold column_width. rewrite z_column_e.
  unfold half_parameter, z_birth_width. lia.
Qed.

Lemma z_column_value previous :
  Z.of_nat (column_value (z_column previous)) = z_birth_value previous.
Proof.
  unfold column_value, z_column; cbn.
  apply z_digits_value.
Qed.

Lemma z_birth_value_odd n : (z_birth_value n mod 2 = 1)%Z.
Proof.
  rewrite z_birth_complement; flia.
Qed.

Lemma Zodd_of_nat n : Z.odd (Z.of_nat n) = Nat.odd n.
Proof.
  induction n using nat_ind2; [reflexivity|reflexivity|].
  rewrite Nat2Z.inj_succ, Nat2Z.inj_succ.
  change (Z.odd (Z.succ (Z.succ (Z.of_nat n))) = Nat.odd (S (S n))).
  now rewrite Z.odd_succ_succ, Nat.odd_succ_succ.
Qed.

Lemma z_column_odd previous :
  Nat.odd (column_value (z_column previous)) = true.
Proof.
  rewrite <- Zodd_of_nat, z_column_value, Zodd_mod, z_birth_value_odd.
  reflexivity.
Qed.
(** Abstract column streams, using [Z] throughout so the lineage and
    stable phases share one numeric representation. *)
Local Transparent pow2 Nat.pow.
Record AbstractColumn := mkAbstractColumn {
  abstract_width : nat;
  abstract_value : Z;
}.
Definition abstract_of_column (c : BinaryColumn) : AbstractColumn :=
  mkAbstractColumn (column_width c) (Z.of_nat (column_value c)).
Definition abstract_safe (c : AbstractColumn) : Prop :=
  (3 <= abstract_value c <= pow2 (abstract_width c)-6)%Z.
Definition abstract_step (right_odd : bool) (c : AbstractColumn) : AbstractColumn :=
  mkAbstractColumn (abstract_width c)
    (arbitrary_column_step (pow2 (abstract_width c)) right_odd (abstract_value c)).
Fixpoint abstract_columns_next (columns : list AbstractColumn) : list AbstractColumn :=
  match columns with
  | [] => []
  | c :: rest =>
      match rest with
      | [] => [abstract_step true c]
      | d :: _ => abstract_step (Z.odd (abstract_value d)) c :: abstract_columns_next rest
      end
  end.
Definition abstract_columns_iter n columns :=
  Nat.iter n abstract_columns_next columns.
Definition abstract_head_odd (columns : list AbstractColumn) : Prop :=
  match columns with [] => False | c::_ => Z.odd (abstract_value c) = true end.
Definition abstract_columns_safe := Forall abstract_safe.
Definition abstract_suffix_good (settle : nat) (columns : list AbstractColumn) : Prop :=
  columns <> [] /\
  (forall n, abstract_columns_safe (abstract_columns_iter n columns)) /\
  (forall n, settle <= n -> abstract_head_odd (abstract_columns_iter n columns)).

Lemma hd_nonempty {A} (x y : A) xs : xs <> [] -> hd x xs = hd y xs.
Proof.
  destruct xs; cbn; congruence.
Qed.

Lemma abstract_columns_next_nonempty columns : columns <> [] -> abstract_columns_next columns <> [].
Proof.
  destruct columns as [|c [|d rest]]; cbn; congruence.
Qed.

Lemma abstract_columns_iter_nonempty n columns : columns <> [] -> abstract_columns_iter n columns <> [].
Proof.
  intro H; unfold abstract_columns_iter.
  eapply Nat.iter_invariant; eauto using abstract_columns_next_nonempty.
Qed.

Lemma abstract_columns_iter_succ_right n columns : abstract_columns_next (abstract_columns_iter n columns) = abstract_columns_iter (S n) columns.
Proof.
  symmetry; apply Nat.iter_succ.
Qed.

Lemma abstract_columns_iter_succ_left n columns :
  abstract_columns_iter n (abstract_columns_next columns) =
  abstract_columns_iter (S n) columns.
Proof.
  unfold abstract_columns_iter; symmetry; apply Nat.iter_succ_r.
Qed.

Lemma abstract_columns_iter_add m n columns : abstract_columns_iter (m+n) columns = abstract_columns_iter n (abstract_columns_iter m columns).
Proof.
  unfold abstract_columns_iter; rewrite Nat.add_comm, Nat.iter_add; reflexivity.
Qed.

Lemma abstract_columns_next_cons c columns :
  columns <> [] ->
  abstract_columns_next (c::columns) =
    abstract_step (Z.odd (abstract_value (hd c columns))) c :: abstract_columns_next columns.
Proof.
  destruct columns; cbn; congruence.
Qed.

Lemma abstract_columns_iter_cons n c columns :
  columns <> [] -> exists c',
    abstract_columns_iter n (c::columns) =
      c'::abstract_columns_iter n columns.
Proof.
  induction n as [|n IH] in c, columns |- *; intro H.
  - exists c; reflexivity.
  - destruct (IH c columns H) as [c' E].
    rewrite <- !abstract_columns_iter_succ_right, E.
    rewrite abstract_columns_next_cons by
      (apply abstract_columns_iter_nonempty; exact H).
    eexists; reflexivity.
Qed.

Lemma abstract_columns_iter_head_width n c columns :
  columns <> [] -> abstract_width (hd c (abstract_columns_iter n (c::columns))) = abstract_width c.
Proof.
  induction n as [|n IH] in c, columns |- *; intro H.
  - reflexivity.
  - unfold abstract_columns_iter; rewrite Nat.iter_succ_r.
    rewrite abstract_columns_next_cons by exact H.
    set (c' := abstract_step (Z.odd (abstract_value (hd c columns))) c).
    fold (abstract_columns_iter n (c'::abstract_columns_next columns)).
    rewrite (hd_nonempty c c') by
      (apply abstract_columns_iter_nonempty; discriminate).
    rewrite IH by (apply abstract_columns_next_nonempty; exact H).
    reflexivity.
Qed.

Lemma column_safe_abstract c : column_safe c <-> abstract_safe (abstract_of_column c).
Proof.
  unfold column_safe, abstract_safe, abstract_of_column, pow2; cbn.
  zify; lia.
Qed.

Lemma columns_safe_abstract columns :
  Forall column_safe columns <-> abstract_columns_safe (map abstract_of_column columns).
Proof.
  induction columns; cbn [abstract_columns_safe]; split; intro H; inversion H;
    subst; constructor; try apply column_safe_abstract; try apply IHcolumns;
    assumption.
Qed.

Lemma abstract_column_step c c' right_odd :
  column_safe c -> column_step right_odd c c' ->
  abstract_of_column c' = abstract_step right_odd (abstract_of_column c).
Proof.
  intros Hsafe [He Hv].
  unfold abstract_of_column, abstract_step; cbn.
  f_equal; [unfold column_width in *; lia|].
  rewrite Hv. unfold arbitrary_column_step, column_next_value.
  assert (Hhalf : column_value c / 2 <= 2^column_e c).
  { unfold column_safe, column_width in Hsafe.
    rewrite Nat.pow_succ_r in Hsafe by lia; nia. }
  destruct right_odd.
  - rewrite Nat2Z.inj_sub by exact Hhalf.
    rewrite Nat2Z.inj_div by lia.
    unfold column_width; rewrite pow2_succ.
    replace (2 * pow2 (column_e c))%Z with
      (pow2 (column_e c) * 2)%Z by ring.
    rewrite Z.div_mul by lia; reflexivity.
  - rewrite Nat2Z.inj_sub by
      (rewrite Nat.pow_succ_r by lia; nia).
    rewrite Nat2Z.inj_div by lia. reflexivity.
Qed.

Lemma columns_step_abstract columns columns' :
  Forall column_safe columns ->
  columns_step columns columns' ->
  map abstract_of_column columns' = abstract_columns_next (map abstract_of_column columns).
Proof.
  intros Hsafe; revert columns' Hsafe.
  induction columns as [|c [|d tail] IH]; intros columns' Hsafe Hstep;
    destruct columns' as [|c' rest']; cbn [columns_step] in Hstep;
    try contradiction.
  - destruct rest'; [|contradiction]. cbn [map abstract_columns_next].
    inversion Hsafe as [|? ? Hc Hnil]; subst.
    rewrite (abstract_column_step _ _ true Hc Hstep).
    reflexivity.
  - destruct rest' as [|d' tail'];
      [destruct Hstep as [_ Hrest]; destruct tail;
       cbn [columns_step] in Hrest; contradiction|].
    inversion Hsafe as [|? ? Hc Htail]; subst.
    destruct Hstep as [Hhead Hrest]. cbn [map abstract_columns_next].
    change (abstract_of_column c' :: map abstract_of_column (d'::tail') =
      abstract_step (Z.odd (Z.of_nat (column_value d))) (abstract_of_column c) ::
      abstract_columns_next (map abstract_of_column (d::tail))).
    rewrite Zodd_of_nat, (abstract_column_step _ _ _ Hc Hhead).
    rewrite (IH (d'::tail') Htail Hrest). reflexivity.
Qed.
Fixpoint abstract_head_inputs (n : nat) (columns : list AbstractColumn) : list bool :=
  match n with
  | O => []
  | S n' =>
      match columns with
      | [] => []
      | c::_ => Z.odd (abstract_value c) :: abstract_head_inputs n' (abstract_columns_next columns)
      end
  end.

Lemma abstract_head_inputs_length n columns :
  columns <> [] -> length (abstract_head_inputs n columns) = n.
Proof.
  induction n as [|n IH] in columns |- *; intro H.
  - reflexivity.
  - destruct columns as [|c columns]; [contradiction|].
    cbn [abstract_head_inputs length]. f_equal.
    apply IH, abstract_columns_next_nonempty. discriminate.
Qed.
Definition abstract_birth birth := mkAbstractColumn (z_birth_width birth) (z_birth_value birth).

Lemma abstract_birth_eq birth : abstract_birth birth = abstract_of_column (z_column birth).
Proof.
  unfold abstract_birth, abstract_of_column. rewrite z_column_width, z_column_value. reflexivity.
Qed.

Lemma abstract_iter_head_value c columns n :
  columns <> [] ->
  abstract_value (hd c (abstract_columns_iter n (c::columns))) =
    zinputs (pow2 (abstract_width c)) (abstract_head_inputs n columns) (abstract_value c).
Proof.
  induction n as [|n IH] in c, columns |- *; intro H.
  - reflexivity.
  - unfold abstract_columns_iter; rewrite Nat.iter_succ_r.
    rewrite abstract_columns_next_cons by exact H.
    set (b := Z.odd (abstract_value (hd c columns))).
    set (c' := abstract_step b c).
    fold (abstract_columns_iter n (c'::abstract_columns_next columns)).
    rewrite (hd_nonempty c c') by
      (apply abstract_columns_iter_nonempty; discriminate).
    rewrite IH by (apply abstract_columns_next_nonempty; exact H).
    cbn [abstract_head_inputs zinputs]. destruct columns; [contradiction|].
    unfold c', b, abstract_step; cbn [abstract_width abstract_value]. reflexivity.
Qed.

Theorem abstract_birth_early_safe birth columns n :
  columns <> [] -> n <= z_birth_width birth-4 ->
  abstract_safe (hd (abstract_birth birth) (abstract_columns_iter n (abstract_birth birth::columns))).
Proof.
  intros Hnonempty Hage.
  set (inputs := abstract_head_inputs n columns).
  assert (Hlength : length inputs <= lineage_fuel (LBirth birth)).
  { unfold inputs. rewrite abstract_head_inputs_length by exact Hnonempty.
    unfold z_birth_width, lineage_fuel in *. lia. }
  unfold abstract_safe.
  rewrite (abstract_columns_iter_head_width n (abstract_birth birth) columns Hnonempty).
  rewrite (abstract_iter_head_value (abstract_birth birth) columns n Hnonempty).
  unfold abstract_birth; cbn [abstract_width abstract_value].
  fold inputs.
  exact (lineage_inputs_safe
    (pow2 (z_birth_width birth)) (LBirth birth) (z_birth_value birth)
    inputs Hlength (z_birth_low_slice birth)).
Qed.

Lemma stable_step_safe_Z width value :
  4 <= width ->
  (3 <= value <= pow2 width-6)%Z ->
  (3 <= stable_column_step (pow2 (width-1)) value <= pow2 width-6)%Z.
Proof.
  intros Hwidth Hsafe.
  assert (H8 : (8 <= pow2 (width-1))%Z).
  { unfold pow2; change (Z.of_nat 8 <= Z.of_nat (2^(width-1)))%Z.
    apply (proj1 (Nat2Z.inj_le _ _)).
    change (2^3 <= 2^(width-1)); apply Nat.pow_le_mono_r; lia. }
  assert (Hpow : pow2 width = (2 * pow2 (width-1))%Z).
  { replace width with (S (width-1)) at 1 by lia; apply pow2_succ. }
  rewrite Hpow in Hsafe |- *.
  unfold stable_column_step; flia.
Qed.

Lemma zinputs_repeat_true total n value :
  zinputs total (repeat true n) value =
    Nat.iter n (arbitrary_column_step total true) value.
Proof.
  induction n as [|n IH] in value |- *; cbn [repeat zinputs Nat.iter].
  - reflexivity.
  - rewrite IH, Nat.iter_swap. reflexivity.
Qed.

Lemma arbitrary_true_iter width n value :
  1 <= width ->
  Nat.iter n (arbitrary_column_step (pow2 width) true) value =
  Nat.iter n (stable_column_step (pow2 (width-1))) value.
Proof.
  intro Hwidth; induction n; [reflexivity|].
  rewrite !Nat.iter_succ, IHn.
  unfold arbitrary_column_step, stable_column_step.
  replace width with (S (width-1)) at 1 by lia.
  rewrite pow2_succ, Z.mul_comm, Z.div_mul by lia; reflexivity.
Qed.

Lemma arbitrary_true_iter_safe width n value :
  4 <= width ->
  (3 <= value <= pow2 width-6)%Z ->
  (3 <= Nat.iter n (arbitrary_column_step (pow2 width) true) value <=
    pow2 width-6)%Z.
Proof.
  intros Hwidth Hsafe; rewrite arbitrary_true_iter by lia.
  eapply Nat.iter_invariant; eauto using stable_step_safe_Z.
Qed.

Theorem z_odd_width_converges_odd k value :
  2 <= k ->
  (3 <= value <= pow2 (odd_column_width k)-6)%Z ->
  Z.odd (Nat.iter (2*odd_column_width k)
    (arbitrary_column_step (pow2 (odd_column_width k)) true) value) = true.
Proof.
  intros Hk Hsafe.
  rewrite arbitrary_true_iter by (unfold odd_column_width; lia).
  assert (Hrange :
    (-pow2 (odd_column_width k) < value-odd_column_fixed k <
      pow2 (odd_column_width k))%Z).
  { pose proof (odd_column_fixed_pos k).
    pose proof (odd_column_fixed_equation k).
    pose proof (pow2_odd_width k); flia. }
  assert (Hhalf : pow2 (odd_column_width k-1) = odd_column_half k).
  { unfold odd_column_width, odd_column_half.
    replace (2*k+1-1) with (2*k) by lia; apply pow2_even_width. }
  rewrite Hhalf.
  rewrite (odd_column_converges k value ltac:(lia) Hrange).
  rewrite Zodd_mod, odd_column_fixed_odd. reflexivity.
Qed.

Lemma abstract_suffix_good_inputs settle columns q n :
  abstract_suffix_good settle columns -> settle <= q ->
  abstract_head_inputs n (abstract_columns_iter q columns) = repeat true n.
Proof.
  intros [Hnonempty [Hsafe Hodd]] Hq.
  induction n as [|n IH] in q, Hq |- *; [reflexivity|].
  assert (HN : abstract_columns_iter q columns <> []) by (apply abstract_columns_iter_nonempty; exact Hnonempty).
  destruct (abstract_columns_iter q columns) as [|c rest] eqn:Hiter; [contradiction|].
  cbn [abstract_head_inputs repeat].
  assert (HO : Z.odd (abstract_value c) = true).
  { specialize (Hodd q Hq). unfold abstract_head_odd in Hodd.
    rewrite Hiter in Hodd. exact Hodd. }
  rewrite HO, <- Hiter, abstract_columns_iter_succ_right.
  rewrite (IH (S q) ltac:(lia)). reflexivity.
Qed.

Lemma abstract_safe_width c : abstract_safe c -> 4 <= abstract_width c.
Proof.
  intro Hsafe. unfold abstract_safe, pow2 in Hsafe.
  destruct (abstract_width c) as [|[|[|[|w]]]];
    cbn [Nat.pow] in Hsafe; lia.
Qed.

Theorem abstract_suffix_good_prepend_birth settle columns birth :
  abstract_suffix_good settle columns ->
  settle <= z_birth_width birth-4 ->
  abstract_suffix_good (settle+2*z_birth_width birth) (abstract_birth birth::columns).
Proof.
  intros Hgood Hprotected.
  destruct Hgood as [Hnonempty [Hsuffix_safe Hsuffix_odd]].
  assert (Hgood : abstract_suffix_good settle columns) by (repeat split; assumption).
  set (born := abstract_birth birth).
  set (width := z_birth_width birth).
  assert (Hhead_safe_all : forall q,
      abstract_safe (hd born (abstract_columns_iter q (born::columns)))).
  { intro q. destruct (le_gt_dec q settle) as [Hearly|Hlate].
    - unfold born. apply abstract_birth_early_safe; [exact Hnonempty|lia].
    - set (r := q-settle).
      assert (Hq : q = settle+r) by (unfold r; lia).
      rewrite Hq, abstract_columns_iter_add.
      destruct (abstract_columns_iter_cons settle born columns Hnonempty)
        as [c Hstate]. rewrite Hstate.
      assert (Hc_safe : abstract_safe c).
      { pose proof (abstract_birth_early_safe birth columns settle
          Hnonempty Hprotected) as H; fold born in H; now rewrite Hstate in H. }
      rewrite (hd_nonempty born c) by
        (apply abstract_columns_iter_nonempty; discriminate).
      unfold abstract_safe.
      rewrite abstract_columns_iter_head_width by
        (apply abstract_columns_iter_nonempty; exact Hnonempty).
      rewrite abstract_iter_head_value by
        (apply abstract_columns_iter_nonempty; exact Hnonempty).
      rewrite (abstract_suffix_good_inputs settle columns settle r Hgood
        ltac:(lia)), zinputs_repeat_true.
      apply arbitrary_true_iter_safe; [apply abstract_safe_width|]; assumption. }
  repeat split.
  - discriminate.
  - intro q.
    destruct (abstract_columns_iter_cons q born columns Hnonempty)
      as [c Hstate]. rewrite Hstate.
    constructor.
    + specialize (Hhead_safe_all q). now rewrite Hstate in Hhead_safe_all.
    + exact (Hsuffix_safe q).
  - intros q Hsettled.
    set (r := q-(settle+2*width)).
    set (base := settle+r).
    assert (Hq : q = base+2*width) by (unfold base, r; lia).
    destruct (abstract_columns_iter_cons base born columns Hnonempty)
      as [c Hstate].
    assert (Hc_safe : abstract_safe c).
    { specialize (Hhead_safe_all base). now rewrite Hstate in Hhead_safe_all. }
    assert (Hc_width : abstract_width c = odd_column_width (birth+3)).
    { pose proof (abstract_columns_iter_head_width base born columns Hnonempty) as H.
      rewrite Hstate in H. cbn in H. rewrite H.
      unfold born, abstract_birth, z_birth_width, odd_column_width; cbn. lia. }
    assert (Hinputs : abstract_head_inputs (2*abstract_width c)
        (abstract_columns_iter base columns) =
        repeat true (2*abstract_width c)).
    { apply abstract_suffix_good_inputs with (settle:=settle);
        [exact Hgood|unfold base; lia]. }
    assert (Hodd : Z.odd (abstract_value (hd c
        (abstract_columns_iter (2*abstract_width c)
          (c::abstract_columns_iter base columns)))) = true).
    { rewrite abstract_iter_head_value by
        (apply abstract_columns_iter_nonempty; exact Hnonempty).
      rewrite Hinputs, zinputs_repeat_true, Hc_width.
      apply z_odd_width_converges_odd.
      - pose proof (abstract_safe_width c Hc_safe).
        unfold odd_column_width in Hc_width; lia.
      - unfold abstract_safe in Hc_safe; now rewrite Hc_width in Hc_safe. }
    unfold abstract_head_odd. rewrite Hq, abstract_columns_iter_add.
    rewrite Hstate.
    replace (2*width) with (2*abstract_width c) by
      (rewrite Hc_width; unfold width, z_birth_width, odd_column_width; lia).
    destruct (abstract_columns_iter (2*abstract_width c)
      (c::abstract_columns_iter base columns)) eqn:E;
      [pose proof (abstract_columns_iter_nonempty (2*abstract_width c)
         (c::abstract_columns_iter base columns) ltac:(discriminate));
       congruence|exact Hodd].
Qed.

Lemma abstract_singleton_iter n c :
  abstract_columns_iter n [c] =
  [mkAbstractColumn (abstract_width c)
    (Nat.iter n (arbitrary_column_step (pow2 (abstract_width c)) true) (abstract_value c))].
Proof.
  induction n as [|n IH] in c |- *; [destruct c; reflexivity|].
  rewrite <- abstract_columns_iter_succ_right, IH.
  destruct c as [width value]; cbn [abstract_columns_next abstract_step].
  now rewrite Nat.iter_succ.
Qed.

Theorem abstract_singleton_good k c :
  abstract_width c = odd_column_width k -> abstract_safe c ->
  abstract_suffix_good (2*abstract_width c) [c].
Proof.
  intros Hwidth Hsafe.
  pose proof (abstract_safe_width c Hsafe) as Hwidth4.
  repeat split.
  - discriminate.
  - intro n. rewrite abstract_singleton_iter. constructor; [|constructor].
    unfold abstract_safe; cbn [abstract_width abstract_value].
    exact (arbitrary_true_iter_safe (abstract_width c) n (abstract_value c)
      Hwidth4 Hsafe).
  - intros n Hn.
    set (r := n-2*abstract_width c).
    assert (Hn' : n = r+2*abstract_width c) by (unfold r; lia).
    rewrite Hn', abstract_columns_iter_add, abstract_singleton_iter.
    cbn [abstract_head_odd].
    set (v := Nat.iter r (arbitrary_column_step (pow2 (abstract_width c)) true)
      (abstract_value c)).
    rewrite abstract_singleton_iter. cbn [abstract_value].
    change (Z.odd (Nat.iter (2*abstract_width c)
      (arbitrary_column_step (pow2 (abstract_width c)) true) v) = true).
    rewrite Hwidth. apply z_odd_width_converges_odd.
    + unfold odd_column_width in Hwidth. lia.
    + unfold v. rewrite <- Hwidth.
      exact (arbitrary_true_iter_safe (abstract_width c) r (abstract_value c)
        Hwidth4 Hsafe).
Qed.

Lemma abstract_suffix_good_shift settle columns :
  abstract_suffix_good settle columns ->
  abstract_suffix_good (Nat.pred settle) (abstract_columns_next columns).
Proof.
  intros [Hnonempty [Hsafe Hodd]].
  repeat split.
  - apply abstract_columns_next_nonempty. exact Hnonempty.
  - intro n; rewrite abstract_columns_iter_succ_left; apply Hsafe.
  - intros n Hn; rewrite abstract_columns_iter_succ_left; apply Hodd; lia.
Qed.
Definition columns_schedule (columns : list BinaryColumn) : Prop :=
  exists settle,
    abstract_suffix_good settle (map abstract_of_column columns) /\
    settle <= 2 * columns_width_sum columns.
Definition sobc1_round_invariant
    (current previous : nat) (columns : list BinaryColumn) : Prop :=
  round_width_dominance current previous columns /\
  columns_schedule columns /\
  columns_head_odd columns.

Theorem sobc1_round_invariant_progress current previous columns :
  sobc1_round_invariant current previous columns ->
  exists columns',
    post_ca_state (round_post_unary current previous)
        (round_primary_width current previous) columns
      -[source_tm]->+
    post_ca_state
      (round_post_unary
        (round_next_index current previous columns) current)
      (round_primary_width
        (round_next_index current previous columns) current)
      (z_column previous :: columns') /\
    sobc1_round_invariant
      (round_next_index current previous columns) current
      (z_column previous :: columns').
Proof.
  intros [Hwidth [Hschedule Hodd]].
  destruct Hschedule as [settle [Hgood Hsettle]].
  pose proof Hgood as [Habstract_nonempty [Habstract_safe _]].
  assert (Hnonempty : columns <> []) by
    (destruct columns; cbn in Habstract_nonempty; congruence).
  assert (Hsafe : Forall column_safe columns) by
    (apply columns_safe_abstract; exact (Habstract_safe O)).
  destruct (columns_step_exists columns Hnonempty Hsafe)
    as [columns' Hstep].
  exists columns'. split.
  - exact (sobc1_canonical_round current previous columns columns'
      Hnonempty Hodd Hstep).
  - pose proof (round_width_dominance_step current previous columns columns'
      Hnonempty Hstep Hwidth) as Hnext_width.
    destruct Hwidth as [Hbirth Hcurrent].
    pose proof (abstract_suffix_good_shift settle
      (map abstract_of_column columns) Hgood) as Hshift.
    rewrite <- (columns_step_abstract columns columns' Hsafe Hstep) in Hshift.
    assert (Hprotect : Nat.pred settle <= z_birth_width previous-4).
    { rewrite <- z_column_width; unfold column_width; rewrite z_column_e;
        unfold half_parameter in Hbirth |- *; lia. }
    split; [exact Hnext_width|].
    split; [|apply z_column_odd].
    exists (Nat.pred settle+2*z_birth_width previous); split.
    + cbn [map]; rewrite <- abstract_birth_eq.
      apply abstract_suffix_good_prepend_birth; assumption.
    + rewrite (output_columns_width_sum previous columns columns' Hstep),
        <- z_column_width; unfold column_width; rewrite z_column_e;
        unfold half_parameter in *; lia.
Qed.

Theorem sobc1_canonical_nonhalt current previous columns :
  sobc1_round_invariant current previous columns ->
  ~ halts source_tm
    (post_ca_state (round_post_unary current previous)
      (round_primary_width current previous) columns).
Proof.
  intro Hinv.
  eapply progress_nonhalt_cond with
    (C:=fun x : nat*nat*list BinaryColumn =>
      let '(i,j,cs) := x in post_ca_state
        (round_post_unary i j) (round_primary_width i j) cs)
    (P:=fun x => let '(i,j,cs) := x in sobc1_round_invariant i j cs)
    (i0:=(current, previous, columns)).
  - intros [[i j] cs] H; cbn in H |- *.
    destruct (sobc1_round_invariant_progress i j cs H)
      as [cs' [Hrun Hnext]].
    exists (round_next_index i j cs, i, z_column j::cs'); auto.
  - exact Hinv.
Qed.
Local Opaque Nat.pow.
Definition sobc1_second_base : nat :=
  2^(sobc1_first_half+25)-1 +
    2^(sobc1_first_half+1) *
      digits_value sobc1_second_tail_digits.
Definition sobc1_current_index : nat := sobc1_second_base-3.

Lemma double_pred_sum_mul a b c :
  1 <= a -> 2*a-2+2*b*c = 2*(a-1+b*c).
Proof.
  nia.
Qed.

Lemma sobc1_second_half_double_at n :
  2^sobc1_middle_width n-2 + digits_value (sobc1_second_digits_at n) =
  2*(2^(n+25)-1 + 2^(n+1)*digits_value sobc1_second_tail_digits).
Proof.
  unfold sobc1_middle_width.
  rewrite sobc1_second_digits_at_value.
  replace (n+26) with (S (n+25)) by lia.
  rewrite Nat.pow_succ_r by lia.
  replace (n+2) with (S (n+1)) by lia.
  rewrite Nat.pow_succ_r by lia.
  apply double_pred_sum_mul, Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate.
Qed.

Lemma sobc1_second_half_double :
  sobc1_second_half = 2*sobc1_second_base.
Proof.
  unfold sobc1_second_half, sobc1_second_digits, sobc1_second_base.
  apply sobc1_second_half_double_at.
Qed.

Lemma second_base_ge3_at n v :
  3 <= 2^(n+25)-1 + 2^(n+1)*v.
Proof.
  assert (4 <= 2^(n+25)).
  { change (2^2 <= 2^(n+25)); apply Nat.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma sobc1_second_base_ge3 : 3 <= sobc1_second_base.
Proof.
  unfold sobc1_second_base; apply second_base_ge3_at.
Qed.

Lemma half_parameter_pred3 n :
  3 <= n -> half_parameter (n-3) = 2*n.
Proof.
  unfold half_parameter; lia.
Qed.

Lemma sobc1_current_index_half :
  half_parameter sobc1_current_index = sobc1_second_half.
Proof.
  unfold sobc1_current_index.
  rewrite sobc1_second_half_double.
  apply half_parameter_pred3, sobc1_second_base_ge3.
Qed.

Lemma sobc1_first_half_large : 46 <= sobc1_first_half+1.
Proof.
  unfold sobc1_first_half.
  assert (48 <= 2^23).
  { assert (2^6 <= 2^23) by (apply Nat.pow_le_mono_r; lia).
    cbn in H; lia. }
  lia.
Qed.

Lemma entry_current_dominance n v :
  2*(n+22)+4 <= 2*(2^(n+25)-1+2^(n+1)*v)+1.
Proof.
  eapply Nat.le_trans with (m := 2^(n+25)).
  - replace (2*(n+22)+4) with (2*(n+20)+8) by lia.
    replace (n+25) with (n+20+5) by lia.
    apply pow2_linear_margin.
  -
  assert (1 <= 2^(n+25)) by
    (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  nia.
Qed.
Definition sobc1_entry_rest : list BDigit :=
  ([BB; BA]^^7) ++ [BA; BB; BB; BB; BA].
Definition sobc1_entry_digits : list BDigit :=
  [BB; BB] ++ sobc1_entry_rest.

Lemma sobc1_second_digits_split :
  sobc1_second_digits =
    repeat BA (sobc1_first_half+2) ++
      [BB; BB; BA; BB; BA] ++ sobc1_entry_rest.
Proof.
  unfold sobc1_second_digits, sobc1_second_digits_at,
    sobc1_second_tail_digits, sobc1_entry_rest.
  replace 9 with (2+7) by lia.
  rewrite lpow_add. cbn [lpow].
  repeat rewrite app_nil_r.
  repeat rewrite <- app_assoc. reflexivity.
Qed.
Definition sobc1_entry_column : BinaryColumn :=
  mkBinaryColumn 20 sobc1_entry_digits ltac:(
    unfold sobc1_entry_digits, sobc1_entry_rest;
    rewrite !length_app, lpow_length; reflexivity).

Lemma sobc1_entry_column_facts :
  column_width sobc1_entry_column = odd_column_width 10 /\
  column_safe sobc1_entry_column /\
  Nat.odd (column_value sobc1_entry_column) = true.
Proof.
  assert (Hsplit : sobc1_entry_digits =
      ([BB; BB] ++ ([BB; BA]^^7) ++ [BA; BB; BB; BB]) ++ [BA]).
  { unfold sobc1_entry_digits, sobc1_entry_rest.
    repeat rewrite <- app_assoc; reflexivity. }
  split; [reflexivity|]; split.
  - change (3 <= digits_value sobc1_entry_digits /\
      digits_value sobc1_entry_digits <= 2^21-6).
    rewrite Hsplit; split.
    + apply digits_value_BB_BB_lower.
    + apply digits_value_msb_BA_safe.
      rewrite !length_app, lpow_length; cbn; lia.
  - change (Nat.odd (digits_value sobc1_entry_digits) = true).
    rewrite Hsplit; apply digits_value_BB_odd.
Qed.

Theorem sobc1_entry_invariant :
  sobc1_round_invariant sobc1_current_index sobc1_middle_index
    [sobc1_entry_column].
Proof.
  destruct sobc1_entry_column_facts as [Hcolumn_width [Hsafe Hodd]].
  unfold column_width in Hcolumn_width.
  split.
  - unfold round_width_dominance.
    rewrite columns_width_sum_singleton, Hcolumn_width; split.
    + unfold odd_column_width, half_parameter.
      fold (half_parameter sobc1_middle_index).
      rewrite sobc1_middle_index_half; exact sobc1_first_half_large.
    + rewrite sobc1_middle_index_half,
        sobc1_current_index_half, sobc1_second_half_double.
      unfold odd_column_width, sobc1_second_base.
      replace (sobc1_first_half+1+(2*10+1))
        with (sobc1_first_half+22) by lia.
      apply entry_current_dominance.
  - split; [|exact Hodd].
    exists (2*column_width sobc1_entry_column); split.
    + cbn [map]; apply abstract_singleton_good with (k:=10);
        [exact Hcolumn_width|now apply column_safe_abstract].
    + rewrite columns_width_sum_singleton; unfold column_width; lia.
Qed.
Definition sobc1_first_output : list Sym :=
  A8^^20 ++ B8 ++ A8 ++ D8 ++ A8.

Lemma sobc1_first_exception_seg :
  segRLs source_tm (hashes^^sobc1_first_half) []
    (E8^^23 ++ A8) sobc1_first_output.
Proof.
  pose proof (segRLs_concat hash_E (segRLs_O source_tm A8)) as Hbase.
  pose proof (segRLs_concat (hash_E_even 1) Hbase) as H4.
  pose proof (segRLs_concat (hash_E_odd 4) H4) as H11.
  pose proof (prefix_E_even 20 11 _ _ 0 H11) as Hrun.
  unfold sobc1_first_half, sobc1_first_output.
  replace (2^23 + 2^22 + 2^20 - 2)
    with (2^20*11 + 2*(2^20-1)).
  2: {
    replace 23 with (20+3) by lia.
    replace 22 with (20+2) by lia.
    rewrite !Nat.pow_add_r. cbn [Nat.pow].
    pose proof (Nat.pow_nonzero 2 20 ltac:(lia)). nia. }
  replace 23 with (20+3) by lia.
  rewrite (lpow_add _ 20 3 E8).
  replace (E8^^3) with (E8 ++ E8 ++ E8) by reflexivity.
  repeat rewrite <- app_assoc.
  exact Hrun.
Qed.
(** The ordinary binary word immediately before the second exceptional
    counter reaches the dotted edge. *)
Definition sobc1_middle_digits (n : nat) : list BDigit :=
  repeat BA (n+22) ++ [BB; BB; BA; BA].

Lemma sobc1_middle_digits_word n :
  digits_word (sobc1_middle_digits n) =
    A8^^(n+22) ++ B8 ++ B8 ++ A8 ++ A8.
Proof.
  unfold sobc1_middle_digits.
  rewrite digits_word_app, digits_word_repeat_BA.
  reflexivity.
Qed.

Lemma sobc1_middle_digits_length n :
  length (sobc1_middle_digits n) = sobc1_middle_width n.
Proof.
  unfold sobc1_middle_digits, sobc1_middle_width.
  rewrite length_app, repeat_length. cbn. lia.
Qed.

Lemma sobc1_middle_finish_count n :
  bfinish_count (sobc1_middle_digits n) 0 =
    13 * 2^(n+22) - 1.
Proof.
  unfold sobc1_middle_digits.
  rewrite bfinish_count_app, bfinish_repeat_BA_formula.
  cbn [bfinish_count].
  pose proof (Nat.pow_nonzero 2 (n+22) ltac:(lia)). nia.
Qed.

Lemma sobc1_middle_to_zero_edge n :
  sideRLs source_tm
    (hashes^^
      (13*2^(n+22)-1 + (2^(n+26)+1)))
    ((digits_word (sobc1_middle_digits n)) *> 0inf)
    ((A8^^(n+26) ++ [1;1]%sym) *> 0inf).
Proof.
  pose proof (bfinish_spec
    (sobc1_middle_digits n) 0) as Hfinish.
  pose proof (segRLs_0inf Hfinish) as Hfinish_side.
  rewrite sobc1_middle_digits_length in Hfinish_side.
  replace (sobc1_middle_width n) with (S (n+25)) in Hfinish_side by
    (unfold sobc1_middle_width; lia).
  pose proof (sideRLs_trans Hfinish_side
    (sobc1_B_edge (n+25))) as H.
  rewrite sobc1_middle_finish_count in H.
  replace (S (n+25)) with (n+26) in H by lia.
  repeat rewrite <- lpow_add in H.
  exact H.
Qed.

Lemma sobc1_initial_blank_bridge :
  sideRLs source_tm hashes
    ((C8 ++ B8 ++ U^^2 ++ A8^^2) *> 0inf)
    ((D8 ++ B8 ++ B8 ++ A8 ++ A8) *> 0inf).
Proof.
  apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity.
Qed.

Lemma sobc1_after_cd_to_before_second_finish_side n :
  sideRLs source_tm
    (hashes^^sobc1_before_second_finish_calls n)
    ((A8^^n ++ C8 ++ A8 ++ sobc1_first_output) *> 0inf)
    ((A8^^sobc1_middle_width n ++ [1;1]%sym) *> 0inf).
Proof.
  pose proof (segRLs_0inf (primary_one_rule n _ _
    (segRLs_concat (sobc1_hash_CABAD 21) (segRLs_O source_tm A8)))) as Hcab.
  pose proof (segRLs_0inf (primary_D_absorb n
    (C8^^21++B8++U^^2++A8++A8))) as Hd1.
  pose proof (segRLs_0inf (c_sweep (n+1) 10
    (B8++U^^2++A8++A8))) as Hsweep.
  pose proof (primary_one_side_rule (n+21) _ _
    sobc1_initial_blank_bridge) as Hbridge.
  pose proof (segRLs_0inf (primary_D_absorb (n+21)
    (B8++B8++A8++A8))) as Hd2.
  pose proof (sobc1_middle_to_zero_edge n) as Hedge.
  replace (S (n+21)) with (n+22) in Hd2 by lia.
  rewrite sobc1_middle_digits_word in Hedge.
  repeat rewrite <- Str_app_assoc in Hbridge.
  replace (A8^^2) with (A8++A8) in Hbridge by reflexivity.
  replace (n+1+2*10) with (n+21) in Hsweep by lia.
  replace (S n) with (n+1) in Hd1 by lia.
  replace (2*10+1) with 21 in Hsweep by lia.
  pose proof (sideRLs_trans Hcab (sideRLs_trans Hd1
    (sideRLs_trans Hsweep (sideRLs_trans Hbridge
      (sideRLs_trans Hd2 Hedge))))) as H.
  repeat rewrite <- lpow_add in H.
  unfold sobc1_first_output, sobc1_middle_width,
    sobc1_before_second_finish_calls; exact H.
Qed.

Lemma sobc1_after_cd_to_before_second_finish n :
  after_cd n sobc1_first_output -[source_tm]->*
  ordinary_left (cd_calls n+sobc1_before_second_finish_calls n)
    {{{((B, []), R)}}}
    ((A8^^sobc1_middle_width n++[1;1]) *> 0inf).
Proof.
  unfold after_cd, cd_output.
  applys_eq (sideRLs_concat_1
    (sobc1_after_cd_to_before_second_finish_side n)
    (left_emit_calls (sobc1_before_second_finish_calls n) (cd_calls n)));
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Theorem sobc1_first_done_to_second_exception :
  exception_done sobc1_first_half sobc1_first_output -[source_tm]->*
    exception_raw_source sobc1_second_half (sobc1_first_half+25).
Proof.
  eapply evstep_trans.
  - apply progress_evstep, exception_done_cd.
    rewrite <- sobc1_middle_index_half; unfold half_parameter; lia.
  - eapply evstep_trans with (c':=ordinary_left
      (cd_calls sobc1_first_half+
        sobc1_before_second_finish_calls sobc1_first_half)
      {{{((B, []), R)}}}
      ((A8^^sobc1_middle_width sobc1_first_half++[1;1]) *> 0inf)).
    + apply sobc1_after_cd_to_before_second_finish.
    + apply progress_evstep.
      replace (sobc1_first_half+25) with
        (sobc1_middle_width sobc1_first_half-1) by
        (unfold sobc1_middle_width; lia).
      apply ordinary_all_A_to_exception;
        [unfold sobc1_middle_width; lia|exact sobc1_second_total_half].
Qed.

Lemma sobc1_second_tail_word :
  digits_word sobc1_second_digits =
  A8^^(2*(sobc1_middle_index+4)) ++
    B8++B8++A8++B8++A8++digits_word sobc1_entry_rest.
Proof.
  assert (Heq:sobc1_first_half+2=2*(sobc1_middle_index+4)).
  { pose proof sobc1_middle_index_half as H; unfold half_parameter in H;
    set (a:=sobc1_first_half) in *; set (p:=sobc1_middle_index) in *;
    clearbody a p; lia. }
  rewrite sobc1_second_digits_split, !digits_word_app,
    digits_word_repeat_BA; cbn [digits_word digit_word].
  rewrite Heq; repeat rewrite app_nil_r; reflexivity.
Qed.

Lemma sobc1_entry_primary_width :
  sobc1_second_half + 2*(sobc1_middle_index+4)+4 =
    round_primary_width sobc1_current_index sobc1_middle_index.
Proof.
  unfold round_primary_width.
  rewrite sobc1_current_index_half, sobc1_middle_index_half.
  pose proof sobc1_middle_index_half as H.
  unfold half_parameter in H.
  set (n := sobc1_second_half) in *.
  set (a := sobc1_first_half) in *.
  set (m := sobc1_middle_index) in *.
  clearbody n a m. lia.
Qed.

Theorem sobc1_c0_to_entry_post :
  c0 -[source_tm]->*
  post_ca_state
    (round_post_unary sobc1_current_index sobc1_middle_index)
    (round_primary_width sobc1_current_index sobc1_middle_index)
    [sobc1_entry_column].
Proof.
  eapply evstep_trans; [eapply without_counter;
    apply sobc1_first_call_reachable|].
  eapply evstep_trans; [apply sobc1_first_call_to_exception|].
  eapply evstep_trans; [apply sobc1_exception_from_seg,
    sobc1_first_exception_seg|].
  eapply evstep_trans; [apply sobc1_first_done_to_second_exception|].
  eapply evstep_trans.
  - apply sobc1_exception_from_seg.
    pose proof (standard_mixed_to_binary_spec
      (sobc1_first_half+25) sobc1_second_digits ltac:(
        rewrite sobc1_second_digits_length; unfold sobc1_middle_width;
        replace 26 with (S 25) by reflexivity;
        rewrite Nat.add_succ_r; reflexivity)) as H.
    unfold sobc1_second_half, sobc1_middle_width.
    replace 26 with (S 25) by reflexivity.
    rewrite Nat.add_succ_r; exact H.
  - apply progress_evstep; rewrite sobc1_second_tail_word.
    unfold post_ca_state, post_ca_side.
    rewrite <- sobc1_entry_primary_width.
    unfold round_post_unary; rewrite sobc1_current_index_half.
    cbn [binary_columns_word spaced_words map binary_column_word
      sobc1_entry_column sobc1_entry_digits column_digits].
    exact (exception_done_ca sobc1_second_half
      (sobc1_middle_index+4) (digits_word sobc1_entry_rest)
      ltac:(rewrite <- sobc1_current_index_half;
        unfold half_parameter; lia)).
Qed.

Theorem sobc1_nonhalt : ~ halts source_tm c0.
Proof.
  intro Hhalt.
  apply (sobc1_canonical_nonhalt _ _ _ sobc1_entry_invariant).
  apply (proj1 (halts_evstep_iff source_tm c0 _ sobc1_c0_to_entry_post)), Hhalt.
Qed.

Print Assumptions sobc1_nonhalt.

End SOBCv10.

Module W61Exit.
(** Exit from the counter system.

    These lemmas use SOBCv10's frame and transition table
    ([1LB0RD_1LC0RC_1RA1LC_1LE0RB_1LF---_0LA0LE]). The target machine is
    this table mirrored and renamed, started in SOBCv10's state D.

    Contents
    - T2   : the raw pass with a tail [U^(2k+1) B t], k = 0..5
             ([raw_tail_base], [raw_tail_column], [raw_tail_columns]).
    - O    : the raw pass with k = 6 overflows into the cycler window
             ([overflow_base], [overflow_column], [overflow_columns]).
    - C    : the 919-step, 3-cell translated cycler ([cycler_step],
             [cycler_nonhalt]); with O: [exit_nonhalt].
    - E'/E'': the nested exception launched by a trigger hash inside an
             ordinary exception's call phase ([nested_pre_left],
             [launch_far], [relaunches_far], [nested_launch]), its counter
             run to the all-B word ([nested_counter]), and the whole exit
             from exception 9's decode trigger ([nested_exit]). *)

From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10.
Require Import ZifyNat Lia Arith List.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Ltac run_c steps :=
  unfold source_tm; eapply multistep_progress with (n := steps);
  apply multistep_c_spec; vm_compute; reflexivity.

(** * 1. Law T2: the raw pass with a tail *)

(** The tail digit after a raw pass with tail index [k]: level [k - 1]. *)
Definition y_after (k : nat) : list Sym :=
  match k with
  | 0%nat => A8
  | 1%nat => B8
  | 2%nat => E8 ++ [1;1]
  | 3%nat => D8 ++ [1;1]
  | 4%nat => A8 ++ [1;1]
  | _ => B8 ++ [1;1]
  end.

(** The tail at level 4 ([B t]) behind [2k+1] separators. *)
Definition tail_word (k : nat) : list Sym := U^^(2*k+1) ++ B8 ++ [1;1].

Lemma raw_tail_base k l : k <= 5 ->
  l {{{((B, []), R)}}} ((B8 ++ U^^(2*k+1) ++ B8 ++ [1;1]) *> 0inf)
    -[source_tm]->+
  ([1;0;1] *> l) {{{((F, []), L)}}} ((U^^(2*k+3) ++ y_after k) *> 0inf).
Proof.
  intro Hk.
  destruct k as [|[|[|[|[|[|k]]]]]];
    [run_c 97|run_c 199|run_c 343|run_c 501|run_c 695|run_c 909|lia].
Qed.

Lemma raw_tail_column k e l : k <= 5 ->
  l {{{((B, []), R)}}} ((B8^^S e ++ tail_word k) *> 0inf)
    -[source_tm]->+
  ([1;0;1] *> l) {{{((F, []), L)}}}
    ((E8^^e ++ U^^(2*k+3) ++ y_after k) *> 0inf).
Proof.
  intro Hk.
  induction e as [|e IH] in l |- *.
  - exact (raw_tail_base k l Hk).
  - eapply evstep_progress_trans.
    + applys_eq (raw_B_forward l ((B8^^(S e) ++ tail_word k) *> 0inf)).
    + eapply progress_trans.
      * applys_eq (IH (Q8 *> l)).
      * applys_eq (raw_B_return l
          ((E8^^e ++ U^^(2*k+3) ++ y_after k) *> 0inf)).
Qed.

(** Column layouts: columns [es] (column [i] is [B^(S e_i)]), then a last
    column [B^(S e)], then the tail. *)
Definition full_tail (es : list nat) (e k : nat) : list Sym :=
  spaced_words (map (fun e => B8^^S e) es ++ [B8^^S e]) ++ tail_word k.

(** After the raw pass: every column but the last is [E^e A]; the last
    column has lost its top digit ([E^e]); the U run has grown by a pair. *)
Definition mixed_tail (es : list nat) (e k : nat) : list Sym :=
  spaced_words (map (fun e => E8^^e ++ A8) es ++ [E8^^e]) ++
    U^^(2*k+3) ++ y_after k.

Lemma spaced_snoc_cons (w : list Sym) ws x :
  spaced_words ((w :: ws) ++ [x]) = w ++ U^^2 ++ spaced_words (ws ++ [x]).
Proof.
  destruct ws; reflexivity.
Qed.

Theorem raw_tail_columns es e k l : k <= 5 ->
  l {{{((B, []), R)}}} (full_tail es e k *> 0inf)
    -[source_tm]->+
  ([1;0;1] *> l) {{{((F, []), L)}}} (mixed_tail es e k *> 0inf).
Proof.
  intro Hk.
  induction es as [|e0 es IH] in l |- *.
  - exact (raw_tail_column k e l Hk).
  - unfold full_tail, mixed_tail. cbn [map].
    rewrite !spaced_snoc_cons.
    eapply evstep_progress_trans.
    + applys_eq (raw_Bs_to_Qs (S e0) l
        ((U^^2 ++ full_tail es e k) *> 0inf));
        unfold full_tail; repeat rewrite Str_app_assoc; reflexivity.
    + eapply evstep_progress_trans.
      * applys_eq (raw_Us_to_Xs 2 (Q8^^(S e0) *> l)
          (full_tail es e k *> 0inf)).
      * eapply progress_trans.
        -- exact (IH (X4^^2 *> Q8^^(S e0) *> l)).
        -- eapply progress_evstep_trans.
           ++ applys_eq (raw_separator_return (Q8^^e0 *> l)
                (mixed_tail es e k *> 0inf)).
           ++ applys_eq (raw_B_returns e0 l
                ((A8 ++ U^^2 ++ mixed_tail es e k) *> 0inf));
                unfold mixed_tail; repeat rewrite Str_app_assoc;
                reflexivity.
Qed.

(** * 2. Lemma O (overflow) and Lemma C (translated cycler) *)

(** The cycler window, in tape order (left to right). *)
Definition Yw : list Sym :=
  [1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;
   1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;1;0;1;0;0;1;0;0].

(** C: every 919 steps the head moves 3 cells right; [L] is never read. *)
Lemma cycler_step L :
  (rev Yw *> L) {{B}}> 0inf -[source_tm]->+ (rev Yw *> [0;0;1] *> L) {{B}}> 0inf.
Proof.
  run_c 918.
Qed.

Theorem cycler_nonhalt L : ~ halts source_tm ((rev Yw *> L) {{B}}> 0inf).
Proof.
  apply progress_nonhalt_simple with
    (C := fun L => (rev Yw *> L) {{B}}> 0inf) (i0 := L).
  intro L'. exists ([0;0;1] *> L'). apply cycler_step.
Qed.

(** O, base: from the last remaining [B] of the last column, the k = 6 raw
    pass never comes back; 1208 steps, the left side is never read. *)
Lemma overflow_base l :
  l {{{((B, []), R)}}} ((B8 ++ tail_word 6) *> 0inf)
    -[source_tm]->+
  (rev Yw *> [0;1;0;1] *> l) {{B}}> 0inf.
Proof.
  run_c 1207.
Qed.

Lemma overflow_column e l : exists l',
  l {{{((B, []), R)}}} ((B8^^S e ++ tail_word 6) *> 0inf)
    -[source_tm]->+ (rev Yw *> l') {{B}}> 0inf.
Proof.
  induction e as [|e IH] in l |- *.
  - exists ([0;1;0;1] *> l). exact (overflow_base l).
  - destruct (IH (Q8 *> l)) as [l' H]. exists l'.
    eapply evstep_progress_trans; [|exact H].
    applys_eq (raw_B_forward l ((B8^^(S e) ++ tail_word 6) *> 0inf)).
Qed.

Theorem overflow_columns es e l : exists l',
  l {{{((B, []), R)}}} (full_tail es e 6 *> 0inf)
    -[source_tm]->+ (rev Yw *> l') {{B}}> 0inf.
Proof.
  induction es as [|e0 es IH] in l |- *.
  - exact (overflow_column e l).
  - destruct (IH (X4^^2 *> Q8^^(S e0) *> l)) as [l' H]. exists l'.
    unfold full_tail in *. cbn [map]. rewrite spaced_snoc_cons.
    eapply evstep_progress_trans.
    + applys_eq (raw_Bs_to_Qs (S e0) l
        ((U^^2 ++ full_tail es e 6) *> 0inf));
        unfold full_tail; repeat rewrite Str_app_assoc; reflexivity.
    + eapply evstep_progress_trans; [|exact H].
      applys_eq (raw_Us_to_Xs 2 (Q8^^(S e0) *> l)
        (full_tail es e 6 *> 0inf)).
Qed.

(** O + C: a hash that walks right into an all-B layout whose tail is
    [U^13 B t] (k = 6) starts the cycler, whatever lies to its left. *)
Theorem exit_nonhalt es e l :
  ~ halts source_tm (l {{{((B, []), R)}}} (full_tail es e 6 *> 0inf)).
Proof.
  destruct (overflow_columns es e l) as [l' H].
  intro Hh. apply (cycler_nonhalt l').
  exact (proj1 (halts_evstep_iff source_tm _ _ (progress_evstep _ _ _ H)) Hh).
Qed.

(** * 3. The nested exceptions E' and E'' *)

(** SOBCv10's exception left sides with an arbitrary far end. *)
Definition pre_left_far (n : nat) (far : side) : side :=
  ([1;0;1;0] ++ V4^^(2*n+2)) *> far.
Definition call_left_far (remaining finished : nat) (far : side) : side :=
  (X4^^(2*finished+5) ++ V4^^(2*remaining)) *> far.

Lemma pre_rotate_list m :
  [1;0;1] ++ X4^^(S m) = [1;0;1;0] ++ V4^^m ++ [0;1;0].
Proof.
  induction m as [|m IH].
  - reflexivity.
  - replace (X4^^(S (S m))) with (X4^^(S m) ++ X4)
      by (rewrite lpow_shift; reflexivity).
    rewrite app_assoc, IH.
    replace (V4^^(S m)) with (V4^^m ++ V4)
      by (rewrite lpow_shift; reflexivity).
    repeat rewrite <- app_assoc. reflexivity.
Qed.

(** The raw return of a trigger hash puts [101] in front of the finished
    calls; that is an exception pre-state whose far end holds the outer
    exception's pending calls. *)
Lemma nested_pre_left c f :
  [1;0;1] *> exception_call_left c f =
  pre_left_far (S f) ([0;1;0] *> V4^^(2*c) *> [1;0;1] *> 0inf).
Proof.
  unfold exception_call_left, pre_left_far.
  rewrite <- !Str_app_assoc. f_equal.
  repeat rewrite <- app_assoc.
  replace (2*f+5) with (S (2*f+4)) by lia.
  replace (2 * S f + 2) with (2*f+4) by lia.
  rewrite app_assoc, pre_rotate_list.
  repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma launch_far k far :
  sideRLs (flip source_tm) [left_hash] (pre_left_far (S k) far) (call_left_far k 0 far).
Proof.
  unfold pre_left_far, call_left_far.
  replace (2*S k+2) with (4+2*k) by lia; rewrite lpow_add.
  cbn [Nat.mul Nat.add].
  applys_eq (segRLs_sideRLs_concat left_launch_segment
    (sideRLseq_O (flip source_tm) (V4^^(2*k) *> far)));
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Lemma relaunch_far remaining finished far :
  sideRLs (flip source_tm) [left_hash]
    (call_left_far (S remaining) finished far)
    (call_left_far remaining (S finished) far).
Proof.
  pose proof (segRLs_concat
    (left_hash_X_pairs finished) left_relaunch_base) as Hseg.
  unfold call_left_far.
  replace (2*S remaining) with (2+2*remaining) by lia.
  replace (2*S finished+5) with (2*finished+7) by lia.
  repeat rewrite Str_app_assoc.
  rewrite <- (lpow_add' X4 (2*finished) 5).
  rewrite <- (lpow_add' X4 (2*finished) 7).
  rewrite <- (lpow_add' V4 2 (2*remaining)).
  applys_eq (segRLs_sideRLs_concat Hseg
    (sideRLseq_O (flip source_tm) (V4^^(2*remaining) *> far)));
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Lemma relaunches_far k r finished far :
  sideRLs (flip source_tm) ([left_hash]^^k)
    (call_left_far (k + r) finished far)
    (call_left_far r (finished + k) far).
Proof.
  induction k as [|k IH] in finished |- *.
  - cbn [lpow Nat.add]. replace (finished + 0) with finished by lia.
    constructor.
  - cbn [lpow]; eapply sideRLs_trans.
    + apply relaunch_far.
    + applys_eq (IH (S finished)); flia.
Qed.

(** The nested launch: from the nested pre-state, [h] calls run through the
    counter; the next call leaves with [r] calls still pending. *)
Theorem nested_launch h r far inp out :
  segRLs source_tm (hashes^^h) [] inp out ->
  pre_left_far (S (h + r)) far {{{((F, []), L)}}} (inp *> 0inf)
    -[source_tm]->+
  call_left_far r h far {{{((B, []), R)}}} (out *> 0inf).
Proof.
  intro Hseg.
  eapply progress_evstep_trans.
  - exact (sideRLs_1L _ _ _ _ _ (launch_far (h + r) far) (inp *> 0inf)).
  - pose proof (segRLs_0inf Hseg) as Hright.
    pose proof (relaunches_far h r 0 far) as Hleft.
    cbn [Nat.add] in Hleft.
    exact (sideRLs_concat_1 Hright Hleft).
Qed.

(** E''s counter, from the raw-pass word to the all-B word. *)
Lemma E_to_B m : segRLs source_tm (hashes^^(3*(2^m-1))) [] (E8^^m) (B8^^m).
Proof.
  induction m as [|m IH].
  - rewrite Nat.pow_0_r. cbn [Nat.sub Nat.mul Nat.add lpow]. constructor.
  - applys_eq (segRLs_concat (hash_E_odd (3*(2^m-1))) IH).
    f_equal. rewrite Nat.pow_succ_r'.
    generalize (Nat.pow_nonzero 2 m ltac:(lia)). lia.
Qed.

Lemma digits_word_repeat_BB n : digits_word (repeat BB n) = B8^^n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [repeat digits_word digit_word lpow]. rewrite IH. reflexivity.
Qed.

Lemma digits_value_repeat_BB n : digits_value (repeat BB n) = 2^n - 1.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [repeat digits_value]. rewrite IH, Nat.pow_succ_r'.
  generalize (Nat.pow_nonzero 2 n ltac:(lia)); lia.
Qed.

(** Calls that take [mixed] columns [es] and a last column [E^(S e)] to the
    all-B layout, with no carry into the tail. *)
Fixpoint nested_required (es : list nat) (e : nat) : nat :=
  match es with
  | [] => 3*(2^(S e)-1)
  | e0 :: es' =>
      (nested_required es' e + 1) * 2^(S e0) - 2 + (2^(S e0) - 1)
  end.

Lemma nested_counter es e :
  segRLs source_tm (hashes^^nested_required es e) []
    (spaced_words (map (fun e => E8^^e ++ A8) es ++ [E8^^S e]))
    (spaced_words (map (fun e => B8^^S e) es ++ [B8^^S e])).
Proof.
  induction es as [|e0 es IH].
  - exact (E_to_B (S e)).
  - cbn [map nested_required]. rewrite !spaced_snoc_cons.
    pose proof (standard_mixed_to_binary_out_spec e0 (repeat BB (S e0))
      (nested_required es e) (repeat_length _ _)) as H0.
    rewrite digits_word_repeat_BB, digits_value_repeat_BB in H0.
    exact (segRLs_concat H0
      (segRLs_concat (hashes_U_run (nested_required es e) 2) IH)).
Qed.

(** The exit, from the configuration in which exception 9's trigger hash
    leaves its call region: [c] calls pending, [f] finished, the counter all
    B with layout [es ++ [S (S e)]] and the tail [U^11 B t] (k = 5).
    The trigger's raw pass (T2, k = 5) starts E' with [S f] calls; E'' fires
    after [nested_required es e] of them, and its raw pass overflows (O)
    into the cycler (C). *)
Theorem nested_exit c f es e :
  nested_required es e <= f ->
  ~ halts source_tm (exception_call_left c f {{{((B, []), R)}}}
    (full_tail es (S e) 5 *> 0inf)).
Proof.
  intros Hle Hh.
  set (h := nested_required es e) in *.
  set (far := [0;1;0] *> V4^^(2*c) *> [1;0;1] *> 0inf).
  pose proof (raw_tail_columns es (S e) 5 (exception_call_left c f)
    ltac:(lia)) as Hraw.
  rewrite nested_pre_left in Hraw. fold far in Hraw.
  pose proof (segRLs_concat (nested_counter es e) (segRLs_O source_tm (tail_word 6)))
    as Hseg.
  pose proof (nested_launch h (f - h) far _ _ Hseg) as Hlaunch.
  replace (S (h + (f - h))) with (S f) in Hlaunch by lia.
  destruct (overflow_columns es e (call_left_far (f - h) h far))
    as [l' Hover].
  apply (cycler_nonhalt l').
  refine (proj1 (halts_evstep_iff source_tm _ _ _) Hh).
  apply progress_evstep.
  eapply progress_trans; [exact Hraw|].
  eapply progress_trans; [exact Hlaunch|].
  exact Hover.
Qed.

Print Assumptions nested_exit.
Print Assumptions exit_nonhalt.

End W61Exit.

Module TailState.
(** Signed digits and counter configurations with a tail. *)
From BusyCoq Require Import Individual62 Longitudinal Flip Permute.
Import SOBCv10 W61Exit.
Require Import ZifyNat Lia Arith ZArith String List.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

(** * 1. The tail-aware post-C/A state *)

(** Digits of the last column: SOBCv10's [A]/[B] plus the deficit (pre-state)
    digits [D] (-1) and [E] (-2) that a short decode leaves behind (law T3). *)
Inductive SDigit := SE | SD | SA | SB.
Definition sdigit_word (d : SDigit) : list Sym :=
  match d with SE => E8 | SD => D8 | SA => A8 | SB => B8 end.
Definition sdigit_value (d : SDigit) : Z :=
  match d with SE => (-2)%Z | SD => (-1)%Z | SA => 0%Z | SB => 1%Z end.
Fixpoint sdigits_word (ds : list SDigit) : list Sym :=
  match ds with [] => [] | d :: ds' => sdigit_word d ++ sdigits_word ds' end.
Fixpoint sdigits_value (ds : list SDigit) : Z :=
  match ds with
  | [] => 0%Z
  | d :: ds' => (sdigit_value d + 2 * sdigits_value ds')%Z
  end.
Definition sdigit_of (d : BDigit) : SDigit := match d with BA => SA | BB => SB end.

(** The counter after C/A: primary [A^primary], the z-columns [zs] (SOBCv10
    binary columns), the last column [last], then the tail [U^(2k+1) y] with
    [y = y_after lv]: tail value [lv] (= level + 1), i.e.
    [A], [B], [E t], [D t], [A t], [B t] for [lv] = 0..5. *)
Definition tail_layout (primary : nat) (zs : list BinaryColumn)
    (last : list SDigit) (k lv : nat) : list Sym :=
  A8^^primary ++ U^^2 ++
  spaced_words (map binary_column_word zs ++ [sdigits_word last]) ++
  U^^(2*k+1) ++ y_after lv.

Definition post_ca_tail (unary primary : nat) (zs : list BinaryColumn)
    (last : list SDigit) (k lv : nat) : Q * tape :=
  ordinary_left unary {{{((B, []), R)}}} (tail_layout primary zs last k lv *> 0inf).

(** * 2. The round parameters with a tail (laws T1 and T3) *)

Fixpoint zs_value (o : nat) (zs : list BinaryColumn) : Z :=
  match zs with
  | [] => 0%Z
  | c :: zs' => (2^Z.of_nat o * Z.of_nat (column_value c) +
                 zs_value (o + column_width c) zs')%Z
  end.

(** W: digits before the tail.  V: the counter value, tail level at 2^W. *)
Definition tail_W (primary : nat) zs (last : list SDigit) : nat :=
  primary + columns_width_sum zs + length last.
Definition tail_V (primary : nat) zs last (lv : nat) : Z :=
  (zs_value primary zs +
   2^Z.of_nat (primary + columns_width_sum zs) * sdigits_value last +
   2^Z.of_nat (tail_W primary zs last) * (Z.of_nat lv - 1))%Z.

(** T1: the hash that finds every digit [B] and the tail at [B t]. *)
Definition trigger_hash primary zs last lv : Z :=
  (5 * 2^Z.of_nat (tail_W primary zs last) - tail_V primary zs last lv)%Z.

(** The exception's n: the tally after the trigger hash is [2n+1]. *)
Definition tail_next_half current previous zs last lv : Z :=
  ((Z.of_nat (round_post_unary current previous) +
    trigger_hash (round_primary_width current previous) zs last lv - 1) / 2)%Z.
Definition tail_next_index current previous zs last lv : nat :=
  Z.to_nat ((tail_next_half current previous zs last lv - 6) / 2).

(** Effective tail level: the level minus the deficit left in the last column. *)
Definition eff_level (last : list SDigit) (lv : nat) : Z :=
  ((sdigits_value last + 2^Z.of_nat (length last) * (Z.of_nat lv - 1)) /
     2^Z.of_nat (length last))%Z.

(** The decode of the next exception reaches [B t] with a carry left over. *)
Definition tail_triggers (k : nat) (last : list SDigit) (lv : nat) : Prop :=
  (Z.of_nat k - 1 + (2 - eff_level last lv) >= 5)%Z.


End TailState.

Module FiniteColumns.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10.
Require Import ZifyNat Lia Arith ZArith List Bool.
Import ListNotations.
Local Open Scope nat_scope.

(** A finite budget of safe steps, independent of every right-hand parity.
    Only three nontriggering rounds are needed for this start. *)
Definition column_budget (n : nat) (c : BinaryColumn) : Prop :=
  exists phase,
    n <= lineage_fuel phase /\
    low_slice (pow2 (column_width c)) (lineage_width phase)
      (lineage_residue phase) (Z.of_nat (column_value c)).

Lemma column_budget_safe n c : column_budget n c -> column_safe c.
Proof.
  intros [phase [Hfuel Hslice]].
  apply column_safe_abstract.
  unfold abstract_safe, abstract_of_column; cbn.
  exact (low_slice_safe _ _ _ _ Hslice (lineage_residue_bounds phase)).
Qed.

Lemma lineage_next_fuel phase :
  1 <= lineage_fuel phase ->
  exists phase', lineage_next phase phase' /\
    S (lineage_fuel phase') = lineage_fuel phase.
Proof.
  destruct phase as [n|[|n]|n]; cbn [lineage_fuel]; intro H; try lia.
  - exists (LEven (S n)); split; [constructor|cbn; lia].
  - exists (LOdd n); split; [constructor|cbn; lia].
  - exists (LEven n); split; [constructor|cbn; lia].
Qed.

Lemma column_budget_step n c c' b :
  column_budget (S n) c -> column_step b c c' -> column_budget n c'.
Proof.
  intros Hbudget Hstep.
  pose proof (column_budget_safe _ _ Hbudget) as Hsafe.
  destruct Hbudget as [phase [Hfuel Hslice]].
  destruct (lineage_next_fuel phase ltac:(lia)) as [phase' [Hnext Hleft]].
  exists phase'; split; [lia|].
  pose proof (abstract_column_step c c' b Hsafe Hstep) as Hab.
  pose proof (f_equal abstract_width Hab) as Hw.
  pose proof (f_equal abstract_value Hab) as Hv.
  cbn [abstract_of_column abstract_step abstract_width abstract_value] in Hw, Hv.
  rewrite Hw, Hv.
  exact (lineage_step_preserves_slice _ _ _ _ b Hnext Hslice).
Qed.

Lemma z_column_budget previous : column_budget 3 (z_column previous).
Proof.
  exists (LBirth previous); split; [cbn; lia|].
  cbn [lineage_width lineage_residue].
  rewrite z_column_width, z_column_value.
  exact (z_birth_low_slice previous).
Qed.

Fixpoint tail_columns_step (right_odd : bool)
    (cs cs' : list BinaryColumn) : Prop :=
  match cs, cs' with
  | [], [] => True
  | c::rest, c'::rest' =>
      column_step (match rest with [] => right_odd
                   | d::_ => Nat.odd (column_value d) end) c c' /\
      tail_columns_step right_odd rest rest'
  | _, _ => False
  end.

Theorem tail_columns_budget_step n cs b :
  Forall (column_budget (S n)) cs ->
  exists cs', tail_columns_step b cs cs' /\ Forall (column_budget n) cs'.
Proof.
  intro H; induction H as [|c cs Hc Hcs IH].
  - exists ([] : list BinaryColumn); split; [exact I|constructor].
  - destruct IH as [cs' [Hstep Hbudget]].
    destruct (column_step_exists
      (match cs with [] => b | d::_ => Nat.odd (column_value d) end)
      c (column_safe_lower _ (column_budget_safe _ _ Hc))) as [c' Hcstep].
    exists (c'::cs'); split.
    + split; assumption.
    + constructor; [eapply column_budget_step; eauto|exact Hbudget].
Qed.

Print Assumptions tail_columns_budget_step.
Print Assumptions z_column_budget.

Lemma column_budget_weaken n m c : n <= m -> column_budget m c -> column_budget n c.
Proof.
  intros Hnm [phase [Hfuel Hslice]]. exists phase; split; [lia|exact Hslice].
Qed.

Theorem tail_columns_round_budget k previous cs b :
  1 <= k <= 3 -> Forall (column_budget (4-k)) cs ->
  exists cs', tail_columns_step b cs cs' /\
    Forall (column_budget (4-S k)) (z_column previous :: cs').
Proof.
  intros Hk Hcs.
  replace (4-k) with (S (4-S k)) in Hcs by lia.
  destruct (tail_columns_budget_step _ _ b Hcs) as [cs' [Hstep Hbudget]].
  exists cs'; split; [exact Hstep|].
  constructor; [eapply column_budget_weaken; [|apply z_column_budget]; lia|exact Hbudget].
Qed.

Print Assumptions tail_columns_round_budget.

End FiniteColumns.

Module FiniteRound.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState FiniteColumns.
Require Import ZifyNat Lia Arith ZArith List Bool.
Import ListNotations.
Local Open Scope nat_scope.

(** Last-column values before exceptions 6,7,8,9.
    The signed values include deficits; the display value in the informal
    table is the residue modulo 2^width. *)
Definition phase_width k := 30-k.
Definition phase_value k : Z :=
  match k with
  | 1 => 391468375%Z
  | 2 => (-195734187)%Z
  | 3 => 97867094%Z
  | _ => (-116042411)%Z
  end.
Definition phase_lv k := match k with 1 => 4 | 2 => 1 | 3 => 5 | _ => 3 end.
Definition phase_eff k : Z :=
  ((phase_value k + 2^Z.of_nat (phase_width k) * (Z.of_nat (phase_lv k)-1)) /
    2^Z.of_nat (phase_width k))%Z.

Lemma phase_effective_levels :
  phase_eff 1 = 3%Z /\ phase_eff 2 = (-1)%Z /\
  phase_eff 3 = 4%Z /\ phase_eff 4 = 0%Z.
Proof. vm_compute; repeat split; reflexivity. Qed.

Lemma phase_level_step k :
  1 <= k <= 3 -> phase_eff (S k) = (Z.of_nat k + 1 - phase_eff k)%Z.
Proof.
  intro H; assert (k=1 \/ k=2 \/ k=3) by lia.
  destruct H0 as [E | [E | E]]; subst k; vm_compute; reflexivity.
Qed.

Lemma phase_value_step k :
  1 <= k <= 3 ->
  (phase_value (S k) mod 2^Z.of_nat (phase_width (S k)) =
    2^Z.of_nat (phase_width (S k)) -
      (phase_value k mod 2^Z.of_nat (phase_width k))/2)%Z.
Proof.
  intro H; assert (k=1 \/ k=2 \/ k=3) by lia.
  destruct H0 as [E | [E | E]]; subst k; vm_compute; reflexivity.
Qed.

Lemma phase_window k :
  1 <= k <= 4 ->
  (3 <= phase_value k + 2^Z.of_nat (phase_width k)*2)%Z /\
  (phase_value k <= 2^Z.of_nat (phase_width k)-6)%Z.
Proof.
  intro H; assert (k=1 \/ k=2 \/ k=3 \/ k=4) by lia.
  destruct H0 as [E | [E | [E | E]]]; subst k; vm_compute; split; discriminate.
Qed.

Record finite_round_pre current previous zs last k lv : Prop := {
  fr_stage : 1 <= k <= 4;
  fr_columns : Forall (column_budget (4-k)) zs;
  fr_head_odd : match zs with
                | c::_ => Nat.odd (column_value c) = true
                | [] => Z.odd (sdigits_value last) = true end;
  fr_width :
    2*(columns_width_sum zs + length last)+4 <= half_parameter previous+1 /\
    2*(half_parameter previous+1 + columns_width_sum zs + length last)+4 <=
      half_parameter current+1;
  fr_last_len : length last = phase_width k;
  fr_last_value : sdigits_value last = phase_value k;
  fr_lv : lv = phase_lv k
}.

Lemma finite_pre_safe current previous zs last k lv :
  finite_round_pre current previous zs last k lv -> Forall column_safe zs.
Proof.
  intro H; destruct H as [_ Hcs _ _ _ _ _].
  eapply Forall_impl; [|exact Hcs]. intros c Hc; eapply column_budget_safe; exact Hc.
Qed.

Lemma finite_pre_eff current previous zs last k lv :
  finite_round_pre current previous zs last k lv -> eff_level last lv = phase_eff k.
Proof.
  intro H; destruct H as [_ _ _ _ Hw Hv Hl].
  unfold eff_level, phase_eff; rewrite Hw, Hv, Hl; reflexivity.
Qed.

Lemma finite_pre_nontrigger current previous zs last k lv :
  finite_round_pre current previous zs last k lv -> k <= 3 ->
  ~ tail_triggers k last lv.
Proof.
  intros H Hk.
  pose proof (finite_pre_eff _ _ _ _ _ _ H) as He.
  destruct H as [Hstage _ _ _ _ _ _].
  unfold tail_triggers; rewrite He.
  assert (k=1 \/ k=2 \/ k=3) by lia.
  destruct H as [E | [E | E]]; subst k; vm_compute; congruence.
Qed.

Lemma finite_pre_trigger current previous zs last lv :
  finite_round_pre current previous zs last 4 lv -> tail_triggers 4 last lv.
Proof.
  intro H; pose proof (finite_pre_eff _ _ _ _ _ _ H) as He.
  unfold tail_triggers; rewrite He. vm_compute; discriminate.
Qed.

(** Physical traversal specifications. Their proofs are
    finite_round_proved and finite_trigger_proved below. *)
Definition finite_round_obligation : Prop :=
  forall current previous zs last k lv,
  finite_round_pre current previous zs last k lv -> k <= 3 ->
  exists zs' last' lv',
    post_ca_tail (round_post_unary current previous)
      (round_primary_width current previous) zs last k lv
    -[source_tm]->+
    post_ca_tail
      (round_post_unary (tail_next_index current previous zs last lv) current)
      (round_primary_width (tail_next_index current previous zs last lv) current)
      (z_column previous :: zs') last' (S k) lv' /\
    finite_round_pre (tail_next_index current previous zs last lv) current
      (z_column previous :: zs') last' (S k) lv'.

Definition finite_trigger_obligation : Prop :=
  forall current previous zs last lv,
  finite_round_pre current previous zs last 4 lv ->
  exists c f es e,
    post_ca_tail (round_post_unary current previous)
      (round_primary_width current previous) zs last 4 lv
    -[source_tm]->+
    exception_call_left c f {{{((B, []), R)}}} (full_tail es (S e) 5 *> 0inf) /\
    nested_required es e <= f.

Print Assumptions finite_pre_safe.
Print Assumptions finite_pre_nontrigger.
Print Assumptions finite_pre_trigger.

End FiniteRound.

Module OpeningEarly.
(** The blank opening into the fourth-exception frontier.

    AI assistance: this proof sketch, the scripts and the checks were produced with the help of GPT-6 Astra (OpenAI).
*)
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10.
Require Import Lia Arith NArith List.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Definition early_tail := U^^3 ++ A8 ++ B8^^2 ++ [1;1].
Definition fourth_tail := C8 ++ [1;1] ++ C8 ++ A8^^2 ++ [1;1;1;1].

Lemma opening_D_to_third_done :
  (D;; tape0) -[source_tm]->* exception_done 28 early_tail.
Proof.
  eapply without_counter with (n:=43119).
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma opening_local_hash :
  segRLs source_tm hashes []
    (C8 ++ A8 ++ U ++ A8 ++ B8^^2 ++ [1;1])
    (D8 ++ fourth_tail).
Proof.
  unfold fourth_tail.
  apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.
Qed.

Local Opaque Nat.pow.
Definition opening_after_cd_calls p :=
  initial_u_pair_calls p 1 +
    (2^(p+1) + (2^(p+1) + (2^(p+2)-1))).

Lemma opening_after_cd_side p :
  sideRLs source_tm (hashes^^opening_after_cd_calls p)
    ((A8^^p ++ C8 ++ A8 ++ early_tail) *> 0inf)
    ((B8^^(p+2) ++ fourth_tail) *> 0inf).
Proof.
  pose proof (segRLs_0inf (initial_u_pairs p 1
    (U ++ A8 ++ B8^^2 ++ [1;1]))) as Hfirst.
  pose proof (segRLs_0inf (primary_one_rule (p+1) _ _ opening_local_hash)) as Hbridge.
  pose proof (segRLs_0inf (primary_D_absorb (p+1) fourth_tail)) as Hd.
  replace (S (p+1)) with (p+2) in Hd by lia.
  pose proof (segRLs_0inf (zero_primary_finish_seg (p+2) fourth_tail)) as Hfinish.
  pose proof (sideRLs_trans Hfirst (sideRLs_trans Hbridge
    (sideRLs_trans Hd Hfinish))) as H.
  repeat rewrite <- lpow_add in H.
  unfold opening_after_cd_calls, early_tail.
  applys_eq H; repeat rewrite Str_app_assoc; repeat rewrite <- app_assoc; reflexivity.
Qed.

Definition opening_n4 := 3*2^29-2.

Lemma opening_total_count_general p :
  cd_calls p + opening_after_cd_calls p = 2*(3*2^(p+1)-2)+1.
Proof.
  unfold cd_calls, opening_after_cd_calls.
  cbn [initial_u_pair_calls].
  rewrite !Nat.pow_add_r.
  change (2*(2^p-1) + (2*2^p+0 +
    (2^p*2 + (2^p*2 + (2^p*4-1)))) =
    2*(3*(2^p*2)-2)+1).
  pose proof (Nat.pow_nonzero 2 p ltac:(lia)). nia.
Qed.

Lemma opening_total_count :
  cd_calls 28 + opening_after_cd_calls 28 = 2*opening_n4+1.
Proof. exact (opening_total_count_general 28). Qed.

Theorem opening_D_to_fourth_frontier :
  (D;; tape0) -[source_tm]->*
  ordinary_left (2*opening_n4+1) {{{((B, []), R)}}}
    ((B8^^30 ++ fourth_tail) *> 0inf).
Proof.
  eapply evstep_trans; [exact opening_D_to_third_done|].
  eapply evstep_trans; [apply progress_evstep; apply exception_done_cd; lia|].
  pose proof (sideRLs_concat_1 (opening_after_cd_side 28)
    (left_emit_calls (opening_after_cd_calls 28) (cd_calls 28))) as H.
  rewrite opening_total_count in H.
  exact H.
Qed.

Print Assumptions opening_D_to_third_done.
Print Assumptions opening_local_hash.
Print Assumptions opening_D_to_fourth_frontier.

End OpeningEarly.

Module SignedFrontier.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState.
Require Import ZifyNat Lia Arith Ring ZArith List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Fixpoint sfinish_count (ds : list SDigit) (out : nat) : nat :=
  match ds with
  | [] => out
  | d::rest => 2*sfinish_count rest out +
      match d with SE => 3 | SD => 2 | SA => 1 | SB => 0 end
  end.

Lemma hash_D_finish n :
  segRLs source_tm (hashes^^(2*n+2)) (hashes^^n) D8 B8.
Proof.
  applys_eq (segRLs_trans hash_D (hash_A_finish n)).
  replace (2*n+2) with (1+(2*n+1)) by lia.
  rewrite lpow_add; reflexivity.
Qed.

Theorem sfinish_spec ds out :
  segRLs source_tm (hashes^^sfinish_count ds out) (hashes^^out)
    (sdigits_word ds) (B8^^length ds).
Proof.
  induction ds as [|d ds IH].
  - cbn [sfinish_count sdigits_word lpow length]. apply segRLs_nil.
  - destruct d; cbn [sfinish_count sdigits_word sdigit_word length lpow];
      eapply segRLs_concat; try exact IH.
    + apply hash_E_odd.
    + apply hash_D_finish.
    + apply hash_A_finish.
    + rewrite Nat.add_0_r. apply hash_B_finish.
Qed.

Theorem sfinish_value ds out :
  (Z.of_nat (sfinish_count ds out) + sdigits_value ds + 1 =
    (Z.of_nat out+1)*pow2 (length ds))%Z.
Proof.
  induction ds as [|d ds IH].
  - cbn [sfinish_count sdigits_value length].
    unfold pow2. rewrite Nat.pow_0_r. cbn. ring.
  - destruct d; cbn [sfinish_count sdigits_value sdigit_value length];
      rewrite pow2_succ, Nat2Z.inj_add, Nat2Z.inj_mul; cbn [Z.of_nat]; nia.
Qed.

Lemma tail_level_finish lv : lv <= 5 ->
  sideRLs source_tm (hashes^^(5-lv))
    (y_after lv *> 0inf) ((B8 ++ [1;1]) *> 0inf).
Proof.
  intro H; destruct lv as [|[|[|[|[|[|lv]]]]]]; try lia;
    unfold source_tm, y_after;
    apply BoundedConfig.sideRLs_c_spec with (T:=10000); reflexivity.
Qed.

Definition last_finish_count last lv := sfinish_count last (5-lv).
Lemma last_to_frontier last k lv : lv <= 5 ->
  sideRLs source_tm (hashes^^last_finish_count last lv)
    ((sdigits_word last ++ U^^(2*k+1) ++ y_after lv) *> 0inf)
    ((B8^^length last ++ U^^(2*k+1) ++ B8 ++ [1;1]) *> 0inf).
Proof.
  intro Hlv.
  pose proof (segRLs_concat (sfinish_spec last (5-lv))
    (hashes_U_run (5-lv) (2*k+1))) as Hprefix.
  pose proof (segRLs_sideRLs_concat Hprefix (tail_level_finish lv Hlv)) as H.
  unfold last_finish_count.
  applys_eq H; repeat rewrite Str_app_assoc; reflexivity.
Qed.

Fixpoint columns_with_tail (zs : list BinaryColumn) (tail : list Sym) : list Sym :=
  match zs with [] => tail
  | c::rest => binary_column_word c ++ U^^2 ++ columns_with_tail rest tail end.
Fixpoint all_B_with_tail (zs : list BinaryColumn) (tail : list Sym) : list Sym :=
  match zs with [] => tail
  | c::rest => B8^^column_width c ++ U^^2 ++ all_B_with_tail rest tail end.
Fixpoint columns_finish_count (zs : list BinaryColumn) (out : nat) : nat :=
  match zs with [] => out
  | c::rest => bfinish_count (column_digits c) (columns_finish_count rest out) end.

Lemma columns_finish_tail zs out input output :
  sideRLs source_tm (hashes^^out) (input *> 0inf) (output *> 0inf) ->
  sideRLs source_tm (hashes^^columns_finish_count zs out)
    (columns_with_tail zs input *> 0inf) (all_B_with_tail zs output *> 0inf).
Proof.
  intro Htail; induction zs as [|c zs IH]; [exact Htail|].
  cbn [columns_finish_count columns_with_tail all_B_with_tail].
  pose proof (bfinish_spec (column_digits c) (columns_finish_count zs out)) as Hc.
  rewrite column_length in Hc.
  pose proof (segRLs_concat Hc (hashes_U_run (columns_finish_count zs out) 2)) as Hp.
  applys_eq (segRLs_sideRLs_concat Hp IH);
    unfold binary_column_word, column_width; repeat rewrite Str_app_assoc; reflexivity.
Qed.

Definition tail_finish_count primary zs last lv :=
  bfinish_count (repeat BA primary) (columns_finish_count zs (last_finish_count last lv)).
Definition tail_frontier primary zs (last : list SDigit) k :=
  B8^^primary ++ U^^2 ++
    all_B_with_tail zs (B8^^length last ++ U^^(2*k+1) ++ B8 ++ [1;1]).

Lemma spaced_cons_nonempty a xs : xs <> [] ->
  spaced_words (a::xs) = a ++ U^^2 ++ spaced_words xs.
Proof. destruct xs; [contradiction|reflexivity]. Qed.

Lemma tail_layout_chain primary zs last k lv :
  tail_layout primary zs last k lv =
  A8^^primary ++ U^^2 ++
    columns_with_tail zs (sdigits_word last ++ U^^(2*k+1) ++ y_after lv).
Proof.
  unfold tail_layout.
  induction zs as [|c zs IH].
  - cbn [columns_with_tail map List.app spaced_words].
    repeat rewrite app_nil_r; repeat rewrite <- app_assoc; reflexivity.
  - cbn [columns_with_tail map List.app].
    rewrite spaced_cons_nonempty.
    2: { intro E; apply app_eq_nil in E; destruct E as [_ E]; discriminate. }
    repeat rewrite <- app_assoc in *.
    apply (app_inv_head (A8^^primary)) in IH.
    apply (app_inv_head (U^^2)) in IH.
    rewrite <- IH. repeat rewrite <- app_assoc. reflexivity.
Qed.

Theorem tail_to_frontier primary zs last k lv : lv <= 5 ->
  sideRLs source_tm (hashes^^tail_finish_count primary zs last lv)
    (tail_layout primary zs last k lv *> 0inf)
    (tail_frontier primary zs last k *> 0inf).
Proof.
  intro Hlv.
  pose proof (columns_finish_tail zs _ _ _ (last_to_frontier last k lv Hlv)) as Htail.
  pose proof (bfinish_spec (repeat BA primary)
    (columns_finish_count zs (last_finish_count last lv))) as Hprimary.
  rewrite digits_word_repeat_BA, repeat_length in Hprimary.
  pose proof (segRLs_concat Hprimary
    (hashes_U_run (columns_finish_count zs (last_finish_count last lv)) 2)) as Hp.
  unfold tail_finish_count, tail_frontier; rewrite tail_layout_chain.
  applys_eq (segRLs_sideRLs_concat Hp Htail);
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Print Assumptions sfinish_spec.
Print Assumptions tail_to_frontier.

Lemma pow2_add_local a b : (pow2 (a+b) = pow2 a * pow2 b)%Z.
Proof. unfold pow2. rewrite Nat.pow_add_r, Nat2Z.inj_mul. reflexivity. Qed.

Lemma pow2_Zpow n : pow2 n = (2^Z.of_nat n)%Z.
Proof. unfold pow2. rewrite Nat2Z.inj_pow. reflexivity. Qed.

Lemma bfinish_value_Z ds out :
  (Z.of_nat (bfinish_count ds out) + Z.of_nat (digits_value ds) + 1 =
    (Z.of_nat out+1)*pow2 (length ds))%Z.
Proof.
  pose proof (f_equal Z.of_nat (bfinish_count_value ds out)) as H.
  rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul, !Nat2Z.inj_add in H. exact H.
Qed.

Fixpoint columns_value_Z (zs : list BinaryColumn) : Z :=
  match zs with [] => 0%Z
  | c::rest => (Z.of_nat (column_value c) +
      pow2 (column_width c)*columns_value_Z rest)%Z end.

Lemma zs_value_shift o zs : (zs_value o zs = pow2 o * columns_value_Z zs)%Z.
Proof.
  induction zs as [|c zs IH] in o |- *.
  - cbn [zs_value columns_value_Z]; ring.
  - cbn [zs_value columns_value_Z].
    rewrite <- pow2_Zpow, IH, pow2_add_local. ring.
Qed.

Lemma columns_finish_value zs out :
  (Z.of_nat (columns_finish_count zs out) + columns_value_Z zs + 1 =
    (Z.of_nat out+1)*pow2 (columns_width_sum zs))%Z.
Proof.
  induction zs as [|c zs IH].
  - cbn [columns_finish_count columns_value_Z columns_width_sum columns_widths widths_sum].
    unfold pow2; rewrite Nat.pow_0_r; cbn; ring.
  - cbn [columns_finish_count columns_value_Z].
    rewrite columns_width_sum_cons, pow2_add_local.
    pose proof (bfinish_value_Z (column_digits c) (columns_finish_count zs out)) as H.
    rewrite column_length in H.
    fold (column_width c) in H |- *.
    fold (column_value c) in H.
    nia.
Qed.

(** The next call after the proved frontier is exactly the original T1
    trigger-hash formula, including signed deficits and all separators. *)
Theorem trigger_hash_count primary zs last lv : lv <= 5 ->
  Z.of_nat (S (tail_finish_count primary zs last lv)) = trigger_hash primary zs last lv.
Proof.
  intro Hlv.
  pose proof (bfinish_value_Z (repeat BA primary)
    (columns_finish_count zs (last_finish_count last lv))) as Hp.
  rewrite repeat_length in Hp.
  assert (Hzero : digits_value (repeat BA primary) = 0%nat).
  { clear Hp. induction primary; cbn; [reflexivity|rewrite IHprimary; reflexivity]. }
  rewrite Hzero in Hp.
  fold (tail_finish_count primary zs last lv) in Hp.
  pose proof (columns_finish_value zs (last_finish_count last lv)) as Hc.
  pose proof (sfinish_value last (5-lv)) as Hl.
  fold (last_finish_count last lv) in Hl.
  rewrite Nat2Z.inj_sub in Hl by lia.
  assert (Hl' : (Z.of_nat (last_finish_count last lv)+1 =
    (6-Z.of_nat lv)*pow2 (length last)-sdigits_value last)%Z) by lia.
  assert (Hc' : (Z.of_nat (columns_finish_count zs (last_finish_count last lv))+1 =
    (Z.of_nat (last_finish_count last lv)+1)*pow2 (columns_width_sum zs)-columns_value_Z zs)%Z) by lia.
  rewrite Hl' in Hc'. rewrite Hc' in Hp.
  unfold trigger_hash, tail_V, tail_W.
  rewrite zs_value_shift. repeat rewrite <- pow2_Zpow.
  rewrite !pow2_add_local, Nat2Z.inj_succ.
  nia.
Qed.

Print Assumptions trigger_hash_count.

End SignedFrontier.

Module SignedDecode.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier.
Require Import ZifyNat Lia Arith ZArith NArith List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

(** A binary-sized evaluator for a block of deficit digits. It recurses on
    the block width, never on the number of returning calls. *)
Definition E_digit (n : N) : SDigit :=
  match n with
  | N0 => SE | Npos xH => SD
  | Npos (xO _) => SA | Npos (xI _) => SB
  end.
Definition E_carry (n : N) : N :=
  match n with
  | N0 | Npos xH => N0
  | Npos (xO p) | Npos (xI p) => N.pred (Npos p)
  end.
Fixpoint E_decode (width : nat) (n : N) : list SDigit * N :=
  match width with
  | O => ([], n)
  | S w => let '(ds, out) := E_decode w (E_carry n) in
      (E_digit n :: ds, out)
  end.

Lemma E_digit_spec n :
  segRLs source_tm (hashes^^N.to_nat n) (hashes^^N.to_nat (E_carry n))
    E8 (sdigit_word (E_digit n)).
Proof.
  destruct n as [|[p|p|]]; cbn [E_carry E_digit sdigit_word].
  - apply segRLs_O.
  - replace (N.to_nat (Npos (xI p))) with
      (2*N.to_nat (N.pred (Npos p))+3).
    + apply hash_E_odd.
    + rewrite N2Nat.inj_pred.
      change (2*Nat.pred (Pos.to_nat p)+3 = Pos.to_nat (xI p)).
      rewrite Pos2Nat.inj_xI. pose proof (Pos2Nat.is_pos p). lia.
  - replace (N.to_nat (Npos (xO p))) with
      (2*N.to_nat (N.pred (Npos p))+2).
    + apply hash_E_even.
    + rewrite N2Nat.inj_pred.
      change (2*Nat.pred (Pos.to_nat p)+2 = Pos.to_nat (xO p)).
      rewrite Pos2Nat.inj_xO. pose proof (Pos2Nat.is_pos p). lia.
  - exact hash_E.
Qed.

Theorem E_decode_spec width n :
  segRLs source_tm (hashes^^N.to_nat n) (hashes^^N.to_nat (snd (E_decode width n)))
    (E8^^width) (sdigits_word (fst (E_decode width n))).
Proof.
  induction width as [|w IH] in n |- *.
  - cbn [E_decode fst snd lpow sdigits_word]. apply segRLs_nil.
  - cbn [E_decode]. destruct (E_decode w (E_carry n)) as [ds out] eqn:E.
    cbn [fst snd sdigits_word lpow].
    eapply segRLs_concat; [apply E_digit_spec|].
    specialize (IH (E_carry n)); rewrite E in IH; exact IH.
Qed.

Lemma E_decode_length width n : length (fst (E_decode width n)) = width.
Proof.
  induction width as [|w IH] in n |- *; [reflexivity|].
  cbn [E_decode]. destruct (E_decode w (E_carry n)) as [ds out] eqn:E.
  cbn [fst length]. specialize (IH (E_carry n)); rewrite E in IH; cbn in IH; lia.
Qed.

Print Assumptions E_decode_spec.

Lemma E_digit_value n :
  (Z.of_N n - 2 = sdigit_value (E_digit n) + 2*Z.of_N (E_carry n))%Z.
Proof.
  destruct n as [|[p|p|]]; cbn [E_digit E_carry sdigit_value]; try reflexivity.
  all: rewrite N2Z.inj_pred; cbn [Z.of_N]; lia.
Qed.

Theorem E_decode_value width n :
  (sdigits_value (fst (E_decode width n)) +
    pow2 width * Z.of_N (snd (E_decode width n)) =
    Z.of_N n - 2*(pow2 width-1))%Z.
Proof.
  induction width as [|w IH] in n |- *.
  - change (0 + 1*Z.of_N n = Z.of_N n - 2*(1-1))%Z. ring.
  - cbn [E_decode]. destruct (E_decode w (E_carry n)) as [ds out] eqn:E.
    cbn [fst snd sdigits_value]. rewrite pow2_succ.
    specialize (IH (E_carry n)); rewrite E in IH; cbn [fst snd] in IH.
    pose proof (E_digit_value n). nia.
Qed.

Print Assumptions E_decode_value.

End SignedDecode.

Module OpeningDecode.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier SignedDecode.
Require Import ZifyNat Lia Arith ZArith NArith List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Definition opening_call_base : N := 462424812206%N.
Definition opening_digits : list SDigit := [SA;SA;SA;SA;SB;SB;SA;SB;SA;SB;SA;SB;SA;SB;SA;SB;SA;SB;SA;SB;SA;SB;SA;SB;SA;SB;SA;SB;SA;SB;SA;SB;SB;SB;SA;SB].

Lemma opening_decode_exact :
  E_decode 36 opening_call_base = (opening_digits, 4%N).
Proof. vm_compute; reflexivity. Qed.

Lemma opening_digits_value : sdigits_value opening_digits = 50107951792%Z.
Proof. vm_compute; reflexivity. Qed.

Lemma opening_tail_four :
  sideRLs source_tm (hashes^^4) (A8 *> 0inf) ((A8 ++ [1;1]) *> 0inf).
Proof.
  unfold source_tm. apply BoundedConfig.sideRLs_c_spec with (T:=10000); reflexivity.
Qed.

Lemma opening_decode_base :
  sideRLs source_tm (hashes^^N.to_nat opening_call_base)
    ((E8^^36 ++ U^^3 ++ A8) *> 0inf)
    ((sdigits_word opening_digits ++ U^^3 ++ A8 ++ [1;1]) *> 0inf).
Proof.
  pose proof (E_decode_spec 36 opening_call_base) as H.
  rewrite opening_decode_exact in H; cbn [fst snd] in H.
  pose proof (segRLs_concat H (hashes_U_run 4 3)) as Hp.
  applys_eq (segRLs_sideRLs_concat Hp opening_tail_four);
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Definition opening_decode_calls k :=
  2^k*N.to_nat opening_call_base + 2*(2^k-1).

(** Family (d) at the actual m=30, with arbitrary p=k+2. The primary
    width remains symbolic, including at p=n4>1.6 billion. *)
Theorem opening_decode k :
  sideRLs source_tm (hashes^^opening_decode_calls k)
    ((E8^^(k+36) ++ U^^3 ++ A8) *> 0inf)
    ((A8^^k ++ sdigits_word opening_digits ++ U^^3 ++ A8 ++ [1;1]) *> 0inf).
Proof.
  pose proof (prefix_E_even k (N.to_nat opening_call_base)
    [] [] (N.to_nat opening_call_base) (@segRLs_nil source_tm (hashes^^N.to_nat opening_call_base))) as all_E_prefix.
  rewrite !app_nil_r in all_E_prefix.
  pose proof (segRLs_sideRLs_concat all_E_prefix opening_decode_base) as H.
  unfold opening_decode_calls. rewrite (lpow_add sym k 36 E8).
  applys_eq H; repeat rewrite Str_app_assoc; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma opening_call_base_formula :
  N.to_nat opening_call_base = (1292*2^30+4)/3 + 2.
Proof.
  apply Nat2N.inj.
  rewrite N2Nat.id, !Nat2N.inj_add, Nat2N.inj_div,
    !Nat2N.inj_add, Nat2N.inj_mul, Nat2N.inj_pow.
  vm_compute; reflexivity.
Qed.

Theorem opening_decode_calls_formula k :
  opening_decode_calls k = 2^(k+2)-2 + 2^k*((1292*2^30+4)/3).
Proof.
  unfold opening_decode_calls. rewrite opening_call_base_formula, Nat.pow_add_r.
  change (2^2) with 4.
  pose proof (Nat.pow_nonzero 2 k ltac:(lia)). nia.
Qed.

Print Assumptions opening_decode.
Print Assumptions opening_decode_calls_formula.

End OpeningDecode.

Module OpeningEntry.
(** Entry into the four finite signed-column rounds.

    AI assistance: this proof sketch, the scripts and the checks were produced with the help of GPT-6 Astra (OpenAI).
*)
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState FiniteColumns FiniteRound OpeningEarly OpeningDecode.
Require Import ZifyNat Lia Arith ZArith NArith List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.
Local Opaque Nat.pow.

Definition entry_n5 := opening_decode_calls (opening_n4-2).
Definition entry_current := (entry_n5-6)/2.
Definition entry_previous := (opening_n4-6)/2.
Definition entry_rest := skipn 9 opening_digits.
Definition entry_last := SB::SB::entry_rest.
Definition entry_state := post_ca_tail
  (round_post_unary entry_current entry_previous)
  (round_primary_width entry_current entry_previous) [] entry_last 1 4.

Lemma opening_n4_even_large :
  (exists q, opening_n4=2*q) /\ 64<=opening_n4.
Proof.
  unfold opening_n4.
  assert (Hpow: 32<=2^28).
  { change (2^5<=2^28). apply Nat.pow_le_mono_r; lia. }
  replace 29 with (S 28) by reflexivity. rewrite Nat.pow_succ_r by lia.
  split; [exists (3*2^28-1)|]; nia.
Qed.

Local Opaque opening_n4.

Lemma even_index_half n :
  (exists q, n=2*q /\ 6<=2*q) -> half_parameter ((n-6)/2)=n.
Proof.
  intros [q [Hq Hge]]. rewrite Hq. unfold half_parameter. lia.
Qed.

Lemma entry_previous_half : half_parameter entry_previous=opening_n4.
Proof.
  unfold entry_previous. apply even_index_half.
  destruct opening_n4_even_large as [[q Hq] Hge].
  exists q. split; [exact Hq|]. rewrite <-Hq.
  exact (Nat.le_trans 6 64 opening_n4 ltac:(lia) Hge).
Qed.

Lemma opening_base_even : exists b, N.to_nat opening_call_base=2*b.
Proof.
  exists (N.to_nat 231212406103%N).
  change (N.to_nat 462424812206%N=N.to_nat 2%N*N.to_nat 231212406103%N).
  rewrite <- N2Nat.inj_mul. reflexivity.
Qed.

Lemma opening_decode_even_ge6 k : 2<=k ->
  exists q, opening_decode_calls k=2*q /\ 6<=2*q.
Proof.
  intro Hk; destruct opening_base_even as [b Hb].
  unfold opening_decode_calls. rewrite Hb.
  assert (Hpow:4<=2^k).
  { change (2^2<=2^k). apply Nat.pow_le_mono_r; lia. }
  exists (2^k*b+(2^k-1)). split; nia.
Qed.

Lemma entry_n5_even_ge6 : exists q, entry_n5=2*q /\ 6<=2*q.
Proof.
  unfold entry_n5. apply opening_decode_even_ge6.
  destruct opening_n4_even_large as [_ H]; lia.
Qed.

Local Opaque entry_n5.

Lemma entry_current_half : half_parameter entry_current=entry_n5.
Proof. unfold entry_current. apply even_index_half, entry_n5_even_ge6. Qed.

Local Opaque entry_current entry_previous.

Lemma opening_entry_growth n : 64<=n ->
  2*(n+30)+4 <= opening_decode_calls (n-2)+1.
Proof.
  intro Hn.
  pose proof (pow2_linear_margin (n-8)) as Hpow.
  replace (n-8+5) with (n-3) in Hpow by lia.
  assert (Heq:2^(n-2)=2*2^(n-3)).
  { replace (n-2) with (S (n-3)) by lia.
    rewrite Nat.pow_succ_r by lia. reflexivity. }
  unfold opening_decode_calls. rewrite Heq. nia.
Qed.

Lemma entry_last_facts :
  length entry_last=29 /\ sdigits_value entry_last=391468375%Z /\
  Z.odd (sdigits_value entry_last)=true.
Proof. vm_compute; repeat split; reflexivity. Qed.

Lemma entry_opening_word :
  A8^^(opening_n4-2) ++ sdigits_word opening_digits ++ U^^3 ++ A8 ++ [1;1] =
  A8^^(2*(entry_previous+4)) ++ B8++B8++A8++B8++A8++
    (sdigits_word entry_rest ++ U^^3 ++ A8 ++ [1;1]).
Proof.
  assert (Hsplit:sdigits_word opening_digits =
    A8^^4 ++ B8++B8++A8++B8++A8++sdigits_word entry_rest)
    by reflexivity.
  rewrite Hsplit. repeat rewrite app_assoc.
  rewrite <- lpow_add.
  pose proof entry_previous_half as Hhalf.
  unfold half_parameter in Hhalf.
  replace (opening_n4-2+4) with (2*(entry_previous+4)) by lia.
  reflexivity.
Qed.

Theorem opening_exception_to_entry :
  exception_done entry_n5
    (A8^^(opening_n4-2) ++ sdigits_word opening_digits ++ U^^3 ++ A8 ++ [1;1])
  -[source_tm]->+ entry_state.
Proof.
  rewrite entry_opening_word.
  unfold entry_state, post_ca_tail, tail_layout.
  cbn [map app spaced_words].
  unfold round_post_unary, round_primary_width.
  rewrite entry_current_half.
  pose proof entry_previous_half as Hhalf.
  unfold half_parameter in Hhalf.
  replace (entry_n5+half_parameter entry_previous+6) with
    (entry_n5+2*(entry_previous+4)+4) by (unfold half_parameter; lia).
  pose proof (exception_done_ca entry_n5 (entry_previous+4)
    (sdigits_word entry_rest ++ U^^3 ++ A8 ++ [1;1])
    ltac:(destruct entry_n5_even_ge6 as [q [Hq Hge]]; lia)) as H.
  applys_eq H; cbn [entry_last sdigits_word sdigit_word y_after];
    repeat rewrite app_nil_r; repeat rewrite <- app_assoc; reflexivity.
Qed.

Theorem entry_pre : finite_round_pre
  entry_current entry_previous [] entry_last 1 4.
Proof.
  destruct entry_last_facts as [Hlen [Hval Hodd]].
  constructor.
  - lia.
  - constructor.
  - exact Hodd.
  - rewrite entry_previous_half, entry_current_half.
    replace (columns_width_sum []) with 0%nat by reflexivity. rewrite Hlen.
    destruct opening_n4_even_large as [_ Hge]. split.
    + lia.
    + replace (opening_n4+1+0+29) with (opening_n4+30) by lia.
      exact (opening_entry_growth opening_n4 Hge).
  - exact Hlen.
  - exact Hval.
  - reflexivity.
Qed.

Print Assumptions opening_exception_to_entry.
Print Assumptions entry_pre.

End OpeningEntry.

Module Fossil.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10.
Require Import ZifyNat Lia Arith Ring ZArith String List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

(** The fixed far-end word left by the fossil scan. *)
Definition fossil_tail := C8 ++ [1;1] ++ C8 ++ U ++ [1;1] ++ U.
Definition fossil_start m := C8 ++ A8^^m ++ D8 ++ D8 ++ A8 ++ U ++ E8 ++ A8.

Lemma fossil_scan m :
  segRLs source_tm hashes [] (fossil_start m)
    (D8 ++ C8^^m ++ D8 ++ D8 ++ fossil_tail).
Proof.
  unfold fossil_start, fossil_tail, source_tm.
  ut; esx.
Qed.

Lemma fossil_tail_finish :
  sideRLs source_tm (hashes^^25)
    (fossil_tail *> 0inf) ((B8^^2 ++ U ++ B8 ++ [1;1]) *> 0inf).
Proof.
  unfold fossil_tail, source_tm.
  apply BoundedConfig.sideRLs_c_spec with (T:=10000); reflexivity.
Qed.

Lemma c_sweep_even width pairs rest :
  segRLs source_tm (hashes^^c_sweep_calls width pairs) []
    (A8^^width ++ C8^^(2*pairs) ++ rest)
    (A8^^(width+2*pairs) ++ rest).
Proof.
  induction pairs as [|pairs IH] in width |- *.
  - cbn [c_sweep_calls lpow]. rewrite Nat.add_0_r. apply segRLs_O.
  - cbn [c_sweep_calls].
    pose proof (ca_pair width (C8^^(2*pairs) ++ rest)) as Hpair.
    pose proof (IH (width+2)) as Htail.
    replace (2*S pairs) with (2+2*pairs) by lia; rewrite lpow_add.
    replace (width+2*S pairs) with ((width+2)+2*pairs) by lia.
    repeat rewrite <- app_assoc in Hpair, Htail |- *.
    applys_eq (segRLs_trans Hpair Htail); try rewrite <- lpow_add;
      repeat rewrite <- app_assoc; try reflexivity; f_equal; f_equal; lia.
Qed.

Lemma fossil_tail_lift width :
  sideRLs source_tm (hashes^^(25*2^width + (2^width-1)))
    ((A8^^width ++ fossil_tail) *> 0inf)
    ((B8^^(width+2) ++ U ++ B8 ++ [1;1]) *> 0inf).
Proof.
  pose proof (segRLs_sideRLs_concat (all_A_cycles width 25)
    fossil_tail_finish) as Htail.
  pose proof (segRLs_0inf (zero_primary_finish_seg width
    (B8^^2 ++ U ++ B8 ++ [1;1]))) as Hlow.
  repeat rewrite <- Str_app_assoc in Htail.
  applys_eq (sideRLs_trans Htail Hlow).
  - rewrite lpow_add; reflexivity.
  - rewrite lpow_add; repeat rewrite <- app_assoc; reflexivity.
Qed.

Definition fossil_calls p k :=
  2^p + 2^p + c_sweep_calls (p+1) k +
  2^(p+1+2*k) + 2^(p+2+2*k) +
  (25*2^(p+3+2*k) + (2^(p+3+2*k)-1)).

Theorem fossil_run p k :
  sideRLs source_tm (hashes^^fossil_calls p k)
    ((A8^^p ++ fossil_start (2*k)) *> 0inf)
    ((B8^^(p+2*k+5) ++ U ++ B8 ++ [1;1]) *> 0inf).
Proof.
  pose proof (segRLs_0inf (primary_one_rule p _ _ (fossil_scan (2*k)))) as Hscan.
  pose proof (segRLs_0inf (primary_D_absorb p
    (C8^^(2*k) ++ D8 ++ D8 ++ fossil_tail))) as Hd.
  pose proof (segRLs_0inf (c_sweep_even (p+1) k
    (D8 ++ D8 ++ fossil_tail))) as Hsweep.
  pose proof (segRLs_0inf (primary_D_absorb (p+1+2*k)
    (D8 ++ fossil_tail))) as Hd1.
  pose proof (segRLs_0inf (primary_D_absorb (p+2+2*k)
    fossil_tail)) as Hd2.
  pose proof (fossil_tail_lift (p+3+2*k)) as Htail.
  replace (S p) with (p+1) in Hd by lia.
  replace (S (p+1+2*k)) with (p+2+2*k) in Hd1 by lia.
  replace (S (p+2+2*k)) with (p+3+2*k) in Hd2 by lia.
  replace (p+3+2*k+2) with (p+2*k+5) in Htail by lia.
  pose proof (sideRLs_trans Hscan (sideRLs_trans Hd
    (sideRLs_trans Hsweep (sideRLs_trans Hd1
      (sideRLs_trans Hd2 Htail))))) as H.
  repeat rewrite <- lpow_add in H.
  unfold fossil_calls.
  applys_eq H; f_equal; lia.
Qed.

Print Assumptions fossil_run.

Lemma geom4n_power k : 3 * geom4n k + 1 = 2^(2*k).
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite geom4n_succ.
  replace (2*S k) with (2+2*k) by lia.
  rewrite Nat.pow_add_r. change (2^2) with 4. nia.
Qed.

Lemma fossil_count_formula n k :
  fossil_calls (S n) k = 2^n * ((1292*2^(2*k)+4)/3) - 1.
Proof.
  pose proof (geom4n_power k) as Hg.
  assert (Hdiv : (1292*2^(2*k)+4)/3 = 1292*geom4n k+432).
  { replace (1292*2^(2*k)+4) with ((1292*geom4n k+432)*3) by nia.
    rewrite Nat.div_mul by lia; reflexivity. }
  rewrite Hdiv.
  unfold fossil_calls; rewrite c_sweep_calls_formula.
  rewrite !Nat.pow_add_r, Nat.pow_succ_r by lia.
  change (2^1) with 2; change (2^2) with 4; change (2^3) with 8.
  pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
  pose proof (Nat.pow_nonzero 2 (2*k) ltac:(lia)).
  nia.
Qed.

(** Family (b): even m=2k, positive primary width p=S n. *)
Theorem fossil_run_closed n k :
  sideRLs source_tm (hashes^^(2^n * ((1292*2^(2*k)+4)/3) - 1))
    ((A8^^(S n) ++ fossil_start (2*k)) *> 0inf)
    ((B8^^(S n+2*k+5) ++ U ++ B8 ++ [1;1]) *> 0inf).
Proof.
  rewrite <- fossil_count_formula. apply fossil_run.
Qed.

Print Assumptions fossil_run_closed.

End Fossil.

Module RoundCaller.
(** Complete and partial exception calls with a live right-hand tail.

    AI assistance: this proof sketch, the scripts and the checks were produced with the help of GPT-6 Astra (OpenAI).
*)
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit.
Require Import Lia Arith List.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Definition exception_done_side n (output : side) : Q * tape :=
  common_left_wall {{{((B, []), R)}}}
    ((C8 ++ A8 ++ U^^(2*n)) *> output).

Lemma exception_exit_side k output :
  exception_call_left 0 k {{{((F, []), L)}}} output -[source_tm]->+
  exception_done_side (S k) output.
Proof.
  unfold exception_call_left, exception_done_side, common_left_wall, source_tm.
  induction k as [|k IH].
  - ut; esx.
  - ut; esx.
Qed.

Lemma exception_exit_zero_side output :
  exception_pre_left 0 {{{((F, []), L)}}} output -[source_tm]->+
  exception_done_side 0 output.
Proof.
  unfold exception_pre_left, exception_done_side, common_left_wall, source_tm.
  ut; esx.
Qed.

Lemma exception_calls_side k input output :
  sideRLs source_tm (hashes^^(S k)) input output ->
  exception_call_left k 0 {{{((B, []), R)}}} input -[source_tm]->+
  exception_call_left 0 k {{{((F, []), L)}}} output.
Proof.
  intro Hright.
  eapply sideRLs_concat.
  - applys_eq (exception_relaunches k 0); flia.
  - applys_eq Hright.
    unfold left_hash; cbn.
    pose proof (lrcons_lpow1 (B, []) (F, []) (S k) ltac:(lia)) as Hl.
    replace (S k - 1) with k in Hl by lia.
    exact Hl.
Qed.

Theorem exception_pre_from_side n input output :
  sideRLs source_tm (hashes^^n) input output ->
  exception_pre_left n {{{((F, []), L)}}} input -[source_tm]->+
  exception_done_side n output.
Proof.
  destruct n as [|k].
  - cbn [lpow]; intro Hright; inverts Hright; apply exception_exit_zero_side.
  - intro Hright; eapply progress_trans;
      [apply exception_launch_progress|].
    eapply progress_trans; [exact (exception_calls_side k input output Hright)|
      apply exception_exit_side].
Qed.

Corollary exception_pre_from_side_word n input output :
  sideRLs source_tm (hashes^^n) (input *> 0inf) (output *> 0inf) ->
  exception_pre_left n {{{((F, []), L)}}} (input *> 0inf) -[source_tm]->+
  exception_done n output.
Proof.
  intro Hright.
  applys_eq (exception_pre_from_side n _ _ Hright).
  unfold exception_done_side, exception_done.
  repeat rewrite Str_app_assoc; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma ordinary_raw_pre_left n :
  [1;0;1] *> ordinary_left (2*n+1) = exception_pre_left n.
Proof.
  unfold ordinary_left, common_left_wall.
  change ([1;0;1] *> X4^^(2*n+1) *> Q8 *> 0inf = exception_pre_left n).
  exact (exception_pre_left_direct n).
Qed.

Lemma ordinary_raw_pre_left_count tally n :
  tally = 2*n+1 -> [1;0;1] *> ordinary_left tally = exception_pre_left n.
Proof. intro H; rewrite H; apply ordinary_raw_pre_left. Qed.

Lemma exception_relaunches_partial h r finished :
  sideRLs (flip source_tm) ([left_hash]^^h)
    (exception_call_left (h+r) finished)
    (exception_call_left r (finished+h)).
Proof.
  induction h as [|h IH] in finished |- *.
  - cbn [lpow Nat.add]. replace (finished+0) with finished by lia.
    constructor.
  - cbn [lpow]; eapply sideRLs_trans.
    + apply exception_relaunch_side.
    + applys_eq (IH (S finished)); flia.
Qed.

Theorem exception_partial_side h r finished input output :
  sideRLs source_tm (hashes^^h) input output ->
  exception_call_left (h+r) finished {{{((B, []), R)}}} input -[source_tm]->*
  exception_call_left r (finished+h) {{{((B, []), R)}}} output.
Proof.
  intro Hright.
  exact (sideRLs_concat_1 Hright (exception_relaunches_partial h r finished)).
Qed.

(** Exactly h calls return; the next call is poised to start, with r
    additional calls after it. Total original budget: h+1+r. *)
Theorem exception_launch_partial_side h r input output :
  sideRLs source_tm (hashes^^h) input output ->
  exception_pre_left (S (h+r)) {{{((F, []), L)}}} input -[source_tm]->+
  exception_call_left r h {{{((B, []), R)}}} output.
Proof.
  intro Hright.
  eapply progress_evstep_trans.
  - exact (exception_launch_progress (h+r) input).
  - exact (exception_partial_side h r 0 input output Hright).
Qed.

Print Assumptions exception_pre_from_side.
Print Assumptions exception_pre_from_side_word.
Print Assumptions ordinary_raw_pre_left.
Print Assumptions exception_partial_side.
Print Assumptions exception_launch_partial_side.

End RoundCaller.

Module OpeningLate.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier SignedDecode OpeningEarly OpeningDecode Fossil RoundCaller.
Require Import ZifyNat Lia Arith ZArith NArith List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.
Local Opaque Nat.pow.

Definition fourth_output := A8^^29 ++ D8 ++ D8 ++ A8 ++ U ++ E8 ++ A8.
Definition fourth_raw_output := E8^^30 ++ D8 ++ A8 ++ U ++ E8 ++ A8.

Lemma fourth_raw l :
  l {{{((B, []), R)}}} ((B8^^30 ++ fourth_tail) *> 0inf) -[source_tm]->+
  ([1;0;1] *> l) {{{((F, []), L)}}} (fourth_raw_output *> 0inf).
Proof.
  unfold source_tm, fourth_tail, fourth_raw_output.
  eapply multistep_progress with (n:=1079); apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma n4_binary : opening_n4 = N.to_nat 1610612734%N.
Proof.
  unfold opening_n4. apply Nat2N.inj.
  rewrite Nat2N.inj_sub, Nat2N.inj_mul, Nat2N.inj_pow, N2Nat.id.
  vm_compute; reflexivity.
Qed.

Lemma n4_large : 10 <= opening_n4.
Proof. rewrite n4_binary. apply Nat2Z.inj_le. rewrite N_nat_Z. vm_compute; discriminate. Qed.

Opaque opening_n4.

Lemma fourth_decode :
  segRLs source_tm (hashes^^opening_n4) [] fourth_raw_output fourth_output.
Proof.
  pose proof (E_decode_spec 30 1610612734%N) as H.
  assert (E: E_decode 30 1610612734%N = (repeat SA 29 ++ [SD], 0%N))
    by (vm_compute; reflexivity).
  rewrite E in H; cbn [fst snd] in H.
  rewrite n4_binary.
  pose proof (segRLs_concat H (segRLs_O source_tm (D8++A8++U++E8++A8))) as Hfull.
  exact Hfull.
Qed.

Theorem fourth_frontier_to_done :
  ordinary_left (2*opening_n4+1) {{{((B, []), R)}}}
    ((B8^^30 ++ fourth_tail) *> 0inf) -[source_tm]->+
  exception_done opening_n4 fourth_output.
Proof.
  eapply progress_trans.
  - apply fourth_raw.
  - rewrite ordinary_raw_pre_left. apply exception_pre_from_seg, fourth_decode.
Qed.

Lemma fourth_cd_to_fossil :
  exception_done opening_n4 fourth_output -[source_tm]->+
  ordinary_left (cd_calls opening_n4) {{{((B, []), R)}}}
    ((A8^^opening_n4 ++ fossil_start 30) *> 0inf).
Proof.
  assert (W: forall n, cd_output n ++ fourth_output = A8^^n ++ fossil_start 30).
  { intro n. unfold cd_output, fourth_output, fossil_start.
    repeat rewrite <- app_assoc. reflexivity. }
  pose proof (exception_done_cd opening_n4 fourth_output ltac:(pose proof n4_large; lia)) as H.
  unfold after_cd in H. rewrite W in H.
  exact H.
Qed.

Lemma fossil_calls_positive_formula p k : 1 <= p ->
  fossil_calls p k = 2^(p-1)*((1292*2^(2*k)+4)/3)-1.
Proof.
  destruct p as [|p]; [lia|]. intro Hp.
  replace (S p-1) with p by lia. apply fossil_count_formula.
Qed.

Lemma fifth_total_tally_generic n : 2 <= n ->
  cd_calls n + fossil_calls n 15 = 2*opening_decode_calls (n-2)+1.
Proof.
  intro Hn.
  rewrite cd_calls_formula by lia.
  rewrite fossil_calls_positive_formula by lia.
  rewrite opening_decode_calls_formula.
  replace (n-2+2) with n by lia.
  change (2*15)%nat with 30%nat.
  assert (H1:2^n=4*2^(n-2)).
  { replace n with (2+(n-2)) at 1 by lia.
    rewrite Nat.pow_add_r. reflexivity. }
  assert (H2:2^(n-1)=2*2^(n-2)).
  { replace (n-1) with (S (n-2)) by lia.
    rewrite Nat.pow_succ_r by lia; reflexivity. }
  rewrite Nat.pow_add_r. change (2^1)%nat with 2%nat.
  rewrite H1, H2.
  pose proof (Nat.pow_nonzero 2 (n-2) ltac:(lia)).
  assert (HQ:1<=(1292*2^30+4)/3).
  { apply Nat2Z.inj_le.
    rewrite Nat2Z.inj_div, Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_pow.
    vm_compute; discriminate. }
  nia.
Qed.

Lemma fifth_total_tally :
  cd_calls opening_n4 + fossil_calls opening_n4 15 =
    2*opening_decode_calls (opening_n4-2)+1.
Proof. apply fifth_total_tally_generic. pose proof n4_large; lia. Qed.

Definition fifth_output := A8^^(opening_n4-2) ++ sdigits_word opening_digits ++ U^^3 ++ A8 ++ [1;1].

Theorem fossil_to_fifth_frontier :
  ordinary_left (cd_calls opening_n4) {{{((B, []), R)}}}
    ((A8^^opening_n4 ++ fossil_start 30) *> 0inf) -[source_tm]->*
  ordinary_left (2*opening_decode_calls (opening_n4-2)+1) {{{((B, []), R)}}}
    ((B8^^(opening_n4+35) ++ U ++ B8 ++ [1;1]) *> 0inf).
Proof.
  pose proof (sideRLs_concat_1 (fossil_run opening_n4 15)
    (left_emit_calls (fossil_calls opening_n4 15) (cd_calls opening_n4))) as H.
  rewrite fifth_total_tally in H.
  replace (opening_n4+2*15+5) with (opening_n4+35) in H by lia.
  exact H.
Qed.

Lemma fifth_frontier_to_done_generic n : 2 <= n ->
  ordinary_left (2*opening_decode_calls (n-2)+1) {{{((B, []), R)}}}
    ((B8^^(n+35) ++ U ++ B8 ++ [1;1]) *> 0inf) -[source_tm]->+
  exception_done (opening_decode_calls (n-2)) (A8^^(n-2) ++ sdigits_word opening_digits ++ U^^3 ++ A8 ++ [1;1]).
Proof.
  intro Hn.
  eapply progress_trans.
  - applys_eq (raw_tail_column 0 (n+34)
      (ordinary_left (2*opening_decode_calls (n-2)+1)) ltac:(lia)).
    unfold tail_word. replace (S (n+34)) with (n+35) by lia.
    cbn [lpow]; repeat rewrite <- app_assoc; reflexivity.
  - rewrite ordinary_raw_pre_left. apply exception_pre_from_side_word.
    pose proof (opening_decode (n-2)) as H.
    replace (n-2+36) with (n+34) in H by lia.
    exact H.
Qed.

Theorem fifth_frontier_to_done :
  ordinary_left (2*opening_decode_calls (opening_n4-2)+1) {{{((B, []), R)}}}
    ((B8^^(opening_n4+35) ++ U ++ B8 ++ [1;1]) *> 0inf) -[source_tm]->+
  exception_done (opening_decode_calls (opening_n4-2)) fifth_output.
Proof.
  exact (fifth_frontier_to_done_generic opening_n4 ltac:(pose proof n4_large; lia)).
Qed.

Theorem opening_D_to_fifth_done :
  (D;; tape0) -[source_tm]->*
  exception_done (opening_decode_calls (opening_n4-2)) fifth_output.
Proof.
  eapply evstep_trans; [exact opening_D_to_fourth_frontier|].
  apply progress_evstep.
  eapply progress_trans; [exact fourth_frontier_to_done|].
  eapply progress_trans; [exact fourth_cd_to_fossil|].
  eapply evstep_progress_trans; [exact fossil_to_fifth_frontier|exact fifth_frontier_to_done].
Qed.

Print Assumptions opening_D_to_fifth_done.

End OpeningLate.

Module RoundDecode.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier FiniteColumns.
Require Import ZifyNat Lia Arith ZArith NArith List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Definition decode_budget r := ceil_half r - 2.

Lemma column_decode_budget c c' r :
  4 <= r -> column_step (Nat.odd r) c c' ->
  column_required (decode_budget r) c' =
    decode_budget (r*2^(column_width c)-column_value c).
Proof.
  intros Hr [He Hv].
  pose proof (binary_column_value_bound c) as Hbound.
  unfold column_required, column_next_value, column_width, column_value in *.
  rewrite He, Hv.
  unfold decode_budget.
  rewrite (ceil_half_scaled_sub r (S (column_e c)) (digits_value (column_digits c))) by lia.
  replace (S (column_e c)-1) with (column_e c) by lia.
  rewrite Nat.pow_succ_r in Hbound |- * by lia.
  set (b:=2^(column_e c)) in *.
  assert (Hb: 1<=b) by (unfold b; apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  assert (Hvhalf: digits_value (column_digits c)/2 < b) by
    (apply Nat.Div0.div_lt_upper_bound; lia).
  clearbody b.
  destruct (Nat.odd r) eqn:Hodd.
  - destruct (odd_true_witness _ Hodd) as [q ->].
    rewrite ceil_half_odd. nia.
  - assert (Heven: Nat.even r = true) by (rewrite <- Nat.negb_odd, Hodd; reflexivity).
    apply Nat.even_spec in Heven; destruct Heven as [q ->].
    replace (ceil_half (2*q)) with q by (unfold ceil_half; flia).
    nia.
Qed.

Print Assumptions column_decode_budget.

Fixpoint right_remaining (cs : list BinaryColumn) (r : nat) : nat :=
  match cs with
  | [] => r
  | c::rest => right_remaining rest r * 2^(column_width c) - column_value c
  end.
Fixpoint columns_input_count (cs : list BinaryColumn) (out : nat) : nat :=
  match cs with
  | [] => out
  | c::rest => column_required (columns_input_count rest out) c
  end.

Lemma right_remaining_lower cs r : 1 <= r -> r <= right_remaining cs r.
Proof.
  intro Hr; induction cs as [|c cs IH]; [reflexivity|].
  cbn [right_remaining].
  pose proof (binary_column_value_bound c) as Hv.
  fold (column_width c) (column_value c) in Hv.
  assert (Hpow: 2 <= 2^(column_width c)).
  { unfold column_width. rewrite Nat.pow_succ_r by lia.
    pose proof (Nat.pow_nonzero 2 (column_e c) ltac:(lia)). nia. }
  nia.
Qed.

Lemma right_remaining_head_parity c cs r : 1 <= r ->
  Nat.odd (right_remaining (c::cs) r) = Nat.odd (column_value c).
Proof.
  intro Hr.
  pose proof (right_remaining_lower cs r Hr) as Hlower.
  pose proof (binary_column_value_bound c) as Hv.
  fold (column_width c) (column_value c) in Hv.
  assert (Heq: right_remaining (c::cs) r + column_value c =
    right_remaining cs r * 2^(column_width c)).
  { cbn [right_remaining]. nia. }
  apply (f_equal Nat.odd) in Heq.
  rewrite Nat.odd_add, Nat.odd_mul in Heq.
  unfold column_width in Heq. rewrite pow2_S_odd_false, andb_false_r in Heq.
  exact (xorb_eq _ _ Heq).
Qed.

Theorem columns_decode_budget cs cs' r :
  4 <= r -> tail_columns_step (Nat.odd r) cs cs' ->
  columns_input_count cs' (decode_budget r) = decode_budget (right_remaining cs r).
Proof.
  intro Hr; induction cs as [|c cs IH] in cs' |- *.
  - destruct cs'; cbn [tail_columns_step]; [reflexivity|contradiction].
  - destruct cs' as [|c' cs']; [cbn [tail_columns_step]; contradiction|].
    cbn [tail_columns_step]. intros [Hc Hrest].
    cbn [columns_input_count right_remaining].
    rewrite (IH cs' Hrest).
    apply column_decode_budget.
    + pose proof (right_remaining_lower cs r ltac:(lia)); lia.
    + destruct cs as [|d rest]; [exact Hc|].
      rewrite (right_remaining_head_parity d rest r ltac:(lia)). exact Hc.
Qed.

Lemma right_remaining_finish cs last lv :
  right_remaining cs (S (last_finish_count last lv)) =
    S (columns_finish_count cs (last_finish_count last lv)).
Proof.
  induction cs as [|c cs IH]; [reflexivity|].
  cbn [right_remaining columns_finish_count]. rewrite IH.
  pose proof (bfinish_count_value (column_digits c)
    (columns_finish_count cs (last_finish_count last lv))) as H.
  rewrite column_length in H. fold (column_value c) (column_width c) in H.
  lia.
Qed.

Print Assumptions columns_decode_budget.
Print Assumptions right_remaining_finish.

Fixpoint mixed_with_tail (cs : list BinaryColumn) (tail : list sym) : list sym :=
  match cs with
  | [] => tail
  | c::rest => mixed_column_word c ++ U^^2 ++ mixed_with_tail rest tail
  end.

Theorem mixed_with_tail_spec cs out input output :
  sideRLs source_tm (hashes^^out) (input *> 0inf) (output *> 0inf) ->
  sideRLs source_tm (hashes^^columns_input_count cs out)
    (mixed_with_tail cs input *> 0inf) (columns_with_tail cs output *> 0inf).
Proof.
  intro H; induction cs as [|c cs IH]; [exact H|].
  cbn [columns_input_count mixed_with_tail columns_with_tail].
  pose proof (segRLs_concat (mixed_column_spec c (columns_input_count cs out))
    (hashes_U_run (columns_input_count cs out) 2)) as Hp.
  applys_eq (segRLs_sideRLs_concat Hp IH);
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Lemma mixed_with_tail_same_width b cs cs' input :
  tail_columns_step b cs cs' -> mixed_with_tail cs input = mixed_with_tail cs' input.
Proof.
  induction cs as [|c cs IH] in cs' |- *; destruct cs' as [|c' cs'];
    cbn [tail_columns_step]; try contradiction; [reflexivity|].
  intros [[He Hv] Hrest]. cbn [mixed_with_tail].
  assert (Hword: mixed_column_word c = mixed_column_word c').
  { unfold mixed_column_word; rewrite He; reflexivity. }
  rewrite Hword, (IH cs' Hrest). reflexivity.
Qed.

Theorem tail_columns_decode cs cs' r input output :
  4 <= r -> tail_columns_step (Nat.odd r) cs cs' ->
  sideRLs source_tm (hashes^^decode_budget r) (input *> 0inf) (output *> 0inf) ->
  sideRLs source_tm (hashes^^decode_budget (right_remaining cs r))
    (mixed_with_tail cs input *> 0inf) (columns_with_tail cs' output *> 0inf).
Proof.
  intros Hr Hstep Htail.
  rewrite <- (columns_decode_budget cs cs' r Hr Hstep).
  rewrite (mixed_with_tail_same_width _ _ _ input Hstep).
  exact (mixed_with_tail_spec cs' _ _ _ Htail).
Qed.

Print Assumptions tail_columns_decode.

Lemma post_unary_even current previous :
  round_post_unary current previous = 2*(round_post_unary current previous/2).
Proof.
  rewrite round_post_unary_formula at 1.
  rewrite round_post_unary_half_formula.
  set (h := half_parameter current).
  set (body := 1+geom4n (previous+4)+2^(2*(previous+4)+1)).
  replace (h+2) with (S (h+1)) by lia.
  rewrite Nat.pow_succ_r by lia.
  assert (Hbase : 1 <= 2^(h+1)*body).
  { assert (Hpow : 1 <= 2^(h+1)) by
      (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
    unfold body; nia. }
  clearbody h body; nia.
Qed.

Theorem primary_decode_tally current previous r :
  4 <= r -> Nat.odd r = true ->
  round_post_unary current previous + (r*2^(round_primary_width current previous)-1) =
    2*column_required (decode_budget r) (round_outer_column current previous)+1.
Proof.
  intros Hr Hodd.
  pose proof (round_unary_decodes_outer current previous) as Hv.
  pose proof (post_unary_even current previous) as Hu.
  pose proof (round_primary_width_positive current previous) as HP.
  unfold column_required, round_outer_column; cbn [column_e column_digits].
  replace (S (round_primary_width current previous-1)) with
    (round_primary_width current previous) by lia.
  set (P:=round_primary_width current previous) in *.
  assert (Hpow: 2^P = 2*2^(P-1)).
  { replace P with (S (P-1)) at 1 by lia. rewrite Nat.pow_succ_r by lia; reflexivity. }
  assert (Hb: 1<=2^(P-1)) by
    (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  destruct (odd_true_witness _ Hodd) as [q ->].
  unfold decode_budget; rewrite ceil_half_odd, Hpow.
  nia.
Qed.

Print Assumptions primary_decode_tally.

End RoundDecode.

Module TailCases.
(** Exact returning signed-column decodes and the final pre-trigger frontier.

    AI assistance: this proof sketch, the scripts and the checks were
    produced with the help of GPT-6 Astra (OpenAI).
*)
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier SignedDecode.
Require Import Lia ZArith NArith List.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Definition decoded_last7 := fst (E_decode 28 341136723%N).
Definition decoded_last8 := fst (E_decode 27 768955732%N).
Definition decoded_last9 := fst (E_decode 26 18175315%N).

Lemma decode_last7 : E_decode 28 341136723%N = (decoded_last7, 0%N).
Proof. unfold decoded_last7; vm_compute; reflexivity. Qed.
Lemma decode_last8 : E_decode 27 768955732%N = (decoded_last8, 3%N).
Proof. unfold decoded_last8; vm_compute; reflexivity. Qed.
Lemma decode_last9 : E_decode 26 18175315%N = (decoded_last9, 0%N).
Proof. unfold decoded_last9; vm_compute; reflexivity. Qed.
Lemma decode_trigger_frontier :
  E_decode 25 134217725%N = (repeat SB 25, 1%N).
Proof. vm_compute; reflexivity. Qed.

Theorem decoded_last_checkpoints :
  length decoded_last7 = 28 /\ sdigits_value decoded_last7 = (-195734187)%Z /\
  length decoded_last8 = 27 /\ sdigits_value decoded_last8 = 97867094%Z /\
  length decoded_last9 = 26 /\ sdigits_value decoded_last9 = (-116042411)%Z.
Proof. vm_compute; repeat split; reflexivity. Qed.

Lemma E_decode_tail_run width calls ds out k lv :
  E_decode width calls = (ds, out) ->
  sideRLs source_tm (hashes^^N.to_nat out)
    (y_after k *> 0inf) (y_after lv *> 0inf) ->
  sideRLs source_tm (hashes^^N.to_nat calls)
    ((E8^^width ++ U^^(2*k+3) ++ y_after k) *> 0inf)
    ((sdigits_word ds ++ U^^(2*k+3) ++ y_after lv) *> 0inf).
Proof.
  intros Hdecode Htail.
  pose proof (E_decode_spec width calls) as Hdigits.
  rewrite Hdecode in Hdigits; cbn [fst snd] in Hdigits.
  pose proof (segRLs_concat Hdigits
    (hashes_U_run (N.to_nat out) (2*k+3))) as Hprefix.
  applys_eq (segRLs_sideRLs_concat Hprefix Htail);
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Theorem last_case6_return :
  sideRLs source_tm (hashes^^N.to_nat 341136723%N)
    ((E8^^28 ++ U^^5 ++ y_after 1) *> 0inf)
    ((sdigits_word decoded_last7 ++ U^^5 ++ y_after 1) *> 0inf).
Proof.
  apply (E_decode_tail_run 28 341136723%N decoded_last7 0%N 1 1 decode_last7).
  exact (sideRLseq_O source_tm (y_after 1 *> 0inf)).
Qed.

Theorem last_case7_return :
  sideRLs source_tm (hashes^^N.to_nat 768955732%N)
    ((E8^^27 ++ U^^7 ++ y_after 2) *> 0inf)
    ((sdigits_word decoded_last8 ++ U^^7 ++ y_after 5) *> 0inf).
Proof.
  apply (E_decode_tail_run 27 768955732%N decoded_last8 3%N 2 5 decode_last8).
  exact (tail_level_finish 2 ltac:(lia)).
Qed.

Theorem last_case8_return :
  sideRLs source_tm (hashes^^N.to_nat 18175315%N)
    ((E8^^26 ++ U^^9 ++ y_after 3) *> 0inf)
    ((sdigits_word decoded_last9 ++ U^^9 ++ y_after 3) *> 0inf).
Proof.
  apply (E_decode_tail_run 26 18175315%N decoded_last9 0%N 3 3 decode_last9).
  exact (sideRLseq_O source_tm (y_after 3 *> 0inf)).
Qed.

Theorem last_case9_frontier :
  sideRLs source_tm (hashes^^N.to_nat 134217725%N)
    ((E8^^25 ++ U^^11 ++ y_after 4) *> 0inf)
    ((B8^^25 ++ U^^11 ++ y_after 5) *> 0inf).
Proof.
  change (sideRLs source_tm (hashes^^N.to_nat 134217725%N)
    ((E8^^25 ++ U^^(2*4+3) ++ y_after 4) *> 0inf)
    ((sdigits_word (repeat SB 25) ++ U^^(2*4+3) ++ y_after 5) *> 0inf)).
  apply (E_decode_tail_run 25 134217725%N (repeat SB 25) 1%N 4 5
    decode_trigger_frontier).
  exact (tail_level_finish 4 ltac:(lia)).
Qed.

Print Assumptions decoded_last_checkpoints.
Print Assumptions last_case6_return.
Print Assumptions last_case7_return.
Print Assumptions last_case8_return.
Print Assumptions last_case9_frontier.

End TailCases.

Module FiniteDecode.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier SignedDecode FiniteColumns FiniteRound RoundDecode TailCases.
Require Import ZifyNat Lia Arith ZArith NArith List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.
Local Open Scope nat_scope.

Definition phase_R (k : nat) : N :=
  match k with
  | 1%nat => 682273449%N | 2%nat => 1537911467%N
  | 3%nat => 36350634%N | _ => 317369003%N
  end.

Lemma phase_R_value k : 1 <= k <= 4 ->
  ((6-Z.of_nat (phase_lv k))*pow2 (phase_width k)-phase_value k =
    Z.of_N (phase_R k))%Z.
Proof.
  intro H. rewrite pow2_Zpow.
  assert (k=1 \/ k=2 \/ k=3 \/ k=4) by lia.
  destruct H0 as [E|[E|[E|E]]]; subst k; vm_compute; reflexivity.
Qed.

Theorem finite_last_R current previous zs last k lv :
  finite_round_pre current previous zs last k lv ->
  S (last_finish_count last lv) = N.to_nat (phase_R k).
Proof.
  intros [Hstage Hcols Hodd Hwidth Hlen Hvalue Hlv].
  assert (Hlvbound: lv<=5).
  { rewrite Hlv; unfold phase_lv. destruct k as [|[|[|[|k]]]]; lia. }
  pose proof (sfinish_value last (5-lv)) as H.
  fold (last_finish_count last lv) in H.
  rewrite Nat2Z.inj_sub in H by lia.
  apply Nat2Z.inj. rewrite Nat2Z.inj_succ, N_nat_Z.
  rewrite Hlen, Hvalue, Hlv in H.
  rewrite Hlv.
  pose proof (phase_R_value k Hstage). nia.
Qed.

Lemma phase_R_large k : (4 <= N.to_nat (phase_R k))%nat.
Proof.
  apply Nat2Z.inj_le. rewrite N_nat_Z.
  destruct k as [|[|[|[|k]]]]; vm_compute; discriminate.
Qed.

Definition next_last k :=
  match k with 1%nat => decoded_last7 | 2%nat => decoded_last8 | _ => decoded_last9 end.

Lemma phase_decode_budget k : 1 <= k <= 3 ->
  decode_budget (N.to_nat (phase_R k)) =
    N.to_nat (match k with 1%nat => 341136723%N | 2%nat => 768955732%N | _ => 18175315%N end).
Proof.
  intro H; unfold decode_budget, ceil_half.
  apply Nat2N.inj.
  rewrite Nat2N.inj_sub, Nat2N.inj_div, Nat2N.inj_add, !N2Nat.id.
  assert (k=1 \/ k=2 \/ k=3) by lia.
  destruct H0 as [E|[E|E]]; subst k; vm_compute; reflexivity.
Qed.

Theorem finite_last_decode k : 1 <= k <= 3 ->
  sideRLs source_tm (hashes^^decode_budget (N.to_nat (phase_R k)))
    ((E8^^(phase_width k-1) ++ U^^(2*k+3) ++ y_after k) *> 0inf)
    ((sdigits_word (next_last k) ++ U^^(2*k+3) ++ y_after (phase_lv (S k))) *> 0inf).
Proof.
  intro H; rewrite phase_decode_budget by exact H.
  assert (k=1 \/ k=2 \/ k=3) by lia.
  destruct H0 as [E|[E|E]]; subst k.
  - exact last_case6_return.
  - exact last_case7_return.
  - exact last_case8_return.
Qed.

Theorem next_last_checkpoints k : 1 <= k <= 3 ->
  length (next_last k) = phase_width (S k) /\
  sdigits_value (next_last k) = phase_value (S k).
Proof.
  intro H; destruct decoded_last_checkpoints as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  assert (k=1 \/ k=2 \/ k=3) by lia.
  destruct H0 as [E|[E|E]]; subst k; split; assumption.
Qed.

Print Assumptions finite_last_R.
Print Assumptions finite_last_decode.
Print Assumptions next_last_checkpoints.

Lemma N_to_nat_odd n : Nat.odd (N.to_nat n) = N.odd n.
Proof.
  destruct n as [|[p|p|]]; [reflexivity| | |reflexivity].
  - change (Nat.odd (Pos.to_nat (xI p)) = true).
    rewrite Pos2Nat.inj_xI, Nat.odd_succ, Nat.even_mul. reflexivity.
  - change (Nat.odd (Pos.to_nat (xO p)) = false).
    rewrite Pos2Nat.inj_xO, Nat.odd_mul. reflexivity.
Qed.

Lemma phase_R_parity k :
  Nat.odd (N.to_nat (phase_R k)) = Z.odd (phase_value k).
Proof.
  rewrite N_to_nat_odd.
  destruct k as [|[|[|[|k]]]]; vm_compute; reflexivity.
Qed.

Lemma finite_suffix_odd current previous zs last k lv :
  finite_round_pre current previous zs last k lv ->
  Nat.odd (right_remaining zs (N.to_nat (phase_R k))) = true.
Proof.
  intro H; destruct H as [Hs Hcs Hodd Hw Hlen Hvalue Hlv].
  destruct zs as [|c zs].
  - cbn [right_remaining]. rewrite phase_R_parity, <- Hvalue. exact Hodd.
  - rewrite right_remaining_head_parity by (pose proof (phase_R_large k); lia).
    exact Hodd.
Qed.

Theorem finite_columns_decode current previous zs last k lv :
  finite_round_pre current previous zs last k lv -> k<=3 ->
  exists zs',
    tail_columns_step (Nat.odd (N.to_nat (phase_R k))) zs zs' /\
    Forall (column_budget (4-S k)) (z_column previous :: zs') /\
    sideRLs source_tm (hashes^^decode_budget (right_remaining zs (N.to_nat (phase_R k))))
      (mixed_with_tail zs (E8^^(phase_width k-1) ++ U^^(2*k+3) ++ y_after k) *> 0inf)
      (columns_with_tail zs' (sdigits_word (next_last k) ++ U^^(2*k+3) ++
        y_after (phase_lv (S k))) *> 0inf).
Proof.
  intros H Hk; destruct H as [Hs Hcs Hodd Hw Hlen Hvalue Hlv].
  destruct (tail_columns_round_budget k previous zs
    (Nat.odd (N.to_nat (phase_R k))) ltac:(lia) Hcs) as [zs' [Hstep Hbudget]].
  exists zs'; split; [exact Hstep|]. split; [exact Hbudget|].
  eapply tail_columns_decode; [apply phase_R_large|exact Hstep|].
  apply finite_last_decode; lia.
Qed.

Print Assumptions finite_suffix_odd.
Print Assumptions finite_columns_decode.

End FiniteDecode.

Module FrontierBridge.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier.
Require Import ZifyNat Lia Arith ZArith List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Definition tail_frontier_state unary primary zs last k : Q * tape :=
  ordinary_left unary {{{((B, []), R)}}} (tail_frontier primary zs last k *> 0inf).

Theorem post_tail_to_frontier unary primary zs last k lv : lv <= 5 ->
  post_ca_tail unary primary zs last k lv -[source_tm]->*
  tail_frontier_state (unary + tail_finish_count primary zs last lv)
    primary zs last k.
Proof.
  intro Hlv.
  exact (sideRLs_concat_1 (tail_to_frontier primary zs last k lv Hlv)
    (left_emit_calls (tail_finish_count primary zs last lv) unary)).
Qed.

Lemma all_B_tail_full zs last k :
  all_B_with_tail zs (B8^^S last ++ tail_word k) =
  full_tail (map column_e zs) last k.
Proof.
  induction zs as [|c zs IH].
  - unfold full_tail. cbn [map List.app spaced_words all_B_with_tail].
    reflexivity.
  - cbn [all_B_with_tail map]. rewrite IH.
    unfold full_tail; cbn [map].
    rewrite spaced_snoc_cons.
    repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma tail_frontier_full primary zs last k e : length last = S e ->
  tail_frontier (S primary) zs last k = full_tail (primary :: map column_e zs) e k.
Proof.
  intro Hlen. unfold tail_frontier.
  rewrite Hlen.
  fold (tail_word k).
  rewrite all_B_tail_full.
  unfold full_tail; cbn [map].
  rewrite spaced_snoc_cons.
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Theorem post_tail_raw unary primary zs last k lv e :
  lv <= 5 -> k <= 5 -> length last = S e ->
  post_ca_tail unary (S primary) zs last k lv -[source_tm]->+
  ([1;0;1] *> ordinary_left
    (unary + tail_finish_count (S primary) zs last lv)) {{{((F, []), L)}}}
    (mixed_tail (primary :: map column_e zs) e k *> 0inf).
Proof.
  intros Hlv Hk Hlen.
  eapply evstep_progress_trans.
  - exact (post_tail_to_frontier unary (S primary) zs last k lv Hlv).
  - unfold tail_frontier_state. rewrite (tail_frontier_full primary zs last k e Hlen).
    exact (raw_tail_columns _ _ _ _ Hk).
Qed.

Print Assumptions post_tail_to_frontier.
Print Assumptions post_tail_raw.

End FrontierBridge.

Module RoundAssembly.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier FiniteColumns FiniteRound RoundDecode FiniteDecode FrontierBridge RoundCaller.
Require Import ZifyNat Lia Arith ZArith NArith List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Lemma mixed_tail_chain cs e k :
  mixed_tail (map column_e cs) e k =
  mixed_with_tail cs (E8^^e ++ U^^(2*k+3) ++ y_after k).
Proof.
  induction cs as [|c cs IH].
  - reflexivity.
  - cbn [map mixed_with_tail]. unfold mixed_tail in *; cbn [map].
    rewrite spaced_snoc_cons.
    rewrite <- IH. unfold mixed_column_word.
    repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma tail_finish_equation primary zs last lv :
  S (tail_finish_count primary zs last lv) =
    S (columns_finish_count zs (last_finish_count last lv))*2^primary.
Proof.
  pose proof (bfinish_count_value (repeat BA primary)
    (columns_finish_count zs (last_finish_count last lv))) as H.
  rewrite repeat_length, digits_value_repeat_BA in H.
  fold (tail_finish_count primary zs last lv) in H. lia.
Qed.

Definition finite_decode_count current previous zs k :=
  column_required (decode_budget (right_remaining zs (N.to_nat (phase_R k))))
    (round_outer_column current previous).
Definition finite_decode_input current previous zs k :=
  mixed_with_tail (round_outer_column current previous :: zs)
    (E8^^(phase_width k-1) ++ U^^(2*k+3) ++ y_after k).
Definition finite_decode_output current previous zs' k :=
  columns_with_tail (round_outer_column current previous :: zs')
    (sdigits_word (next_last k) ++ U^^(2*k+3) ++ y_after (phase_lv (S k))).

Theorem finite_raw_to_pre current previous zs last k lv :
  finite_round_pre current previous zs last k lv ->
  post_ca_tail (round_post_unary current previous)
    (round_primary_width current previous) zs last k lv -[source_tm]->+
  exception_pre_left (finite_decode_count current previous zs k) {{{((F, []), L)}}}
    (finite_decode_input current previous zs k *> 0inf).
Proof.
  intro Hpre.
  pose proof (finite_last_R _ _ _ _ _ _ Hpre) as HR.
  pose proof (finite_suffix_odd _ _ _ _ _ _ Hpre) as Hodd.
  destruct Hpre as [Hs Hcs Hhead Hw Hlen Hvalue Hlv].
  assert (Hlvbound: lv<=5).
  { rewrite Hlv; unfold phase_lv; destruct k as [|[|[|[|k]]]]; lia. }
  pose proof (round_primary_width_positive current previous) as HP.
  assert (Hlenpos: 1<=length last) by (rewrite Hlen; unfold phase_width; lia).
  pose proof (post_tail_raw (round_post_unary current previous)
    (round_primary_width current previous-1) zs last k lv (phase_width k-1)
    Hlvbound ltac:(lia) ltac:(lia)) as Hraw.
  replace (S (round_primary_width current previous-1)) with
    (round_primary_width current previous) in Hraw by lia.
  assert (Htally: round_post_unary current previous +
    tail_finish_count (round_primary_width current previous) zs last lv =
    2*finite_decode_count current previous zs k+1).
  {
    pose proof (tail_finish_equation (round_primary_width current previous) zs last lv) as Hcount.
    rewrite <- right_remaining_finish, HR in Hcount.
    pose proof (phase_R_large k) as Hbase.
    pose proof (right_remaining_lower zs (N.to_nat (phase_R k)) ltac:(lia)) as Hlower.
    pose proof (primary_decode_tally current previous
      (right_remaining zs (N.to_nat (phase_R k)))
      ltac:(lia) Hodd) as Ht.
    unfold finite_decode_count; lia.
  }
  rewrite (ordinary_raw_pre_left_count _ _ Htally) in Hraw.
  unfold finite_decode_input.
  replace (round_primary_width current previous-1 :: map column_e zs) with
    (map column_e (round_outer_column current previous :: zs)) in Hraw by reflexivity.
  rewrite mixed_tail_chain in Hraw. exact Hraw.
Qed.

Theorem finite_decode_side current previous zs last k lv zs' :
  finite_round_pre current previous zs last k lv -> k<=3 ->
  tail_columns_step (Nat.odd (N.to_nat (phase_R k))) zs zs' ->
  sideRLs source_tm (hashes^^finite_decode_count current previous zs k)
    (finite_decode_input current previous zs k *> 0inf)
    (finite_decode_output current previous zs' k *> 0inf).
Proof.
  intros Hpre Hk Hstep.
  pose proof (tail_columns_decode zs zs' (N.to_nat (phase_R k)) _ _
    (phase_R_large k) Hstep (finite_last_decode k ltac:(destruct Hpre; lia))) as Htail.
  pose proof (segRLs_concat
    (mixed_column_spec (round_outer_column current previous)
      (decode_budget (right_remaining zs (N.to_nat (phase_R k)))))
    (hashes_U_run (decode_budget (right_remaining zs (N.to_nat (phase_R k)))) 2)) as Hp.
  unfold finite_decode_count, finite_decode_input, finite_decode_output.
  cbn [mixed_with_tail columns_with_tail].
  applys_eq (segRLs_sideRLs_concat Hp Htail);
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Theorem finite_exception_done current previous zs last k lv :
  finite_round_pre current previous zs last k lv -> k<=3 ->
  exists zs',
    tail_columns_step (Nat.odd (N.to_nat (phase_R k))) zs zs' /\
    Forall (column_budget (4-S k)) (z_column previous :: zs') /\
    post_ca_tail (round_post_unary current previous)
      (round_primary_width current previous) zs last k lv -[source_tm]->+
    exception_done (finite_decode_count current previous zs k)
      (finite_decode_output current previous zs' k).
Proof.
  intros Hpre Hk.
  destruct (finite_columns_decode _ _ _ _ _ _ Hpre Hk) as [zs' [Hstep [Hbudget Hside]]].
  exists zs'; split; [exact Hstep|]. split; [exact Hbudget|].
  eapply progress_trans; [exact (finite_raw_to_pre _ _ _ _ _ _ Hpre)|].
  apply exception_pre_from_side_word.
  exact (finite_decode_side _ _ _ _ _ _ _ Hpre Hk Hstep).
Qed.

Print Assumptions finite_raw_to_pre.
Print Assumptions finite_exception_done.

Theorem finite_done_to_next_post current previous zs' k next :
  exception_done (half_parameter next)
    (finite_decode_output current previous zs' k) -[source_tm]->+
  post_ca_tail (round_post_unary next current) (round_primary_width next current)
    (z_column previous :: zs') (next_last k) (S k) (phase_lv (S k)).
Proof.
  set (tail:=sdigits_word (next_last k) ++ U^^(2*k+3) ++ y_after (phase_lv (S k))).
  set (rest:=B8++digits_word (z_tail_digits previous)++U^^2++columns_with_tail zs' tail).
  applys_eq (exception_done_ca (half_parameter next) (current+4) rest
    ltac:(unfold half_parameter; lia)).
  - unfold finite_decode_output, exception_done.
    cbn [columns_with_tail]. fold tail.
    rewrite round_outer_column_word.
    unfold rest, half_parameter; repeat rewrite app_assoc; flia.
  - unfold post_ca_tail, round_post_unary, round_primary_width.
    rewrite tail_layout_chain. cbn [columns_with_tail].
    rewrite z_column_word, z_digits_word_split.
    replace (2*S k+1) with (2*k+3) by lia.
    fold tail. unfold rest, half_parameter;
      repeat rewrite Str_app_assoc; repeat rewrite app_assoc; flia.
Qed.

Print Assumptions finite_done_to_next_post.

End RoundAssembly.

Module WidthBounds.
(** Width and index bounds for a finite round with a signed last column.

    AI assistance: this proof sketch, the scripts and the checks were produced with the help of GPT-6 Astra (OpenAI).
*)
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier FiniteColumns RoundDecode.
Require Import ZifyNat Lia Arith ZArith List Bool.
Import ListNotations.
Local Open Scope nat_scope.

Lemma outer_decode_even_ge6 current previous out :
  exists q,
    column_required out (round_outer_column current previous) = 2*q /\
    6 <= 2*q.
Proof.
  pose proof (round_primary_width_positive current previous) as HP.
  unfold column_required, round_outer_column; cbn [column_e column_digits].
  replace (S (round_primary_width current previous-1)) with
    (round_primary_width current previous) by lia.
  rewrite round_outer_digits_value.
  set (P:=round_primary_width current previous).
  assert (HP3: 3<=P) by (unfold P, round_primary_width, half_parameter; lia).
  assert (Hsplit: 2^P = 2*2^(P-1)).
  { replace P with (S (P-1)) at 1 by lia.
    rewrite Nat.pow_succ_r by lia; reflexivity. }
  assert (Ha: 4<=2^(P-1)).
  { replace (P-1) with (2+(P-3)) by lia.
    rewrite Nat.pow_add_r. change (2^2) with 4.
    pose proof (Nat.pow_nonzero 2 (P-3) ltac:(lia)); nia. }
  replace (half_parameter current+1) with (S (half_parameter current)) by lia.
  rewrite Nat.pow_succ_r by lia. rewrite Hsplit.
  set (a:=2^(P-1)) in *.
  set (b:=2^(half_parameter current) *
    (1+geom4n (previous+4)+2^(2*(previous+4)+1)+2^(2*(previous+4)+2))).
  exists ((out+1)*a-1+b).
  unfold b. split; nia.
Qed.

Lemma outer_decode_parameter current previous out :
  half_parameter
    ((column_required out (round_outer_column current previous)-6)/2) =
  column_required out (round_outer_column current previous).
Proof.
  destruct (outer_decode_even_ge6 current previous out) as [q [Hq Hge]].
  unfold half_parameter; rewrite Hq; flia.
Qed.

Lemma outer_decode_lower current previous out :
  2^(round_primary_width current previous)-2 <=
    column_required out (round_outer_column current previous).
Proof.
  pose proof (round_primary_width_positive current previous).
  unfold column_required, round_outer_column; cbn [column_e column_digits].
  replace (S (round_primary_width current previous-1)) with
    (round_primary_width current previous) by lia.
  nia.
Qed.

Lemma outer_decode_growth current previous out suffix_width :
  2*suffix_width+4 <= half_parameter previous+1 ->
  2*(half_parameter current+1+half_parameter previous+suffix_width)+4 <=
    column_required out (round_outer_column current previous)+1.
Proof.
  intro Hwidth.
  pose proof (outer_decode_lower current previous out) as Hlower.
  pose proof (pow2_linear_margin
    (half_parameter current+half_parameter previous)) as Hpow.
  unfold round_primary_width in Hlower.
  replace (half_parameter current+half_parameter previous+6) with
    (S (half_parameter current+half_parameter previous+5)) in Hlower by lia.
  rewrite Nat.pow_succ_r in Hlower by lia.
  lia.
Qed.

Lemma tail_columns_step_width_sum b cs cs' :
  tail_columns_step b cs cs' ->
  columns_width_sum cs' = columns_width_sum cs.
Proof.
  induction cs as [|c cs IH] in cs' |- *; destruct cs' as [|c' cs'];
    cbn [tail_columns_step]; try contradiction; [reflexivity|].
  intros [[He Hv] Hrest].
  rewrite !columns_width_sum_cons, (IH _ Hrest).
  unfold column_width; rewrite He; reflexivity.
Qed.

Theorem tail_width_dominance_step current previous next out cs cs'
    (last last' : list SDigit) b :
  tail_columns_step b cs cs' ->
  length last = S (length last') ->
  half_parameter next = column_required out (round_outer_column current previous) ->
  (2*(columns_width_sum cs+length last)+4 <= half_parameter previous+1 /\
   2*(half_parameter previous+1+columns_width_sum cs+length last)+4 <=
     half_parameter current+1) ->
  (2*(columns_width_sum (z_column previous::cs')+length last')+4 <=
     half_parameter current+1 /\
   2*(half_parameter current+1+columns_width_sum (z_column previous::cs')+length last')+4 <=
     half_parameter next+1).
Proof.
  intros Hstep Hlast Hnext [Hprev Hcur].
  rewrite columns_width_sum_cons, (tail_columns_step_width_sum _ _ _ Hstep).
  rewrite !z_column_e.
  rewrite Hnext.
  pose proof (outer_decode_growth current previous out
    (columns_width_sum cs+length last) Hprev) as Hgrowth.
  lia.
Qed.

Lemma tail_next_half_tally current previous cs last lv n :
  lv<=5 ->
  round_post_unary current previous +
    tail_finish_count (round_primary_width current previous) cs last lv = 2*n+1 ->
  tail_next_half current previous cs last lv = Z.of_nat n.
Proof.
  intros Hlv Htally.
  unfold tail_next_half.
  rewrite <- (trigger_hash_count (round_primary_width current previous) cs last lv Hlv).
  rewrite Nat2Z.inj_succ.
  replace (Z.of_nat (round_post_unary current previous) +
    Z.succ (Z.of_nat (tail_finish_count (round_primary_width current previous) cs last lv))-1)%Z
    with (Z.of_nat (round_post_unary current previous +
      tail_finish_count (round_primary_width current previous) cs last lv))
    by (rewrite Nat2Z.inj_add; lia).
  rewrite Htally, Nat2Z.inj_add, Nat2Z.inj_mul.
  change ((2*Z.of_nat n+1)/2 = Z.of_nat n)%Z.
  flia.
Qed.

Theorem tail_next_parameter current previous cs last lv out :
  lv<=5 ->
  round_post_unary current previous +
    tail_finish_count (round_primary_width current previous) cs last lv =
      2*column_required out (round_outer_column current previous)+1 ->
  half_parameter (tail_next_index current previous cs last lv) =
    column_required out (round_outer_column current previous).
Proof.
  intros Hlv Htally.
  unfold tail_next_index.
  rewrite (tail_next_half_tally _ _ _ _ _ _ Hlv Htally).
  pose proof (outer_decode_even_ge6 current previous out) as [q [Hq Hge]].
  assert (H6: 6<=column_required out (round_outer_column current previous)) by lia.
  set (n:=column_required out (round_outer_column current previous)) in *.
  change (half_parameter (Z.to_nat ((Z.of_nat n-Z.of_nat 6)/Z.of_nat 2)) = n).
  rewrite <- Nat2Z.inj_sub by exact H6.
  rewrite <- Nat2Z.inj_div, Nat2Z.id.
  unfold n.
  apply outer_decode_parameter.
Qed.

Print Assumptions outer_decode_even_ge6.
Print Assumptions outer_decode_growth.
Print Assumptions tail_width_dominance_step.
Print Assumptions tail_next_parameter.

End WidthBounds.

Module FiniteComplete.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier FiniteColumns FiniteRound RoundDecode FiniteDecode FrontierBridge RoundCaller RoundAssembly WidthBounds.
Require Import ZifyNat Lia Arith ZArith NArith List Bool.
Import ListNotations.
Local Open Scope nat_scope.

Lemma finite_tally current previous zs last k lv :
  finite_round_pre current previous zs last k lv ->
  round_post_unary current previous +
    tail_finish_count (round_primary_width current previous) zs last lv =
    2*finite_decode_count current previous zs k+1.
Proof.
  intro Hpre.
  pose proof (finite_last_R _ _ _ _ _ _ Hpre) as HR.
  pose proof (finite_suffix_odd _ _ _ _ _ _ Hpre) as Hodd.
  pose proof (tail_finish_equation (round_primary_width current previous) zs last lv) as Hcount.
  rewrite <- right_remaining_finish, HR in Hcount.
  pose proof (phase_R_large k) as Hbase.
  pose proof (right_remaining_lower zs (N.to_nat (phase_R k)) ltac:(lia)) as Hlower.
  pose proof (primary_decode_tally current previous
    (right_remaining zs (N.to_nat (phase_R k))) ltac:(lia) Hodd) as Ht.
  unfold finite_decode_count; lia.
Qed.

Lemma finite_next_parameter current previous zs last k lv :
  finite_round_pre current previous zs last k lv ->
  half_parameter (tail_next_index current previous zs last lv) =
    finite_decode_count current previous zs k.
Proof.
  intro Hpre; pose proof (finite_tally _ _ _ _ _ _ Hpre) as Htally.
  destruct Hpre as [Hs Hcs Hodd Hw Hlen Hvalue Hlv].
  unfold finite_decode_count in *.
  apply tail_next_parameter; [|exact Htally].
  rewrite Hlv; unfold phase_lv; destruct k as [|[|[|[|k]]]]; lia.
Qed.

Theorem finite_round_proved : finite_round_obligation.
Proof.
  unfold finite_round_obligation.
  intros current previous zs last k lv Hpre Hk.
  destruct (finite_exception_done _ _ _ _ _ _ Hpre Hk)
    as [zs' [Hstep [Hbudget Hdone]]].
  pose proof (finite_next_parameter _ _ _ _ _ _ Hpre) as Hnext.
  destruct Hpre as [Hs Hcs Hodd Hw Hlen Hvalue Hlv].
  pose proof (next_last_checkpoints k ltac:(lia)) as [Hlen' Hvalue'].
  exists zs', (next_last k), (phase_lv (S k)). split.
  - eapply progress_trans; [exact Hdone|].
    rewrite <- Hnext. apply finite_done_to_next_post.
  - constructor.
    + lia.
    + exact Hbudget.
    + exact (z_column_odd previous).
    + eapply tail_width_dominance_step; [exact Hstep| |exact Hnext|exact Hw].
      rewrite Hlen, Hlen'; unfold phase_width; lia.
    + exact Hlen'.
    + exact Hvalue'.
    + reflexivity.
Qed.

Print Assumptions finite_round_proved.

End FiniteComplete.

Module FinalTrigger.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState SignedFrontier FiniteColumns FiniteRound RoundDecode FiniteDecode FrontierBridge RoundCaller RoundAssembly WidthBounds FiniteComplete TailCases.
Require Import ZifyNat Lia Arith ZArith NArith List Bool.
Import ListNotations.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope sym.

Fixpoint full_finish_count es out :=
  match es with [] => out
  | e::rest => (full_finish_count rest out+2)*2^(S e)-3 end.

Lemma full_finish_prefix es out input output :
  sideRLs source_tm (hashes^^out) (input *> 0inf) (output *> 0inf) ->
  sideRLs source_tm (hashes^^full_finish_count es out)
    ((spaced_words (map (fun e=>E8^^e++A8) es ++ [input])) *> 0inf)
    ((spaced_words (map (fun e=>B8^^S e) es ++ [output])) *> 0inf).
Proof.
  intro Htail; induction es as [|e es IH]; [exact Htail|].
  cbn [map full_finish_count]. rewrite !spaced_snoc_cons.
  pose proof (standard_mixed_to_binary_out_spec e (repeat BB (S e))
    (full_finish_count es out) (repeat_length _ _)) as Hc.
  rewrite digits_word_repeat_BB, digits_value_repeat_BB in Hc.
  assert (Hpow:2<=2^(S e)).
  { rewrite Nat.pow_succ_r by lia; pose proof (Nat.pow_nonzero 2 e ltac:(lia)); lia. }
  replace ((full_finish_count es out+1)*2^S e-2+(2^S e-1))
    with ((full_finish_count es out+2)*2^S e-3) in Hc by nia.
  pose proof (segRLs_concat Hc (hashes_U_run (full_finish_count es out) 2)) as Hp.
  applys_eq (segRLs_sideRLs_concat Hp IH);
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Lemma spaced_tail_append ws x suffix :
  spaced_words (ws++[x++suffix]) = spaced_words (ws++[x]) ++ suffix.
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  rewrite !spaced_snoc_cons, IH. repeat rewrite <- app_assoc; reflexivity.
Qed.

Definition trigger_finish es := full_finish_count es (N.to_nat 134217725%N).

Theorem raw_four_to_frontier es :
  sideRLs source_tm (hashes^^trigger_finish es)
    (mixed_tail es 25 4 *> 0inf) (full_tail es 24 5 *> 0inf).
Proof.
  pose proof (full_finish_prefix es _ _ _ last_case9_frontier) as H.
  unfold mixed_tail, full_tail, trigger_finish, tail_word.
  applys_eq H; rewrite spaced_tail_append; reflexivity.
Qed.

Lemma full_finish_monotone es a b : a<=b -> full_finish_count es a <= full_finish_count es b.
Proof.
  intro H; induction es as [|e es IH]; [exact H|].
  cbn [full_finish_count]. nia.
Qed.

Lemma nested_required_finish es e :
  nested_required es e = full_finish_count es (3*(2^(S e)-1)).
Proof.
  induction es as [|a es IH]; [reflexivity|].
  cbn [nested_required full_finish_count]. rewrite IH.
  assert (Hpow:2<=2^(S a)).
  { rewrite Nat.pow_succ_r by lia; pose proof (Nat.pow_nonzero 2 a ltac:(lia)); lia. }
  nia.
Qed.

Lemma trigger_finish_sufficient es : nested_required es 23 <= trigger_finish es.
Proof.
  rewrite nested_required_finish. unfold trigger_finish. apply full_finish_monotone.
  apply Nat2Z.inj_le. rewrite Nat2Z.inj_mul, Nat2Z.inj_sub by
    (pose proof (Nat.pow_nonzero 2 24 ltac:(lia)); lia).
  rewrite Nat2Z.inj_pow, N_nat_Z.
  vm_compute; discriminate.
Qed.

Lemma full_finish_less_than_decode cs out small : small<out ->
  full_finish_count (map column_e cs) small < columns_input_count cs out.
Proof.
  intro H; induction cs as [|c cs IH]; [exact H|].
  cbn [map full_finish_count columns_input_count]. unfold column_required.
  assert (Hpow:2<=2^(S (column_e c))).
  { rewrite Nat.pow_succ_r by lia;
    pose proof (Nat.pow_nonzero 2 (column_e c) ltac:(lia)); lia. }
  nia.
Qed.

Lemma safe_tail_steps b cs : Forall column_safe cs -> exists cs', tail_columns_step b cs cs'.
Proof.
  intro H; induction H as [|c cs Hc Hcs IH].
  - exists ([] : list BinaryColumn); exact I.
  - destruct IH as [cs' Hrest].
    destruct (column_step_exists (match cs with []=>b | d::_=>Nat.odd (column_value d) end)
      c (column_safe_lower c Hc)) as [c' Hc'].
    exists (c'::cs'); split; assumption.
Qed.

Lemma tail_steps_es b cs cs' : tail_columns_step b cs cs' ->
  map column_e cs' = map column_e cs.
Proof.
  induction cs as [|c cs IH] in cs' |- *; destruct cs' as [|c' cs'];
    cbn [tail_columns_step]; try contradiction; [reflexivity|].
  intros [[He Hv] Hrest]; cbn [map]. rewrite He, (IH cs' Hrest); reflexivity.
Qed.

Print Assumptions raw_four_to_frontier.
Print Assumptions trigger_finish_sufficient.

Lemma final_last_budget_gap :
  N.to_nat 134217725%N < decode_budget (N.to_nat (phase_R 4)).
Proof.
  assert (Hcalc: decode_budget (N.to_nat (phase_R 4)) = N.to_nat 158684500%N).
  { unfold decode_budget, ceil_half. apply Nat2N.inj.
    rewrite Nat2N.inj_sub, Nat2N.inj_div, Nat2N.inj_add, !N2Nat.id.
    vm_compute; reflexivity. }
  rewrite Hcalc. apply Nat2Z.inj_lt. rewrite !N_nat_Z. vm_compute; reflexivity.
Qed.

Lemma final_decode_budget_gap current previous zs last lv :
  finite_round_pre current previous zs last 4 lv ->
  trigger_finish (frontier_es current previous zs) < finite_decode_count current previous zs 4.
Proof.
  intro Hpre.
  destruct (safe_tail_steps (Nat.odd (N.to_nat (phase_R 4))) zs
    (finite_pre_safe _ _ _ _ _ _ Hpre)) as [zs' Hstep].
  pose proof (full_finish_less_than_decode (round_outer_column current previous :: zs')
    (decode_budget (N.to_nat (phase_R 4))) (N.to_nat 134217725%N)
    final_last_budget_gap) as Hgap.
  cbn [columns_input_count] in Hgap.
  rewrite (columns_decode_budget zs zs' (N.to_nat (phase_R 4)) (phase_R_large 4) Hstep) in Hgap.
  cbn [map] in Hgap.
  rewrite (tail_steps_es _ _ _ Hstep) in Hgap.
  exact Hgap.
Qed.

Lemma final_decode_input_raw current previous zs :
  finite_decode_input current previous zs 4 = mixed_tail (frontier_es current previous zs) 25 4.
Proof.
  unfold finite_decode_input, frontier_es.
  change (mixed_with_tail (round_outer_column current previous :: zs)
    (E8^^25 ++ U^^11 ++ y_after 4) =
    mixed_tail (map column_e (round_outer_column current previous :: zs)) 25 4).
  rewrite mixed_tail_chain. reflexivity.
Qed.

Theorem finite_trigger_proved : finite_trigger_obligation.
Proof.
  unfold finite_trigger_obligation.
  intros current previous zs last lv Hpre.
  pose proof (final_decode_budget_gap _ _ _ _ _ Hpre) as Hgap.
  set (es:=frontier_es current previous zs) in *.
  set (f:=trigger_finish es) in *.
  set (n:=finite_decode_count current previous zs 4) in *.
  exists (n-S f), f, es, 23. split.
  - eapply progress_trans; [exact (finite_raw_to_pre _ _ _ _ _ _ Hpre)|].
    rewrite final_decode_input_raw. fold es.
    pose proof (exception_launch_partial_side f (n-S f) _ _ (raw_four_to_frontier es)) as Hrun.
    replace (S (f+(n-S f))) with n in Hrun by lia. exact Hrun.
  - apply trigger_finish_sufficient.
Qed.

Print Assumptions finite_trigger_proved.

End FinalTrigger.

Module FiniteOrbit.
From BusyCoq Require Import Individual62 Longitudinal.
Import SOBCv10 W61Exit TailState FiniteRound FiniteComplete FinalTrigger.
Require Import Lia List.
Import ListNotations.
Local Open Scope nat_scope.

Lemma halts_after_progress c c' : c -[source_tm]->+ c' -> halts source_tm c -> halts source_tm c'.
Proof.
  intros Hrun Hhalt.
  assert (Hsteps: c -[source_tm]->* c') by (apply progress_evstep; exact Hrun).
  exact (proj1 (halts_evstep_iff source_tm _ _ Hsteps) Hhalt).
Qed.

Theorem finite_entry_nonhalt current previous zs last lv :
  finite_round_pre current previous zs last 1 lv ->
  ~halts source_tm (post_ca_tail (round_post_unary current previous)
    (round_primary_width current previous) zs last 1 lv).
Proof.
  intros Hpre Hhalt.
  destruct (finite_round_proved _ _ _ _ _ _ Hpre ltac:(lia))
    as [zs1 [last1 [lv1 [H1 P1]]]].
  apply (halts_after_progress _ _ H1) in Hhalt.
  destruct (finite_round_proved _ _ _ _ _ _ P1 ltac:(lia))
    as [zs2 [last2 [lv2 [H2 P2]]]].
  apply (halts_after_progress _ _ H2) in Hhalt.
  destruct (finite_round_proved _ _ _ _ _ _ P2 ltac:(lia))
    as [zs3 [last3 [lv3 [H3 P3]]]].
  apply (halts_after_progress _ _ H3) in Hhalt.
  destruct (finite_trigger_proved _ _ _ _ _ P3)
    as [c [f [es [e [H4 Hbound]]]]].
  apply (halts_after_progress _ _ H4) in Hhalt.
  exact (nested_exit c f es e Hbound Hhalt).
Qed.

Print Assumptions finite_entry_nonhalt.

End FiniteOrbit.

(** Nonhalting from the exact blank-tape start.

    AI assistance: this proof sketch, the scripts and the checks were produced with the help of GPT-6 Astra (OpenAI).
*)
From BusyCoq Require Import Individual62 Longitudinal Flip Permute.
Import SOBCv10 W61Exit TailState FiniteRound OpeningEntry OpeningLate FiniteOrbit.
Require Import String List.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope sym.

Lemma entry_count_compat :
  OpeningEntry.entry_n5 =
    OpeningDecode.opening_decode_calls (OpeningEarly.opening_n4-2).
Proof. reflexivity. Qed.

Lemma fifth_word_compat :
  OpeningLate.fifth_output =
    A8^^(OpeningEarly.opening_n4-2) ++
    sdigits_word OpeningDecode.opening_digits ++ U^^3 ++ A8 ++ [1;1].
Proof. reflexivity. Qed.

Lemma blank_to_entry : (D;; tape0) -[SOBCv10.source_tm]->* OpeningEntry.entry_state.
Proof.
  eapply evstep_trans; [exact OpeningLate.opening_D_to_fifth_done|].
  apply progress_evstep.
  pose proof OpeningEntry.opening_exception_to_entry as Hentry.
  rewrite entry_count_compat, <- fifth_word_compat in Hentry.
  exact Hentry.
Qed.

Lemma sobc_D_nonhalt : ~ halts SOBCv10.source_tm (D;; tape0).
Proof.
  intro H.
  apply (proj1 (halts_evstep_iff SOBCv10.source_tm _ _ blank_to_entry)) in H.
  exact (FiniteOrbit.finite_entry_nonhalt _ _ _ _ _ OpeningEntry.entry_pre H).
Qed.

Definition tm := Eval compute in
  (TM_from_str "1RB0LE_1RC---_0RD0RB_1RE0LA_1RF0LF_1LD1RF").

Definition phi (q : Q) : Q :=
  match q with
  | A => D | B => E | C => F | D => A | E => B | F => C
  end.

Lemma original_permutation : Perm (flip tm) SOBCv10.source_tm phi.
Proof.
  split.
  - intros [] [] H; cbn in *; try discriminate; reflexivity.
  - intros [] [] s' d q' H; cbn in *; inversion H; subst; reflexivity.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  intro H.
  apply flip_halts in H.
  change (halts (flip tm) (A;; tape0)) in H.
  exact (sobc_D_nonhalt (perm_halts _ _ _ _ _ original_permutation H)).
Qed.

Print Assumptions blank_to_entry.
Print Assumptions original_permutation.
Print Assumptions nonhalt.
