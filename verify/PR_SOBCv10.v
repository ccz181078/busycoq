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

From BusyCoq Require SOBCv10.

Notation source_tm := SOBCv10.tm.

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

Lemma blank_to_entry : (D;; tape0) -[source_tm]->* OpeningEntry.entry_state.
Proof.
  eapply evstep_trans; [exact OpeningLate.opening_D_to_fifth_done|].
  apply progress_evstep.
  pose proof OpeningEntry.opening_exception_to_entry as Hentry.
  rewrite entry_count_compat, <- fifth_word_compat in Hentry.
  exact Hentry.
Qed.

Lemma sobc_D_nonhalt : ~ halts source_tm (D;; tape0).
Proof.
  intro H.
  apply (proj1 (halts_evstep_iff source_tm _ _ blank_to_entry)) in H.
  exact (FiniteOrbit.finite_entry_nonhalt _ _ _ _ _ OpeningEntry.entry_pre H).
Qed.

Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC---_0RD0RB_1RE0LA_1RF0LF_1LD1RF").

Definition phi (q : Q) : Q :=
  match q with
  | A => D | B => E | C => F | D => A | E => B | F => C
  end.

Lemma original_permutation : Perm (flip tm) source_tm phi.
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
