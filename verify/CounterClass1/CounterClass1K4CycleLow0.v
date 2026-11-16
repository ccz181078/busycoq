Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles BusyCoq.CounterClass1.CounterClass1K4Phase
  BusyCoq.CounterClass1.CounterClass1K4Words BusyCoq.CounterClass1.CounterClass1K4Boundary BusyCoq.CounterClass1.CounterClass1K4BoundaryLow0.
Require Import Lia.
Require Import List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

Section K4Low0Cycle.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable C: K4ComplexRules P K4Low0.
Let R := k4c_simple C.

Lemma k4_low0_prebase_to_base_bits:
  k4_extend k4_prebase_bits 381 11=k4_base_bits.
Proof. vm_compute. reflexivity. Qed.

Lemma k4_low0_scan_next_t4 runs B H S D k:
  K4ScanStart P K4T4 runs B H S D k -> K4HeadBits K4T4 B ->
  let runsp:=runs++[D+3; 1; 2*S+k+3] in
  let Bp:=k4_extend B (D+3) (2*S+k+3) in
  let Hp:=2*H+k+7 in
  let Sp:=2*S+k+3 in
  let Dp:=2*D+1-k in
  K4ScanStart P K4T2 runsp Bp Hp Sp Dp (k+1) /\
  K4HeadBits K4T2 Bp.
Proof.
  intros HS HB. cbv zeta.
  pose proof (k4_scan_next_word P K4T4 runs B H S D k HS HB) as HW.
  cbv zeta in HW.
  destruct HW as [Hshape [Hbits [Hhead [Hheadbits Hdrop]]]].
  pose proof Hshape as Hshape0.
  destruct Hshape0 as [_ [_ [Hsum [_ [Hhs [Hlarge [Hk Hsp]]]]]]].
  assert (Hlen: length (k4_extend B (D+3) (2*S+k+3))=2*H+k+8).
  { rewrite Hbits,k4_bits_length,Hsum. lia. }
  assert (BH: nth (2*H+k+7) (k4_extend B (D+3) (2*S+k+3))
      false=true).
  { eapply k4_bits_last_true; [exact Hshape|exact Hbits|lia]. }
  assert (BHm: nth (2*H+k+7-1) (k4_extend B (D+3) (2*S+k+3))
      false=true).
  { eapply k4_bits_last_true; [exact Hshape|exact Hbits|lia]. }
  assert (Hwin: forall z, 2*D+1-k-4<=z<=2*D+1-k+3 ->
      nth z (k4_extend B (D+3) (2*S+k+3)) false=true).
  { intros z Hz.
    assert (E: z=2*D+1-k-7+(z-(2*D+1-k-7))) by lia.
    rewrite E.
    apply k4_scan_next_middle_window with
      (P:=P) (kind:=K4T4) (runs:=runs) (H:=H) (S:=S) (D:=D) (k:=k);
      assumption || lia. }
  assert (HE:=k4_scan_endfan_t4 P R runs B H S D k HS HB).
  assert (HP: K4ScanPayload P K4T2 (k4_extend B (D+3) (2*S+k+3))
      (2*H+k+7) (2*S+k+3) (2*D+1-k)).
  { apply (k4_low0_end_t2_payload P C); try assumption; try lia.
    exact (proj1 Hheadbits). }
  split; [|exact Hheadbits].
  exact (k4_scan_start_of_payload P K4T2
    (runs++[D+3; 1; 2*S+k+3])
    (k4_extend B (D+3) (2*S+k+3))
    (2*H+k+7) (2*S+k+3) (2*D+1-k) (k+1)
    Hshape Hbits Hhead Hheadbits Hdrop HP).
Qed.

Lemma k4_low0_scan_next_t2 runs B H S D k:
  K4ScanStart P K4T2 runs B H S D k -> K4HeadBits K4T2 B ->
  let runsp:=runs++[D+3; 1; 2*S+k+3] in
  let Bp:=k4_extend B (D+3) (2*S+k+3) in
  let Hp:=2*H+k+7 in
  let Sp:=2*S+k+3 in
  let Dp:=2*D+1-k in
  K4ScanStart P K4T4 runsp Bp Hp Sp Dp (k+2) /\
  K4HeadBits K4T4 Bp.
Proof.
  intros HS HB. cbv zeta.
  pose proof (k4_scan_next_word P K4T2 runs B H S D k HS HB) as HW.
  cbv zeta in HW.
  destruct HW as [Hshape [Hbits [Hhead [Hheadbits Hdrop]]]].
  pose proof Hshape as Hshape0.
  destruct Hshape0 as [_ [_ [Hsum [_ [Hhs [Hlarge [Hk Hsp]]]]]]].
  assert (Hlen: length (k4_extend B (D+3) (2*S+k+3))=2*H+k+8).
  { rewrite Hbits,k4_bits_length,Hsum. lia. }
  assert (BH: nth (2*H+k+7) (k4_extend B (D+3) (2*S+k+3))
      false=true).
  { eapply k4_bits_last_true; [exact Hshape|exact Hbits|lia]. }
  assert (BHm: nth (2*H+k+7-1) (k4_extend B (D+3) (2*S+k+3))
      false=true).
  { eapply k4_bits_last_true; [exact Hshape|exact Hbits|lia]. }
  assert (Hwin: forall z, 2*D+1-k-5<=z<=2*D+1-k+3 ->
      nth z (k4_extend B (D+3) (2*S+k+3)) false=true).
  { intros z Hz.
    assert (E: z=2*D+1-k-7+(z-(2*D+1-k-7))) by lia.
    rewrite E.
    apply k4_scan_next_middle_window with
      (P:=P) (kind:=K4T2) (runs:=runs) (H:=H) (S:=S) (D:=D) (k:=k);
      assumption || lia. }
  assert (HE:=k4_scan_endfan_t2 P R runs B H S D k HS HB).
  assert (HP: K4ScanPayload P K4T4 (k4_extend B (D+3) (2*S+k+3))
      (2*H+k+7) (2*S+k+3) (2*D+1-k)).
  { apply (k4_low0_end_t4_payload P C); try assumption; try lia.
    exact (proj1 Hheadbits). }
  split; [|exact Hheadbits].
  exact (k4_scan_start_of_payload P K4T4
    (runs++[D+3; 1; 2*S+k+3])
    (k4_extend B (D+3) (2*S+k+3))
    (2*H+k+7) (2*S+k+3) (2*D+1-k) (k+2)
    Hshape Hbits Hhead Hheadbits Hdrop HP).
Qed.

(* The last finite phase has the concrete suffix [...;191;2;1].  Its scan
   facts use the effective arithmetic parameters [S=2,D=378], rather than
   the physical final run [1].  The weak scan interface makes this harmless:
   after that one scan the produced word is exactly the stable base word. *)
Lemma k4_low0_prebase_to_base:
  K4ScanData P K4T2 k4_prebase_bits 382 2 378 4 ->
  K4ScanStart P K4T4 k4_base_runs k4_base_bits 775 11 753 6 /\
  K4HeadBits K4T4 k4_base_bits.
Proof.
  intros HS.
  pose proof (k4_scan_endfan_t2_data P R k4_prebase_bits
    382 2 378 4 HS k4_prebase_head_bits) as HE.
  change (K4EndFan P K4T4 (k4_extend k4_prebase_bits 381 11)
    775 11 753) in HE.
  rewrite k4_low0_prebase_to_base_bits in HE.
  destruct k4_base_boundary_bits as [Hlen [BH [BHm Hwin]]].
  assert (HP: K4ScanPayload P K4T4 k4_base_bits 775 11 753).
  { apply (k4_low0_end_t4_payload P C); try assumption; try lia. }
  split; [|exact k4_base_head_bits].
  destruct k4_base_pointer_facts as [Hbase Hdrop].
  exact (k4_scan_start_of_payload P K4T4 k4_base_runs k4_base_bits
    775 11 753 6 k4_base_shape eq_refl k4_base_head
    k4_base_head_bits Hdrop HP).
Qed.

Record K4ScanState0 := {
  k4s0_kind: K4Kind;
  k4s0_runs: list nat;
  k4s0_bits: list bool;
  k4s0_H: nat;
  k4s0_S: nat;
  k4s0_D: nat;
  k4s0_k: nat
}.

Definition k4_scan_state0_step (s:K4ScanState0) : K4ScanState0 :=
  {| k4s0_kind := k4_next_kind (k4s0_kind s);
     k4s0_runs := k4s0_runs s ++ [k4s0_D s+3;1;2*k4s0_S s+k4s0_k s+3];
     k4s0_bits := k4_extend (k4s0_bits s) (k4s0_D s+3)
       (2*k4s0_S s+k4s0_k s+3);
     k4s0_H := 2*k4s0_H s+k4s0_k s+7;
     k4s0_S := 2*k4s0_S s+k4s0_k s+3;
     k4s0_D := 2*k4s0_D s+1-k4s0_k s;
     k4s0_k := k4_next_k (k4s0_kind s) (k4s0_k s) |}.

Fixpoint k4_scan_state0_iter (n:nat) (s:K4ScanState0) : K4ScanState0 :=
  match n with
  | 0 => s
  | S n => k4_scan_state0_step (k4_scan_state0_iter n s)
  end.

Definition k4_low0_base_state : K4ScanState0 :=
  {| k4s0_kind := K4T4;
     k4s0_runs := k4_base_runs;
     k4s0_bits := k4_base_bits;
     k4s0_H := 775;
     k4s0_S := 11;
     k4s0_D := 753;
     k4s0_k := 6 |}.

Definition K4ScanState0Valid0 (s:K4ScanState0) : Prop :=
  K4ScanStart P (k4s0_kind s) (k4s0_runs s) (k4s0_bits s)
    (k4s0_H s) (k4s0_S s) (k4s0_D s) (k4s0_k s) /\
  K4HeadBits (k4s0_kind s) (k4s0_bits s).

Lemma k4_low0_state_step s:
  K4ScanState0Valid0 s -> K4ScanState0Valid0 (k4_scan_state0_step s).
Proof.
  destruct s as [kind runs B H S D k]. unfold K4ScanState0Valid0.
  destruct kind; cbn; intros [HS HB].
  - exact (k4_low0_scan_next_t4 runs B H S D k HS HB).
  - exact (k4_low0_scan_next_t2 runs B H S D k HS HB).
Qed.

Lemma k4_low0_base_valid:
  K4ScanData P K4T2 k4_prebase_bits 382 2 378 4 ->
  K4ScanState0Valid0 k4_low0_base_state.
Proof.
  intros H. exact (k4_low0_prebase_to_base H).
Qed.

Lemma k4_low0_cycle
    (Hpre:K4ScanData P K4T2 k4_prebase_bits 382 2 378 4) n:
  K4ScanState0Valid0 (k4_scan_state0_iter n k4_low0_base_state).
Proof.
  induction n; cbn.
  - exact (k4_low0_base_valid Hpre).
  - apply k4_low0_state_step. exact IHn.
Qed.

Lemma k4_low0_cycle_height
    (Hpre:K4ScanData P K4T2 k4_prebase_bits 382 2 378 4) n:
  775+n <= k4s0_H (k4_scan_state0_iter n k4_low0_base_state).
Proof.
  induction n; cbn; lia.
Qed.

Lemma k4_low0_cycle_left_row
    (Hpre:K4ScanData P K4T2 k4_prebase_bits 382 2 378 4) n:
  exists b c d,
    P 0 b c d /\
    k4s0_H (k4_scan_state0_iter n k4_low0_base_state)
      <= c+2.
Proof.
  remember (k4_scan_state0_iter n k4_low0_base_state) as s.
  pose proof (k4_low0_cycle Hpre n) as [HS HB]. rewrite <-Heqs in HS,HB.
  pose proof (k4_scan_start_data P _ _ _ _ _ _ _ HS) as HD.
  destruct s as [kind runs B H S D k]. cbn in *.
  destruct kind; cbn [K4ScanData k4_gap] in HD,HB.
  - destruct HD as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase [Hdrop
      [RT [RF [Htail Hex]]]]]]]]]].
    cbn [k4_gap] in RT.
    destruct RT as [_ RT].
    exists (2*H+17),(H-2),25.
    split.
    + applys_eq (RT 0 (2*H+17)); try lia. exact (proj1 HB).
    + lia.
  - destruct HD as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase [Hdrop
      [RT [RF [Htail Hex]]]]]]]]]].
    cbn [k4_gap] in RF.
    destruct RF as [_ RF].
    exists (2*H+16),(H-1),22.
    split.
    + applys_eq (RF 0 (2*H+16)); try lia. exact (proj1 HB).
    + lia.
Qed.

Lemma k4_low0_cycle_left_row1
    (Hpre:K4ScanData P K4T2 k4_prebase_bits 382 2 378 4) n:
  exists b c d,
    P 1 b c d /\
    k4s0_H (k4_scan_state0_iter n k4_low0_base_state) <= c+2.
Proof.
  remember (k4_scan_state0_iter n k4_low0_base_state) as s.
  pose proof (k4_low0_cycle Hpre n) as [HS HB]. rewrite <-Heqs in HS,HB.
  pose proof (k4_scan_start_data P _ _ _ _ _ _ _ HS) as HD.
  destruct s as [kind runs B H S D k]. cbn in *.
  destruct kind; cbn [K4ScanData k4_gap] in HD,HB.
  - destruct HD as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase [Hdrop
      [RT [RF [Htail Hex]]]]]]]]]].
    cbn [k4_gap] in RT,RF.
    destruct RT as [_ RT]. destruct RF as [_ RF].
    destruct (nth 1 B false) eqn:E.
    + exists (2*H+15),(H-2),25. split.
      * applys_eq (RT 1 (2*H+15)); try assumption; lia.
      * lia.
    + exists (2*H+16),(H-2),26. split.
      * applys_eq (RF 1 (2*H+16)); try assumption; lia.
      * lia.
  - destruct HD as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase [Hdrop
      [RT [RF [Htail Hex]]]]]]]]]].
    cbn [k4_gap] in RT,RF.
    destruct RT as [_ RT]. destruct RF as [_ RF].
    destruct (nth 1 B false) eqn:E.
    + exists (2*H+13),(H-1),21. split.
      * applys_eq (RT 1 (2*H+13)); try assumption; lia.
      * lia.
    + exists (2*H+14),(H-1),22. split.
      * applys_eq (RF 1 (2*H+14)); try assumption; lia.
      * lia.
Qed.

End K4Low0Cycle.
