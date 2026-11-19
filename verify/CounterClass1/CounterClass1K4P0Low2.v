Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles
  BusyCoq.CounterClass1.CounterClass1K4Words BusyCoq.CounterClass1.CounterClass1K4Phase BusyCoq.CounterClass1.CounterClass1K4Boundary
  BusyCoq.CounterClass1.CounterClass1K4Cycle BusyCoq.CounterClass1.CounterClass1K4P0.
Require Import Lia List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

Section K4P0Low2.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable P0: nat -> nat -> Prop.
Variable C: K4ComplexRules P K4Low2.
Variable R0: K4P0Rules P P0.
Let R:=k4c_simple C.

Lemma k4_low2_type4_align B H S D:
  2<=H -> length B=H+1 -> nth H B false=true ->
  nth (H-1) B false=true ->
  K4Type4Front P B H S D -> P (H+2) 4 (H+1) 10 ->
  P0 (H+4) 2 -> P0 (H-2) 26.
Proof.
  intros HH Hlen BH BHm [Hhs [RT [RF [E1 [E2 [E3 [E4 E5]]]]]]]
    A HP0.
  destruct RT as [dt [Hdt RT]]. destruct RF as [df [Hdf RF]].
  assert (dt=11) by lia. assert (df=14) by lia. subst dt df.
  assert (TH: P H 9 (H+1) 11) by
    (apply RT; try assumption; lia).
  assert (THm: P (H-1) 11 (H+1) 11) by
    (apply RT; try assumption; lia).
  assert (C10: P (H+1) 10 H 16) by
    (applys_eq (k4_rov' R (H+1) 8 (H+1) 8 H 12); try lia;
      applys_eq E1; lia).
  assert (H11: P H 11 (H+1) 13) by
    (applys_eq (k4_rov R H 9 (H+1) 8 (H+1) 12); try lia; assumption).
  assert (H13: P H 13 H 17) by
    (applys_eq (k4_rov R H 11 (H+1) 10 H 16); try lia; assumption).
  assert (Hm13: P (H-1) 13 (H+1) 13) by
    (applys_eq (k4_rov R (H-1) 11 (H+1) 8 (H+1) 12);
      try lia; assumption).
  assert (Hm15: P (H-1) 15 H 17) by
    (applys_eq (k4_rov R (H-1) 13 (H+1) 10 H 16);
      try lia; assumption).
  assert (Hm17: P (H-1) 17 (H-1) 21) by
    (applys_eq (k4_rov' R (H-1) 15 H 13 (H-1) 17);
      try lia; [exact Hm15|applys_eq H13; lia]).
  assert (Hm19: P (H-1) 19 (H-2) 25).
  { applys_eq (k4_rov' R (H-1) 17 (H-1) 17 (H-2) 21); try lia.
    - exact Hm17.
    - applys_eq Hm17; lia. }
  assert (P1: P0 (H+2) 8) by
    (applys_eq (k4p0_inc00_2 R0 (H+2)); try lia; applys_eq HP0; lia).
  assert (P2: P0 H 14) by
    (applys_eq (k4p0_ov' R0 (H+2) 4 H 10); try lia;
      [exact P1|applys_eq A; lia]).
  assert (P3: P0 (H+1) 14) by
    (applys_eq (k4p0_ov R0 H 11 (H+1) 13); try lia; assumption).
  assert (P4: P0 (H-1) 20) by
    (applys_eq (k4p0_ov' R0 (H+1) 10 (H-1) 16); try lia;
      [applys_eq P3; lia|applys_eq C10; lia]).
  assert (P5: P0 (H-1) 22) by
    (applys_eq (k4p0_ov R0 (H-1) 17 (H-1) 21); try lia; assumption).
  applys_eq (k4p0_ov R0 (H-1) 19 (H-2) 25 P5 Hm19); lia.
Qed.

Lemma k4_low2_type2_align B H S D:
  2<=H -> length B=H+1 -> nth H B false=true ->
  D<length B -> D<>H-1 -> nth D B false=true ->
  K4Type2Front P B H S D ->
  P0 (H+3) 1 -> P0 (H-1) 21.
Proof.
  intros HH Hlen BH HDl HDn BD
    [Hhs [RF [E1 [E2 [E3 [RT Dent]]]]]] HP0.
  destruct RT as [dt [Hdt RT]]. assert (dt=7) by lia. subst dt.
  assert (A: P (H+2) 4 (H+1) 10) by
    (applys_eq (k4_rov' R (H+2) 2 (H+2) 2 (H+1) 6); try lia;
      applys_eq E2; lia).
  assert (TH: P H 9 (H+1) 11).
  { applys_eq (k4_rov R H 7 (H+2) 4 (H+1) 10); try lia.
    - apply RT; try assumption; lia.
    - exact A. }
  assert (B1: P (H+1) 6 H 12) by
    (applys_eq (k4_rov' R (H+1) 4 (H+1) 4 H 8); try lia;
      applys_eq E1; lia).
  assert (B2: P (H+1) 8 (H+1) 12) by
    (applys_eq (k4_rov R (H+1) 6 H 9 (H+1) 11); try lia; assumption).
  assert (B3: P (H+1) 10 H 16) by
    (applys_eq (k4_rov' R (H+1) 8 (H+1) 8 H 12); try lia;
      applys_eq B2; lia).
  assert (H11: P H 11 (H+1) 13) by
    (applys_eq (k4_rov R H 9 (H+1) 8 (H+1) 12); try lia; assumption).
  assert (H13: P H 13 H 17) by
    (applys_eq (k4_rov R H 11 (H+1) 10 H 16); try lia; assumption).
  assert (P1: P0 (H+2) 5) by
    (applys_eq (k4p0_inc00_1 R0 (H+2)); try lia; applys_eq HP0; lia).
  assert (P2: P0 (H+2) 7) by
    (applys_eq (k4p0_ov R0 (H+2) 2 (H+2) 6); try lia; assumption).
  assert (P3: P0 (H+1) 11) by
    (applys_eq (k4p0_ov R0 (H+2) 4 (H+1) 10); try lia; assumption).
  assert (P4: P0 (H+1) 13) by
    (applys_eq (k4p0_ov R0 (H+1) 8 (H+1) 12); try lia; assumption).
  assert (P5: P0 H 17) by
    (applys_eq (k4p0_ov R0 (H+1) 10 H 16); try lia; assumption).
  applys_eq (k4p0_ov' R0 H 13 (H-1) 17); try lia.
  - exact P5.
  - applys_eq H13; lia.
Qed.

(* The one fact used before the ordinary T4 prefix is retained here rather
   than bloating [K4ScanPayload]: it is made locally from the preceding
   end-fan and consumed immediately by [k4_low2_type4_align]. *)
Lemma k4_low2_end_t4_entry B H S D:
  3<=S -> length B=H+1 -> nth 0 B false=true ->
  nth (D+1) B false=true ->
  K4EndFan P K4T4 B H S D -> P (H+2) 4 (H+1) 10.
Proof.
  intros HS Hlen B0 BD1
    [Hhs [RF [Z [RT [EH [EHm ED4]]]]]].
  assert (ZT: P 0 (2*H) 0 (2*H+4)) by
    (apply RT; try assumption; try lia; discriminate).
  assert (TD1: P (D+1) (4*S-2) 0 (2*H+4)) by
    (apply RT; try assumption; try lia; discriminate).
  assert (C1: P (H+1) 0 (D+2) (4*S+2)) by
    (applys_eq (k4_inc01 R H (D+2) (4*S-2)); try lia;
      applys_eq EH; lia).
  assert (C2: P (H+2) 0 (D+1) (4*S+6)) by
    (applys_eq (k4_inc01 R (H+1) (D+1) (4*S+2)); try lia;
      applys_eq C1; lia).
  assert (L1: P (D+1) (4*S+1) (H+3) 1).
  { applys_eq (k4c_lov1' C (D+1) (4*S-2) 0 (2*H) (H+2));
      try lia.
    - applys_eq TD1; lia.
    - applys_eq ZT; lia. }
  assert (I1: P (D+1) (4*S+3) (H+2) 5) by
    (applys_eq (k4_inc00_1 R (D+1) (4*S+1) (H+2));
      try lia; applys_eq L1; lia).
  assert (E2: P (H+2) 2 (H+2) 6) by
    (applys_eq (k4_rov R (H+2) 0 (D+1) (4*S+3) (H+2) 5);
      try lia; [applys_eq C2; lia|exact I1]).
  applys_eq (k4_rov' R (H+2) 2 (H+2) 2 (H+1) 6);
    try lia; [exact E2|applys_eq E2; lia].
Qed.

Lemma k4_low2_scan_next_t4_p0 runs B H S D k:
  K4ScanStart P K4T4 runs B H S D k -> K4HeadBits K4T4 B ->
  P0 (H-2) 26 ->
  let runsp:=runs++[D+3;1;2*S+k+3] in
  let Bp:=k4_extend B (D+3) (2*S+k+3) in
  let Hp:=2*H+k+7 in
  let Sp:=2*S+k+3 in
  let Dp:=2*D+1-k in
  K4ScanStart P K4T2 runsp Bp Hp Sp Dp (k+1) /\
  K4HeadBits K4T2 Bp /\ P0 (Hp-1) 21.
Proof.
  intros HS HB HP0. cbv zeta.
  destruct (k4_low2_scan_next_t4 P C runs B H S D k HS HB) as [HS' HB'].
  pose proof (k4_scan_next_word P K4T4 runs B H S D k HS HB) as HW.
  cbv zeta in HW.
  destruct HW as [Hshape [Hbits [Hhead [Hheadbits Hdrop]]]].
  pose proof Hshape as Hshape0.
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast
    [Hhs [Hlarge [Hkp Hsp]]]]]]].
  assert (Hlen: length (k4_extend B (D+3) (2*S+k+3))=2*H+k+8).
  { rewrite Hbits,k4_bits_length,Hsum. lia. }
  assert (BH: nth (2*H+k+7) (k4_extend B (D+3) (2*S+k+3))
      false=true) by
    (eapply k4_bits_last_true; [exact Hshape0|exact Hbits|lia]).
  assert (Hwin: forall z, 2*D+1-k-4<=z<=2*D+1-k+3 ->
      nth z (k4_extend B (D+3) (2*S+k+3)) false=true).
  { intros z Hz.
    replace z with (2*D+1-k-7+(z-(2*D+1-k-7))) by lia.
    apply k4_scan_next_middle_window with
      (P:=P) (kind:=K4T4) (runs:=runs) (H:=H) (S:=S) (D:=D) (k:=k);
      assumption || lia. }
  pose proof (k4_scan_endfan_t4_data P R B H S D k
    (k4_scan_start_data P K4T4 runs B H S D k HS) HB) as HE.
  assert (HF: K4Type2Front P (k4_extend B (D+3) (2*S+k+3))
      (2*H+k+7) (2*S+k+3) (2*D+1-k)).
  { apply (k4_low2_end_t2_front P C); try assumption; try lia;
      try exact (proj1 HB'); apply Hwin; lia. }
  assert (HR: P0 (2*H+k+10) 1).
  { apply (k4_p0_scan_t4_reset P P0 R R0 B H S D k); try assumption.
    exact (k4_scan_start_data P K4T4 runs B H S D k HS). }
  split; [exact HS'|]. split; [exact HB'|].
  eapply (k4_low2_type2_align (k4_extend B (D+3) (2*S+k+3))
    (2*H+k+7) (2*S+k+3) (2*D+1-k)).
  - lia.
  - applys_eq Hlen; lia.
  - exact BH.
  - lia.
  - lia.
  - apply Hwin; lia.
  - exact HF.
  - applys_eq HR; lia.
Qed.

Lemma k4_low2_scan_next_t2_p0 runs B H S D k:
  K4ScanStart P K4T2 runs B H S D k -> K4HeadBits K4T2 B ->
  P0 (H-1) 21 ->
  let runsp:=runs++[D+3;1;2*S+k+3] in
  let Bp:=k4_extend B (D+3) (2*S+k+3) in
  let Hp:=2*H+k+7 in
  let Sp:=2*S+k+3 in
  let Dp:=2*D+1-k in
  K4ScanStart P K4T4 runsp Bp Hp Sp Dp (k+2) /\
  K4HeadBits K4T4 Bp /\ P0 (Hp-2) 26.
Proof.
  intros HS HB HP0. cbv zeta.
  destruct (k4_low2_scan_next_t2 P C runs B H S D k HS HB) as [HS' HB'].
  pose proof (k4_scan_next_word P K4T2 runs B H S D k HS HB) as HW.
  cbv zeta in HW.
  destruct HW as [Hshape [Hbits [Hhead [Hheadbits Hdrop]]]].
  pose proof Hshape as Hshape0.
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast
    [Hhs [Hlarge [Hkp Hsp]]]]]]].
  assert (Hlen: length (k4_extend B (D+3) (2*S+k+3))=2*H+k+8).
  { rewrite Hbits,k4_bits_length,Hsum. lia. }
  assert (BH: nth (2*H+k+7) (k4_extend B (D+3) (2*S+k+3))
      false=true) by
    (eapply k4_bits_last_true; [exact Hshape0|exact Hbits|lia]).
  assert (BHm: nth (2*H+k+7-1) (k4_extend B (D+3) (2*S+k+3))
      false=true) by
    (eapply k4_bits_last_true; [exact Hshape0|exact Hbits|lia]).
  assert (Hwin: forall z, 2*D+1-k-5<=z<=2*D+1-k+3 ->
      nth z (k4_extend B (D+3) (2*S+k+3)) false=true).
  { intros z Hz.
    replace z with (2*D+1-k-7+(z-(2*D+1-k-7))) by lia.
    apply k4_scan_next_middle_window with
      (P:=P) (kind:=K4T2) (runs:=runs) (H:=H) (S:=S) (D:=D) (k:=k);
      assumption || lia. }
  pose proof (k4_scan_endfan_t2_data P R B H S D k
    (k4_scan_start_data P K4T2 runs B H S D k HS) HB) as HE.
  assert (HF: K4Type4Front P (k4_extend B (D+3) (2*S+k+3))
      (2*H+k+7) (2*S+k+3) (2*D+1-k)).
  { apply (k4_low2_end_t4_front P C); try assumption; try lia;
      try exact (proj1 HB'); apply Hwin; lia. }
  assert (HA: P (2*H+k+7+2) 4 (2*H+k+7+1) 10).
  { apply (k4_low2_end_t4_entry (k4_extend B (D+3) (2*S+k+3))
      (2*H+k+7) (2*S+k+3) (2*D+1-k)); try assumption; try lia.
    - exact (proj1 HB').
    - apply Hwin; lia. }
  assert (HR: P0 (2*H+k+11) 2).
  { apply (k4_p0_scan_t2_reset P P0 R R0 B H S D k); try assumption.
    exact (k4_scan_start_data P K4T2 runs B H S D k HS). }
  split; [exact HS'|]. split; [exact HB'|].
  eapply (k4_low2_type4_align (k4_extend B (D+3) (2*S+k+3))
    (2*H+k+7) (2*S+k+3) (2*D+1-k)).
  - lia.
  - applys_eq Hlen; lia.
  - exact BH.
  - exact BHm.
  - exact HF.
  - applys_eq HA; lia.
  - applys_eq HR; lia.
Qed.

Definition K4P0Aligned (kind:K4Kind) (H:nat) : Prop :=
  match kind with
  | K4T4 => P0 (H-2) 26
  | K4T2 => P0 (H-1) 21
  end.

Definition K4P0StateValid (s:K4ScanState) : Prop :=
  K4ScanStateValid P s /\ K4P0Aligned (k4s_kind s) (k4s_H s).

Lemma k4_low2_p0_state_step s:
  K4P0StateValid s -> K4P0StateValid (k4_scan_state_step s).
Proof.
  destruct s as [kind runs B H S D k].
  unfold K4P0StateValid,K4ScanStateValid,K4P0Aligned.
  destruct kind; cbn; intros [[HS HB] HP0].
  - destruct (k4_low2_scan_next_t4_p0 runs B H S D k HS HB HP0)
      as [HS' [HB' HP']]. split; [split; assumption|exact HP'].
  - destruct (k4_low2_scan_next_t2_p0 runs B H S D k HS HB HP0)
      as [HS' [HB' HP']]. split; [split; assumption|exact HP'].
Qed.

Lemma k4_low2_p0_base:
  K4ScanData P K4T2 k4_prebase_bits 382 2 378 4 ->
  P0 381 21 -> K4P0StateValid k4_low2_base_state.
Proof.
  intros HD HP0. split; [exact (k4_low2_base_valid P C HD)|].
  cbn [K4P0Aligned].
  pose proof (k4_p0_scan_t2_reset P P0 R R0 k4_prebase_bits
    382 2 378 4 HD k4_prebase_head_bits HP0) as HR.
  pose proof (k4_scan_endfan_t2_data P R k4_prebase_bits
    382 2 378 4 HD k4_prebase_head_bits) as HE.
  destruct k4_base_boundary_bits as [Hlen [BH [BHm Hwin]]].
  assert (HF: K4Type4Front P k4_base_bits 775 11 753).
  { apply (k4_low2_end_t4_front P C); try assumption; try lia;
      try exact (proj1 k4_base_head_bits); apply Hwin; lia. }
  assert (HA: P 777 4 776 10).
  { apply (k4_low2_end_t4_entry k4_base_bits 775 11 753).
    - lia.
    - exact Hlen.
    - exact (proj1 k4_base_head_bits).
    - apply Hwin; lia.
    - exact HE. }
  eapply (k4_low2_type4_align k4_base_bits 775 11 753).
  - lia.
  - exact Hlen.
  - exact BH.
  - exact BHm.
  - exact HF.
  - exact HA.
  - applys_eq HR; lia.
Qed.

Lemma k4_low2_p0_cycle
    (HD:K4ScanData P K4T2 k4_prebase_bits 382 2 378 4)
    (HP0:P0 381 21) n:
  K4P0StateValid (k4_scan_state_iter n k4_low2_base_state).
Proof.
  induction n; cbn.
  - exact (k4_low2_p0_base HD HP0).
  - apply k4_low2_p0_state_step. exact IHn.
Qed.

Lemma k4_low2_p0_cycle_config
    (HD:K4ScanData P K4T2 k4_prebase_bits 382 2 378 4)
    (HP0:P0 381 21) n:
  exists a b, P0 a b /\
    k4s_H (k4_scan_state_iter n k4_low2_base_state)<=a+b.
Proof.
  pose proof (k4_low2_p0_cycle HD HP0 n) as [_ HA].
  remember (k4_scan_state_iter n k4_low2_base_state) as s.
  destruct s as [kind runs B height S D k]. cbn in *.
  destruct kind; cbn [K4P0Aligned] in HA.
  - exists (height-2),26. split; assumption || lia.
  - exists (height-1),21. split; assumption || lia.
Qed.

End K4P0Low2.
