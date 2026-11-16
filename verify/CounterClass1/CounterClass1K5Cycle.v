Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles BusyCoq.CounterClass1.CounterClass1K4Words
  BusyCoq.CounterClass1.CounterClass1K5Common BusyCoq.CounterClass1.CounterClass1K5Words
  BusyCoq.CounterClass1.CounterClass1K5Phase BusyCoq.CounterClass1.CounterClass1K5Boundary.
Require Import Lia List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

Section K5Cycle.

Variable P:nat->nat->nat->nat->Prop.
Variable R:K5Rules P.

Lemma k5_scan_next kind runs B H S D k:
  K5ScanStart P kind runs B H S D k ->
  K5ScanStart P (k4_next_kind kind)
    (runs++[D+2;1;2*S+k+4])
    (k4_extend B (D+2) (2*S+k+4))
    (2*H+k+7) (2*S+k+4) (2*D-k-1) (k4_next_k kind k).
Proof.
  intros HS0. pose proof HS0 as HS.
  unfold K5ScanStart,K5ScanPayload in HS.
  destruct HS as [Hshape [Hbits [Hhead
    [Hheads [Hdrop [RT [RF [Htail Hend]]]]]]]].
  pose proof Hshape as Hshape0.
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast
    [Hhs [Hlarge [Hk Hs]]]]]]].
  pose proof (k5_scan_next_word P kind runs B H S D k HS0 Hheads) as HW.
  cbv zeta in HW.
  destruct HW as [Hshape' [Hbits' [Hhead' [Hheads' Hdrop']]]].
  assert (Hlen':length (k4_extend B (D+2) (2*S+k+4))=
      2*H+k+7+1).
  { destruct Hshape' as [_ [_ [Hsum' _]]].
    rewrite Hbits',k4_bits_length,Hsum'. reflexivity. }
  assert (Hmiddle:forall z,
      2*D-k-1-5<=z<=2*D-k-1+2 ->
      nth z (k4_extend B (D+2) (2*S+k+4)) false=true).
  { intros z Hz. eapply k5_scan_next_middle_true; [exact HS0|]. lia. }
  assert (Hlast':forall z,
      2*H+k+7+1-(2*S+k+4)<=z<2*H+k+7+1 ->
      nth z (k4_extend B (D+2) (2*S+k+4)) false=true).
  { intros z Hz. eapply k5_bits_last_true;
      [exact Hshape'|exact Hbits'|exact Hz]. }
  assert (HSp:3<=2*S+k+4) by lia.
  assert (HDp:12<=2*D-k-1) by lia.
  assert (Hpayload:K5ScanPayload P (k4_next_kind kind)
      (k4_extend B (D+2) (2*S+k+4))
      (2*H+k+7) (2*S+k+4) (2*D-k-1) (k4_next_k kind k)).
  { destruct kind.
    - eapply k5_end_t2_payload; try eassumption.
      exact (k5_scan_endfan_t4 P R runs B H S D k HS0).
    - eapply k5_end_t4_payload; try eassumption.
      exact (k5_scan_endfan_t2 P R runs B H S D k HS0). }
  exact (conj Hshape' (conj Hbits' (conj Hhead' Hpayload))).
Qed.

Record K5ScanState := {
  k5s_kind:K4Kind;
  k5s_runs:list nat;
  k5s_bits:list bool;
  k5s_H:nat;
  k5s_S:nat;
  k5s_D:nat;
  k5s_k:nat
}.

Definition k5_scan_state_step (s:K5ScanState) : K5ScanState :=
  {| k5s_kind:=k4_next_kind (k5s_kind s);
     k5s_runs:=k5s_runs s++[k5s_D s+2;1;2*k5s_S s+k5s_k s+4];
     k5s_bits:=k4_extend (k5s_bits s) (k5s_D s+2)
       (2*k5s_S s+k5s_k s+4);
     k5s_H:=2*k5s_H s+k5s_k s+7;
     k5s_S:=2*k5s_S s+k5s_k s+4;
     k5s_D:=2*k5s_D s-k5s_k s-1;
     k5s_k:=k4_next_k (k5s_kind s) (k5s_k s) |}.

Fixpoint k5_scan_state_iter (n:nat) (s:K5ScanState) : K5ScanState :=
  match n with
  | 0 => s
  | S n => k5_scan_state_step (k5_scan_state_iter n s)
  end.

Definition K5ScanStateValid (s:K5ScanState) : Prop :=
  K5ScanStart P (k5s_kind s) (k5s_runs s) (k5s_bits s)
    (k5s_H s) (k5s_S s) (k5s_D s) (k5s_k s).

Lemma k5_state_step s:
  K5ScanStateValid s -> K5ScanStateValid (k5_scan_state_step s).
Proof.
  destruct s as [kind runs B H S D k]. unfold K5ScanStateValid.
  exact (k5_scan_next kind runs B H S D k).
Qed.

Lemma k5_state_iter_valid s:
  K5ScanStateValid s -> forall n,
  K5ScanStateValid (k5_scan_state_iter n s).
Proof.
  intros Hs n. induction n; cbn; [exact Hs|].
  apply k5_state_step. exact IHn.
Qed.

Lemma k5_state_iter_height s n:
  k5s_H s+n<=k5s_H (k5_scan_state_iter n s).
Proof.
  induction n; cbn; lia.
Qed.

Lemma k5_state_row s x:
  K5ScanStateValid s -> x<=k5s_H s ->
  exists b c d, P x b c d /\ k5s_H s<=c+1.
Proof.
  destruct s as [kind runs B H S D k]. cbn.
  intros HS Hx. cbn in HS,Hx|-*.
  unfold K5ScanStateValid,K5ScanStart,K5ScanPayload in HS.
  cbn in HS.
  destruct HS as [Hshape [Hbits [Hhead
    [Hheads [Hdrop [RT [RF [Htail Hend]]]]]]]].
  destruct Hshape as [_ [_ [Hsum _]]].
  assert (Hlen:length B=H+1) by
    (rewrite Hbits,k4_bits_length,Hsum; reflexivity).
  destruct kind, (nth x B false) eqn:E; cbn [k5_scan_y k5_row_false_d] in *.
  - exists (2*H+13-2*x),H,18. split; [|lia].
    unfold K5Q in RT. apply (proj2 RT); [lia|exact E|lia].
  - exists (2*H+14-2*x),(H-1),21. split; [|lia].
    unfold K5Q in RF. apply (proj2 RF); [lia|exact E|lia].
  - exists (2*H+13-2*x),H,18. split; [|lia].
    unfold K5Q in RT. apply (proj2 RT); [lia|exact E|lia].
  - exists (2*H+14-2*x),H,19. split; [|lia].
    unfold K5Q in RF. apply (proj2 RF); [lia|exact E|lia].
Qed.

End K5Cycle.
