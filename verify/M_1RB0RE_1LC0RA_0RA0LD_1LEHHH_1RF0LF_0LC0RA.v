(* 1RB0RE_1LC0RA_0RA0LD_1LE---_1RF0LF_0LC0RA never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import String Bool Lists.List Lia ZifyNat PeanoNat.
Import ListNotations.

Open Scope list.
Open Scope sym.
Open Scope nat_scope.

Definition tm := Eval compute in
  (TM_from_str "1RB0RE_1LC0RA_0RA0LD_1LE---_1RF0LF_0LC0RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma pev {c1 c2 : Q * tape} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Ltac pose_div2 x :=
  let H1 := fresh "Hdiv" in
  let H2 := fresh "Hmod" in
  assert (H1 : x = 2 * (x / 2) + x mod 2) by (apply Nat.div_mod; lia);
  assert (H2 : x mod 2 < 2) by (apply Nat.mod_upper_bound; lia).

Ltac omega_div :=
  repeat match goal with
  | |- context [?x / 2] =>
    lazymatch goal with
    | H : x = 2 * (x / 2) + x mod 2 |- _ => fail
    | _ => pose_div2 x
    end
  | H : context [?x / 2] |- _ =>
    lazymatch goal with
    | H' : x = 2 * (x / 2) + x mod 2 |- _ => fail
    | _ => pose_div2 x
    end
  end;
  lia.

(* ========================================================================== *)
(* Mode Configurations & 16 Micro-Step Transition Lemmas                      *)
(* ========================================================================== *)

Definition cfg_h01B (w s : side) : Q * tape :=
  w <{{E}} (1%sym >> 0%sym >> s).

Definition cfg_modeB (w s : side) : Q * tape :=
  (1%sym >> 0%sym >> w) {{B}}> s.

Definition cfg_modeF (w s : side) : Q * tape :=
  (1%sym >> 0%sym >> w) {{F}}> s.

Lemma step_init_to_h01B :
  c0 -->+ cfg_h01B 0inf%sym (1%sym >> 0inf%sym).
Proof.
  unfold c0, tape0, cfg_h01B; simpl; start_progress.
Qed.

Lemma step_h01B_nil (s : side) :
  cfg_h01B 0inf%sym s -->+
    cfg_modeB (1%sym >> 0%sym >> 0%sym >> 0inf%sym) s.
Proof.
  unfold cfg_h01B, cfg_modeB; simpl; repeat rewrite <- const_unfold; start_progress.
Qed.

Lemma step_h01B_010 (w s : side) :
  cfg_h01B (0%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_modeB (1%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_h01B, cfg_modeB; simpl; start_progress. Qed.

Lemma step_h01B_0010 (w s : side) :
  cfg_h01B (0%sym >> 0%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_modeB (1%sym >> 0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_h01B, cfg_modeB; simpl; start_progress. Qed.

Lemma step_h01B_0110 (w s : side) :
  cfg_h01B (0%sym >> 1%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_modeB (1%sym >> 1%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_h01B, cfg_modeB; simpl; start_progress. Qed.

Lemma step_h01B_110 (w s : side) :
  cfg_h01B (1%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_modeB (1%sym >> 0%sym >> 0%sym >> w) s.
Proof. unfold cfg_h01B, cfg_modeB; simpl; start_progress. Qed.

Lemma step_h01B_1110 (w s : side) :
  cfg_h01B (1%sym >> 1%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_modeB (1%sym >> 0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_h01B, cfg_modeB; simpl; start_progress. Qed.

Lemma step_h01B_100 (w s : side) :
  cfg_h01B (1%sym >> 0%sym >> 0%sym >> w) s -->+
    cfg_h01B w (1%sym >> 1%sym >> 0%sym >> s).
Proof. unfold cfg_h01B; simpl; start_progress. Qed.

Lemma step_h01B_1010 (w s : side) :
  cfg_h01B (1%sym >> 0%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_h01B w (0%sym >> 0%sym >> 1%sym >> 0%sym >> s).
Proof. unfold cfg_h01B; simpl; start_progress. Qed.

Lemma step_modeB_base (w : side) :
  cfg_modeB w (1%sym >> 0inf%sym) -->+
    cfg_h01B (1%sym >> 0%sym >> w) (1%sym >> 0inf%sym).
Proof. unfold cfg_modeB, cfg_h01B; simpl; start_progress. Qed.

Lemma step_modeB_0100 (w s : side) :
  cfg_modeB w (0%sym >> 0%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_h01B w (1%sym >> 0%sym >> 1%sym >> 0%sym >> s).
Proof. unfold cfg_modeB, cfg_h01B; simpl; start_progress. Qed.

Lemma step_modeB_0101 (w s : side) :
  cfg_modeB w (1%sym >> 0%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_modeB (1%sym >> 0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_modeB; simpl; start_progress. Qed.

Lemma step_modeB_011 (w s : side) :
  cfg_modeB w (1%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_modeF (0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_modeB, cfg_modeF; simpl; start_progress. Qed.

Lemma step_modeF_0100 (w s : side) :
  cfg_modeF w (0%sym >> 0%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_h01B w (0%sym >> 0%sym >> 1%sym >> 0%sym >> s).
Proof. unfold cfg_modeF, cfg_h01B; simpl; start_progress. Qed.

Lemma step_modeF_0101 (w s : side) :
  cfg_modeF w (1%sym >> 0%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_modeB (1%sym >> 0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_modeF, cfg_modeB; simpl; start_progress. Qed.

Lemma step_modeF_011 (w s : side) :
  cfg_modeF w (1%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_modeF (0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_modeF; simpl; start_progress. Qed.

(* ========================================================================== *)
(* Symbolic Token Lists (WTok, STok) & Shift Algebra                          *)
(* ========================================================================== *)

Inductive WTok : Type :=
  | W010
  | W0010
  | W0110
  | W100
  | W110
  | W1010
  | W1110.

Inductive STok : Type :=
  | T0100
  | T0101
  | T011.

Fixpoint evalW (L : list WTok) : side :=
  match L with
  | [] => 0inf%sym
  | W010 :: L' => 0%sym >> 1%sym >> 0%sym >> evalW L'
  | W0010 :: L' => 0%sym >> 0%sym >> 1%sym >> 0%sym >> evalW L'
  | W0110 :: L' => 0%sym >> 1%sym >> 1%sym >> 0%sym >> evalW L'
  | W100 :: L' => 1%sym >> 0%sym >> 0%sym >> evalW L'
  | W110 :: L' => 1%sym >> 1%sym >> 0%sym >> evalW L'
  | W1010 :: L' => 1%sym >> 0%sym >> 1%sym >> 0%sym >> evalW L'
  | W1110 :: L' => 1%sym >> 1%sym >> 1%sym >> 0%sym >> evalW L'
  end.

Fixpoint evalS (S : list STok) : side :=
  match S with
  | [] => 1%sym >> 0inf%sym
  | T0100 :: S' => 0%sym >> 0%sym >> 1%sym >> 0%sym >> evalS S'
  | T0101 :: S' => 1%sym >> 0%sym >> 1%sym >> 0%sym >> evalS S'
  | T011 :: S' => 1%sym >> 1%sym >> 0%sym >> evalS S'
  end.

Lemma sym_h01B_nil (S : list STok) :
  cfg_h01B (evalW []) (evalS S) -->+ cfg_modeB (evalW [W100]) (evalS S).
Proof. exact (step_h01B_nil (evalS S)). Qed.

Lemma sym_h01B_010 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W010 :: L)) (evalS S) -->+ cfg_modeB (evalW (W110 :: L)) (evalS S).
Proof. exact (step_h01B_010 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_0010 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W0010 :: L)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: L)) (evalS S).
Proof. exact (step_h01B_0010 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_0110 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W0110 :: L)) (evalS S) -->+ cfg_modeB (evalW (W1110 :: L)) (evalS S).
Proof. exact (step_h01B_0110 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_110 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W110 :: L)) (evalS S) -->+ cfg_modeB (evalW (W100 :: L)) (evalS S).
Proof. exact (step_h01B_110 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_1110 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W1110 :: L)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: L)) (evalS S).
Proof. exact (step_h01B_1110 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_100 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W100 :: L)) (evalS S) -->+ cfg_h01B (evalW L) (evalS (T011 :: S)).
Proof. exact (step_h01B_100 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_1010 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W1010 :: L)) (evalS S) -->+ cfg_h01B (evalW L) (evalS (T0100 :: S)).
Proof. exact (step_h01B_1010 (evalW L) (evalS S)). Qed.

Lemma sym_modeB_0100 (L : list WTok) (S : list STok) :
  cfg_modeB (evalW L) (evalS (T0100 :: S)) -->+ cfg_h01B (evalW L) (evalS (T0101 :: S)).
Proof. exact (step_modeB_0100 (evalW L) (evalS S)). Qed.

Lemma sym_modeB_0101 (L : list WTok) (S : list STok) :
  cfg_modeB (evalW L) (evalS (T0101 :: S)) -->+ cfg_modeB (evalW (W1010 :: L)) (evalS S).
Proof. exact (step_modeB_0101 (evalW L) (evalS S)). Qed.

Lemma sym_modeB_011 (L : list WTok) (S : list STok) :
  cfg_modeB (evalW L) (evalS (T011 :: S)) -->+ cfg_modeF (evalW (W010 :: L)) (evalS S).
Proof. exact (step_modeB_011 (evalW L) (evalS S)). Qed.

Lemma sym_modeF_0100 (L : list WTok) (S : list STok) :
  cfg_modeF (evalW L) (evalS (T0100 :: S)) -->+ cfg_h01B (evalW L) (evalS (T0100 :: S)).
Proof. exact (step_modeF_0100 (evalW L) (evalS S)). Qed.

Lemma sym_modeF_0101 (L : list WTok) (S : list STok) :
  cfg_modeF (evalW L) (evalS (T0101 :: S)) -->+ cfg_modeB (evalW (W1010 :: L)) (evalS S).
Proof. exact (step_modeF_0101 (evalW L) (evalS S)). Qed.

Lemma sym_modeF_011 (L : list WTok) (S : list STok) :
  cfg_modeF (evalW L) (evalS (T011 :: S)) -->+ cfg_modeF (evalW (W010 :: L)) (evalS S).
Proof. exact (step_modeF_011 (evalW L) (evalS S)). Qed.

(* ========================================================================== *)
(* Shift Algebra, Demand/Potential Bounds                                     *)
(* ========================================================================== *)

Fixpoint shift (b : bool) (u : list WTok) {struct u} : list WTok :=
  match b, u with
  | true, [] => [W100]
  | true, W0010 :: m => W100 :: W010 :: m
  | true, W0110 :: m => W100 :: W110 :: m
  | true, W010 :: m => W100 :: shift true m
  | true, W1010 :: m => W1010 :: shift true m
  | true, W100 :: m => W1010 :: shift false m
  | true, W110 :: m => W110 :: m
  | true, W1110 :: m => W1110 :: m
  | false, [] => []
  | false, W010 :: m => W0010 :: m
  | false, W110 :: m => W0110 :: m
  | false, W100 :: m => W010 :: shift false m
  | false, W1010 :: m => W010 :: shift true m
  | false, W0010 :: m => W0010 :: m
  | false, W0110 :: m => W0110 :: m
  | false, W1110 :: m => W1110 :: m
  end.

Definition isHigh (u : list WTok) : bool :=
  match u with
  | W1010 :: _ | W0010 :: _ | W1110 :: _ | W0110 :: _ => true
  | _ => false
  end.

Fixpoint dem (b : bool) (u : list WTok) {struct u} : nat :=
  match b, u with
  | false, [] => 0
  | true, [] => 3
  | _, W1010 :: m => (dem true m + 1) / 2
  | _, W0010 :: m => (dem true m + 1) / 2 + 1
  | _, W1110 :: m => (dem true m + 1) / 2 + 1
  | _, W0110 :: m => (dem true m + 1) / 2 + 2
  | true, W100 :: m => 2 * dem false m
  | true, W010 :: m => 2 * dem false m + 1
  | true, W110 :: m => Nat.max 3 (2 * dem false m + 2)
  | false, W010 :: m => 3 * dem false m
  | false, W110 :: m => 3 * dem false m - 1
  | false, W100 :: m => 3 * dem false m - 2
  end.

Fixpoint potF (b : bool) (u : list WTok) {struct u} : nat :=
  match b, u with
  | false, [] => 2
  | true, [] => 4
  | _, W1010 :: m => (potF true m + 4) / 2
  | _, W0010 :: m => (potF true m + 4) / 2
  | _, W1110 :: m => (potF true m + 4) / 2
  | _, W0110 :: m => (potF true m + 4) / 2
  | true, W010 :: m => 2 * potF false m + 1
  | true, W100 :: m => 2 * potF false m + 2
  | true, W110 :: m => 2 * potF false m + 3
  | false, W010 :: m => Nat.max 3 (3 * potF false m - 5)
  | false, W110 :: m => Nat.max 3 (3 * potF false m - 4)
  | false, W100 :: m => 3 * potF false m - 3
  end.

Local Opaque Nat.div Nat.max.

Lemma evalW_shift : forall (b : bool) (u : list WTok),
  dem b u = 0 ->
  evalW (shift b u) =
    (if b then 1%sym >> 0%sym >> evalW u else 0%sym >> evalW u).
Proof.
  intros b u; revert b.
  induction u as [| t m IH]; intros [|] H.
  - simpl in H; discriminate.
  - simpl; apply const_unfold.
  - destruct t; simpl in H |- *; try reflexivity; try omega_div.
    + assert (Hm : dem false m = 0) by omega_div.
      rewrite (IH false Hm); reflexivity.
    + assert (Hm : dem true m = 0) by omega_div.
      rewrite (IH true Hm); reflexivity.
  - destruct t; simpl in H |- *; try reflexivity; try omega_div.
    + assert (Hm : dem false m = 0) by omega_div.
      rewrite (IH false Hm); reflexivity.
    + assert (Hm : dem true m = 0) by omega_div.
      rewrite (IH true Hm); reflexivity.
Qed.

Lemma potF_ge (u : list WTok) : potF false u >= 2 /\ potF true u >= 4.
Proof.
  induction u as [| t m [IHf IHt]]; [simpl; lia |].
  destruct t; simpl; split; omega_div.
Qed.

Lemma potF_true_le (u : list WTok) : potF true u <= 2 * potF false u + 3.
Proof.
  destruct u as [| t m]; [simpl; lia |].
  destruct (potF_ge m) as [HpF HpT].
  destruct t; simpl; omega_div.
Qed.

Lemma dem_true_of_dem_false_zero {u : list WTok} (H : dem false u = 0) :
  dem true u <= 3.
Proof.
  destruct u as [| t m]; [simpl; lia |].
  destruct t; simpl in H |- *; omega_div.
Qed.

Lemma isHigh_shift_true {u : list WTok} (H : dem true u = 0) :
  isHigh (shift true u) = true.
Proof.
  destruct u as [| t m]; [simpl in H; discriminate |].
  destruct t; simpl in H |- *; try reflexivity; omega_div.
Qed.

Lemma shift_false_true_le {m : list WTok} (Hm : dem false m = 0)
    (IHf2 : potF false (shift false m) <= 3 * potF false m - 4) :
  3 * dem true (shift false m) <= 2 * dem false (shift false m) + 9 /\
  potF true (shift false m) <= 2 * potF false m + 2.
Proof.
  destruct m as [| t n]; [simpl; lia |].
  destruct (potF_ge n) as [HpF HpT].
  pose proof (potF_true_le n) as Hptle.
  destruct t.
  - (* W010 *)
    assert (Hn : dem false n = 0) by (simpl in Hm; omega_div).
    pose proof (dem_true_of_dem_false_zero Hn) as Hdt.
    simpl; split; omega_div.
  - (* W0010 *) simpl in Hm; omega_div.
  - (* W0110 *) simpl in Hm; omega_div.
  - (* W100 *)
    simpl in IHf2 |- *.
    revert IHf2; generalize (shift false n); intros s IHf2.
    simpl in IHf2 |- *.
    split; omega_div.
  - (* W110 *)
    assert (Hn : dem false n = 0) by (simpl in Hm; omega_div).
    pose proof (dem_true_of_dem_false_zero Hn) as Hdt.
    simpl; split; omega_div.
  - (* W1010 *)
    simpl in IHf2 |- *.
    revert IHf2; generalize (shift true n); intros s IHf2.
    simpl in IHf2 |- *.
    split; omega_div.
  - (* W1110 *) simpl in Hm; omega_div.
Qed.

Lemma shift_true_false_eq {m : list WTok} (H : dem true m = 0) :
  dem false (shift true m) = dem true (shift true m) /\
  potF false (shift true m) = potF true (shift true m).
Proof.
  destruct m as [| t n]; [simpl in H; discriminate |].
  destruct t; simpl in H |- *; try (split; reflexivity); omega_div.
Qed.

Lemma shift_bounds (u : list WTok) :
  (dem false u = 0 ->
    2 * dem false (shift false u) <= 6 * potF false u - 9 /\
    potF false (shift false u) <= 3 * potF false u - 4) /\
  (dem true u = 0 ->
    2 * dem true (shift true u) <= potF true u - 2 /\
    potF true (shift true u) <= (potF true u + 4) / 2).
Proof.
  induction u as [| t m [IHf IHt]].
  - split; intro H; [simpl; lia | simpl in H; discriminate].
  - destruct (potF_ge m) as [HpF HpT].
    pose proof (potF_true_le m) as Hptle.
    destruct t.
    + (* W010 *)
      split; intro H.
      * assert (Hm : dem false m = 0) by (simpl in H; omega_div).
        pose proof (dem_true_of_dem_false_zero Hm) as Hdt.
        simpl; split; omega_div.
      * simpl in H; omega_div.
    + (* W0010 *)
      split; intro H; simpl in H; omega_div.
    + (* W0110 *)
      split; intro H; simpl in H; omega_div.
    + (* W100 *)
      split; intro H.
      * assert (Hm : dem false m = 0) by (simpl in H; omega_div).
        destruct (IHf Hm) as [IHf1 IHf2].
        simpl; split; omega_div.
      * assert (Hm : dem false m = 0) by (simpl in H; omega_div).
        destruct (IHf Hm) as [IHf1 IHf2].
        destruct (shift_false_true_le Hm IHf2) as [Hsf1 Hsf2].
        simpl; split; omega_div.
    + (* W110 *)
      split; intro H.
      * assert (Hm : dem false m = 0) by (simpl in H; omega_div).
        pose proof (dem_true_of_dem_false_zero Hm) as Hdt.
        simpl; split; omega_div.
      * simpl in H; omega_div.
    + (* W1010 *)
      split; intro H.
      * assert (Hm : dem true m = 0) by (simpl in H; omega_div).
        destruct (IHt Hm) as [IHt1 IHt2].
        destruct (shift_true_false_eq Hm) as [Hst1 Hst2].
        simpl; split; omega_div.
      * assert (Hm : dem true m = 0) by (simpl in H; omega_div).
        destruct (IHt Hm) as [IHt1 IHt2].
        simpl; split; omega_div.
    + (* W1110 *)
      split; intro H; simpl in H; omega_div.
Qed.

(* ========================================================================== *)
(* Fuel-Indexed Multi-Pass Transducer (TreeW) with StepOK                     *)
(* ========================================================================== *)

Definition ExitAt (S : list STok) (isB : bool) (L' : list WTok) : Q * tape :=
  if isB then cfg_modeB (evalW L') (evalS S) else cfg_modeF (evalW (W010 :: L')) (evalS S).

Definition StepOK (lw : list WTok) (isB : bool) (next : list WTok) : Prop :=
  match lw with
  | [] => isB = true /\ next = [W100]
  | W010 :: rest => isB = true /\ next = W110 :: rest
  | W110 :: rest => isB = true /\ next = W100 :: rest
  | W100 :: rest =>
    isB = false /\
    dem false next <= dem false rest - 1 /\
    potF false next <= potF false rest + 1
  | _ =>
    isB = true /\
    isHigh next = true /\
    dem false next <= dem false lw - 1 /\
    potF false next <= potF false lw + 1
  end.

Lemma stepOK_of_isHigh {w next : list WTok} {isB : bool}
    (Hw : isHigh w = true) (Hok : StepOK w isB next) :
  isB = true /\ isHigh next = true /\
  dem false next <= dem false w - 1 /\
  potF false next <= potF false w + 1.
Proof.
  destruct w as [| t rest]; [simpl in Hw; discriminate |].
  destruct t; simpl in Hw; try discriminate; exact Hok.
Qed.

Lemma dem_potF_of_isHigh {w : list WTok} (Hw : isHigh w = true) :
  dem true w = dem false w /\ potF true w = potF false w.
Proof.
  destruct w as [| t rest]; [simpl in Hw; discriminate |].
  destruct t; simpl in Hw; try discriminate; split; reflexivity.
Qed.

Lemma stepOK_W100_true {M next : list WTok} (Hok : StepOK M true next) :
  StepOK (W100 :: M) false next.
Proof.
  destruct M as [| t rest].
  - destruct Hok as [_ ->].
    simpl; repeat split; lia.
  - destruct t.
    + destruct Hok as [_ ->]; simpl; repeat split; omega_div.
    + destruct Hok as [_ [_ [Hd1 Hp]]]; exact (conj eq_refl (conj Hd1 Hp)).
    + destruct Hok as [_ [_ [Hd1 Hp]]]; exact (conj eq_refl (conj Hd1 Hp)).
    + destruct Hok as [Hb _]; discriminate.
    + destruct Hok as [_ ->]; simpl; repeat split; omega_div.
    + destruct Hok as [_ [_ [Hd1 Hp]]]; exact (conj eq_refl (conj Hd1 Hp)).
    + destruct Hok as [_ [_ [Hd1 Hp]]]; exact (conj eq_refl (conj Hd1 Hp)).
Qed.

Lemma stepOK_W100_false {M K : list WTok} (Hok : StepOK M false K) :
  StepOK (W100 :: M) false (W010 :: K).
Proof.
  destruct M as [| t rest]; [destruct Hok as [Hb _]; discriminate |].
  destruct t; try (destruct Hok as [Hb _]; discriminate).
  destruct Hok as [_ [Hd1 Hp]].
  destruct (potF_ge rest) as [HpR _].
  simpl; repeat split; omega_div.
Qed.

Lemma stepOK_W1010_TT {M M1 M2 : list WTok}
    (Hok1 : StepOK M true M1) (Hok2 : StepOK M1 true M2) :
  StepOK (W1010 :: M) true (W1010 :: M2).
Proof.
  destruct M as [| t rest].
  - destruct Hok1 as [_ ->]; destruct Hok2 as [Hb _]; discriminate.
  - destruct t.
    + (* W010 *)
      destruct Hok1 as [_ ->].
      destruct Hok2 as [_ ->].
      simpl; repeat split; omega_div.
    + (* W0010 *)
      destruct Hok1 as [_ [Hm1 [Hd1 Hp1]]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [_ [Hm2 [Hd2 Hp2]]].
      destruct (dem_potF_of_isHigh Hm2) as [Hdt2 Hpt2].
      simpl in Hd1, Hp1 |- *; repeat split; omega_div.
    + (* W0110 *)
      destruct Hok1 as [_ [Hm1 [Hd1 Hp1]]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [_ [Hm2 [Hd2 Hp2]]].
      destruct (dem_potF_of_isHigh Hm2) as [Hdt2 Hpt2].
      simpl in Hd1, Hp1 |- *; repeat split; omega_div.
    + (* W100 *) destruct Hok1 as [Hb _]; discriminate.
    + (* W110 *) destruct Hok1 as [_ ->]; destruct Hok2 as [Hb _]; discriminate.
    + (* W1010 *)
      destruct Hok1 as [_ [Hm1 [Hd1 Hp1]]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [_ [Hm2 [Hd2 Hp2]]].
      destruct (dem_potF_of_isHigh Hm2) as [Hdt2 Hpt2].
      simpl in Hd1, Hp1 |- *; repeat split; omega_div.
    + (* W1110 *)
      destruct Hok1 as [_ [Hm1 [Hd1 Hp1]]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [_ [Hm2 [Hd2 Hp2]]].
      destruct (dem_potF_of_isHigh Hm2) as [Hdt2 Hpt2].
      simpl in Hd1, Hp1 |- *; repeat split; omega_div.
Qed.

Lemma stepOK_W1010_TF {M M1 M2 : list WTok}
    (Hok1 : StepOK M true M1) (Hok2 : StepOK M1 false M2) :
  StepOK (W1010 :: M) true (W1010 :: W010 :: M2).
Proof.
  destruct M as [| t rest].
  - destruct Hok1 as [_ ->].
    destruct Hok2 as [_ [Hd2 Hp2]].
    simpl in Hd2, Hp2 |- *; repeat split; omega_div.
  - destruct t.
    + (* W010 *) destruct Hok1 as [_ ->]; destruct Hok2 as [Hb _]; discriminate.
    + (* W0010 *)
      destruct Hok1 as [_ [Hm1 _]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [Hb _]; discriminate.
    + (* W0110 *)
      destruct Hok1 as [_ [Hm1 _]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [Hb _]; discriminate.
    + (* W100 *) destruct Hok1 as [Hb _]; discriminate.
    + (* W110 *)
      destruct Hok1 as [_ ->].
      destruct Hok2 as [_ [Hd2 Hp2]].
      simpl in Hd2, Hp2 |- *; repeat split; omega_div.
    + (* W1010 *)
      destruct Hok1 as [_ [Hm1 _]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [Hb _]; discriminate.
    + (* W1110 *)
      destruct Hok1 as [_ [Hm1 _]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [Hb _]; discriminate.
Qed.

Lemma stepOK_W1010_F {M M1 : list WTok}
    (Hok1 : StepOK M false M1) :
  StepOK (W1010 :: M) true (W1010 :: W100 :: M1).
Proof.
  destruct M as [| t rest]; [destruct Hok1 as [Hb _]; discriminate |].
  destruct t; try (destruct Hok1 as [Hb _]; discriminate).
  destruct Hok1 as [_ [Hd1 Hp1]].
  simpl in Hd1, Hp1 |- *; repeat split; omega_div.
Qed.

(* Symbolic pass combinators *)
Lemma pass_W100_B {M M' : list WTok}
    (H : forall S : list STok, cfg_h01B (evalW M) (evalS S) -->+ cfg_modeB (evalW M') (evalS S))
    (S : list STok) :
  cfg_h01B (evalW (W100 :: M)) (evalS S) -->+ cfg_modeF (evalW (W010 :: M')) (evalS S).
Proof.
  exact (ptrans (sym_h01B_100 M S) (ptrans (H (T011 :: S)) (sym_modeB_011 M' S))).
Qed.

Lemma pass_W100_F {M M' : list WTok}
    (H : forall S : list STok, cfg_h01B (evalW M) (evalS S) -->+ cfg_modeF (evalW M') (evalS S))
    (S : list STok) :
  cfg_h01B (evalW (W100 :: M)) (evalS S) -->+ cfg_modeF (evalW (W010 :: M')) (evalS S).
Proof.
  exact (ptrans (sym_h01B_100 M S) (ptrans (H (T011 :: S)) (sym_modeF_011 M' S))).
Qed.

Lemma pass_W1010_BB {M M1 M2 : list WTok}
    (H1 : forall S : list STok, cfg_h01B (evalW M) (evalS S) -->+ cfg_modeB (evalW M1) (evalS S))
    (H2 : forall S : list STok, cfg_h01B (evalW M1) (evalS S) -->+ cfg_modeB (evalW M2) (evalS S))
    (S : list STok) :
  cfg_h01B (evalW (W1010 :: M)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: M2)) (evalS S).
Proof.
  exact (ptrans (sym_h01B_1010 M S)
    (ptrans (H1 (T0100 :: S))
      (ptrans (sym_modeB_0100 M1 S)
        (ptrans (H2 (T0101 :: S))
          (sym_modeB_0101 M2 S))))).
Qed.

Lemma pass_W1010_BF {M M1 M2 : list WTok}
    (H1 : forall S : list STok, cfg_h01B (evalW M) (evalS S) -->+ cfg_modeB (evalW M1) (evalS S))
    (H2 : forall S : list STok, cfg_h01B (evalW M1) (evalS S) -->+ cfg_modeF (evalW M2) (evalS S))
    (S : list STok) :
  cfg_h01B (evalW (W1010 :: M)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: M2)) (evalS S).
Proof.
  exact (ptrans (sym_h01B_1010 M S)
    (ptrans (H1 (T0100 :: S))
      (ptrans (sym_modeB_0100 M1 S)
        (ptrans (H2 (T0101 :: S))
          (sym_modeF_0101 M2 S))))).
Qed.

Lemma pass_W1010_F {M M1 : list WTok}
    (H1 : forall S : list STok, cfg_h01B (evalW M) (evalS S) -->+ cfg_modeF (evalW (W010 :: M1)) (evalS S))
    (S : list STok) :
  cfg_h01B (evalW (W1010 :: M)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: W100 :: M1)) (evalS S).
Proof.
  exact (ptrans (sym_h01B_1010 M S)
    (ptrans (H1 (T0100 :: S))
      (ptrans (sym_modeF_0100 (W010 :: M1) S)
        (ptrans (sym_h01B_010 M1 (T0100 :: S))
          (ptrans (sym_modeB_0100 (W110 :: M1) S)
            (ptrans (sym_h01B_110 M1 (T0101 :: S))
              (sym_modeB_0101 (W100 :: M1) S))))))).
Qed.

Fixpoint TreeW (n : nat) (L : list WTok) : Prop :=
  match n with
  | O => True
  | S n' =>
    exists (isB : bool) (next : list WTok),
      StepOK L isB next /\
      (forall S : list STok, cfg_h01B (evalW L) (evalS S) -->+ ExitAt S isB next) /\
      TreeW n' next
  end.

Lemma treeW_succ : forall {n : nat} {L : list WTok}, TreeW (S n) L -> TreeW n L.
Proof.
  induction n as [| n IH]; intros L H.
  - exact I.
  - destruct H as [isB [next [Hok [Hstep Hsub]]]].
    exists isB, next; split; [exact Hok | split; [exact Hstep | exact (IH next Hsub)]].
Qed.

Lemma treeW_triple (n : nat) :
  (forall M : list WTok, TreeW n M -> TreeW n (W100 :: M)) /\
  (forall M : list WTok, TreeW n M -> TreeW n (W110 :: M)) /\
  (forall M : list WTok, TreeW n M -> TreeW n (W010 :: M)).
Proof.
  induction n as [| n [IH100 [IH110 IH010]]].
  - repeat split; intros; exact I.
  - repeat split; intros M H.
    + destruct H as [[|] [next [Hok [Hstep Hsub]]]].
      * exists false, next; split; [exact (stepOK_W100_true Hok) | split; [exact (pass_W100_B Hstep) | exact Hsub]].
      * exists false, (W010 :: next); split;
          [exact (stepOK_W100_false Hok) | split; [exact (pass_W100_F Hstep) | exact (IH010 next Hsub)]].
    + exists true, (W100 :: M); split; [split; reflexivity | split; [exact (sym_h01B_110 M) | exact (IH100 M (treeW_succ H))]].
    + exists true, (W110 :: M); split; [split; reflexivity | split; [exact (sym_h01B_010 M) | exact (IH110 M (treeW_succ H))]].
Qed.

Lemma treeW_W100 {n : nat} {M : list WTok} (H : TreeW n M) : TreeW n (W100 :: M).
Proof. exact (proj1 (treeW_triple n) M H). Qed.

Lemma treeW_W110 {n : nat} {M : list WTok} (H : TreeW n M) : TreeW n (W110 :: M).
Proof. exact (proj1 (proj2 (treeW_triple n)) M H). Qed.

Lemma treeW_W010 {n : nat} {M : list WTok} (H : TreeW n M) : TreeW n (W010 :: M).
Proof. exact (proj2 (proj2 (treeW_triple n)) M H). Qed.

Lemma treeW_nil (n : nat) : TreeW n [].
Proof.
  induction n as [| n IH]; [exact I |].
  exists true, [W100]; split; [split; reflexivity | split; [exact sym_h01B_nil | exact (treeW_W100 IH)]].
Qed.

Lemma treeW_W1010_step {n : nat} {M : list WTok} (t : TreeW (S (S n)) M) :
  exists next : list WTok,
    StepOK (W1010 :: M) true (W1010 :: next) /\
    (forall S : list STok,
      cfg_h01B (evalW (W1010 :: M)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: next)) (evalS S)) /\
    TreeW n next.
Proof.
  destruct t as [[|] [M1 [Hok1 [Hstep1 Hsub1]]]].
  - destruct Hsub1 as [[|] [M2 [Hok2 [Hstep2 Hsub2]]]].
    + exists M2; split;
        [exact (stepOK_W1010_TT Hok1 Hok2) | split; [exact (pass_W1010_BB Hstep1 Hstep2) | exact Hsub2]].
    + exists (W010 :: M2); split;
        [exact (stepOK_W1010_TF Hok1 Hok2) | split; [exact (pass_W1010_BF Hstep1 Hstep2) | exact (treeW_W010 Hsub2)]].
  - exists (W100 :: M1); split;
      [exact (stepOK_W1010_F Hok1) | split; [exact (pass_W1010_F Hstep1) | exact (treeW_W100 (treeW_succ Hsub1))]].
Qed.

Lemma treeW_W1010 : forall (n : nat) {M : list WTok}, TreeW (2 * n) M -> TreeW n (W1010 :: M).
Proof.
  induction n as [| n IH]; intros M t; [exact I |].
  replace (2 * S n) with (S (S (2 * n))) in t by lia.
  destruct (treeW_W1010_step t) as [next [Hok [Hstep Hsub]]].
  exists true, (W1010 :: next); split; [exact Hok | split; [exact Hstep | exact (IH next Hsub)]].
Qed.

Lemma treeW_W0010 {n : nat} {M : list WTok} (t : TreeW (2 * n) M) : TreeW n (W0010 :: M).
Proof.
  destruct n as [| n]; [exact I |].
  replace (2 * S n) with (S (S (2 * n))) in t by lia.
  exists true, (W1010 :: M); repeat split.
  - simpl; omega_div.
  - simpl; omega_div.
  - exact (sym_h01B_0010 M).
  - exact (treeW_W1010 n (treeW_succ (treeW_succ t))).
Qed.

Lemma treeW_W1110 {n : nat} {M : list WTok} (t : TreeW (2 * n) M) : TreeW n (W1110 :: M).
Proof.
  destruct n as [| n]; [exact I |].
  replace (2 * S n) with (S (S (2 * n))) in t by lia.
  exists true, (W1010 :: M); repeat split.
  - simpl; omega_div.
  - simpl; omega_div.
  - exact (sym_h01B_1110 M).
  - exact (treeW_W1010 n (treeW_succ (treeW_succ t))).
Qed.

Lemma treeW_W0110 {n : nat} {M : list WTok} (t : TreeW (2 * n) M) : TreeW n (W0110 :: M).
Proof.
  destruct n as [| n]; [exact I |].
  replace (2 * S n) with (S (S (2 * n))) in t by lia.
  exists true, (W1110 :: M); repeat split.
  - simpl; omega_div.
  - simpl; omega_div.
  - exact (sym_h01B_0110 M).
  - exact (treeW_W1110 (treeW_succ (treeW_succ t))).
Qed.

Lemma buildTreeW (L : list WTok) : forall n : nat, TreeW n L.
Proof.
  induction L as [| t M IH]; intro n.
  - exact (treeW_nil n).
  - destruct t.
    + exact (treeW_W010 (IH n)).
    + exact (treeW_W0010 (IH (2 * n))).
    + exact (treeW_W0110 (IH (2 * n))).
    + exact (treeW_W100 (IH n)).
    + exact (treeW_W110 (IH n)).
    + exact (treeW_W1010 n (IH (2 * n))).
    + exact (treeW_W1110 (IH (2 * n))).
Qed.

(* ========================================================================== *)
(* Initial Reachability & Non-Halting Theorem                                 *)
(* ========================================================================== *)

Lemma step_modeB_reparse {u w : list WTok}
    (Heq : 1%sym >> 0%sym >> evalW u = evalW w) :
  cfg_modeB (evalW u) (evalS []) -->+ cfg_h01B (evalW w) (evalS []).
Proof.
  rewrite <- Heq.
  exact (step_modeB_base (evalW u)).
Qed.

Definition w4 : list WTok := [W1010; W1010; W1010; W0010; W1010; W010; W100].

Lemma step_init_to_w4 :
  c0 -->+ cfg_h01B (evalW w4) (evalS []).
Proof.
  unfold w4.
  pose proof (pass_W1010_BF sym_h01B_nil (pass_W100_B sym_h01B_nil)) as Hw1.
  pose proof (pass_W1010_F (pass_W100_B Hw1)) as Hw2.
  pose proof (pass_W1010_BB (sym_h01B_010 [W100; W1010]) (sym_h01B_110 [W100; W1010])) as Hw3_a.
  pose proof (pass_W1010_F (pass_W100_F (pass_W100_B Hw1))) as Hw3_b.
  pose proof (pass_W1010_BB Hw3_a Hw3_b) as Hw3.
  assert (Hp0 : c0 -->+ cfg_h01B (evalW [W1010]) (evalS [])).
  { eapply ptrans; [exact step_init_to_h01B |].
    eapply ptrans; [exact (sym_h01B_nil []) |].
    apply step_modeB_reparse; simpl; repeat rewrite <- const_unfold; reflexivity. }
  assert (Hp1 : cfg_h01B (evalW [W1010]) (evalS []) -->+
      cfg_h01B (evalW [W1010; W100; W1010]) (evalS [])).
  { eapply ptrans; [exact (Hw1 []) |].
    apply step_modeB_reparse; simpl; repeat rewrite <- const_unfold; reflexivity. }
  assert (Hp2 : cfg_h01B (evalW [W1010; W100; W1010]) (evalS []) -->+
      cfg_h01B (evalW [W1010; W1010; W010; W100; W1010]) (evalS [])).
  { eapply ptrans; [exact (Hw2 []) |].
    apply step_modeB_reparse; simpl; repeat rewrite <- const_unfold; reflexivity. }
  assert (Hp3 : cfg_h01B (evalW [W1010; W1010; W010; W100; W1010]) (evalS []) -->+
      cfg_h01B (evalW [W1010; W1010; W1010; W0010; W1010; W010; W100]) (evalS [])).
  { eapply ptrans; [exact (Hw3 []) |].
    apply step_modeB_reparse; simpl; repeat rewrite <- const_unfold; reflexivity. }
  exact (ptrans Hp0 (ptrans Hp1 (ptrans Hp2 Hp3))).
Qed.

Definition CfgW (w : list WTok) : Q * tape :=
  cfg_h01B (evalW w) (evalS []).

Definition InvW (w : list WTok) : Prop :=
  isHigh w = true /\ dem false w <= 1 /\ potF false w <= 4.

Lemma invW_step (w : list WTok) (H : InvW w) :
  exists w' : list WTok, CfgW w -->+ CfgW w' /\ InvW w'.
Proof.
  destruct H as [Hw [Hd Hp]].
  destruct (buildTreeW w 1) as [isB [u [Hok [Hstep _]]]].
  destruct (stepOK_of_isHigh Hw Hok) as [-> [Hu_high [Hu_dem1 Hu_pot]]].
  destruct (dem_potF_of_isHigh Hu_high) as [Hdu_eq Hpu_eq].
  assert (Hdu : dem true u = 0) by lia.
  assert (Hpu : potF true u <= 5) by lia.
  pose proof (isHigh_shift_true Hdu) as Hw'_high.
  destruct (dem_potF_of_isHigh Hw'_high) as [Hdw'_eq Hpw'_eq].
  destruct (proj2 (shift_bounds u) Hdu) as [Hb_dem Hb_pot].
  exists (shift true u).
  split.
  - unfold CfgW.
    eapply ptrans; [exact (Hstep []) |].
    apply step_modeB_reparse.
    symmetry; exact (evalW_shift true u Hdu).
  - unfold InvW.
    split; [exact Hw'_high | split; omega_div].
Qed.

Local Transparent Nat.div Nat.max.

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt with (c' := CfgW w4).
  - exact (pev step_init_to_w4).
  - eapply progress_nonhalt_cond with (C := CfgW) (P := InvW) (i0 := w4).
    + exact invW_step.
    + unfold InvW, w4; simpl; repeat split; lia.
Qed.

Print Assumptions nonhalt.
