(* Refactored from BusyCoq PR #79. *)
(* 1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA--- never halts. *)

From BusyCoq Require Import Individual62.
From BusyCoq Require Import PR78_79Base.
From Coq Require Import Bool List Lists.Streams Lia ZifyNat ZifyN ZifyBool NArith ZArith PeanoNat String.
Import ListNotations.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm : TM := TM_from_str "1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---".
Arguments tm _ : simpl never.

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).

(* ========================================================================== *)
(* Reachability Combinators & Micro-Step Automation                           *)
(* ========================================================================== *)

Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma ps_trans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->* c3 -> c1 -->+ c3.
Proof. apply progress_evstep_trans. Qed.

Lemma sp_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma etrans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Lemma pev {c1 c2 : Q * tape} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Lemma some_inj {X : Type} {x y : X} : Some x = Some y -> x = y.
Proof. congruence. Qed.

Lemma pair_inj {X Y : Type} {x1 x2 : X} {y1 y2 : Y} :
  (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2.
Proof. split; congruence. Qed.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  (apply evstep_refl'; cbn [Streams.hd Streams.tl]; repeat rewrite <- const_unfold; reflexivity)
  || finish_progress.

Ltac fast_execute :=
  intros; repeat (try solve [fast_finish]; fast_step).

Ltac fast_start_progress :=
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  fast_execute.

Lemma cons_zero_0inf : S0 >> 0inf = 0inf.
Proof. symmetry. apply const_unfold. Qed.

(* ========================================================================== *)
(* Layer 1: Triplet Repetition Algebra, Era Contractions, and 4^m Cascade     *)
(* ========================================================================== *)

Fixpoint rep110 (n : nat) (lb : side) : side :=
  match n with
  | 0 => lb
  | S k => S1 >> S1 >> S0 >> rep110 k lb
  end.

Fixpoint rep001 (n : nat) (lb : side) : side :=
  match n with
  | 0 => lb
  | S k => S0 >> S0 >> S1 >> rep001 k lb
  end.

Lemma rep110_add (a b : nat) (lb : side) :
  rep110 (a + b) lb = rep110 a (rep110 b lb).
Proof.
  induction a as [| a IH]; [reflexivity |].
  cbn [Nat.add rep110]. rewrite IH. reflexivity.
Qed.

Lemma rep001_add (a b : nat) (lb : side) :
  rep001 (a + b) lb = rep001 a (rep001 b lb).
Proof.
  induction a as [| a IH]; [reflexivity |].
  cbn [Nat.add rep001]. rewrite IH. reflexivity.
Qed.

Lemma rep110_shift (n : nat) (lb : side) :
  rep110 n (S1 >> S1 >> S0 >> lb) = S1 >> S1 >> S0 >> rep110 n lb.
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [rep110]. rewrite IH. reflexivity.
Qed.

Lemma rep001_shift (n : nat) (lb : side) :
  rep001 n (S0 >> S0 >> S1 >> lb) = S0 >> S0 >> S1 >> rep001 n lb.
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [rep001]. rewrite IH. reflexivity.
Qed.

Lemma reach_splitR_lb : forall (q : nat) (l r : side),
  (l {{C}}> (S1 >> rep001 q r)) -->* (rep110 q l {{C}}> (S1 >> r)).
Proof.
  induction q as [| q IH]; intros l r.
  - apply evstep_refl.
  - cbn [rep001].
    assert (h1 : (l {{C}}> (S1 >> S0 >> S0 >> S1 >> rep001 q r)) -->*
                 ((S1 >> S1 >> S0 >> l) {{C}}> (S1 >> rep001 q r)))
      by fast_execute.
    pose proof (IH (S1 >> S1 >> S0 >> l) r) as h2.
    rewrite rep110_shift in h2.
    exact (etrans h1 h2).
Qed.

Lemma reach_splitL_lb : forall (k : nat) (l r : side),
  (rep110 (2 * k) l {{C}}> (S0 >> r)) -->* (l {{C}}> (S0 >> rep001 (2 * k) r)).
Proof.
  induction k as [| k IH]; intros l r.
  - cbn [Nat.mul rep110 rep001]. apply evstep_refl.
  - replace (2 * S k) with (2 + 2 * k) by lia.
    rewrite (rep110_add 2 (2 * k)), (rep001_add 2 (2 * k)).
    cbn [rep110].
    assert (h1 : ((S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> rep110 (2 * k) l) {{C}}> (S0 >> r)) -->*
                 (rep110 (2 * k) l {{C}}> (S0 >> S0 >> S0 >> S1 >> S0 >> S0 >> S1 >> r)))
      by fast_execute.
    pose proof (IH l (S0 >> S0 >> S1 >> S0 >> S0 >> S1 >> r)) as h2.
    rewrite !rep001_shift in h2.
    exact (etrans h1 h2).
Qed.

Lemma reach_R1_lb (l r : side) :
  (l {{C}}> (S1 >> S1 >> r)) -->+ (l {{C}}> (S0 >> S0 >> r)).
Proof. fast_start_progress. Qed.

Lemma reach_R2_lb (b3 : Sym) (l r : side) :
  (l {{C}}> (S1 >> S0 >> S0 >> b3 >> r)) -->+
  ((S1 >> S1 >> S0 >> l) {{C}}> (b3 >> r)).
Proof. destruct b3; fast_start_progress. Qed.

Lemma reach_R3_lb (l r : side) :
  (l {{C}}> (S1 >> S0 >> S1 >> S0 >> r)) -->+
  ((S0 >> l) {{C}}> (S1 >> S0 >> S0 >> r)).
Proof. fast_start_progress. Qed.

Lemma reach_L1_lb (l r : side) :
  ((S0 >> l) {{D}}> (S0 >> r)) -->+ ((S1 >> l) {{C}}> (S1 >> r)).
Proof. fast_start_progress. Qed.

Lemma reach_L2_lb (cb : Sym) (l r : side) :
  ((S1 >> S1 >> cb >> l) {{D}}> (S0 >> r)) -->+
  (l {{C}}> (cb >> S0 >> S0 >> S1 >> r)).
Proof. destruct cb; fast_start_progress. Qed.

Lemma reach_L3_lb (l r : side) :
  ((S1 >> S0 >> l) {{D}}> (S0 >> r)) -->+
  ((S1 >> S1 >> l) {{C}}> (S1 >> r)).
Proof. fast_start_progress. Qed.

(* Quadratic Era Contractions *)

Lemma era_drain_one (k : nat) (r : side) :
  (rep110 (2 * (k + 1)) (S1 >> S1 >> 0inf) {{C}}>
    (S0 >> S1 >> S0 >> S0 >> S1 >> r)) -->+
  (rep110 (2 * (k + 2)) (S1 >> S1 >> 0inf) {{C}}>
    (S0 >> S1 >> r)).
Proof.
  pose proof (reach_splitL_lb (k + 1) (S1 >> S1 >> 0inf) (S1 >> S0 >> S0 >> S1 >> r)) as hs1.
  assert (ht1 : ((S1 >> S1 >> 0inf) {{C}}>
                  (S0 >> rep001 (2 * (k + 1)) (S1 >> S0 >> S0 >> S1 >> r))) -->+
                ((S1 >> 0inf) {{C}}>
                  (S1 >> rep001 (2 * k + 3) (S1 >> S0 >> S0 >> S1 >> r)))).
  { replace (2 * k + 3) with (1 + 2 * (k + 1)) by lia.
    rewrite (rep001_add 1 (2 * (k + 1))).
    cbn [rep001]. fast_start_progress. }
  pose proof (reach_splitR_lb (2 * k + 3) (S1 >> 0inf) (S1 >> S0 >> S0 >> S1 >> r)) as hs2.
  pose proof (reach_R1_lb (rep110 (2 * k + 3) (S1 >> 0inf)) (S0 >> S0 >> S1 >> r)) as ht2.
  assert (hl3_eq : rep110 (2 * k + 3) (S1 >> 0inf) =
                   rep110 (2 * (k + 1)) (S1 >> S1 >> S0 >> S1 >> 0inf)).
  { replace (2 * k + 3) with (2 * (k + 1) + 1) by lia.
    rewrite (rep110_add (2 * (k + 1)) 1). reflexivity. }
  pose proof (reach_splitL_lb (k + 1) (S1 >> S1 >> S0 >> S1 >> 0inf)
                (S0 >> S0 >> S0 >> S1 >> r)) as hs3.
  rewrite <- hl3_eq in hs3.
  assert (ht3 : ((S1 >> S1 >> S0 >> S1 >> 0inf) {{C}}>
                  (S0 >> rep001 (2 * (k + 1)) (S0 >> S0 >> S0 >> S1 >> r))) -->+
                ((S1 >> S1 >> 0inf) {{C}}>
                  (S1 >> rep001 (2 * k + 3) (S0 >> S0 >> S0 >> S1 >> r)))).
  { replace (2 * k + 3) with (1 + 2 * (k + 1)) by lia.
    rewrite (rep001_add 1 (2 * (k + 1))).
    cbn [rep001]. fast_start_progress. }
  pose proof (reach_splitR_lb (2 * k + 3) (S1 >> S1 >> 0inf) (S0 >> S0 >> S0 >> S1 >> r)) as hs4.
  pose proof (reach_R2_lb S0 (rep110 (2 * k + 3) (S1 >> S1 >> 0inf)) (S1 >> r)) as ht4.
  assert (hl4_eq : (S1 >> S1 >> S0 >> rep110 (2 * k + 3) (S1 >> S1 >> 0inf)) =
                   rep110 (2 * (k + 2)) (S1 >> S1 >> 0inf)).
  { replace (2 * (k + 2)) with (1 + (2 * k + 3)) by lia.
    rewrite (rep110_add 1 (2 * k + 3)). reflexivity. }
  rewrite hl4_eq in ht4.
  exact (ptrans (ps_trans (sp_trans hs1 ht1) hs2)
          (ptrans (ps_trans ht2 hs3)
            (ptrans (ps_trans ht3 hs4) ht4))).
Qed.

Lemma era_drain_iter : forall (c_m1 k : nat) (r : side),
  (rep110 (2 * (k + 1)) (S1 >> S1 >> 0inf) {{C}}>
    (S0 >> S1 >> rep001 (c_m1 + 1) r)) -->+
  (rep110 (2 * (k + 1 + (c_m1 + 1))) (S1 >> S1 >> 0inf) {{C}}>
    (S0 >> S1 >> r)).
Proof.
  induction c_m1 as [| c_m1 IH]; intros k r.
  - cbn [Nat.add rep001].
    replace (k + 1 + 1) with (k + 2) by lia.
    exact (era_drain_one k r).
  - replace (S c_m1 + 1) with (1 + (c_m1 + 1)) by lia.
    rewrite (rep001_add 1 (c_m1 + 1)).
    cbn [rep001].
    pose proof (era_drain_one k (rep001 (c_m1 + 1) r)) as h1.
    pose proof (IH (k + 1) r) as h2.
    replace (2 * (k + 1 + 1 + (c_m1 + 1))) with (2 * (k + 1 + (1 + (c_m1 + 1)))) in h2 by lia.
    replace (k + 2) with (k + 1 + 1) in h1 by lia.
    exact (ptrans h1 h2).
Qed.

Lemma era_osc_one (j : nat) (l r : side) :
  ((S0 >> S1 >> S1 >> S0 >> l) {{C}}>
    (S1 >> rep001 (2 * j) (S0 >> S0 >> S0 >> S1 >> r))) -->+
  ((S0 >> l) {{C}}>
    (S1 >> rep001 (2 * (j + 1)) (S0 >> r))).
Proof.
  set (L0 := S0 >> S1 >> S1 >> S0 >> l).
  pose proof (reach_splitR_lb (2 * j) L0 (S0 >> S0 >> S0 >> S1 >> r)) as hs1.
  pose proof (reach_R2_lb S0 (rep110 (2 * j) L0) (S1 >> r)) as ht1.
  rewrite <- (rep110_shift (2 * j) L0) in ht1.
  pose proof (reach_splitL_lb j (S1 >> S1 >> S0 >> L0) (S1 >> r)) as hs2.
  assert (ht2 : ((S1 >> S1 >> S0 >> L0) {{C}}> (S0 >> rep001 (2 * j) (S1 >> r))) -->+
                ((S1 >> S1 >> S1 >> S0 >> l) {{C}}> (S1 >> rep001 (2 * j + 1) (S1 >> r)))).
  { replace (2 * j + 1) with (1 + 2 * j) by lia.
    rewrite (rep001_add 1 (2 * j)).
    unfold L0. cbn [rep001]. fast_start_progress. }
  set (L1 := S1 >> S1 >> S1 >> S0 >> l).
  pose proof (reach_splitR_lb (2 * j + 1) L1 (S1 >> r)) as hs3.
  pose proof (reach_R1_lb (rep110 (2 * j + 1) L1) r) as ht3.
  assert (hl3_eq : rep110 (2 * j + 1) L1 = rep110 (2 * j) (S1 >> S1 >> S0 >> L1)).
  { rewrite (rep110_add (2 * j) 1). reflexivity. }
  pose proof (reach_splitL_lb j (S1 >> S1 >> S0 >> L1) (S0 >> r)) as hs4.
  rewrite <- hl3_eq in hs4.
  assert (ht4 : ((S1 >> S1 >> S0 >> L1) {{C}}> (S0 >> rep001 (2 * j) (S0 >> r))) -->+
                ((S0 >> l) {{C}}> (S1 >> rep001 (2 * (j + 1)) (S0 >> r)))).
  { replace (2 * (j + 1)) with (2 + 2 * j) by lia.
    rewrite (rep001_add 2 (2 * j)).
    unfold L1. cbn [rep001]. fast_start_progress. }
  exact (ptrans (ps_trans (sp_trans hs1 ht1) hs2)
          (ptrans (ps_trans ht2 hs3)
            (ptrans (ps_trans ht3 hs4) ht4))).
Qed.

Lemma era_osc_iter : forall (n_m1 j : nat) (l r : side),
  ((S0 >> rep110 (n_m1 + 1) l) {{C}}>
    (S1 >> rep001 (2 * j) (S0 >> rep001 (n_m1 + 1) r))) -->+
  ((S0 >> l) {{C}}>
    (S1 >> rep001 (2 * (j + (n_m1 + 1))) (S0 >> r))).
Proof.
  induction n_m1 as [| n_m1 IH]; intros j l r.
  - cbn [Nat.add rep110 rep001]. exact (era_osc_one j l r).
  - replace (S n_m1 + 1) with (1 + (n_m1 + 1)) by lia.
    rewrite (rep110_add 1 (n_m1 + 1)), (rep001_add 1 (n_m1 + 1)).
    cbn [rep110 rep001].
    pose proof (era_osc_one j (rep110 (n_m1 + 1) l) (rep001 (n_m1 + 1) r)) as h1.
    pose proof (IH (j + 1) l r) as h2.
    replace (2 * (j + 1 + (n_m1 + 1))) with (2 * (j + (1 + (n_m1 + 1)))) in h2 by lia.
    exact (ptrans h1 h2).
Qed.

Lemma era_osc10_one (j : nat) (l r : side) :
  ((S1 >> S0 >> S1 >> S1 >> S0 >> l) {{C}}>
    (S1 >> rep001 (2 * j) (S0 >> S0 >> S0 >> S1 >> r))) -->+
  ((S1 >> S0 >> l) {{C}}>
    (S1 >> rep001 (2 * (j + 1)) (S0 >> r))).
Proof.
  set (L0 := S1 >> S0 >> S1 >> S1 >> S0 >> l).
  pose proof (reach_splitR_lb (2 * j) L0 (S0 >> S0 >> S0 >> S1 >> r)) as hs1.
  pose proof (reach_R2_lb S0 (rep110 (2 * j) L0) (S1 >> r)) as ht1.
  rewrite <- (rep110_shift (2 * j) L0) in ht1.
  pose proof (reach_splitL_lb j (S1 >> S1 >> S0 >> L0) (S1 >> r)) as hs2.
  assert (ht2 : ((S1 >> S1 >> S0 >> L0) {{C}}> (S0 >> rep001 (2 * j) (S1 >> r))) -->+
                ((S1 >> S1 >> S1 >> S1 >> S0 >> l) {{C}}> (S1 >> rep001 (2 * j + 1) (S1 >> r)))).
  { replace (2 * j + 1) with (1 + 2 * j) by lia.
    rewrite (rep001_add 1 (2 * j)).
    unfold L0. cbn [rep001]. fast_start_progress. }
  set (L1 := S1 >> S1 >> S1 >> S1 >> S0 >> l).
  pose proof (reach_splitR_lb (2 * j + 1) L1 (S1 >> r)) as hs3.
  pose proof (reach_R1_lb (rep110 (2 * j + 1) L1) r) as ht3.
  assert (hl3_eq : rep110 (2 * j + 1) L1 = rep110 (2 * j) (S1 >> S1 >> S0 >> L1)).
  { rewrite (rep110_add (2 * j) 1). reflexivity. }
  pose proof (reach_splitL_lb j (S1 >> S1 >> S0 >> L1) (S0 >> r)) as hs4.
  rewrite <- hl3_eq in hs4.
  assert (ht4 : ((S1 >> S1 >> S0 >> L1) {{C}}> (S0 >> rep001 (2 * j) (S0 >> r))) -->+
                ((S1 >> S0 >> l) {{C}}> (S1 >> rep001 (2 * (j + 1)) (S0 >> r)))).
  { replace (2 * (j + 1)) with (2 + 2 * j) by lia.
    rewrite (rep001_add 2 (2 * j)).
    unfold L1. cbn [rep001]. fast_start_progress. }
  exact (ptrans (ps_trans (sp_trans hs1 ht1) hs2)
          (ptrans (ps_trans ht2 hs3)
            (ptrans (ps_trans ht3 hs4) ht4))).
Qed.

Lemma era_osc10_iter : forall (n_m1 j : nat) (l r : side),
  ((S1 >> S0 >> rep110 (n_m1 + 1) l) {{C}}>
    (S1 >> rep001 (2 * j) (S0 >> rep001 (n_m1 + 1) r))) -->+
  ((S1 >> S0 >> l) {{C}}>
    (S1 >> rep001 (2 * (j + (n_m1 + 1))) (S0 >> r))).
Proof.
  induction n_m1 as [| n_m1 IH]; intros j l r.
  - cbn [Nat.add rep110 rep001]. exact (era_osc10_one j l r).
  - replace (S n_m1 + 1) with (1 + (n_m1 + 1)) by lia.
    rewrite (rep110_add 1 (n_m1 + 1)), (rep001_add 1 (n_m1 + 1)).
    cbn [rep110 rep001].
    pose proof (era_osc10_one j (rep110 (n_m1 + 1) l) (rep001 (n_m1 + 1) r)) as h1.
    pose proof (IH (j + 1) l r) as h2.
    replace (2 * (j + 1 + (n_m1 + 1))) with (2 * (j + (1 + (n_m1 + 1)))) in h2 by lia.
    exact (ptrans h1 h2).
Qed.

(* Exponential 4^m Arithmetic, Binary Shift Bridges, and Super-Era Cascade *)

Fixpoint pow4 (m : nat) : nat :=
  match m with
  | 0 => 1
  | S k => 4 * pow4 k
  end.

Fixpoint sum4 (m : nat) : nat :=
  match m with
  | 0 => 0
  | S k => 1 + 4 * sum4 k
  end.

Lemma sum4_spec (m : nat) : 3 * sum4 m + 1 = pow4 m.
Proof.
  induction m as [| m IH]; [reflexivity |].
  cbn [sum4 pow4]. lia.
Qed.

Lemma sum4_add (m d : nat) : sum4 (m + d) = pow4 d * sum4 m + sum4 d.
Proof.
  induction d as [| d IH].
  - rewrite Nat.add_0_r. cbn [pow4 sum4]. lia.
  - rewrite Nat.add_succ_r. cbn [sum4 pow4]. rewrite IH. nia.
Qed.

Lemma pow4_add (m d : nat) : pow4 (m + d) = pow4 d * pow4 m.
Proof.
  induction d as [| d IH].
  - rewrite Nat.add_0_r. cbn [pow4]. lia.
  - rewrite Nat.add_succ_r. cbn [pow4]. rewrite IH. nia.
Qed.

Lemma pow4_pos (k : nat) : 1 <= pow4 k.
Proof.
  induction k as [| k IH]; cbn [pow4]; lia.
Qed.

Lemma sum4_ge_self (k : nat) : k <= sum4 k.
Proof.
  induction k as [| k IH]; cbn [sum4]; lia.
Qed.

Lemma sum4_odd (m : nat) : 1 <= m -> sum4 m mod 2 = 1.
Proof.
  destruct m as [| k]; [lia | intros _; cbn [sum4]; lia].
Qed.

Lemma N_pow4_of_nat (k : nat) : N.to_nat (4 ^ N.of_nat k)%N = pow4 k.
Proof.
  induction k as [| k IH]; [reflexivity |].
  replace (N.of_nat (S k)) with (N.of_nat k + 1)%N by lia.
  rewrite N.pow_add_r.
  change (4 ^ 1)%N with 4%N.
  rewrite N2Nat.inj_mul, IH.
  cbn [pow4 N.to_nat]. lia.
Qed.

Lemma N_pow4_to_nat (m : N) : N.to_nat (4 ^ m)%N = pow4 (N.to_nat m).
Proof.
  rewrite <- (N2Nat.id m) at 1.
  apply N_pow4_of_nat.
Qed.

Lemma s4_N_to_nat (m : N) : N.to_nat ((4 ^ m - 1) / 3)%N = sum4 (N.to_nat m).
Proof.
  pose proof (sum4_spec (N.to_nat m)) as hs.
  pose proof (pow4_pos (N.to_nat m)) as hp.
  rewrite <- N_pow4_to_nat in hs, hp.
  lia.
Qed.

Lemma N_shiftl_double_pow4 (vA m : N) :
  N.shiftl vA (N.double m) = (vA * 4 ^ m)%N.
Proof.
  rewrite N.shiftl_mul_pow2, N.double_spec.
  change 4%N with (2 ^ 2)%N.
  rewrite <- N.pow_mul_r. reflexivity.
Qed.

Lemma N_shiftl_1_pow4 (m : N) :
  N.to_nat (N.shiftl 1%N (N.double m)) = pow4 (N.to_nat m).
Proof.
  rewrite N_shiftl_double_pow4, N.mul_1_l.
  apply N_pow4_to_nat.
Qed.

Lemma N_shiftl_1_s4 (m : N) :
  N.to_nat ((N.shiftl 1%N (N.double m) - 1) / 3)%N = sum4 (N.to_nat m).
Proof.
  rewrite N_shiftl_double_pow4, N.mul_1_l.
  apply s4_N_to_nat.
Qed.

Lemma N_even_mod2 (x : N) : N.even x = true <-> (x mod 2 = 0)%N.
Proof.
  rewrite N.even_spec. split; intros H.
  - destruct H as [k ->]. lia.
  - exists (x / 2)%N. lia.
Qed.

Lemma N_even_false_mod2 (x : N) : N.even x = false <-> (x mod 2 = 1)%N.
Proof.
  destruct (N.even x) eqn:E.
  - apply N_even_mod2 in E. split; [discriminate | lia].
  - split; [intros _; destruct (N.eq_dec (x mod 2)%N 0%N) as [h0 | h1];
      [apply N_even_mod2 in h0; congruence | lia] | intros _; reflexivity].
Qed.

Lemma N_odd_mod2 (x : N) : N.odd x = true <-> (x mod 2 = 1)%N.
Proof.
  rewrite N.odd_spec. split; intros H.
  - destruct H as [k ->]. lia.
  - exists (x / 2)%N. lia.
Qed.

Lemma Z_even_mod2 (x : Z) : Z.even x = true <-> (x mod 2 = 0)%Z.
Proof.
  rewrite Z.even_spec. split; intros H.
  - destruct H as [k ->]. lia.
  - exists (x / 2)%Z. lia.
Qed.

Lemma Z_even_false_mod2 (x : Z) : Z.even x = false <-> (x mod 2 = 1)%Z.
Proof.
  destruct (Z.even x) eqn:E.
  - apply Z_even_mod2 in E. split; [discriminate | lia].
  - split; [intros _; destruct (Z.eq_dec (x mod 2)%Z 0%Z) as [h0 | h1];
      [apply Z_even_mod2 in h0; congruence | lia] | intros _; reflexivity].
Qed.

Lemma sum4_10_Z : Z.of_nat (sum4 10) = 349525%Z.
Proof.
  change 10 with (N.to_nat 10%N).
  rewrite <- (s4_N_to_nat 10%N).
  change (((4 ^ 10 - 1) / 3)%N) with 349525%N.
  lia.
Qed.

Lemma sum4_lower_Z (m : nat) :
  10 <= m -> (15000 * Z.of_nat m + 150000 <= Z.of_nat (sum4 m))%Z.
Proof.
  induction m as [| m IH]; [lia |].
  intros hm.
  destruct (Nat.eq_dec m 9) as [-> | hne].
  - change (S 9) with 10. rewrite sum4_10_Z. lia.
  - assert (h10 : 10 <= m) by lia.
    specialize (IH h10). cbn [sum4]. lia.
Qed.

Lemma sum4_ge_21_Z (k : nat) :
  4 <= k -> (21 * Z.of_nat k + 1 <= Z.of_nat (sum4 k))%Z.
Proof.
  induction k as [| k IH]; [lia |].
  intros hk.
  destruct (Nat.eq_dec k 3) as [-> | hne].
  - cbn [sum4]. lia.
  - assert (h4 : 4 <= k) by lia.
    specialize (IH h4). cbn [sum4]. lia.
Qed.

Lemma super4x_pre1 (r : side) :
  (0inf {{C}}> (S0 >> rep001 3 r)) -->+
  (0inf {{C}}> (S1 >> rep001 4 (S0 >> r))).
Proof.
  cbn [rep001]. fast_start_progress.
Qed.

Lemma super4x_pre2 (r : side) :
  (0inf {{C}}> (S1 >> rep001 4 (S0 >> rep001 2 r))) -->+
  (rep110 6 (S1 >> S1 >> 0inf) {{C}}> (S0 >> S1 >> r)).
Proof.
  cbn [rep001 rep110]. fast_start_progress.
Qed.

Lemma super4x_partA (a d : nat) (r : side) :
  (0inf {{C}}> (S0 >> rep001 (2 * (a + 3)) (S0 >> rep001 (2 * (2 * (a + 3)) + 1 + d) r))) -->+
  (rep110 (2 * (2 * a + 5)) (S1 >> S1 >> 0inf) {{C}}>
    (S0 >> S0 >> S1 >> rep001 (4 * a + 12 + d) r)).
Proof.
  set (r0 := S0 >> rep001 (2 * (2 * (a + 3)) + 1 + d) r).
  replace (2 * (a + 3)) with (3 + (2 + (2 * a + 1))) by lia.
  rewrite (rep001_add 3 (2 + (2 * a + 1))), (rep001_add 2 (2 * a + 1)).
  pose proof (super4x_pre1 (rep001 2 (rep001 (2 * a + 1) r0))) as hp1.
  pose proof (super4x_pre2 (rep001 (2 * a + 1) r0)) as hp2.
  pose proof (era_drain_iter (2 * a) 2 r0) as hdr.
  replace (2 * (2 + 1)) with 6 in hdr by lia.
  replace (2 * (2 + 1 + (2 * a + 1))) with (2 * (2 * a + 4)) in hdr by lia.
  pose proof (reach_splitL_lb (2 * a + 4) (S1 >> S1 >> 0inf) (S1 >> r0)) as hs19.
  assert (ht19 : ((S1 >> S1 >> 0inf) {{C}}> (S0 >> rep001 (2 * (2 * a + 4)) (S1 >> r0))) -->+
                 ((S1 >> 0inf) {{C}}> (S1 >> rep001 (4 * a + 9) (S1 >> r0)))).
  { replace (4 * a + 9) with (1 + 2 * (2 * a + 4)) by lia.
    rewrite (rep001_add 1 (2 * (2 * a + 4))).
    cbn [rep001]. fast_start_progress. }
  pose proof (reach_splitR_lb (4 * a + 9) (S1 >> 0inf) (S1 >> r0)) as hs20.
  pose proof (pev (reach_R1_lb (rep110 (4 * a + 9) (S1 >> 0inf)) r0)) as ht20.
  assert (hl21 : rep110 (4 * a + 9) (S1 >> 0inf) =
                 rep110 (2 * (2 * a + 4)) (S1 >> S1 >> S0 >> S1 >> 0inf)).
  { replace (4 * a + 9) with (2 * (2 * a + 4) + 1) by lia.
    rewrite (rep110_add (2 * (2 * a + 4)) 1). reflexivity. }
  pose proof (reach_splitL_lb (2 * a + 4) (S1 >> S1 >> S0 >> S1 >> 0inf) (S0 >> r0)) as hs21.
  rewrite <- hl21 in hs21.
  assert (ht21 : ((S1 >> S1 >> S0 >> S1 >> 0inf) {{C}}> (S0 >> rep001 (2 * (2 * a + 4)) (S0 >> r0))) -->+
                 ((S1 >> S1 >> 0inf) {{C}}> (S1 >> rep001 (4 * a + 9) (S0 >> r0)))).
  { replace (4 * a + 9) with (1 + 2 * (2 * a + 4)) by lia.
    rewrite (rep001_add 1 (2 * (2 * a + 4))).
    cbn [rep001]. fast_start_progress. }
  assert (hr0_eq : S0 >> r0 = S0 >> S0 >> S0 >> S0 >> S1 >> rep001 (4 * a + 12 + d) r).
  { unfold r0.
    replace (2 * (2 * (a + 3)) + 1 + d) with (1 + (4 * a + 12 + d)) by lia.
    rewrite (rep001_add 1 (4 * a + 12 + d)). reflexivity. }
  assert (hs22 : ((S1 >> S1 >> 0inf) {{C}}> (S1 >> rep001 (4 * a + 9) (S0 >> r0))) -->*
                 (rep110 (4 * a + 9) (S1 >> S1 >> 0inf) {{C}}>
                   (S1 >> S0 >> S0 >> S0 >> S0 >> S1 >> rep001 (4 * a + 12 + d) r))).
  { rewrite hr0_eq.
    exact (reach_splitR_lb (4 * a + 9) (S1 >> S1 >> 0inf) _). }
  pose proof (pev (reach_R2_lb S0 (rep110 (4 * a + 9) (S1 >> S1 >> 0inf))
                    (S0 >> S1 >> rep001 (4 * a + 12 + d) r))) as ht22.
  assert (hl22 : (S1 >> S1 >> S0 >> rep110 (4 * a + 9) (S1 >> S1 >> 0inf)) =
                 rep110 (2 * (2 * a + 5)) (S1 >> S1 >> 0inf)).
  { replace (2 * (2 * a + 5)) with (1 + (4 * a + 9)) by lia.
    rewrite (rep110_add 1 (4 * a + 9)). reflexivity. }
  rewrite hl22 in ht22.
  pose proof (ptrans (ptrans hp1 hp2) hdr) as hpre.
  pose proof (etrans hs19 (etrans (pev ht19) (etrans hs20
               (etrans ht20 (etrans hs21 (etrans (pev ht21) (etrans hs22 ht22))))))) as htail.
  exact (ps_trans hpre htail).
Qed.

Lemma super4x_partB (a d : nat) (r : side) :
  (rep110 (2 * (2 * a + 5)) (S1 >> S1 >> 0inf) {{C}}>
    (S0 >> S0 >> S1 >> rep001 (4 * a + 12 + d) r)) -->*
  (0inf {{C}}> (S0 >> rep001 (4 * (2 * (a + 3))) (S0 >> rep001 d r))).
Proof.
  set (r22 := S0 >> S1 >> rep001 (4 * a + 12 + d) r).
  pose proof (reach_splitL_lb (2 * a + 5) (S1 >> S1 >> 0inf) r22) as hs23.
  assert (ht23 : ((S1 >> S1 >> 0inf) {{C}}> (S0 >> rep001 (2 * (2 * a + 5)) r22)) -->*
                 ((S1 >> 0inf) {{C}}> (S1 >> rep001 (4 * a + 11) r22))).
  { replace (4 * a + 11) with (1 + 2 * (2 * a + 5)) by lia.
    rewrite (rep001_add 1 (2 * (2 * a + 5))).
    cbn [rep001]. fast_execute. }
  assert (hr24_eq : r22 = S0 >> S1 >> S0 >> S0 >> S1 >> rep001 (4 * a + 11 + d) r).
  { unfold r22.
    replace (4 * a + 12 + d) with (1 + (4 * a + 11 + d)) by lia.
    rewrite (rep001_add 1 (4 * a + 11 + d)). reflexivity. }
  assert (hs24 : ((S1 >> 0inf) {{C}}> (S1 >> rep001 (4 * a + 11) r22)) -->*
                 (rep110 (4 * a + 11) (S1 >> 0inf) {{C}}>
                   (S1 >> S0 >> S1 >> S0 >> S0 >> S1 >> rep001 (4 * a + 11 + d) r))).
  { rewrite hr24_eq.
    exact (reach_splitR_lb (4 * a + 11) (S1 >> 0inf) _). }
  pose proof (pev (reach_R3_lb (rep110 (4 * a + 11) (S1 >> 0inf))
                    (S0 >> S1 >> rep001 (4 * a + 11 + d) r))) as ht24.
  assert (hr24_out : (S0 >> S0 >> S0 >> S1 >> rep001 (4 * a + 11 + d) r) =
                     S0 >> rep001 ((4 * a + 10 + 1) + (1 + d)) r).
  { replace ((4 * a + 10 + 1) + (1 + d)) with (1 + (4 * a + 11 + d)) by lia.
    rewrite (rep001_add 1 (4 * a + 11 + d)). reflexivity. }
  rewrite hr24_out, (rep001_add (4 * a + 10 + 1) (1 + d)) in ht24.
  pose proof (pev (era_osc_iter (4 * a + 10) 0 (S1 >> 0inf) (rep001 (1 + d) r))) as hosc.
  replace (4 * a + 10 + 1) with (4 * a + 11) in ht24, hosc by lia.
  replace (2 * 0) with 0 in hosc by lia.
  replace (0 + (4 * a + 11)) with (4 * a + 11) in hosc by lia.
  cbn [rep001] in hosc.
  assert (hr26_eq : S0 >> rep001 (1 + d) r = S0 >> S0 >> S0 >> S1 >> rep001 d r).
  { rewrite (rep001_add 1 d). reflexivity. }
  assert (hs26 : ((S0 >> S1 >> 0inf) {{C}}>
                    (S1 >> rep001 (2 * (4 * a + 11)) (S0 >> rep001 (1 + d) r))) -->*
                 (rep110 (2 * (4 * a + 11)) (S0 >> S1 >> 0inf) {{C}}>
                    (S1 >> S0 >> S0 >> S0 >> S1 >> rep001 d r))).
  { rewrite hr26_eq.
    exact (reach_splitR_lb (2 * (4 * a + 11)) (S0 >> S1 >> 0inf) _). }
  pose proof (pev (reach_R2_lb S0 (rep110 (2 * (4 * a + 11)) (S0 >> S1 >> 0inf))
                    (S1 >> rep001 d r))) as ht26.
  rewrite <- (rep110_shift (2 * (4 * a + 11))) in ht26.
  pose proof (reach_splitL_lb (4 * a + 11)
                (S1 >> S1 >> S0 >> S0 >> S1 >> 0inf) (S1 >> rep001 d r)) as hs27.
  assert (ht27 : ((S1 >> S1 >> S0 >> S0 >> S1 >> 0inf) {{C}}>
                    (S0 >> rep001 (2 * (4 * a + 11)) (S1 >> rep001 d r))) -->*
                 ((S1 >> S1 >> 0inf) {{C}}>
                    (S1 >> rep001 (8 * a + 23) (S1 >> rep001 d r)))).
  { replace (8 * a + 23) with (1 + 2 * (4 * a + 11)) by lia.
    rewrite (rep001_add 1 (2 * (4 * a + 11))).
    cbn [rep001]. fast_execute. }
  pose proof (reach_splitR_lb (8 * a + 23) (S1 >> S1 >> 0inf) (S1 >> rep001 d r)) as hs28.
  pose proof (pev (reach_R1_lb (rep110 (8 * a + 23) (S1 >> S1 >> 0inf)) (rep001 d r))) as ht28.
  assert (hl29 : rep110 (8 * a + 23) (S1 >> S1 >> 0inf) =
                 rep110 (2 * (4 * a + 11)) (S1 >> S1 >> S0 >> S1 >> S1 >> 0inf)).
  { replace (8 * a + 23) with (2 * (4 * a + 11) + 1) by lia.
    rewrite (rep110_add (2 * (4 * a + 11)) 1). reflexivity. }
  pose proof (reach_splitL_lb (4 * a + 11)
                (S1 >> S1 >> S0 >> S1 >> S1 >> 0inf) (S0 >> rep001 d r)) as hs29.
  rewrite <- hl29 in hs29.
  assert (ht29 : ((S1 >> S1 >> S0 >> S1 >> S1 >> 0inf) {{C}}>
                    (S0 >> rep001 (2 * (4 * a + 11)) (S0 >> rep001 d r))) -->*
                 (0inf {{C}}> (S0 >> rep001 (4 * (2 * (a + 3))) (S0 >> rep001 d r)))).
  { replace (4 * (2 * (a + 3))) with (2 + 2 * (4 * a + 11)) by lia.
    rewrite (rep001_add 2 (2 * (4 * a + 11))).
    cbn [rep001].
    do 6 fast_step.
    fast_finish. }
  exact (etrans hs23 (etrans ht23 (etrans hs24 (etrans ht24
          (etrans hosc (etrans hs26 (etrans ht26 (etrans hs27
            (etrans ht27 (etrans hs28 (etrans ht28 (etrans hs29 ht29)))))))))))).
Qed.

Lemma super4x_one (a d : nat) (r : side) :
  (0inf {{C}}> (S0 >> rep001 (2 * (a + 3)) (S0 >> rep001 (2 * (2 * (a + 3)) + 1 + d) r))) -->+
  (0inf {{C}}> (S0 >> rep001 (4 * (2 * (a + 3))) (S0 >> rep001 d r))).
Proof.
  exact (ps_trans (super4x_partA a d r) (super4x_partB a d r)).
Qed.

Lemma super4x_iter : forall (m a d : nat) (r : side),
  (0inf {{C}}> (S0 >> rep001 (2 * (a + 3))
    (S0 >> rep001 (2 * (2 * (a + 3)) * sum4 m + m + d) r))) -->*
  (0inf {{C}}> (S0 >> rep001 ((2 * (a + 3)) * pow4 m) (S0 >> rep001 d r))).
Proof.
  induction m as [| m IH]; intros a d r.
  - cbn [sum4 pow4].
    replace (2 * (2 * (a + 3)) * 0 + 0 + d) with d by lia.
    replace ((2 * (a + 3)) * 1) with (2 * (a + 3)) by lia.
    apply evstep_refl.
  - assert (hdr_eq : 2 * (2 * (a + 3)) * sum4 (S m) + S m + d =
                     2 * (2 * (a + 3)) + 1 + (2 * (2 * (4 * a + 9 + 3)) * sum4 m + m + d)).
    { clear. cbn [sum4]. nia. }
    rewrite hdr_eq.
    pose proof (pev (super4x_one a (2 * (2 * (4 * a + 9 + 3)) * sum4 m + m + d) r)) as h1.
    replace (4 * (2 * (a + 3))) with (2 * (4 * a + 9 + 3)) in h1 by lia.
    pose proof (IH (4 * a + 9) d r) as h2.
    replace ((2 * (4 * a + 9 + 3)) * pow4 m) with ((2 * (a + 3)) * pow4 (S m)) in h2
      by (clear; cbn [pow4]; nia).
    exact (etrans h1 h2).
Qed.

Lemma super4x_iter_plus (m a d : nat) (hm : 0 < m) (r : side) :
  (0inf {{C}}> (S0 >> rep001 (2 * (a + 3))
    (S0 >> rep001 (2 * (2 * (a + 3)) * sum4 m + m + d) r))) -->+
  (0inf {{C}}> (S0 >> rep001 ((2 * (a + 3)) * pow4 m) (S0 >> rep001 d r))).
Proof.
  destruct m as [| k]; [lia |].
  assert (hdr_eq : 2 * (2 * (a + 3)) * sum4 (S k) + S k + d =
                   2 * (2 * (a + 3)) + 1 + (2 * (2 * (4 * a + 9 + 3)) * sum4 k + k + d)).
  { clear. cbn [sum4]. nia. }
  rewrite hdr_eq.
  pose proof (super4x_one a (2 * (2 * (4 * a + 9 + 3)) * sum4 k + k + d) r) as h1.
  replace (4 * (2 * (a + 3))) with (2 * (4 * a + 9 + 3)) in h1 by lia.
  pose proof (super4x_iter k (4 * a + 9) d r) as h2.
  replace ((2 * (4 * a + 9 + 3)) * pow4 k) with ((2 * (a + 3)) * pow4 (S k)) in h2
    by (clear; cbn [pow4]; nia).
  exact (ps_trans h1 h2).
Qed.

(* ========================================================================== *)
(* Layer 2: Fast Concrete Macro Executor Over Binary N                        *)
(* ========================================================================== *)

Inductive LChunk : Type :=
  | lb0_c : LChunk
  | lb1_c : LChunk
  | lt110 (m : N) : LChunk.

Inductive RChunk : Type :=
  | rb0_c : RChunk
  | rb1_c : RChunk
  | rt001 (m : N) : RChunk.

Record State : Type := mkState {
  st_hd : Sym;
  st_l : list LChunk;
  st_r : list RChunk;
}.

Fixpoint exL (l : list LChunk) : side :=
  match l with
  | [] => 0inf
  | lb0_c :: tl => S0 >> exL tl
  | lb1_c :: tl => S1 >> exL tl
  | lt110 m :: tl => rep110 (N.to_nat m + 1) (exL tl)
  end.

Fixpoint exR (r : list RChunk) : side :=
  match r with
  | [] => 0inf
  | rb0_c :: tl => S0 >> exR tl
  | rb1_c :: tl => S1 >> exR tl
  | rt001 m :: tl => rep001 (N.to_nat m + 1) (exR tl)
  end.

Definition encode (s : State) : Q * tape :=
  (exL (st_l s)) {{C}}> ((st_hd s) >> exR (st_r s)).

Definition p60Cfg (a b : nat) : Q * tape :=
  0inf {{C}}> (S0 >> rep001 (a - 1) (S0 >> rep001 (b - 1) 0inf)).

Definition attractorCfg (n : nat) : Q * tape :=
  (rep110 n (S1 >> 0inf)) {{C}}> (S0 >> 0inf).

Definition pushL110 (m : N) (l : list LChunk) : list LChunk :=
  match l with
  | lt110 k :: tl => lt110 (m + 1 + k)%N :: tl
  | _ => lt110 m :: l
  end.

Definition pushLN110 (n : N) (l : list LChunk) : list LChunk :=
  if (n =? 0)%N then l else pushL110 (n - 1)%N l.

Definition pushL0 (l : list LChunk) : list LChunk :=
  match l with
  | [] => []
  | _ => lb0_c :: l
  end.

Definition pushL1 (l : list LChunk) : list LChunk :=
  match l with
  | lb1_c :: lb0_c :: tl => pushL110 0%N tl
  | _ => lb1_c :: l
  end.

Definition pushR001 (m : N) (r : list RChunk) : list RChunk :=
  match r with
  | rt001 k :: tl => rt001 (m + 1 + k)%N :: tl
  | _ => rt001 m :: r
  end.

Definition pushRN001 (n : N) (r : list RChunk) : list RChunk :=
  if (n =? 0)%N then r else pushR001 (n - 1)%N r.

Definition pushR0 (r : list RChunk) : list RChunk :=
  match r with
  | [] => []
  | rb0_c :: rb1_c :: tl => pushR001 0%N tl
  | _ => rb0_c :: r
  end.

Definition pushR1 (r : list RChunk) : list RChunk := rb1_c :: r.

Definition popL (l : list LChunk) : Sym * list LChunk :=
  match l with
  | [] => (S0, [])
  | lb0_c :: tl => (S0, tl)
  | lb1_c :: tl => (S1, tl)
  | lt110 m :: tl =>
    if (m =? 0)%N then (S1, lb1_c :: lb0_c :: tl)
    else (S1, lb1_c :: lb0_c :: lt110 (m - 1)%N :: tl)
  end.

Definition popR (r : list RChunk) : Sym * list RChunk :=
  match r with
  | [] => (S0, [])
  | rb0_c :: tl => (S0, tl)
  | rb1_c :: tl => (S1, tl)
  | rt001 m :: tl =>
    if (m =? 0)%N then (S0, rb0_c :: rb1_c :: tl)
    else (S0, rb0_c :: rb1_c :: rt001 (m - 1)%N :: tl)
  end.

Fixpoint splitRChunk (l : list LChunk) (r : list RChunk) {struct r} : list LChunk * list RChunk :=
  match r with
  | rt001 m :: r' => splitRChunk (pushL110 m l) r'
  | _ => (l, r)
  end.

Fixpoint splitLChunk (l : list LChunk) (r : list RChunk) {struct l} : list LChunk * list RChunk :=
  match l with
  | lt110 m :: tl =>
    if (m =? 0)%N then (l, r)
    else
      let m1 := (m - 1)%N in
      let p := N.div2 m1 in
      let r1 := pushR001 (N.succ_double p) r in
      if N.even m1 then splitLChunk tl r1
      else (lt110 0%N :: tl, r1)
  | _ => (l, r)
  end.

Fixpoint stripOnesL (l : list LChunk) (r : list RChunk) {struct l} : list LChunk * list RChunk :=
  match l with
  | [] => ([], r)
  | lb0_c :: tl => (tl, r)
  | lb1_c :: tl => stripOnesL tl (pushR0 r)
  | lt110 m :: tl =>
    if (m =? 0)%N then (tl, pushR0 (pushR0 r))
    else (lt110 (m - 1)%N :: tl, pushR0 (pushR0 r))
  end.

Definition checkS4x (vA vB m : N) : option (N * N) :=
  if (0 <? m)%N then
    let sh := N.double m in
    let vA_p4 := N.shiftl vA sh in
    let twoA := N.double vA in
    let twoA_s4 := ((N.double vA_p4 - twoA) / 3)%N in
    let dr := (twoA_s4 + m)%N in
    if (dr + 1 <=? vB)%N then Some (vA_p4, dr) else None
  else None.

Definition findS4x (vA vB : N) : option (N * N * N) :=
  let twoA := N.double vA in
  if (twoA + 2 <=? vB)%N then
    let lnum := N.log2 (N.double vB + vB)%N in
    let lden := N.log2 twoA in
    let e := (lnum - lden)%N in
    let m0 := N.div2 (e + 1)%N in
    match checkS4x vA vB m0 with
    | Some (vA_p4, dr) => Some (m0, vA_p4, dr)
    | None =>
      match checkS4x vA vB (m0 - 1)%N with
      | Some (vA_p4, dr) => Some ((m0 - 1)%N, vA_p4, dr)
      | None =>
        match checkS4x vA vB (m0 - 2)%N with
        | Some (vA_p4, dr) => Some ((m0 - 2)%N, vA_p4, dr)
        | None => None
        end
      end
    end
  else None.

Definition trySuper4x (hd : Sym) (l : list LChunk) (r : list RChunk) : option State :=
  match hd, l, r with
  | S0, [], rt001 a_m1 :: rb0_c :: rt001 b_m1 :: rtail =>
    if (5 <=? a_m1)%N && N.odd a_m1 then
      let vA := (a_m1 + 1)%N in
      let vB := (b_m1 + 1)%N in
      match findS4x vA vB with
      | Some (_, vA_p4, dr) =>
        Some (mkState S0 [] (rt001 (vA_p4 - 1)%N :: rb0_c :: rt001 (vB - (dr + 1))%N :: rtail))
      | None => None
      end
    else None
  | _, _, _ => None
  end.

Definition tryEraDrain (hd : Sym) (l : list LChunk) (r : list RChunk) : option State :=
  match hd, l, r with
  | S0, [lt110 m_val; lb1_c; lb1_c], rb1_c :: rt001 c_m1 :: rtail =>
    if (1 <=? m_val)%N && N.even (m_val - 1)%N then
      Some (mkState S0 [lt110 (m_val + N.double (c_m1 + 1))%N; lb1_c; lb1_c] (pushR1 rtail))
    else None
  | _, _, _ => None
  end.

Definition tryEraOscR (r : list RChunk) : option (N * N * list RChunk) :=
  match r with
  | rb0_c :: rt001 c_m1 :: rtail => Some (0%N, c_m1, rtail)
  | rt001 m_val :: rb0_c :: rt001 c_m1 :: rtail =>
    if (1 <=? m_val)%N && N.even (m_val - 1)%N then
      Some ((N.div2 (m_val - 1) + 1)%N, c_m1, rtail)
    else None
  | _ => None
  end.

Definition tryEraOsc (hd : Sym) (l : list LChunk) (r : list RChunk) : option State :=
  match hd, l with
  | S1, lb0_c :: lt110 a_m1 :: ltail =>
    match tryEraOscR r with
    | Some (j, c_m1, rtail) =>
      let n_m1 := N.min a_m1 c_m1 in
      let l_new := pushL0 (pushLN110 (a_m1 - n_m1)%N ltail) in
      let r_new := pushR001 (N.succ_double (j + n_m1)%N) (pushR0 (pushRN001 (c_m1 - n_m1)%N rtail)) in
      Some (mkState S1 l_new r_new)
    | None => None
    end
  | S1, lb1_c :: lb0_c :: lt110 a_m1 :: ltail =>
    match tryEraOscR r with
    | Some (j, c_m1, rtail) =>
      let n_m1 := N.min a_m1 c_m1 in
      let l_new := pushL1 (pushL0 (pushLN110 (a_m1 - n_m1)%N ltail)) in
      let r_new := pushR001 (N.succ_double (j + n_m1)%N) (pushR0 (pushRN001 (c_m1 - n_m1)%N rtail)) in
      Some (mkState S1 l_new r_new)
    | None => None
    end
  | _, _ => None
  end.

Definition stepBase (hd : Sym) (l : list LChunk) (r : list RChunk) : option State :=
  match baseDispatch (fun l r => Some (splitLChunk l r))
    (fun l r => Some (stripOnesL l r)) splitRChunk
    (fun l => Some (popL l)) (fun r => Some (popR r))
    pushL0 pushL1 (pushL110 0%N) pushR0 pushR1 (pushR001 0%N) hd l r with
  | Some (hd', l', r') => Some (mkState hd' l' r')
  | None => None
  end.

Definition stepFast (s : State) : option State :=
  match trySuper4x (st_hd s) (st_l s) (st_r s) with
  | Some s' => Some s'
  | None =>
    match tryEraDrain (st_hd s) (st_l s) (st_r s) with
    | Some s' => Some s'
    | None =>
      match tryEraOsc (st_hd s) (st_l s) (st_r s) with
      | Some s' => Some s'
      | None => stepBase (st_hd s) (st_l s) (st_r s)
      end
    end
  end.

Definition optBind {X Y : Type} (ox : option X) (f : X -> option Y) : option Y :=
  match ox with
  | Some x => f x
  | None => None
  end.

Fixpoint iterPow2 (k : nat) (s : State) : option State :=
  match k with
  | 0 => stepFast s
  | S k' => optBind (iterPow2 k' s) (iterPow2 k')
  end.

(* Soundness of Concrete Executor *)

Lemma exL_pushL110 (m : N) (l : list LChunk) :
  exL (pushL110 m l) = rep110 (N.to_nat m + 1) (exL l).
Proof.
  destruct l as [| [| | k] tl]; try reflexivity.
  cbn [pushL110 exL].
  replace (N.to_nat (m + 1 + k)%N + 1) with ((N.to_nat m + 1) + (N.to_nat k + 1)) by lia.
  apply rep110_add.
Qed.

Lemma exL_pushLN110 (n : N) (l : list LChunk) :
  exL (pushLN110 n l) = rep110 (N.to_nat n) (exL l).
Proof.
  unfold pushLN110.
  destruct (N.eqb_spec n 0%N) as [-> | hne]; [reflexivity |].
  rewrite exL_pushL110. f_equal. lia.
Qed.

Lemma exL_pushL0 (l : list LChunk) :
  exL (pushL0 l) = S0 >> exL l.
Proof.
  destruct l; [cbn [pushL0 exL]; symmetry; exact cons_zero_0inf | reflexivity].
Qed.

Lemma exL_pushL1 (l : list LChunk) :
  exL (pushL1 l) = S1 >> exL l.
Proof.
  destruct l as [| [| | ?] [| [| | ?] tl]]; try reflexivity.
  cbn [pushL1]. rewrite exL_pushL110. reflexivity.
Qed.

Lemma exR_pushR001 (m : N) (r : list RChunk) :
  exR (pushR001 m r) = rep001 (N.to_nat m + 1) (exR r).
Proof.
  destruct r as [| [| | k] tl]; try reflexivity.
  cbn [pushR001 exR].
  replace (N.to_nat (m + 1 + k)%N + 1) with ((N.to_nat m + 1) + (N.to_nat k + 1)) by lia.
  apply rep001_add.
Qed.

Lemma exR_pushRN001 (n : N) (r : list RChunk) :
  exR (pushRN001 n r) = rep001 (N.to_nat n) (exR r).
Proof.
  unfold pushRN001.
  destruct (N.eqb_spec n 0%N) as [-> | hne]; [reflexivity |].
  rewrite exR_pushR001. f_equal. lia.
Qed.

Lemma exR_pushR0 (r : list RChunk) :
  exR (pushR0 r) = S0 >> exR r.
Proof.
  destruct r as [| [| | ?] [| [| | ?] tl]];
    try reflexivity;
    try (cbn [pushR0 exR]; symmetry; exact cons_zero_0inf).
  cbn [pushR0]. rewrite exR_pushR001. reflexivity.
Qed.

Lemma popL_ok (l : list LChunk) :
  exL l = fst (popL l) >> exL (snd (popL l)).
Proof.
  destruct l as [| [| | m] tl];
    [cbn [popL fst snd exL]; symmetry; exact cons_zero_0inf | reflexivity | reflexivity |].
  cbn [popL].
  destruct (N.eqb_spec m 0%N) as [-> | hne]; [reflexivity |].
  cbn [fst snd exL].
  replace (N.to_nat m + 1) with (1 + (N.to_nat (m - 1)%N + 1)) by lia.
  rewrite (rep110_add 1). reflexivity.
Qed.

Lemma popR_ok (r : list RChunk) :
  exR r = fst (popR r) >> exR (snd (popR r)).
Proof.
  destruct r as [| [| | m] tl];
    [cbn [popR fst snd exR]; symmetry; exact cons_zero_0inf | reflexivity | reflexivity |].
  cbn [popR].
  destruct (N.eqb_spec m 0%N) as [-> | hne]; [reflexivity |].
  cbn [fst snd exR].
  replace (N.to_nat m + 1) with (1 + (N.to_nat (m - 1)%N + 1)) by lia.
  rewrite (rep001_add 1). reflexivity.
Qed.

Lemma splitRChunk_ok : forall (r : list RChunk) (l : list LChunk),
  (exL l {{C}}> (S1 >> exR r)) -->*
  (exL (fst (splitRChunk l r)) {{C}}> (S1 >> exR (snd (splitRChunk l r)))).
Proof.
  induction r as [| [| | m] r IH]; intros l; try apply evstep_refl.
  cbn [splitRChunk exR].
  pose proof (reach_splitR_lb (N.to_nat m + 1) (exL l) (exR r)) as h1.
  rewrite <- (exL_pushL110 m l) in h1.
  exact (etrans h1 (IH (pushL110 m l))).
Qed.

Lemma splitLChunk_ok : forall (l : list LChunk) (r : list RChunk),
  (exL l {{C}}> (S0 >> exR r)) -->*
  (exL (fst (splitLChunk l r)) {{C}}> (S0 >> exR (snd (splitLChunk l r)))).
Proof.
  induction l as [| [| | m] tl IH]; intros r; try apply evstep_refl.
  cbn [splitLChunk].
  destruct (N.eqb_spec m 0%N) as [-> | hne]; [apply evstep_refl |].
  set (m1 := (m - 1)%N).
  set (p := N.div2 m1).
  set (r1 := pushR001 (N.succ_double p) r).
  assert (hp_eq : p = (m1 / 2)%N) by (unfold p; apply N.div2_div).
  assert (hr_eq : rep001 (2 * (N.to_nat p + 1)) (exR r) = exR r1).
  { unfold r1. rewrite exR_pushR001, N.succ_double_spec. f_equal. lia. }
  destruct (N.even m1) eqn:Eev.
  - apply N_even_mod2 in Eev.
    cbn [exL].
    replace (N.to_nat m + 1) with (2 * (N.to_nat p + 1))
      by (clear - hne hp_eq Eev; unfold m1 in *; lia).
    pose proof (reach_splitL_lb (N.to_nat p + 1) (exL tl) (exR r)) as h1.
    rewrite hr_eq in h1.
    exact (etrans h1 (IH r1)).
  - apply N_even_false_mod2 in Eev.
    cbn [fst snd exL].
    replace (N.to_nat m + 1) with (2 * (N.to_nat p + 1) + 1)
      by (clear - hne hp_eq Eev; unfold m1 in *; lia).
    rewrite (rep110_add (2 * (N.to_nat p + 1)) 1).
    pose proof (reach_splitL_lb (N.to_nat p + 1) (rep110 1 (exL tl)) (exR r)) as h1.
    rewrite hr_eq in h1.
    exact h1.
Qed.

Lemma stripOnesD_ok : forall (l : list LChunk) (r : list RChunk),
  (exL l <{{D}} exR r) -->*
  (exL (fst (stripOnesL l r)) {{D}}> (S0 >> exR (snd (stripOnesL l r)))).
Proof.
  induction l as [| [| | m] tl IH]; intros r.
  - cbn [stripOnesL fst snd exL]. apply evstep_refl.
  - cbn [stripOnesL fst snd exL]. apply evstep_refl.
  - cbn [stripOnesL exL].
    assert (h1 : ((S1 >> exL tl) <{{D}} exR r) -->* (exL tl <{{D}} exR (pushR0 r))).
    { rewrite exR_pushR0. fast_execute. }
    exact (etrans h1 (IH (pushR0 r))).
  - cbn [stripOnesL].
    destruct (N.eqb_spec m 0%N) as [-> | hne].
    + cbn [fst snd exL rep110]. rewrite !exR_pushR0. fast_execute.
    + cbn [fst snd exL].
      replace (N.to_nat m + 1) with (1 + (N.to_nat (m - 1)%N + 1)) by lia.
      rewrite (rep110_add 1). cbn [rep110]. rewrite !exR_pushR0. fast_execute.
Qed.

Lemma checkS4x_some (vA vB m vA_p4 dr : N) :
  checkS4x vA vB m = Some (vA_p4, dr) ->
  (0 < m)%N /\
  vA_p4 = (vA * 4 ^ m)%N /\
  dr = (2 * vA * ((4 ^ m - 1) / 3) + m)%N /\
  (dr + 1 <= vB)%N.
Proof.
  unfold checkS4x.
  destruct (N.ltb_spec 0%N m) as [hm | _]; [| discriminate].
  cbv zeta.
  destruct (N.leb_spec ((((N.double (N.shiftl vA (N.double m)) - N.double vA) / 3) + m) + 1)%N vB)
    as [hB | _]; [| discriminate].
  intros H; apply some_inj, pair_inj in H; destruct H as [<- <-].
  rewrite N_shiftl_double_pow4 in *.
  set (p4 := (4 ^ m)%N) in *.
  set (s4 := ((p4 - 1) / 3)%N).
  assert (hs4_id : (3 * s4 + 1 = p4)%N).
  { pose proof (sum4_spec (N.to_nat m)) as hs.
    pose proof (pow4_pos (N.to_nat m)) as hp.
    rewrite <- N_pow4_to_nat in hs, hp.
    pose proof (s4_N_to_nat m) as hs2.
    unfold p4, s4 in *. lia. }
  assert (hdiv : ((N.double (vA * p4) - N.double vA) / 3)%N = (2 * vA * s4)%N).
  { assert (heq : (N.double (vA * p4) - N.double vA)%N = (3 * (2 * vA * s4))%N).
    { pose proof (N.double_spec (vA * p4)%N) as hd1.
      pose proof (N.double_spec vA) as hd2.
      clear - hs4_id hd1 hd2. nia. }
    rewrite heq. lia. }
  rewrite hdiv in hB |- *.
  exact (conj hm (conj eq_refl (conj eq_refl hB))).
Qed.

Lemma findS4x_some (vA vB m vA_p4 dr : N) :
  findS4x vA vB = Some (m, vA_p4, dr) ->
  checkS4x vA vB m = Some (vA_p4, dr).
Proof.
  unfold findS4x; cbv zeta.
  destruct ((N.double vA + 2 <=? vB)%N); [| discriminate].
  set (m0 := N.div2 ((N.log2 (N.double vB + vB) - N.log2 (N.double vA)) + 1)%N).
  destruct (checkS4x vA vB m0) as [[p0 d0] |] eqn:E0;
    [intros [= <- <- <-]; exact E0 |].
  destruct (checkS4x vA vB (m0 - 1)%N) as [[p1 d1] |] eqn:E1;
    [intros [= <- <- <-]; exact E1 |].
  destruct (checkS4x vA vB (m0 - 2)%N) as [[p2 d2] |] eqn:E2;
    [intros [= <- <- <-]; exact E2 | discriminate].
Qed.

Lemma trySuper4x_some (hd : Sym) (l : list LChunk) (r : list RChunk) (s' : State) :
  trySuper4x hd l r = Some s' -> encode (mkState hd l r) -->+ encode s'.
Proof.
  unfold trySuper4x.
  destruct hd as [|]; [| discriminate].
  destruct l as [| ? ?]; [| discriminate].
  destruct r as [| [| | a_m1] [| [| | ?] [| [| | b_m1] rtail]]]; try discriminate.
  destruct (((5 <=? a_m1)%N && N.odd a_m1)) eqn:hcond; [| discriminate].
  rewrite Bool.andb_true_iff, N.leb_le, N_odd_mod2 in hcond.
  destruct hcond as [ha5 haodd].
  set (vA := (a_m1 + 1)%N).
  set (vB := (b_m1 + 1)%N).
  destruct (findS4x vA vB) as [[[m vA_p4] dr] |] eqn:Ef; [| discriminate].
  intros H; apply some_inj in H; subst s'.
  destruct (checkS4x_some vA vB m vA_p4 dr (findS4x_some vA vB m vA_p4 dr Ef))
    as [hm [-> [-> hB]]].
  set (p4 := (4 ^ m)%N) in *.
  set (s4 := ((p4 - 1) / 3)%N) in *.
  set (dr := (2 * vA * s4 + m)%N) in *.
  unfold encode; cbn [st_hd st_l st_r exL exR].
  set (a_nat := N.to_nat ((a_m1 - 5) / 2)%N).
  set (m_nat := N.to_nat m).
  set (d_nat := N.to_nat (vB - (dr + 1))%N + 1).
  assert (hA : N.to_nat a_m1 + 1 = 2 * (a_nat + 3)) by (clear - ha5 haodd; unfold a_nat; lia).
  assert (hvA : N.to_nat vA = 2 * (a_nat + 3)) by (unfold vA; clear - hA; lia).
  assert (hp4_eq : N.to_nat p4 = pow4 m_nat) by (unfold p4, m_nat; apply N_pow4_to_nat).
  assert (hs4_eq : N.to_nat s4 = sum4 m_nat) by (unfold s4, p4, m_nat; apply s4_N_to_nat).
  pose proof (pow4_pos m_nat) as hp4_pos.
  assert (hdr_eq : N.to_nat dr = 2 * (2 * (a_nat + 3)) * sum4 m_nat + m_nat).
  { unfold dr, m_nat. rewrite N2Nat.inj_add, !N2Nat.inj_mul, hvA, hs4_eq. reflexivity. }
  assert (hAp4 : N.to_nat (vA * p4 - 1)%N + 1 = (2 * (a_nat + 3)) * pow4 m_nat).
  { assert (hp : N.to_nat (vA * p4)%N = (2 * (a_nat + 3)) * pow4 m_nat)
      by (rewrite N2Nat.inj_mul, hvA, hp4_eq; reflexivity).
    clear - hp hp4_pos. lia. }
  assert (hB_eq : N.to_nat b_m1 + 1 = 2 * (2 * (a_nat + 3)) * sum4 m_nat + m_nat + d_nat).
  { unfold d_nat. unfold vB in hB. clear - hB hdr_eq. lia. }
  assert (hm_pos : 0 < m_nat) by (unfold m_nat; clear - hm; lia).
  rewrite hA, hB_eq, hAp4.
  exact (super4x_iter_plus m_nat a_nat d_nat hm_pos (exR rtail)).
Qed.

Lemma tryEraDrain_some (hd : Sym) (l : list LChunk) (r : list RChunk) (s' : State) :
  tryEraDrain hd l r = Some s' -> encode (mkState hd l r) -->+ encode s'.
Proof.
  unfold tryEraDrain.
  destruct hd as [|]; [| discriminate].
  destruct l as [| [| | m_val] [| [| | ?] [| [| | ?] [| ? ?]]]]; try discriminate.
  destruct r as [| [| | ?] [| [| | c_m1] rtail]]; try discriminate.
  destruct (((1 <=? m_val)%N && N.even (m_val - 1)%N)) eqn:hcond; [| discriminate].
  rewrite Bool.andb_true_iff, N.leb_le, N_even_mod2 in hcond.
  destruct hcond as [hm1 hmev].
  intros H; apply some_inj in H; subst s'.
  unfold encode, pushR1; cbn [st_hd st_l st_r exL exR].
  set (k := N.to_nat ((m_val - 1) / 2)%N).
  set (cm1 := N.to_nat c_m1).
  replace (N.to_nat m_val + 1) with (2 * (k + 1)) by (clear - hm1 hmev; unfold k; lia).
  replace (N.to_nat c_m1 + 1) with (cm1 + 1) by (unfold cm1; lia).
  replace (N.to_nat (m_val + N.double (c_m1 + 1))%N + 1) with (2 * (k + 1 + (cm1 + 1)))
    by (pose proof (N.double_spec (c_m1 + 1)%N) as hd; clear - hm1 hmev hd; unfold k, cm1; lia).
  exact (era_drain_iter cm1 k (exR rtail)).
Qed.

Lemma tryEraOscR_ok (r : list RChunk) (j c_m1 : N) (rtail : list RChunk) :
  tryEraOscR r = Some (j, c_m1, rtail) ->
  exR r = rep001 (2 * N.to_nat j) (S0 >> rep001 (N.to_nat c_m1 + 1) (exR rtail)).
Proof.
  unfold tryEraOscR.
  destruct r as [| [| | m_val] r1]; try discriminate.
  - destruct r1 as [| [| | cm] rt]; try discriminate.
    intros [= <- <- <-]. reflexivity.
  - destruct r1 as [| [| | ?] [| [| | cm] rt]]; try discriminate.
    destruct (((1 <=? m_val)%N && N.even (m_val - 1)%N)) eqn:hcond; [| discriminate].
    rewrite Bool.andb_true_iff, N.leb_le, N_even_mod2 in hcond.
    intros H; apply some_inj in H; inversion H; subst; clear H.
    rewrite N.div2_div. cbn [exR]. f_equal. lia.
Qed.

Lemma tryEraOsc_some (hd : Sym) (l : list LChunk) (r : list RChunk) (s' : State) :
  tryEraOsc hd l r = Some s' -> encode (mkState hd l r) -->+ encode s'.
Proof.
  unfold tryEraOsc.
  destruct hd as [|]; [discriminate |].
  destruct l as [| [| | ?] l1]; try discriminate.
  - destruct l1 as [| [| | a_m1] ltail]; try discriminate.
    destruct (tryEraOscR r) as [[[j c_m1] rtail] |] eqn:Er; [| discriminate].
    intros H; apply some_inj in H; subst s'.
    set (n_m1 := N.min a_m1 c_m1).
    unfold encode; cbn [st_hd st_l st_r].
    rewrite (tryEraOscR_ok r j c_m1 rtail Er),
            exL_pushL0, exL_pushLN110, exR_pushR001, exR_pushR0, exR_pushRN001.
    cbn [exL].
    replace (N.to_nat a_m1 + 1) with ((N.to_nat n_m1 + 1) + N.to_nat (a_m1 - n_m1)%N)
      by (clear; unfold n_m1; lia).
    replace (N.to_nat c_m1 + 1) with ((N.to_nat n_m1 + 1) + N.to_nat (c_m1 - n_m1)%N)
      by (clear; unfold n_m1; lia).
    replace (N.to_nat (N.succ_double (j + n_m1)%N) + 1) with (2 * (N.to_nat j + (N.to_nat n_m1 + 1)))
      by (rewrite N.succ_double_spec; clear; lia).
    rewrite (rep110_add (N.to_nat n_m1 + 1)), (rep001_add (N.to_nat n_m1 + 1)).
    exact (era_osc_iter (N.to_nat n_m1) (N.to_nat j)
            (rep110 (N.to_nat (a_m1 - n_m1)%N) (exL ltail))
            (rep001 (N.to_nat (c_m1 - n_m1)%N) (exR rtail))).
  - destruct l1 as [| [| | ?] [| [| | a_m1] ltail]]; try discriminate.
    destruct (tryEraOscR r) as [[[j c_m1] rtail] |] eqn:Er; [| discriminate].
    intros H; apply some_inj in H; subst s'.
    set (n_m1 := N.min a_m1 c_m1).
    unfold encode; cbn [st_hd st_l st_r].
    rewrite (tryEraOscR_ok r j c_m1 rtail Er),
            exL_pushL1, exL_pushL0, exL_pushLN110, exR_pushR001, exR_pushR0, exR_pushRN001.
    cbn [exL].
    replace (N.to_nat a_m1 + 1) with ((N.to_nat n_m1 + 1) + N.to_nat (a_m1 - n_m1)%N)
      by (clear; unfold n_m1; lia).
    replace (N.to_nat c_m1 + 1) with ((N.to_nat n_m1 + 1) + N.to_nat (c_m1 - n_m1)%N)
      by (clear; unfold n_m1; lia).
    replace (N.to_nat (N.succ_double (j + n_m1)%N) + 1) with (2 * (N.to_nat j + (N.to_nat n_m1 + 1)))
      by (rewrite N.succ_double_spec; clear; lia).
    rewrite (rep110_add (N.to_nat n_m1 + 1)), (rep001_add (N.to_nat n_m1 + 1)).
    exact (era_osc10_iter (N.to_nat n_m1) (N.to_nat j)
            (rep110 (N.to_nat (a_m1 - n_m1)%N) (exL ltail))
            (rep001 (N.to_nat (c_m1 - n_m1)%N) (exR rtail))).
Qed.

Lemma stepBase_some (hd : Sym) (l : list LChunk) (r : list RChunk) (s' : State) :
  stepBase hd l r = Some s' -> encode (mkState hd l r) -->+ encode s'.
Proof.
  unfold stepBase.
  destruct (baseDispatch _ _ _ _ _ _ _ _ _ _ _ hd l r) as [[[hd' l'] r']|] eqn:E;
    [|discriminate].
  intros [= <-].
  eapply (baseDispatch_sound tm C D exL exR (fun _ => True) (fun _ => True)) in E; try exact I.
  - exact (proj2 (proj2 E)).
  - intros a b a' b' _ _ H. cbn beta in H.
    pose proof (splitLChunk_ok a b) as Hr.
    destruct (splitLChunk a b); injection H as <- <-. exact (conj I (conj I Hr)).
  - intros b a _ _. exact (conj I (conj I (splitRChunk_ok b a))).
  - intros a b a' b' _ _ H. cbn beta in H.
    pose proof (stripOnesD_ok a b) as Hr.
    destruct (stripOnesL a b); injection H as <- <-. exact (conj I (conj I Hr)).
  - intros a a' c _ H. cbn beta in H.
    pose proof (popL_ok a) as Hr.
    destruct (popL a); injection H as <- <-. exact (conj I Hr).
  - intros a a' c _ H. cbn beta in H.
    pose proof (popR_ok a) as Hr.
    destruct (popR a); injection H as <- <-. exact (conj I Hr).
  - intros a _. exact (conj I (exL_pushL0 a)).
  - intros a _. exact (conj I (exL_pushL1 a)).
  - intros a _. exact (conj I (exL_pushL110 0%N a)).
  - intros a _. exact (conj I (exR_pushR0 a)).
  - intros a _. exact (conj I eq_refl).
  - intros a _. exact (conj I (exR_pushR001 0%N a)).
  - intros a b. apply evstep_one. apply @step_left. reflexivity.
  - exact reach_R1_lb.
  - exact reach_R2_lb.
  - exact reach_R3_lb.
  - exact reach_L1_lb.
  - exact reach_L2_lb.
  - exact reach_L3_lb.
Qed.

Lemma stepFast_sound (s s' : State) :
  stepFast s = Some s' -> encode s -->+ encode s'.
Proof.
  destruct s as [hd l r].
  unfold stepFast; cbn [st_hd st_l st_r].
  destruct (trySuper4x hd l r) as [s0 |] eqn:E0.
  - intros [= <-]. exact (trySuper4x_some hd l r s0 E0).
  - destruct (tryEraDrain hd l r) as [s1 |] eqn:E1.
    + intros [= <-]. exact (tryEraDrain_some hd l r s1 E1).
    + destruct (tryEraOsc hd l r) as [s2 |] eqn:E2.
      * intros [= <-]. exact (tryEraOsc_some hd l r s2 E2).
      * exact (stepBase_some hd l r s').
Qed.

Lemma iterPow2_sound : forall (k : nat) (s s' : State),
  iterPow2 k s = Some s' -> encode s -->+ encode s'.
Proof.
  induction k as [| k IH]; intros s s' H.
  - exact (stepFast_sound s s' H).
  - cbn [iterPow2 optBind] in H.
    destruct (iterPow2 k s) as [sm |] eqn:E1; [| discriminate].
    exact (ptrans (IH s sm E1) (IH sm s' H)).
Qed.

Definition startState : State := mkState S0 [lb1_c; lb1_c] [].

Definition p60StateN (a b : N) : State :=
  mkState S0 [] [rt001 (a - 2)%N; rb0_c; rt001 (b - 2)%N].

Lemma init_reaches_start : c0 -->* encode startState.
Proof.
  unfold c0, tape0, encode, startState; cbn [st_hd st_l st_r exL exR].
  fast_execute.
Qed.

Lemma encode_p60StateN (a b : N) :
  (2 <= a)%N -> (2 <= b)%N ->
  encode (p60StateN a b) = p60Cfg (N.to_nat a) (N.to_nat b).
Proof.
  intros ha hb.
  unfold encode, p60StateN, p60Cfg; cbn [st_hd st_l st_r exL exR].
  replace (N.to_nat (a - 2)%N + 1) with (N.to_nat a - 1) by lia.
  replace (N.to_nat (b - 2)%N + 1) with (N.to_nat b - 1) by lia.
  reflexivity.
Qed.

(* ========================================================================== *)
(* Layer 3: Unified Linear-Form Symbolic Engine                               *)
(* ========================================================================== *)

Record LinForm : Type := mkLF {
  lf_aN : Z;
  lf_aQ : Z;
  lf_am : Z;
  lf_ac : Z;
}.

Definition lf_eqb (x y : LinForm) : bool :=
  (lf_aN x =? lf_aN y)%Z && (lf_aQ x =? lf_aQ y)%Z &&
  (lf_am x =? lf_am y)%Z && (lf_ac x =? lf_ac y)%Z.

Lemma lf_eqb_eq (x y : LinForm) : lf_eqb x y = true <-> x = y.
Proof.
  destruct x, y; unfold lf_eqb; cbn [lf_aN lf_aQ lf_am lf_ac].
  rewrite !Bool.andb_true_iff, !Z.eqb_eq.
  intuition congruence.
Qed.

Definition lfConst (c : Z) : LinForm := mkLF 0%Z 0%Z 0%Z c.
Definition lfAdd (x y : LinForm) : LinForm :=
  mkLF (lf_aN x + lf_aN y)%Z (lf_aQ x + lf_aQ y)%Z (lf_am x + lf_am y)%Z (lf_ac x + lf_ac y)%Z.
Definition lfSub (x y : LinForm) : LinForm :=
  mkLF (lf_aN x - lf_aN y)%Z (lf_aQ x - lf_aQ y)%Z (lf_am x - lf_am y)%Z (lf_ac x - lf_ac y)%Z.
Definition lfScale2 (x : LinForm) : LinForm :=
  mkLF (Z.double (lf_aN x)) (Z.double (lf_aQ x)) (Z.double (lf_am x)) (Z.double (lf_ac x)).

Definition evalLF (vN vQ vm : nat) (f : LinForm) : Z :=
  (lf_aN f * Z.of_nat vN + lf_aQ f * Z.of_nat vQ + lf_am f * Z.of_nat vm + lf_ac f)%Z.

Definition evalLFNat (vN vQ vm : nat) (f : LinForm) : nat :=
  Z.to_nat (evalLF vN vQ vm f).

Lemma evalLF_const (vN vQ vm : nat) (c : Z) : evalLF vN vQ vm (lfConst c) = c.
Proof. unfold evalLF, lfConst; cbn [lf_aN lf_aQ lf_am lf_ac]. lia. Qed.

Lemma evalLF_add (vN vQ vm : nat) (x y : LinForm) :
  evalLF vN vQ vm (lfAdd x y) = (evalLF vN vQ vm x + evalLF vN vQ vm y)%Z.
Proof. unfold evalLF, lfAdd; cbn [lf_aN lf_aQ lf_am lf_ac]. nia. Qed.

Lemma evalLF_sub (vN vQ vm : nat) (x y : LinForm) :
  evalLF vN vQ vm (lfSub x y) = (evalLF vN vQ vm x - evalLF vN vQ vm y)%Z.
Proof. unfold evalLF, lfSub; cbn [lf_aN lf_aQ lf_am lf_ac]. nia. Qed.

Lemma evalLF_scale2 (vN vQ vm : nat) (x : LinForm) :
  evalLF vN vQ vm (lfScale2 x) = (2 * evalLF vN vQ vm x)%Z.
Proof.
  unfold evalLF, lfScale2; cbn [lf_aN lf_aQ lf_am lf_ac].
  pose proof (Z.double_spec (lf_aN x)) as hd1.
  pose proof (Z.double_spec (lf_aQ x)) as hd2.
  pose proof (Z.double_spec (lf_am x)) as hd3.
  pose proof (Z.double_spec (lf_ac x)) as hd4.
  nia.
Qed.

Lemma evalLFNat_const (vN vQ vm k : nat) :
  evalLFNat vN vQ vm (lfConst (Z.of_nat k)) = k.
Proof.
  unfold evalLFNat. rewrite evalLF_const. apply Nat2Z.id.
Qed.

Record SymPred : Type := mkSymPred {
  sp_isNonneg : LinForm -> bool;
  sp_isEven : LinForm -> bool;
  sp_allowS4x : bool;
}.

Definition sp_isPos (P : SymPred) (f : LinForm) : bool :=
  sp_isNonneg P (lfSub f (lfConst 1%Z)).

Record ValidPred (P : SymPred) (vN vQ vm : nat) : Prop := mkValidPred {
  vp_nonneg_ok : forall f, sp_isNonneg P f = true -> (0 <= evalLF vN vQ vm f)%Z;
  vp_even_ok : forall f, sp_isEven P f = true -> (evalLF vN vQ vm f mod 2 = 0)%Z;
  vp_odd_ok : forall f, sp_isEven P f = false -> (evalLF vN vQ vm f mod 2 = 1)%Z;
  vp_s4x_ok : sp_allowS4x P = true -> vQ = sum4 vm /\ 1 <= vm;
}.

Lemma vp_pos_ok {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm) (f : LinForm) :
  sp_isPos P f = true -> (1 <= evalLF vN vQ vm f)%Z.
Proof.
  intros hok.
  pose proof (vp_nonneg_ok _ _ _ _ hP (lfSub f (lfConst 1%Z)) hok) as h.
  rewrite evalLF_sub, evalLF_const in h. lia.
Qed.

Inductive SLChunk : Type :=
  | slb0 : SLChunk
  | slb1 : SLChunk
  | slt110 (f : LinForm) : SLChunk.

Inductive SRChunk : Type :=
  | srb0 : SRChunk
  | srb1 : SRChunk
  | srt001 (f : LinForm) : SRChunk.

Record SymState : Type := mkSymState {
  sst_hd : Sym;
  sst_l : list SLChunk;
  sst_r : list SRChunk;
  sst_hs : list N;
}.

Fixpoint exSL (vN vQ vm : nat) (l : list SLChunk) : side :=
  match l with
  | [] => 0inf
  | slb0 :: tl => S0 >> exSL vN vQ vm tl
  | slb1 :: tl => S1 >> exSL vN vQ vm tl
  | slt110 f :: tl => rep110 (evalLFNat vN vQ vm f) (exSL vN vQ vm tl)
  end.

Fixpoint exSR (vN vQ vm : nat) (r : list SRChunk) : side :=
  match r with
  | [] => 0inf
  | srb0 :: tl => S0 >> exSR vN vQ vm tl
  | srb1 :: tl => S1 >> exSR vN vQ vm tl
  | srt001 f :: tl => rep001 (evalLFNat vN vQ vm f) (exSR vN vQ vm tl)
  end.

Definition evalSym (vN vQ vm : nat) (s : SymState) : Q * tape :=
  (exSL vN vQ vm (sst_l s)) {{C}}> ((sst_hd s) >> exSR vN vQ vm (sst_r s)).

Fixpoint validL (vN vQ vm : nat) (l : list SLChunk) : Prop :=
  match l with
  | [] => True
  | slb0 :: tl => validL vN vQ vm tl
  | slb1 :: tl => validL vN vQ vm tl
  | slt110 f :: tl => (1 <= evalLF vN vQ vm f)%Z /\ validL vN vQ vm tl
  end.

Fixpoint validR (vN vQ vm : nat) (r : list SRChunk) : Prop :=
  match r with
  | [] => True
  | srb0 :: tl => validR vN vQ vm tl
  | srb1 :: tl => validR vN vQ vm tl
  | srt001 f :: tl => (1 <= evalLF vN vQ vm f)%Z /\ validR vN vQ vm tl
  end.

Definition validSym (vN vQ vm : nat) (s : SymState) : Prop :=
  validL vN vQ vm (sst_l s) /\ validR vN vQ vm (sst_r s).

Definition symPushL110 (f : LinForm) (l : list SLChunk) : list SLChunk :=
  match l with
  | slt110 g :: tl => slt110 (lfAdd f g) :: tl
  | _ => slt110 f :: l
  end.

Definition symPushL0 (l : list SLChunk) : list SLChunk :=
  match l with
  | [] => []
  | _ => slb0 :: l
  end.

Definition symPushL1 (l : list SLChunk) : list SLChunk :=
  match l with
  | slb1 :: slb0 :: tl => symPushL110 (lfConst 1%Z) tl
  | _ => slb1 :: l
  end.

Definition symPushR001 (f : LinForm) (r : list SRChunk) : list SRChunk :=
  match r with
  | srt001 g :: tl => srt001 (lfAdd f g) :: tl
  | _ => srt001 f :: r
  end.

Definition symPushR0 (r : list SRChunk) : list SRChunk :=
  match r with
  | [] => []
  | srb0 :: srb1 :: tl => symPushR001 (lfConst 1%Z) tl
  | _ => srb0 :: r
  end.

Definition symPushR1 (r : list SRChunk) : list SRChunk := srb1 :: r.

Definition symPopL (P : SymPred) (l : list SLChunk) : option (Sym * list SLChunk) :=
  match l with
  | [] => Some (S0, [])
  | slb0 :: tl => Some (S0, tl)
  | slb1 :: tl => Some (S1, tl)
  | slt110 f :: tl =>
    if lf_eqb f (lfConst 1%Z) then Some (S1, slb1 :: slb0 :: tl)
    else if sp_isPos P (lfSub f (lfConst 1%Z)) then
      Some (S1, slb1 :: slb0 :: slt110 (lfSub f (lfConst 1%Z)) :: tl)
    else None
  end.

Definition symPopR (P : SymPred) (r : list SRChunk) : option (Sym * list SRChunk) :=
  match r with
  | [] => Some (S0, [])
  | srb0 :: tl => Some (S0, tl)
  | srb1 :: tl => Some (S1, tl)
  | srt001 f :: tl =>
    if lf_eqb f (lfConst 1%Z) then Some (S0, srb0 :: srb1 :: tl)
    else if sp_isPos P (lfSub f (lfConst 1%Z)) then
      Some (S0, srb0 :: srb1 :: srt001 (lfSub f (lfConst 1%Z)) :: tl)
    else None
  end.

Fixpoint symSplitR (l : list SLChunk) (r : list SRChunk) {struct r} : list SLChunk * list SRChunk :=
  match r with
  | srt001 f :: r' => symSplitR (symPushL110 f l) r'
  | _ => (l, r)
  end.

Fixpoint symSplitL (P : SymPred) (l : list SLChunk) (r : list SRChunk) {struct l} :
  option (list SLChunk * list SRChunk) :=
  match l with
  | slt110 f :: tl =>
    if lf_eqb f (lfConst 1%Z) then Some (slt110 f :: tl, r)
    else if sp_isEven P f then
      if sp_isNonneg P (lfSub f (lfConst 2%Z)) then
        symSplitL P tl (symPushR001 f r)
      else None
    else
      if sp_isNonneg P (lfSub f (lfConst 3%Z)) then
        Some (slt110 (lfConst 1%Z) :: tl, symPushR001 (lfSub f (lfConst 1%Z)) r)
      else None
  | _ => Some (l, r)
  end.

Fixpoint symStripOnesL (P : SymPred) (l : list SLChunk) (r : list SRChunk) {struct l} :
  option (list SLChunk * list SRChunk) :=
  match l with
  | [] => Some ([], r)
  | slb0 :: tl => Some (tl, r)
  | slb1 :: tl => symStripOnesL P tl (symPushR0 r)
  | slt110 f :: tl =>
    if lf_eqb f (lfConst 1%Z) then Some (tl, symPushR0 (symPushR0 r))
    else if sp_isPos P (lfSub f (lfConst 1%Z)) then
      Some (slt110 (lfSub f (lfConst 1%Z)) :: tl, symPushR0 (symPushR0 r))
    else None
  end.

Definition s4xNeed (d : N) : LinForm :=
  let p := N.shiftl 1%N (N.double d) in
  let s := ((p - 1) / 3)%N in
  mkLF 0%Z (20 * Z.of_N p)%Z 1%Z (20 * Z.of_N s + Z.of_N d)%Z.

Definition s4xNewA (d : N) : LinForm :=
  let p := N.shiftl 1%N (N.double d) in
  mkLF 0%Z (30 * Z.of_N p)%Z 0%Z (10 * Z.of_N p)%Z.

Definition symTrySuper4x (P : SymPred) (hd : Sym) (l : list SLChunk) (r : list SRChunk) (hs : list N) :
  option SymState :=
  match sp_allowS4x P, hd, l, r, hs with
  | true, S0, [], srt001 a :: srb0 :: srt001 vB :: rtail, d :: hs' =>
    if lf_eqb a (lfConst 10%Z) then
      let need := s4xNeed d in
      if sp_isPos P (lfSub vB need) then
        Some (mkSymState S0 [] (srt001 (s4xNewA d) :: srb0 :: srt001 (lfSub vB need) :: rtail) hs')
      else None
    else None
  | _, _, _, _, _ => None
  end.

Definition symTryEraDrain (P : SymPred) (hd : Sym) (l : list SLChunk) (r : list SRChunk) (hs : list N) :
  option SymState :=
  match hd, l, r with
  | S0, [slt110 a; slb1; slb1], srb1 :: srt001 c :: rtail =>
    if sp_isEven P a && sp_isNonneg P (lfSub a (lfConst 2%Z)) && sp_isPos P c then
      Some (mkSymState S0 [slt110 (lfAdd a (lfScale2 c)); slb1; slb1] (symPushR1 rtail) hs)
    else None
  | _, _, _ => None
  end.

Definition symTryEraOscR (P : SymPred) (r : list SRChunk) : option (LinForm * LinForm * list SRChunk) :=
  match r with
  | srb0 :: srt001 c :: rtail => Some (lfConst 0%Z, c, rtail)
  | srt001 j2 :: srb0 :: srt001 c :: rtail =>
    if sp_isEven P j2 && sp_isNonneg P (lfSub j2 (lfConst 2%Z)) then Some (j2, c, rtail) else None
  | _ => None
  end.

Definition symTryEraOsc (P : SymPred) (hd : Sym) (l : list SLChunk) (r : list SRChunk) (hs : list N) :
  option SymState :=
  match hd with
  | S1 =>
    let extracted : option (bool * LinForm * list SLChunk) :=
      match l with
      | slb0 :: slt110 a :: ltail => Some (false, a, ltail)
      | slb1 :: slb0 :: slt110 a :: ltail => Some (true, a, ltail)
      | _ => None
      end
    in
    match extracted with
    | Some (is10, a, ltail) =>
      match symTryEraOscR P r with
      | Some (j2, c, rtail) =>
        let cmp : option (LinForm * list SLChunk * list SRChunk) :=
          if lf_eqb a c then Some (a, ltail, rtail)
          else if sp_isPos P (lfSub c a) then Some (a, ltail, symPushR001 (lfSub c a) rtail)
          else if sp_isPos P (lfSub a c) then Some (c, symPushL110 (lfSub a c) ltail, rtail)
          else None
        in
        match cmp with
        | Some (n, lbase, rbase) =>
          let l1 := symPushL0 lbase in
          let l_new := if is10 then symPushL1 l1 else l1 in
          let r_new := symPushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase) in
          Some (mkSymState S1 l_new r_new hs)
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | S0 => None
  end.

Definition symStepBase (P : SymPred) (hd : Sym) (l : list SLChunk) (r : list SRChunk) (hs : list N) : option SymState :=
  match baseDispatch (symSplitL P) (symStripOnesL P) symSplitR (symPopL P) (symPopR P)
    symPushL0 symPushL1 (symPushL110 (lfConst 1%Z))
    symPushR0 symPushR1 (symPushR001 (lfConst 1%Z)) hd l r with
  | Some (hd', l', r') => Some (mkSymState hd' l' r' hs)
  | None => None
  end.

Definition symStep (P : SymPred) (s : SymState) : option SymState :=
  match symTrySuper4x P (sst_hd s) (sst_l s) (sst_r s) (sst_hs s) with
  | Some s' => Some s'
  | None =>
    match symTryEraDrain P (sst_hd s) (sst_l s) (sst_r s) (sst_hs s) with
    | Some s' => Some s'
    | None =>
      match symTryEraOsc P (sst_hd s) (sst_l s) (sst_r s) (sst_hs s) with
      | Some s' => Some s'
      | None => symStepBase P (sst_hd s) (sst_l s) (sst_r s) (sst_hs s)
      end
    end
  end.

Fixpoint symIterPow2 (P : SymPred) (k : nat) (s : SymState) : option SymState :=
  match k with
  | 0 => symStep P s
  | S k' => optBind (symIterPow2 P k' s) (symIterPow2 P k')
  end.

(* Soundness of Unified Symbolic Engine *)

Lemma exSL_pushL110 {vN vQ vm : nat} (f : LinForm) (l : list SLChunk) :
  (1 <= evalLF vN vQ vm f)%Z -> validL vN vQ vm l ->
  validL vN vQ vm (symPushL110 f l) /\
  exSL vN vQ vm (symPushL110 f l) = rep110 (evalLFNat vN vQ vm f) (exSL vN vQ vm l).
Proof.
  intros hf hl.
  destruct l as [| [| | g] tl].
  - exact (conj (conj hf I) eq_refl).
  - exact (conj (conj hf hl) eq_refl).
  - exact (conj (conj hf hl) eq_refl).
  - destruct hl as [hg htl].
    cbn [symPushL110 validL exSL].
    split; [split; [rewrite evalLF_add; lia | exact htl] |].
    assert (hadd : evalLFNat vN vQ vm (lfAdd f g) = evalLFNat vN vQ vm f + evalLFNat vN vQ vm g).
    { unfold evalLFNat. rewrite evalLF_add. lia. }
    rewrite hadd, rep110_add. reflexivity.
Qed.

Lemma exSL_pushL0 {vN vQ vm : nat} (l : list SLChunk) :
  validL vN vQ vm l ->
  validL vN vQ vm (symPushL0 l) /\ exSL vN vQ vm (symPushL0 l) = S0 >> exSL vN vQ vm l.
Proof.
  intros hl.
  destruct l; [exact (conj I (eq_sym cons_zero_0inf)) | exact (conj hl eq_refl)].
Qed.

Lemma exSL_pushL1 {vN vQ vm : nat} (l : list SLChunk) :
  validL vN vQ vm l ->
  validL vN vQ vm (symPushL1 l) /\ exSL vN vQ vm (symPushL1 l) = S1 >> exSL vN vQ vm l.
Proof.
  intros hl.
  destruct l as [| [| | ?] [| [| | ?] tl]]; try exact (conj hl eq_refl).
  cbn [symPushL1].
  assert (h1 : (1 <= evalLF vN vQ vm (lfConst 1%Z))%Z) by (rewrite evalLF_const; lia).
  destruct (exSL_pushL110 (lfConst 1%Z) tl h1 hl) as [hv hex].
  split; [exact hv |].
  rewrite hex. change 1%Z with (Z.of_nat 1). rewrite evalLFNat_const. reflexivity.
Qed.

Lemma exSR_pushR001 {vN vQ vm : nat} (f : LinForm) (r : list SRChunk) :
  (1 <= evalLF vN vQ vm f)%Z -> validR vN vQ vm r ->
  validR vN vQ vm (symPushR001 f r) /\
  exSR vN vQ vm (symPushR001 f r) = rep001 (evalLFNat vN vQ vm f) (exSR vN vQ vm r).
Proof.
  intros hf hr.
  destruct r as [| [| | g] tl].
  - exact (conj (conj hf I) eq_refl).
  - exact (conj (conj hf hr) eq_refl).
  - exact (conj (conj hf hr) eq_refl).
  - destruct hr as [hg htl].
    cbn [symPushR001 validR exSR].
    split; [split; [rewrite evalLF_add; lia | exact htl] |].
    assert (hadd : evalLFNat vN vQ vm (lfAdd f g) = evalLFNat vN vQ vm f + evalLFNat vN vQ vm g).
    { unfold evalLFNat. rewrite evalLF_add. lia. }
    rewrite hadd, rep001_add. reflexivity.
Qed.

Lemma exSR_pushR0 {vN vQ vm : nat} (r : list SRChunk) :
  validR vN vQ vm r ->
  validR vN vQ vm (symPushR0 r) /\ exSR vN vQ vm (symPushR0 r) = S0 >> exSR vN vQ vm r.
Proof.
  intros hr.
  destruct r as [| [| | ?] [| [| | ?] tl]];
    try exact (conj hr eq_refl);
    try exact (conj I (eq_sym cons_zero_0inf)).
  cbn [symPushR0].
  assert (h1 : (1 <= evalLF vN vQ vm (lfConst 1%Z))%Z) by (rewrite evalLF_const; lia).
  destruct (exSR_pushR001 (lfConst 1%Z) tl h1 hr) as [hv hex].
  split; [exact hv |].
  rewrite hex. change 1%Z with (Z.of_nat 1). rewrite evalLFNat_const. reflexivity.
Qed.

Lemma symPopL_ok {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm)
  (l l' : list SLChunk) (b : Sym) :
  validL vN vQ vm l -> symPopL P l = Some (b, l') ->
  validL vN vQ vm l' /\ exSL vN vQ vm l = b >> exSL vN vQ vm l'.
Proof.
  intros hl H.
  destruct l as [| [| | f] tl].
  - cbn [symPopL] in H. apply some_inj, pair_inj in H; destruct H as [<- <-].
    exact (conj I (eq_sym cons_zero_0inf)).
  - cbn [symPopL] in H. apply some_inj, pair_inj in H; destruct H as [<- <-].
    exact (conj hl eq_refl).
  - cbn [symPopL] in H. apply some_inj, pair_inj in H; destruct H as [<- <-].
    exact (conj hl eq_refl).
  - destruct hl as [hf htl].
    cbn [symPopL] in H.
    destruct (lf_eqb f (lfConst 1%Z)) eqn:h1.
    + apply lf_eqb_eq in h1. subst f.
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      split; [exact htl |].
      cbn [exSL]. change 1%Z with (Z.of_nat 1). rewrite evalLFNat_const. reflexivity.
    + destruct (sp_isPos P (lfSub f (lfConst 1%Z))) eqn:h2; [| discriminate].
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      pose proof (vp_pos_ok hP _ h2) as hsub.
      split; [exact (conj hsub htl) |].
      cbn [exSL].
      assert (heq : evalLFNat vN vQ vm f = 1 + evalLFNat vN vQ vm (lfSub f (lfConst 1%Z))).
      { unfold evalLFNat. rewrite evalLF_sub, evalLF_const in hsub |- *. lia. }
      rewrite heq, (rep110_add 1). reflexivity.
Qed.

Lemma symPopR_ok {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm)
  (r r' : list SRChunk) (b : Sym) :
  validR vN vQ vm r -> symPopR P r = Some (b, r') ->
  validR vN vQ vm r' /\ exSR vN vQ vm r = b >> exSR vN vQ vm r'.
Proof.
  intros hr H.
  destruct r as [| [| | f] tl].
  - cbn [symPopR] in H. apply some_inj, pair_inj in H; destruct H as [<- <-].
    exact (conj I (eq_sym cons_zero_0inf)).
  - cbn [symPopR] in H. apply some_inj, pair_inj in H; destruct H as [<- <-].
    exact (conj hr eq_refl).
  - cbn [symPopR] in H. apply some_inj, pair_inj in H; destruct H as [<- <-].
    exact (conj hr eq_refl).
  - destruct hr as [hf htl].
    cbn [symPopR] in H.
    destruct (lf_eqb f (lfConst 1%Z)) eqn:h1.
    + apply lf_eqb_eq in h1. subst f.
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      split; [exact htl |].
      cbn [exSR]. change 1%Z with (Z.of_nat 1). rewrite evalLFNat_const. reflexivity.
    + destruct (sp_isPos P (lfSub f (lfConst 1%Z))) eqn:h2; [| discriminate].
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      pose proof (vp_pos_ok hP _ h2) as hsub.
      split; [exact (conj hsub htl) |].
      cbn [exSR].
      assert (heq : evalLFNat vN vQ vm f = 1 + evalLFNat vN vQ vm (lfSub f (lfConst 1%Z))).
      { unfold evalLFNat. rewrite evalLF_sub, evalLF_const in hsub |- *. lia. }
      rewrite heq, (rep001_add 1). reflexivity.
Qed.

Lemma symSplitR_ok {vN vQ vm : nat} : forall (r : list SRChunk) (l : list SLChunk),
  validL vN vQ vm l -> validR vN vQ vm r ->
  validL vN vQ vm (fst (symSplitR l r)) /\
  validR vN vQ vm (snd (symSplitR l r)) /\
  (exSL vN vQ vm l {{C}}> (S1 >> exSR vN vQ vm r)) -->*
  (exSL vN vQ vm (fst (symSplitR l r)) {{C}}> (S1 >> exSR vN vQ vm (snd (symSplitR l r)))).
Proof.
  induction r as [| [| | f] r IH]; intros l hl hr;
    try exact (conj hl (conj hr (evstep_refl tm _))).
  destruct hr as [hf hr].
  cbn [symSplitR exSR].
  destruct (exSL_pushL110 f l hf hl) as [hl' hex].
  pose proof (reach_splitR_lb (evalLFNat vN vQ vm f) (exSL vN vQ vm l) (exSR vN vQ vm r)) as h1.
  rewrite <- hex in h1.
  destruct (IH (symPushL110 f l) hl' hr) as [hvL [hvR h2]].
  exact (conj hvL (conj hvR (etrans h1 h2))).
Qed.

Lemma symSplitL_ok {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm) :
  forall (l : list SLChunk) (r : list SRChunk) (l' : list SLChunk) (r' : list SRChunk),
  validL vN vQ vm l -> validR vN vQ vm r -> symSplitL P l r = Some (l', r') ->
  validL vN vQ vm l' /\ validR vN vQ vm r' /\
  (exSL vN vQ vm l {{C}}> (S0 >> exSR vN vQ vm r)) -->*
  (exSL vN vQ vm l' {{C}}> (S0 >> exSR vN vQ vm r')).
Proof.
  induction l as [| [| | f] tl IH]; intros r l' r' hl hr H;
    try (cbn [symSplitL] in H; apply some_inj, pair_inj in H; destruct H as [<- <-];
         exact (conj hl (conj hr (evstep_refl tm _)))).
  destruct hl as [hf htl].
  cbn [symSplitL] in H.
  destruct (lf_eqb f (lfConst 1%Z)) eqn:h1.
  - apply some_inj, pair_inj in H; destruct H as [<- <-].
    exact (conj (conj hf htl) (conj hr (evstep_refl tm _))).
  - destruct (sp_isEven P f) eqn:hev.
    + destruct (sp_isNonneg P (lfSub f (lfConst 2%Z))) eqn:h2; [| discriminate].
      pose proof (vp_even_ok _ _ _ _ hP f hev) as hfev.
      pose proof (vp_nonneg_ok _ _ _ _ hP _ h2) as hge2.
      rewrite evalLF_sub, evalLF_const in hge2.
      assert (hfn : evalLFNat vN vQ vm f = 2 * (evalLFNat vN vQ vm f / 2))
        by (unfold evalLFNat; lia).
      destruct (exSR_pushR001 f r hf hr) as [hr1 hex1].
      assert (hstep : (exSL vN vQ vm (slt110 f :: tl) {{C}}> (S0 >> exSR vN vQ vm r)) -->*
                      (exSL vN vQ vm tl {{C}}> (S0 >> exSR vN vQ vm (symPushR001 f r)))).
      { cbn [exSL]. rewrite hex1, hfn.
        exact (reach_splitL_lb (evalLFNat vN vQ vm f / 2) (exSL vN vQ vm tl) (exSR vN vQ vm r)). }
      destruct (IH (symPushR001 f r) l' r' htl hr1 H) as [hvL [hvR hrest]].
      exact (conj hvL (conj hvR (etrans hstep hrest))).
    + destruct (sp_isNonneg P (lfSub f (lfConst 3%Z))) eqn:h3; [| discriminate].
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      pose proof (vp_nonneg_ok _ _ _ _ hP _ h3) as hge3.
      rewrite evalLF_sub, evalLF_const in hge3.
      pose proof (vp_odd_ok _ _ _ _ hP f hev) as hfodd.
      assert (hsub_pos : (1 <= evalLF vN vQ vm (lfSub f (lfConst 1%Z)))%Z)
        by (rewrite evalLF_sub, evalLF_const; lia).
      destruct (exSR_pushR001 (lfSub f (lfConst 1%Z)) r hsub_pos hr) as [hr1 hex1].
      assert (hc1 : (1 <= evalLF vN vQ vm (lfConst 1%Z))%Z) by (rewrite evalLF_const; lia).
      split; [exact (conj hc1 htl) | split; [exact hr1 |]].
      cbn [exSL]. rewrite hex1.
      set (half := evalLFNat vN vQ vm (lfSub f (lfConst 1%Z)) / 2).
      assert (hsub_even : evalLFNat vN vQ vm (lfSub f (lfConst 1%Z)) = 2 * half)
        by (unfold half, evalLFNat; rewrite evalLF_sub, evalLF_const; lia).
      assert (hfn : evalLFNat vN vQ vm f = 2 * half + 1)
        by (unfold half, evalLFNat; rewrite evalLF_sub, evalLF_const; lia).
      rewrite hfn, (rep110_add (2 * half) 1), hsub_even.
      change (lfConst 1%Z) with (lfConst (Z.of_nat 1)). rewrite evalLFNat_const.
      exact (reach_splitL_lb half (rep110 1 (exSL vN vQ vm tl)) (exSR vN vQ vm r)).
Qed.

Lemma symStripOnesL_ok {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm) :
  forall (l : list SLChunk) (r : list SRChunk) (l' : list SLChunk) (r' : list SRChunk),
  validL vN vQ vm l -> validR vN vQ vm r -> symStripOnesL P l r = Some (l', r') ->
  validL vN vQ vm l' /\ validR vN vQ vm r' /\
  (exSL vN vQ vm l <{{D}} exSR vN vQ vm r) -->*
  (exSL vN vQ vm l' {{D}}> (S0 >> exSR vN vQ vm r')).
Proof.
  induction l as [| [| | f] tl IH]; intros r l' r' hl hr H.
  - cbn [symStripOnesL] in H. apply some_inj, pair_inj in H; destruct H as [<- <-].
    exact (conj I (conj hr (evstep_refl tm _))).
  - cbn [symStripOnesL] in H. apply some_inj, pair_inj in H; destruct H as [<- <-].
    exact (conj hl (conj hr (evstep_refl tm _))).
  - cbn [symStripOnesL] in H.
    destruct (exSR_pushR0 r hr) as [hr1 hex1].
    destruct (IH (symPushR0 r) l' r' hl hr1 H) as [hvL [hvR h2]].
    split; [exact hvL | split; [exact hvR |]].
    cbn [exSL].
    assert (h1 : ((S1 >> exSL vN vQ vm tl) <{{D}} exSR vN vQ vm r) -->*
                 (exSL vN vQ vm tl <{{D}} exSR vN vQ vm (symPushR0 r))).
    { rewrite hex1. fast_execute. }
    exact (etrans h1 h2).
  - destruct hl as [hf htl].
    cbn [symStripOnesL] in H.
    destruct (exSR_pushR0 r hr) as [hr1 hex1].
    destruct (exSR_pushR0 (symPushR0 r) hr1) as [hr2 hex2].
    destruct (lf_eqb f (lfConst 1%Z)) eqn:h1.
    + apply lf_eqb_eq in h1. subst f.
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      split; [exact htl | split; [exact hr2 |]].
      cbn [exSL]. change 1%Z with (Z.of_nat 1). rewrite evalLFNat_const, hex2, hex1.
      cbn [rep110]. fast_execute.
    + destruct (sp_isPos P (lfSub f (lfConst 1%Z))) eqn:h2; [| discriminate].
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      pose proof (vp_pos_ok hP _ h2) as hsub.
      split; [exact (conj hsub htl) | split; [exact hr2 |]].
      cbn [exSL].
      assert (heq : evalLFNat vN vQ vm f = 1 + evalLFNat vN vQ vm (lfSub f (lfConst 1%Z))).
      { unfold evalLFNat. rewrite evalLF_sub, evalLF_const in hsub |- *. lia. }
      rewrite heq, (rep110_add 1), hex2, hex1.
      cbn [rep110]. fast_execute.
Qed.

Lemma symTrySuper4x_sound {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm)
  (hd : Sym) (l : list SLChunk) (r : list SRChunk) (hs : list N) (s' : SymState) :
  validSym vN vQ vm (mkSymState hd l r hs) ->
  symTrySuper4x P hd l r hs = Some s' ->
  validSym vN vQ vm s' /\ evalSym vN vQ vm (mkSymState hd l r hs) -->+ evalSym vN vQ vm s'.
Proof.
  intros hv H.
  unfold symTrySuper4x in H.
  destruct (sp_allowS4x P) eqn:hallow; [| discriminate].
  destruct (vp_s4x_ok _ _ _ _ hP hallow) as [hQeq hm1].
  destruct hd as [|]; [| discriminate].
  destruct l as [| ? ?]; [| discriminate].
  destruct r as [| [| | a] [| [| | ?] [| [| | vB] rtail]]]; try discriminate.
  destruct hs as [| d hs']; [discriminate |].
  destruct (lf_eqb a (lfConst 10%Z)) eqn:ha; [| discriminate].
  apply lf_eqb_eq in ha. subst a.
  cbv zeta in H.
  destruct (sp_isPos P (lfSub vB (s4xNeed d))) eqn:hpos; [| discriminate].
  apply some_inj in H; subst s'.
  pose proof (vp_pos_ok hP _ hpos) as hBsub.
  destruct hv as [_ [_ [hBvalid hrtail]]].
  set (dn := N.to_nat d).
  assert (hp_Z : Z.of_N (N.shiftl 1%N (N.double d)) = Z.of_nat (pow4 dn))
    by (unfold dn; rewrite <- N_shiftl_1_pow4; lia).
  assert (hs_Z : Z.of_N ((N.shiftl 1%N (N.double d) - 1) / 3)%N = Z.of_nat (sum4 dn))
    by (unfold dn; rewrite <- N_shiftl_1_s4; lia).
  assert (hd_Z : Z.of_N d = Z.of_nat dn) by (unfold dn; lia).
  pose proof (pow4_pos dn) as hp4d.
  assert (hnewA_pos : (1 <= evalLF vN vQ vm (s4xNewA d))%Z)
    by (unfold evalLF, s4xNewA; cbn [lf_aN lf_aQ lf_am lf_ac]; rewrite hp_Z; clear - hp4d; nia).
  split; [exact (conj I (conj hnewA_pos (conj hBsub hrtail))) |].
  unfold evalSym; cbn [sst_hd sst_l sst_r exSL exSR].
  assert (h10 : evalLFNat vN vQ vm (lfConst 10%Z) = 2 * (2 + 3))
    by (change 10%Z with (Z.of_nat 10); apply evalLFNat_const).
  assert (hneed_eq : evalLF vN vQ vm (s4xNeed d) =
                     Z.of_nat (2 * (2 * (2 + 3)) * sum4 (vm + dn) + (vm + dn))).
  { unfold evalLF, s4xNeed; cbn [lf_aN lf_aQ lf_am lf_ac].
    rewrite hp_Z, hs_Z, hd_Z, hQeq, (sum4_add vm dn). clear. nia. }
  assert (hnewA_eq : evalLFNat vN vQ vm (s4xNewA d) = (2 * (2 + 3)) * pow4 (vm + dn)).
  { unfold evalLFNat, evalLF, s4xNewA; cbn [lf_aN lf_aQ lf_am lf_ac].
    rewrite hp_Z, hQeq.
    replace (0 * Z.of_nat vN + 30 * Z.of_nat (pow4 dn) * Z.of_nat (sum4 vm) +
             0 * Z.of_nat vm + 10 * Z.of_nat (pow4 dn))%Z
      with (Z.of_nat ((2 * (2 + 3)) * pow4 (vm + dn)))
      by (clear; rewrite (pow4_add vm dn), <- (sum4_spec vm); nia).
    apply Nat2Z.id. }
  assert (hB_eq : evalLFNat vN vQ vm vB =
                  2 * (2 * (2 + 3)) * sum4 (vm + dn) + (vm + dn) +
                  evalLFNat vN vQ vm (lfSub vB (s4xNeed d)))
    by (unfold evalLFNat; rewrite evalLF_sub, hneed_eq in hBsub |- *; lia).
  rewrite h10, hB_eq, hnewA_eq.
  assert (hmd : 0 < vm + dn) by lia.
  exact (super4x_iter_plus (vm + dn) 2 (evalLFNat vN vQ vm (lfSub vB (s4xNeed d))) hmd (exSR vN vQ vm rtail)).
Qed.

Lemma symTryEraDrain_sound {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm)
  (hd : Sym) (l : list SLChunk) (r : list SRChunk) (hs : list N) (s' : SymState) :
  validSym vN vQ vm (mkSymState hd l r hs) ->
  symTryEraDrain P hd l r hs = Some s' ->
  validSym vN vQ vm s' /\ evalSym vN vQ vm (mkSymState hd l r hs) -->+ evalSym vN vQ vm s'.
Proof.
  intros hv H.
  unfold symTryEraDrain in H.
  destruct hd as [|]; [| discriminate].
  destruct l as [| [| | a] [| [| | ?] [| [| | ?] [| ? ?]]]]; try discriminate.
  destruct r as [| [| | ?] [| [| | c] rtail]]; try discriminate.
  destruct (sp_isEven P a && sp_isNonneg P (lfSub a (lfConst 2%Z)) && sp_isPos P c) eqn:hcond; [| discriminate].
  apply some_inj in H; subst s'.
  rewrite !Bool.andb_true_iff in hcond.
  destruct hcond as [[hev h2] hc].
  pose proof (vp_even_ok _ _ _ _ hP a hev) as haev.
  pose proof (vp_nonneg_ok _ _ _ _ hP _ h2) as hage2.
  rewrite evalLF_sub, evalLF_const in hage2.
  pose proof (vp_pos_ok hP c hc) as hcpos.
  destruct hv as [_ [_ hrtail]].
  assert (hnew_pos : (1 <= evalLF vN vQ vm (lfAdd a (lfScale2 c)))%Z)
    by (rewrite evalLF_add, evalLF_scale2; lia).
  split; [exact (conj (conj hnew_pos I) hrtail) |].
  unfold evalSym, symPushR1; cbn [sst_hd sst_l sst_r exSL exSR].
  set (k := evalLFNat vN vQ vm a / 2 - 1).
  set (cm1 := evalLFNat vN vQ vm c - 1).
  assert (ha_eq : evalLFNat vN vQ vm a = 2 * (k + 1)) by (unfold k, evalLFNat; lia).
  assert (hc_eq : evalLFNat vN vQ vm c = cm1 + 1) by (unfold cm1, evalLFNat; lia).
  assert (hout_eq : evalLFNat vN vQ vm (lfAdd a (lfScale2 c)) = 2 * (k + 1 + (cm1 + 1)))
    by (unfold k, cm1, evalLFNat; rewrite evalLF_add, evalLF_scale2; lia).
  rewrite ha_eq, hc_eq, hout_eq.
  exact (era_drain_iter cm1 k (exSR vN vQ vm rtail)).
Qed.

Lemma symTryEraOscR_ok {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm) (r : list SRChunk)
  (j2 c : LinForm) (rtail : list SRChunk) :
  validR vN vQ vm r -> symTryEraOscR P r = Some (j2, c, rtail) ->
  (0 <= evalLF vN vQ vm j2)%Z /\ (evalLF vN vQ vm j2 mod 2 = 0)%Z /\
  (1 <= evalLF vN vQ vm c)%Z /\ validR vN vQ vm rtail /\
  exSR vN vQ vm r = rep001 (evalLFNat vN vQ vm j2) (S0 >> rep001 (evalLFNat vN vQ vm c) (exSR vN vQ vm rtail)).
Proof.
  intros hr H.
  unfold symTryEraOscR in H.
  destruct r as [| [| | j0] r1]; try discriminate.
  - destruct r1 as [| [| | c0] rt]; try discriminate.
    apply some_inj, pair_inj in H; destruct H as [H <-]; apply pair_inj in H; destruct H as [<- <-].
    destruct hr as [hc hrt].
    split; [rewrite evalLF_const; lia |].
    split; [rewrite evalLF_const; lia |].
    split; [exact hc | split; [exact hrt |]].
    cbn [exSR]. change 0%Z with (Z.of_nat 0). rewrite evalLFNat_const. reflexivity.
  - destruct r1 as [| [| | ?] [| [| | c0] rt]]; try discriminate.
    destruct (sp_isEven P j0 && sp_isNonneg P (lfSub j0 (lfConst 2%Z))) eqn:hcond; [| discriminate].
    apply some_inj, pair_inj in H; destruct H as [H <-]; apply pair_inj in H; destruct H as [<- <-].
    rewrite Bool.andb_true_iff in hcond.
    destruct hcond as [hev h2].
    pose proof (vp_even_ok _ _ _ _ hP j0 hev) as hjev.
    pose proof (vp_nonneg_ok _ _ _ _ hP _ h2) as hjge2.
    rewrite evalLF_sub, evalLF_const in hjge2.
    destruct hr as [_ [hc hrt]].
    split; [lia | exact (conj hjev (conj hc (conj hrt eq_refl)))].
Qed.

Lemma symTryEraOsc_sound {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm)
  (hd : Sym) (l : list SLChunk) (r : list SRChunk) (hs : list N) (s' : SymState) :
  validSym vN vQ vm (mkSymState hd l r hs) ->
  symTryEraOsc P hd l r hs = Some s' ->
  validSym vN vQ vm s' /\ evalSym vN vQ vm (mkSymState hd l r hs) -->+ evalSym vN vQ vm s'.
Proof.
  intros [hvl hvr] H.
  unfold symTryEraOsc in H.
  destruct hd as [|]; [discriminate |].
  assert (hcore : forall (is10 : bool) (a : LinForm) (ltail : list SLChunk),
    (1 <= evalLF vN vQ vm a)%Z -> validL vN vQ vm ltail ->
    exSL vN vQ vm l = (if is10 then S1 >> S0 >> rep110 (evalLFNat vN vQ vm a) (exSL vN vQ vm ltail)
                       else S0 >> rep110 (evalLFNat vN vQ vm a) (exSL vN vQ vm ltail)) ->
    (match symTryEraOscR P r with
     | Some (j2, c, rtail) =>
       let cmp :=
         if lf_eqb a c then Some (a, ltail, rtail)
         else if sp_isPos P (lfSub c a) then Some (a, ltail, symPushR001 (lfSub c a) rtail)
         else if sp_isPos P (lfSub a c) then Some (c, symPushL110 (lfSub a c) ltail, rtail)
         else None
       in
       match cmp with
       | Some (n, lbase, rbase) =>
         let l1 := symPushL0 lbase in
         let l_new := if is10 then symPushL1 l1 else l1 in
         let r_new := symPushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase) in
         Some (mkSymState S1 l_new r_new hs)
       | None => None
       end
     | None => None
     end) = Some s' ->
    validSym vN vQ vm s' /\ evalSym vN vQ vm (mkSymState S1 l r hs) -->+ evalSym vN vQ vm s').
  { intros is10 a ltail ha hltail hexL Hbody.
    destruct (symTryEraOscR P r) as [[[j2 c] rtail] |] eqn:Er; [| discriminate].
    destruct (symTryEraOscR_ok hP r j2 c rtail hvr Er) as [hj0 [hjev [hc [hrtail hexR]]]].
    assert (hfinish : forall (n : LinForm) (lbase : list SLChunk) (rbase : list SRChunk),
      (1 <= evalLF vN vQ vm n)%Z ->
      validL vN vQ vm lbase -> validR vN vQ vm rbase ->
      rep110 (evalLFNat vN vQ vm a) (exSL vN vQ vm ltail) = rep110 (evalLFNat vN vQ vm n) (exSL vN vQ vm lbase) ->
      rep001 (evalLFNat vN vQ vm c) (exSR vN vQ vm rtail) = rep001 (evalLFNat vN vQ vm n) (exSR vN vQ vm rbase) ->
      s' = mkSymState S1 (if is10 then symPushL1 (symPushL0 lbase) else symPushL0 lbase)
                         (symPushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase)) hs ->
      validSym vN vQ vm s' /\ evalSym vN vQ vm (mkSymState S1 l r hs) -->+ evalSym vN vQ vm s').
    { intros n lbase rbase hn hlbase hrbase hLsplit hRsplit ->.
      destruct (exSL_pushL0 lbase hlbase) as [hvl0 hexl0].
      destruct (exSR_pushR0 rbase hrbase) as [hvr0 hexr0].
      assert (hj2n_pos : (1 <= evalLF vN vQ vm (lfAdd j2 (lfScale2 n)))%Z)
        by (rewrite evalLF_add, evalLF_scale2; lia).
      destruct (exSR_pushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase) hj2n_pos hvr0) as [hvr1 hexr1].
      set (nm1 := evalLFNat vN vQ vm n - 1).
      set (j := evalLFNat vN vQ vm j2 / 2).
      assert (hn_eq : evalLFNat vN vQ vm n = nm1 + 1) by (unfold nm1, evalLFNat; lia).
      assert (hj_eq : evalLFNat vN vQ vm j2 = 2 * j) by (unfold j, evalLFNat; lia).
      assert (hjout_eq : evalLFNat vN vQ vm (lfAdd j2 (lfScale2 n)) = 2 * (j + (nm1 + 1)))
        by (unfold j, nm1, evalLFNat; rewrite evalLF_add, evalLF_scale2; lia).
      destruct is10.
      - destruct (exSL_pushL1 (symPushL0 lbase) hvl0) as [hvl1 hexl1].
        split; [exact (conj hvl1 hvr1) |].
        unfold evalSym; cbn [sst_hd sst_l sst_r].
        rewrite hexL, hexR, hLsplit, hRsplit, hexl1, hexl0, hexr1, hexr0, hn_eq, hj_eq, hjout_eq.
        exact (era_osc10_iter nm1 j (exSL vN vQ vm lbase) (exSR vN vQ vm rbase)).
      - split; [exact (conj hvl0 hvr1) |].
        unfold evalSym; cbn [sst_hd sst_l sst_r].
        rewrite hexL, hexR, hLsplit, hRsplit, hexl0, hexr1, hexr0, hn_eq, hj_eq, hjout_eq.
        exact (era_osc_iter nm1 j (exSL vN vQ vm lbase) (exSR vN vQ vm rbase)). }
    cbv zeta in Hbody.
    destruct (lf_eqb a c) eqn:heq.
    - apply lf_eqb_eq in heq. subst c.
      apply some_inj in Hbody.
      exact (hfinish a ltail rtail ha hltail hrtail eq_refl eq_refl (eq_sym Hbody)).
    - destruct (sp_isPos P (lfSub c a)) eqn:hca.
      + apply some_inj in Hbody.
        pose proof (vp_pos_ok hP _ hca) as hsub.
        destruct (exSR_pushR001 (lfSub c a) rtail hsub hrtail) as [hvr_sub hexr_sub].
        assert (hce : evalLFNat vN vQ vm c = evalLFNat vN vQ vm a + evalLFNat vN vQ vm (lfSub c a))
          by (unfold evalLFNat; rewrite evalLF_sub in hsub |- *; lia).
        refine (hfinish a ltail (symPushR001 (lfSub c a) rtail) ha hltail hvr_sub eq_refl _ (eq_sym Hbody)).
        rewrite hexr_sub, hce, rep001_add. reflexivity.
      + destruct (sp_isPos P (lfSub a c)) eqn:hac2; [| discriminate].
        apply some_inj in Hbody.
        pose proof (vp_pos_ok hP _ hac2) as hsub.
        destruct (exSL_pushL110 (lfSub a c) ltail hsub hltail) as [hvl_sub hexl_sub].
        assert (hae : evalLFNat vN vQ vm a = evalLFNat vN vQ vm c + evalLFNat vN vQ vm (lfSub a c))
          by (unfold evalLFNat; rewrite evalLF_sub in hsub |- *; lia).
        refine (hfinish c (symPushL110 (lfSub a c) ltail) rtail hc hvl_sub hrtail _ eq_refl (eq_sym Hbody)).
        rewrite hexl_sub, hae, rep110_add. reflexivity. }
  destruct l as [| [| | ?] l1]; try discriminate.
  - destruct l1 as [| [| | a] ltail]; try discriminate.
    destruct hvl as [ha hltail].
    exact (hcore false a ltail ha hltail eq_refl H).
  - destruct l1 as [| [| | ?] [| [| | a] ltail]]; try discriminate.
    destruct hvl as [ha hltail].
    exact (hcore true a ltail ha hltail eq_refl H).
Qed.

Lemma symStepBase_sound {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm)
  (hd : Sym) (l : list SLChunk) (r : list SRChunk) (hs : list N) (s' : SymState) :
  validSym vN vQ vm (mkSymState hd l r hs) ->
  symStepBase P hd l r hs = Some s' ->
  validSym vN vQ vm s' /\ evalSym vN vQ vm (mkSymState hd l r hs) -->+ evalSym vN vQ vm s'.
Proof.
  intros [hl hr].
  unfold symStepBase.
  destruct (baseDispatch _ _ _ _ _ _ _ _ _ _ _ hd l r) as [[[hd' l'] r']|] eqn:E;
    [|discriminate].
  intros [= <-].
  assert (hc : (1 <= evalLF vN vQ vm (lfConst 1%Z))%Z) by (rewrite evalLF_const; lia).
  assert (hcN : evalLFNat vN vQ vm (lfConst 1%Z) = 1).
  { change 1%Z with (Z.of_nat 1). apply evalLFNat_const. }
  eapply (baseDispatch_sound tm C D (exSL vN vQ vm) (exSR vN vQ vm) (validL vN vQ vm) (validR vN vQ vm)) in E.
  - destruct E as [hl' [hr' H]]. exact (conj (conj hl' hr') H).
  - exact (symSplitL_ok hP).
  - exact symSplitR_ok.
  - exact (symStripOnesL_ok hP).
  - exact (symPopL_ok hP).
  - exact (symPopR_ok hP).
  - exact exSL_pushL0.
  - exact exSL_pushL1.
  - intros a ha. pose proof (exSL_pushL110 _ a hc ha) as H. rewrite hcN in H. exact H.
  - exact exSR_pushR0.
  - intros a ha. exact (conj ha eq_refl).
  - intros a ha. pose proof (exSR_pushR001 _ a hc ha) as H. rewrite hcN in H. exact H.
  - intros a b. apply evstep_one. apply @step_left. reflexivity.
  - exact reach_R1_lb.
  - exact reach_R2_lb.
  - exact reach_R3_lb.
  - exact reach_L1_lb.
  - exact reach_L2_lb.
  - exact reach_L3_lb.
  - exact hl.
  - exact hr.
Qed.

Lemma symStep_sound {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm)
  (s s' : SymState) :
  validSym vN vQ vm s -> symStep P s = Some s' ->
  validSym vN vQ vm s' /\ evalSym vN vQ vm s -->+ evalSym vN vQ vm s'.
Proof.
  destruct s as [hd l r hs].
  intros hv H.
  unfold symStep in H; cbn [sst_hd sst_l sst_r sst_hs] in H.
  destruct (symTrySuper4x P hd l r hs) as [s0 |] eqn:E0.
  - apply some_inj in H; subst s'. exact (symTrySuper4x_sound hP hd l r hs s0 hv E0).
  - destruct (symTryEraDrain P hd l r hs) as [s1 |] eqn:E1.
    + apply some_inj in H; subst s'. exact (symTryEraDrain_sound hP hd l r hs s1 hv E1).
    + destruct (symTryEraOsc P hd l r hs) as [s2 |] eqn:E2.
      * apply some_inj in H; subst s'. exact (symTryEraOsc_sound hP hd l r hs s2 hv E2).
      * exact (symStepBase_sound hP hd l r hs s' hv H).
Qed.

Lemma symIterPow2_sound {P : SymPred} {vN vQ vm : nat} (hP : ValidPred P vN vQ vm) :
  forall (k : nat) (s s' : SymState),
  validSym vN vQ vm s -> symIterPow2 P k s = Some s' ->
  validSym vN vQ vm s' /\ evalSym vN vQ vm s -->+ evalSym vN vQ vm s'.
Proof.
  induction k as [| k IH]; intros s s' hv H.
  - exact (symStep_sound hP s s' hv H).
  - cbn [symIterPow2 optBind] in H.
    destruct (symIterPow2 P k s) as [sm |] eqn:E1; [| discriminate].
    destruct (IH s sm hv E1) as [hvm h1].
    destruct (IH sm s' hvm H) as [hv' h2].
    exact (conj hv' (ptrans h1 h2)).
Qed.

(* ========================================================================== *)
(* Layer 4: Period-60 Shift, Attractor Closure, Symbolic Collapse, Non-Halt   *)
(* ========================================================================== *)

(* Stage B: Period-60 Exponential Shift *)

Definition InvB (a b : nat) : Prop :=
  16 <= b /\ 6 * b <= a /\ a mod 4 = 0 /\ b mod 4 = 0.

Definition predB : SymPred := mkSymPred
  (fun f =>
    (lf_am f =? 0)%Z && (0 <=? lf_aN f)%Z &&
    (0 <=? 6 * lf_aN f + lf_aQ f)%Z &&
    (0 <=? 16 * (6 * lf_aN f + lf_aQ f) + lf_ac f)%Z)
  (fun f => Z.even (lf_ac f))
  false.

Lemma validPredB {a b : nat} (h : InvB a b) : ValidPred predB a b 0.
Proof.
  assert (hpar : forall f : LinForm, exists K : Z, evalLF a b 0 f = (2 * K + lf_ac f)%Z).
  { intros f. destruct h as [_ [_ [ha4 hb4]]].
    set (ka := a / 2). set (kb := b / 2).
    assert (ha2 : a = 2 * ka) by (clear - ha4; unfold ka; lia).
    assert (hb2 : b = 2 * kb) by (clear - hb4; unfold kb; lia).
    exists (lf_aN f * Z.of_nat ka + lf_aQ f * Z.of_nat kb)%Z.
    unfold evalLF. rewrite ha2, hb2. clear. nia. }
  constructor.
  - intros f hok.
    destruct h as [hb16 [h6 [_ _]]].
    unfold predB in hok; cbn [sp_isNonneg] in hok.
    rewrite !Bool.andb_true_iff, Z.eqb_eq, !Z.leb_le in hok.
    destruct hok as [[[ham haN] h6a] h16].
    unfold evalLF; rewrite ham.
    assert (hs1 : (lf_aN f * (6 * Z.of_nat b) <= lf_aN f * Z.of_nat a)%Z) by (clear - h6 haN; nia).
    assert (hs2 : ((6 * lf_aN f + lf_aQ f) * 16 <= (6 * lf_aN f + lf_aQ f) * Z.of_nat b)%Z)
      by (clear - hb16 h6a; nia).
    clear - hs1 hs2 h16. nia.
  - intros f hok.
    unfold predB in hok; cbn [sp_isEven] in hok.
    apply Z_even_mod2 in hok.
    destruct (hpar f) as [K ->]. clear - hok. lia.
  - intros f hne.
    unfold predB in hne; cbn [sp_isEven] in hne.
    apply Z_even_false_mod2 in hne.
    destruct (hpar f) as [K ->]. clear - hne. lia.
  - cbn [sp_allowS4x]; discriminate.
Qed.

Definition symStartB : SymState :=
  mkSymState S0 [] [srt001 (mkLF 1%Z 0%Z 0%Z (-1)%Z); srb0; srt001 (mkLF 0%Z 1%Z 0%Z (-1)%Z)] [].

Definition symEndB : SymState :=
  mkSymState S0 [] [srt001 (mkLF 4%Z (-4)%Z 0%Z (-1)%Z); srb0; srt001 (mkLF 0%Z 4%Z 0%Z (-1)%Z)] [].

Definition symRun60 (s : SymState) : option SymState :=
  optBind (symIterPow2 predB 5 s) (fun s1 =>
  optBind (symIterPow2 predB 4 s1) (fun s2 =>
  optBind (symIterPow2 predB 3 s2) (symIterPow2 predB 2))).

Lemma symRun60_eq : symRun60 symStartB = Some symEndB.
Proof. vm_compute. reflexivity. Qed.

Lemma symRun60_sound {vN vQ vm : nat} (hP : ValidPred predB vN vQ vm) (s s' : SymState) :
  validSym vN vQ vm s -> symRun60 s = Some s' ->
  validSym vN vQ vm s' /\ evalSym vN vQ vm s -->+ evalSym vN vQ vm s'.
Proof.
  intros hv0 H.
  unfold symRun60 in H.
  destruct (symIterPow2 predB 5 s) as [s1 |] eqn:E1; [| discriminate].
  cbn [optBind] in H.
  destruct (symIterPow2 predB 4 s1) as [s2 |] eqn:E2; [| discriminate].
  cbn [optBind] in H.
  destruct (symIterPow2 predB 3 s2) as [s3 |] eqn:E3; [| discriminate].
  cbn [optBind] in H.
  destruct (symIterPow2_sound hP 5 s s1 hv0 E1) as [hv1 h1].
  destruct (symIterPow2_sound hP 4 s1 s2 hv1 E2) as [hv2 h2].
  destruct (symIterPow2_sound hP 3 s2 s3 hv2 E3) as [hv3 h3].
  destruct (symIterPow2_sound hP 2 s3 s' hv3 H) as [hv4 h4].
  exact (conj hv4 (ptrans h1 (ptrans h2 (ptrans h3 h4)))).
Qed.

Lemma period60_one {a b : nat} (hinv : InvB a b) :
  p60Cfg a b -->+ p60Cfg (4 * (a - b)) (4 * b).
Proof.
  pose proof (validPredB hinv) as hP.
  destruct hinv as [hb16 [h6 [_ _]]].
  assert (hv0 : validSym a b 0 symStartB).
  { unfold validSym, symStartB; cbn [sst_l sst_r validL validR].
    unfold evalLF; cbn [lf_aN lf_aQ lf_am lf_ac].
    split; [exact I | split; [lia | split; [lia | exact I]]]. }
  destruct (symRun60_sound hP symStartB symEndB hv0 symRun60_eq) as [_ hall].
  assert (hstart : evalSym a b 0 symStartB = p60Cfg a b).
  { unfold evalSym, symStartB, p60Cfg; cbn [sst_hd sst_l sst_r exSL exSR].
    replace (evalLFNat a b 0 (mkLF 1%Z 0%Z 0%Z (-1)%Z)) with (a - 1)
      by (unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; lia).
    replace (evalLFNat a b 0 (mkLF 0%Z 1%Z 0%Z (-1)%Z)) with (b - 1)
      by (unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; lia).
    reflexivity. }
  assert (hend : evalSym a b 0 symEndB = p60Cfg (4 * (a - b)) (4 * b)).
  { unfold evalSym, symEndB, p60Cfg; cbn [sst_hd sst_l sst_r exSL exSR].
    replace (evalLFNat a b 0 (mkLF 4%Z (-4)%Z 0%Z (-1)%Z)) with (4 * (a - b) - 1)
      by (unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; lia).
    replace (evalLFNat a b 0 (mkLF 0%Z 4%Z 0%Z (-1)%Z)) with (4 * b - 1)
      by (unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; lia).
    reflexivity. }
  rewrite hstart, hend in hall.
  exact hall.
Qed.

Lemma period60_iter : forall (k a b : nat),
  16 <= b -> b mod 4 = 0 -> a mod 4 = 0 -> (k + 5) * b <= a ->
  p60Cfg a b -->* p60Cfg (pow4 k * (a - k * b)) (pow4 k * b).
Proof.
  induction k as [| k IH]; intros a b hb16 hb4 ha4 hle.
  - cbn [pow4].
    replace (1 * (a - 0 * b)) with a by (clear; lia).
    replace (1 * b) with b by (clear; lia).
    apply evstep_refl.
  - assert (h6 : 6 * b <= a) by (clear - hle; nia).
    pose proof (pev (period60_one (conj hb16 (conj h6 (conj ha4 hb4))))) as h1.
    assert (hb16' : 16 <= 4 * b) by (clear - hb16; lia).
    assert (hb4' : (4 * b) mod 4 = 0) by (clear; lia).
    assert (ha4' : (4 * (a - b)) mod 4 = 0) by (clear; lia).
    assert (hle' : (k + 5) * (4 * b) <= 4 * (a - b)) by (clear - hle; nia).
    pose proof (IH (4 * (a - b)) (4 * b) hb16' hb4' ha4' hle') as h2.
    replace (pow4 k * (4 * (a - b) - k * (4 * b))) with (pow4 (S k) * (a - S k * b)) in h2
      by (clear - hle; cbn [pow4]; nia).
    replace (pow4 k * (4 * b)) with (pow4 (S k) * b) in h2
      by (clear; cbn [pow4]; nia).
    exact (etrans h1 h2).
Qed.

(* Stage D: Period-642 Exponential Attractor Closure *)

Definition Inv (vm vn : nat) : Prop :=
  10 <= vm /\ vm mod 2 = 0 /\ vn mod 2 = 0 /\
  (600 * Z.of_nat (sum4 vm) + 200 + 2000 * Z.of_nat vm <= 9 * Z.of_nat vn)%Z /\
  (9 * Z.of_nat vn + 2000 * Z.of_nat vm <= 615 * Z.of_nat (sum4 vm) + 205)%Z.

Lemma inv_step {vm vn : nat} (h : Inv vm vn) :
  Inv (vm + 4) (N.to_nat 256%N * vn + 54 - N.to_nat 180%N * vm).
Proof.
  destruct h as [hm10 [hme [hNe [hlo hhi]]]].
  pose proof (sum4_lower_Z vm hm10) as hql.
  assert (hs4 : Z.of_nat (sum4 (vm + 4)) = (256 * Z.of_nat (sum4 vm) + 85)%Z).
  { rewrite (sum4_add vm 4). cbn [pow4 sum4]. clear. lia. }
  assert (hsub : (N.to_nat 180%N * vm <= N.to_nat 256%N * vn)).
  { change (N.to_nat 180%N) with (Z.to_nat 180%Z).
    change (N.to_nat 256%N) with (Z.to_nat 256%Z).
    clear - hm10 hql hlo. lia. }
  unfold Inv. rewrite hs4.
  split; [clear - hm10; lia |].
  split; [clear - hme; lia |].
  split; [clear - hNe hsub;
    replace (N.to_nat 256%N) with (2 * 128) by reflexivity;
    replace (N.to_nat 180%N) with (2 * 90) by reflexivity; lia |].
  split; (
    change (N.to_nat 256%N) with (Z.to_nat 256%Z);
    change (N.to_nat 180%N) with (Z.to_nat 180%Z);
    clear - hm10 hql hlo hhi; lia).
Qed.

Definition isNonnegD (f : LinForm) : bool :=
  let '(cQ, cm, cc) :=
    if (0 <=? lf_aN f)%Z then
      (600 * lf_aN f + 9 * lf_aQ f, 2000 * lf_aN f + 9 * lf_am f, 200 * lf_aN f + 9 * lf_ac f)%Z
    else
      (615 * lf_aN f + 9 * lf_aQ f, -2000 * lf_aN f + 9 * lf_am f, 205 * lf_aN f + 9 * lf_ac f)%Z
  in
  if (cQ <? 0)%Z then false
  else if (cQ =? 0)%Z then (0 <=? cm)%Z && (0 <=? cm * 10 + cc)%Z
  else
    let mc := (cQ * 15000 + cm)%Z in
    let kc := (cQ * 150000 + cc)%Z in
    (0 <=? mc)%Z && (0 <=? mc * 10 + kc)%Z.

Definition predD : SymPred := mkSymPred
  isNonnegD
  (fun f => Z.even (lf_aQ f + lf_ac f)%Z)
  true.

Lemma validPredD {vm vn : nat} (hinv : Inv vm vn) : ValidPred predD vn (sum4 vm) vm.
Proof.
  assert (hpar : forall f : LinForm, exists K : Z,
    evalLF vn (sum4 vm) vm f = (2 * K + (lf_aQ f + lf_ac f))%Z).
  { intros f. destruct hinv as [hm10 [hme [hNe _]]].
    pose proof (sum4_odd vm ltac:(clear - hm10; lia)) as hQo.
    set (kN := vn / 2). set (km := vm / 2). set (kQ := sum4 vm / 2).
    assert (hvn : vn = 2 * kN) by (clear - hNe; unfold kN; lia).
    assert (hvm : vm = 2 * km) by (clear - hme; unfold km; lia).
    assert (hq : sum4 vm = 2 * kQ + 1) by (clear - hQo; unfold kQ; lia).
    exists (lf_aN f * Z.of_nat kN + lf_aQ f * Z.of_nat kQ + lf_am f * Z.of_nat km)%Z.
    unfold evalLF. rewrite hq, hvn, hvm. clear. nia. }
  constructor.
  - intros f hok.
    destruct hinv as [hm10 [_ [_ [hlo hhi]]]].
    pose proof (sum4_lower_Z vm hm10) as hQ_low.
    assert (hfinish : forall cQ cm cc : Z,
      (cQ * Z.of_nat (sum4 vm) + cm * Z.of_nat vm + cc <= 9 * evalLF vn (sum4 vm) vm f)%Z ->
      (if (cQ <? 0)%Z then false
       else if (cQ =? 0)%Z then (0 <=? cm)%Z && (0 <=? cm * 10 + cc)%Z
       else
         let mc := (cQ * 15000 + cm)%Z in
         let kc := (cQ * 150000 + cc)%Z in
         (0 <=? mc)%Z && (0 <=? mc * 10 + kc)%Z) = true ->
      (0 <= evalLF vn (sum4 vm) vm f)%Z).
    { intros cQ cm cc hbound hchk.
      destruct (Z.ltb_spec cQ 0%Z) as [hneg | hnn]; [discriminate |].
      destruct (Z.eqb_spec cQ 0%Z) as [-> | hnz].
      - rewrite Bool.andb_true_iff, !Z.leb_le in hchk. clear - hm10 hbound hchk. nia.
      - cbv zeta in hchk. rewrite Bool.andb_true_iff, !Z.leb_le in hchk.
        clear - hm10 hQ_low hnn hbound hchk. nia. }
    unfold predD in hok; cbn [sp_isNonneg] in hok; unfold isNonnegD in hok.
    destruct (Z.leb_spec 0%Z (lf_aN f)) as [ha | ha].
    + apply (hfinish (600 * lf_aN f + 9 * lf_aQ f)%Z
                     (2000 * lf_aN f + 9 * lf_am f)%Z
                     (200 * lf_aN f + 9 * lf_ac f)%Z);
        [clear - hlo ha; unfold evalLF; nia | exact hok].
    + apply (hfinish (615 * lf_aN f + 9 * lf_aQ f)%Z
                     (-2000 * lf_aN f + 9 * lf_am f)%Z
                     (205 * lf_aN f + 9 * lf_ac f)%Z);
        [clear - hhi ha; unfold evalLF; nia | exact hok].
  - intros f hok.
    unfold predD in hok; cbn [sp_isEven] in hok.
    apply Z_even_mod2 in hok.
    destruct (hpar f) as [K ->]. clear - hok. lia.
  - intros f hne.
    unfold predD in hne; cbn [sp_isEven] in hne.
    apply Z_even_false_mod2 in hne.
    destruct (hpar f) as [K ->]. clear - hne. lia.
  - intros _. destruct hinv as [hm10 _]. split; [reflexivity | clear - hm10; lia].
Qed.

Definition symStartD : SymState :=
  mkSymState S0 [slt110 (mkLF 1%Z 0%Z 0%Z 0%Z); slb1] [] [0; 1; 1; 0; 2; 3; 3; 2]%N.

Definition symEndD : SymState :=
  mkSymState S0 [slt110 (mkLF 256%Z 0%Z (-180)%Z 54%Z); slb1] [] [].

Definition symRun642 (s : SymState) : option SymState :=
  optBind (optBind (symIterPow2 predD 9 s) (symIterPow2 predD 7)) (symIterPow2 predD 1).

Lemma symRun642_eq : symRun642 symStartD = Some symEndD.
Proof. vm_compute. reflexivity. Qed.

Lemma symRun642_sound {vN vQ vm : nat} (hP : ValidPred predD vN vQ vm) (s s' : SymState) :
  validSym vN vQ vm s -> symRun642 s = Some s' ->
  validSym vN vQ vm s' /\ evalSym vN vQ vm s -->+ evalSym vN vQ vm s'.
Proof.
  intros hv0 H.
  unfold symRun642 in H.
  destruct (symIterPow2 predD 9 s) as [s1 |] eqn:E1; [| discriminate].
  cbn [optBind] in H.
  destruct (symIterPow2 predD 7 s1) as [s2 |] eqn:E2; [| discriminate].
  cbn [optBind] in H.
  destruct (symIterPow2_sound hP 9 s s1 hv0 E1) as [hv1 h1].
  destruct (symIterPow2_sound hP 7 s1 s2 hv1 E2) as [hv2 h2].
  destruct (symIterPow2_sound hP 1 s2 s' hv2 H) as [hv3 h3].
  exact (conj hv3 (ptrans h1 (ptrans h2 h3))).
Qed.

Lemma cycle_642 {vm vn : nat} (hinv : Inv vm vn) :
  attractorCfg vn -->+ attractorCfg (N.to_nat 256%N * vn + 54 - N.to_nat 180%N * vm).
Proof.
  pose proof (validPredD hinv) as hP.
  assert (hNpos : 1 <= vn).
  { destruct hinv as [hm10 [_ [_ [hlo _]]]].
    pose proof (sum4_lower_Z vm hm10) as hq. clear - hm10 hlo hq. lia. }
  assert (hge : (180 * Z.of_nat vm <= 256 * Z.of_nat vn)%Z).
  { destruct hinv as [hm10 [_ [_ [hlo _]]]].
    pose proof (sum4_lower_Z vm hm10) as hq. clear - hm10 hlo hq. lia. }
  assert (hv0 : validSym vn (sum4 vm) vm symStartD).
  { unfold validSym, symStartD; cbn [sst_l sst_r validL validR].
    unfold evalLF; cbn [lf_aN lf_aQ lf_am lf_ac].
    split; [split; [clear - hNpos; lia | exact I] | exact I]. }
  destruct (symRun642_sound hP symStartD symEndD hv0 symRun642_eq) as [_ hall].
  assert (hstart_eq : evalSym vn (sum4 vm) vm symStartD = attractorCfg vn).
  { unfold evalSym, symStartD, attractorCfg; cbn [sst_hd sst_l sst_r exSL exSR].
    replace (evalLFNat vn (sum4 vm) vm (mkLF 1%Z 0%Z 0%Z 0%Z)) with vn
      by (clear; unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; lia).
    reflexivity. }
  assert (hend_eq : evalSym vn (sum4 vm) vm symEndD = attractorCfg (N.to_nat 256%N * vn + 54 - N.to_nat 180%N * vm)).
  { unfold evalSym, symEndD, attractorCfg; cbn [sst_hd sst_l sst_r exSL exSR].
    replace (evalLFNat vn (sum4 vm) vm (mkLF 256%Z 0%Z (-180)%Z 54%Z))
      with (N.to_nat 256%N * vn + 54 - N.to_nat 180%N * vm)
      by (change (N.to_nat 256%N) with (Z.to_nat 256%Z);
          change (N.to_nat 180%N) with (Z.to_nat 180%Z);
          clear - hge; unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; lia).
    reflexivity. }
  rewrite hstart_eq, hend_eq in hall.
  exact hall.
Qed.

Definition InAttractor (cfg : Q * tape) : Prop :=
  exists vm vn : nat, Inv vm vn /\ cfg = attractorCfg vn.

Lemma attractor_closed : forall cfg, InAttractor cfg -> exists cfg', InAttractor cfg' /\ cfg -->+ cfg'.
Proof.
  intros _ [vm [vn [hinv ->]]].
  exists (attractorCfg (N.to_nat 256%N * vn + 54 - N.to_nat 180%N * vm)).
  split.
  - exists (vm + 4), (N.to_nat 256%N * vn + 54 - N.to_nat 180%N * vm).
    exact (conj (inv_step hinv) eq_refl).
  - exact (cycle_642 hinv).
Qed.

(* Stage C: 2,083-Step Symbolic Collapse into the Attractor *)

Definition a0Val_N : N := 0xee1a05c2bb202af7062a2205f9258e64018c1ae1866fec79497a64be47663822739b8caa5eb18c94923a8884032508de9f299563b0b4c508418c43069d3bb7a9f34293b44a241b4987741c6e3d8cf0a1e5e17fa1a9e3d126b6831297dd605ba9d7f0ad768092bbeda11010ea078b4349bfcce9acf80125b0ffa1bf6bb4b3dff76278675aaf5f486d1ab973becccc1572c8fe69f9a1a4bd671f765ffc57dc73f31126c35d7866ff94906aab353035d831b4a38dc242f9f79494285c0017307a7be0e4ad8bc485a610e1a98904e84736f953e4abff2045ab820815b9f4a1c7206789bc2753034592c2c25977a3de3e1858acdc6e96feaec77b0187eaf7b59790f47ed6c7d1b7a0d7fa23bef2c93fce7209b4228b539432ac2a5003abf71d9d7fd580429430c934b4a36eeacf4234f20c6f35ccde90a9dce10dc86c34cd18adfdf4a220b2a350d687155e1cabbab5c6b740face124cf8c3dded7ce6a9991a2a1680e86926a6ed3d49f7c0a96f3c9cd2cd8aa3042f6c4f8c50cac3918004be5bbff20c06363c4018cbc08a97a65f6285d4bbbb3eecca1d1fb1532e1ded8ad8f92462b24ee238a2069cd0a93b0a752685b6744349d6c619c84dc4629ed988d085c1ef04eec41e71d63870f89a3db056f368d5499e8f6cc0e0e12d5fe1fce83abd036136960dc2c67ea66b06bbbb7427efe48c798b42846f08c814791bcda2b151c2a9b610e8517bfac69280be16786d9671620a807f3937649647e51e84408d32424a4de223e3d5726d56f5de94f85d0f7ef457c6873ee40cd5f0fb793ce6946907a4df1301f92a4b34ab36ebc8785e69d13fcbfe1974d4ade3c731fec37ca6082626a645fc86bfc3a861631b0bd89fd649c821977def0a2059450bf0019898e9022c7c1dcbdfd24e92ed603cb248a6c04607cd8223d53d0%N.
Definition b0Val_N : N := 0x940a0c42196215e0dd1f535e6f94667060b3b3d5e82e85a881bf05505b6413f822659cda53cf16489d31dd61eec3ab1a7320e09c082c41bf5a9919d431d8a6e8eaa837317cee9c2130fba38d5b80b06f1178ca1fd16e814f0026793c6ce8b56b86668f6a3db9fac66bad39cf49890309304f2451d4ec0c9d7443df3e7606c2c1907134f4593b17df628f48e1557420454142a3e585b0e1beaacd6bdd146645be762b1fde3ad58fff2d76d00499bd2902dd2ec0997b9e640ebedfc2538784ec2f86c406e82f9a20831f911252a054d10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000%N.
Definition KVal_N : N := 115895156973855250%N.
Definition ACoeff_N : N := 0x2fdf89e5a060e54855ec267c02a342c80e5405fbe9896e295101932464eac8158ae8ce146e785d57e569a64935de0416f29f0d483c10fab6f2df68481ed7a9dd14593b84cf086dcdf0755289fe63906f9cfb5a08dadf3c3c5a9f90fabbb95993a8559eea463fe8f48b599e1fbb51b8e33437b19a42988f203013fe333fcf09da164836ce385f191711084ed4da1ef40ecb2cbaed1f27aa6475d2af857a1ea10b16e46cf346e6bb551f026ef61956a51172783c58667c68f11cdd62a07dde4a3850cf84a48aeab44561fecc71a142793ab820815b9f4a1c7206789bc2753034592c2c25977a3de3e1858acdc6e96feaec77b0187eaf7b59790f47ed6c7d1b7a0d7fa23bef2c93fce7209b4228b539432ac2a5003abf71d9d7fd580429430c934b4a36eeacf4234f20c6f35ccde90a9dce10dc86c34cd18adfdf4a220b2a350d687155e1cabbab5c6b740face124cf8c3dded7ce6a9991a2a1680e86926a6ed3d49f7c0a96f3c9cd2cd8aa3042f6c4f8c50cac3918004be5bbff20c06363c4018cbc08a97a65f6285d4bbbb3eecca1d1fb1532e1ded8ad8f92462b24ee238a2069cd0a93b0a752685b6744349d6c619c84dc4629ed988d085c1ef04eec41e71d63870f89a3db056f368d5499e8f6cc0e0e12d5fe1fce83abd036136960dc2c67ea66b06bbbb7427efe48c798b42846f08c814791bcda2b151c2a9b610e8517bfac69280be16786d9671620a807f3937649647e51e84408d32424a4de223e3d5726d56f5de94f85d0f7ef457c6873ee40cd5f0fb793ce6946907a4df1301f92a4b34ab36ebc8785e69d13fcbfe1974d4ade3c731fec37ca6082626a645fc86bfc3a861631b0bd89fd649c821977def0a2059450bf0019898e9022c7c1dcbdfd24e92ed603cb248a6c04607cd8223d53d0%N.
Definition C3Val_N : N := 0x4303147573c479bc55e386c3babf6e1ae11cdb6bc1fa98fda87e46c7c493aabfb2828e971e7c7323732e70f51f657e37a696141a913b6ab85ce2c235a4eaaa404c81e79c6bb43477535ec497ea78c8719a326385f163ccf40b17fedfa95e8b501c635c4894d1ca3a8708746f80dc4b24e20a6ea469f5b73c1404b12f795801c5721fedf70bfe3a4328d827b1b43b0187db6dd4e5703cd0acab32d2a388cf03d7b6389720533c09eb6d884b01c994832b32e8a432955a0e57e9b1f5230ace64af5b8521b922e55110b833e3445b8ef3dcc3ff7607a6864032acf693c73a4dde52144f10e70500029f8ec414d7344324a0ba179752d9e7cf92f8c724850fb9de4bd5016f8ae75c85db542d2a0ef18c78732d77eefc9e4efb7fe0255400604ece779b6f64d4433d89771f2479b0233db68ffc60c8b3b097d28dd68aba6e01ee7948a57056e5994e2af11389851230ff6a7bfb1a57c2533ad297f99e219aa023ec4e8e75783b7ba6d99e4a1e198ede09f799e2bea9f23cb3fe1c4d71df7e0b043d4f63ed8ca50ca0c89e5260293e2a6cb191347226fbccd0943d9f01c976ecb96c9ebe359f89d328f71ad7cd14e86f11ef432d1e08c7c2cc6fadbeb31f75b598c15a45ad55cd6c98b2e1896a191363b43dc190a6fff06bcfaac74006883818841cb9a19a2a62d26f11e0b5a3621736bce46065fdcfcb7df5224713c5e05cf2be8d251ac780878d1a6132f29e645c1030db33200802846a0edf284edca9e3478f744f34d25c5a5a46e24c9ed3408ab8ce5441c7d2137756b3300dd1d6a73d40893a65ff02d14964583221bc6677adc311a13ed913c82d9f1cb0483697c79b8c5dfbcebe403e1b981d6a382d0dde9f8ef595f65f94c3546cc4c5c7d1444d4cf437458035ab88b979b5e4802bd9dd628cc89c0000000%N.
Definition D0Val_N : N := 0x16565c272696d33ec74bd796939524b3a05ef3ce95fe32ff382a1797ec3138ea90d62f87b4d426612664d051b521d4bd37875c08db13ce3d744b9611e1a38e156ed5f7dece9166d2711f96dd4e2842d088bb7681fb2144515907ff9fe31f83c55ecbc96d86f098be2d02d17a80496e61a0ae24e178a73d1406ac3b0fd31d55ec7b5ff9fd03ff68c10d9d6290916900829e79f1a1d014458ee3bb9b8bd8450147e76832601bbeadf92482c3ab4331810e664d8c10dc735a1d4de5fc61039a218fc92c60930ba1c5b03d66a116c92fa69eebffd2028cd76abb8efcdbed136f4a1b5c1a5af7ac5556352f96b19d116bb6e03e07dd1b9df7efdba8426181afe89f6e9c55cfd8f7c981f3c6b9b8afa5d97d7bb9d2a4fedf6fa92aa00c7155756f9a27de7a76f16bbf2dd25fb6d33ab669e785542042e690329b849cd8e8cf55fa286d8c7ac7a1ddc4b8fb06832c5b65aa78d3fe5e1d40c668f0dd5334b5de35614ec4da272813d3e2488a18b4b32f9f58a7ddf63f8dfb699154b419d09fd4ae56bf1a76a4843704359834c6200dbf63799085bc260cfe999adc148a55edd24ee8798a3f67352df10da7b39d445c4d7a5b4fc10f0a02ed40eecfe494e65fd1e732eb1e1739c74479883ba083235db1213c1495dae2555023efe397c0022d68082c099335de0e20f0cfb0a03c8bcb5d123ef6cacca9efee7f51b617b141f57450ea2f0c5e42802d2f08cb10fb8a217405659e666002ab8178af9fb81a498df66d2fd16fbc461ec8c8c24b6edf9bc02e3d9a1c15ed46067d1ce66559f09ce269c02dbe21ffab9b1876c810b5e9777d39ebb08b14f306980f35099018123297de841f53ef94c014b3dd5f23680f049f8a84fc87521fdc411c244197429b16c46efc126c8011e3d83dd33ca1800e9df4762eed8cec43bd2%N.
Definition m2630_N : N := 2630%N.
Definition c373004_N : N := 373004%N.
Definition p4_2630_N : N := N.shiftl 1%N (N.double m2630_N).
Definition s4_2630_N : N := ((p4_2630_N - 1) / 3)%N.

Definition predC : SymPred := mkSymPred
  (fun f =>
    (lf_aN f =? 0)%Z && (0 <=? lf_aQ f)%Z &&
    (0 <=? 21 * lf_aQ f + lf_am f)%Z &&
    (0 <=? 85 * lf_aQ f + 4 * lf_am f + lf_ac f)%Z)
  (fun f => Z.even (lf_aQ f + lf_ac f)%Z)
  true.

Lemma validPredC {vK : nat} (hK4 : 4 <= vK) (hKe : vK mod 2 = 0) :
  ValidPred predC 0 (sum4 vK) vK.
Proof.
  assert (hpar : forall f : LinForm, exists K : Z,
    evalLF 0 (sum4 vK) vK f = (2 * K + (lf_aQ f + lf_ac f))%Z).
  { intros f.
    pose proof (sum4_odd vK ltac:(clear - hK4; lia)) as hQo.
    set (kK := vK / 2). set (kQ := sum4 vK / 2).
    assert (hvK : vK = 2 * kK) by (clear - hKe; unfold kK; lia).
    assert (hq : sum4 vK = 2 * kQ + 1) by (clear - hQo; unfold kQ; lia).
    exists (lf_aQ f * Z.of_nat kQ + lf_am f * Z.of_nat kK)%Z.
    unfold evalLF. rewrite hq, hvK. clear. nia. }
  constructor.
  - intros f hok.
    unfold predC in hok; cbn [sp_isNonneg] in hok.
    rewrite !Bool.andb_true_iff, Z.eqb_eq, !Z.leb_le in hok.
    destruct hok as [[[haN haQ] h21] h85].
    pose proof (sum4_ge_21_Z vK hK4) as hQ.
    unfold evalLF; rewrite haN.
    assert (hs1 : (lf_aQ f * (21 * Z.of_nat vK + 1) <= lf_aQ f * Z.of_nat (sum4 vK))%Z)
      by (clear - haQ hQ; nia).
    assert (hs2 : ((21 * lf_aQ f + lf_am f) * 4 <= (21 * lf_aQ f + lf_am f) * Z.of_nat vK)%Z)
      by (clear - h21 hK4; nia).
    clear - hs1 hs2 h85. nia.
  - intros f hok.
    unfold predC in hok; cbn [sp_isEven] in hok.
    apply Z_even_mod2 in hok.
    destruct (hpar f) as [K ->]. clear - hok. lia.
  - intros f hne.
    unfold predC in hne; cbn [sp_isEven] in hne.
    apply Z_even_false_mod2 in hne.
    destruct (hpar f) as [K ->]. clear - hne. lia.
  - intros _. split; [reflexivity | clear - hK4; lia].
Qed.

Definition symStartC : SymState :=
  mkSymState S0 []
    [srt001 (mkLF 0%Z (3 * Z.of_N ACoeff_N)%Z 0%Z (Z.of_N ACoeff_N - 1)%Z); srb0;
     srt001 (mkLF 0%Z (3 * Z.of_N b0Val_N)%Z 0%Z (Z.of_N b0Val_N - 1)%Z)]
    [2621; 2621; 2621; 2620; 2623; 2623; 2623; 2623; 2624; 2624; 2624;
     2625; 2625; 2625; 2626; 2626; 2627; 2628; 2629; 2629; 2627; 2625]%N.

Definition symEndC : SymState :=
  mkSymState S0 [slt110 (mkLF 0%Z (Z.of_N C3Val_N) (Z.of_N c373004_N) (Z.of_N D0Val_N)); slb1] [] [].

Definition symRun2083 (s : SymState) : option SymState :=
  optBind (symIterPow2 predC 11 s) (fun s1 =>
  optBind (symIterPow2 predC 5 s1) (fun s2 =>
  optBind (symIterPow2 predC 1 s2) (symIterPow2 predC 0))).

Lemma symRun2083_eq : symRun2083 symStartC = Some symEndC.
Proof. vm_compute. reflexivity. Qed.

Lemma ACoeff_ge_2_N : (2 <= ACoeff_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma b0Val_ge_16_N : (16 <= b0Val_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma b0Val_ge_2_N : (2 <= b0Val_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma a0Val_ge_2_N : (2 <= a0Val_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma D0Val_ge_1_N : (1 <= D0Val_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma C3Val_even_N : N.even C3Val_N = true. Proof. vm_compute. reflexivity. Qed.
Lemma D0Val_even_N : N.even D0Val_N = true. Proof. vm_compute. reflexivity. Qed.
Lemma c373004_even_N : N.even c373004_N = true. Proof. vm_compute. reflexivity. Qed.
Lemma m2630_ge_10_N : (10 <= m2630_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma m2630_even_N : N.even m2630_N = true. Proof. vm_compute. reflexivity. Qed.
Lemma c373004_bound_N : (2000 <= 9 * c373004_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma b0Val_mod4_N : (b0Val_N mod 4 = 0)%N. Proof. vm_compute. reflexivity. Qed.
Lemma a0Val_mod4_N : (a0Val_N mod 4 = 0)%N. Proof. vm_compute. reflexivity. Qed.
Lemma a0Val_ge_K_N : ((KVal_N + 5) * b0Val_N <= a0Val_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma a0Val_sub_K_N : (a0Val_N - KVal_N * b0Val_N = ACoeff_N)%N. Proof. vm_compute. reflexivity. Qed.
Lemma KVal_ge_4_N : (4 <= KVal_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma KVal_even_N : N.even KVal_N = true. Proof. vm_compute. reflexivity. Qed.
Lemma inv_c_lo1_N : (600 * p4_2630_N <= 9 * C3Val_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma inv_c_lo2_N : (600 * s4_2630_N + 200 + 2000 * m2630_N <= 9 * D0Val_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma inv_c_hi1_N : (9 * C3Val_N + 9 * c373004_N + 2000 <= 615 * p4_2630_N)%N. Proof. vm_compute. discriminate. Qed.
Lemma inv_c_hi2_N : (9 * D0Val_N + 2000 * m2630_N <= 615 * s4_2630_N + 205)%N. Proof. vm_compute. discriminate. Qed.

Lemma bridge_stageC_start (ac b0 : N) (vK : nat) :
  (2 <= ac)%N -> (16 <= b0)%N ->
  validSym 0 (sum4 vK) vK
    (mkSymState S0 []
      [srt001 (mkLF 0%Z (3 * Z.of_N ac)%Z 0%Z (Z.of_N ac - 1)%Z); srb0;
       srt001 (mkLF 0%Z (3 * Z.of_N b0)%Z 0%Z (Z.of_N b0 - 1)%Z)]
      [2621; 2621; 2621; 2620; 2623; 2623; 2623; 2623; 2624; 2624; 2624;
       2625; 2625; 2625; 2626; 2626; 2627; 2628; 2629; 2629; 2627; 2625]%N) /\
  evalSym 0 (sum4 vK) vK
    (mkSymState S0 []
      [srt001 (mkLF 0%Z (3 * Z.of_N ac)%Z 0%Z (Z.of_N ac - 1)%Z); srb0;
       srt001 (mkLF 0%Z (3 * Z.of_N b0)%Z 0%Z (Z.of_N b0 - 1)%Z)]
      [2621; 2621; 2621; 2620; 2623; 2623; 2623; 2623; 2624; 2624; 2624;
       2625; 2625; 2625; 2626; 2626; 2627; 2628; 2629; 2629; 2627; 2625]%N) =
  p60Cfg (pow4 vK * N.to_nat ac) (pow4 vK * N.to_nat b0).
Proof.
  intros hac hb0.
  pose proof (pow4_pos vK) as hp4.
  pose proof (sum4_spec vK) as hs4.
  split.
  - unfold validSym; cbn [sst_l sst_r validL validR].
    unfold evalLF; cbn [lf_aN lf_aQ lf_am lf_ac].
    split; [exact I | split; [nia | split; [nia | exact I]]].
  - unfold evalSym, p60Cfg; cbn [sst_hd sst_l sst_r exSL exSR].
    replace (evalLFNat 0 (sum4 vK) vK (mkLF 0%Z (3 * Z.of_N ac)%Z 0%Z (Z.of_N ac - 1)%Z))
      with (pow4 vK * N.to_nat ac - 1)
      by (unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; nia).
    replace (evalLFNat 0 (sum4 vK) vK (mkLF 0%Z (3 * Z.of_N b0)%Z 0%Z (Z.of_N b0 - 1)%Z))
      with (pow4 vK * N.to_nat b0 - 1)
      by (unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; nia).
    reflexivity.
Qed.

Lemma bridge_stageC_end (c3 c373 d0 : N) (vK : nat) :
  evalSym 0 (sum4 vK) vK
    (mkSymState S0 [slt110 (mkLF 0%Z (Z.of_N c3) (Z.of_N c373) (Z.of_N d0)); slb1] [] []) =
  attractorCfg (N.to_nat c3 * sum4 vK + N.to_nat c373 * vK + N.to_nat d0).
Proof.
  unfold evalSym, attractorCfg; cbn [sst_hd sst_l sst_r exSL exSR].
  replace (evalLFNat 0 (sum4 vK) vK (mkLF 0%Z (Z.of_N c3) (Z.of_N c373) (Z.of_N d0)))
    with (N.to_nat c3 * sum4 vK + N.to_nat c373 * vK + N.to_nat d0)
    by (unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; nia).
  reflexivity.
Qed.

Lemma symRun2083_sound {vN vQ vm : nat} (hP : ValidPred predC vN vQ vm) (s s' : SymState) :
  validSym vN vQ vm s -> symRun2083 s = Some s' ->
  validSym vN vQ vm s' /\ evalSym vN vQ vm s -->+ evalSym vN vQ vm s'.
Proof.
  intros hv0 H.
  unfold symRun2083 in H.
  destruct (symIterPow2 predC 11 s) as [s1 |] eqn:E1; [| discriminate].
  cbn [optBind] in H.
  destruct (symIterPow2 predC 5 s1) as [s2 |] eqn:E2; [| discriminate].
  cbn [optBind] in H.
  destruct (symIterPow2 predC 1 s2) as [s3 |] eqn:E3; [| discriminate].
  cbn [optBind] in H.
  destruct (symIterPow2_sound hP 11 s s1 hv0 E1) as [hv1 h1].
  destruct (symIterPow2_sound hP 5 s1 s2 hv1 E2) as [hv2 h2].
  destruct (symIterPow2_sound hP 1 s2 s3 hv2 E3) as [hv3 h3].
  destruct (symIterPow2_sound hP 0 s3 s' hv3 H) as [hv4 h4].
  exact (conj hv4 (ptrans h1 (ptrans h2 (ptrans h3 h4)))).
Qed.

Definition mkSymStartC (ac b0 : N) : SymState :=
  mkSymState S0 []
    [srt001 (mkLF 0%Z (3 * Z.of_N ac)%Z 0%Z (Z.of_N ac - 1)%Z); srb0;
     srt001 (mkLF 0%Z (3 * Z.of_N b0)%Z 0%Z (Z.of_N b0 - 1)%Z)]
    [2621; 2621; 2621; 2620; 2623; 2623; 2623; 2623; 2624; 2624; 2624;
     2625; 2625; 2625; 2626; 2626; 2627; 2628; 2629; 2629; 2627; 2625]%N.

Definition mkSymEndC (c3 c373 d0 : N) : SymState :=
  mkSymState S0 [slt110 (mkLF 0%Z (Z.of_N c3) (Z.of_N c373) (Z.of_N d0)); slb1] [] [].

Lemma bridge_stageC_reaches {vK : nat} (ac b0 c3 c373 d0 : N) :
  4 <= vK -> vK mod 2 = 0 ->
  (2 <= ac)%N -> (16 <= b0)%N ->
  symRun2083 (mkSymStartC ac b0) = Some (mkSymEndC c3 c373 d0) ->
  p60Cfg (pow4 vK * N.to_nat ac) (pow4 vK * N.to_nat b0) -->+
  attractorCfg (N.to_nat c3 * sum4 vK + N.to_nat c373 * vK + N.to_nat d0).
Proof.
  intros hK4 hKe hac hb0 Hrun.
  pose proof (validPredC hK4 hKe) as hP.
  destruct (bridge_stageC_start ac b0 vK hac hb0) as [hv0 hstart].
  pose proof (bridge_stageC_end c3 c373 d0 vK) as hend.
  destruct (symRun2083_sound hP (mkSymStartC ac b0) (mkSymEndC c3 c373 d0) hv0 Hrun) as [_ hall].
  unfold mkSymStartC in hall.
  unfold mkSymEndC in hall.
  rewrite hstart, hend in hall.
  exact hall.
Qed.

Lemma stageC_reaches {vK : nat} (hK4 : 4 <= vK) (hKe : vK mod 2 = 0) :
  p60Cfg (pow4 vK * N.to_nat ACoeff_N) (pow4 vK * N.to_nat b0Val_N) -->+
  attractorCfg (N.to_nat C3Val_N * sum4 vK + N.to_nat c373004_N * vK + N.to_nat D0Val_N).
Proof.
  exact (bridge_stageC_reaches ACoeff_N b0Val_N C3Val_N c373004_N D0Val_N
           hK4 hKe ACoeff_ge_2_N b0Val_ge_16_N symRun2083_eq).
Qed.

Lemma bridge_inv_stageC (p4 s4 m c3 c373 d0 : N) (vK : nat) :
  N.to_nat p4 = pow4 (N.to_nat m) ->
  N.to_nat s4 = sum4 (N.to_nat m) ->
  (10 <= m)%N ->
  N.even m = true ->
  N.even c3 = true ->
  N.even c373 = true ->
  N.even d0 = true ->
  (2000 <= 9 * c373)%N ->
  (600 * p4 <= 9 * c3)%N ->
  (600 * s4 + 200 + 2000 * m <= 9 * d0)%N ->
  (9 * c3 + 9 * c373 + 2000 <= 615 * p4)%N ->
  (9 * d0 + 2000 * m <= 615 * s4 + 205)%N ->
  vK mod 2 = 0 ->
  Inv (vK + N.to_nat m)
      (N.to_nat c3 * sum4 vK + N.to_nat c373 * vK + N.to_nat d0).
Proof.
  intros hp hs hm10 hme hc3e hc373e hd0e hc373b hlo1 hlo2 hhi1 hhi2 hKe.
  pose proof (sum4_ge_self vK) as hKs.
  pose proof (sum4_add vK (N.to_nat m)) as hs_add.
  rewrite <- hp, <- hs in hs_add.
  unfold Inv. rewrite hs_add.
  split; [clear - hm10; lia |].
  split; [apply N_even_mod2 in hme; clear - hKe hme; lia |].
  split.
  - apply N_even_mod2 in hc3e.
    apply N_even_mod2 in hc373e.
    apply N_even_mod2 in hd0e.
    clear - hc3e hc373e hd0e.
    set (kc3 := (c3 / 2)%N). set (kc373 := (c373 / 2)%N). set (kd0 := (d0 / 2)%N).
    assert (hc3_2 : N.to_nat c3 = 2 * N.to_nat kc3) by (clear - hc3e; unfold kc3; lia).
    assert (hc373_2 : N.to_nat c373 = 2 * N.to_nat kc373) by (clear - hc373e; unfold kc373; lia).
    assert (hd0_2 : N.to_nat d0 = 2 * N.to_nat kd0) by (clear - hd0e; unfold kd0; lia).
    rewrite hc3_2, hc373_2, hd0_2. clear. lia.
  - split.
    + clear - hc373b hlo1 hlo2. nia.
    + clear - hKs hhi1 hhi2. nia.
Qed.

Lemma inv_stageC {vK : nat} (hKe : vK mod 2 = 0) :
  Inv (vK + N.to_nat m2630_N)
      (N.to_nat C3Val_N * sum4 vK + N.to_nat c373004_N * vK + N.to_nat D0Val_N).
Proof.
  exact (bridge_inv_stageC p4_2630_N s4_2630_N m2630_N C3Val_N c373004_N D0Val_N vK
           (N_shiftl_1_pow4 m2630_N) (N_shiftl_1_s4 m2630_N)
           m2630_ge_10_N m2630_even_N C3Val_even_N c373004_even_N D0Val_even_N
           c373004_bound_N inv_c_lo1_N inv_c_lo2_N inv_c_hi1_N inv_c_hi2_N hKe).
Qed.

Lemma bridge_stageB (k a0 b0 ac : N) :
  (16 <= b0)%N ->
  (b0 mod 4 = 0)%N ->
  (a0 mod 4 = 0)%N ->
  ((k + 5) * b0 <= a0)%N ->
  (a0 - k * b0 = ac)%N ->
  p60Cfg (N.to_nat a0) (N.to_nat b0) -->*
  p60Cfg (pow4 (N.to_nat k) * N.to_nat ac) (pow4 (N.to_nat k) * N.to_nat b0).
Proof.
  intros hb16 hb4 ha4 hle hsub.
  assert (hb16' : 16 <= N.to_nat b0) by (clear - hb16; lia).
  assert (hb4' : N.to_nat b0 mod 4 = 0) by (clear - hb4; lia).
  assert (ha4' : N.to_nat a0 mod 4 = 0) by (clear - ha4; lia).
  assert (hle' : (N.to_nat k + 5) * N.to_nat b0 <= N.to_nat a0) by (clear - hle; nia).
  pose proof (period60_iter (N.to_nat k) (N.to_nat a0) (N.to_nat b0) hb16' hb4' ha4' hle') as hB.
  replace (N.to_nat a0 - N.to_nat k * N.to_nat b0) with (N.to_nat ac) in hB
    by (clear - hle hsub; nia).
  exact hB.
Qed.

Lemma bridge_KVal_props (k : N) :
  (4 <= k)%N -> N.even k = true -> 4 <= N.to_nat k /\ N.to_nat k mod 2 = 0.
Proof.
  intros hk4 hke. apply N_even_mod2 in hke. split; lia.
Qed.

Lemma from_t595860_in_attractor :
  exists cfg', p60Cfg (N.to_nat a0Val_N) (N.to_nat b0Val_N) -->* cfg' /\ InAttractor cfg'.
Proof.
  pose proof (bridge_stageB KVal_N a0Val_N b0Val_N ACoeff_N
                b0Val_ge_16_N b0Val_mod4_N a0Val_mod4_N a0Val_ge_K_N a0Val_sub_K_N) as hB.
  destruct (bridge_KVal_props KVal_N KVal_ge_4_N KVal_even_N) as [hK4 hKe].
  pose proof (pev (stageC_reaches hK4 hKe)) as hC.
  exists (attractorCfg (N.to_nat C3Val_N * sum4 (N.to_nat KVal_N) +
                        N.to_nat c373004_N * N.to_nat KVal_N + N.to_nat D0Val_N)).
  split.
  - exact (etrans hB hC).
  - exists (N.to_nat KVal_N + N.to_nat m2630_N),
           (N.to_nat C3Val_N * sum4 (N.to_nat KVal_N) +
            N.to_nat c373004_N * N.to_nat KVal_N + N.to_nat D0Val_N).
    exact (conj (inv_stageC hKe) eq_refl).
Qed.

(* Stage A: 595,860 Concrete Macro Steps from c0 to p60Cfg(a0Val, b0Val) *)

Definition runFast595860 (s : State) : option State :=
  optBind (iterPow2 19 s) (fun s1 =>
  optBind (iterPow2 16 s1) (fun s2 =>
  optBind (iterPow2 12 s2) (fun s3 =>
  optBind (iterPow2 10 s3) (fun s4 =>
  optBind (iterPow2 9 s4) (fun s5 =>
  optBind (iterPow2 8 s5) (fun s6 =>
  optBind (iterPow2 7 s6) (fun s7 =>
  optBind (iterPow2 4 s7) (iterPow2 2)))))))).

Lemma stageA_eq : runFast595860 startState = Some (p60StateN a0Val_N b0Val_N).
Proof. vm_compute. reflexivity. Qed.

Lemma runFast595860_sound (s s' : State) :
  runFast595860 s = Some s' -> encode s -->+ encode s'.
Proof.
  intros H.
  unfold runFast595860 in H.
  destruct (iterPow2 19 s) as [s1 |] eqn:E1; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 16 s1) as [s2 |] eqn:E2; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 12 s2) as [s3 |] eqn:E3; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 10 s3) as [s4 |] eqn:E4; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 9 s4) as [s5 |] eqn:E5; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 8 s5) as [s6 |] eqn:E6; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 7 s6) as [s7 |] eqn:E7; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 4 s7) as [s8 |] eqn:E8; [| discriminate].
  cbn [optBind] in H.
  exact (ptrans (iterPow2_sound 19 _ _ E1)
          (ptrans (iterPow2_sound 16 _ _ E2)
            (ptrans (iterPow2_sound 12 _ _ E3)
              (ptrans (iterPow2_sound 10 _ _ E4)
                (ptrans (iterPow2_sound 9 _ _ E5)
                  (ptrans (iterPow2_sound 8 _ _ E6)
                    (ptrans (iterPow2_sound 7 _ _ E7)
                      (ptrans (iterPow2_sound 4 _ _ E8)
                        (iterPow2_sound 2 _ _ H))))))))).
Qed.

Lemma start_reaches_p60 :
  encode startState -->+ encode (p60StateN a0Val_N b0Val_N).
Proof.
  exact (runFast595860_sound startState (p60StateN a0Val_N b0Val_N) stageA_eq).
Qed.

Lemma stageA_reaches_p60 : c0 -->* p60Cfg (N.to_nat a0Val_N) (N.to_nat b0Val_N).
Proof.
  rewrite <- (encode_p60StateN a0Val_N b0Val_N a0Val_ge_2_N b0Val_ge_2_N).
  exact (etrans init_reaches_start (pev start_reaches_p60)).
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  destruct from_t595860_in_attractor as [cfg' [hBC hIn]].
  eapply multistep_nonhalt; [exact (etrans stageA_reaches_p60 hBC) |].
  eapply (progress_nonhalt tm InAttractor); [exact attractor_closed | exact hIn].
Qed.

Print Assumptions nonhalt.
