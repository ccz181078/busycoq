(* 1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool List Lists.Streams Lia ZifyNat ZifyN ZifyBool NArith ZArith PeanoNat String.
Import ListNotations.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm : TM := TM_from_str "1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---".
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
  (l {{B}}> (S1 >> rep001 q r)) -->* (rep110 q l {{B}}> (S1 >> r)).
Proof.
  induction q as [| q IH]; intros l r.
  - apply evstep_refl.
  - cbn [rep001].
    assert (h1 : (l {{B}}> (S1 >> S0 >> S0 >> S1 >> rep001 q r)) -->*
                 ((S1 >> S1 >> S0 >> l) {{B}}> (S1 >> rep001 q r)))
      by fast_execute.
    pose proof (IH (S1 >> S1 >> S0 >> l) r) as h2.
    rewrite rep110_shift in h2.
    exact (etrans h1 h2).
Qed.

Lemma reach_splitL_lb : forall (k : nat) (l r : side),
  (rep110 (2 * k) l {{B}}> (S0 >> r)) -->* (l {{B}}> (S0 >> rep001 (2 * k) r)).
Proof.
  induction k as [| k IH]; intros l r.
  - cbn [Nat.mul rep110 rep001]. apply evstep_refl.
  - replace (2 * S k) with (2 + 2 * k) by lia.
    rewrite (rep110_add 2 (2 * k)), (rep001_add 2 (2 * k)).
    cbn [rep110].
    assert (h1 : ((S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> rep110 (2 * k) l) {{B}}> (S0 >> r)) -->*
                 (rep110 (2 * k) l {{B}}> (S0 >> S0 >> S0 >> S1 >> S0 >> S0 >> S1 >> r)))
      by fast_execute.
    pose proof (IH l (S0 >> S0 >> S1 >> S0 >> S0 >> S1 >> r)) as h2.
    rewrite !rep001_shift in h2.
    exact (etrans h1 h2).
Qed.

Lemma reach_R1_lb (l r : side) :
  (l {{B}}> (S1 >> S1 >> r)) -->+ (l {{B}}> (S0 >> S0 >> r)).
Proof. fast_start_progress. Qed.

Lemma reach_R2_lb (b3 : Sym) (l r : side) :
  (l {{B}}> (S1 >> S0 >> S0 >> b3 >> r)) -->+
  ((S1 >> S1 >> S0 >> l) {{B}}> (b3 >> r)).
Proof. destruct b3; fast_start_progress. Qed.

Lemma reach_R3_lb (l r : side) :
  (l {{B}}> (S1 >> S0 >> S1 >> S0 >> r)) -->+
  ((S0 >> l) {{B}}> (S1 >> S0 >> S0 >> r)).
Proof. fast_start_progress. Qed.

Lemma reach_L1_lb (l r : side) :
  ((S0 >> l) {{C}}> (S0 >> r)) -->+ ((S1 >> l) {{B}}> (S1 >> r)).
Proof. fast_start_progress. Qed.

Lemma reach_L2_lb (cb : Sym) (l r : side) :
  ((S1 >> S1 >> cb >> l) {{C}}> (S0 >> r)) -->+
  (l {{B}}> (cb >> S0 >> S0 >> S1 >> r)).
Proof. destruct cb; fast_start_progress. Qed.

Lemma reach_L3_lb (l r : side) :
  ((S1 >> S0 >> l) {{C}}> (S0 >> r)) -->+
  ((S1 >> S1 >> l) {{B}}> (S1 >> r)).
Proof. fast_start_progress. Qed.

(* Quadratic Era Contractions *)

Lemma era_drain_one (k : nat) (r : side) :
  (rep110 (2 * (k + 1)) (S1 >> S1 >> 0inf) {{B}}>
    (S0 >> S1 >> S0 >> S0 >> S1 >> r)) -->+
  (rep110 (2 * (k + 2)) (S1 >> S1 >> 0inf) {{B}}>
    (S0 >> S1 >> r)).
Proof.
  pose proof (reach_splitL_lb (k + 1) (S1 >> S1 >> 0inf) (S1 >> S0 >> S0 >> S1 >> r)) as hs1.
  assert (ht1 : ((S1 >> S1 >> 0inf) {{B}}>
                  (S0 >> rep001 (2 * (k + 1)) (S1 >> S0 >> S0 >> S1 >> r))) -->+
                ((S1 >> 0inf) {{B}}>
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
  assert (ht3 : ((S1 >> S1 >> S0 >> S1 >> 0inf) {{B}}>
                  (S0 >> rep001 (2 * (k + 1)) (S0 >> S0 >> S0 >> S1 >> r))) -->+
                ((S1 >> S1 >> 0inf) {{B}}>
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
  (rep110 (2 * (k + 1)) (S1 >> S1 >> 0inf) {{B}}>
    (S0 >> S1 >> rep001 (c_m1 + 1) r)) -->+
  (rep110 (2 * (k + 1 + (c_m1 + 1))) (S1 >> S1 >> 0inf) {{B}}>
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
  ((S0 >> S1 >> S1 >> S0 >> l) {{B}}>
    (S1 >> rep001 (2 * j) (S0 >> S0 >> S0 >> S1 >> r))) -->+
  ((S0 >> l) {{B}}>
    (S1 >> rep001 (2 * (j + 1)) (S0 >> r))).
Proof.
  set (L0 := S0 >> S1 >> S1 >> S0 >> l).
  pose proof (reach_splitR_lb (2 * j) L0 (S0 >> S0 >> S0 >> S1 >> r)) as hs1.
  pose proof (reach_R2_lb S0 (rep110 (2 * j) L0) (S1 >> r)) as ht1.
  rewrite <- (rep110_shift (2 * j) L0) in ht1.
  pose proof (reach_splitL_lb j (S1 >> S1 >> S0 >> L0) (S1 >> r)) as hs2.
  assert (ht2 : ((S1 >> S1 >> S0 >> L0) {{B}}> (S0 >> rep001 (2 * j) (S1 >> r))) -->+
                ((S1 >> S1 >> S1 >> S0 >> l) {{B}}> (S1 >> rep001 (2 * j + 1) (S1 >> r)))).
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
  assert (ht4 : ((S1 >> S1 >> S0 >> L1) {{B}}> (S0 >> rep001 (2 * j) (S0 >> r))) -->+
                ((S0 >> l) {{B}}> (S1 >> rep001 (2 * (j + 1)) (S0 >> r)))).
  { replace (2 * (j + 1)) with (2 + 2 * j) by lia.
    rewrite (rep001_add 2 (2 * j)).
    unfold L1. cbn [rep001]. fast_start_progress. }
  exact (ptrans (ps_trans (sp_trans hs1 ht1) hs2)
          (ptrans (ps_trans ht2 hs3)
            (ptrans (ps_trans ht3 hs4) ht4))).
Qed.

Lemma era_osc_iter : forall (n_m1 j : nat) (l r : side),
  ((S0 >> rep110 (n_m1 + 1) l) {{B}}>
    (S1 >> rep001 (2 * j) (S0 >> rep001 (n_m1 + 1) r))) -->+
  ((S0 >> l) {{B}}>
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
  ((S1 >> S0 >> S1 >> S1 >> S0 >> l) {{B}}>
    (S1 >> rep001 (2 * j) (S0 >> S0 >> S0 >> S1 >> r))) -->+
  ((S1 >> S0 >> l) {{B}}>
    (S1 >> rep001 (2 * (j + 1)) (S0 >> r))).
Proof.
  set (L0 := S1 >> S0 >> S1 >> S1 >> S0 >> l).
  pose proof (reach_splitR_lb (2 * j) L0 (S0 >> S0 >> S0 >> S1 >> r)) as hs1.
  pose proof (reach_R2_lb S0 (rep110 (2 * j) L0) (S1 >> r)) as ht1.
  rewrite <- (rep110_shift (2 * j) L0) in ht1.
  pose proof (reach_splitL_lb j (S1 >> S1 >> S0 >> L0) (S1 >> r)) as hs2.
  assert (ht2 : ((S1 >> S1 >> S0 >> L0) {{B}}> (S0 >> rep001 (2 * j) (S1 >> r))) -->+
                ((S1 >> S1 >> S1 >> S1 >> S0 >> l) {{B}}> (S1 >> rep001 (2 * j + 1) (S1 >> r)))).
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
  assert (ht4 : ((S1 >> S1 >> S0 >> L1) {{B}}> (S0 >> rep001 (2 * j) (S0 >> r))) -->+
                ((S1 >> S0 >> l) {{B}}> (S1 >> rep001 (2 * (j + 1)) (S0 >> r)))).
  { replace (2 * (j + 1)) with (2 + 2 * j) by lia.
    rewrite (rep001_add 2 (2 * j)).
    unfold L1. cbn [rep001]. fast_start_progress. }
  exact (ptrans (ps_trans (sp_trans hs1 ht1) hs2)
          (ptrans (ps_trans ht2 hs3)
            (ptrans (ps_trans ht3 hs4) ht4))).
Qed.

Lemma era_osc10_iter : forall (n_m1 j : nat) (l r : side),
  ((S1 >> S0 >> rep110 (n_m1 + 1) l) {{B}}>
    (S1 >> rep001 (2 * j) (S0 >> rep001 (n_m1 + 1) r))) -->+
  ((S1 >> S0 >> l) {{B}}>
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

(* Exponential 4^m Arithmetic & Super-Era Cascade *)

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

Lemma super4x_pre1 (r : side) :
  (0inf {{B}}> (S0 >> rep001 3 r)) -->+
  (0inf {{B}}> (S1 >> rep001 4 (S0 >> r))).
Proof.
  cbn [rep001]. fast_start_progress.
Qed.

Lemma super4x_pre2 (r : side) :
  (0inf {{B}}> (S1 >> rep001 4 (S0 >> rep001 2 r))) -->+
  (rep110 6 (S1 >> S1 >> 0inf) {{B}}> (S0 >> S1 >> r)).
Proof.
  cbn [rep001 rep110]. fast_start_progress.
Qed.

Lemma super4x_partA (a d : nat) (r : side) :
  (0inf {{B}}> (S0 >> rep001 (2 * (a + 3)) (S0 >> rep001 (2 * (2 * (a + 3)) + 1 + d) r))) -->+
  (rep110 (2 * (2 * a + 5)) (S1 >> S1 >> 0inf) {{B}}>
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
  assert (ht19 : ((S1 >> S1 >> 0inf) {{B}}> (S0 >> rep001 (2 * (2 * a + 4)) (S1 >> r0))) -->+
                 ((S1 >> 0inf) {{B}}> (S1 >> rep001 (4 * a + 9) (S1 >> r0)))).
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
  assert (ht21 : ((S1 >> S1 >> S0 >> S1 >> 0inf) {{B}}> (S0 >> rep001 (2 * (2 * a + 4)) (S0 >> r0))) -->+
                 ((S1 >> S1 >> 0inf) {{B}}> (S1 >> rep001 (4 * a + 9) (S0 >> r0)))).
  { replace (4 * a + 9) with (1 + 2 * (2 * a + 4)) by lia.
    rewrite (rep001_add 1 (2 * (2 * a + 4))).
    cbn [rep001]. fast_start_progress. }
  assert (hr0_eq : S0 >> r0 = S0 >> S0 >> S0 >> S0 >> S1 >> rep001 (4 * a + 12 + d) r).
  { unfold r0.
    replace (2 * (2 * (a + 3)) + 1 + d) with (1 + (4 * a + 12 + d)) by lia.
    rewrite (rep001_add 1 (4 * a + 12 + d)). reflexivity. }
  assert (hs22 : ((S1 >> S1 >> 0inf) {{B}}> (S1 >> rep001 (4 * a + 9) (S0 >> r0))) -->*
                 (rep110 (4 * a + 9) (S1 >> S1 >> 0inf) {{B}}>
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
  (rep110 (2 * (2 * a + 5)) (S1 >> S1 >> 0inf) {{B}}>
    (S0 >> S0 >> S1 >> rep001 (4 * a + 12 + d) r)) -->*
  (0inf {{B}}> (S0 >> rep001 (4 * (2 * (a + 3))) (S0 >> rep001 d r))).
Proof.
  set (r22 := S0 >> S1 >> rep001 (4 * a + 12 + d) r).
  pose proof (reach_splitL_lb (2 * a + 5) (S1 >> S1 >> 0inf) r22) as hs23.
  assert (ht23 : ((S1 >> S1 >> 0inf) {{B}}> (S0 >> rep001 (2 * (2 * a + 5)) r22)) -->*
                 ((S1 >> 0inf) {{B}}> (S1 >> rep001 (4 * a + 11) r22))).
  { replace (4 * a + 11) with (1 + 2 * (2 * a + 5)) by lia.
    rewrite (rep001_add 1 (2 * (2 * a + 5))).
    cbn [rep001]. fast_execute. }
  assert (hr24_eq : r22 = S0 >> S1 >> S0 >> S0 >> S1 >> rep001 (4 * a + 11 + d) r).
  { unfold r22.
    replace (4 * a + 12 + d) with (1 + (4 * a + 11 + d)) by lia.
    rewrite (rep001_add 1 (4 * a + 11 + d)). reflexivity. }
  assert (hs24 : ((S1 >> 0inf) {{B}}> (S1 >> rep001 (4 * a + 11) r22)) -->*
                 (rep110 (4 * a + 11) (S1 >> 0inf) {{B}}>
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
  assert (hs26 : ((S0 >> S1 >> 0inf) {{B}}>
                    (S1 >> rep001 (2 * (4 * a + 11)) (S0 >> rep001 (1 + d) r))) -->*
                 (rep110 (2 * (4 * a + 11)) (S0 >> S1 >> 0inf) {{B}}>
                    (S1 >> S0 >> S0 >> S0 >> S1 >> rep001 d r))).
  { rewrite hr26_eq.
    exact (reach_splitR_lb (2 * (4 * a + 11)) (S0 >> S1 >> 0inf) _). }
  pose proof (pev (reach_R2_lb S0 (rep110 (2 * (4 * a + 11)) (S0 >> S1 >> 0inf))
                    (S1 >> rep001 d r))) as ht26.
  rewrite <- (rep110_shift (2 * (4 * a + 11))) in ht26.
  pose proof (reach_splitL_lb (4 * a + 11)
                (S1 >> S1 >> S0 >> S0 >> S1 >> 0inf) (S1 >> rep001 d r)) as hs27.
  assert (ht27 : ((S1 >> S1 >> S0 >> S0 >> S1 >> 0inf) {{B}}>
                    (S0 >> rep001 (2 * (4 * a + 11)) (S1 >> rep001 d r))) -->*
                 ((S1 >> S1 >> 0inf) {{B}}>
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
  assert (ht29 : ((S1 >> S1 >> S0 >> S1 >> S1 >> 0inf) {{B}}>
                    (S0 >> rep001 (2 * (4 * a + 11)) (S0 >> rep001 d r))) -->*
                 (0inf {{B}}> (S0 >> rep001 (4 * (2 * (a + 3))) (S0 >> rep001 d r)))).
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
  (0inf {{B}}> (S0 >> rep001 (2 * (a + 3)) (S0 >> rep001 (2 * (2 * (a + 3)) + 1 + d) r))) -->+
  (0inf {{B}}> (S0 >> rep001 (4 * (2 * (a + 3))) (S0 >> rep001 d r))).
Proof.
  exact (ps_trans (super4x_partA a d r) (super4x_partB a d r)).
Qed.

Lemma super4x_iter : forall (m a d : nat) (r : side),
  (0inf {{B}}> (S0 >> rep001 (2 * (a + 3))
    (S0 >> rep001 (2 * (2 * (a + 3)) * sum4 m + m + d) r))) -->*
  (0inf {{B}}> (S0 >> rep001 ((2 * (a + 3)) * pow4 m) (S0 >> rep001 d r))).
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
  (0inf {{B}}> (S0 >> rep001 (2 * (a + 3))
    (S0 >> rep001 (2 * (2 * (a + 3)) * sum4 m + m + d) r))) -->+
  (0inf {{B}}> (S0 >> rep001 ((2 * (a + 3)) * pow4 m) (S0 >> rep001 d r))).
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
(* Layer 2: Fast Concrete Macro Executor Over Binary N (c0 -->* C(N_init))    *)
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
  (exL (st_l s)) {{B}}> ((st_hd s) >> exR (st_r s)).

Definition attractorCfg (n : nat) : Q * tape :=
  (rep110 n (S1 >> 0inf)) {{B}}> (S0 >> 0inf).

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
      let p := (m1 / 2)%N in
      let r1 := pushR001 (2 * p + 1)%N r in
      if (m1 mod 2 =? 0)%N then splitLChunk tl r1
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

Definition okSuper4x (vA vB m : N) : bool :=
  (0 <? m)%N && (2 * vA * ((4 ^ m - 1) / 3) + m <? vB)%N.

Fixpoint bsearchM (vA vB : N) (fuel : nat) (lo hi : N) : N :=
  match fuel with
  | 0 => lo
  | S fuel' =>
    if (hi <=? lo + 1)%N then lo
    else
      let mid := ((lo + hi) / 2)%N in
      if okSuper4x vA vB mid then bsearchM vA vB fuel' mid hi
      else bsearchM vA vB fuel' lo mid
  end.

Definition findMaxM (vA vB : N) : N :=
  if okSuper4x vA vB 1%N then bsearchM vA vB 9 1%N 512%N else 0%N.

Definition trySuper4x (hd : Sym) (l : list LChunk) (r : list RChunk) : option State :=
  match hd, l, r with
  | S0, [], rt001 a_m1 :: rb0_c :: rt001 b_m1 :: rtail =>
    if (5 <=? a_m1)%N && (a_m1 mod 2 =? 1)%N then
      let vA := (a_m1 + 1)%N in
      let vB := (b_m1 + 1)%N in
      let m := findMaxM vA vB in
      if (0 <? m)%N then
        let p4 := (4 ^ m)%N in
        let s4 := ((p4 - 1) / 3)%N in
        let dr := (2 * vA * s4 + m)%N in
        if (dr + 1 <=? vB)%N then
          Some (mkState S0 [] (rt001 (vA * p4 - 1)%N :: rb0_c :: rt001 (vB - (dr + 1))%N :: rtail))
        else None
      else None
    else None
  | _, _, _ => None
  end.

Definition tryEraDrain (hd : Sym) (l : list LChunk) (r : list RChunk) : option State :=
  match hd, l, r with
  | S0, [lt110 m_val; lb1_c; lb1_c], rb1_c :: rt001 c_m1 :: rtail =>
    if (1 <=? m_val)%N && ((m_val - 1) mod 2 =? 0)%N then
      Some (mkState S0 [lt110 (m_val + 2 * (c_m1 + 1))%N; lb1_c; lb1_c] (pushR1 rtail))
    else None
  | _, _, _ => None
  end.

Definition tryEraOscR (r : list RChunk) : option (N * N * list RChunk) :=
  match r with
  | rb0_c :: rt001 c_m1 :: rtail => Some (0%N, c_m1, rtail)
  | rt001 m_val :: rb0_c :: rt001 c_m1 :: rtail =>
    if (1 <=? m_val)%N && ((m_val - 1) mod 2 =? 0)%N then
      Some (((m_val - 1) / 2 + 1)%N, c_m1, rtail)
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
      let r_new := pushR001 (2 * j + 2 * n_m1 + 1)%N (pushR0 (pushRN001 (c_m1 - n_m1)%N rtail)) in
      Some (mkState S1 l_new r_new)
    | None => None
    end
  | S1, lb1_c :: lb0_c :: lt110 a_m1 :: ltail =>
    match tryEraOscR r with
    | Some (j, c_m1, rtail) =>
      let n_m1 := N.min a_m1 c_m1 in
      let l_new := pushL1 (pushL0 (pushLN110 (a_m1 - n_m1)%N ltail)) in
      let r_new := pushR001 (2 * j + 2 * n_m1 + 1)%N (pushR0 (pushRN001 (c_m1 - n_m1)%N rtail)) in
      Some (mkState S1 l_new r_new)
    | None => None
    end
  | _, _ => None
  end.

Definition stepBase (hd : Sym) (l : list LChunk) (r : list RChunk) : option State :=
  match hd with
  | S1 =>
    let '(l1, r_in) := splitRChunk l r in
    let '(b1, r1) := popR r_in in
    match b1 with
    | S1 => Some (mkState S0 l1 (pushR0 r1))
    | S0 =>
      let '(b2, r2) := popR r1 in
      match b2 with
      | S0 =>
        let '(b3, r3) := popR r2 in
        Some (mkState b3 (pushL110 0%N l1) r3)
      | S1 =>
        let '(b3, r3) := popR r2 in
        match b3 with
        | S0 => Some (mkState S1 (pushL0 l1) (pushR0 (pushR0 r3)))
        | S1 => None
        end
      end
    end
  | S0 =>
    let '(l1, r1) := splitLChunk l r in
    let '(l_after, r_rem) := stripOnesL l1 (pushR1 r1) in
    let '(e, e_rem) := popL l_after in
    match e with
    | S0 => Some (mkState S1 (pushL1 e_rem) r_rem)
    | S1 =>
      let '(ab, a_rem) := popL e_rem in
      match ab with
      | S1 =>
        let '(cb, c_rem) := popL a_rem in
        Some (mkState cb c_rem (pushR001 0%N r_rem))
      | S0 => Some (mkState S1 (pushL1 (pushL1 a_rem)) r_rem)
      end
    end
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
  (exL l {{B}}> (S1 >> exR r)) -->*
  (exL (fst (splitRChunk l r)) {{B}}> (S1 >> exR (snd (splitRChunk l r)))).
Proof.
  induction r as [| [| | m] r IH]; intros l; try apply evstep_refl.
  cbn [splitRChunk exR].
  pose proof (reach_splitR_lb (N.to_nat m + 1) (exL l) (exR r)) as h1.
  rewrite <- (exL_pushL110 m l) in h1.
  exact (etrans h1 (IH (pushL110 m l))).
Qed.

Lemma splitLChunk_ok : forall (l : list LChunk) (r : list RChunk),
  (exL l {{B}}> (S0 >> exR r)) -->*
  (exL (fst (splitLChunk l r)) {{B}}> (S0 >> exR (snd (splitLChunk l r)))).
Proof.
  induction l as [| [| | m] tl IH]; intros r; try apply evstep_refl.
  cbn [splitLChunk].
  destruct (N.eqb_spec m 0%N) as [-> | hne]; [apply evstep_refl |].
  set (m1 := (m - 1)%N).
  set (p := (m1 / 2)%N).
  set (r1 := pushR001 (2 * p + 1)%N r).
  destruct (N.eqb_spec (m1 mod 2)%N 0%N) as [hev | hodd].
  - cbn [exL].
    replace (N.to_nat m + 1) with (2 * (N.to_nat p + 1)) by (unfold p, m1 in *; lia).
    pose proof (reach_splitL_lb (N.to_nat p + 1) (exL tl) (exR r)) as h1.
    assert (hr_eq : rep001 (2 * (N.to_nat p + 1)) (exR r) = exR r1).
    { unfold r1. rewrite exR_pushR001. f_equal. lia. }
    rewrite hr_eq in h1.
    exact (etrans h1 (IH r1)).
  - cbn [fst snd exL].
    replace (N.to_nat m + 1) with (2 * (N.to_nat p + 1) + 1) by (unfold p, m1 in *; lia).
    rewrite (rep110_add (2 * (N.to_nat p + 1)) 1).
    pose proof (reach_splitL_lb (N.to_nat p + 1) (rep110 1 (exL tl)) (exR r)) as h1.
    assert (hr_eq : rep001 (2 * (N.to_nat p + 1)) (exR r) = exR r1).
    { unfold r1. rewrite exR_pushR001. f_equal. lia. }
    rewrite hr_eq in h1.
    exact h1.
Qed.

Lemma stripOnesC_ok : forall (l : list LChunk) (r : list RChunk),
  (exL l <{{C}} exR r) -->*
  (exL (fst (stripOnesL l r)) {{C}}> (S0 >> exR (snd (stripOnesL l r)))).
Proof.
  induction l as [| [| | m] tl IH]; intros r.
  - cbn [stripOnesL fst snd exL]. apply evstep_refl.
  - cbn [stripOnesL fst snd exL]. apply evstep_refl.
  - cbn [stripOnesL exL].
    assert (h1 : ((S1 >> exL tl) <{{C}} exR r) -->* (exL tl <{{C}} exR (pushR0 r))).
    { rewrite exR_pushR0. fast_execute. }
    exact (etrans h1 (IH (pushR0 r))).
  - cbn [stripOnesL].
    destruct (N.eqb_spec m 0%N) as [-> | hne].
    + cbn [fst snd exL rep110]. rewrite !exR_pushR0. fast_execute.
    + cbn [fst snd exL].
      replace (N.to_nat m + 1) with (1 + (N.to_nat (m - 1)%N + 1)) by lia.
      rewrite (rep110_add 1). cbn [rep110]. rewrite !exR_pushR0. fast_execute.
Qed.

Lemma trySuper4x_some (hd : Sym) (l : list LChunk) (r : list RChunk) (s' : State) :
  trySuper4x hd l r = Some s' -> encode (mkState hd l r) -->+ encode s'.
Proof.
  unfold trySuper4x.
  destruct hd as [|]; [| discriminate].
  destruct l as [| ? ?]; [| discriminate].
  destruct r as [| [| | a_m1] [| [| | ?] [| [| | b_m1] rtail]]]; try discriminate.
  destruct (((5 <=? a_m1)%N && (a_m1 mod 2 =? 1)%N)) eqn:hcond; [| discriminate].
  rewrite Bool.andb_true_iff, N.leb_le, N.eqb_eq in hcond.
  destruct hcond as [ha5 haodd].
  set (vA := (a_m1 + 1)%N).
  set (vB := (b_m1 + 1)%N).
  set (m := findMaxM vA vB).
  destruct (N.ltb_spec 0%N m) as [hm | _]; [| discriminate].
  set (p4 := (4 ^ m)%N).
  set (s4 := ((p4 - 1) / 3)%N).
  set (dr := (2 * vA * s4 + m)%N).
  destruct (N.leb_spec (dr + 1)%N vB) as [hB | _]; [| discriminate].
  intros H; apply some_inj in H; subst s'.
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
  destruct (((1 <=? m_val)%N && ((m_val - 1) mod 2 =? 0)%N)) eqn:hcond; [| discriminate].
  rewrite Bool.andb_true_iff, N.leb_le, N.eqb_eq in hcond.
  destruct hcond as [hm1 hmev].
  intros H; apply some_inj in H; subst s'.
  unfold encode, pushR1; cbn [st_hd st_l st_r exL exR].
  set (k := N.to_nat ((m_val - 1) / 2)%N).
  set (cm1 := N.to_nat c_m1).
  replace (N.to_nat m_val + 1) with (2 * (k + 1)) by (clear - hm1 hmev; unfold k; lia).
  replace (N.to_nat c_m1 + 1) with (cm1 + 1) by (unfold cm1; lia).
  replace (N.to_nat (m_val + 2 * (c_m1 + 1))%N + 1) with (2 * (k + 1 + (cm1 + 1)))
    by (clear - hm1 hmev; unfold k, cm1; lia).
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
    destruct (((1 <=? m_val)%N && ((m_val - 1) mod 2 =? 0)%N)) eqn:hcond; [| discriminate].
    rewrite Bool.andb_true_iff, N.leb_le, N.eqb_eq in hcond.
    intros H; apply some_inj in H; inversion H; subst; clear H.
    cbn [exR]. f_equal. lia.
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
    replace (N.to_nat (2 * j + 2 * n_m1 + 1)%N + 1) with (2 * (N.to_nat j + (N.to_nat n_m1 + 1)))
      by (clear; lia).
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
    replace (N.to_nat (2 * j + 2 * n_m1 + 1)%N + 1) with (2 * (N.to_nat j + (N.to_nat n_m1 + 1)))
      by (clear; lia).
    rewrite (rep110_add (N.to_nat n_m1 + 1)), (rep001_add (N.to_nat n_m1 + 1)).
    exact (era_osc10_iter (N.to_nat n_m1) (N.to_nat j)
            (rep110 (N.to_nat (a_m1 - n_m1)%N) (exL ltail))
            (rep001 (N.to_nat (c_m1 - n_m1)%N) (exR rtail))).
Qed.

Lemma stepBase_some (hd : Sym) (l : list LChunk) (r : list RChunk) (s' : State) :
  stepBase hd l r = Some s' -> encode (mkState hd l r) -->+ encode s'.
Proof.
  unfold stepBase.
  destruct hd as [|].
  - pose proof (splitLChunk_ok l r) as hsw.
    destruct (splitLChunk l r) as [l1 r1]; cbn [fst snd] in hsw.
    assert (hb0 : (exL l1 {{B}}> (S0 >> exR r1)) -->* (exL l1 <{{C}} exR (pushR1 r1))).
    { cbn [pushR1 exR]. apply evstep_one. apply @step_left. reflexivity. }
    pose proof (stripOnesC_ok l1 (pushR1 r1)) as hones.
    destruct (stripOnesL l1 (pushR1 r1)) as [l_after r_rem]; cbn [fst snd] in hones.
    pose proof (etrans (etrans hsw hb0) hones) as hpre.
    pose proof (popL_ok l_after) as hpe.
    destruct (popL l_after) as [e e_rem]; cbn [fst snd] in hpe.
    destruct e as [|].
    + intros [= <-].
      unfold encode; cbn [st_hd st_l st_r].
      rewrite hpe in hpre. rewrite exL_pushL1.
      exact (sp_trans hpre (reach_L1_lb (exL e_rem) (exR r_rem))).
    + pose proof (popL_ok e_rem) as hpa.
      destruct (popL e_rem) as [ab a_rem]; cbn [fst snd] in hpa.
      destruct ab as [|].
      * intros [= <-].
        unfold encode; cbn [st_hd st_l st_r].
        rewrite hpe, hpa in hpre. rewrite !exL_pushL1.
        exact (sp_trans hpre (reach_L3_lb (exL a_rem) (exR r_rem))).
      * pose proof (popL_ok a_rem) as hpc.
        destruct (popL a_rem) as [cb c_rem]; cbn [fst snd] in hpc.
        intros [= <-].
        unfold encode; cbn [st_hd st_l st_r].
        rewrite hpe, hpa, hpc in hpre. rewrite exR_pushR001.
        cbn [N.to_nat Nat.add rep001].
        exact (sp_trans hpre (reach_L2_lb cb (exL c_rem) (exR r_rem))).
  - pose proof (splitRChunk_ok r l) as hsw.
    destruct (splitRChunk l r) as [l1 r_in]; cbn [fst snd] in hsw.
    pose proof (popR_ok r_in) as hp1.
    destruct (popR r_in) as [b1 r1]; cbn [fst snd] in hp1.
    destruct b1 as [|].
    + pose proof (popR_ok r1) as hp2.
      destruct (popR r1) as [b2 r2]; cbn [fst snd] in hp2.
      destruct b2 as [|].
      * pose proof (popR_ok r2) as hp3.
        destruct (popR r2) as [b3 r3]; cbn [fst snd] in hp3.
        intros [= <-].
        unfold encode; cbn [st_hd st_l st_r].
        rewrite hp1, hp2, hp3 in hsw. rewrite exL_pushL110.
        cbn [N.to_nat Nat.add rep110].
        exact (sp_trans hsw (reach_R2_lb b3 (exL l1) (exR r3))).
      * pose proof (popR_ok r2) as hp3.
        destruct (popR r2) as [b3 r3]; cbn [fst snd] in hp3.
        destruct b3 as [|]; [| discriminate].
        intros [= <-].
        unfold encode; cbn [st_hd st_l st_r].
        rewrite hp1, hp2, hp3 in hsw. rewrite exL_pushL0, !exR_pushR0.
        exact (sp_trans hsw (reach_R3_lb (exL l1) (exR r3))).
    + intros [= <-].
      unfold encode; cbn [st_hd st_l st_r].
      rewrite hp1 in hsw. rewrite exR_pushR0.
      exact (sp_trans hsw (reach_R1_lb (exL l1) (exR r1))).
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

Definition startState : State := mkState S0 [lb1_c] [].

Definition N_init : N :=
  168916542770708232164041355802806696743472136660680390606743144800220774608018174794%N.

Definition attractorStateN (vN : N) : State :=
  mkState S0 [lt110 (vN - 1)%N; lb1_c] [].

Definition runFast17205 (s : State) : option State :=
  optBind
    (optBind
      (optBind
        (optBind
          (optBind (iterPow2 14 s) (iterPow2 9))
          (iterPow2 8))
        (iterPow2 5))
      (iterPow2 4))
    (fun x => optBind (iterPow2 2 x) (iterPow2 0)).

Lemma init_reaches_start : c0 -->* encode startState.
Proof.
  unfold c0, tape0, encode, startState; cbn [st_hd st_l st_r exL exR].
  fast_execute.
Qed.

Lemma start_reaches_N0_eq :
  runFast17205 startState = Some (attractorStateN N_init).
Proof. vm_compute. reflexivity. Qed.

Lemma start_reaches_N0 :
  encode startState -->+ encode (attractorStateN N_init).
Proof.
  pose proof start_reaches_N0_eq as H.
  unfold runFast17205 in H.
  destruct (iterPow2 14 startState) as [s1 |] eqn:E1; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 9 s1) as [s2 |] eqn:E2; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 8 s2) as [s3 |] eqn:E3; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 5 s3) as [s4 |] eqn:E4; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 4 s4) as [s5 |] eqn:E5; [| discriminate].
  cbn [optBind] in H.
  destruct (iterPow2 2 s5) as [s6 |] eqn:E6; [| discriminate].
  cbn [optBind] in H.
  exact (ptrans (iterPow2_sound 14 _ _ E1)
          (ptrans (iterPow2_sound 9 _ _ E2)
            (ptrans (iterPow2_sound 8 _ _ E3)
              (ptrans (iterPow2_sound 5 _ _ E4)
                (ptrans (iterPow2_sound 4 _ _ E5)
                  (ptrans (iterPow2_sound 2 _ _ E6)
                    (iterPow2_sound 0 _ _ H))))))).
Qed.

Lemma encode_attractorStateN (vN : N) :
  (1 <= vN)%N -> encode (attractorStateN vN) = attractorCfg (N.to_nat vN).
Proof.
  intros hv.
  unfold encode, attractorStateN, attractorCfg; cbn [st_hd st_l st_r exL exR].
  replace (N.to_nat (vN - 1)%N + 1) with (N.to_nat vN) by lia.
  reflexivity.
Qed.

Lemma N_init_pos : (1 <= N_init)%N.
Proof. vm_compute. discriminate. Qed.

Lemma init_reaches_N0 : c0 -->* attractorCfg (N.to_nat N_init).
Proof.
  rewrite <- (encode_attractorStateN N_init N_init_pos).
  exact (etrans init_reaches_start (pev start_reaches_N0)).
Qed.

(* ========================================================================== *)
(* Layer 3: Symbolic 642-Step Period Closure on the Exponential Attractor     *)
(* ========================================================================== *)

Definition Inv (m vn : nat) : Prop :=
  10 <= m /\ m mod 2 = 0 /\ vn mod 2 = 0 /\
  600 * sum4 m + 200 + 2000 * m <= 9 * vn /\
  9 * vn + 2000 * m <= 615 * sum4 m + 205.

Definition s4_N (m : N) : N := ((4 ^ m - 1) / 3)%N.

Definition inv_N (m vN : N) : bool :=
  (10 <=? m)%N && (m mod 2 =? 0)%N && (vN mod 2 =? 0)%N &&
  (600 * s4_N m + 200 + 2000 * m <=? 9 * vN)%N &&
  (9 * vN + 2000 * m <=? 615 * s4_N m + 205)%N.

Lemma inv_N_sound (m vN : N) :
  inv_N m vN = true -> Inv (N.to_nat m) (N.to_nat vN).
Proof.
  unfold inv_N, s4_N, Inv.
  rewrite !Bool.andb_true_iff, !N.leb_le, !N.eqb_eq.
  pose proof (s4_N_to_nat m) as hs4.
  lia.
Qed.

Lemma inv_N_init : inv_N 136%N N_init = true.
Proof. vm_compute. reflexivity. Qed.

Lemma inv_init_N0 : Inv 136 (N.to_nat N_init).
Proof.
  change 136 with (N.to_nat 136%N).
  exact (inv_N_sound 136%N N_init inv_N_init).
Qed.

Lemma inv_step {m vn : nat} (h : Inv m vn) :
  Inv (m + 4) (256 * vn + 54 - 180 * m).
Proof.
  destruct h as [hm10 [hme [hNe [hlo hhi]]]].
  pose proof (sum4_lower_Z m hm10) as hql.
  assert (hs4 : sum4 (m + 4) = 256 * sum4 m + 85).
  { rewrite (sum4_add m 4). cbn [pow4 sum4]. lia. }
  unfold Inv. rewrite hs4.
  repeat split; lia.
Qed.

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
  mkLF (2 * lf_aN x)%Z (2 * lf_aQ x)%Z (2 * lf_am x)%Z (2 * lf_ac x)%Z.

Definition evalLF (m vn : nat) (f : LinForm) : Z :=
  (lf_aN f * Z.of_nat vn + lf_aQ f * Z.of_nat (sum4 m) + lf_am f * Z.of_nat m + lf_ac f)%Z.

Definition evalLFNat (m vn : nat) (f : LinForm) : nat :=
  Z.to_nat (evalLF m vn f).

Definition isNonnegLF (f : LinForm) : bool :=
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

Definition isPosLF (f : LinForm) : bool := isNonnegLF (lfSub f (lfConst 1%Z)).
Definition isEvenLF (f : LinForm) : bool := ((lf_aQ f + lf_ac f) mod 2 =? 0)%Z.

Lemma evalLF_const (m vn : nat) (c : Z) : evalLF m vn (lfConst c) = c.
Proof. unfold evalLF, lfConst; cbn [lf_aN lf_aQ lf_am lf_ac]. lia. Qed.

Lemma evalLF_add (m vn : nat) (x y : LinForm) :
  evalLF m vn (lfAdd x y) = (evalLF m vn x + evalLF m vn y)%Z.
Proof. unfold evalLF, lfAdd; cbn [lf_aN lf_aQ lf_am lf_ac]. nia. Qed.

Lemma evalLF_sub (m vn : nat) (x y : LinForm) :
  evalLF m vn (lfSub x y) = (evalLF m vn x - evalLF m vn y)%Z.
Proof. unfold evalLF, lfSub; cbn [lf_aN lf_aQ lf_am lf_ac]. nia. Qed.

Lemma evalLF_scale2 (m vn : nat) (x : LinForm) :
  evalLF m vn (lfScale2 x) = (2 * evalLF m vn x)%Z.
Proof. unfold evalLF, lfScale2; cbn [lf_aN lf_aQ lf_am lf_ac]. nia. Qed.

Lemma isNonnegLF_sound {m vn : nat} (hinv : Inv m vn) (f : LinForm) :
  isNonnegLF f = true -> (0 <= evalLF m vn f)%Z.
Proof.
  destruct hinv as [hm10 [_ [_ [hlo hhi]]]].
  pose proof (sum4_lower_Z m hm10) as hQ_low.
  assert (hfinish : forall cQ cm cc : Z,
    (cQ * Z.of_nat (sum4 m) + cm * Z.of_nat m + cc <= 9 * evalLF m vn f)%Z ->
    (if (cQ <? 0)%Z then false
     else if (cQ =? 0)%Z then (0 <=? cm)%Z && (0 <=? cm * 10 + cc)%Z
     else
       let mc := (cQ * 15000 + cm)%Z in
       let kc := (cQ * 150000 + cc)%Z in
       (0 <=? mc)%Z && (0 <=? mc * 10 + kc)%Z) = true ->
    (0 <= evalLF m vn f)%Z).
  { intros cQ cm cc hbound hchk.
    destruct (Z.ltb_spec cQ 0%Z) as [hneg | hnn]; [discriminate |].
    destruct (Z.eqb_spec cQ 0%Z) as [-> | hnz].
    - rewrite Bool.andb_true_iff, !Z.leb_le in hchk. clear - hm10 hbound hchk. nia.
    - cbv zeta in hchk. rewrite Bool.andb_true_iff, !Z.leb_le in hchk.
      clear - hm10 hQ_low hnn hbound hchk. nia. }
  unfold isNonnegLF.
  destruct (Z.leb_spec 0%Z (lf_aN f)) as [ha | ha].
  - intros hok.
    apply (hfinish (600 * lf_aN f + 9 * lf_aQ f)%Z
                   (2000 * lf_aN f + 9 * lf_am f)%Z
                   (200 * lf_aN f + 9 * lf_ac f)%Z);
      [clear - hlo ha; unfold evalLF; nia | exact hok].
  - intros hok.
    apply (hfinish (615 * lf_aN f + 9 * lf_aQ f)%Z
                   (-2000 * lf_aN f + 9 * lf_am f)%Z
                   (205 * lf_aN f + 9 * lf_ac f)%Z);
      [clear - hhi ha; unfold evalLF; nia | exact hok].
Qed.

Lemma isPosLF_sound {m vn : nat} (hinv : Inv m vn) (f : LinForm) :
  isPosLF f = true -> (1 <= evalLF m vn f)%Z.
Proof.
  intros hok.
  pose proof (isNonnegLF_sound hinv (lfSub f (lfConst 1%Z)) hok) as h.
  rewrite evalLF_sub, evalLF_const in h. lia.
Qed.

Lemma evalLF_parity_decomp {m vn : nat} (hinv : Inv m vn) (f : LinForm) :
  exists K : Z, evalLF m vn f = (2 * K + (lf_aQ f + lf_ac f))%Z.
Proof.
  destruct hinv as [hm10 [hme [hNe _]]].
  pose proof (sum4_odd m ltac:(lia)) as hQo.
  set (kN := vn / 2).
  set (km := m / 2).
  set (kQ := sum4 m / 2).
  assert (hvn : vn = 2 * kN) by (unfold kN; lia).
  assert (hm : m = 2 * km) by (unfold km; lia).
  assert (hq : sum4 m = 2 * kQ + 1) by (unfold kQ; lia).
  exists (lf_aN f * Z.of_nat kN + lf_aQ f * Z.of_nat kQ + lf_am f * Z.of_nat km)%Z.
  unfold evalLF. rewrite hq, hvn, hm. clear. nia.
Qed.

Lemma isEvenLF_sound {m vn : nat} (hinv : Inv m vn) (f : LinForm) :
  isEvenLF f = true -> (evalLF m vn f mod 2 = 0)%Z.
Proof.
  unfold isEvenLF. rewrite Z.eqb_eq. intros hev.
  destruct (evalLF_parity_decomp hinv f) as [K ->].
  lia.
Qed.

Lemma isOddLF_sound {m vn : nat} (hinv : Inv m vn) (f : LinForm) :
  isEvenLF f = false -> (evalLF m vn f mod 2 = 1)%Z.
Proof.
  unfold isEvenLF. intros hne.
  destruct (Z.eqb_spec ((lf_aQ f + lf_ac f) mod 2)%Z 0%Z) as [? | hodd]; [discriminate |].
  destruct (evalLF_parity_decomp hinv f) as [K ->].
  lia.
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
}.

Fixpoint exSL (m vn : nat) (l : list SLChunk) : side :=
  match l with
  | [] => 0inf
  | slb0 :: tl => S0 >> exSL m vn tl
  | slb1 :: tl => S1 >> exSL m vn tl
  | slt110 f :: tl => rep110 (evalLFNat m vn f) (exSL m vn tl)
  end.

Fixpoint exSR (m vn : nat) (r : list SRChunk) : side :=
  match r with
  | [] => 0inf
  | srb0 :: tl => S0 >> exSR m vn tl
  | srb1 :: tl => S1 >> exSR m vn tl
  | srt001 f :: tl => rep001 (evalLFNat m vn f) (exSR m vn tl)
  end.

Definition evalSym (m vn : nat) (s : SymState) : Q * tape :=
  (exSL m vn (sst_l s)) {{B}}> ((sst_hd s) >> exSR m vn (sst_r s)).

Fixpoint validL (m vn : nat) (l : list SLChunk) : Prop :=
  match l with
  | [] => True
  | slb0 :: tl => validL m vn tl
  | slb1 :: tl => validL m vn tl
  | slt110 f :: tl => (1 <= evalLF m vn f)%Z /\ validL m vn tl
  end.

Fixpoint validR (m vn : nat) (r : list SRChunk) : Prop :=
  match r with
  | [] => True
  | srb0 :: tl => validR m vn tl
  | srb1 :: tl => validR m vn tl
  | srt001 f :: tl => (1 <= evalLF m vn f)%Z /\ validR m vn tl
  end.

Definition validSym (m vn : nat) (s : SymState) : Prop :=
  validL m vn (sst_l s) /\ validR m vn (sst_r s).

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

Definition symPopL (l : list SLChunk) : option (Sym * list SLChunk) :=
  match l with
  | [] => Some (S0, [])
  | slb0 :: tl => Some (S0, tl)
  | slb1 :: tl => Some (S1, tl)
  | slt110 f :: tl =>
    if lf_eqb f (lfConst 1%Z) then Some (S1, slb1 :: slb0 :: tl)
    else if isPosLF (lfSub f (lfConst 1%Z)) then
      Some (S1, slb1 :: slb0 :: slt110 (lfSub f (lfConst 1%Z)) :: tl)
    else None
  end.

Definition symPopR (r : list SRChunk) : option (Sym * list SRChunk) :=
  match r with
  | [] => Some (S0, [])
  | srb0 :: tl => Some (S0, tl)
  | srb1 :: tl => Some (S1, tl)
  | srt001 f :: tl =>
    if lf_eqb f (lfConst 1%Z) then Some (S0, srb0 :: srb1 :: tl)
    else if isPosLF (lfSub f (lfConst 1%Z)) then
      Some (S0, srb0 :: srb1 :: srt001 (lfSub f (lfConst 1%Z)) :: tl)
    else None
  end.

Fixpoint symSplitR (l : list SLChunk) (r : list SRChunk) {struct r} : list SLChunk * list SRChunk :=
  match r with
  | srt001 f :: r' => symSplitR (symPushL110 f l) r'
  | _ => (l, r)
  end.

Fixpoint symSplitL (l : list SLChunk) (r : list SRChunk) {struct l} : option (list SLChunk * list SRChunk) :=
  match l with
  | slt110 f :: tl =>
    if lf_eqb f (lfConst 1%Z) then Some (slt110 f :: tl, r)
    else if isEvenLF f then
      if isNonnegLF (lfSub f (lfConst 2%Z)) then
        symSplitL tl (symPushR001 f r)
      else None
    else
      if isNonnegLF (lfSub f (lfConst 3%Z)) then
        Some (slt110 (lfConst 1%Z) :: tl, symPushR001 (lfSub f (lfConst 1%Z)) r)
      else None
  | _ => Some (l, r)
  end.

Fixpoint symStripOnesL (l : list SLChunk) (r : list SRChunk) {struct l} : option (list SLChunk * list SRChunk) :=
  match l with
  | [] => Some ([], r)
  | slb0 :: tl => Some (tl, r)
  | slb1 :: tl => symStripOnesL tl (symPushR0 r)
  | slt110 f :: tl =>
    if lf_eqb f (lfConst 1%Z) then Some (tl, symPushR0 (symPushR0 r))
    else if isPosLF (lfSub f (lfConst 1%Z)) then
      Some (slt110 (lfSub f (lfConst 1%Z)) :: tl, symPushR0 (symPushR0 r))
    else None
  end.

Definition s4xNeed (d : nat) : LinForm :=
  mkLF 0%Z (20 * Z.of_nat (pow4 d))%Z 1%Z (20 * Z.of_nat (sum4 d) + Z.of_nat d)%Z.

Definition s4xNewA (d : nat) : LinForm :=
  mkLF 0%Z (30 * Z.of_nat (pow4 d))%Z 0%Z (10 * Z.of_nat (pow4 d))%Z.

Definition symTrySuper4x (hd : Sym) (l : list SLChunk) (r : list SRChunk) : option SymState :=
  match hd, l, r with
  | S0, [], srt001 a :: srb0 :: srt001 vB :: rtail =>
    if lf_eqb a (lfConst 10%Z) then
      let pick :=
        if isPosLF (lfSub vB (s4xNeed 3)) then Some 3
        else if isPosLF (lfSub vB (s4xNeed 2)) then Some 2
        else if isPosLF (lfSub vB (s4xNeed 1)) then Some 1
        else if isPosLF (lfSub vB (s4xNeed 0)) then Some 0
        else None
      in
      match pick with
      | Some d => Some (mkSymState S0 [] (srt001 (s4xNewA d) :: srb0 :: srt001 (lfSub vB (s4xNeed d)) :: rtail))
      | None => None
      end
    else None
  | _, _, _ => None
  end.

Definition symTryEraDrain (hd : Sym) (l : list SLChunk) (r : list SRChunk) : option SymState :=
  match hd, l, r with
  | S0, [slt110 a; slb1; slb1], srb1 :: srt001 c :: rtail =>
    if isEvenLF a && isNonnegLF (lfSub a (lfConst 2%Z)) && isPosLF c then
      Some (mkSymState S0 [slt110 (lfAdd a (lfScale2 c)); slb1; slb1] (symPushR1 rtail))
    else None
  | _, _, _ => None
  end.

Definition symTryEraOscR (r : list SRChunk) : option (LinForm * LinForm * list SRChunk) :=
  match r with
  | srb0 :: srt001 c :: rtail => Some (lfConst 0%Z, c, rtail)
  | srt001 j2 :: srb0 :: srt001 c :: rtail =>
    if isEvenLF j2 && isNonnegLF (lfSub j2 (lfConst 2%Z)) then Some (j2, c, rtail) else None
  | _ => None
  end.

Definition symTryEraOsc (hd : Sym) (l : list SLChunk) (r : list SRChunk) : option SymState :=
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
      match symTryEraOscR r with
      | Some (j2, c, rtail) =>
        let cmp : option (LinForm * list SLChunk * list SRChunk) :=
          if lf_eqb a c then Some (a, ltail, rtail)
          else if isPosLF (lfSub c a) then Some (a, ltail, symPushR001 (lfSub c a) rtail)
          else if isPosLF (lfSub a c) then Some (c, symPushL110 (lfSub a c) ltail, rtail)
          else None
        in
        match cmp with
        | Some (n, lbase, rbase) =>
          let l1 := symPushL0 lbase in
          let l_new := if is10 then symPushL1 l1 else l1 in
          let r_new := symPushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase) in
          Some (mkSymState S1 l_new r_new)
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | S0 => None
  end.

Definition symStepBase (hd : Sym) (l : list SLChunk) (r : list SRChunk) : option SymState :=
  match hd with
  | S1 =>
    let '(l1, r_in) := symSplitR l r in
    match symPopR r_in with
    | None => None
    | Some (b1, r1) =>
      match b1 with
      | S1 => Some (mkSymState S0 l1 (symPushR0 r1))
      | S0 =>
        match symPopR r1 with
        | None => None
        | Some (b2, r2) =>
          match b2 with
          | S0 =>
            match symPopR r2 with
            | None => None
            | Some (b3, r3) => Some (mkSymState b3 (symPushL110 (lfConst 1%Z) l1) r3)
            end
          | S1 =>
            match symPopR r2 with
            | None => None
            | Some (b3, r3) =>
              match b3 with
              | S0 => Some (mkSymState S1 (symPushL0 l1) (symPushR0 (symPushR0 r3)))
              | S1 => None
              end
            end
          end
        end
      end
    end
  | S0 =>
    match symSplitL l r with
    | None => None
    | Some (l1, r1) =>
      match symStripOnesL l1 (symPushR1 r1) with
      | None => None
      | Some (l_after, r_rem) =>
        match symPopL l_after with
        | None => None
        | Some (e, e_rem) =>
          match e with
          | S0 => Some (mkSymState S1 (symPushL1 e_rem) r_rem)
          | S1 =>
            match symPopL e_rem with
            | None => None
            | Some (ab, a_rem) =>
              match ab with
              | S1 =>
                match symPopL a_rem with
                | None => None
                | Some (cb, c_rem) => Some (mkSymState cb c_rem (symPushR001 (lfConst 1%Z) r_rem))
                end
              | S0 => Some (mkSymState S1 (symPushL1 (symPushL1 a_rem)) r_rem)
              end
            end
          end
        end
      end
    end
  end.

Definition symStep (s : SymState) : option SymState :=
  match symTrySuper4x (sst_hd s) (sst_l s) (sst_r s) with
  | Some s' => Some s'
  | None =>
    match symTryEraDrain (sst_hd s) (sst_l s) (sst_r s) with
    | Some s' => Some s'
    | None =>
      match symTryEraOsc (sst_hd s) (sst_l s) (sst_r s) with
      | Some s' => Some s'
      | None => symStepBase (sst_hd s) (sst_l s) (sst_r s)
      end
    end
  end.

Fixpoint symIterPow2 (k : nat) (s : SymState) : option SymState :=
  match k with
  | 0 => symStep s
  | S k' => optBind (symIterPow2 k' s) (symIterPow2 k')
  end.

(* Soundness of Symbolic Interpreter *)

Lemma evalLFNat_const (m vn k : nat) :
  evalLFNat m vn (lfConst (Z.of_nat k)) = k.
Proof.
  unfold evalLFNat. rewrite evalLF_const. apply Nat2Z.id.
Qed.

Lemma exSL_pushL110 {m vn : nat} (f : LinForm) (l : list SLChunk) :
  (1 <= evalLF m vn f)%Z -> validL m vn l ->
  validL m vn (symPushL110 f l) /\
  exSL m vn (symPushL110 f l) = rep110 (evalLFNat m vn f) (exSL m vn l).
Proof.
  intros hf hl.
  destruct l as [| [| | g] tl].
  - exact (conj (conj hf I) eq_refl).
  - exact (conj (conj hf hl) eq_refl).
  - exact (conj (conj hf hl) eq_refl).
  - destruct hl as [hg htl].
    cbn [symPushL110 validL exSL].
    split; [split; [rewrite evalLF_add; lia | exact htl] |].
    assert (hadd : evalLFNat m vn (lfAdd f g) = evalLFNat m vn f + evalLFNat m vn g).
    { unfold evalLFNat. rewrite evalLF_add. lia. }
    rewrite hadd, rep110_add. reflexivity.
Qed.

Lemma exSL_pushL0 {m vn : nat} (l : list SLChunk) :
  validL m vn l ->
  validL m vn (symPushL0 l) /\ exSL m vn (symPushL0 l) = S0 >> exSL m vn l.
Proof.
  intros hl.
  destruct l; [exact (conj I (eq_sym cons_zero_0inf)) | exact (conj hl eq_refl)].
Qed.

Lemma exSL_pushL1 {m vn : nat} (l : list SLChunk) :
  validL m vn l ->
  validL m vn (symPushL1 l) /\ exSL m vn (symPushL1 l) = S1 >> exSL m vn l.
Proof.
  intros hl.
  destruct l as [| [| | ?] [| [| | ?] tl]]; try exact (conj hl eq_refl).
  cbn [symPushL1].
  assert (h1 : (1 <= evalLF m vn (lfConst 1%Z))%Z) by (rewrite evalLF_const; lia).
  destruct (exSL_pushL110 (lfConst 1%Z) tl h1 hl) as [hv hex].
  split; [exact hv |].
  rewrite hex. change 1%Z with (Z.of_nat 1). rewrite evalLFNat_const. reflexivity.
Qed.

Lemma exSR_pushR001 {m vn : nat} (f : LinForm) (r : list SRChunk) :
  (1 <= evalLF m vn f)%Z -> validR m vn r ->
  validR m vn (symPushR001 f r) /\
  exSR m vn (symPushR001 f r) = rep001 (evalLFNat m vn f) (exSR m vn r).
Proof.
  intros hf hr.
  destruct r as [| [| | g] tl].
  - exact (conj (conj hf I) eq_refl).
  - exact (conj (conj hf hr) eq_refl).
  - exact (conj (conj hf hr) eq_refl).
  - destruct hr as [hg htl].
    cbn [symPushR001 validR exSR].
    split; [split; [rewrite evalLF_add; lia | exact htl] |].
    assert (hadd : evalLFNat m vn (lfAdd f g) = evalLFNat m vn f + evalLFNat m vn g).
    { unfold evalLFNat. rewrite evalLF_add. lia. }
    rewrite hadd, rep001_add. reflexivity.
Qed.

Lemma exSR_pushR0 {m vn : nat} (r : list SRChunk) :
  validR m vn r ->
  validR m vn (symPushR0 r) /\ exSR m vn (symPushR0 r) = S0 >> exSR m vn r.
Proof.
  intros hr.
  destruct r as [| [| | ?] [| [| | ?] tl]];
    try exact (conj hr eq_refl);
    try exact (conj I (eq_sym cons_zero_0inf)).
  cbn [symPushR0].
  assert (h1 : (1 <= evalLF m vn (lfConst 1%Z))%Z) by (rewrite evalLF_const; lia).
  destruct (exSR_pushR001 (lfConst 1%Z) tl h1 hr) as [hv hex].
  split; [exact hv |].
  rewrite hex. change 1%Z with (Z.of_nat 1). rewrite evalLFNat_const. reflexivity.
Qed.

Lemma symPopL_ok {m vn : nat} (hinv : Inv m vn) (l l' : list SLChunk) (b : Sym) :
  validL m vn l -> symPopL l = Some (b, l') ->
  validL m vn l' /\ exSL m vn l = b >> exSL m vn l'.
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
    + destruct (isPosLF (lfSub f (lfConst 1%Z))) eqn:h2; [| discriminate].
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      pose proof (isPosLF_sound hinv _ h2) as hsub.
      split; [exact (conj hsub htl) |].
      cbn [exSL].
      assert (heq : evalLFNat m vn f = 1 + evalLFNat m vn (lfSub f (lfConst 1%Z))).
      { unfold evalLFNat. rewrite evalLF_sub, evalLF_const in hsub |- *. lia. }
      rewrite heq, (rep110_add 1). reflexivity.
Qed.

Lemma symPopR_ok {m vn : nat} (hinv : Inv m vn) (r r' : list SRChunk) (b : Sym) :
  validR m vn r -> symPopR r = Some (b, r') ->
  validR m vn r' /\ exSR m vn r = b >> exSR m vn r'.
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
    + destruct (isPosLF (lfSub f (lfConst 1%Z))) eqn:h2; [| discriminate].
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      pose proof (isPosLF_sound hinv _ h2) as hsub.
      split; [exact (conj hsub htl) |].
      cbn [exSR].
      assert (heq : evalLFNat m vn f = 1 + evalLFNat m vn (lfSub f (lfConst 1%Z))).
      { unfold evalLFNat. rewrite evalLF_sub, evalLF_const in hsub |- *. lia. }
      rewrite heq, (rep001_add 1). reflexivity.
Qed.

Lemma symSplitR_ok {m vn : nat} : forall (r : list SRChunk) (l : list SLChunk),
  validL m vn l -> validR m vn r ->
  validL m vn (fst (symSplitR l r)) /\
  validR m vn (snd (symSplitR l r)) /\
  (exSL m vn l {{B}}> (S1 >> exSR m vn r)) -->*
  (exSL m vn (fst (symSplitR l r)) {{B}}> (S1 >> exSR m vn (snd (symSplitR l r)))).
Proof.
  induction r as [| [| | f] r IH]; intros l hl hr;
    try exact (conj hl (conj hr (evstep_refl tm _))).
  destruct hr as [hf hr].
  cbn [symSplitR exSR].
  destruct (exSL_pushL110 f l hf hl) as [hl' hex].
  pose proof (reach_splitR_lb (evalLFNat m vn f) (exSL m vn l) (exSR m vn r)) as h1.
  rewrite <- hex in h1.
  destruct (IH (symPushL110 f l) hl' hr) as [hvL [hvR h2]].
  exact (conj hvL (conj hvR (etrans h1 h2))).
Qed.

Lemma symSplitL_ok {m vn : nat} (hinv : Inv m vn) :
  forall (l : list SLChunk) (r : list SRChunk) (l' : list SLChunk) (r' : list SRChunk),
  validL m vn l -> validR m vn r -> symSplitL l r = Some (l', r') ->
  validL m vn l' /\ validR m vn r' /\
  (exSL m vn l {{B}}> (S0 >> exSR m vn r)) -->*
  (exSL m vn l' {{B}}> (S0 >> exSR m vn r')).
Proof.
  induction l as [| [| | f] tl IH]; intros r l' r' hl hr H;
    try (cbn [symSplitL] in H; apply some_inj, pair_inj in H; destruct H as [<- <-];
         exact (conj hl (conj hr (evstep_refl tm _)))).
  destruct hl as [hf htl].
  cbn [symSplitL] in H.
  destruct (lf_eqb f (lfConst 1%Z)) eqn:h1.
  - apply some_inj, pair_inj in H; destruct H as [<- <-].
    exact (conj (conj hf htl) (conj hr (evstep_refl tm _))).
  - destruct (isEvenLF f) eqn:hev.
    + destruct (isNonnegLF (lfSub f (lfConst 2%Z))) eqn:h2; [| discriminate].
      pose proof (isEvenLF_sound hinv f hev) as hfev.
      pose proof (isNonnegLF_sound hinv _ h2) as hge2.
      rewrite evalLF_sub, evalLF_const in hge2.
      assert (hfn : evalLFNat m vn f = 2 * (evalLFNat m vn f / 2))
        by (unfold evalLFNat; lia).
      destruct (exSR_pushR001 f r hf hr) as [hr1 hex1].
      assert (hstep : (exSL m vn (slt110 f :: tl) {{B}}> (S0 >> exSR m vn r)) -->*
                      (exSL m vn tl {{B}}> (S0 >> exSR m vn (symPushR001 f r)))).
      { cbn [exSL]. rewrite hex1, hfn.
        exact (reach_splitL_lb (evalLFNat m vn f / 2) (exSL m vn tl) (exSR m vn r)). }
      destruct (IH (symPushR001 f r) l' r' htl hr1 H) as [hvL [hvR hrest]].
      exact (conj hvL (conj hvR (etrans hstep hrest))).
    + destruct (isNonnegLF (lfSub f (lfConst 3%Z))) eqn:h3; [| discriminate].
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      pose proof (isNonnegLF_sound hinv _ h3) as hge3.
      rewrite evalLF_sub, evalLF_const in hge3.
      pose proof (isOddLF_sound hinv f hev) as hfodd.
      assert (hsub_pos : (1 <= evalLF m vn (lfSub f (lfConst 1%Z)))%Z)
        by (rewrite evalLF_sub, evalLF_const; lia).
      destruct (exSR_pushR001 (lfSub f (lfConst 1%Z)) r hsub_pos hr) as [hr1 hex1].
      assert (hc1 : (1 <= evalLF m vn (lfConst 1%Z))%Z) by (rewrite evalLF_const; lia).
      split; [exact (conj hc1 htl) | split; [exact hr1 |]].
      cbn [exSL]. rewrite hex1.
      set (half := evalLFNat m vn (lfSub f (lfConst 1%Z)) / 2).
      assert (hsub_even : evalLFNat m vn (lfSub f (lfConst 1%Z)) = 2 * half)
        by (unfold half, evalLFNat; rewrite evalLF_sub, evalLF_const; lia).
      assert (hfn : evalLFNat m vn f = 2 * half + 1)
        by (unfold half, evalLFNat; rewrite evalLF_sub, evalLF_const; lia).
      rewrite hfn, (rep110_add (2 * half) 1), hsub_even.
      change (lfConst 1%Z) with (lfConst (Z.of_nat 1)). rewrite evalLFNat_const.
      exact (reach_splitL_lb half (rep110 1 (exSL m vn tl)) (exSR m vn r)).
Qed.

Lemma symStripOnesL_ok {m vn : nat} (hinv : Inv m vn) :
  forall (l : list SLChunk) (r : list SRChunk) (l' : list SLChunk) (r' : list SRChunk),
  validL m vn l -> validR m vn r -> symStripOnesL l r = Some (l', r') ->
  validL m vn l' /\ validR m vn r' /\
  (exSL m vn l <{{C}} exSR m vn r) -->*
  (exSL m vn l' {{C}}> (S0 >> exSR m vn r')).
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
    assert (h1 : ((S1 >> exSL m vn tl) <{{C}} exSR m vn r) -->*
                 (exSL m vn tl <{{C}} exSR m vn (symPushR0 r))).
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
    + destruct (isPosLF (lfSub f (lfConst 1%Z))) eqn:h2; [| discriminate].
      apply some_inj, pair_inj in H; destruct H as [<- <-].
      pose proof (isPosLF_sound hinv _ h2) as hsub.
      split; [exact (conj hsub htl) | split; [exact hr2 |]].
      cbn [exSL].
      assert (heq : evalLFNat m vn f = 1 + evalLFNat m vn (lfSub f (lfConst 1%Z))).
      { unfold evalLFNat. rewrite evalLF_sub, evalLF_const in hsub |- *. lia. }
      rewrite heq, (rep110_add 1), hex2, hex1.
      cbn [rep110]. fast_execute.
Qed.

Lemma symTrySuper4x_sound {m vn : nat} (hinv : Inv m vn)
  (hd : Sym) (l : list SLChunk) (r : list SRChunk) (s' : SymState) :
  validSym m vn (mkSymState hd l r) ->
  symTrySuper4x hd l r = Some s' ->
  validSym m vn s' /\ evalSym m vn (mkSymState hd l r) -->+ evalSym m vn s'.
Proof.
  intros hv H.
  unfold symTrySuper4x in H.
  destruct hd as [|]; [| discriminate].
  destruct l as [| ? ?]; [| discriminate].
  destruct r as [| [| | a] [| [| | ?] [| [| | vB] rtail]]]; try discriminate.
  destruct (lf_eqb a (lfConst 10%Z)) eqn:ha; [| discriminate].
  apply lf_eqb_eq in ha. subst a.
  assert (hrun : forall d : nat,
    isPosLF (lfSub vB (s4xNeed d)) = true ->
    s' = mkSymState S0 [] (srt001 (s4xNewA d) :: srb0 :: srt001 (lfSub vB (s4xNeed d)) :: rtail) ->
    validSym m vn s' /\
    evalSym m vn (mkSymState S0 [] (srt001 (lfConst 10%Z) :: srb0 :: srt001 vB :: rtail)) -->+
    evalSym m vn s').
  { intros d hpos ->.
    pose proof (isPosLF_sound hinv _ hpos) as hBsub.
    destruct hv as [_ [_ [hBvalid hrtail]]].
    pose proof (pow4_pos d) as hp4d.
    assert (hnewA_pos : (1 <= evalLF m vn (s4xNewA d))%Z)
      by (clear - hp4d; unfold evalLF, s4xNewA; cbn [lf_aN lf_aQ lf_am lf_ac]; nia).
    split; [exact (conj I (conj hnewA_pos (conj hBsub hrtail))) |].
    unfold evalSym; cbn [sst_hd sst_l sst_r exSL exSR].
    assert (h10 : evalLFNat m vn (lfConst 10%Z) = 2 * (2 + 3)).
    { change 10%Z with (Z.of_nat 10). rewrite evalLFNat_const. reflexivity. }
    assert (hneed_eq : evalLF m vn (s4xNeed d) =
                       Z.of_nat (2 * (2 * (2 + 3)) * sum4 (m + d) + (m + d))).
    { clear. unfold evalLF, s4xNeed; cbn [lf_aN lf_aQ lf_am lf_ac].
      rewrite (sum4_add m d). nia. }
    assert (hnewA_eq : evalLFNat m vn (s4xNewA d) = (2 * (2 + 3)) * pow4 (m + d)).
    { unfold evalLFNat, evalLF, s4xNewA; cbn [lf_aN lf_aQ lf_am lf_ac].
      replace (0 * Z.of_nat vn + 30 * Z.of_nat (pow4 d) * Z.of_nat (sum4 m) +
               0 * Z.of_nat m + 10 * Z.of_nat (pow4 d))%Z
        with (Z.of_nat ((2 * (2 + 3)) * pow4 (m + d)))
        by (clear; rewrite (pow4_add m d), <- (sum4_spec m); nia).
      apply Nat2Z.id. }
    assert (hB_eq : evalLFNat m vn vB =
                    2 * (2 * (2 + 3)) * sum4 (m + d) + (m + d) +
                    evalLFNat m vn (lfSub vB (s4xNeed d))).
    { unfold evalLFNat. rewrite evalLF_sub, hneed_eq in hBsub |- *. lia. }
    rewrite h10, hB_eq, hnewA_eq.
    assert (hmd : 0 < m + d) by (destruct hinv as [hm10 _]; lia).
    exact (super4x_iter_plus (m + d) 2 (evalLFNat m vn (lfSub vB (s4xNeed d))) hmd (exSR m vn rtail)). }
  destruct (isPosLF (lfSub vB (s4xNeed 3))) eqn:h3;
    [apply some_inj in H; exact (hrun 3 h3 (eq_sym H)) |].
  destruct (isPosLF (lfSub vB (s4xNeed 2))) eqn:h2;
    [apply some_inj in H; exact (hrun 2 h2 (eq_sym H)) |].
  destruct (isPosLF (lfSub vB (s4xNeed 1))) eqn:h1;
    [apply some_inj in H; exact (hrun 1 h1 (eq_sym H)) |].
  destruct (isPosLF (lfSub vB (s4xNeed 0))) eqn:h0;
    [apply some_inj in H; exact (hrun 0 h0 (eq_sym H)) | discriminate].
Qed.

Lemma symTryEraDrain_sound {m vn : nat} (hinv : Inv m vn)
  (hd : Sym) (l : list SLChunk) (r : list SRChunk) (s' : SymState) :
  validSym m vn (mkSymState hd l r) ->
  symTryEraDrain hd l r = Some s' ->
  validSym m vn s' /\ evalSym m vn (mkSymState hd l r) -->+ evalSym m vn s'.
Proof.
  intros hv H.
  unfold symTryEraDrain in H.
  destruct hd as [|]; [| discriminate].
  destruct l as [| [| | a] [| [| | ?] [| [| | ?] [| ? ?]]]]; try discriminate.
  destruct r as [| [| | ?] [| [| | c] rtail]]; try discriminate.
  destruct (isEvenLF a && isNonnegLF (lfSub a (lfConst 2%Z)) && isPosLF c) eqn:hcond; [| discriminate].
  apply some_inj in H; subst s'.
  rewrite !Bool.andb_true_iff in hcond.
  destruct hcond as [[hev h2] hc].
  pose proof (isEvenLF_sound hinv a hev) as haev.
  pose proof (isNonnegLF_sound hinv _ h2) as hage2.
  rewrite evalLF_sub, evalLF_const in hage2.
  pose proof (isPosLF_sound hinv c hc) as hcpos.
  destruct hv as [_ [_ hrtail]].
  assert (hnew_pos : (1 <= evalLF m vn (lfAdd a (lfScale2 c)))%Z)
    by (rewrite evalLF_add, evalLF_scale2; lia).
  split; [exact (conj (conj hnew_pos I) hrtail) |].
  unfold evalSym, symPushR1; cbn [sst_hd sst_l sst_r exSL exSR].
  set (k := evalLFNat m vn a / 2 - 1).
  set (cm1 := evalLFNat m vn c - 1).
  assert (ha_eq : evalLFNat m vn a = 2 * (k + 1)) by (unfold k, evalLFNat; lia).
  assert (hc_eq : evalLFNat m vn c = cm1 + 1) by (unfold cm1, evalLFNat; lia).
  assert (hout_eq : evalLFNat m vn (lfAdd a (lfScale2 c)) = 2 * (k + 1 + (cm1 + 1)))
    by (unfold k, cm1, evalLFNat; rewrite evalLF_add, evalLF_scale2; lia).
  rewrite ha_eq, hc_eq, hout_eq.
  exact (era_drain_iter cm1 k (exSR m vn rtail)).
Qed.

Lemma symTryEraOscR_ok {m vn : nat} (hinv : Inv m vn) (r : list SRChunk)
  (j2 c : LinForm) (rtail : list SRChunk) :
  validR m vn r -> symTryEraOscR r = Some (j2, c, rtail) ->
  (0 <= evalLF m vn j2)%Z /\ (evalLF m vn j2 mod 2 = 0)%Z /\
  (1 <= evalLF m vn c)%Z /\ validR m vn rtail /\
  exSR m vn r = rep001 (evalLFNat m vn j2) (S0 >> rep001 (evalLFNat m vn c) (exSR m vn rtail)).
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
    destruct (isEvenLF j0 && isNonnegLF (lfSub j0 (lfConst 2%Z))) eqn:hcond; [| discriminate].
    apply some_inj, pair_inj in H; destruct H as [H <-]; apply pair_inj in H; destruct H as [<- <-].
    rewrite Bool.andb_true_iff in hcond.
    destruct hcond as [hev h2].
    pose proof (isEvenLF_sound hinv j0 hev) as hjev.
    pose proof (isNonnegLF_sound hinv _ h2) as hjge2.
    rewrite evalLF_sub, evalLF_const in hjge2.
    destruct hr as [_ [hc hrt]].
    split; [lia | exact (conj hjev (conj hc (conj hrt eq_refl)))].
Qed.

Lemma symTryEraOsc_sound {m vn : nat} (hinv : Inv m vn)
  (hd : Sym) (l : list SLChunk) (r : list SRChunk) (s' : SymState) :
  validSym m vn (mkSymState hd l r) ->
  symTryEraOsc hd l r = Some s' ->
  validSym m vn s' /\ evalSym m vn (mkSymState hd l r) -->+ evalSym m vn s'.
Proof.
  intros [hvl hvr] H.
  unfold symTryEraOsc in H.
  destruct hd as [|]; [discriminate |].
  assert (hcore : forall (is10 : bool) (a : LinForm) (ltail : list SLChunk),
    (1 <= evalLF m vn a)%Z -> validL m vn ltail ->
    exSL m vn l = (if is10 then S1 >> S0 >> rep110 (evalLFNat m vn a) (exSL m vn ltail)
                   else S0 >> rep110 (evalLFNat m vn a) (exSL m vn ltail)) ->
    (match symTryEraOscR r with
     | Some (j2, c, rtail) =>
       let cmp :=
         if lf_eqb a c then Some (a, ltail, rtail)
         else if isPosLF (lfSub c a) then Some (a, ltail, symPushR001 (lfSub c a) rtail)
         else if isPosLF (lfSub a c) then Some (c, symPushL110 (lfSub a c) ltail, rtail)
         else None
       in
       match cmp with
       | Some (n, lbase, rbase) =>
         let l1 := symPushL0 lbase in
         let l_new := if is10 then symPushL1 l1 else l1 in
         let r_new := symPushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase) in
         Some (mkSymState S1 l_new r_new)
       | None => None
       end
     | None => None
     end) = Some s' ->
    validSym m vn s' /\ evalSym m vn (mkSymState S1 l r) -->+ evalSym m vn s').
  { intros is10 a ltail ha hltail hexL Hbody.
    destruct (symTryEraOscR r) as [[[j2 c] rtail] |] eqn:Er; [| discriminate].
    destruct (symTryEraOscR_ok hinv r j2 c rtail hvr Er) as [hj0 [hjev [hc [hrtail hexR]]]].
    assert (hfinish : forall (n : LinForm) (lbase : list SLChunk) (rbase : list SRChunk),
      (1 <= evalLF m vn n)%Z ->
      validL m vn lbase -> validR m vn rbase ->
      rep110 (evalLFNat m vn a) (exSL m vn ltail) = rep110 (evalLFNat m vn n) (exSL m vn lbase) ->
      rep001 (evalLFNat m vn c) (exSR m vn rtail) = rep001 (evalLFNat m vn n) (exSR m vn rbase) ->
      s' = mkSymState S1 (if is10 then symPushL1 (symPushL0 lbase) else symPushL0 lbase)
                         (symPushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase)) ->
      validSym m vn s' /\ evalSym m vn (mkSymState S1 l r) -->+ evalSym m vn s').
    { intros n lbase rbase hn hlbase hrbase hLsplit hRsplit ->.
      destruct (exSL_pushL0 lbase hlbase) as [hvl0 hexl0].
      destruct (exSR_pushR0 rbase hrbase) as [hvr0 hexr0].
      assert (hj2n_pos : (1 <= evalLF m vn (lfAdd j2 (lfScale2 n)))%Z)
        by (rewrite evalLF_add, evalLF_scale2; lia).
      destruct (exSR_pushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase) hj2n_pos hvr0) as [hvr1 hexr1].
      set (nm1 := evalLFNat m vn n - 1).
      set (j := evalLFNat m vn j2 / 2).
      assert (hn_eq : evalLFNat m vn n = nm1 + 1) by (unfold nm1, evalLFNat; lia).
      assert (hj_eq : evalLFNat m vn j2 = 2 * j) by (unfold j, evalLFNat; lia).
      assert (hjout_eq : evalLFNat m vn (lfAdd j2 (lfScale2 n)) = 2 * (j + (nm1 + 1)))
        by (unfold j, nm1, evalLFNat; rewrite evalLF_add, evalLF_scale2; lia).
      destruct is10.
      - destruct (exSL_pushL1 (symPushL0 lbase) hvl0) as [hvl1 hexl1].
        split; [exact (conj hvl1 hvr1) |].
        unfold evalSym; cbn [sst_hd sst_l sst_r].
        rewrite hexL, hexR, hLsplit, hRsplit, hexl1, hexl0, hexr1, hexr0, hn_eq, hj_eq, hjout_eq.
        exact (era_osc10_iter nm1 j (exSL m vn lbase) (exSR m vn rbase)).
      - split; [exact (conj hvl0 hvr1) |].
        unfold evalSym; cbn [sst_hd sst_l sst_r].
        rewrite hexL, hexR, hLsplit, hRsplit, hexl0, hexr1, hexr0, hn_eq, hj_eq, hjout_eq.
        exact (era_osc_iter nm1 j (exSL m vn lbase) (exSR m vn rbase)). }
    cbv zeta in Hbody.
    destruct (lf_eqb a c) eqn:heq.
    - apply lf_eqb_eq in heq. subst c.
      apply some_inj in Hbody.
      exact (hfinish a ltail rtail ha hltail hrtail eq_refl eq_refl (eq_sym Hbody)).
    - destruct (isPosLF (lfSub c a)) eqn:hca.
      + apply some_inj in Hbody.
        pose proof (isPosLF_sound hinv _ hca) as hsub.
        destruct (exSR_pushR001 (lfSub c a) rtail hsub hrtail) as [hvr_sub hexr_sub].
        assert (hce : evalLFNat m vn c = evalLFNat m vn a + evalLFNat m vn (lfSub c a))
          by (unfold evalLFNat; rewrite evalLF_sub in hsub |- *; lia).
        refine (hfinish a ltail (symPushR001 (lfSub c a) rtail) ha hltail hvr_sub eq_refl _ (eq_sym Hbody)).
        rewrite hexr_sub, hce, rep001_add. reflexivity.
      + destruct (isPosLF (lfSub a c)) eqn:hac2; [| discriminate].
        apply some_inj in Hbody.
        pose proof (isPosLF_sound hinv _ hac2) as hsub.
        destruct (exSL_pushL110 (lfSub a c) ltail hsub hltail) as [hvl_sub hexl_sub].
        assert (hae : evalLFNat m vn a = evalLFNat m vn c + evalLFNat m vn (lfSub a c))
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

Lemma symStepBase_sound {m vn : nat} (hinv : Inv m vn)
  (hd : Sym) (l : list SLChunk) (r : list SRChunk) (s' : SymState) :
  validSym m vn (mkSymState hd l r) ->
  symStepBase hd l r = Some s' ->
  validSym m vn s' /\ evalSym m vn (mkSymState hd l r) -->+ evalSym m vn s'.
Proof.
  intros [hvl hvr] H.
  unfold symStepBase in H.
  destruct hd as [|].
  - destruct (symSplitL l r) as [[l1 r1] |] eqn:EL; [| discriminate].
    destruct (symSplitL_ok hinv l r l1 r1 hvl hvr EL) as [hvL1 [hvR1 hsw]].
    assert (hb0 : (exSL m vn l1 {{B}}> (S0 >> exSR m vn r1)) -->*
                  (exSL m vn l1 <{{C}} exSR m vn (symPushR1 r1))).
    { cbn [symPushR1 exSR]. apply evstep_one. apply @step_left. reflexivity. }
    destruct (symStripOnesL l1 (symPushR1 r1)) as [[l_after r_rem] |] eqn:EO; [| discriminate].
    destruct (symStripOnesL_ok hinv l1 (symPushR1 r1) l_after r_rem hvL1 hvR1 EO)
      as [hvLa [hvRr hones]].
    pose proof (etrans (etrans hsw hb0) hones) as hpre.
    destruct (symPopL l_after) as [[e e_rem] |] eqn:EPE; [| discriminate].
    destruct (symPopL_ok hinv l_after e_rem e hvLa EPE) as [hve hpe].
    destruct e as [|].
    + apply some_inj in H; subst s'.
      destruct (exSL_pushL1 e_rem hve) as [hvl1 hexl1].
      split; [exact (conj hvl1 hvRr) |].
      unfold evalSym; cbn [sst_hd sst_l sst_r].
      rewrite hpe in hpre. rewrite hexl1.
      exact (sp_trans hpre (reach_L1_lb (exSL m vn e_rem) (exSR m vn r_rem))).
    + destruct (symPopL e_rem) as [[ab a_rem] |] eqn:EPA; [| discriminate].
      destruct (symPopL_ok hinv e_rem a_rem ab hve EPA) as [hva hpa].
      destruct ab as [|].
      * apply some_inj in H; subst s'.
        destruct (exSL_pushL1 a_rem hva) as [hvl1 hexl1].
        destruct (exSL_pushL1 (symPushL1 a_rem) hvl1) as [hvl2 hexl2].
        split; [exact (conj hvl2 hvRr) |].
        unfold evalSym; cbn [sst_hd sst_l sst_r].
        rewrite hpe, hpa in hpre. rewrite hexl2, hexl1.
        exact (sp_trans hpre (reach_L3_lb (exSL m vn a_rem) (exSR m vn r_rem))).
      * destruct (symPopL a_rem) as [[cb c_rem] |] eqn:EPC; [| discriminate].
        apply some_inj in H; subst s'.
        destruct (symPopL_ok hinv a_rem c_rem cb hva EPC) as [hvc hpc].
        assert (hc1 : (1 <= evalLF m vn (lfConst 1%Z))%Z) by (rewrite evalLF_const; lia).
        destruct (exSR_pushR001 (lfConst 1%Z) r_rem hc1 hvRr) as [hvr1 hexr1].
        split; [exact (conj hvc hvr1) |].
        unfold evalSym; cbn [sst_hd sst_l sst_r].
        rewrite hpe, hpa, hpc in hpre.
        rewrite hexr1. change 1%Z with (Z.of_nat 1). rewrite evalLFNat_const.
        cbn [rep001].
        exact (sp_trans hpre (reach_L2_lb cb (exSL m vn c_rem) (exSR m vn r_rem))).
  - destruct (symSplitR_ok r l hvl hvr) as [hvL1 [hvR1 hsw]].
    destruct (symSplitR l r) as [l1 r_in]; cbn [fst snd] in hvL1, hvR1, hsw.
    destruct (symPopR r_in) as [[b1 r1] |] eqn:EP1; [| discriminate].
    destruct (symPopR_ok hinv r_in r1 b1 hvR1 EP1) as [hvr1 hp1].
    destruct b1 as [|].
    + destruct (symPopR r1) as [[b2 r2] |] eqn:EP2; [| discriminate].
      destruct (symPopR_ok hinv r1 r2 b2 hvr1 EP2) as [hvr2 hp2].
      destruct b2 as [|].
      * destruct (symPopR r2) as [[b3 r3] |] eqn:EP3; [| discriminate].
        apply some_inj in H; subst s'.
        destruct (symPopR_ok hinv r2 r3 b3 hvr2 EP3) as [hvr3 hp3].
        assert (hc1 : (1 <= evalLF m vn (lfConst 1%Z))%Z) by (rewrite evalLF_const; lia).
        destruct (exSL_pushL110 (lfConst 1%Z) l1 hc1 hvL1) as [hvl2 hexl2].
        split; [exact (conj hvl2 hvr3) |].
        unfold evalSym; cbn [sst_hd sst_l sst_r].
        rewrite hp1, hp2, hp3 in hsw.
        rewrite hexl2. change 1%Z with (Z.of_nat 1). rewrite evalLFNat_const.
        cbn [rep110].
        exact (sp_trans hsw (reach_R2_lb b3 (exSL m vn l1) (exSR m vn r3))).
      * destruct (symPopR r2) as [[b3 r3] |] eqn:EP3; [| discriminate].
        destruct (symPopR_ok hinv r2 r3 b3 hvr2 EP3) as [hvr3 hp3].
        destruct b3 as [|]; [| discriminate].
        apply some_inj in H; subst s'.
        destruct (exSL_pushL0 l1 hvL1) as [hvl2 hexl2].
        destruct (exSR_pushR0 r3 hvr3) as [hvr4 hexr4].
        destruct (exSR_pushR0 (symPushR0 r3) hvr4) as [hvr5 hexr5].
        split; [exact (conj hvl2 hvr5) |].
        unfold evalSym; cbn [sst_hd sst_l sst_r].
        rewrite hp1, hp2, hp3 in hsw. rewrite hexl2, hexr5, hexr4.
        exact (sp_trans hsw (reach_R3_lb (exSL m vn l1) (exSR m vn r3))).
    + apply some_inj in H; subst s'.
      destruct (exSR_pushR0 r1 hvr1) as [hvr0 hexr0].
      split; [exact (conj hvL1 hvr0) |].
      unfold evalSym; cbn [sst_hd sst_l sst_r].
      rewrite hp1 in hsw. rewrite hexr0.
      exact (sp_trans hsw (reach_R1_lb (exSL m vn l1) (exSR m vn r1))).
Qed.

Lemma symStep_sound {m vn : nat} (hinv : Inv m vn) (s s' : SymState) :
  validSym m vn s -> symStep s = Some s' ->
  validSym m vn s' /\ evalSym m vn s -->+ evalSym m vn s'.
Proof.
  destruct s as [hd l r].
  intros hv H.
  unfold symStep in H; cbn [sst_hd sst_l sst_r] in H.
  destruct (symTrySuper4x hd l r) as [s0 |] eqn:E0.
  - apply some_inj in H; subst s'. exact (symTrySuper4x_sound hinv hd l r s0 hv E0).
  - destruct (symTryEraDrain hd l r) as [s1 |] eqn:E1.
    + apply some_inj in H; subst s'. exact (symTryEraDrain_sound hinv hd l r s1 hv E1).
    + destruct (symTryEraOsc hd l r) as [s2 |] eqn:E2.
      * apply some_inj in H; subst s'. exact (symTryEraOsc_sound hinv hd l r s2 hv E2).
      * exact (symStepBase_sound hinv hd l r s' hv H).
Qed.

Lemma symIterPow2_sound {m vn : nat} (hinv : Inv m vn) :
  forall (k : nat) (s s' : SymState),
  validSym m vn s -> symIterPow2 k s = Some s' ->
  validSym m vn s' /\ evalSym m vn s -->+ evalSym m vn s'.
Proof.
  induction k as [| k IH]; intros s s' hv H.
  - exact (symStep_sound hinv s s' hv H).
  - cbn [symIterPow2 optBind] in H.
    destruct (symIterPow2 k s) as [sm |] eqn:E1; [| discriminate].
    destruct (IH s sm hv E1) as [hvm h1].
    destruct (IH sm s' hvm H) as [hv' h2].
    exact (conj hv' (ptrans h1 h2)).
Qed.

Definition symStart : SymState := mkSymState S0 [slt110 (mkLF 1%Z 0%Z 0%Z 0%Z); slb1] [].
Definition symEnd : SymState := mkSymState S0 [slt110 (mkLF 256%Z 0%Z (-180)%Z 54%Z); slb1] [].

Definition symRun642 (s : SymState) : option SymState :=
  optBind (optBind (symIterPow2 9 s) (symIterPow2 7)) (symIterPow2 1).

Lemma symRun642_eq : symRun642 symStart = Some symEnd.
Proof. vm_compute. reflexivity. Qed.

Lemma cycle_642 {m vn : nat} (hinv : Inv m vn) :
  attractorCfg vn -->+ attractorCfg (256 * vn + 54 - 180 * m).
Proof.
  assert (hNpos : 1 <= vn).
  { destruct hinv as [hm10 [_ [_ [hlo _]]]].
    pose proof (sum4_lower_Z m hm10). lia. }
  assert (hge : 180 * m <= 256 * vn).
  { destruct hinv as [hm10 [_ [_ [hlo _]]]].
    pose proof (sum4_lower_Z m hm10). lia. }
  assert (hv0 : validSym m vn symStart).
  { unfold validSym, symStart; cbn [sst_l sst_r validL validR].
    unfold evalLF; cbn [lf_aN lf_aQ lf_am lf_ac].
    split; [split; [lia | exact I] | exact I]. }
  pose proof symRun642_eq as H.
  unfold symRun642 in H.
  destruct (symIterPow2 9 symStart) as [s1 |] eqn:E1; [| discriminate].
  cbn [optBind] in H.
  destruct (symIterPow2 7 s1) as [s2 |] eqn:E2; [| discriminate].
  cbn [optBind] in H.
  destruct (symIterPow2_sound hinv 9 symStart s1 hv0 E1) as [hv1 h1].
  destruct (symIterPow2_sound hinv 7 s1 s2 hv1 E2) as [hv2 h2].
  destruct (symIterPow2_sound hinv 1 s2 symEnd hv2 H) as [_ h3].
  pose proof (ptrans h1 (ptrans h2 h3)) as hall.
  assert (hstart_eq : evalSym m vn symStart = attractorCfg vn).
  { unfold evalSym, symStart, attractorCfg; cbn [sst_hd sst_l sst_r exSL exSR].
    assert (hN : evalLFNat m vn (mkLF 1%Z 0%Z 0%Z 0%Z) = vn)
      by (unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; lia).
    rewrite hN. reflexivity. }
  assert (hend_eq : evalSym m vn symEnd = attractorCfg (256 * vn + 54 - 180 * m)).
  { unfold evalSym, symEnd, attractorCfg; cbn [sst_hd sst_l sst_r exSL exSR].
    assert (hN' : evalLFNat m vn (mkLF 256%Z 0%Z (-180)%Z 54%Z) = 256 * vn + 54 - 180 * m)
      by (unfold evalLFNat, evalLF; cbn [lf_aN lf_aQ lf_am lf_ac]; lia).
    rewrite hN'. reflexivity. }
  rewrite hstart_eq, hend_eq in hall.
  exact hall.
Qed.

(* ========================================================================== *)
(* Top-Level Attractor Invariant & Non-Halting Theorem                        *)
(* ========================================================================== *)

Definition InAttractor (cfg : Q * tape) : Prop :=
  exists m vn : nat, Inv m vn /\ cfg = attractorCfg vn.

Lemma attractor_closed : forall cfg, InAttractor cfg -> exists cfg', InAttractor cfg' /\ cfg -->+ cfg'.
Proof.
  intros _ [m [vn [hinv ->]]].
  exists (attractorCfg (256 * vn + 54 - 180 * m)).
  split.
  - exists (m + 4), (256 * vn + 54 - 180 * m).
    exact (conj (inv_step hinv) eq_refl).
  - exact (cycle_642 hinv).
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init_reaches_N0 |].
  eapply (progress_nonhalt tm InAttractor); [exact attractor_closed |].
  exists 136, (N.to_nat N_init).
  exact (conj inv_init_N0 eq_refl).
Qed.
