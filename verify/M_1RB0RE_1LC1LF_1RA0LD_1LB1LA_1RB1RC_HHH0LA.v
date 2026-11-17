(** * BB(6) Holdout 608:#300 / 797:#395: 1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA *)

From BusyCoq Require Import Individual62.
From Coq Require Import String Bool Lists.List Arith Lia PArith.
Import ListNotations.

Definition tm : TM := TM_from_str "1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA"%string.

Module M300_Internal.

Local Close Scope sym_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Notation lb0 := (const S0).

(** ** 1. Division-Free Parity/Halving & Tape Block Encodings *)

Fixpoint nat_ind2 (P : nat -> Prop)
    (H0 : P 0) (H1 : P 1) (HS : forall n, P n -> P (S (S n))) (n : nat) : P n :=
  match n with
  | 0 => H0
  | 1 => H1
  | S (S n') => HS n' (nat_ind2 P H0 H1 HS n')
  end.

Fixpoint halfN (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n') => S (halfN n')
  end.

Fixpoint evenN (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n') => evenN n'
  end.

Lemma halfN_evenN_spec (n : nat) :
  n = 2 * halfN n + (if evenN n then 0 else 1).
Proof.
  induction n as [| | n IH] using nat_ind2; cbn [halfN evenN].
  - reflexivity.
  - reflexivity.
  - lia.
Qed.

Lemma halfN_unique (n q : nat) (b : bool) :
  n = 2 * q + (if b then 0 else 1) ->
  halfN n = q /\ evenN n = b.
Proof.
  intro H.
  pose proof (halfN_evenN_spec n) as Hspec.
  destruct (evenN n), b; split; try reflexivity; lia.
Qed.

Lemma lb_zero_cons : S0 >> lb0 = lb0.
Proof.
  rewrite <- const_unfold.
  reflexivity.
Qed.

Fixpoint enc0 (n : nat) (lb : side) : side :=
  match n with
  | 0 => lb
  | S n' => S0 >> enc0 n' lb
  end.

Fixpoint enc1 (n : nat) (lb : side) : side :=
  match n with
  | 0 => lb
  | S n' => S1 >> enc1 n' lb
  end.

Fixpoint encW (n : nat) (lb : side) : side :=
  match n with
  | 0 => lb
  | S n' => S1 >> S1 >> S0 >> encW n' lb
  end.

Lemma enc0_add (m n : nat) (lb : side) : enc0 (m + n) lb = enc0 m (enc0 n lb).
Proof.
  induction m as [| m IH]; cbn [Nat.add enc0]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma enc1_add (m n : nat) (lb : side) : enc1 (m + n) lb = enc1 m (enc1 n lb).
Proof.
  induction m as [| m IH]; cbn [Nat.add enc1]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma encW_add (m n : nat) (lb : side) : encW (m + n) lb = encW m (encW n lb).
Proof.
  induction m as [| m IH]; cbn [Nat.add encW]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma enc0_succ (n : nat) (lb : side) : enc0 (n + 1) lb = S0 >> enc0 n lb.
Proof.
  replace (n + 1) with (S n) by lia.
  reflexivity.
Qed.

Lemma enc1_succ (n : nat) (lb : side) : enc1 (n + 1) lb = S1 >> enc1 n lb.
Proof.
  replace (n + 1) with (S n) by lia.
  reflexivity.
Qed.

Lemma encW_succ (n : nat) (lb : side) : encW (n + 1) lb = S1 >> S1 >> S0 >> encW n lb.
Proof.
  replace (n + 1) with (S n) by lia.
  reflexivity.
Qed.

Lemma enc0_lb0 (n : nat) : enc0 n lb0 = lb0.
Proof.
  induction n as [| n IH]; cbn [enc0]; [reflexivity | rewrite IH, lb_zero_cons; reflexivity].
Qed.

Lemma encW_snoc (n : nat) (lb : side) :
  encW n (S1 >> S1 >> S0 >> lb) = S1 >> S1 >> S0 >> encW n lb.
Proof.
  change (S1 >> S1 >> S0 >> lb) with (encW 1 lb).
  rewrite <- encW_add.
  replace (n + 1) with (S n) by lia.
  reflexivity.
Qed.

Lemma encW_snoc_add (n : nat) (lb : side) :
  encW n (S1 >> S1 >> S0 >> lb) = encW (n + 1) lb.
Proof.
  change (S1 >> S1 >> S0 >> lb) with (encW 1 lb).
  rewrite <- encW_add.
  reflexivity.
Qed.

Lemma encW_snoc2_add (n : nat) (lb : side) :
  encW n (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> lb) = encW (n + 2) lb.
Proof.
  change (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> lb) with (encW 2 lb).
  rewrite <- encW_add.
  reflexivity.
Qed.

Lemma encW_2_plus (n : nat) (lb : side) :
  encW (n + 2) lb = S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> encW n lb.
Proof.
  replace (n + 2) with (S (S n)) by lia.
  reflexivity.
Qed.

Lemma encW_pos (n : nat) (lb : side) :
  1 <= n -> S1 >> S1 >> S0 >> encW (n - 1) lb = encW n lb.
Proof.
  destruct n as [| n']; [lia | intro; replace (S n' - 1) with n' by lia; reflexivity].
Qed.

(** ** 2. Reachability Combinators & 11 Elementary Micro-Rules *)

Lemma to_star {c1 c2 : Q * tape} (H : c1 -[ tm ]->+ c2) : c1 -[ tm ]->* c2.
Proof. exact (progress_evstep tm c1 c2 H). Qed.

Lemma stepStar_trans {c1 c2 c3 : Q * tape}
    (H1 : c1 -[ tm ]->* c2) (H2 : c2 -[ tm ]->* c3) : c1 -[ tm ]->* c3.
Proof. exact (evstep_trans tm c1 c2 c3 H1 H2). Qed.

Lemma stepPlus_trans {c1 c2 c3 : Q * tape}
    (H1 : c1 -[ tm ]->+ c2) (H2 : c2 -[ tm ]->+ c3) : c1 -[ tm ]->+ c3.
Proof. exact (progress_trans tm c1 c2 c3 H1 H2). Qed.

Lemma stepStar_plus_trans {c1 c2 c3 : Q * tape}
    (H1 : c1 -[ tm ]->* c2) (H2 : c2 -[ tm ]->+ c3) : c1 -[ tm ]->+ c3.
Proof. exact (evstep_progress_trans tm c1 c2 c3 H1 H2). Qed.

Lemma stepPlus_star_trans {c1 c2 c3 : Q * tape}
    (H1 : c1 -[ tm ]->+ c2) (H2 : c2 -[ tm ]->* c3) : c1 -[ tm ]->+ c3.
Proof. exact (progress_evstep_trans tm c1 c2 c3 H1 H2). Qed.

Lemma micro_A_w1 (l r : side) :
  (l {{A}}> (S1 >> S1 >> S0 >> r)) -[ tm ]->+ ((S1 >> S1 >> S0 >> l) {{A}}> r).
Proof. intros. start_progress. Qed.

Lemma micro_C0_step (l r : side) :
  (l {{C}}> (S0 >> r)) -[ tm ]->+ ((S1 >> l) {{A}}> r).
Proof. intros. start_progress. Qed.

Lemma micro_f1_pp1 (l r : side) :
  ((S1 >> S1 >> S0 >> l) {{F}}> (S1 >> S1 >> r)) -[ tm ]->+
  (l {{F}}> (S1 >> S1 >> S0 >> S1 >> S1 >> r)).
Proof. intros. start_progress. Qed.

Lemma micro_P2 (l r : side) :
  ((S0 >> S1 >> S1 >> S0 >> l) {{F}}> (S1 >> r)) -[ tm ]->+
  ((S1 >> S1 >> S0 >> S0 >> l) {{A}}> (S1 >> r)).
Proof. intros. start_progress. Qed.

Lemma micro_P3 (l r : side) :
  (l {{A}}> (S1 >> S1 >> S1 >> r)) -[ tm ]->+
  (l {{F}}> (S1 >> S1 >> S0 >> r)).
Proof. intros. start_progress. Qed.

Lemma micro_P4 (l r : side) :
  ((S0 >> S0 >> S1 >> S1 >> S0 >> l) {{F}}> (S1 >> r)) -[ tm ]->+
  ((S0 >> l) {{F}}> (S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof. intros. start_progress. Qed.

Lemma micro_A0_B1 (l r : side) :
  (l {{A}}> (S0 >> S1 >> r)) -[ tm ]->+
  (l {{F}}> (S1 >> S1 >> r)).
Proof. intros. start_progress. Qed.

Lemma micro_B1_0 (l r : side) :
  ((S0 >> S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> l) {{F}}> (S1 >> S1 >> r))
  -[ tm ]->+
  ((S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S0 >> l) {{F}}> (S1 >> S1 >> S1 >> r)).
Proof. intros. start_progress. Qed.

Lemma micro_B3_tail (l r : side) :
  ((S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> l) {{A}}> (S0 >> S0 >> S1 >> S1 >> S0 >> S1 >> r))
  -[ tm ]->+
  ((S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S0 >> l) {{F}}> (S1 >> S1 >> r)).
Proof. intros. start_progress. Qed.

Lemma micro_B2_tail (l r : side) :
  ((S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> l) {{A}}> (S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> r))
  -[ tm ]->+
  ((S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S0 >> l) {{F}}> (S1 >> S1 >> r)).
Proof. intros. start_progress. Qed.

Lemma micro_J3B_bounce_gen (l r : side) :
  ((S1 >> S0 >> S0 >> S0 >> l) {{F}}> (S1 >> S1 >> r)) -[ tm ]->+
  ((S1 >> S1 >> S0 >> S1 >> l) {{A}}> (S1 >> S1 >> r)).
Proof. intros. start_progress. Qed.

(** ** 3. Level-2, Level-3, and Clean-Loop Macro Transitions *)

Lemma sweep_A_w (n : nat) : forall (l r : side),
  (l {{A}}> encW n r) -[ tm ]->* ((encW n l) {{A}}> r).
Proof.
  induction n as [| n IH]; intros l r; cbn [encW].
  - apply evstep_refl.
  - pose proof (to_star (micro_A_w1 l (encW n r))) as H1.
    pose proof (IH (S1 >> S1 >> S0 >> l) r) as H2.
    pose proof (stepStar_trans H1 H2) as H3.
    rewrite encW_snoc in H3.
    exact H3.
Qed.

Lemma rule_wR_C0 (c : nat) (l r : side) :
  (l {{C}}> (S0 >> encW c r)) -[ tm ]->+ ((encW c (S1 >> l)) {{A}}> r).
Proof.
  exact (stepPlus_star_trans (micro_C0_step l (encW c r)) (sweep_A_w c (S1 >> l) r)).
Qed.

Lemma rule_wR_A1 (c : nat) (l r : side) :
  (l {{A}}> (S1 >> S1 >> S0 >> encW c r)) -[ tm ]->+ ((encW (c + 1) l) {{A}}> r).
Proof.
  pose proof (stepPlus_star_trans (micro_A_w1 l (encW c r)) (sweep_A_w c (S1 >> S1 >> S0 >> l) r)) as H.
  rewrite encW_snoc_add in H.
  exact H.
Qed.

Lemma rule_f1_pp (a : nat) : forall (l r : side),
  ((encW a l) {{F}}> (S1 >> S1 >> S0 >> r)) -[ tm ]->* (l {{F}}> (S1 >> S1 >> S0 >> encW a r)).
Proof.
  induction a as [| a IH]; intros l r; cbn [encW].
  - apply evstep_refl.
  - pose proof (to_star (micro_f1_pp1 (encW a l) (S0 >> r))) as H1.
    pose proof (IH l (S1 >> S1 >> S0 >> r)) as H2.
    pose proof (stepStar_trans H1 H2) as H3.
    rewrite encW_snoc in H3.
    exact H3.
Qed.

Lemma rule_f1_pp_any1 (a : nat) (l r : side) :
  ((encW (a + 1) l) {{F}}> (S1 >> S1 >> r)) -[ tm ]->+
  (l {{F}}> (S1 >> S1 >> S0 >> encW a (S1 >> S1 >> r))).
Proof.
  rewrite encW_succ.
  exact (stepPlus_star_trans (micro_f1_pp1 (encW a l) r) (rule_f1_pp a l (S1 >> S1 >> r))).
Qed.

Lemma rule_P1 (a : nat) (l r : side) :
  ((encW a (S0 >> S1 >> S1 >> S0 >> l)) {{F}}> (S1 >> S1 >> S0 >> r)) -[ tm ]->+
  ((encW (a + 2) (S0 >> l)) {{A}}> r).
Proof.
  pose proof (rule_f1_pp a (S0 >> S1 >> S1 >> S0 >> l) r) as H1.
  pose proof (micro_P2 l (S1 >> S0 >> encW a r)) as H2.
  pose proof (to_star (micro_A_w1 (S1 >> S1 >> S0 >> S0 >> l) (encW a r))) as H3.
  pose proof (sweep_A_w a (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S0 >> l) r) as H4.
  pose proof (stepPlus_star_trans (stepStar_plus_trans H1 H2) (stepStar_trans H3 H4)) as H5.
  rewrite encW_snoc2_add in H5.
  exact H5.
Qed.

Lemma rule_HC1_gen (a : nat) (l r : side) :
  ((encW a (S0 >> S1 >> S1 >> S0 >> l)) {{F}}> (S1 >> S1 >> S1 >> r)) -[ tm ]->+
  ((encW (a + 1) (S0 >> l)) {{F}}> (S1 >> S1 >> S0 >> r)).
Proof.
  destruct a as [| a'].
  - cbn [Nat.add encW].
    exact (stepPlus_star_trans (micro_P2 l (S1 >> S1 >> r))
             (to_star (micro_P3 (S1 >> S1 >> S0 >> S0 >> l) r))).
  - replace (S a') with (a' + 1) by lia.
    pose proof (rule_f1_pp_any1 a' (S0 >> S1 >> S1 >> S0 >> l) (S1 >> r)) as H1.
    pose proof (to_star (micro_P2 l (S1 >> S0 >> encW a' (S1 >> S1 >> S1 >> r)))) as H2.
    pose proof (to_star (micro_A_w1 (S1 >> S1 >> S0 >> S0 >> l) (encW a' (S1 >> S1 >> S1 >> r)))) as H3.
    pose proof (sweep_A_w a' (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S0 >> l) (S1 >> S1 >> S1 >> r)) as H4.
    rewrite encW_snoc2_add in H4.
    replace (a' + 2) with (a' + 1 + 1) in H4 by lia.
    pose proof (to_star (micro_P3 (encW (a' + 1 + 1) (S0 >> l)) r)) as H5.
    exact (stepPlus_star_trans H1 (stepStar_trans H2 (stepStar_trans H3 (stepStar_trans H4 H5)))).
Qed.

Lemma rule_HC2 (a : nat) (l r : side) :
  ((encW a (S0 >> S1 >> S1 >> S0 >> l)) {{F}}> (S1 >> S1 >> S0 >> S0 >> S1 >> r)) -[ tm ]->+
  ((encW (a + 2) (S0 >> l)) {{F}}> (S1 >> S1 >> r)).
Proof.
  exact (stepPlus_star_trans (rule_P1 a l (S0 >> S1 >> r))
           (to_star (micro_A0_B1 (encW (a + 2) (S0 >> l)) r))).
Qed.

Lemma rule_J3A_1 (a : nat) (l r : side) :
  ((encW a (S0 >> encW 2 l)) {{F}}> (S1 >> encW 1 (S1 >> r))) -[ tm ]->+
  ((encW (a + 3) (S0 >> l)) {{F}}> (S1 >> S1 >> r)).
Proof.
  cbn [encW].
  pose proof (rule_HC1_gen a (S1 >> S1 >> S0 >> l) (S0 >> S1 >> r)) as H1.
  pose proof (rule_HC2 (a + 1) l r) as H2.
  pose proof (stepPlus_trans H1 H2) as H3.
  replace (a + 1 + 2) with (a + 3) in H3 by lia.
  exact H3.
Qed.

Lemma rule_J3A (k : nat) : forall (a : nat) (l r : side),
  ((encW a (S0 >> encW (2 * k) l)) {{F}}> (S1 >> encW k (S1 >> r))) -[ tm ]->*
  ((encW (a + 3 * k) (S0 >> l)) {{F}}> (S1 >> S1 >> r)).
Proof.
  induction k as [| k IH]; intros a l r.
  - replace (2 * 0) with 0 by lia.
    replace (a + 3 * 0) with a by lia.
    cbn [encW].
    apply evstep_refl.
  - replace (2 * S k) with (2 + 2 * k) by lia.
    replace (S k) with (1 + k) at 1 by lia.
    rewrite encW_add, encW_add.
    set (rTail := match k with 0 => r | S k' => S1 >> S0 >> encW k' (S1 >> r) end).
    assert (HR1 : encW k (S1 >> r) = S1 >> rTail).
    { destruct k as [| k']; reflexivity. }
    pose proof (to_star (rule_J3A_1 a (encW (2 * k) l) rTail)) as H1.
    rewrite <- HR1 in H1.
    pose proof (stepStar_trans H1 (IH (a + 3) l r)) as H2.
    replace (a + 3 + 3 * k) with (a + 3 * S k) in H2 by lia.
    exact H2.
Qed.

Lemma rule_B1 (a : nat) (l r : side) :
  ((encW a (S0 >> S0 >> encW 3 l)) {{F}}> (S1 >> S1 >> r)) -[ tm ]->+
  ((encW 3 (S0 >> l)) {{F}}> (S1 >> encW a (S1 >> S1 >> r))).
Proof.
  destruct a as [| a'].
  - cbn [encW].
    exact (micro_B1_0 l r).
  - replace (S a') with (a' + 1) by lia.
    pose proof (rule_f1_pp_any1 a' (S0 >> S0 >> encW 3 l) r) as H1.
    pose proof (to_star (micro_B1_0 l (S0 >> encW a' (S1 >> S1 >> r)))) as H2.
    change (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> l) with (encW 3 l) in H2.
    change (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S0 >> l) with (encW 3 (S0 >> l)) in H2.
    pose proof (stepPlus_star_trans H1 H2) as H3.
    rewrite <- encW_succ in H3.
    exact H3.
Qed.

Lemma rule_B3 (a : nat) (l r : side) :
  ((encW a (S0 >> S1 >> S1 >> S0 >> l)) {{F}}> (S1 >> S1 >> S0 >> S0 >> S0 >> S1 >> S1 >> S0 >> S1 >> r))
  -[ tm ]->+
  ((encW 3 (S0 >> encW a (S0 >> l))) {{F}}> (S1 >> S1 >> r)).
Proof.
  pose proof (rule_P1 a l (S0 >> S0 >> S1 >> S1 >> S0 >> S1 >> r)) as H1.
  rewrite encW_2_plus in H1.
  pose proof (to_star (micro_B3_tail (encW a (S0 >> l)) r)) as H2.
  exact (stepPlus_star_trans H1 H2).
Qed.

Lemma rule_B2 (a : nat) (l r : side) :
  ((encW a (S0 >> encW 2 l)) {{F}}> (S1 >> S1 >> encW 2 (S1 >> r))) -[ tm ]->+
  ((encW 3 (S0 >> encW (a + 1) (S0 >> l))) {{F}}> (S1 >> S1 >> r)).
Proof.
  cbn [encW].
  pose proof (rule_HC1_gen a (S1 >> S1 >> S0 >> l) (S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> r)) as H1.
  pose proof (rule_P1 (a + 1) l (S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> r)) as H2.
  rewrite encW_2_plus in H2.
  pose proof (to_star (micro_B2_tail (encW (a + 1) (S0 >> l)) r)) as H3.
  exact (stepPlus_star_trans (stepPlus_trans H1 H2) H3).
Qed.

Lemma micro_J3B_bounce (r : side) :
  ((S1 >> lb0) {{F}}> (S1 >> S1 >> r)) -[ tm ]->+
  ((S1 >> S1 >> S0 >> S1 >> lb0) {{A}}> (S1 >> S1 >> r)).
Proof.
  pose proof (micro_J3B_bounce_gen lb0 r) as H.
  rewrite lb_zero_cons, lb_zero_cons, lb_zero_cons in H.
  exact H.
Qed.

Lemma rule_J3B_h1 (a : nat) (r : side) :
  ((encW a (S1 >> lb0)) {{F}}> (S1 >> S1 >> S1 >> r)) -[ tm ]->+
  ((encW (a + 1) (S1 >> lb0)) {{F}}> (S1 >> S1 >> S0 >> r)).
Proof.
  destruct a as [| a'].
  - cbn [Nat.add encW].
    exact (stepPlus_star_trans (micro_J3B_bounce (S1 >> r))
             (to_star (micro_P3 (S1 >> S1 >> S0 >> S1 >> lb0) r))).
  - replace (S a') with (a' + 1) by lia.
    pose proof (rule_f1_pp_any1 a' (S1 >> lb0) (S1 >> r)) as H1.
    pose proof (to_star (micro_J3B_bounce (S0 >> encW a' (S1 >> S1 >> S1 >> r)))) as H2.
    pose proof (to_star (micro_A_w1 (S1 >> S1 >> S0 >> S1 >> lb0) (encW a' (S1 >> S1 >> S1 >> r)))) as H3.
    pose proof (sweep_A_w a' (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> lb0) (S1 >> S1 >> S1 >> r)) as H4.
    rewrite encW_snoc2_add in H4.
    replace (a' + 2) with (a' + 1 + 1) in H4 by lia.
    pose proof (to_star (micro_P3 (encW (a' + 1 + 1) (S1 >> lb0)) r)) as H5.
    exact (stepPlus_star_trans H1 (stepStar_trans H2 (stepStar_trans H3 (stepStar_trans H4 H5)))).
Qed.

Lemma rule_J3B_h2 (a : nat) (r : side) :
  ((encW a (S1 >> lb0)) {{F}}> (S1 >> S1 >> S0 >> S0 >> S1 >> r)) -[ tm ]->+
  ((encW (a + 2) (S1 >> lb0)) {{F}}> (S1 >> S1 >> r)).
Proof.
  pose proof (rule_f1_pp a (S1 >> lb0) (S0 >> S1 >> r)) as H1.
  pose proof (micro_J3B_bounce (S0 >> encW a (S0 >> S1 >> r))) as H2.
  pose proof (to_star (micro_A_w1 (S1 >> S1 >> S0 >> S1 >> lb0) (encW a (S0 >> S1 >> r)))) as H3.
  pose proof (sweep_A_w a (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> lb0) (S0 >> S1 >> r)) as H4.
  rewrite encW_snoc2_add in H4.
  pose proof (to_star (micro_A0_B1 (encW (a + 2) (S1 >> lb0)) r)) as H5.
  exact (stepPlus_star_trans (stepStar_plus_trans H1 H2) (stepStar_trans H3 (stepStar_trans H4 H5))).
Qed.

Lemma rule_J3B_1 (a : nat) (r : side) :
  ((encW a (S1 >> lb0)) {{F}}> (S1 >> encW 1 (S1 >> r))) -[ tm ]->+
  ((encW (a + 3) (S1 >> lb0)) {{F}}> (S1 >> S1 >> r)).
Proof.
  cbn [encW].
  pose proof (stepPlus_trans (rule_J3B_h1 a (S0 >> S1 >> r)) (rule_J3B_h2 (a + 1) r)) as H.
  replace (a + 1 + 2) with (a + 3) in H by lia.
  exact H.
Qed.

Lemma rule_J3B (k : nat) : forall (a : nat) (r : side),
  ((encW a (S1 >> lb0)) {{F}}> (S1 >> encW k (S1 >> r))) -[ tm ]->*
  ((encW (a + 3 * k) (S1 >> lb0)) {{F}}> (S1 >> S1 >> r)).
Proof.
  induction k as [| k IH]; intros a r.
  - replace (a + 3 * 0) with a by lia.
    cbn [encW].
    apply evstep_refl.
  - replace (S k) with (1 + k) at 1 by lia.
    rewrite encW_add.
    set (rTail := match k with 0 => r | S k' => S1 >> S0 >> encW k' (S1 >> r) end).
    assert (HR1 : encW k (S1 >> r) = S1 >> rTail).
    { destruct k as [| k']; reflexivity. }
    pose proof (to_star (rule_J3B_1 a rTail)) as H1.
    rewrite <- HR1 in H1.
    pose proof (stepStar_trans H1 (IH (a + 3) r)) as H2.
    replace (a + 3 + 3 * k) with (a + 3 * S k) in H2 by lia.
    exact H2.
Qed.

Lemma clean_B1_even (b0 b1 c0 : nat) (sl rt : side)
    (Hrem : evenN b0 = true) (Hb1 : 4 <= b1) (Hc0 : halfN b0 + 1 <= c0) :
  ((encW 3 (S0 >> encW b0 (S0 >> encW b1 sl))) {{F}}> (S1 >> encW c0 rt)) -[ tm ]->*
  ((encW 3 (S0 >> encW (b1 - 3) sl)) {{F}}>
    (S1 >> encW (3 + 3 * halfN b0) (S1 >> encW (c0 - halfN b0) rt))).
Proof.
  pose proof (halfN_evenN_spec b0) as Hb0_spec.
  rewrite Hrem in Hb0_spec.
  set (q := halfN b0) in *.
  assert (Hb0 : b0 = 2 * q) by lia.
  assert (Hb1_eq : b1 = 3 + (b1 - 3)) by lia.
  assert (Hc0_eq : c0 = q + (c0 - q)) by lia.
  assert (HR_in : S1 >> S1 >> S0 >> encW (c0 - q - 1) rt = encW (c0 - q) rt) by (apply encW_pos; lia).
  pose proof (rule_J3A q 3 (S0 >> encW b1 sl) (S1 >> S0 >> encW (c0 - q - 1) rt)) as H1.
  rewrite HR_in in H1.
  rewrite <- Hb0 in H1.
  rewrite <- encW_add, <- Hc0_eq in H1.
  pose proof (to_star (rule_B1 (3 + 3 * q) (encW (b1 - 3) sl) (S1 >> S0 >> encW (c0 - q - 1) rt))) as H2.
  rewrite <- encW_add, <- Hb1_eq, HR_in in H2.
  exact (stepStar_trans H1 H2).
Qed.

Lemma clean_B1_odd (b0 b1 c0 : nat) (sl rt : side)
    (Hrem : evenN b0 = false) (Hb1 : 4 <= b1) (Hc0 : halfN b0 + 2 <= c0) :
  ((encW 3 (S0 >> encW b0 (S0 >> encW b1 sl))) {{F}}> (S1 >> encW c0 rt)) -[ tm ]->*
  ((encW 3 (S0 >> encW (b1 - 3) sl)) {{F}}>
    (S1 >> encW (5 + 3 * halfN b0) (S0 >> encW (c0 - (halfN b0 + 1)) rt))).
Proof.
  pose proof (halfN_evenN_spec b0) as Hb0_spec.
  rewrite Hrem in Hb0_spec.
  set (q := halfN b0) in *.
  assert (Hb0 : b0 = 2 * q + 1) by lia.
  assert (Hb1_eq : b1 = 3 + (b1 - 3)) by lia.
  assert (Hc0_eq : c0 = q + 1 + (c0 - (q + 1))) by lia.
  pose proof (rule_J3A q 3 (encW 1 (S0 >> encW b1 sl)) (S1 >> S0 >> encW (c0 - (q + 1)) rt)) as H1.
  rewrite <- encW_add, <- Hb0 in H1.
  rewrite encW_snoc_add in H1.
  rewrite <- encW_add, <- Hc0_eq in H1.
  pose proof (to_star (rule_HC1_gen (3 + 3 * q) (S0 >> encW b1 sl) (S0 >> encW (c0 - (q + 1)) rt))) as H2.
  pose proof (to_star (rule_B1 (3 + 3 * q + 1) (encW (b1 - 3) sl) (S0 >> S0 >> encW (c0 - (q + 1)) rt))) as H3.
  rewrite <- encW_add, <- Hb1_eq in H3.
  rewrite encW_snoc_add in H3.
  replace (3 + 3 * q + 1 + 1) with (5 + 3 * q) in H3 by lia.
  exact (stepStar_trans H1 (stepStar_trans H2 H3)).
Qed.

Lemma clean_B23_c1 (b0 c0 c1 : nat) (sl rt : side)
    (Hb0 : 2 * c0 + 3 <= b0) (Hc1 : 3 <= c1) :
  ((encW 3 (S0 >> encW b0 sl)) {{F}}> (S1 >> encW c0 (S1 >> encW c1 rt))) -[ tm ]->*
  ((encW 3 (S0 >> encW (4 + 3 * c0) (S0 >> encW (b0 - (2 * c0 + 2)) sl))) {{F}}>
    (S1 >> encW (c1 - 2) rt)).
Proof.
  assert (Hb0_eq : b0 = 2 * c0 + 2 + (b0 - (2 * c0 + 2))) by lia.
  assert (Hc1_eq : c1 = 2 + (c1 - 2)) by lia.
  pose proof (rule_J3A c0 3 (encW 2 (encW (b0 - (2 * c0 + 2)) sl)) (encW 2 (encW (c1 - 2) rt))) as H1.
  rewrite <- encW_add, <- encW_add, <- Hb0_eq in H1.
  rewrite <- encW_add, <- Hc1_eq in H1.
  pose proof (to_star (rule_B2 (3 + 3 * c0) (encW (b0 - (2 * c0 + 2)) sl) (S1 >> S0 >> encW (c1 - 3) rt))) as H2.
  assert (HR_tail : S1 >> S1 >> S0 >> encW (c1 - 3) rt = encW (c1 - 2) rt).
  { replace (c1 - 3) with (c1 - 2 - 1) by lia. apply encW_pos; lia. }
  rewrite HR_tail in H2.
  replace (encW 2 (encW (c1 - 2) rt)) with (encW c1 rt) in H2 by (rewrite <- encW_add, <- Hc1_eq; reflexivity).
  replace (3 + 3 * c0 + 1) with (4 + 3 * c0) in H2 by lia.
  exact (stepStar_trans H1 H2).
Qed.

Lemma clean_B23_c0 (b0 c0 c1 : nat) (sl rt : side)
    (Hc0 : 1 <= c0) (Hb0 : 2 * c0 + 1 <= b0) (Hc1 : 2 <= c1) :
  ((encW 3 (S0 >> encW b0 sl)) {{F}}> (S1 >> encW c0 (S0 >> encW c1 rt))) -[ tm ]->*
  ((encW 3 (S0 >> encW (1 + 3 * c0) (S0 >> encW (b0 - 2 * c0) sl))) {{F}}>
    (S1 >> encW (c1 - 1) rt)).
Proof.
  set (c0' := c0 - 1).
  assert (Hc0_eq : c0 = c0' + 1) by lia.
  assert (Hb0_eq : b0 = 2 * c0' + 1 + 1 + (b0 - 2 * c0)) by lia.
  assert (Hc1_eq : c1 = 1 + (c1 - 1)) by lia.
  pose proof (rule_J3A c0' 3 (encW 1 (encW 1 (encW (b0 - 2 * c0) sl)))
                (S1 >> S0 >> S0 >> encW 1 (encW (c1 - 1) rt))) as H1.
  rewrite <- encW_add, <- encW_add, <- encW_add, <- Hb0_eq in H1.
  rewrite encW_snoc_add in H1.
  rewrite <- Hc0_eq, <- encW_add, <- Hc1_eq in H1.
  pose proof (to_star (rule_HC1_gen (3 + 3 * c0') (encW 1 (encW (b0 - 2 * c0) sl))
                (S0 >> S0 >> encW 1 (encW (c1 - 1) rt)))) as H2.
  assert (HR_tail : S1 >> S1 >> S0 >> encW (c1 - 2) rt = encW (c1 - 1) rt).
  { replace (c1 - 2) with (c1 - 1 - 1) by lia. apply encW_pos; lia. }
  pose proof (to_star (rule_B3 (3 + 3 * c0' + 1) (encW (b0 - 2 * c0) sl)
                (S1 >> S0 >> encW (c1 - 2) rt))) as H3.
  rewrite HR_tail in H3.
  replace (3 + 3 * c0' + 1) with (1 + 3 * c0) in H2, H3 by lia.
  pose proof (stepStar_trans H2 H3) as H23.
  replace (encW 1 (encW (c1 - 1) rt)) with (encW c1 rt) in H23 by (rewrite <- encW_add, <- Hc1_eq; reflexivity).
  exact (stepStar_trans H1 H23).
Qed.

(** ** 4. Reference [nat] Hybrid State & Stepper ([HybStateN], [stepOuterN]) *)

Inductive Q_st : Type := QA | QB | QC | QD | QE | QF.

Definition qToQ (q : Q_st) : Q :=
  match q with
  | QA => A | QB => B | QC => C | QD => D | QE => E | QF => F
  end.

Definition bitToSym (b : bool) : Sym := if b then S1 else S0.

Inductive TokN : Type :=
  | TokZN (n : nat)
  | TokON (n : nat)
  | TokWN (n : nat).

Inductive LStackN : Type :=
  | LNilN
  | LCN (b : nat) (tl : LStackN)
  | LTokN (t : TokN) (tl : LStackN).

Inductive RStackN : Type :=
  | RNilN
  | RCN (is1 : bool) (c : nat) (tl : RStackN)
  | RTokN (t : TokN) (tl : RStackN).

Inductive HybStateN : Type :=
  | HCleanN (sL : LStackN) (sR : RStackN)
  | HGenN (q : Q_st) (h : bool) (bL : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN).

Definition encTokN (t : TokN) (lb : side) : side :=
  match t with
  | TokZN n => enc0 n lb
  | TokON n => enc1 n lb
  | TokWN n => encW n lb
  end.

Fixpoint encToksN (ts : list TokN) (lb : side) : side :=
  match ts with
  | [] => lb
  | t :: rest => encTokN t (encToksN rest lb)
  end.

Lemma encToksN_app (xs ys : list TokN) (lb : side) :
  encToksN (xs ++ ys) lb = encToksN xs (encToksN ys lb).
Proof.
  induction xs as [| x xs IH]; cbn [List.app encToksN]; [reflexivity | rewrite IH; reflexivity].
Qed.

Fixpoint encLN (sL : LStackN) : side :=
  match sL with
  | LNilN => lb0
  | LCN b tl => S0 >> encW b (encLN tl)
  | LTokN t tl => encTokN t (encLN tl)
  end.

Fixpoint encRN (sR : RStackN) : side :=
  match sR with
  | RNilN => lb0
  | RCN b c tl => encW c (bitToSym b >> encRN tl)
  | RTokN t tl => encTokN t (encRN tl)
  end.

Definition encHybN (s : HybStateN) : Q * tape :=
  match s with
  | HCleanN sL sR => (encW 3 (encLN sL)) {{F}}> (S1 >> encRN sR)
  | HGenN q h bL rL bR rR =>
    (encToksN bL (encLN rL)) {{qToQ q}}> (bitToSym h >> encToksN bR (encRN rR))
  end.

Definition isZeroN (n : nat) : bool := Nat.eqb n 0.
Definition isOneN (n : nat) : bool := Nat.eqb n 1.
Definition isTwoN (n : nat) : bool := Nat.eqb n 2.
Definition isThreeN (n : nat) : bool := Nat.eqb n 3.
Definition lebN (x y : nat) : bool := Nat.leb x y.
Definition eqbN (x y : nat) : bool := Nat.eqb x y.
Definition oddN (n : nat) : bool := negb (evenN n).
Definition mul3addcN (c x : nat) : nat := 3 * x + c.

Fixpoint runCleanLoopN (steps : nat) (b0 : nat) (lt : LStackN) (isC1 : bool) (c0 : nat) (rt : RStackN) : HybStateN :=
  match steps with
  | O => HCleanN (LCN b0 lt) (RCN isC1 c0 rt)
  | S steps' =>
    let diff := b0 - 2 * c0 in
    if isZeroN diff then
      match lt with
      | LCN b1 lt2 =>
        let nb1 := b1 - 3 in
        if isZeroN nb1 then HGenN QF true [TokWN 3] (LCN b0 lt) [] (RCN isC1 c0 rt)
        else
          if evenN b0 then
            let nc0 := c0 - halfN b0 in
            if isZeroN nc0 then HGenN QF true [TokWN 3] (LCN b0 lt) [] (RCN isC1 c0 rt)
            else runCleanLoopN steps' nb1 lt2 true (mul3addcN 3 (halfN b0)) (RCN isC1 nc0 rt)
          else
            let nc0 := c0 - (halfN b0 + 1) in
            if isZeroN nc0 then HGenN QF true [TokWN 3] (LCN b0 lt) [] (RCN isC1 c0 rt)
            else runCleanLoopN steps' nb1 lt2 false (mul3addcN 5 (halfN b0)) (RCN isC1 nc0 rt)
      | _ => HGenN QF true [TokWN 3] (LCN b0 lt) [] (RCN isC1 c0 rt)
      end
    else
      if isC1 then
        let nb0 := diff - 2 in
        if isZeroN nb0 then HGenN QF true [TokWN 3] (LCN b0 lt) [] (RCN true c0 rt)
        else
          match rt with
          | RCN t1 c1 rt2 =>
            let nc1 := c1 - 2 in
            if isZeroN nc1 then HGenN QF true [TokWN 3] (LCN b0 lt) [] (RCN true c0 rt)
            else runCleanLoopN steps' (mul3addcN 4 c0) (LCN nb0 lt) t1 nc1 rt2
          | _ => HGenN QF true [TokWN 3] (LCN b0 lt) [] (RCN true c0 rt)
          end
      else
        if isZeroN c0 then HGenN QF true [TokWN 3] (LCN b0 lt) [] (RCN false c0 rt)
        else
          match rt with
          | RCN t1 c1 rt2 =>
            let nc1 := c1 - 1 in
            if isZeroN nc1 then HGenN QF true [TokWN 3] (LCN b0 lt) [] (RCN false c0 rt)
            else runCleanLoopN steps' (mul3addcN 1 c0) (LCN diff lt) t1 nc1 rt2
          | _ => HGenN QF true [TokWN 3] (LCN b0 lt) [] (RCN false c0 rt)
          end
  end.

Definition runCleanChunkN (kc4 : nat) (sL : LStackN) (sR : RStackN) : HybStateN :=
  match sL, sR with
  | LCN b0 lt, RCN isC1 c0 rt => runCleanLoopN kc4 b0 lt isC1 c0 rt
  | _, _ => HGenN QF true [TokWN 3] sL [] sR
  end.

Definition pushTokN (t : TokN) (ts : list TokN) : list TokN :=
  match t with
  | TokZN 0 => ts
  | TokON 0 => ts
  | TokWN 0 => ts
  | TokZN a => match ts with TokZN b :: rest => TokZN (a + b) :: rest | _ => t :: ts end
  | TokON a => match ts with TokON b :: rest => TokON (a + b) :: rest | _ => t :: ts end
  | TokWN a => match ts with TokWN b :: rest => TokWN (a + b) :: rest | _ => t :: ts end
  end.

Fixpoint pushTokBackN (ts : list TokN) (t : TokN) : list TokN :=
  match ts with
  | [] => pushTokN t []
  | [t0] => pushTokN t0 (pushTokN t [])
  | t0 :: rest => t0 :: pushTokBackN rest t
  end.

Fixpoint stripEndZN (ts : list TokN) : list TokN :=
  match ts with
  | [] => []
  | t :: rest =>
    match stripEndZN rest with
    | [] => match t with TokZN _ => [] | _ => [t] end
    | rest' => t :: rest'
    end
  end.

Definition needPullN (ts : list TokN) : bool :=
  match ts with
  | _ :: _ :: _ :: _ :: _ => false
  | _ => true
  end.

Definition pullOneLN (bL : list TokN) (rL : LStackN) : list TokN * LStackN :=
  match rL with
  | LNilN => (stripEndZN bL, LNilN)
  | LCN b tl => (pushTokBackN (pushTokBackN bL (TokZN 1)) (TokWN b), tl)
  | LTokN t tl => (pushTokBackN bL t, tl)
  end.

Definition pullOneRN (bR : list TokN) (rR : RStackN) : list TokN * RStackN :=
  match rR with
  | RNilN => (stripEndZN bR, RNilN)
  | RCN false c tl => (pushTokBackN (pushTokBackN bR (TokWN c)) (TokZN 1), tl)
  | RCN true c tl => (pushTokBackN (pushTokBackN bR (TokWN c)) (TokON 1), tl)
  | RTokN t tl => (pushTokBackN bR t, tl)
  end.

Definition pullStepLN (p : list TokN * LStackN) : list TokN * LStackN :=
  if needPullN (fst p) then pullOneLN (fst p) (snd p) else p.

Definition pullStepRN (p : list TokN * RStackN) : list TokN * RStackN :=
  if needPullN (fst p) then pullOneRN (fst p) (snd p) else p.

Definition ensureLN (bL : list TokN) (rL : LStackN) : list TokN * LStackN :=
  pullStepLN (pullStepLN (pullStepLN (pullStepLN (bL, rL)))).

Definition ensureRN (bR : list TokN) (rR : RStackN) : list TokN * RStackN :=
  pullStepRN (pullStepRN (pullStepRN (pullStepRN (bR, rR)))).

Fixpoint foldPackLN (revTs : list TokN) (rL : LStackN) : LStackN :=
  match revTs with
  | [] => rL
  | t :: revRest =>
    match t with
    | TokWN b =>
      if negb (isZeroN b) then
        match revRest with
        | TokZN z :: revRest2 =>
          if isOneN z then foldPackLN revRest2 (LCN b rL)
          else foldPackLN revRest (LTokN t rL)
        | _ => foldPackLN revRest (LTokN t rL)
        end
      else foldPackLN revRest (LTokN t rL)
    | TokZN z =>
      if isOneN z then
        match rL with
        | LTokN (TokWN b) tl =>
          if negb (isZeroN b) then foldPackLN revRest (LCN b tl)
          else foldPackLN revRest (LTokN t rL)
        | _ => foldPackLN revRest (LTokN t rL)
        end
      else foldPackLN revRest (LTokN t rL)
    | _ => foldPackLN revRest (LTokN t rL)
    end
  end.

Fixpoint foldPackRN (revTs : list TokN) (rR : RStackN) : RStackN :=
  match revTs with
  | [] => rR
  | t :: revRest =>
    match t with
    | TokZN z =>
      if isOneN z then
        match revRest with
        | TokWN c :: revRest2 =>
          if negb (isZeroN c) then foldPackRN revRest2 (RCN false c rR)
          else foldPackRN revRest (RCN false 0 rR)
        | _ => foldPackRN revRest (RCN false 0 rR)
        end
      else foldPackRN revRest (RTokN t rR)
    | TokON o =>
      if isOneN o then
        match revRest with
        | TokWN c :: revRest2 =>
          if negb (isZeroN c) then foldPackRN revRest2 (RCN true c rR)
          else foldPackRN revRest (RCN true 0 rR)
        | _ => foldPackRN revRest (RCN true 0 rR)
        end
      else foldPackRN revRest (RTokN t rR)
    | TokWN c =>
      if negb (isZeroN c) then
        match rR with
        | RTokN (TokZN z) tl =>
          if isOneN z then foldPackRN revRest (RCN false c tl)
          else foldPackRN revRest (RTokN t rR)
        | RTokN (TokON o) tl =>
          if isOneN o then foldPackRN revRest (RCN true c tl)
          else foldPackRN revRest (RTokN t rR)
        | RCN b c' tl => foldPackRN revRest (RCN b (c + c') tl)
        | _ => foldPackRN revRest (RTokN t rR)
        end
      else
        match rR with
        | RCN b c' tl => foldPackRN revRest (RCN b c' tl)
        | _ => foldPackRN revRest (RTokN t rR)
        end
    end
  end.

Definition pushRawOverflowLN (bL : list TokN) (rL : LStackN) : list TokN * LStackN :=
  match bL with
  | t0 :: t1 :: t2 :: t3 :: t4 :: t5 :: rest =>
    ([t0; t1; t2; t3], foldPackLN (List.rev (t4 :: t5 :: rest)) rL)
  | _ => (bL, rL)
  end.

Definition pushRawOverflowRN (bR : list TokN) (rR : RStackN) : list TokN * RStackN :=
  match bR with
  | t0 :: t1 :: t2 :: t3 :: t4 :: t5 :: rest =>
    ([t0; t1; t2; t3], foldPackRN (List.rev (t4 :: t5 :: rest)) rR)
  | _ => (bR, rR)
  end.

Definition canCleanN (sL : LStackN) (sR : RStackN) : bool :=
  match sL, sR with
  | LCN b0 lt, RCN isC1 c0 rt =>
    let diff := b0 - 2 * c0 in
    if isZeroN diff then
      match lt with
      | LCN b1 _ =>
        if isZeroN (b1 - 3) then false
        else negb (isZeroN (c0 - (halfN b0 + (if oddN b0 then 1 else 0))))
      | _ => false
      end
    else
      if isC1 then
        if isZeroN (diff - 2) then false
        else match rt with RCN _ c1 _ => negb (isZeroN (c1 - 2)) | _ => false end
      else
        if isZeroN c0 then false
        else match rt with RCN _ c1 _ => negb (isZeroN (c1 - 1)) | _ => false end
  | _, _ => false
  end.

Definition finishGenN (q : Q_st) (h : bool) (bL : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN) : HybStateN :=
  match q, h, bL with
  | QF, true, TokWN w0 :: restL =>
    if isThreeN w0 then
      let rL' := foldPackLN (List.rev restL) rL in
      let rR' := foldPackRN (List.rev bR) rR in
      if canCleanN rL' rR' then HCleanN rL' rR'
      else
        let oL := pushRawOverflowLN bL rL in
        let oR := pushRawOverflowRN bR rR in
        HGenN QF true (fst oL) (snd oL) (fst oR) (snd oR)
    else
      let oL := pushRawOverflowLN bL rL in
      let oR := pushRawOverflowRN bR rR in
      HGenN q h (fst oL) (snd oL) (fst oR) (snd oR)
  | _, _, _ =>
    let oL := pushRawOverflowLN bL rL in
    let oR := pushRawOverflowRN bR rR in
    HGenN q h (fst oL) (snd oL) (fst oR) (snd oR)
  end.

Definition pushBitN (b : bool) (ts : list TokN) (emptyTail : bool) : list TokN :=
  if b then
    match ts with
    | [TokON o0] =>
      if isOneN o0 then (if emptyTail then [TokWN 1] else [TokON 2])
      else TokON (o0 + 1) :: []
    | TokON o0 :: TokZN z0 :: rest =>
      if isOneN o0 then
        if isOneN z0 then pushTokN (TokWN 1) rest
        else if lebN 2 z0 then TokWN 1 :: TokZN (z0 - 1) :: rest
        else TokON 2 :: TokZN z0 :: rest
      else TokON (o0 + 1) :: TokZN z0 :: rest
    | TokON n :: rest => TokON (n + 1) :: rest
    | _ => TokON 1 :: ts
    end
  else
    match ts with
    | [] => if emptyTail then [] else [TokZN 1]
    | TokZN n :: rest => TokZN (n + 1) :: rest
    | _ => TokZN 1 :: ts
    end.

Fixpoint popBitN (ts : list TokN) : option (bool * list TokN) :=
  match ts with
  | [] => None
  | TokZN n :: rest =>
    if isZeroN n then popBitN rest
    else if isOneN n then Some (false, rest)
    else Some (false, TokZN (n - 1) :: rest)
  | TokON n :: rest =>
    if isZeroN n then popBitN rest
    else if isOneN n then Some (true, rest)
    else Some (true, TokON (n - 1) :: rest)
  | TokWN n :: rest =>
    if isZeroN n then popBitN rest
    else if isOneN n then Some (true, TokON 1 :: pushTokN (TokZN 1) rest)
    else Some (true, TokON 1 :: TokZN 1 :: TokWN (n - 1) :: rest)
  end.

Definition isEmptyLN (rL : LStackN) : bool := match rL with LNilN => true | _ => false end.
Definition isEmptyRN (rR : RStackN) : bool := match rR with RNilN => true | _ => false end.

Definition popBitLN (bL : list TokN) (rL : LStackN) : option (bool * list TokN * LStackN) :=
  match popBitN bL with
  | Some (b, bL') => Some (b, bL', rL)
  | None => match rL with LNilN => Some (false, [], LNilN) | _ => None end
  end.

Definition popBitRN (bR : list TokN) (rR : RStackN) : option (bool * list TokN * RStackN) :=
  match popBitN bR with
  | Some (b, bR') => Some (b, bR', rR)
  | None => match rR with RNilN => Some (false, [], RNilN) | _ => None end
  end.

Definition stepRawN (q : Q_st) (h : bool) (bL : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN) : HybStateN :=
  match q, h with
  | QA, false =>
    match popBitRN bR rR with
    | Some (h', bR', rR') => finishGenN QB h' (pushBitN true bL (isEmptyLN rL)) rL bR' rR'
    | None => HGenN q h bL rL bR rR
    end
  | QA, true =>
    match popBitRN bR rR with
    | Some (h', bR', rR') => finishGenN QE h' (pushBitN false bL (isEmptyLN rL)) rL bR' rR'
    | None => HGenN q h bL rL bR rR
    end
  | QB, false =>
    match popBitLN bL rL with
    | Some (h', bL', rL') => finishGenN QC h' bL' rL' (pushBitN true bR (isEmptyRN rR)) rR
    | None => HGenN q h bL rL bR rR
    end
  | QB, true =>
    match popBitLN bL rL with
    | Some (h', bL', rL') => finishGenN QF h' bL' rL' (pushBitN true bR (isEmptyRN rR)) rR
    | None => HGenN q h bL rL bR rR
    end
  | QC, false =>
    match popBitRN bR rR with
    | Some (h', bR', rR') => finishGenN QA h' (pushBitN true bL (isEmptyLN rL)) rL bR' rR'
    | None => HGenN q h bL rL bR rR
    end
  | QC, true =>
    match popBitLN bL rL with
    | Some (h', bL', rL') => finishGenN QD h' bL' rL' (pushBitN false bR (isEmptyRN rR)) rR
    | None => HGenN q h bL rL bR rR
    end
  | QD, false =>
    match popBitLN bL rL with
    | Some (h', bL', rL') => finishGenN QB h' bL' rL' (pushBitN true bR (isEmptyRN rR)) rR
    | None => HGenN q h bL rL bR rR
    end
  | QD, true =>
    match popBitLN bL rL with
    | Some (h', bL', rL') => finishGenN QA h' bL' rL' (pushBitN true bR (isEmptyRN rR)) rR
    | None => HGenN q h bL rL bR rR
    end
  | QE, false =>
    match popBitRN bR rR with
    | Some (h', bR', rR') => finishGenN QB h' (pushBitN true bL (isEmptyLN rL)) rL bR' rR'
    | None => HGenN q h bL rL bR rR
    end
  | QE, true =>
    match popBitRN bR rR with
    | Some (h', bR', rR') => finishGenN QC h' (pushBitN true bL (isEmptyLN rL)) rL bR' rR'
    | None => HGenN q h bL rL bR rR
    end
  | QF, false => HGenN q h bL rL bR rR
  | QF, true =>
    match popBitLN bL rL with
    | Some (h', bL', rL') => finishGenN QA h' bL' rL' (pushBitN false bR (isEmptyRN rR)) rR
    | None => HGenN q h bL rL bR rR
    end
  end.

Definition startsWith1N (ts : list TokN) : bool :=
  match ts with
  | TokON n :: _ => negb (isZeroN n)
  | TokWN n :: _ => negb (isZeroN n)
  | _ => false
  end.

Definition subWHeadN (c d : nat) (rest : list TokN) : list TokN :=
  let rem := c - d in
  if isZeroN rem then rest else TokWN rem :: rest.

Definition stepGenF1PPN (a : nat) (lTail : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN)
    (bL_orig : list TokN) : HybStateN :=
  match bR with
  | TokON o0 :: TokZN z :: rTail =>
    if andb (isOneN o0) (negb (isZeroN z)) then
      let z1 := z - 1 in
      let rRest := if isZeroN z1 then rTail else TokZN z1 :: rTail in
      let bR' := TokON 1 :: TokZN 1 :: pushTokN (TokWN a) rRest in
      finishGenN QF true lTail rL bR' rR
    else stepRawN QF true bL_orig rL bR rR
  | [TokON o0] =>
    if isOneN o0 then
      match rR with
      | RNilN => finishGenN QF true lTail rL [TokON 1; TokZN 1; TokWN a] RNilN
      | _ => stepRawN QF true bL_orig rL bR rR
      end
    else stepRawN QF true bL_orig rL bR rR
  | _ => stepRawN QF true bL_orig rL bR rR
  end.

Definition stepGenP1N (a b1 : nat) (lTail : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN)
    (bL_orig : list TokN) : HybStateN :=
  match bR with
  | TokON o0 :: TokZN z :: rTail =>
    if andb (isOneN o0) (negb (isZeroN z)) then
      let z1 := z - 1 in
      let rAfter := if isZeroN z1 then rTail else TokZN z1 :: rTail in
      match popBitRN rAfter rR with
      | Some (h', bR', rR') =>
        let a' := a + 2 in
        let bL' := if isZeroN b1 then TokWN a' :: pushTokN (TokZN 1) lTail else TokWN a' :: TokZN 1 :: TokWN b1 :: lTail in
        finishGenN QA h' bL' rL bR' rR'
      | None => stepRawN QF true bL_orig rL bR rR
      end
    else stepRawN QF true bL_orig rL bR rR
  | [TokON o0] =>
    if isOneN o0 then
      match rR with
      | RNilN =>
        let a' := a + 2 in
        let bL' := if isZeroN b1 then TokWN a' :: pushTokN (TokZN 1) lTail else TokWN a' :: TokZN 1 :: TokWN b1 :: lTail in
        finishGenN QA false bL' rL [] RNilN
      | _ => stepRawN QF true bL_orig rL bR rR
      end
    else stepRawN QF true bL_orig rL bR rR
  | _ => stepRawN QF true bL_orig rL bR rR
  end.

Definition stepGenCoreN (q : Q_st) (h : bool) (bL : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN) : HybStateN :=
  match q, h with
  | QF, true =>
    match bL with
    | TokWN a :: TokZN z0 :: TokWN b :: lTail =>
      if isOneN z0 then
        if andb (negb (isZeroN a)) (negb (isZeroN b)) then
          let b1 := b - 1 in
          match bR with
          | TokWN c :: rTail =>
            if isZeroN c then stepRawN QF true bL rL bR rR
            else
              let b2 := halfN b in
              let k0 := if lebN b2 c then b2 else c in
              let k := if eqbN k0 c then (if startsWith1N rTail then k0 else k0 - 1) else k0 in
              if negb (isZeroN k) then
                let a' := a + mul3addcN 0 k in
                let b' := b - 2 * k in
                let bL' := if isZeroN b' then TokWN a' :: pushTokN (TokZN 1) lTail else TokWN a' :: TokZN 1 :: TokWN b' :: lTail in
                finishGenN QF true bL' rL (subWHeadN c k rTail) rR
              else
                let a' := a + 1 in
                let bL' := if isZeroN b1 then TokWN a' :: pushTokN (TokZN 1) lTail else TokWN a' :: TokZN 1 :: TokWN b1 :: lTail in
                let bR' := TokON 1 :: pushTokN (TokZN 2) (subWHeadN c 1 rTail) in
                finishGenN QF true bL' rL bR' rR
          | TokON o0 :: TokZN z1 :: rTail =>
            if isOneN o0 then
              if isTwoN z1 then
                if startsWith1N rTail then
                  let a' := a + 2 in
                  let bL' := if isZeroN b1 then TokWN a' :: pushTokN (TokZN 1) lTail else TokWN a' :: TokZN 1 :: TokWN b1 :: lTail in
                  finishGenN QF true bL' rL rTail rR
                else stepRawN QF true bL rL bR rR
              else if isThreeN z1 then
                match rTail with
                | TokWN c :: rTail2 =>
                  if negb (isZeroN c) then
                    let ok := if isOneN c then startsWith1N rTail2 else true in
                    if ok then
                      let bL' := if isZeroN b1 then TokWN 3 :: TokZN 1 :: TokWN a :: pushTokN (TokZN 1) lTail
                                 else TokWN 3 :: TokZN 1 :: TokWN a :: TokZN 1 :: TokWN b1 :: lTail in
                      finishGenN QF true bL' rL (subWHeadN c 1 rTail2) rR
                    else stepRawN QF true bL rL bR rR
                  else stepGenP1N a b1 lTail rL bR rR bL
                | _ => stepGenP1N a b1 lTail rL bR rR bL
                end
              else stepGenP1N a b1 lTail rL bR rR bL
            else stepRawN QF true bL rL bR rR
          | TokON o0 :: TokWN c :: rTail =>
            if andb (isOneN o0) (lebN 2 c) then
              if lebN 2 b then
                let ok := if isTwoN c then startsWith1N rTail else true in
                if ok then
                  let a' := a + 1 in
                  let b2 := b - 2 in
                  let bL' := if isZeroN b2 then TokWN 3 :: TokZN 1 :: TokWN a' :: pushTokN (TokZN 1) lTail
                             else TokWN 3 :: TokZN 1 :: TokWN a' :: TokZN 1 :: TokWN b2 :: lTail in
                  finishGenN QF true bL' rL (subWHeadN c 2 rTail) rR
                else stepRawN QF true bL rL bR rR
              else stepRawN QF true bL rL bR rR
            else stepRawN QF true bL rL bR rR
          | _ => stepGenP1N a b1 lTail rL bR rR bL
          end
        else if negb (isZeroN a) then stepGenF1PPN a (TokZN z0 :: TokWN b :: lTail) rL bR rR bL
        else stepRawN QF true bL rL bR rR
      else if isTwoN z0 then
        if andb (negb (isZeroN a)) (lebN 3 b) then
          if startsWith1N bR then
            let b3 := b - 3 in
            let bL' := if isZeroN b3 then TokWN 3 :: pushTokN (TokZN 1) lTail else TokWN 3 :: TokZN 1 :: TokWN b3 :: lTail in
            let bR' := pushTokN (TokWN a) (pushBitN true bR (isEmptyRN rR)) in
            finishGenN QF true bL' rL bR' rR
          else stepGenF1PPN a (TokZN z0 :: TokWN b :: lTail) rL bR rR bL
        else if negb (isZeroN a) then stepGenF1PPN a (TokZN z0 :: TokWN b :: lTail) rL bR rR bL
        else stepRawN QF true bL rL bR rR
      else if negb (isZeroN a) then stepGenF1PPN a (TokZN z0 :: TokWN b :: lTail) rL bR rR bL
      else stepRawN QF true bL rL bR rR
    | [TokWN a; TokON o0] =>
      if andb (negb (isZeroN a)) (isOneN o0) then
        match rL, bR with
        | LNilN, TokWN c :: rTail =>
          if isZeroN c then stepRawN QF true bL rL bR rR
          else
            let k := if startsWith1N rTail then c else c - 1 in
            if negb (isZeroN k) then
              let a' := a + mul3addcN 0 k in
              finishGenN QF true [TokWN a'; TokON 1] LNilN (subWHeadN c k rTail) rR
            else stepRawN QF true bL rL bR rR
        | _, _ => stepGenF1PPN a [TokON o0] rL bR rR bL
        end
      else if negb (isZeroN a) then stepGenF1PPN a [TokON o0] rL bR rR bL
      else stepRawN QF true bL rL bR rR
    | TokZN z0 :: TokWN b :: lTail =>
      if isOneN z0 then
        if isZeroN b then stepRawN QF true bL rL bR rR
        else
          let b1 := b - 1 in
          let bL' := if isZeroN b1 then TokWN 1 :: pushTokN (TokZN 1) lTail else TokWN 1 :: TokZN 1 :: TokWN b1 :: lTail in
          finishGenN QA true bL' rL bR rR
      else if isTwoN z0 then
        if isZeroN b then stepRawN QF true bL rL bR rR
        else
          let b1 := b - 1 in
          let bL' := if isZeroN b1 then pushTokN (TokZN 1) lTail else TokZN 1 :: TokWN b1 :: lTail in
          let bR' := pushTokN (TokWN 1) (pushBitN true bR (isEmptyRN rR)) in
          finishGenN QF true bL' rL bR' rR
      else stepRawN QF true bL rL bR rR
    | TokWN a :: lTail =>
      if isZeroN a then stepRawN QF true bL rL bR rR
      else stepGenF1PPN a lTail rL bR rR bL
    | _ => stepRawN QF true bL rL bR rR
    end
  | QC, false =>
    match bR with
    | TokWN c :: rTail =>
      if isZeroN c then stepRawN QC false bL rL bR rR
      else
        match popBitRN rTail rR with
        | Some (h', bR', rR') =>
          let bL' := pushTokN (TokWN c) (pushBitN true bL (isEmptyLN rL)) in
          finishGenN QA h' bL' rL bR' rR'
        | None => stepRawN QC false bL rL bR rR
        end
    | _ => stepRawN QC false bL rL bR rR
    end
  | QA, true =>
    match bR with
    | TokWN c :: rTail =>
      if isZeroN c then stepRawN QA true bL rL bR rR
      else finishGenN QF true bL rL (TokON 1 :: TokZN 2 :: subWHeadN c 1 rTail) rR
    | TokON n :: rTail =>
      if lebN 2 n then
        let n2 := n - 2 in
        let rRest := if isZeroN n2 then rTail else TokON n2 :: rTail in
        finishGenN QF true bL rL (TokON 1 :: pushTokN (TokZN 1) rRest) rR
      else if isOneN n then
        match rTail with
        | TokZN z :: rTail2 =>
          if isZeroN z then stepRawN QA true bL rL bR rR
          else
            let z1 := z - 1 in
            let rAfter := if isZeroN z1 then rTail2 else TokZN z1 :: rTail2 in
            match rAfter with
            | TokWN c :: rTail3 =>
              if isZeroN c then
                match popBitRN rAfter rR with
                | Some (h', bR', rR') => finishGenN QA h' (pushTokN (TokWN 1) bL) rL bR' rR'
                | None => stepRawN QA true bL rL bR rR
                end
              else
                match popBitRN rTail3 rR with
                | Some (h', bR', rR') => finishGenN QA h' (pushTokN (TokWN (c + 1)) bL) rL bR' rR'
                | None => stepRawN QA true bL rL bR rR
                end
            | _ =>
              match popBitRN rAfter rR with
              | Some (h', bR', rR') => finishGenN QA h' (pushTokN (TokWN 1) bL) rL bR' rR'
              | None => stepRawN QA true bL rL bR rR
              end
            end
        | [] =>
          match rR with
          | RNilN => finishGenN QA false (pushTokN (TokWN 1) bL) rL [] RNilN
          | _ => stepRawN QA true bL rL bR rR
          end
        | TokWN c :: rTail2 =>
          if isZeroN c then stepRawN QA true bL rL bR rR
          else finishGenN QF true bL rL (TokON 1 :: TokZN 1 :: TokON 1 :: TokZN 1 :: subWHeadN c 1 rTail2) rR
        | _ => stepRawN QA true bL rL bR rR
        end
      else stepRawN QA true bL rL bR rR
    | _ => stepRawN QA true bL rL bR rR
    end
  | _, _ => stepRawN q h bL rL bR rR
  end.

Definition stepGenN (q : Q_st) (h : bool) (bL : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN) : HybStateN :=
  let pL := ensureLN bL rL in
  let pR := ensureRN bR rR in
  stepGenCoreN q h (fst pL) (snd pL) (fst pR) (snd pR).

Fixpoint runGenChunkN (kg : nat) (s : HybStateN) : HybStateN :=
  match kg with
  | O => s
  | S kg' =>
    match s with
    | HCleanN sL sR => HCleanN sL sR
    | HGenN q h bL rL bR rR => runGenChunkN kg' (stepGenN q h bL rL bR rR)
    end
  end.

Definition kc1000 : nat := Pos.to_nat 1000%positive.
Definition kg128 : nat := Pos.to_nat 128%positive.

Definition stepOuterN (s : HybStateN) : HybStateN :=
  match s with
  | HCleanN sL sR => runCleanChunkN kc1000 sL sR
  | HGenN q h bL rL bR rR => runGenChunkN kg128 (HGenN q h bL rL bR rR)
  end.

Definition r1StartN : HybStateN := HGenN QA false [] LNilN [] RNilN.

Definition check_cycler_entryN (s : HybStateN) : bool :=
  match s with
  | HGenN QA true (TokWN n :: _) _ [] RNilN => lebN 18 n
  | _ => false
  end.

(** ** 5. Soundness of Reference [nat] Hybrid Stepper ([stepOuterN_sound]) *)

Lemma isZeroN_true (n : nat) : isZeroN n = true -> n = 0.
Proof. unfold isZeroN. apply Nat.eqb_eq. Qed.

Lemma isZeroN_false (n : nat) : isZeroN n = false -> n <> 0.
Proof. unfold isZeroN. apply Nat.eqb_neq. Qed.

Lemma isOneN_true (n : nat) : isOneN n = true -> n = 1.
Proof. unfold isOneN. apply Nat.eqb_eq. Qed.

Lemma isTwoN_true (n : nat) : isTwoN n = true -> n = 2.
Proof. unfold isTwoN. apply Nat.eqb_eq. Qed.

Lemma isThreeN_true (n : nat) : isThreeN n = true -> n = 3.
Proof. unfold isThreeN. apply Nat.eqb_eq. Qed.

Lemma lebN_true (x y : nat) : lebN x y = true -> x <= y.
Proof. unfold lebN. apply Nat.leb_le. Qed.

Lemma lebN_false (x y : nat) : lebN x y = false -> y < x.
Proof. unfold lebN. apply Nat.leb_gt. Qed.

Lemma eqbN_true (x y : nat) : eqbN x y = true -> x = y.
Proof. unfold eqbN. apply Nat.eqb_eq. Qed.

Lemma eqbN_false (x y : nat) : eqbN x y = false -> x <> y.
Proof. unfold eqbN. apply Nat.eqb_neq. Qed.

Lemma runCleanLoopN_sound (steps : nat) :
  forall (b0 : nat) (lt : LStackN) (isC1 : bool) (c0 : nat) (rt : RStackN),
    encHybN (HCleanN (LCN b0 lt) (RCN isC1 c0 rt)) -[ tm ]->*
    encHybN (runCleanLoopN steps b0 lt isC1 c0 rt).
Proof.
  induction steps as [| steps' IH]; intros b0 lt isC1 c0 rt; cbn [runCleanLoopN].
  - apply evstep_refl.
  - destruct (isZeroN (b0 - 2 * c0)) eqn:Hdiff.
    + destruct lt as [| b1 lt2 | t lt2]; [apply evstep_refl | | apply evstep_refl].
      destruct (isZeroN (b1 - 3)) eqn:Hb1; [apply evstep_refl | ].
      apply isZeroN_false in Hb1.
      destruct (evenN b0) eqn:Hev.
      * destruct (isZeroN (c0 - halfN b0)) eqn:Hc0; [apply evstep_refl | ].
        apply isZeroN_false in Hc0.
        pose proof (clean_B1_even b0 b1 c0 (encLN lt2) (bitToSym isC1 >> encRN rt)
                      Hev ltac:(lia) ltac:(lia)) as Hstep.
        replace (3 + 3 * halfN b0) with (mul3addcN 3 (halfN b0)) in Hstep by (unfold mul3addcN; lia).
        exact (stepStar_trans Hstep (IH (b1 - 3) lt2 true (mul3addcN 3 (halfN b0)) (RCN isC1 (c0 - halfN b0) rt))).
      * destruct (isZeroN (c0 - (halfN b0 + 1))) eqn:Hc0; [apply evstep_refl | ].
        apply isZeroN_false in Hc0.
        pose proof (clean_B1_odd b0 b1 c0 (encLN lt2) (bitToSym isC1 >> encRN rt)
                      Hev ltac:(lia) ltac:(lia)) as Hstep.
        replace (5 + 3 * halfN b0) with (mul3addcN 5 (halfN b0)) in Hstep by (unfold mul3addcN; lia).
        exact (stepStar_trans Hstep (IH (b1 - 3) lt2 false (mul3addcN 5 (halfN b0)) (RCN isC1 (c0 - (halfN b0 + 1)) rt))).
    + apply isZeroN_false in Hdiff.
      destruct isC1.
      * destruct (isZeroN (b0 - 2 * c0 - 2)) eqn:Hnb0; [apply evstep_refl | ].
        apply isZeroN_false in Hnb0.
        destruct rt as [| t1 c1 rt2 | t rt2]; [apply evstep_refl | | apply evstep_refl].
        destruct (isZeroN (c1 - 2)) eqn:Hc1; [apply evstep_refl | ].
        apply isZeroN_false in Hc1.
        pose proof (clean_B23_c1 b0 c0 c1 (encLN lt) (bitToSym t1 >> encRN rt2)
                      ltac:(lia) ltac:(lia)) as Hstep.
        replace (4 + 3 * c0) with (mul3addcN 4 c0) in Hstep by (unfold mul3addcN; lia).
        replace (b0 - (2 * c0 + 2)) with (b0 - 2 * c0 - 2) in Hstep by lia.
        exact (stepStar_trans Hstep (IH (mul3addcN 4 c0) (LCN (b0 - 2 * c0 - 2) lt) t1 (c1 - 2) rt2)).
      * destruct (isZeroN c0) eqn:Hc0; [apply evstep_refl | ].
        apply isZeroN_false in Hc0.
        destruct rt as [| t1 c1 rt2 | t rt2]; [apply evstep_refl | | apply evstep_refl].
        destruct (isZeroN (c1 - 1)) eqn:Hc1; [apply evstep_refl | ].
        apply isZeroN_false in Hc1.
        pose proof (clean_B23_c0 b0 c0 c1 (encLN lt) (bitToSym t1 >> encRN rt2)
                      ltac:(lia) ltac:(lia) ltac:(lia)) as Hstep.
        replace (1 + 3 * c0) with (mul3addcN 1 c0) in Hstep by (unfold mul3addcN; lia).
        exact (stepStar_trans Hstep (IH (mul3addcN 1 c0) (LCN (b0 - 2 * c0) lt) t1 (c1 - 1) rt2)).
Qed.

Lemma runCleanChunkN_sound (kc4 : nat) (sL : LStackN) (sR : RStackN) :
  encHybN (HCleanN sL sR) -[ tm ]->* encHybN (runCleanChunkN kc4 sL sR).
Proof.
  destruct sL as [| b0 lt | t lt]; try apply evstep_refl.
  destruct sR as [| isC1 c0 rt | t rt]; try apply evstep_refl.
  apply runCleanLoopN_sound.
Qed.

Lemma encPushTokN (t : TokN) (ts : list TokN) (lb : side) :
  encToksN (pushTokN t ts) lb = encTokN t (encToksN ts lb).
Proof.
  destruct t as [[| a] | [| a] | [| a]]; try reflexivity;
    destruct ts as [| [b | b | b] rest]; cbn [pushTokN encToksN encTokN]; try reflexivity.
  - rewrite enc0_add; reflexivity.
  - rewrite enc1_add; reflexivity.
  - rewrite encW_add; reflexivity.
Qed.

Lemma encPushTokBackN (ts : list TokN) (t : TokN) (lb : side) :
  encToksN (pushTokBackN ts t) lb = encToksN ts (encTokN t lb).
Proof.
  induction ts as [| t0 rest IH].
  - apply encPushTokN.
  - destruct rest as [| t1 rest2].
    + cbn [pushTokBackN encToksN]; rewrite encPushTokN, encPushTokN; reflexivity.
    + change (pushTokBackN (t0 :: t1 :: rest2) t) with (t0 :: pushTokBackN (t1 :: rest2) t).
      cbn [encToksN]; rewrite IH; reflexivity.
Qed.

Lemma encStripEndZN (ts : list TokN) :
  encToksN (stripEndZN ts) lb0 = encToksN ts lb0.
Proof.
  induction ts as [| t rest IH]; cbn [stripEndZN].
  - reflexivity.
  - destruct (stripEndZN rest) as [| t' rest']; cbn [encToksN] in *.
    + destruct t as [n | n | n]; cbn [encToksN encTokN]; rewrite <- IH;
        [symmetry; apply enc0_lb0 | reflexivity | reflexivity].
    + rewrite IH; reflexivity.
Qed.

Lemma encPullOneLN (bL : list TokN) (rL : LStackN) :
  encToksN (fst (pullOneLN bL rL)) (encLN (snd (pullOneLN bL rL))) = encToksN bL (encLN rL).
Proof.
  destruct rL as [| b tl | t tl]; cbn [pullOneLN fst snd encLN].
  - apply encStripEndZN.
  - rewrite encPushTokBackN, encPushTokBackN; reflexivity.
  - rewrite encPushTokBackN; reflexivity.
Qed.

Lemma encPullOneRN (bR : list TokN) (rR : RStackN) :
  encToksN (fst (pullOneRN bR rR)) (encRN (snd (pullOneRN bR rR))) = encToksN bR (encRN rR).
Proof.
  destruct rR as [| [|] c tl | t tl]; cbn [pullOneRN fst snd encRN].
  - apply encStripEndZN.
  - rewrite encPushTokBackN, encPushTokBackN; reflexivity.
  - rewrite encPushTokBackN, encPushTokBackN; reflexivity.
  - rewrite encPushTokBackN; reflexivity.
Qed.

Lemma encPullStepLN (p : list TokN * LStackN) :
  encToksN (fst (pullStepLN p)) (encLN (snd (pullStepLN p))) = encToksN (fst p) (encLN (snd p)).
Proof.
  unfold pullStepLN. destruct (needPullN (fst p)); [apply encPullOneLN | reflexivity].
Qed.

Lemma encPullStepRN (p : list TokN * RStackN) :
  encToksN (fst (pullStepRN p)) (encRN (snd (pullStepRN p))) = encToksN (fst p) (encRN (snd p)).
Proof.
  unfold pullStepRN. destruct (needPullN (fst p)); [apply encPullOneRN | reflexivity].
Qed.

Lemma encEnsureLN (bL : list TokN) (rL : LStackN) :
  encToksN (fst (ensureLN bL rL)) (encLN (snd (ensureLN bL rL))) = encToksN bL (encLN rL).
Proof.
  unfold ensureLN. rewrite !encPullStepLN. reflexivity.
Qed.

Lemma encEnsureRN (bR : list TokN) (rR : RStackN) :
  encToksN (fst (ensureRN bR rR)) (encRN (snd (ensureRN bR rR))) = encToksN bR (encRN rR).
Proof.
  unfold ensureRN. rewrite !encPullStepRN. reflexivity.
Qed.

Lemma encFoldPackLN_aux (n : nat) :
  forall (revTs : list TokN) (rL : LStackN),
    List.length revTs <= n ->
    encLN (foldPackLN revTs rL) = encToksN (List.rev revTs) (encLN rL).
Proof.
  induction n as [| n IH]; intros [| t revRest] rL Hlen; cbn [List.length] in Hlen.
  - reflexivity.
  - lia.
  - reflexivity.
  - cbn [foldPackLN].
    destruct t as [z | o | b].
    + destruct (isOneN z) eqn:Hz.
      * apply isOneN_true in Hz; subst z.
        destruct rL as [| b' tl | [z' | o' | b] tl];
          try (rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity).
        destruct (negb (isZeroN b)) eqn:Hb;
          rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity.
      * rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity.
    + rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity.
    + destruct (negb (isZeroN b)) eqn:Hb.
      * destruct revRest as [| [z | o' | b'] revRest2];
          try (rewrite IH by (cbn [List.length] in Hlen |- *; lia); cbn [List.rev]; rewrite !encToksN_app; reflexivity).
        destruct (isOneN z) eqn:Hz.
        { apply isOneN_true in Hz; subst z.
          rewrite IH by (cbn [List.length] in Hlen |- *; lia).
          cbn [List.rev]; rewrite !encToksN_app; reflexivity. }
        { rewrite IH by (cbn [List.length] in Hlen |- *; lia).
          cbn [List.rev]; rewrite !encToksN_app; reflexivity. }
      * rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity.
Qed.

Lemma encFoldPackLN (revTs : list TokN) (rL : LStackN) :
  encLN (foldPackLN revTs rL) = encToksN (List.rev revTs) (encLN rL).
Proof.
  exact (encFoldPackLN_aux (List.length revTs) revTs rL (Nat.le_refl _)).
Qed.

Lemma encFoldPackRN_aux (n : nat) :
  forall (revTs : list TokN) (rR : RStackN),
    List.length revTs <= n ->
    encRN (foldPackRN revTs rR) = encToksN (List.rev revTs) (encRN rR).
Proof.
  induction n as [| n IH]; intros [| t revRest] rR Hlen; cbn [List.length] in Hlen.
  - reflexivity.
  - lia.
  - reflexivity.
  - cbn [foldPackRN].
    destruct t as [z | o | c].
    + destruct (isOneN z) eqn:Hz.
      * apply isOneN_true in Hz; subst z.
        destruct revRest as [| [z' | o' | c] revRest2];
          try (rewrite IH by (cbn [List.length] in Hlen |- *; lia); cbn [List.rev]; rewrite !encToksN_app; reflexivity).
        destruct (negb (isZeroN c)) eqn:Hc;
          rewrite IH by (cbn [List.length] in Hlen |- *; lia);
          cbn [List.rev]; rewrite !encToksN_app; reflexivity.
      * rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity.
    + destruct (isOneN o) eqn:Ho.
      * apply isOneN_true in Ho; subst o.
        destruct revRest as [| [z' | o' | c] revRest2];
          try (rewrite IH by (cbn [List.length] in Hlen |- *; lia); cbn [List.rev]; rewrite !encToksN_app; reflexivity).
        destruct (negb (isZeroN c)) eqn:Hc;
          rewrite IH by (cbn [List.length] in Hlen |- *; lia);
          cbn [List.rev]; rewrite !encToksN_app; reflexivity.
      * rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity.
    + destruct (negb (isZeroN c)) eqn:Hc.
      * destruct rR as [| b c' tl | [z | o | w'] tl].
        { rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity. }
        { rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; cbn [encToksN encTokN encRN].
          rewrite encW_add; reflexivity. }
        { destruct (isOneN z) eqn:Hz;
            [apply isOneN_true in Hz; subst z | ];
            rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity. }
        { destruct (isOneN o) eqn:Ho;
            [apply isOneN_true in Ho; subst o | ];
            rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity. }
        { rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity. }
      * apply Bool.negb_false_iff in Hc; apply isZeroN_true in Hc; subst c.
        destruct rR as [| b c' tl | t' tl];
          rewrite IH by lia; cbn [List.rev]; rewrite encToksN_app; reflexivity.
Qed.

Lemma encFoldPackRN (revTs : list TokN) (rR : RStackN) :
  encRN (foldPackRN revTs rR) = encToksN (List.rev revTs) (encRN rR).
Proof.
  exact (encFoldPackRN_aux (List.length revTs) revTs rR (Nat.le_refl _)).
Qed.

Lemma encPushRawOverflowLN (bL : list TokN) (rL : LStackN) :
  encToksN (fst (pushRawOverflowLN bL rL)) (encLN (snd (pushRawOverflowLN bL rL))) =
  encToksN bL (encLN rL).
Proof.
  destruct bL as [| t0 [| t1 [| t2 [| t3 [| t4 [| t5 rest]]]]]]; try reflexivity.
  cbn [pushRawOverflowLN fst snd encToksN].
  rewrite encFoldPackLN, List.rev_involutive.
  reflexivity.
Qed.

Lemma encPushRawOverflowRN (bR : list TokN) (rR : RStackN) :
  encToksN (fst (pushRawOverflowRN bR rR)) (encRN (snd (pushRawOverflowRN bR rR))) =
  encToksN bR (encRN rR).
Proof.
  destruct bR as [| t0 [| t1 [| t2 [| t3 [| t4 [| t5 rest]]]]]]; try reflexivity.
  cbn [pushRawOverflowRN fst snd encToksN].
  rewrite encFoldPackRN, List.rev_involutive.
  reflexivity.
Qed.

Lemma encFinishGenN (q : Q_st) (h : bool) (bL : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN) :
  encHybN (finishGenN q h bL rL bR rR) = encHybN (HGenN q h bL rL bR rR).
Proof.
  unfold finishGenN.
  destruct q; try (cbn [encHybN]; rewrite encPushRawOverflowLN, encPushRawOverflowRN; reflexivity).
  destruct h; [| cbn [encHybN]; rewrite encPushRawOverflowLN, encPushRawOverflowRN; reflexivity].
  destruct bL as [| [z0 | o0 | w0] restL];
    try (cbn [encHybN]; rewrite encPushRawOverflowLN, encPushRawOverflowRN; reflexivity).
  destruct (isThreeN w0) eqn:Hw0;
    [apply isThreeN_true in Hw0; subst w0 |
     cbn [encHybN]; rewrite encPushRawOverflowLN, encPushRawOverflowRN; reflexivity].
  destruct (canCleanN (foldPackLN (List.rev restL) rL) (foldPackRN (List.rev bR) rR)).
  - cbn [encHybN encToksN encTokN qToQ bitToSym].
    rewrite encFoldPackLN, encFoldPackRN, !List.rev_involutive.
    reflexivity.
  - cbn [encHybN]; rewrite encPushRawOverflowLN, encPushRawOverflowRN; reflexivity.
Qed.

Lemma isEmptyLN_spec (rL : LStackN) : isEmptyLN rL = true -> encLN rL = lb0.
Proof. destruct rL; [reflexivity | discriminate | discriminate]. Qed.

Lemma isEmptyRN_spec (rR : RStackN) : isEmptyRN rR = true -> encRN rR = lb0.
Proof. destruct rR; [reflexivity | discriminate | discriminate]. Qed.

Lemma encPushBitN (b : bool) (ts : list TokN) (emptyTail : bool) (lb : side)
    (Hempty : emptyTail = true -> lb = lb0) :
  encToksN (pushBitN b ts emptyTail) lb = bitToSym b >> encToksN ts lb.
Proof.
  destruct b; cbn [pushBitN bitToSym].
  - destruct ts as [| [z0 | o0 | w0] rest]; try reflexivity.
    destruct rest as [| [z1 | o1 | w1] rest2].
    + destruct (isOneN o0) eqn:Ho0.
      * apply isOneN_true in Ho0; subst o0.
        destruct emptyTail.
        { rewrite (Hempty eq_refl); cbn [encToksN encTokN encW enc1]; rewrite lb_zero_cons; reflexivity. }
        { reflexivity. }
      * cbn [encToksN encTokN]; rewrite enc1_succ; reflexivity.
    + destruct (isOneN o0) eqn:Ho0.
      * apply isOneN_true in Ho0; subst o0.
        destruct (isOneN z1) eqn:Hz1.
        { apply isOneN_true in Hz1; subst z1.
          rewrite encPushTokN; reflexivity. }
        { destruct (lebN 2 z1) eqn:Hz2.
          - apply lebN_true in Hz2.
            cbn [encToksN encTokN].
            replace z1 with (S (S (z1 - 2))) at 2 by lia.
            replace (z1 - 1) with (S (z1 - 2)) by lia.
            reflexivity.
          - reflexivity. }
      * cbn [encToksN encTokN]; rewrite enc1_succ; reflexivity.
    + cbn [encToksN encTokN]; rewrite enc1_succ; reflexivity.
    + cbn [encToksN encTokN]; rewrite enc1_succ; reflexivity.
  - destruct ts as [| [n | n | n] rest].
    + destruct emptyTail.
      * rewrite (Hempty eq_refl); cbn [encToksN]; symmetry; apply lb_zero_cons.
      * reflexivity.
    + cbn [encToksN encTokN]; rewrite enc0_succ; reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Lemma encPopBitN (ts : list TokN) :
  forall (b : bool) (ts' : list TokN) (lb : side),
    popBitN ts = Some (b, ts') ->
    encToksN ts lb = bitToSym b >> encToksN ts' lb.
Proof.
  induction ts as [| [n | n | n] rest IH]; intros b ts' lb Hp; cbn [popBitN] in Hp.
  - discriminate.
  - destruct (isZeroN n) eqn:Hn0.
    + apply isZeroN_true in Hn0; subst n; cbn [encToksN encTokN]; exact (IH b ts' lb Hp).
    + apply isZeroN_false in Hn0.
      destruct (isOneN n) eqn:Hn1.
      * apply isOneN_true in Hn1; subst n; injection Hp as <- <-; reflexivity.
      * injection Hp as <- <-.
        destruct n as [| n']; [congruence | ].
        replace (S n' - 1) with n' by lia.
        reflexivity.
  - destruct (isZeroN n) eqn:Hn0.
    + apply isZeroN_true in Hn0; subst n; cbn [encToksN encTokN]; exact (IH b ts' lb Hp).
    + apply isZeroN_false in Hn0.
      destruct (isOneN n) eqn:Hn1.
      * apply isOneN_true in Hn1; subst n; injection Hp as <- <-; reflexivity.
      * injection Hp as <- <-.
        destruct n as [| n']; [congruence | ].
        replace (S n' - 1) with n' by lia.
        reflexivity.
  - destruct (isZeroN n) eqn:Hn0.
    + apply isZeroN_true in Hn0; subst n; cbn [encToksN encTokN]; exact (IH b ts' lb Hp).
    + apply isZeroN_false in Hn0.
      destruct (isOneN n) eqn:Hn1.
      * apply isOneN_true in Hn1; subst n; injection Hp as <- <-.
        destruct rest as [| [? | ? | ?] ?]; reflexivity.
      * injection Hp as <- <-.
        destruct n as [| n']; [congruence | ].
        replace (S n' - 1) with n' by lia.
        reflexivity.
Qed.

Lemma popBitN_none_lb0 (ts : list TokN) :
  popBitN ts = None -> encToksN ts lb0 = lb0.
Proof.
  induction ts as [| [n | n | n] rest IH]; intro Hp; cbn [popBitN] in Hp.
  - reflexivity.
  - destruct (isZeroN n) eqn:Hn0; [apply isZeroN_true in Hn0; subst n; exact (IH Hp) | ].
    destruct (isOneN n); discriminate.
  - destruct (isZeroN n) eqn:Hn0; [apply isZeroN_true in Hn0; subst n; exact (IH Hp) | ].
    destruct (isOneN n); discriminate.
  - destruct (isZeroN n) eqn:Hn0; [apply isZeroN_true in Hn0; subst n; exact (IH Hp) | ].
    destruct (isOneN n); discriminate.
Qed.

Lemma encPopBitLN (bL bL' : list TokN) (rL rL' : LStackN) (b : bool) :
  popBitLN bL rL = Some (b, bL', rL') ->
  encToksN bL (encLN rL) = bitToSym b >> encToksN bL' (encLN rL').
Proof.
  unfold popBitLN.
  destruct (popBitN bL) as [[b0 ts0] | ] eqn:Hp.
  - intro H; injection H as <- <- <-. exact (encPopBitN bL b0 ts0 (encLN rL) Hp).
  - destruct rL; try discriminate.
    intro H; injection H as <- <- <-.
    exact (eq_trans (popBitN_none_lb0 bL Hp) (eq_sym lb_zero_cons)).
Qed.

Lemma encPopBitRN (bR bR' : list TokN) (rR rR' : RStackN) (b : bool) :
  popBitRN bR rR = Some (b, bR', rR') ->
  encToksN bR (encRN rR) = bitToSym b >> encToksN bR' (encRN rR').
Proof.
  unfold popBitRN.
  destruct (popBitN bR) as [[b0 ts0] | ] eqn:Hp.
  - intro H; injection H as <- <- <-. exact (encPopBitN bR b0 ts0 (encRN rR) Hp).
  - destruct rR; try discriminate.
    intro H; injection H as <- <- <-.
    exact (eq_trans (popBitN_none_lb0 bR Hp) (eq_sym lb_zero_cons)).
Qed.

Lemma stepRawN_sound (q : Q_st) (h : bool) (bL : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN) :
  encHybN (HGenN q h bL rL bR rR) -[ tm ]->* encHybN (stepRawN q h bL rL bR rR).
Proof.
  destruct q, h; cbn [stepRawN].
  - (* QA, true -> 0RE *)
    destruct (popBitRN bR rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitRN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyLN_spec rL)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_right; reflexivity | apply evstep_refl].
  - (* QA, false -> 1RB *)
    destruct (popBitRN bR rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitRN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyLN_spec rL)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_right; reflexivity | apply evstep_refl].
  - (* QB, true -> 1LF *)
    destruct (popBitLN bL rL) as [[[h' bL'] rL'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitLN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyRN_spec rR)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_left; reflexivity | apply evstep_refl].
  - (* QB, false -> 1LC *)
    destruct (popBitLN bL rL) as [[[h' bL'] rL'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitLN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyRN_spec rR)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_left; reflexivity | apply evstep_refl].
  - (* QC, true -> 0LD *)
    destruct (popBitLN bL rL) as [[[h' bL'] rL'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitLN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyRN_spec rR)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_left; reflexivity | apply evstep_refl].
  - (* QC, false -> 1RA *)
    destruct (popBitRN bR rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitRN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyLN_spec rL)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_right; reflexivity | apply evstep_refl].
  - (* QD, true -> 1LA *)
    destruct (popBitLN bL rL) as [[[h' bL'] rL'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitLN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyRN_spec rR)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_left; reflexivity | apply evstep_refl].
  - (* QD, false -> 1LB *)
    destruct (popBitLN bL rL) as [[[h' bL'] rL'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitLN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyRN_spec rR)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_left; reflexivity | apply evstep_refl].
  - (* QE, true -> 1RC *)
    destruct (popBitRN bR rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitRN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyLN_spec rL)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_right; reflexivity | apply evstep_refl].
  - (* QE, false -> 1RB *)
    destruct (popBitRN bR rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitRN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyLN_spec rL)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_right; reflexivity | apply evstep_refl].
  - (* QF, true -> 0LA *)
    destruct (popBitLN bL rL) as [[[h' bL'] rL'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN qToQ bitToSym].
    rewrite (encPopBitLN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyRN_spec rR)).
    cbn [bitToSym]; eapply evstep_step; [apply @step_left; reflexivity | apply evstep_refl].
  - (* QF, false -> stay *)
    apply evstep_refl.
Qed.

Lemma encStartsWith1N (ts : list TokN) (lb : side) :
  startsWith1N ts = true -> exists r, encToksN ts lb = S1 >> r.
Proof.
  destruct ts as [| [z | o | w] rest]; cbn [startsWith1N]; try discriminate.
  - destruct o as [| o']; [discriminate | ].
    intro; exists (enc1 o' (encToksN rest lb)); reflexivity.
  - destruct w as [| w']; [discriminate | ].
    intro; exists (S1 >> S0 >> encW w' (encToksN rest lb)); reflexivity.
Qed.

Lemma encSubWHeadN (c d : nat) (rest : list TokN) (lb : side) :
  d <= c ->
  encToksN (TokWN c :: rest) lb = encW d (encToksN (subWHeadN c d rest) lb).
Proof.
  intro Hle; unfold subWHeadN; cbn [encToksN encTokN].
  destruct (isZeroN (c - d)) eqn:Hz.
  - apply isZeroN_true in Hz; replace c with d by lia; reflexivity.
  - apply isZeroN_false in Hz; cbn [encToksN encTokN].
    rewrite <- encW_add; replace (d + (c - d)) with c by lia; reflexivity.
Qed.

Lemma subWHeadN_starts1 (c k : nat) (rTail : list TokN) (lb : side) :
  (k < c \/ (k = c /\ startsWith1N rTail = true)) ->
  exists r', encToksN (subWHeadN c k rTail) lb = S1 >> r'.
Proof.
  intro H; unfold subWHeadN.
  destruct (isZeroN (c - k)) eqn:Hz.
  - apply isZeroN_true in Hz.
    destruct H as [Hlt | [_ Hsw]]; [lia | apply encStartsWith1N; exact Hsw].
  - apply isZeroN_false in Hz.
    destruct (c - k) as [| m]; [congruence | ].
    exists (S1 >> S0 >> encW m (encToksN rTail lb)); reflexivity.
Qed.

Lemma enc0_pred_toks (z : nat) (rTail : list TokN) (lb : side) :
  z <> 0 ->
  enc0 z (encToksN rTail lb) =
  S0 >> encToksN (if isZeroN (z - 1) then rTail else TokZN (z - 1) :: rTail) lb.
Proof.
  destruct z as [| [| z']]; [congruence | intro; reflexivity | intro; reflexivity].
Qed.

Lemma encL_tail_wN (a b : nat) (lTail : list TokN) (rL : LStackN) :
  encToksN (if isZeroN b then TokWN a :: pushTokN (TokZN 1) lTail
            else TokWN a :: TokZN 1 :: TokWN b :: lTail) (encLN rL) =
  encW a (S0 >> encW b (encToksN lTail (encLN rL))).
Proof.
  destruct b as [| b']; cbn [isZeroN Nat.eqb encToksN encTokN].
  - rewrite encPushTokN; reflexivity.
  - reflexivity.
Qed.

Lemma encL_tail_w3N (a b : nat) (lTail : list TokN) (rL : LStackN) :
  encToksN (if isZeroN b then TokWN 3 :: TokZN 1 :: TokWN a :: pushTokN (TokZN 1) lTail
            else TokWN 3 :: TokZN 1 :: TokWN a :: TokZN 1 :: TokWN b :: lTail) (encLN rL) =
  encW 3 (S0 >> encW a (S0 >> encW b (encToksN lTail (encLN rL)))).
Proof.
  destruct b as [| b']; cbn [isZeroN Nat.eqb encToksN encTokN].
  - rewrite encPushTokN; reflexivity.
  - reflexivity.
Qed.

Lemma stepGenF1PPN_sound (a : nat) (lTail : list TokN) (rL : LStackN)
    (bR : list TokN) (rR : RStackN) (bL_orig : list TokN)
    (HbL : encToksN bL_orig (encLN rL) = encW a (encToksN lTail (encLN rL))) :
  encHybN (HGenN QF true bL_orig rL bR rR) -[ tm ]->*
  encHybN (stepGenF1PPN a lTail rL bR rR bL_orig).
Proof.
  unfold stepGenF1PPN.
  destruct bR as [| [z0 | o0 | w0] [| [z | o1 | w1] rTail]]; try apply stepRawN_sound.
  - destruct (isOneN o0) eqn:Ho0; [| apply stepRawN_sound].
    apply isOneN_true in Ho0; subst o0.
    destruct rR; try apply stepRawN_sound.
    rewrite encFinishGenN; cbn [encHybN encToksN encTokN encRN qToQ bitToSym].
    rewrite HbL.
    pose proof (rule_f1_pp a (encToksN lTail (encLN rL)) lb0) as H.
    rewrite lb_zero_cons in H; exact H.
  - destruct (andb (isOneN o0) (negb (isZeroN z))) eqn:Hcond; [| apply stepRawN_sound].
    apply Bool.andb_true_iff in Hcond; destruct Hcond as [Ho0 Hz].
    apply isOneN_true in Ho0; apply Bool.negb_true_iff in Hz; apply isZeroN_false in Hz; subst o0.
    rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym].
    rewrite HbL, (enc0_pred_toks z rTail _ Hz), encPushTokN; cbn [encTokN].
    apply rule_f1_pp.
Qed.

Lemma stepGenP1N_sound (a b1 : nat) (lTail : list TokN) (rL : LStackN)
    (bR : list TokN) (rR : RStackN) (bL_orig : list TokN)
    (HbL : encToksN bL_orig (encLN rL) =
           encW a (S0 >> S1 >> S1 >> S0 >> encW b1 (encToksN lTail (encLN rL)))) :
  encHybN (HGenN QF true bL_orig rL bR rR) -[ tm ]->*
  encHybN (stepGenP1N a b1 lTail rL bR rR bL_orig).
Proof.
  unfold stepGenP1N.
  destruct bR as [| [z0 | o0 | w0] [| [z | o1 | w1] rTail]]; try apply stepRawN_sound.
  - destruct (isOneN o0) eqn:Ho0; [| apply stepRawN_sound].
    apply isOneN_true in Ho0; subst o0.
    destruct rR; try apply stepRawN_sound.
    rewrite encFinishGenN; cbn [encHybN encToksN encTokN encRN qToQ bitToSym].
    rewrite HbL, encL_tail_wN.
    pose proof (to_star (rule_P1 a (encW b1 (encToksN lTail (encLN rL))) lb0)) as H.
    rewrite lb_zero_cons in H; exact H.
  - destruct (andb (isOneN o0) (negb (isZeroN z))) eqn:Hcond; [| apply stepRawN_sound].
    apply Bool.andb_true_iff in Hcond; destruct Hcond as [Ho0 Hz].
    apply isOneN_true in Ho0; apply Bool.negb_true_iff in Hz; apply isZeroN_false in Hz; subst o0.
    set (rAfter := if isZeroN (z - 1) then rTail else TokZN (z - 1) :: rTail).
    destruct (popBitRN rAfter rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply stepRawN_sound].
    rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym].
    rewrite HbL, (enc0_pred_toks z rTail _ Hz).
    fold rAfter.
    rewrite (encPopBitRN _ _ _ _ _ Hp), encL_tail_wN.
    exact (to_star (rule_P1 a (encW b1 (encToksN lTail (encLN rL))) (bitToSym h' >> encToksN bR' (encRN rR')))).
Qed.

Lemma stepGenCoreN_sound (q : Q_st) (h : bool) (bL : list TokN) (rL : LStackN)
    (bR : list TokN) (rR : RStackN) :
  encHybN (HGenN q h bL rL bR rR) -[ tm ]->* encHybN (stepGenCoreN q h bL rL bR rR).
Proof.
  unfold stepGenCoreN.
  destruct q, h; try apply stepRawN_sound.
  - (* QA, true *)
    destruct bR as [| [z0 | n | c] rTail]; try apply stepRawN_sound.
    + (* TokON n :: rTail *)
      destruct (lebN 2 n) eqn:Hn2.
      * apply lebN_true in Hn2.
        destruct n as [| [| n']]; [lia | lia | ].
        replace (S (S n') - 2) with n' by lia.
        rewrite encFinishGenN; cbn [encHybN encToksN encTokN enc1 qToQ bitToSym].
        rewrite encPushTokN; cbn [encTokN].
        destruct (isZeroN n') eqn:Hz2.
        { apply isZeroN_true in Hz2; subst n'; cbn [enc1 encToksN].
          exact (to_star (micro_P3 (encToksN bL (encLN rL)) (encToksN rTail (encRN rR)))). }
        { cbn [encToksN encTokN].
          exact (to_star (micro_P3 (encToksN bL (encLN rL)) (enc1 n' (encToksN rTail (encRN rR))))). }
      * destruct (isOneN n) eqn:Hn1; [| apply stepRawN_sound].
        apply isOneN_true in Hn1; subst n.
        destruct rTail as [| [z | o1 | c] rTail2].
        { destruct rR; try apply stepRawN_sound.
          rewrite encFinishGenN; cbn [encHybN encToksN encTokN encRN qToQ bitToSym].
          rewrite encPushTokN; cbn [encTokN encW enc1].
          pose proof (to_star (micro_A_w1 (encToksN bL (encLN rL)) lb0)) as H.
          rewrite lb_zero_cons in H; exact H. }
        { (* TokON 1 :: TokZN z :: rTail2 *)
          destruct (isZeroN z) eqn:Hz0; [apply stepRawN_sound | ].
          apply isZeroN_false in Hz0.
          set (rAfter := if isZeroN (z - 1) then rTail2 else TokZN (z - 1) :: rTail2).
          assert (HrAfter : encHybN (HGenN QA true bL rL (TokON 1 :: TokZN z :: rTail2) rR) =
                            (encToksN bL (encLN rL)) {{A}}> (S1 >> S1 >> S0 >> encToksN rAfter (encRN rR))).
          { cbn [encHybN encToksN encTokN qToQ bitToSym].
            rewrite (enc0_pred_toks z rTail2 _ Hz0); reflexivity. }
          destruct rAfter as [| [z2 | o2 | c] rTail3] eqn:HeqAfter.
          - destruct (popBitRN [] rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply stepRawN_sound].
            rewrite encFinishGenN, HrAfter; cbn [encHybN qToQ].
            rewrite (encPopBitRN _ _ _ _ _ Hp), encPushTokN; cbn [encTokN encW].
            exact (to_star (micro_A_w1 (encToksN bL (encLN rL)) (bitToSym h' >> encToksN bR' (encRN rR')))).
          - destruct (popBitRN (TokZN z2 :: rTail3) rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply stepRawN_sound].
            rewrite encFinishGenN, HrAfter; cbn [encHybN qToQ].
            rewrite (encPopBitRN _ _ _ _ _ Hp), encPushTokN; cbn [encTokN encW].
            exact (to_star (micro_A_w1 (encToksN bL (encLN rL)) (bitToSym h' >> encToksN bR' (encRN rR')))).
          - destruct (popBitRN (TokON o2 :: rTail3) rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply stepRawN_sound].
            rewrite encFinishGenN, HrAfter; cbn [encHybN qToQ].
            rewrite (encPopBitRN _ _ _ _ _ Hp), encPushTokN; cbn [encTokN encW].
            exact (to_star (micro_A_w1 (encToksN bL (encLN rL)) (bitToSym h' >> encToksN bR' (encRN rR')))).
          - destruct (isZeroN c) eqn:Hc0.
            + destruct (popBitRN (TokWN c :: rTail3) rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply stepRawN_sound].
              rewrite encFinishGenN, HrAfter; cbn [encHybN qToQ].
              rewrite (encPopBitRN _ _ _ _ _ Hp), encPushTokN; cbn [encTokN encW].
              exact (to_star (micro_A_w1 (encToksN bL (encLN rL)) (bitToSym h' >> encToksN bR' (encRN rR')))).
            + destruct (popBitRN rTail3 rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply stepRawN_sound].
              rewrite encFinishGenN, HrAfter; cbn [encHybN encToksN encTokN qToQ].
              rewrite (encPopBitRN _ _ _ _ _ Hp), encPushTokN; cbn [encTokN].
              exact (to_star (rule_wR_A1 c (encToksN bL (encLN rL)) (bitToSym h' >> encToksN bR' (encRN rR')))). }
        { apply stepRawN_sound. }
        { (* TokON 1 :: TokWN c :: rTail2 *)
          destruct (isZeroN c) eqn:Hc0; [apply stepRawN_sound | ].
          apply isZeroN_false in Hc0.
          rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym].
          pose proof (encSubWHeadN c 1 rTail2 (encRN rR) ltac:(lia)) as Hsub; cbn [encToksN encTokN] in Hsub.
          rewrite Hsub; cbn [encW enc1 enc0].
          exact (to_star (micro_P3 (encToksN bL (encLN rL)) (S1 >> S0 >> encToksN (subWHeadN c 1 rTail2) (encRN rR)))). }
    + (* TokWN c :: rTail *)
      destruct (isZeroN c) eqn:Hc0; [apply stepRawN_sound | ].
      apply isZeroN_false in Hc0.
      rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym].
      pose proof (encSubWHeadN c 1 rTail (encRN rR) ltac:(lia)) as Hsub; cbn [encToksN encTokN] in Hsub.
      rewrite Hsub; cbn [encW enc1 enc0].
      exact (to_star (micro_P3 (encToksN bL (encLN rL)) (S0 >> encToksN (subWHeadN c 1 rTail) (encRN rR)))).
  - (* QC, false *)
    destruct bR as [| [z0 | o0 | c] rTail]; try apply stepRawN_sound.
    destruct (isZeroN c) eqn:Hc0; [apply stepRawN_sound | ].
    destruct (popBitRN rTail rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply stepRawN_sound].
    rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym].
    rewrite (encPopBitRN _ _ _ _ _ Hp), encPushTokN, (encPushBitN _ _ _ _ (isEmptyLN_spec rL)).
    cbn [encTokN bitToSym].
    exact (to_star (rule_wR_C0 c (encToksN bL (encLN rL)) (bitToSym h' >> encToksN bR' (encRN rR')))).
  - (* QF, true *)
    destruct bL as [| [z0 | o0 | a] lTail]; try apply stepRawN_sound.
    + (* TokZN z0 :: lTail *)
      destruct lTail as [| [z1 | o1 | b] lTail2]; try apply stepRawN_sound.
      destruct (isOneN z0) eqn:Hz01.
      * apply isOneN_true in Hz01; subst z0.
        destruct (isZeroN b) eqn:Hb0; [apply stepRawN_sound | ].
        apply isZeroN_false in Hb0.
        rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym].
        rewrite encL_tail_wN; cbn [encW enc0].
        replace b with (S (b - 1)) at 1 by lia; cbn [encW].
        exact (to_star (micro_P2 (encW (b - 1) (encToksN lTail2 (encLN rL))) (encToksN bR (encRN rR)))).
      * destruct (isTwoN z0) eqn:Hz02; [| apply stepRawN_sound].
        apply isTwoN_true in Hz02; subst z0.
        destruct (isZeroN b) eqn:Hb0; [apply stepRawN_sound | ].
        apply isZeroN_false in Hb0.
        rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym].
        rewrite encPushTokN, (encPushBitN _ _ _ _ (isEmptyRN_spec rR)); cbn [encTokN encW enc0 bitToSym].
        replace b with (S (b - 1)) at 1 by lia; cbn [encW].
        assert (HL : encToksN (if isZeroN (b - 1) then pushTokN (TokZN 1) lTail2
                               else TokZN 1 :: TokWN (b - 1) :: lTail2) (encLN rL) =
                     S0 >> encW (b - 1) (encToksN lTail2 (encLN rL))).
        { destruct (b - 1) as [| b']; cbn [isZeroN Nat.eqb encToksN encTokN];
            [rewrite encPushTokN; reflexivity | reflexivity]. }
        rewrite HL.
        exact (to_star (micro_P4 (encW (b - 1) (encToksN lTail2 (encLN rL))) (encToksN bR (encRN rR)))).
    + (* TokWN a :: lTail *)
      assert (HF1 : encHybN (HGenN QF true (TokWN a :: lTail) rL bR rR) -[ tm ]->*
                    encHybN (stepGenF1PPN a lTail rL bR rR (TokWN a :: lTail))).
      { apply stepGenF1PPN_sound; reflexivity. }
      destruct lTail as [| [z0 | o0 | w0] lTail1].
      * destruct (isZeroN a) eqn:Ha0; [apply stepRawN_sound | exact HF1].
      * (* TokWN a :: TokZN z0 :: lTail1 *)
        destruct lTail1 as [| [z2 | o2 | b] lTail2];
          try (destruct (isZeroN a) eqn:Ha0; [apply stepRawN_sound | exact HF1]).
        (* TokWN a :: TokZN z0 :: TokWN b :: lTail2 *)
        destruct (isOneN z0) eqn:Hz01.
        { apply isOneN_true in Hz01; subst z0.
          destruct (andb (negb (isZeroN a)) (negb (isZeroN b))) eqn:Hab.
          - apply Bool.andb_true_iff in Hab; destruct Hab as [Ha Hb].
            apply Bool.negb_true_iff in Ha; apply isZeroN_false in Ha.
            apply Bool.negb_true_iff in Hb; apply isZeroN_false in Hb.
            set (b1 := b - 1).
            assert (HP1 : encHybN (HGenN QF true (TokWN a :: TokZN 1 :: TokWN b :: lTail2) rL bR rR) -[ tm ]->*
                          encHybN (stepGenP1N a b1 lTail2 rL bR rR (TokWN a :: TokZN 1 :: TokWN b :: lTail2))).
            { apply stepGenP1N_sound; cbn [encToksN encTokN enc0].
              replace b with (S b1) at 1 by lia; reflexivity. }
            destruct bR as [| [zr0 | o0 | c] rTail]; try exact HP1.
            + (* TokON o0 :: rTail *)
              destruct rTail as [| [z1 | or1 | c] rTail2]; try exact HP1.
              * (* TokON o0 :: TokZN z1 :: rTail2 *)
                destruct (isOneN o0) eqn:Ho0; [| apply stepRawN_sound].
                apply isOneN_true in Ho0; subst o0.
                destruct (isTwoN z1) eqn:Hz12.
                { (* 1b. HC2 *)
                  apply isTwoN_true in Hz12; subst z1.
                  destruct (startsWith1N rTail2) eqn:Hsw; [| apply stepRawN_sound].
                  destruct (encStartsWith1N rTail2 (encRN rR) Hsw) as [r' Hr'].
                  rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym enc0 enc1].
                  rewrite encL_tail_wN, Hr'.
                  replace b with (S b1) at 1 by lia; cbn [encW].
                  exact (to_star (rule_HC2 a (encW b1 (encToksN lTail2 (encLN rL))) r')). }
                { destruct (isThreeN z1) eqn:Hz13; [| exact HP1].
                  apply isThreeN_true in Hz13; subst z1.
                  destruct rTail2 as [| [zr2 | or2 | c] rTail3]; try exact HP1.
                  destruct (negb (isZeroN c)) eqn:Hc; [| exact HP1].
                  apply Bool.negb_true_iff in Hc; apply isZeroN_false in Hc.
                  (* 1c. B3 *)
                  set (ok := if isOneN c then startsWith1N rTail3 else true).
                  destruct ok eqn:Hok; [| apply stepRawN_sound].
                  assert (Hrem : 1 < c \/ (1 = c /\ startsWith1N rTail3 = true)).
                  { subst ok; destruct (isOneN c) eqn:Hc1.
                    - apply isOneN_true in Hc1; right; split; [lia | exact Hok].
                    - unfold isOneN in Hc1; apply Nat.eqb_neq in Hc1; left; lia. }
                  destruct (subWHeadN_starts1 c 1 rTail3 (encRN rR) Hrem) as [r' Hr'].
                  pose proof (encSubWHeadN c 1 rTail3 (encRN rR) ltac:(lia)) as Hsub; cbn [encToksN encTokN] in Hsub.
                  rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym enc0 enc1].
                  rewrite encL_tail_w3N, Hsub, Hr'; cbn [encW].
                  replace b with (S b1) at 1 by lia; cbn [encW].
                  exact (to_star (rule_B3 a (encW b1 (encToksN lTail2 (encLN rL))) r')). }
              * (* 1d. B2: TokON o0 :: TokWN c :: rTail2 *)
                destruct (andb (isOneN o0) (lebN 2 c)) eqn:Hoc; [| apply stepRawN_sound].
                apply Bool.andb_true_iff in Hoc; destruct Hoc as [Ho0 Hc2].
                apply isOneN_true in Ho0; apply lebN_true in Hc2; subst o0.
                destruct (lebN 2 b) eqn:Hb2; [| apply stepRawN_sound].
                apply lebN_true in Hb2.
                set (ok := if isTwoN c then startsWith1N rTail2 else true).
                destruct ok eqn:Hok; [| apply stepRawN_sound].
                assert (Hrem : 2 < c \/ (2 = c /\ startsWith1N rTail2 = true)).
                { subst ok; destruct (isTwoN c) eqn:Hc_two.
                  - apply isTwoN_true in Hc_two; right; split; [lia | exact Hok].
                  - unfold isTwoN in Hc_two; apply Nat.eqb_neq in Hc_two; left; lia. }
                destruct (subWHeadN_starts1 c 2 rTail2 (encRN rR) Hrem) as [r' Hr'].
                pose proof (encSubWHeadN c 2 rTail2 (encRN rR) Hc2) as Hsub; cbn [encToksN encTokN] in Hsub.
                rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym enc0 enc1].
                rewrite encL_tail_w3N, Hsub, Hr'.
                replace b with (2 + (b - 2)) at 1 by lia; rewrite (encW_add 2 (b - 2)).
                exact (to_star (rule_B2 a (encW (b - 2) (encToksN lTail2 (encLN rL))) r')).
            + (* 1a. J3A / HC1: TokWN c :: rTail *)
              destruct (isZeroN c) eqn:Hc0; [apply stepRawN_sound | ].
              apply isZeroN_false in Hc0.
              set (b2 := halfN b).
              set (k0 := if lebN b2 c then b2 else c).
              set (k := if eqbN k0 c then (if startsWith1N rTail then k0 else k0 - 1) else k0).
              destruct (negb (isZeroN k)) eqn:Hk.
              * (* J3A(k) *)
                apply Bool.negb_true_iff in Hk; apply isZeroN_false in Hk.
                pose proof (halfN_evenN_spec b) as Hb_half; fold b2 in Hb_half.
                assert (Hk0_bounds : k0 <= b2 /\ k0 <= c).
                { subst k0; destruct (lebN b2 c) eqn:Hbc;
                    [apply lebN_true in Hbc; lia | apply lebN_false in Hbc; lia]. }
                assert (Hk_le_k0 : k <= k0).
                { subst k; destruct (eqbN k0 c); [destruct (startsWith1N rTail); lia | lia]. }
                assert (Hrem : k < c \/ (k = c /\ startsWith1N rTail = true)).
                { subst k; destruct (eqbN k0 c) eqn:Hk0c.
                  - apply eqbN_true in Hk0c.
                    destruct (startsWith1N rTail) eqn:Hsw; [right; split; [lia | reflexivity] | left; lia].
                  - apply eqbN_false in Hk0c; left; lia. }
                destruct (subWHeadN_starts1 c k rTail (encRN rR) Hrem) as [r' Hr'].
                pose proof (encSubWHeadN c k rTail (encRN rR) ltac:(lia)) as Hsub; cbn [encToksN encTokN] in Hsub.
                rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym enc0].
                rewrite encL_tail_wN, Hsub, Hr'.
                assert (Hb_split : b = 2 * k + (b - 2 * k)) by (destruct (evenN b); lia).
                rewrite Hb_split at 1; rewrite (encW_add (2 * k) (b - 2 * k)).
                replace (a + mul3addcN 0 k) with (a + 3 * k) by (unfold mul3addcN; lia).
                exact (rule_J3A k a (encW (b - 2 * k) (encToksN lTail2 (encLN rL))) r').
              * (* HC1 *)
                pose proof (encSubWHeadN c 1 rTail (encRN rR) ltac:(lia)) as Hsub; cbn [encToksN encTokN] in Hsub.
                rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym enc0 enc1].
                rewrite encL_tail_wN, encPushTokN, Hsub; cbn [encTokN encW enc0].
                replace b with (S b1) at 1 by lia; cbn [encW].
                exact (to_star (rule_HC1_gen a (encW b1 (encToksN lTail2 (encLN rL)))
                                  (S0 >> encToksN (subWHeadN c 1 rTail) (encRN rR)))).
          - destruct (negb (isZeroN a)) eqn:Ha;
              [exact HF1 | apply stepRawN_sound]. }
        { (* z0 <> 1 *)
          destruct (isTwoN z0) eqn:Hz02.
          - (* Pattern 2: z0 = 2, B1 or F1_pp *)
            apply isTwoN_true in Hz02; subst z0.
            destruct (andb (negb (isZeroN a)) (lebN 3 b)) eqn:Hab3.
            + apply Bool.andb_true_iff in Hab3; destruct Hab3 as [Ha Hb3].
              apply Bool.negb_true_iff in Ha; apply isZeroN_false in Ha.
              apply lebN_true in Hb3.
              destruct (startsWith1N bR) eqn:Hsw.
              * destruct (encStartsWith1N bR (encRN rR) Hsw) as [r' Hr'].
                rewrite encFinishGenN; cbn [encHybN encToksN encTokN qToQ bitToSym enc0].
                rewrite encPushTokN, (encPushBitN _ _ _ _ (isEmptyRN_spec rR)); cbn [encTokN bitToSym].
                pose proof (encL_tail_wN 3 (b - 3) lTail2 rL) as HL; rewrite HL; rewrite Hr'.
                replace b with (3 + (b - 3)) at 1 by lia; rewrite (encW_add 3 (b - 3)).
                exact (to_star (rule_B1 a (encW (b - 3) (encToksN lTail2 (encLN rL))) r')).
              * apply stepGenF1PPN_sound; reflexivity.
            + destruct (negb (isZeroN a)) eqn:Ha;
                [exact HF1 | apply stepRawN_sound].
          - destruct (negb (isZeroN a)) eqn:Ha;
              [exact HF1 | apply stepRawN_sound]. }
      * (* TokWN a :: TokON o0 :: lTail1 *)
        destruct lTail1 as [| t2 lTail2];
          [| destruct (isZeroN a) eqn:Ha0; [apply stepRawN_sound | exact HF1]].
        (* Pattern 3: [TokWN a; TokON o0] *)
        destruct (andb (negb (isZeroN a)) (isOneN o0)) eqn:Hao.
        { apply Bool.andb_true_iff in Hao; destruct Hao as [Ha Ho0].
          apply Bool.negb_true_iff in Ha; apply isZeroN_false in Ha.
          apply isOneN_true in Ho0; subst o0.
          destruct rL; try (apply stepGenF1PPN_sound; reflexivity).
          destruct bR as [| [zr0 | or0 | c] rTail]; try (apply stepGenF1PPN_sound; reflexivity).
          destruct (isZeroN c) eqn:Hc0; [apply stepRawN_sound | ].
          apply isZeroN_false in Hc0.
          set (k := if startsWith1N rTail then c else c - 1).
          destruct (negb (isZeroN k)) eqn:Hk; [| apply stepRawN_sound].
          apply Bool.negb_true_iff in Hk; apply isZeroN_false in Hk.
          assert (Hrem : k < c \/ (k = c /\ startsWith1N rTail = true)).
          { subst k; destruct (startsWith1N rTail); [right; split; [reflexivity | reflexivity] | left; lia]. }
          destruct (subWHeadN_starts1 c k rTail (encRN rR) Hrem) as [r' Hr'].
          pose proof (encSubWHeadN c k rTail (encRN rR) ltac:(subst k; destruct (startsWith1N rTail); lia)) as Hsub;
            cbn [encToksN encTokN] in Hsub.
          rewrite encFinishGenN; cbn [encHybN encToksN encTokN encLN qToQ bitToSym enc1].
          rewrite Hsub, Hr'.
          replace (a + mul3addcN 0 k) with (a + 3 * k) by (unfold mul3addcN; lia).
          exact (rule_J3B k a r'). }
        { destruct (negb (isZeroN a)) eqn:Ha;
            [exact HF1 | apply stepRawN_sound]. }
      * (* TokWN a :: TokWN w0 :: lTail1 *)
        destruct (isZeroN a) eqn:Ha0; [apply stepRawN_sound | exact HF1].
Qed.

Lemma stepGenN_sound (q : Q_st) (h : bool) (bL : list TokN) (rL : LStackN)
    (bR : list TokN) (rR : RStackN) :
  encHybN (HGenN q h bL rL bR rR) -[ tm ]->* encHybN (stepGenN q h bL rL bR rR).
Proof.
  unfold stepGenN.
  assert (Heq : encHybN (HGenN q h bL rL bR rR) =
                encHybN (HGenN q h (fst (ensureLN bL rL)) (snd (ensureLN bL rL))
                                   (fst (ensureRN bR rR)) (snd (ensureRN bR rR)))).
  { cbn [encHybN]; rewrite encEnsureLN, encEnsureRN; reflexivity. }
  rewrite Heq.
  apply stepGenCoreN_sound.
Qed.

Lemma runGenChunkN_sound (kg : nat) :
  forall (s : HybStateN), encHybN s -[ tm ]->* encHybN (runGenChunkN kg s).
Proof.
  induction kg as [| kg' IH]; intros [sL sR | q h bL rL bR rR]; cbn [runGenChunkN].
  - apply evstep_refl.
  - apply evstep_refl.
  - apply evstep_refl.
  - exact (stepStar_trans (stepGenN_sound q h bL rL bR rR) (IH _)).
Qed.

Lemma stepOuterN_sound (s : HybStateN) :
  encHybN s -[ tm ]->* encHybN (stepOuterN s).
Proof.
  destruct s as [sL sR | q h bL rL bR rR]; cbn [stepOuterN].
  - apply runCleanChunkN_sound.
  - apply runGenChunkN_sound.
Qed.

Lemma Pos_iter_sound (p : positive) :
  forall (s : HybStateN), encHybN s -[ tm ]->* encHybN (Pos.iter stepOuterN s p).
Proof.
  induction p as [p IHp | p IHp | ]; intros s; cbn [Pos.iter].
  - eapply stepStar_trans; [apply IHp | ].
    eapply stepStar_trans; [apply IHp | apply stepOuterN_sound].
  - eapply stepStar_trans; [apply IHp | apply IHp].
  - apply stepOuterN_sound.
Qed.

Lemma check_cycler_entryN_sound (s : HybStateN) :
  check_cycler_entryN s = true ->
  exists restL : side, encHybN s = (encW 18 restL) {{A}}> (S1 >> lb0).
Proof.
  destruct s as [sL sR | q h bL rL bR rR]; cbn [check_cycler_entryN]; [discriminate | ].
  destruct q; try discriminate.
  destruct h; [| discriminate].
  destruct bL as [| [z | o | n] bL_rest]; try discriminate.
  destruct bR as [| tR bR_rest]; [| discriminate].
  destruct rR; try discriminate.
  intro Hleb; apply lebN_true in Hleb.
  exists (encW (n - 18) (encToksN bL_rest (encLN rL))).
  cbn [encHybN encToksN encTokN encRN qToQ bitToSym].
  rewrite <- encW_add.
  replace (18 + (n - 18)) with n by lia.
  reflexivity.
Qed.

(** ** 6. Fast Base-64 ([D64] / [Big]) Stepper & Shadow Interpretation *)

Inductive D64 : Type :=
  | D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7
  | D8 | D9 | D10 | D11 | D12 | D13 | D14 | D15
  | D16 | D17 | D18 | D19 | D20 | D21 | D22 | D23
  | D24 | D25 | D26 | D27 | D28 | D29 | D30 | D31
  | D32 | D33 | D34 | D35 | D36 | D37 | D38 | D39
  | D40 | D41 | D42 | D43 | D44 | D45 | D46 | D47
  | D48 | D49 | D50 | D51 | D52 | D53 | D54 | D55
  | D56 | D57 | D58 | D59 | D60 | D61 | D62 | D63.

Inductive R128 : Type :=
  | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7
  | P8 | P9 | P10 | P11 | P12 | P13 | P14 | P15
  | P16 | P17 | P18 | P19 | P20 | P21 | P22 | P23
  | P24 | P25 | P26 | P27 | P28 | P29 | P30 | P31
  | P32 | P33 | P34 | P35 | P36 | P37 | P38 | P39
  | P40 | P41 | P42 | P43 | P44 | P45 | P46 | P47
  | P48 | P49 | P50 | P51 | P52 | P53 | P54 | P55
  | P56 | P57 | P58 | P59 | P60 | P61 | P62 | P63
  | P64 | P65 | P66 | P67 | P68 | P69 | P70 | P71
  | P72 | P73 | P74 | P75 | P76 | P77 | P78 | P79
  | P80 | P81 | P82 | P83 | P84 | P85 | P86 | P87
  | P88 | P89 | P90 | P91 | P92 | P93 | P94 | P95
  | P96 | P97 | P98 | P99 | P100 | P101 | P102 | P103
  | P104 | P105 | P106 | P107 | P108 | P109 | P110 | P111
  | P112 | P113 | P114 | P115 | P116 | P117 | P118 | P119
  | P120 | P121 | P122 | P123 | P124 | P125 | P126 | P127.

Inductive R256 : Type :=
  | W0 | W1 | W2 | W3 | W4 | W5 | W6 | W7
  | W8 | W9 | W10 | W11 | W12 | W13 | W14 | W15
  | W16 | W17 | W18 | W19 | W20 | W21 | W22 | W23
  | W24 | W25 | W26 | W27 | W28 | W29 | W30 | W31
  | W32 | W33 | W34 | W35 | W36 | W37 | W38 | W39
  | W40 | W41 | W42 | W43 | W44 | W45 | W46 | W47
  | W48 | W49 | W50 | W51 | W52 | W53 | W54 | W55
  | W56 | W57 | W58 | W59 | W60 | W61 | W62 | W63
  | W64 | W65 | W66 | W67 | W68 | W69 | W70 | W71
  | W72 | W73 | W74 | W75 | W76 | W77 | W78 | W79
  | W80 | W81 | W82 | W83 | W84 | W85 | W86 | W87
  | W88 | W89 | W90 | W91 | W92 | W93 | W94 | W95
  | W96 | W97 | W98 | W99 | W100 | W101 | W102 | W103
  | W104 | W105 | W106 | W107 | W108 | W109 | W110 | W111
  | W112 | W113 | W114 | W115 | W116 | W117 | W118 | W119
  | W120 | W121 | W122 | W123 | W124 | W125 | W126 | W127
  | W128 | W129 | W130 | W131 | W132 | W133 | W134 | W135
  | W136 | W137 | W138 | W139 | W140 | W141 | W142 | W143
  | W144 | W145 | W146 | W147 | W148 | W149 | W150 | W151
  | W152 | W153 | W154 | W155 | W156 | W157 | W158 | W159
  | W160 | W161 | W162 | W163 | W164 | W165 | W166 | W167
  | W168 | W169 | W170 | W171 | W172 | W173 | W174 | W175
  | W176 | W177 | W178 | W179 | W180 | W181 | W182 | W183
  | W184 | W185 | W186 | W187 | W188 | W189 | W190 | W191
  | W192 | W193 | W194 | W195 | W196 | W197 | W198 | W199
  | W200 | W201 | W202 | W203 | W204 | W205 | W206 | W207
  | W208 | W209 | W210 | W211 | W212 | W213 | W214 | W215
  | W216 | W217 | W218 | W219 | W220 | W221 | W222 | W223
  | W224 | W225 | W226 | W227 | W228 | W229 | W230 | W231
  | W232 | W233 | W234 | W235 | W236 | W237 | W238 | W239
  | W240 | W241 | W242 | W243 | W244 | W245 | W246 | W247
  | W248 | W249 | W250 | W251 | W252 | W253 | W254 | W255.

Inductive C6 : Type := C0 | C1 | C2 | C3 | C4 | C5.

Inductive Big : Type :=
  | BNil
  | BUnder
  | BCons (d : D64) (tl : Big).

Definition mkBCons (d : D64) (tl : Big) : Big :=
  match d with
  | D0 => match tl with BNil => BNil | _ => BCons D0 tl end
  | _ => BCons d tl
  end.

Definition combineTry (lo : D64) (z : Big) : Big :=
  match lo with
  | D0 => match z with BNil => BNil | BUnder => BUnder | BCons d tl => BCons D0 (BCons d tl) end
  | _ => match z with BNil => BCons lo BNil | BUnder => BUnder | BCons d tl => BCons lo (BCons d tl) end
  end.

Definition B0 : Big := BNil.
Definition B1 : Big := BCons D1 BNil.
Definition B2 : Big := BCons D2 BNil.
Definition B3 : Big := BCons D3 BNil.
Definition B18 : Big := BCons D18 BNil.

Definition isZeroB (x : Big) : bool :=
  match x with BNil => true | BUnder => true | BCons _ _ => false end.

Definition isOneB (x : Big) : bool :=
  match x with BCons D1 BNil => true | _ => false end.

Definition isTwoB (x : Big) : bool :=
  match x with BCons D2 BNil => true | _ => false end.

Definition isThreeB (x : Big) : bool :=
  match x with BCons D3 BNil => true | _ => false end.

Definition oddB (x : Big) : bool := match x with BCons d _ => match d with D0 => false | D1 => true | D2 => false | D3 => true | D4 => false | D5 => true | D6 => false | D7 => true | D8 => false | D9 => true | D10 => false | D11 => true | D12 => false | D13 => true | D14 => false | D15 => true | D16 => false | D17 => true | D18 => false | D19 => true | D20 => false | D21 => true | D22 => false | D23 => true | D24 => false | D25 => true | D26 => false | D27 => true | D28 => false | D29 => true | D30 => false | D31 => true | D32 => false | D33 => true | D34 => false | D35 => true | D36 => false | D37 => true | D38 => false | D39 => true | D40 => false | D41 => true | D42 => false | D43 => true | D44 => false | D45 => true | D46 => false | D47 => true | D48 => false | D49 => true | D50 => false | D51 => true | D52 => false | D53 => true | D54 => false | D55 => true | D56 => false | D57 => true | D58 => false | D59 => true | D60 => false | D61 => true | D62 => false | D63 => true end | _ => false end.
Definition evenB (x : Big) : bool := match x with BCons d _ => match d with D0 => true | D1 => false | D2 => true | D3 => false | D4 => true | D5 => false | D6 => true | D7 => false | D8 => true | D9 => false | D10 => true | D11 => false | D12 => true | D13 => false | D14 => true | D15 => false | D16 => true | D17 => false | D18 => true | D19 => false | D20 => true | D21 => false | D22 => true | D23 => false | D24 => true | D25 => false | D26 => true | D27 => false | D28 => true | D29 => false | D30 => true | D31 => false | D32 => true | D33 => false | D34 => true | D35 => false | D36 => true | D37 => false | D38 => true | D39 => false | D40 => true | D41 => false | D42 => true | D43 => false | D44 => true | D45 => false | D46 => true | D47 => false | D48 => true | D49 => false | D50 => true | D51 => false | D52 => true | D53 => false | D54 => true | D55 => false | D56 => true | D57 => false | D58 => true | D59 => false | D60 => true | D61 => false | D62 => true | D63 => false end | _ => true end.

Fixpoint incB (x : Big) : Big :=
  match x with
  | BCons d xt => match d with D0 => BCons D1 xt | D1 => BCons D2 xt | D2 => BCons D3 xt | D3 => BCons D4 xt | D4 => BCons D5 xt | D5 => BCons D6 xt | D6 => BCons D7 xt | D7 => BCons D8 xt | D8 => BCons D9 xt | D9 => BCons D10 xt | D10 => BCons D11 xt | D11 => BCons D12 xt | D12 => BCons D13 xt | D13 => BCons D14 xt | D14 => BCons D15 xt | D15 => BCons D16 xt | D16 => BCons D17 xt | D17 => BCons D18 xt | D18 => BCons D19 xt | D19 => BCons D20 xt | D20 => BCons D21 xt | D21 => BCons D22 xt | D22 => BCons D23 xt | D23 => BCons D24 xt | D24 => BCons D25 xt | D25 => BCons D26 xt | D26 => BCons D27 xt | D27 => BCons D28 xt | D28 => BCons D29 xt | D29 => BCons D30 xt | D30 => BCons D31 xt | D31 => BCons D32 xt | D32 => BCons D33 xt | D33 => BCons D34 xt | D34 => BCons D35 xt | D35 => BCons D36 xt | D36 => BCons D37 xt | D37 => BCons D38 xt | D38 => BCons D39 xt | D39 => BCons D40 xt | D40 => BCons D41 xt | D41 => BCons D42 xt | D42 => BCons D43 xt | D43 => BCons D44 xt | D44 => BCons D45 xt | D45 => BCons D46 xt | D46 => BCons D47 xt | D47 => BCons D48 xt | D48 => BCons D49 xt | D49 => BCons D50 xt | D50 => BCons D51 xt | D51 => BCons D52 xt | D52 => BCons D53 xt | D53 => BCons D54 xt | D54 => BCons D55 xt | D55 => BCons D56 xt | D56 => BCons D57 xt | D57 => BCons D58 xt | D58 => BCons D59 xt | D59 => BCons D60 xt | D60 => BCons D61 xt | D61 => BCons D62 xt | D62 => BCons D63 xt | D63 => BCons D0 (incB xt) end
  | _ => B1
  end.

Fixpoint dec1B (x : Big) : Big :=
  match x with
  | BCons d xt => match d with D0 => BCons D63 (dec1B xt) | D1 => mkBCons D0 xt | D2 => BCons D1 xt | D3 => BCons D2 xt | D4 => BCons D3 xt | D5 => BCons D4 xt | D6 => BCons D5 xt | D7 => BCons D6 xt | D8 => BCons D7 xt | D9 => BCons D8 xt | D10 => BCons D9 xt | D11 => BCons D10 xt | D12 => BCons D11 xt | D13 => BCons D12 xt | D14 => BCons D13 xt | D15 => BCons D14 xt | D16 => BCons D15 xt | D17 => BCons D16 xt | D18 => BCons D17 xt | D19 => BCons D18 xt | D20 => BCons D19 xt | D21 => BCons D20 xt | D22 => BCons D21 xt | D23 => BCons D22 xt | D24 => BCons D23 xt | D25 => BCons D24 xt | D26 => BCons D25 xt | D27 => BCons D26 xt | D28 => BCons D27 xt | D29 => BCons D28 xt | D30 => BCons D29 xt | D31 => BCons D30 xt | D32 => BCons D31 xt | D33 => BCons D32 xt | D34 => BCons D33 xt | D35 => BCons D34 xt | D36 => BCons D35 xt | D37 => BCons D36 xt | D38 => BCons D37 xt | D39 => BCons D38 xt | D40 => BCons D39 xt | D41 => BCons D40 xt | D42 => BCons D41 xt | D43 => BCons D42 xt | D44 => BCons D43 xt | D45 => BCons D44 xt | D46 => BCons D45 xt | D47 => BCons D46 xt | D48 => BCons D47 xt | D49 => BCons D48 xt | D50 => BCons D49 xt | D51 => BCons D50 xt | D52 => BCons D51 xt | D53 => BCons D52 xt | D54 => BCons D53 xt | D55 => BCons D54 xt | D56 => BCons D55 xt | D57 => BCons D56 xt | D58 => BCons D57 xt | D59 => BCons D58 xt | D60 => BCons D59 xt | D61 => BCons D60 xt | D62 => BCons D61 xt | D63 => BCons D62 xt end
  | _ => BNil
  end.

Definition dec2B (x : Big) : Big :=
  match x with
  | BCons d xt => match d with D0 => BCons D62 (dec1B xt) | D1 => BCons D63 (dec1B xt) | D2 => mkBCons D0 xt | D3 => BCons D1 xt | D4 => BCons D2 xt | D5 => BCons D3 xt | D6 => BCons D4 xt | D7 => BCons D5 xt | D8 => BCons D6 xt | D9 => BCons D7 xt | D10 => BCons D8 xt | D11 => BCons D9 xt | D12 => BCons D10 xt | D13 => BCons D11 xt | D14 => BCons D12 xt | D15 => BCons D13 xt | D16 => BCons D14 xt | D17 => BCons D15 xt | D18 => BCons D16 xt | D19 => BCons D17 xt | D20 => BCons D18 xt | D21 => BCons D19 xt | D22 => BCons D20 xt | D23 => BCons D21 xt | D24 => BCons D22 xt | D25 => BCons D23 xt | D26 => BCons D24 xt | D27 => BCons D25 xt | D28 => BCons D26 xt | D29 => BCons D27 xt | D30 => BCons D28 xt | D31 => BCons D29 xt | D32 => BCons D30 xt | D33 => BCons D31 xt | D34 => BCons D32 xt | D35 => BCons D33 xt | D36 => BCons D34 xt | D37 => BCons D35 xt | D38 => BCons D36 xt | D39 => BCons D37 xt | D40 => BCons D38 xt | D41 => BCons D39 xt | D42 => BCons D40 xt | D43 => BCons D41 xt | D44 => BCons D42 xt | D45 => BCons D43 xt | D46 => BCons D44 xt | D47 => BCons D45 xt | D48 => BCons D46 xt | D49 => BCons D47 xt | D50 => BCons D48 xt | D51 => BCons D49 xt | D52 => BCons D50 xt | D53 => BCons D51 xt | D54 => BCons D52 xt | D55 => BCons D53 xt | D56 => BCons D54 xt | D57 => BCons D55 xt | D58 => BCons D56 xt | D59 => BCons D57 xt | D60 => BCons D58 xt | D61 => BCons D59 xt | D62 => BCons D60 xt | D63 => BCons D61 xt end
  | _ => BNil
  end.

Definition subSmall1B (x : Big) : Big := match x with BCons d xt => match d with D0 => match xt with BCons _ _ => BCons D63 (dec1B xt) | _ => BNil end | D1 => mkBCons D0 xt | D2 => BCons D1 xt | D3 => BCons D2 xt | D4 => BCons D3 xt | D5 => BCons D4 xt | D6 => BCons D5 xt | D7 => BCons D6 xt | D8 => BCons D7 xt | D9 => BCons D8 xt | D10 => BCons D9 xt | D11 => BCons D10 xt | D12 => BCons D11 xt | D13 => BCons D12 xt | D14 => BCons D13 xt | D15 => BCons D14 xt | D16 => BCons D15 xt | D17 => BCons D16 xt | D18 => BCons D17 xt | D19 => BCons D18 xt | D20 => BCons D19 xt | D21 => BCons D20 xt | D22 => BCons D21 xt | D23 => BCons D22 xt | D24 => BCons D23 xt | D25 => BCons D24 xt | D26 => BCons D25 xt | D27 => BCons D26 xt | D28 => BCons D27 xt | D29 => BCons D28 xt | D30 => BCons D29 xt | D31 => BCons D30 xt | D32 => BCons D31 xt | D33 => BCons D32 xt | D34 => BCons D33 xt | D35 => BCons D34 xt | D36 => BCons D35 xt | D37 => BCons D36 xt | D38 => BCons D37 xt | D39 => BCons D38 xt | D40 => BCons D39 xt | D41 => BCons D40 xt | D42 => BCons D41 xt | D43 => BCons D42 xt | D44 => BCons D43 xt | D45 => BCons D44 xt | D46 => BCons D45 xt | D47 => BCons D46 xt | D48 => BCons D47 xt | D49 => BCons D48 xt | D50 => BCons D49 xt | D51 => BCons D50 xt | D52 => BCons D51 xt | D53 => BCons D52 xt | D54 => BCons D53 xt | D55 => BCons D54 xt | D56 => BCons D55 xt | D57 => BCons D56 xt | D58 => BCons D57 xt | D59 => BCons D58 xt | D60 => BCons D59 xt | D61 => BCons D60 xt | D62 => BCons D61 xt | D63 => BCons D62 xt end | _ => BNil end.
Definition subSmall2B (x : Big) : Big := match x with BCons d xt => match d with D0 => match xt with BCons _ _ => BCons D62 (dec1B xt) | _ => BNil end | D1 => match xt with BCons _ _ => BCons D63 (dec1B xt) | _ => BNil end | D2 => mkBCons D0 xt | D3 => BCons D1 xt | D4 => BCons D2 xt | D5 => BCons D3 xt | D6 => BCons D4 xt | D7 => BCons D5 xt | D8 => BCons D6 xt | D9 => BCons D7 xt | D10 => BCons D8 xt | D11 => BCons D9 xt | D12 => BCons D10 xt | D13 => BCons D11 xt | D14 => BCons D12 xt | D15 => BCons D13 xt | D16 => BCons D14 xt | D17 => BCons D15 xt | D18 => BCons D16 xt | D19 => BCons D17 xt | D20 => BCons D18 xt | D21 => BCons D19 xt | D22 => BCons D20 xt | D23 => BCons D21 xt | D24 => BCons D22 xt | D25 => BCons D23 xt | D26 => BCons D24 xt | D27 => BCons D25 xt | D28 => BCons D26 xt | D29 => BCons D27 xt | D30 => BCons D28 xt | D31 => BCons D29 xt | D32 => BCons D30 xt | D33 => BCons D31 xt | D34 => BCons D32 xt | D35 => BCons D33 xt | D36 => BCons D34 xt | D37 => BCons D35 xt | D38 => BCons D36 xt | D39 => BCons D37 xt | D40 => BCons D38 xt | D41 => BCons D39 xt | D42 => BCons D40 xt | D43 => BCons D41 xt | D44 => BCons D42 xt | D45 => BCons D43 xt | D46 => BCons D44 xt | D47 => BCons D45 xt | D48 => BCons D46 xt | D49 => BCons D47 xt | D50 => BCons D48 xt | D51 => BCons D49 xt | D52 => BCons D50 xt | D53 => BCons D51 xt | D54 => BCons D52 xt | D55 => BCons D53 xt | D56 => BCons D54 xt | D57 => BCons D55 xt | D58 => BCons D56 xt | D59 => BCons D57 xt | D60 => BCons D58 xt | D61 => BCons D59 xt | D62 => BCons D60 xt | D63 => BCons D61 xt end | _ => BNil end.
Definition subSmall3B (x : Big) : Big := match x with BCons d xt => match d with D0 => match xt with BCons _ _ => BCons D61 (dec1B xt) | _ => BNil end | D1 => match xt with BCons _ _ => BCons D62 (dec1B xt) | _ => BNil end | D2 => match xt with BCons _ _ => BCons D63 (dec1B xt) | _ => BNil end | D3 => mkBCons D0 xt | D4 => BCons D1 xt | D5 => BCons D2 xt | D6 => BCons D3 xt | D7 => BCons D4 xt | D8 => BCons D5 xt | D9 => BCons D6 xt | D10 => BCons D7 xt | D11 => BCons D8 xt | D12 => BCons D9 xt | D13 => BCons D10 xt | D14 => BCons D11 xt | D15 => BCons D12 xt | D16 => BCons D13 xt | D17 => BCons D14 xt | D18 => BCons D15 xt | D19 => BCons D16 xt | D20 => BCons D17 xt | D21 => BCons D18 xt | D22 => BCons D19 xt | D23 => BCons D20 xt | D24 => BCons D21 xt | D25 => BCons D22 xt | D26 => BCons D23 xt | D27 => BCons D24 xt | D28 => BCons D25 xt | D29 => BCons D26 xt | D30 => BCons D27 xt | D31 => BCons D28 xt | D32 => BCons D29 xt | D33 => BCons D30 xt | D34 => BCons D31 xt | D35 => BCons D32 xt | D36 => BCons D33 xt | D37 => BCons D34 xt | D38 => BCons D35 xt | D39 => BCons D36 xt | D40 => BCons D37 xt | D41 => BCons D38 xt | D42 => BCons D39 xt | D43 => BCons D40 xt | D44 => BCons D41 xt | D45 => BCons D42 xt | D46 => BCons D43 xt | D47 => BCons D44 xt | D48 => BCons D45 xt | D49 => BCons D46 xt | D50 => BCons D47 xt | D51 => BCons D48 xt | D52 => BCons D49 xt | D53 => BCons D50 xt | D54 => BCons D51 xt | D55 => BCons D52 xt | D56 => BCons D53 xt | D57 => BCons D54 xt | D58 => BCons D55 xt | D59 => BCons D56 xt | D60 => BCons D57 xt | D61 => BCons D58 xt | D62 => BCons D59 xt | D63 => BCons D60 xt end | _ => BNil end.

Definition addSmall1B (x : Big) : Big := incB x.
Definition addSmall2B (x : Big) : Big := match x with BCons d xt => match d with D0 => BCons D2 xt | D1 => BCons D3 xt | D2 => BCons D4 xt | D3 => BCons D5 xt | D4 => BCons D6 xt | D5 => BCons D7 xt | D6 => BCons D8 xt | D7 => BCons D9 xt | D8 => BCons D10 xt | D9 => BCons D11 xt | D10 => BCons D12 xt | D11 => BCons D13 xt | D12 => BCons D14 xt | D13 => BCons D15 xt | D14 => BCons D16 xt | D15 => BCons D17 xt | D16 => BCons D18 xt | D17 => BCons D19 xt | D18 => BCons D20 xt | D19 => BCons D21 xt | D20 => BCons D22 xt | D21 => BCons D23 xt | D22 => BCons D24 xt | D23 => BCons D25 xt | D24 => BCons D26 xt | D25 => BCons D27 xt | D26 => BCons D28 xt | D27 => BCons D29 xt | D28 => BCons D30 xt | D29 => BCons D31 xt | D30 => BCons D32 xt | D31 => BCons D33 xt | D32 => BCons D34 xt | D33 => BCons D35 xt | D34 => BCons D36 xt | D35 => BCons D37 xt | D36 => BCons D38 xt | D37 => BCons D39 xt | D38 => BCons D40 xt | D39 => BCons D41 xt | D40 => BCons D42 xt | D41 => BCons D43 xt | D42 => BCons D44 xt | D43 => BCons D45 xt | D44 => BCons D46 xt | D45 => BCons D47 xt | D46 => BCons D48 xt | D47 => BCons D49 xt | D48 => BCons D50 xt | D49 => BCons D51 xt | D50 => BCons D52 xt | D51 => BCons D53 xt | D52 => BCons D54 xt | D53 => BCons D55 xt | D54 => BCons D56 xt | D55 => BCons D57 xt | D56 => BCons D58 xt | D57 => BCons D59 xt | D58 => BCons D60 xt | D59 => BCons D61 xt | D60 => BCons D62 xt | D61 => BCons D63 xt | D62 => BCons D0 (incB xt) | D63 => BCons D1 (incB xt) end | _ => B2 end.

Definition lo128 (r : R128) : D64 := match r with P0 => D0 | P1 => D1 | P2 => D2 | P3 => D3 | P4 => D4 | P5 => D5 | P6 => D6 | P7 => D7 | P8 => D8 | P9 => D9 | P10 => D10 | P11 => D11 | P12 => D12 | P13 => D13 | P14 => D14 | P15 => D15 | P16 => D16 | P17 => D17 | P18 => D18 | P19 => D19 | P20 => D20 | P21 => D21 | P22 => D22 | P23 => D23 | P24 => D24 | P25 => D25 | P26 => D26 | P27 => D27 | P28 => D28 | P29 => D29 | P30 => D30 | P31 => D31 | P32 => D32 | P33 => D33 | P34 => D34 | P35 => D35 | P36 => D36 | P37 => D37 | P38 => D38 | P39 => D39 | P40 => D40 | P41 => D41 | P42 => D42 | P43 => D43 | P44 => D44 | P45 => D45 | P46 => D46 | P47 => D47 | P48 => D48 | P49 => D49 | P50 => D50 | P51 => D51 | P52 => D52 | P53 => D53 | P54 => D54 | P55 => D55 | P56 => D56 | P57 => D57 | P58 => D58 | P59 => D59 | P60 => D60 | P61 => D61 | P62 => D62 | P63 => D63 | P64 => D0 | P65 => D1 | P66 => D2 | P67 => D3 | P68 => D4 | P69 => D5 | P70 => D6 | P71 => D7 | P72 => D8 | P73 => D9 | P74 => D10 | P75 => D11 | P76 => D12 | P77 => D13 | P78 => D14 | P79 => D15 | P80 => D16 | P81 => D17 | P82 => D18 | P83 => D19 | P84 => D20 | P85 => D21 | P86 => D22 | P87 => D23 | P88 => D24 | P89 => D25 | P90 => D26 | P91 => D27 | P92 => D28 | P93 => D29 | P94 => D30 | P95 => D31 | P96 => D32 | P97 => D33 | P98 => D34 | P99 => D35 | P100 => D36 | P101 => D37 | P102 => D38 | P103 => D39 | P104 => D40 | P105 => D41 | P106 => D42 | P107 => D43 | P108 => D44 | P109 => D45 | P110 => D46 | P111 => D47 | P112 => D48 | P113 => D49 | P114 => D50 | P115 => D51 | P116 => D52 | P117 => D53 | P118 => D54 | P119 => D55 | P120 => D56 | P121 => D57 | P122 => D58 | P123 => D59 | P124 => D60 | P125 => D61 | P126 => D62 | P127 => D63 end.
Definition hi128 (r : R128) : bool := match r with P0 => false | P1 => false | P2 => false | P3 => false | P4 => false | P5 => false | P6 => false | P7 => false | P8 => false | P9 => false | P10 => false | P11 => false | P12 => false | P13 => false | P14 => false | P15 => false | P16 => false | P17 => false | P18 => false | P19 => false | P20 => false | P21 => false | P22 => false | P23 => false | P24 => false | P25 => false | P26 => false | P27 => false | P28 => false | P29 => false | P30 => false | P31 => false | P32 => false | P33 => false | P34 => false | P35 => false | P36 => false | P37 => false | P38 => false | P39 => false | P40 => false | P41 => false | P42 => false | P43 => false | P44 => false | P45 => false | P46 => false | P47 => false | P48 => false | P49 => false | P50 => false | P51 => false | P52 => false | P53 => false | P54 => false | P55 => false | P56 => false | P57 => false | P58 => false | P59 => false | P60 => false | P61 => false | P62 => false | P63 => false | P64 => true | P65 => true | P66 => true | P67 => true | P68 => true | P69 => true | P70 => true | P71 => true | P72 => true | P73 => true | P74 => true | P75 => true | P76 => true | P77 => true | P78 => true | P79 => true | P80 => true | P81 => true | P82 => true | P83 => true | P84 => true | P85 => true | P86 => true | P87 => true | P88 => true | P89 => true | P90 => true | P91 => true | P92 => true | P93 => true | P94 => true | P95 => true | P96 => true | P97 => true | P98 => true | P99 => true | P100 => true | P101 => true | P102 => true | P103 => true | P104 => true | P105 => true | P106 => true | P107 => true | P108 => true | P109 => true | P110 => true | P111 => true | P112 => true | P113 => true | P114 => true | P115 => true | P116 => true | P117 => true | P118 => true | P119 => true | P120 => true | P121 => true | P122 => true | P123 => true | P124 => true | P125 => true | P126 => true | P127 => true end.
Definition lo256 (r : R256) : D64 := match r with W0 => D0 | W1 => D1 | W2 => D2 | W3 => D3 | W4 => D4 | W5 => D5 | W6 => D6 | W7 => D7 | W8 => D8 | W9 => D9 | W10 => D10 | W11 => D11 | W12 => D12 | W13 => D13 | W14 => D14 | W15 => D15 | W16 => D16 | W17 => D17 | W18 => D18 | W19 => D19 | W20 => D20 | W21 => D21 | W22 => D22 | W23 => D23 | W24 => D24 | W25 => D25 | W26 => D26 | W27 => D27 | W28 => D28 | W29 => D29 | W30 => D30 | W31 => D31 | W32 => D32 | W33 => D33 | W34 => D34 | W35 => D35 | W36 => D36 | W37 => D37 | W38 => D38 | W39 => D39 | W40 => D40 | W41 => D41 | W42 => D42 | W43 => D43 | W44 => D44 | W45 => D45 | W46 => D46 | W47 => D47 | W48 => D48 | W49 => D49 | W50 => D50 | W51 => D51 | W52 => D52 | W53 => D53 | W54 => D54 | W55 => D55 | W56 => D56 | W57 => D57 | W58 => D58 | W59 => D59 | W60 => D60 | W61 => D61 | W62 => D62 | W63 => D63 | W64 => D0 | W65 => D1 | W66 => D2 | W67 => D3 | W68 => D4 | W69 => D5 | W70 => D6 | W71 => D7 | W72 => D8 | W73 => D9 | W74 => D10 | W75 => D11 | W76 => D12 | W77 => D13 | W78 => D14 | W79 => D15 | W80 => D16 | W81 => D17 | W82 => D18 | W83 => D19 | W84 => D20 | W85 => D21 | W86 => D22 | W87 => D23 | W88 => D24 | W89 => D25 | W90 => D26 | W91 => D27 | W92 => D28 | W93 => D29 | W94 => D30 | W95 => D31 | W96 => D32 | W97 => D33 | W98 => D34 | W99 => D35 | W100 => D36 | W101 => D37 | W102 => D38 | W103 => D39 | W104 => D40 | W105 => D41 | W106 => D42 | W107 => D43 | W108 => D44 | W109 => D45 | W110 => D46 | W111 => D47 | W112 => D48 | W113 => D49 | W114 => D50 | W115 => D51 | W116 => D52 | W117 => D53 | W118 => D54 | W119 => D55 | W120 => D56 | W121 => D57 | W122 => D58 | W123 => D59 | W124 => D60 | W125 => D61 | W126 => D62 | W127 => D63 | W128 => D0 | W129 => D1 | W130 => D2 | W131 => D3 | W132 => D4 | W133 => D5 | W134 => D6 | W135 => D7 | W136 => D8 | W137 => D9 | W138 => D10 | W139 => D11 | W140 => D12 | W141 => D13 | W142 => D14 | W143 => D15 | W144 => D16 | W145 => D17 | W146 => D18 | W147 => D19 | W148 => D20 | W149 => D21 | W150 => D22 | W151 => D23 | W152 => D24 | W153 => D25 | W154 => D26 | W155 => D27 | W156 => D28 | W157 => D29 | W158 => D30 | W159 => D31 | W160 => D32 | W161 => D33 | W162 => D34 | W163 => D35 | W164 => D36 | W165 => D37 | W166 => D38 | W167 => D39 | W168 => D40 | W169 => D41 | W170 => D42 | W171 => D43 | W172 => D44 | W173 => D45 | W174 => D46 | W175 => D47 | W176 => D48 | W177 => D49 | W178 => D50 | W179 => D51 | W180 => D52 | W181 => D53 | W182 => D54 | W183 => D55 | W184 => D56 | W185 => D57 | W186 => D58 | W187 => D59 | W188 => D60 | W189 => D61 | W190 => D62 | W191 => D63 | W192 => D0 | W193 => D1 | W194 => D2 | W195 => D3 | W196 => D4 | W197 => D5 | W198 => D6 | W199 => D7 | W200 => D8 | W201 => D9 | W202 => D10 | W203 => D11 | W204 => D12 | W205 => D13 | W206 => D14 | W207 => D15 | W208 => D16 | W209 => D17 | W210 => D18 | W211 => D19 | W212 => D20 | W213 => D21 | W214 => D22 | W215 => D23 | W216 => D24 | W217 => D25 | W218 => D26 | W219 => D27 | W220 => D28 | W221 => D29 | W222 => D30 | W223 => D31 | W224 => D32 | W225 => D33 | W226 => D34 | W227 => D35 | W228 => D36 | W229 => D37 | W230 => D38 | W231 => D39 | W232 => D40 | W233 => D41 | W234 => D42 | W235 => D43 | W236 => D44 | W237 => D45 | W238 => D46 | W239 => D47 | W240 => D48 | W241 => D49 | W242 => D50 | W243 => D51 | W244 => D52 | W245 => D53 | W246 => D54 | W247 => D55 | W248 => D56 | W249 => D57 | W250 => D58 | W251 => D59 | W252 => D60 | W253 => D61 | W254 => D62 | W255 => D63 end.
Definition hi256 (r : R256) : C6 := match r with W0 => C0 | W1 => C0 | W2 => C0 | W3 => C0 | W4 => C0 | W5 => C0 | W6 => C0 | W7 => C0 | W8 => C0 | W9 => C0 | W10 => C0 | W11 => C0 | W12 => C0 | W13 => C0 | W14 => C0 | W15 => C0 | W16 => C0 | W17 => C0 | W18 => C0 | W19 => C0 | W20 => C0 | W21 => C0 | W22 => C0 | W23 => C0 | W24 => C0 | W25 => C0 | W26 => C0 | W27 => C0 | W28 => C0 | W29 => C0 | W30 => C0 | W31 => C0 | W32 => C0 | W33 => C0 | W34 => C0 | W35 => C0 | W36 => C0 | W37 => C0 | W38 => C0 | W39 => C0 | W40 => C0 | W41 => C0 | W42 => C0 | W43 => C0 | W44 => C0 | W45 => C0 | W46 => C0 | W47 => C0 | W48 => C0 | W49 => C0 | W50 => C0 | W51 => C0 | W52 => C0 | W53 => C0 | W54 => C0 | W55 => C0 | W56 => C0 | W57 => C0 | W58 => C0 | W59 => C0 | W60 => C0 | W61 => C0 | W62 => C0 | W63 => C0 | W64 => C1 | W65 => C1 | W66 => C1 | W67 => C1 | W68 => C1 | W69 => C1 | W70 => C1 | W71 => C1 | W72 => C1 | W73 => C1 | W74 => C1 | W75 => C1 | W76 => C1 | W77 => C1 | W78 => C1 | W79 => C1 | W80 => C1 | W81 => C1 | W82 => C1 | W83 => C1 | W84 => C1 | W85 => C1 | W86 => C1 | W87 => C1 | W88 => C1 | W89 => C1 | W90 => C1 | W91 => C1 | W92 => C1 | W93 => C1 | W94 => C1 | W95 => C1 | W96 => C1 | W97 => C1 | W98 => C1 | W99 => C1 | W100 => C1 | W101 => C1 | W102 => C1 | W103 => C1 | W104 => C1 | W105 => C1 | W106 => C1 | W107 => C1 | W108 => C1 | W109 => C1 | W110 => C1 | W111 => C1 | W112 => C1 | W113 => C1 | W114 => C1 | W115 => C1 | W116 => C1 | W117 => C1 | W118 => C1 | W119 => C1 | W120 => C1 | W121 => C1 | W122 => C1 | W123 => C1 | W124 => C1 | W125 => C1 | W126 => C1 | W127 => C1 | W128 => C2 | W129 => C2 | W130 => C2 | W131 => C2 | W132 => C2 | W133 => C2 | W134 => C2 | W135 => C2 | W136 => C2 | W137 => C2 | W138 => C2 | W139 => C2 | W140 => C2 | W141 => C2 | W142 => C2 | W143 => C2 | W144 => C2 | W145 => C2 | W146 => C2 | W147 => C2 | W148 => C2 | W149 => C2 | W150 => C2 | W151 => C2 | W152 => C2 | W153 => C2 | W154 => C2 | W155 => C2 | W156 => C2 | W157 => C2 | W158 => C2 | W159 => C2 | W160 => C2 | W161 => C2 | W162 => C2 | W163 => C2 | W164 => C2 | W165 => C2 | W166 => C2 | W167 => C2 | W168 => C2 | W169 => C2 | W170 => C2 | W171 => C2 | W172 => C2 | W173 => C2 | W174 => C2 | W175 => C2 | W176 => C2 | W177 => C2 | W178 => C2 | W179 => C2 | W180 => C2 | W181 => C2 | W182 => C2 | W183 => C2 | W184 => C2 | W185 => C2 | W186 => C2 | W187 => C2 | W188 => C2 | W189 => C2 | W190 => C2 | W191 => C2 | W192 => C3 | W193 => C3 | W194 => C3 | W195 => C3 | W196 => C3 | W197 => C3 | W198 => C3 | W199 => C3 | W200 => C3 | W201 => C3 | W202 => C3 | W203 => C3 | W204 => C3 | W205 => C3 | W206 => C3 | W207 => C3 | W208 => C3 | W209 => C3 | W210 => C3 | W211 => C3 | W212 => C3 | W213 => C3 | W214 => C3 | W215 => C3 | W216 => C3 | W217 => C3 | W218 => C3 | W219 => C3 | W220 => C3 | W221 => C3 | W222 => C3 | W223 => C3 | W224 => C3 | W225 => C3 | W226 => C3 | W227 => C3 | W228 => C3 | W229 => C3 | W230 => C3 | W231 => C3 | W232 => C3 | W233 => C3 | W234 => C3 | W235 => C3 | W236 => C3 | W237 => C3 | W238 => C3 | W239 => C3 | W240 => C3 | W241 => C3 | W242 => C3 | W243 => C3 | W244 => C3 | W245 => C3 | W246 => C3 | W247 => C3 | W248 => C3 | W249 => C3 | W250 => C3 | W251 => C3 | W252 => C3 | W253 => C3 | W254 => C3 | W255 => C3 end.

Definition add64c (c : bool) (a b : D64) : R128 :=
  if c then match a with
  | D0 => match b with D0 => P1 | D1 => P2 | D2 => P3 | D3 => P4 | D4 => P5 | D5 => P6 | D6 => P7 | D7 => P8 | D8 => P9 | D9 => P10 | D10 => P11 | D11 => P12 | D12 => P13 | D13 => P14 | D14 => P15 | D15 => P16 | D16 => P17 | D17 => P18 | D18 => P19 | D19 => P20 | D20 => P21 | D21 => P22 | D22 => P23 | D23 => P24 | D24 => P25 | D25 => P26 | D26 => P27 | D27 => P28 | D28 => P29 | D29 => P30 | D30 => P31 | D31 => P32 | D32 => P33 | D33 => P34 | D34 => P35 | D35 => P36 | D36 => P37 | D37 => P38 | D38 => P39 | D39 => P40 | D40 => P41 | D41 => P42 | D42 => P43 | D43 => P44 | D44 => P45 | D45 => P46 | D46 => P47 | D47 => P48 | D48 => P49 | D49 => P50 | D50 => P51 | D51 => P52 | D52 => P53 | D53 => P54 | D54 => P55 | D55 => P56 | D56 => P57 | D57 => P58 | D58 => P59 | D59 => P60 | D60 => P61 | D61 => P62 | D62 => P63 | D63 => P64 end
  | D1 => match b with D0 => P2 | D1 => P3 | D2 => P4 | D3 => P5 | D4 => P6 | D5 => P7 | D6 => P8 | D7 => P9 | D8 => P10 | D9 => P11 | D10 => P12 | D11 => P13 | D12 => P14 | D13 => P15 | D14 => P16 | D15 => P17 | D16 => P18 | D17 => P19 | D18 => P20 | D19 => P21 | D20 => P22 | D21 => P23 | D22 => P24 | D23 => P25 | D24 => P26 | D25 => P27 | D26 => P28 | D27 => P29 | D28 => P30 | D29 => P31 | D30 => P32 | D31 => P33 | D32 => P34 | D33 => P35 | D34 => P36 | D35 => P37 | D36 => P38 | D37 => P39 | D38 => P40 | D39 => P41 | D40 => P42 | D41 => P43 | D42 => P44 | D43 => P45 | D44 => P46 | D45 => P47 | D46 => P48 | D47 => P49 | D48 => P50 | D49 => P51 | D50 => P52 | D51 => P53 | D52 => P54 | D53 => P55 | D54 => P56 | D55 => P57 | D56 => P58 | D57 => P59 | D58 => P60 | D59 => P61 | D60 => P62 | D61 => P63 | D62 => P64 | D63 => P65 end
  | D2 => match b with D0 => P3 | D1 => P4 | D2 => P5 | D3 => P6 | D4 => P7 | D5 => P8 | D6 => P9 | D7 => P10 | D8 => P11 | D9 => P12 | D10 => P13 | D11 => P14 | D12 => P15 | D13 => P16 | D14 => P17 | D15 => P18 | D16 => P19 | D17 => P20 | D18 => P21 | D19 => P22 | D20 => P23 | D21 => P24 | D22 => P25 | D23 => P26 | D24 => P27 | D25 => P28 | D26 => P29 | D27 => P30 | D28 => P31 | D29 => P32 | D30 => P33 | D31 => P34 | D32 => P35 | D33 => P36 | D34 => P37 | D35 => P38 | D36 => P39 | D37 => P40 | D38 => P41 | D39 => P42 | D40 => P43 | D41 => P44 | D42 => P45 | D43 => P46 | D44 => P47 | D45 => P48 | D46 => P49 | D47 => P50 | D48 => P51 | D49 => P52 | D50 => P53 | D51 => P54 | D52 => P55 | D53 => P56 | D54 => P57 | D55 => P58 | D56 => P59 | D57 => P60 | D58 => P61 | D59 => P62 | D60 => P63 | D61 => P64 | D62 => P65 | D63 => P66 end
  | D3 => match b with D0 => P4 | D1 => P5 | D2 => P6 | D3 => P7 | D4 => P8 | D5 => P9 | D6 => P10 | D7 => P11 | D8 => P12 | D9 => P13 | D10 => P14 | D11 => P15 | D12 => P16 | D13 => P17 | D14 => P18 | D15 => P19 | D16 => P20 | D17 => P21 | D18 => P22 | D19 => P23 | D20 => P24 | D21 => P25 | D22 => P26 | D23 => P27 | D24 => P28 | D25 => P29 | D26 => P30 | D27 => P31 | D28 => P32 | D29 => P33 | D30 => P34 | D31 => P35 | D32 => P36 | D33 => P37 | D34 => P38 | D35 => P39 | D36 => P40 | D37 => P41 | D38 => P42 | D39 => P43 | D40 => P44 | D41 => P45 | D42 => P46 | D43 => P47 | D44 => P48 | D45 => P49 | D46 => P50 | D47 => P51 | D48 => P52 | D49 => P53 | D50 => P54 | D51 => P55 | D52 => P56 | D53 => P57 | D54 => P58 | D55 => P59 | D56 => P60 | D57 => P61 | D58 => P62 | D59 => P63 | D60 => P64 | D61 => P65 | D62 => P66 | D63 => P67 end
  | D4 => match b with D0 => P5 | D1 => P6 | D2 => P7 | D3 => P8 | D4 => P9 | D5 => P10 | D6 => P11 | D7 => P12 | D8 => P13 | D9 => P14 | D10 => P15 | D11 => P16 | D12 => P17 | D13 => P18 | D14 => P19 | D15 => P20 | D16 => P21 | D17 => P22 | D18 => P23 | D19 => P24 | D20 => P25 | D21 => P26 | D22 => P27 | D23 => P28 | D24 => P29 | D25 => P30 | D26 => P31 | D27 => P32 | D28 => P33 | D29 => P34 | D30 => P35 | D31 => P36 | D32 => P37 | D33 => P38 | D34 => P39 | D35 => P40 | D36 => P41 | D37 => P42 | D38 => P43 | D39 => P44 | D40 => P45 | D41 => P46 | D42 => P47 | D43 => P48 | D44 => P49 | D45 => P50 | D46 => P51 | D47 => P52 | D48 => P53 | D49 => P54 | D50 => P55 | D51 => P56 | D52 => P57 | D53 => P58 | D54 => P59 | D55 => P60 | D56 => P61 | D57 => P62 | D58 => P63 | D59 => P64 | D60 => P65 | D61 => P66 | D62 => P67 | D63 => P68 end
  | D5 => match b with D0 => P6 | D1 => P7 | D2 => P8 | D3 => P9 | D4 => P10 | D5 => P11 | D6 => P12 | D7 => P13 | D8 => P14 | D9 => P15 | D10 => P16 | D11 => P17 | D12 => P18 | D13 => P19 | D14 => P20 | D15 => P21 | D16 => P22 | D17 => P23 | D18 => P24 | D19 => P25 | D20 => P26 | D21 => P27 | D22 => P28 | D23 => P29 | D24 => P30 | D25 => P31 | D26 => P32 | D27 => P33 | D28 => P34 | D29 => P35 | D30 => P36 | D31 => P37 | D32 => P38 | D33 => P39 | D34 => P40 | D35 => P41 | D36 => P42 | D37 => P43 | D38 => P44 | D39 => P45 | D40 => P46 | D41 => P47 | D42 => P48 | D43 => P49 | D44 => P50 | D45 => P51 | D46 => P52 | D47 => P53 | D48 => P54 | D49 => P55 | D50 => P56 | D51 => P57 | D52 => P58 | D53 => P59 | D54 => P60 | D55 => P61 | D56 => P62 | D57 => P63 | D58 => P64 | D59 => P65 | D60 => P66 | D61 => P67 | D62 => P68 | D63 => P69 end
  | D6 => match b with D0 => P7 | D1 => P8 | D2 => P9 | D3 => P10 | D4 => P11 | D5 => P12 | D6 => P13 | D7 => P14 | D8 => P15 | D9 => P16 | D10 => P17 | D11 => P18 | D12 => P19 | D13 => P20 | D14 => P21 | D15 => P22 | D16 => P23 | D17 => P24 | D18 => P25 | D19 => P26 | D20 => P27 | D21 => P28 | D22 => P29 | D23 => P30 | D24 => P31 | D25 => P32 | D26 => P33 | D27 => P34 | D28 => P35 | D29 => P36 | D30 => P37 | D31 => P38 | D32 => P39 | D33 => P40 | D34 => P41 | D35 => P42 | D36 => P43 | D37 => P44 | D38 => P45 | D39 => P46 | D40 => P47 | D41 => P48 | D42 => P49 | D43 => P50 | D44 => P51 | D45 => P52 | D46 => P53 | D47 => P54 | D48 => P55 | D49 => P56 | D50 => P57 | D51 => P58 | D52 => P59 | D53 => P60 | D54 => P61 | D55 => P62 | D56 => P63 | D57 => P64 | D58 => P65 | D59 => P66 | D60 => P67 | D61 => P68 | D62 => P69 | D63 => P70 end
  | D7 => match b with D0 => P8 | D1 => P9 | D2 => P10 | D3 => P11 | D4 => P12 | D5 => P13 | D6 => P14 | D7 => P15 | D8 => P16 | D9 => P17 | D10 => P18 | D11 => P19 | D12 => P20 | D13 => P21 | D14 => P22 | D15 => P23 | D16 => P24 | D17 => P25 | D18 => P26 | D19 => P27 | D20 => P28 | D21 => P29 | D22 => P30 | D23 => P31 | D24 => P32 | D25 => P33 | D26 => P34 | D27 => P35 | D28 => P36 | D29 => P37 | D30 => P38 | D31 => P39 | D32 => P40 | D33 => P41 | D34 => P42 | D35 => P43 | D36 => P44 | D37 => P45 | D38 => P46 | D39 => P47 | D40 => P48 | D41 => P49 | D42 => P50 | D43 => P51 | D44 => P52 | D45 => P53 | D46 => P54 | D47 => P55 | D48 => P56 | D49 => P57 | D50 => P58 | D51 => P59 | D52 => P60 | D53 => P61 | D54 => P62 | D55 => P63 | D56 => P64 | D57 => P65 | D58 => P66 | D59 => P67 | D60 => P68 | D61 => P69 | D62 => P70 | D63 => P71 end
  | D8 => match b with D0 => P9 | D1 => P10 | D2 => P11 | D3 => P12 | D4 => P13 | D5 => P14 | D6 => P15 | D7 => P16 | D8 => P17 | D9 => P18 | D10 => P19 | D11 => P20 | D12 => P21 | D13 => P22 | D14 => P23 | D15 => P24 | D16 => P25 | D17 => P26 | D18 => P27 | D19 => P28 | D20 => P29 | D21 => P30 | D22 => P31 | D23 => P32 | D24 => P33 | D25 => P34 | D26 => P35 | D27 => P36 | D28 => P37 | D29 => P38 | D30 => P39 | D31 => P40 | D32 => P41 | D33 => P42 | D34 => P43 | D35 => P44 | D36 => P45 | D37 => P46 | D38 => P47 | D39 => P48 | D40 => P49 | D41 => P50 | D42 => P51 | D43 => P52 | D44 => P53 | D45 => P54 | D46 => P55 | D47 => P56 | D48 => P57 | D49 => P58 | D50 => P59 | D51 => P60 | D52 => P61 | D53 => P62 | D54 => P63 | D55 => P64 | D56 => P65 | D57 => P66 | D58 => P67 | D59 => P68 | D60 => P69 | D61 => P70 | D62 => P71 | D63 => P72 end
  | D9 => match b with D0 => P10 | D1 => P11 | D2 => P12 | D3 => P13 | D4 => P14 | D5 => P15 | D6 => P16 | D7 => P17 | D8 => P18 | D9 => P19 | D10 => P20 | D11 => P21 | D12 => P22 | D13 => P23 | D14 => P24 | D15 => P25 | D16 => P26 | D17 => P27 | D18 => P28 | D19 => P29 | D20 => P30 | D21 => P31 | D22 => P32 | D23 => P33 | D24 => P34 | D25 => P35 | D26 => P36 | D27 => P37 | D28 => P38 | D29 => P39 | D30 => P40 | D31 => P41 | D32 => P42 | D33 => P43 | D34 => P44 | D35 => P45 | D36 => P46 | D37 => P47 | D38 => P48 | D39 => P49 | D40 => P50 | D41 => P51 | D42 => P52 | D43 => P53 | D44 => P54 | D45 => P55 | D46 => P56 | D47 => P57 | D48 => P58 | D49 => P59 | D50 => P60 | D51 => P61 | D52 => P62 | D53 => P63 | D54 => P64 | D55 => P65 | D56 => P66 | D57 => P67 | D58 => P68 | D59 => P69 | D60 => P70 | D61 => P71 | D62 => P72 | D63 => P73 end
  | D10 => match b with D0 => P11 | D1 => P12 | D2 => P13 | D3 => P14 | D4 => P15 | D5 => P16 | D6 => P17 | D7 => P18 | D8 => P19 | D9 => P20 | D10 => P21 | D11 => P22 | D12 => P23 | D13 => P24 | D14 => P25 | D15 => P26 | D16 => P27 | D17 => P28 | D18 => P29 | D19 => P30 | D20 => P31 | D21 => P32 | D22 => P33 | D23 => P34 | D24 => P35 | D25 => P36 | D26 => P37 | D27 => P38 | D28 => P39 | D29 => P40 | D30 => P41 | D31 => P42 | D32 => P43 | D33 => P44 | D34 => P45 | D35 => P46 | D36 => P47 | D37 => P48 | D38 => P49 | D39 => P50 | D40 => P51 | D41 => P52 | D42 => P53 | D43 => P54 | D44 => P55 | D45 => P56 | D46 => P57 | D47 => P58 | D48 => P59 | D49 => P60 | D50 => P61 | D51 => P62 | D52 => P63 | D53 => P64 | D54 => P65 | D55 => P66 | D56 => P67 | D57 => P68 | D58 => P69 | D59 => P70 | D60 => P71 | D61 => P72 | D62 => P73 | D63 => P74 end
  | D11 => match b with D0 => P12 | D1 => P13 | D2 => P14 | D3 => P15 | D4 => P16 | D5 => P17 | D6 => P18 | D7 => P19 | D8 => P20 | D9 => P21 | D10 => P22 | D11 => P23 | D12 => P24 | D13 => P25 | D14 => P26 | D15 => P27 | D16 => P28 | D17 => P29 | D18 => P30 | D19 => P31 | D20 => P32 | D21 => P33 | D22 => P34 | D23 => P35 | D24 => P36 | D25 => P37 | D26 => P38 | D27 => P39 | D28 => P40 | D29 => P41 | D30 => P42 | D31 => P43 | D32 => P44 | D33 => P45 | D34 => P46 | D35 => P47 | D36 => P48 | D37 => P49 | D38 => P50 | D39 => P51 | D40 => P52 | D41 => P53 | D42 => P54 | D43 => P55 | D44 => P56 | D45 => P57 | D46 => P58 | D47 => P59 | D48 => P60 | D49 => P61 | D50 => P62 | D51 => P63 | D52 => P64 | D53 => P65 | D54 => P66 | D55 => P67 | D56 => P68 | D57 => P69 | D58 => P70 | D59 => P71 | D60 => P72 | D61 => P73 | D62 => P74 | D63 => P75 end
  | D12 => match b with D0 => P13 | D1 => P14 | D2 => P15 | D3 => P16 | D4 => P17 | D5 => P18 | D6 => P19 | D7 => P20 | D8 => P21 | D9 => P22 | D10 => P23 | D11 => P24 | D12 => P25 | D13 => P26 | D14 => P27 | D15 => P28 | D16 => P29 | D17 => P30 | D18 => P31 | D19 => P32 | D20 => P33 | D21 => P34 | D22 => P35 | D23 => P36 | D24 => P37 | D25 => P38 | D26 => P39 | D27 => P40 | D28 => P41 | D29 => P42 | D30 => P43 | D31 => P44 | D32 => P45 | D33 => P46 | D34 => P47 | D35 => P48 | D36 => P49 | D37 => P50 | D38 => P51 | D39 => P52 | D40 => P53 | D41 => P54 | D42 => P55 | D43 => P56 | D44 => P57 | D45 => P58 | D46 => P59 | D47 => P60 | D48 => P61 | D49 => P62 | D50 => P63 | D51 => P64 | D52 => P65 | D53 => P66 | D54 => P67 | D55 => P68 | D56 => P69 | D57 => P70 | D58 => P71 | D59 => P72 | D60 => P73 | D61 => P74 | D62 => P75 | D63 => P76 end
  | D13 => match b with D0 => P14 | D1 => P15 | D2 => P16 | D3 => P17 | D4 => P18 | D5 => P19 | D6 => P20 | D7 => P21 | D8 => P22 | D9 => P23 | D10 => P24 | D11 => P25 | D12 => P26 | D13 => P27 | D14 => P28 | D15 => P29 | D16 => P30 | D17 => P31 | D18 => P32 | D19 => P33 | D20 => P34 | D21 => P35 | D22 => P36 | D23 => P37 | D24 => P38 | D25 => P39 | D26 => P40 | D27 => P41 | D28 => P42 | D29 => P43 | D30 => P44 | D31 => P45 | D32 => P46 | D33 => P47 | D34 => P48 | D35 => P49 | D36 => P50 | D37 => P51 | D38 => P52 | D39 => P53 | D40 => P54 | D41 => P55 | D42 => P56 | D43 => P57 | D44 => P58 | D45 => P59 | D46 => P60 | D47 => P61 | D48 => P62 | D49 => P63 | D50 => P64 | D51 => P65 | D52 => P66 | D53 => P67 | D54 => P68 | D55 => P69 | D56 => P70 | D57 => P71 | D58 => P72 | D59 => P73 | D60 => P74 | D61 => P75 | D62 => P76 | D63 => P77 end
  | D14 => match b with D0 => P15 | D1 => P16 | D2 => P17 | D3 => P18 | D4 => P19 | D5 => P20 | D6 => P21 | D7 => P22 | D8 => P23 | D9 => P24 | D10 => P25 | D11 => P26 | D12 => P27 | D13 => P28 | D14 => P29 | D15 => P30 | D16 => P31 | D17 => P32 | D18 => P33 | D19 => P34 | D20 => P35 | D21 => P36 | D22 => P37 | D23 => P38 | D24 => P39 | D25 => P40 | D26 => P41 | D27 => P42 | D28 => P43 | D29 => P44 | D30 => P45 | D31 => P46 | D32 => P47 | D33 => P48 | D34 => P49 | D35 => P50 | D36 => P51 | D37 => P52 | D38 => P53 | D39 => P54 | D40 => P55 | D41 => P56 | D42 => P57 | D43 => P58 | D44 => P59 | D45 => P60 | D46 => P61 | D47 => P62 | D48 => P63 | D49 => P64 | D50 => P65 | D51 => P66 | D52 => P67 | D53 => P68 | D54 => P69 | D55 => P70 | D56 => P71 | D57 => P72 | D58 => P73 | D59 => P74 | D60 => P75 | D61 => P76 | D62 => P77 | D63 => P78 end
  | D15 => match b with D0 => P16 | D1 => P17 | D2 => P18 | D3 => P19 | D4 => P20 | D5 => P21 | D6 => P22 | D7 => P23 | D8 => P24 | D9 => P25 | D10 => P26 | D11 => P27 | D12 => P28 | D13 => P29 | D14 => P30 | D15 => P31 | D16 => P32 | D17 => P33 | D18 => P34 | D19 => P35 | D20 => P36 | D21 => P37 | D22 => P38 | D23 => P39 | D24 => P40 | D25 => P41 | D26 => P42 | D27 => P43 | D28 => P44 | D29 => P45 | D30 => P46 | D31 => P47 | D32 => P48 | D33 => P49 | D34 => P50 | D35 => P51 | D36 => P52 | D37 => P53 | D38 => P54 | D39 => P55 | D40 => P56 | D41 => P57 | D42 => P58 | D43 => P59 | D44 => P60 | D45 => P61 | D46 => P62 | D47 => P63 | D48 => P64 | D49 => P65 | D50 => P66 | D51 => P67 | D52 => P68 | D53 => P69 | D54 => P70 | D55 => P71 | D56 => P72 | D57 => P73 | D58 => P74 | D59 => P75 | D60 => P76 | D61 => P77 | D62 => P78 | D63 => P79 end
  | D16 => match b with D0 => P17 | D1 => P18 | D2 => P19 | D3 => P20 | D4 => P21 | D5 => P22 | D6 => P23 | D7 => P24 | D8 => P25 | D9 => P26 | D10 => P27 | D11 => P28 | D12 => P29 | D13 => P30 | D14 => P31 | D15 => P32 | D16 => P33 | D17 => P34 | D18 => P35 | D19 => P36 | D20 => P37 | D21 => P38 | D22 => P39 | D23 => P40 | D24 => P41 | D25 => P42 | D26 => P43 | D27 => P44 | D28 => P45 | D29 => P46 | D30 => P47 | D31 => P48 | D32 => P49 | D33 => P50 | D34 => P51 | D35 => P52 | D36 => P53 | D37 => P54 | D38 => P55 | D39 => P56 | D40 => P57 | D41 => P58 | D42 => P59 | D43 => P60 | D44 => P61 | D45 => P62 | D46 => P63 | D47 => P64 | D48 => P65 | D49 => P66 | D50 => P67 | D51 => P68 | D52 => P69 | D53 => P70 | D54 => P71 | D55 => P72 | D56 => P73 | D57 => P74 | D58 => P75 | D59 => P76 | D60 => P77 | D61 => P78 | D62 => P79 | D63 => P80 end
  | D17 => match b with D0 => P18 | D1 => P19 | D2 => P20 | D3 => P21 | D4 => P22 | D5 => P23 | D6 => P24 | D7 => P25 | D8 => P26 | D9 => P27 | D10 => P28 | D11 => P29 | D12 => P30 | D13 => P31 | D14 => P32 | D15 => P33 | D16 => P34 | D17 => P35 | D18 => P36 | D19 => P37 | D20 => P38 | D21 => P39 | D22 => P40 | D23 => P41 | D24 => P42 | D25 => P43 | D26 => P44 | D27 => P45 | D28 => P46 | D29 => P47 | D30 => P48 | D31 => P49 | D32 => P50 | D33 => P51 | D34 => P52 | D35 => P53 | D36 => P54 | D37 => P55 | D38 => P56 | D39 => P57 | D40 => P58 | D41 => P59 | D42 => P60 | D43 => P61 | D44 => P62 | D45 => P63 | D46 => P64 | D47 => P65 | D48 => P66 | D49 => P67 | D50 => P68 | D51 => P69 | D52 => P70 | D53 => P71 | D54 => P72 | D55 => P73 | D56 => P74 | D57 => P75 | D58 => P76 | D59 => P77 | D60 => P78 | D61 => P79 | D62 => P80 | D63 => P81 end
  | D18 => match b with D0 => P19 | D1 => P20 | D2 => P21 | D3 => P22 | D4 => P23 | D5 => P24 | D6 => P25 | D7 => P26 | D8 => P27 | D9 => P28 | D10 => P29 | D11 => P30 | D12 => P31 | D13 => P32 | D14 => P33 | D15 => P34 | D16 => P35 | D17 => P36 | D18 => P37 | D19 => P38 | D20 => P39 | D21 => P40 | D22 => P41 | D23 => P42 | D24 => P43 | D25 => P44 | D26 => P45 | D27 => P46 | D28 => P47 | D29 => P48 | D30 => P49 | D31 => P50 | D32 => P51 | D33 => P52 | D34 => P53 | D35 => P54 | D36 => P55 | D37 => P56 | D38 => P57 | D39 => P58 | D40 => P59 | D41 => P60 | D42 => P61 | D43 => P62 | D44 => P63 | D45 => P64 | D46 => P65 | D47 => P66 | D48 => P67 | D49 => P68 | D50 => P69 | D51 => P70 | D52 => P71 | D53 => P72 | D54 => P73 | D55 => P74 | D56 => P75 | D57 => P76 | D58 => P77 | D59 => P78 | D60 => P79 | D61 => P80 | D62 => P81 | D63 => P82 end
  | D19 => match b with D0 => P20 | D1 => P21 | D2 => P22 | D3 => P23 | D4 => P24 | D5 => P25 | D6 => P26 | D7 => P27 | D8 => P28 | D9 => P29 | D10 => P30 | D11 => P31 | D12 => P32 | D13 => P33 | D14 => P34 | D15 => P35 | D16 => P36 | D17 => P37 | D18 => P38 | D19 => P39 | D20 => P40 | D21 => P41 | D22 => P42 | D23 => P43 | D24 => P44 | D25 => P45 | D26 => P46 | D27 => P47 | D28 => P48 | D29 => P49 | D30 => P50 | D31 => P51 | D32 => P52 | D33 => P53 | D34 => P54 | D35 => P55 | D36 => P56 | D37 => P57 | D38 => P58 | D39 => P59 | D40 => P60 | D41 => P61 | D42 => P62 | D43 => P63 | D44 => P64 | D45 => P65 | D46 => P66 | D47 => P67 | D48 => P68 | D49 => P69 | D50 => P70 | D51 => P71 | D52 => P72 | D53 => P73 | D54 => P74 | D55 => P75 | D56 => P76 | D57 => P77 | D58 => P78 | D59 => P79 | D60 => P80 | D61 => P81 | D62 => P82 | D63 => P83 end
  | D20 => match b with D0 => P21 | D1 => P22 | D2 => P23 | D3 => P24 | D4 => P25 | D5 => P26 | D6 => P27 | D7 => P28 | D8 => P29 | D9 => P30 | D10 => P31 | D11 => P32 | D12 => P33 | D13 => P34 | D14 => P35 | D15 => P36 | D16 => P37 | D17 => P38 | D18 => P39 | D19 => P40 | D20 => P41 | D21 => P42 | D22 => P43 | D23 => P44 | D24 => P45 | D25 => P46 | D26 => P47 | D27 => P48 | D28 => P49 | D29 => P50 | D30 => P51 | D31 => P52 | D32 => P53 | D33 => P54 | D34 => P55 | D35 => P56 | D36 => P57 | D37 => P58 | D38 => P59 | D39 => P60 | D40 => P61 | D41 => P62 | D42 => P63 | D43 => P64 | D44 => P65 | D45 => P66 | D46 => P67 | D47 => P68 | D48 => P69 | D49 => P70 | D50 => P71 | D51 => P72 | D52 => P73 | D53 => P74 | D54 => P75 | D55 => P76 | D56 => P77 | D57 => P78 | D58 => P79 | D59 => P80 | D60 => P81 | D61 => P82 | D62 => P83 | D63 => P84 end
  | D21 => match b with D0 => P22 | D1 => P23 | D2 => P24 | D3 => P25 | D4 => P26 | D5 => P27 | D6 => P28 | D7 => P29 | D8 => P30 | D9 => P31 | D10 => P32 | D11 => P33 | D12 => P34 | D13 => P35 | D14 => P36 | D15 => P37 | D16 => P38 | D17 => P39 | D18 => P40 | D19 => P41 | D20 => P42 | D21 => P43 | D22 => P44 | D23 => P45 | D24 => P46 | D25 => P47 | D26 => P48 | D27 => P49 | D28 => P50 | D29 => P51 | D30 => P52 | D31 => P53 | D32 => P54 | D33 => P55 | D34 => P56 | D35 => P57 | D36 => P58 | D37 => P59 | D38 => P60 | D39 => P61 | D40 => P62 | D41 => P63 | D42 => P64 | D43 => P65 | D44 => P66 | D45 => P67 | D46 => P68 | D47 => P69 | D48 => P70 | D49 => P71 | D50 => P72 | D51 => P73 | D52 => P74 | D53 => P75 | D54 => P76 | D55 => P77 | D56 => P78 | D57 => P79 | D58 => P80 | D59 => P81 | D60 => P82 | D61 => P83 | D62 => P84 | D63 => P85 end
  | D22 => match b with D0 => P23 | D1 => P24 | D2 => P25 | D3 => P26 | D4 => P27 | D5 => P28 | D6 => P29 | D7 => P30 | D8 => P31 | D9 => P32 | D10 => P33 | D11 => P34 | D12 => P35 | D13 => P36 | D14 => P37 | D15 => P38 | D16 => P39 | D17 => P40 | D18 => P41 | D19 => P42 | D20 => P43 | D21 => P44 | D22 => P45 | D23 => P46 | D24 => P47 | D25 => P48 | D26 => P49 | D27 => P50 | D28 => P51 | D29 => P52 | D30 => P53 | D31 => P54 | D32 => P55 | D33 => P56 | D34 => P57 | D35 => P58 | D36 => P59 | D37 => P60 | D38 => P61 | D39 => P62 | D40 => P63 | D41 => P64 | D42 => P65 | D43 => P66 | D44 => P67 | D45 => P68 | D46 => P69 | D47 => P70 | D48 => P71 | D49 => P72 | D50 => P73 | D51 => P74 | D52 => P75 | D53 => P76 | D54 => P77 | D55 => P78 | D56 => P79 | D57 => P80 | D58 => P81 | D59 => P82 | D60 => P83 | D61 => P84 | D62 => P85 | D63 => P86 end
  | D23 => match b with D0 => P24 | D1 => P25 | D2 => P26 | D3 => P27 | D4 => P28 | D5 => P29 | D6 => P30 | D7 => P31 | D8 => P32 | D9 => P33 | D10 => P34 | D11 => P35 | D12 => P36 | D13 => P37 | D14 => P38 | D15 => P39 | D16 => P40 | D17 => P41 | D18 => P42 | D19 => P43 | D20 => P44 | D21 => P45 | D22 => P46 | D23 => P47 | D24 => P48 | D25 => P49 | D26 => P50 | D27 => P51 | D28 => P52 | D29 => P53 | D30 => P54 | D31 => P55 | D32 => P56 | D33 => P57 | D34 => P58 | D35 => P59 | D36 => P60 | D37 => P61 | D38 => P62 | D39 => P63 | D40 => P64 | D41 => P65 | D42 => P66 | D43 => P67 | D44 => P68 | D45 => P69 | D46 => P70 | D47 => P71 | D48 => P72 | D49 => P73 | D50 => P74 | D51 => P75 | D52 => P76 | D53 => P77 | D54 => P78 | D55 => P79 | D56 => P80 | D57 => P81 | D58 => P82 | D59 => P83 | D60 => P84 | D61 => P85 | D62 => P86 | D63 => P87 end
  | D24 => match b with D0 => P25 | D1 => P26 | D2 => P27 | D3 => P28 | D4 => P29 | D5 => P30 | D6 => P31 | D7 => P32 | D8 => P33 | D9 => P34 | D10 => P35 | D11 => P36 | D12 => P37 | D13 => P38 | D14 => P39 | D15 => P40 | D16 => P41 | D17 => P42 | D18 => P43 | D19 => P44 | D20 => P45 | D21 => P46 | D22 => P47 | D23 => P48 | D24 => P49 | D25 => P50 | D26 => P51 | D27 => P52 | D28 => P53 | D29 => P54 | D30 => P55 | D31 => P56 | D32 => P57 | D33 => P58 | D34 => P59 | D35 => P60 | D36 => P61 | D37 => P62 | D38 => P63 | D39 => P64 | D40 => P65 | D41 => P66 | D42 => P67 | D43 => P68 | D44 => P69 | D45 => P70 | D46 => P71 | D47 => P72 | D48 => P73 | D49 => P74 | D50 => P75 | D51 => P76 | D52 => P77 | D53 => P78 | D54 => P79 | D55 => P80 | D56 => P81 | D57 => P82 | D58 => P83 | D59 => P84 | D60 => P85 | D61 => P86 | D62 => P87 | D63 => P88 end
  | D25 => match b with D0 => P26 | D1 => P27 | D2 => P28 | D3 => P29 | D4 => P30 | D5 => P31 | D6 => P32 | D7 => P33 | D8 => P34 | D9 => P35 | D10 => P36 | D11 => P37 | D12 => P38 | D13 => P39 | D14 => P40 | D15 => P41 | D16 => P42 | D17 => P43 | D18 => P44 | D19 => P45 | D20 => P46 | D21 => P47 | D22 => P48 | D23 => P49 | D24 => P50 | D25 => P51 | D26 => P52 | D27 => P53 | D28 => P54 | D29 => P55 | D30 => P56 | D31 => P57 | D32 => P58 | D33 => P59 | D34 => P60 | D35 => P61 | D36 => P62 | D37 => P63 | D38 => P64 | D39 => P65 | D40 => P66 | D41 => P67 | D42 => P68 | D43 => P69 | D44 => P70 | D45 => P71 | D46 => P72 | D47 => P73 | D48 => P74 | D49 => P75 | D50 => P76 | D51 => P77 | D52 => P78 | D53 => P79 | D54 => P80 | D55 => P81 | D56 => P82 | D57 => P83 | D58 => P84 | D59 => P85 | D60 => P86 | D61 => P87 | D62 => P88 | D63 => P89 end
  | D26 => match b with D0 => P27 | D1 => P28 | D2 => P29 | D3 => P30 | D4 => P31 | D5 => P32 | D6 => P33 | D7 => P34 | D8 => P35 | D9 => P36 | D10 => P37 | D11 => P38 | D12 => P39 | D13 => P40 | D14 => P41 | D15 => P42 | D16 => P43 | D17 => P44 | D18 => P45 | D19 => P46 | D20 => P47 | D21 => P48 | D22 => P49 | D23 => P50 | D24 => P51 | D25 => P52 | D26 => P53 | D27 => P54 | D28 => P55 | D29 => P56 | D30 => P57 | D31 => P58 | D32 => P59 | D33 => P60 | D34 => P61 | D35 => P62 | D36 => P63 | D37 => P64 | D38 => P65 | D39 => P66 | D40 => P67 | D41 => P68 | D42 => P69 | D43 => P70 | D44 => P71 | D45 => P72 | D46 => P73 | D47 => P74 | D48 => P75 | D49 => P76 | D50 => P77 | D51 => P78 | D52 => P79 | D53 => P80 | D54 => P81 | D55 => P82 | D56 => P83 | D57 => P84 | D58 => P85 | D59 => P86 | D60 => P87 | D61 => P88 | D62 => P89 | D63 => P90 end
  | D27 => match b with D0 => P28 | D1 => P29 | D2 => P30 | D3 => P31 | D4 => P32 | D5 => P33 | D6 => P34 | D7 => P35 | D8 => P36 | D9 => P37 | D10 => P38 | D11 => P39 | D12 => P40 | D13 => P41 | D14 => P42 | D15 => P43 | D16 => P44 | D17 => P45 | D18 => P46 | D19 => P47 | D20 => P48 | D21 => P49 | D22 => P50 | D23 => P51 | D24 => P52 | D25 => P53 | D26 => P54 | D27 => P55 | D28 => P56 | D29 => P57 | D30 => P58 | D31 => P59 | D32 => P60 | D33 => P61 | D34 => P62 | D35 => P63 | D36 => P64 | D37 => P65 | D38 => P66 | D39 => P67 | D40 => P68 | D41 => P69 | D42 => P70 | D43 => P71 | D44 => P72 | D45 => P73 | D46 => P74 | D47 => P75 | D48 => P76 | D49 => P77 | D50 => P78 | D51 => P79 | D52 => P80 | D53 => P81 | D54 => P82 | D55 => P83 | D56 => P84 | D57 => P85 | D58 => P86 | D59 => P87 | D60 => P88 | D61 => P89 | D62 => P90 | D63 => P91 end
  | D28 => match b with D0 => P29 | D1 => P30 | D2 => P31 | D3 => P32 | D4 => P33 | D5 => P34 | D6 => P35 | D7 => P36 | D8 => P37 | D9 => P38 | D10 => P39 | D11 => P40 | D12 => P41 | D13 => P42 | D14 => P43 | D15 => P44 | D16 => P45 | D17 => P46 | D18 => P47 | D19 => P48 | D20 => P49 | D21 => P50 | D22 => P51 | D23 => P52 | D24 => P53 | D25 => P54 | D26 => P55 | D27 => P56 | D28 => P57 | D29 => P58 | D30 => P59 | D31 => P60 | D32 => P61 | D33 => P62 | D34 => P63 | D35 => P64 | D36 => P65 | D37 => P66 | D38 => P67 | D39 => P68 | D40 => P69 | D41 => P70 | D42 => P71 | D43 => P72 | D44 => P73 | D45 => P74 | D46 => P75 | D47 => P76 | D48 => P77 | D49 => P78 | D50 => P79 | D51 => P80 | D52 => P81 | D53 => P82 | D54 => P83 | D55 => P84 | D56 => P85 | D57 => P86 | D58 => P87 | D59 => P88 | D60 => P89 | D61 => P90 | D62 => P91 | D63 => P92 end
  | D29 => match b with D0 => P30 | D1 => P31 | D2 => P32 | D3 => P33 | D4 => P34 | D5 => P35 | D6 => P36 | D7 => P37 | D8 => P38 | D9 => P39 | D10 => P40 | D11 => P41 | D12 => P42 | D13 => P43 | D14 => P44 | D15 => P45 | D16 => P46 | D17 => P47 | D18 => P48 | D19 => P49 | D20 => P50 | D21 => P51 | D22 => P52 | D23 => P53 | D24 => P54 | D25 => P55 | D26 => P56 | D27 => P57 | D28 => P58 | D29 => P59 | D30 => P60 | D31 => P61 | D32 => P62 | D33 => P63 | D34 => P64 | D35 => P65 | D36 => P66 | D37 => P67 | D38 => P68 | D39 => P69 | D40 => P70 | D41 => P71 | D42 => P72 | D43 => P73 | D44 => P74 | D45 => P75 | D46 => P76 | D47 => P77 | D48 => P78 | D49 => P79 | D50 => P80 | D51 => P81 | D52 => P82 | D53 => P83 | D54 => P84 | D55 => P85 | D56 => P86 | D57 => P87 | D58 => P88 | D59 => P89 | D60 => P90 | D61 => P91 | D62 => P92 | D63 => P93 end
  | D30 => match b with D0 => P31 | D1 => P32 | D2 => P33 | D3 => P34 | D4 => P35 | D5 => P36 | D6 => P37 | D7 => P38 | D8 => P39 | D9 => P40 | D10 => P41 | D11 => P42 | D12 => P43 | D13 => P44 | D14 => P45 | D15 => P46 | D16 => P47 | D17 => P48 | D18 => P49 | D19 => P50 | D20 => P51 | D21 => P52 | D22 => P53 | D23 => P54 | D24 => P55 | D25 => P56 | D26 => P57 | D27 => P58 | D28 => P59 | D29 => P60 | D30 => P61 | D31 => P62 | D32 => P63 | D33 => P64 | D34 => P65 | D35 => P66 | D36 => P67 | D37 => P68 | D38 => P69 | D39 => P70 | D40 => P71 | D41 => P72 | D42 => P73 | D43 => P74 | D44 => P75 | D45 => P76 | D46 => P77 | D47 => P78 | D48 => P79 | D49 => P80 | D50 => P81 | D51 => P82 | D52 => P83 | D53 => P84 | D54 => P85 | D55 => P86 | D56 => P87 | D57 => P88 | D58 => P89 | D59 => P90 | D60 => P91 | D61 => P92 | D62 => P93 | D63 => P94 end
  | D31 => match b with D0 => P32 | D1 => P33 | D2 => P34 | D3 => P35 | D4 => P36 | D5 => P37 | D6 => P38 | D7 => P39 | D8 => P40 | D9 => P41 | D10 => P42 | D11 => P43 | D12 => P44 | D13 => P45 | D14 => P46 | D15 => P47 | D16 => P48 | D17 => P49 | D18 => P50 | D19 => P51 | D20 => P52 | D21 => P53 | D22 => P54 | D23 => P55 | D24 => P56 | D25 => P57 | D26 => P58 | D27 => P59 | D28 => P60 | D29 => P61 | D30 => P62 | D31 => P63 | D32 => P64 | D33 => P65 | D34 => P66 | D35 => P67 | D36 => P68 | D37 => P69 | D38 => P70 | D39 => P71 | D40 => P72 | D41 => P73 | D42 => P74 | D43 => P75 | D44 => P76 | D45 => P77 | D46 => P78 | D47 => P79 | D48 => P80 | D49 => P81 | D50 => P82 | D51 => P83 | D52 => P84 | D53 => P85 | D54 => P86 | D55 => P87 | D56 => P88 | D57 => P89 | D58 => P90 | D59 => P91 | D60 => P92 | D61 => P93 | D62 => P94 | D63 => P95 end
  | D32 => match b with D0 => P33 | D1 => P34 | D2 => P35 | D3 => P36 | D4 => P37 | D5 => P38 | D6 => P39 | D7 => P40 | D8 => P41 | D9 => P42 | D10 => P43 | D11 => P44 | D12 => P45 | D13 => P46 | D14 => P47 | D15 => P48 | D16 => P49 | D17 => P50 | D18 => P51 | D19 => P52 | D20 => P53 | D21 => P54 | D22 => P55 | D23 => P56 | D24 => P57 | D25 => P58 | D26 => P59 | D27 => P60 | D28 => P61 | D29 => P62 | D30 => P63 | D31 => P64 | D32 => P65 | D33 => P66 | D34 => P67 | D35 => P68 | D36 => P69 | D37 => P70 | D38 => P71 | D39 => P72 | D40 => P73 | D41 => P74 | D42 => P75 | D43 => P76 | D44 => P77 | D45 => P78 | D46 => P79 | D47 => P80 | D48 => P81 | D49 => P82 | D50 => P83 | D51 => P84 | D52 => P85 | D53 => P86 | D54 => P87 | D55 => P88 | D56 => P89 | D57 => P90 | D58 => P91 | D59 => P92 | D60 => P93 | D61 => P94 | D62 => P95 | D63 => P96 end
  | D33 => match b with D0 => P34 | D1 => P35 | D2 => P36 | D3 => P37 | D4 => P38 | D5 => P39 | D6 => P40 | D7 => P41 | D8 => P42 | D9 => P43 | D10 => P44 | D11 => P45 | D12 => P46 | D13 => P47 | D14 => P48 | D15 => P49 | D16 => P50 | D17 => P51 | D18 => P52 | D19 => P53 | D20 => P54 | D21 => P55 | D22 => P56 | D23 => P57 | D24 => P58 | D25 => P59 | D26 => P60 | D27 => P61 | D28 => P62 | D29 => P63 | D30 => P64 | D31 => P65 | D32 => P66 | D33 => P67 | D34 => P68 | D35 => P69 | D36 => P70 | D37 => P71 | D38 => P72 | D39 => P73 | D40 => P74 | D41 => P75 | D42 => P76 | D43 => P77 | D44 => P78 | D45 => P79 | D46 => P80 | D47 => P81 | D48 => P82 | D49 => P83 | D50 => P84 | D51 => P85 | D52 => P86 | D53 => P87 | D54 => P88 | D55 => P89 | D56 => P90 | D57 => P91 | D58 => P92 | D59 => P93 | D60 => P94 | D61 => P95 | D62 => P96 | D63 => P97 end
  | D34 => match b with D0 => P35 | D1 => P36 | D2 => P37 | D3 => P38 | D4 => P39 | D5 => P40 | D6 => P41 | D7 => P42 | D8 => P43 | D9 => P44 | D10 => P45 | D11 => P46 | D12 => P47 | D13 => P48 | D14 => P49 | D15 => P50 | D16 => P51 | D17 => P52 | D18 => P53 | D19 => P54 | D20 => P55 | D21 => P56 | D22 => P57 | D23 => P58 | D24 => P59 | D25 => P60 | D26 => P61 | D27 => P62 | D28 => P63 | D29 => P64 | D30 => P65 | D31 => P66 | D32 => P67 | D33 => P68 | D34 => P69 | D35 => P70 | D36 => P71 | D37 => P72 | D38 => P73 | D39 => P74 | D40 => P75 | D41 => P76 | D42 => P77 | D43 => P78 | D44 => P79 | D45 => P80 | D46 => P81 | D47 => P82 | D48 => P83 | D49 => P84 | D50 => P85 | D51 => P86 | D52 => P87 | D53 => P88 | D54 => P89 | D55 => P90 | D56 => P91 | D57 => P92 | D58 => P93 | D59 => P94 | D60 => P95 | D61 => P96 | D62 => P97 | D63 => P98 end
  | D35 => match b with D0 => P36 | D1 => P37 | D2 => P38 | D3 => P39 | D4 => P40 | D5 => P41 | D6 => P42 | D7 => P43 | D8 => P44 | D9 => P45 | D10 => P46 | D11 => P47 | D12 => P48 | D13 => P49 | D14 => P50 | D15 => P51 | D16 => P52 | D17 => P53 | D18 => P54 | D19 => P55 | D20 => P56 | D21 => P57 | D22 => P58 | D23 => P59 | D24 => P60 | D25 => P61 | D26 => P62 | D27 => P63 | D28 => P64 | D29 => P65 | D30 => P66 | D31 => P67 | D32 => P68 | D33 => P69 | D34 => P70 | D35 => P71 | D36 => P72 | D37 => P73 | D38 => P74 | D39 => P75 | D40 => P76 | D41 => P77 | D42 => P78 | D43 => P79 | D44 => P80 | D45 => P81 | D46 => P82 | D47 => P83 | D48 => P84 | D49 => P85 | D50 => P86 | D51 => P87 | D52 => P88 | D53 => P89 | D54 => P90 | D55 => P91 | D56 => P92 | D57 => P93 | D58 => P94 | D59 => P95 | D60 => P96 | D61 => P97 | D62 => P98 | D63 => P99 end
  | D36 => match b with D0 => P37 | D1 => P38 | D2 => P39 | D3 => P40 | D4 => P41 | D5 => P42 | D6 => P43 | D7 => P44 | D8 => P45 | D9 => P46 | D10 => P47 | D11 => P48 | D12 => P49 | D13 => P50 | D14 => P51 | D15 => P52 | D16 => P53 | D17 => P54 | D18 => P55 | D19 => P56 | D20 => P57 | D21 => P58 | D22 => P59 | D23 => P60 | D24 => P61 | D25 => P62 | D26 => P63 | D27 => P64 | D28 => P65 | D29 => P66 | D30 => P67 | D31 => P68 | D32 => P69 | D33 => P70 | D34 => P71 | D35 => P72 | D36 => P73 | D37 => P74 | D38 => P75 | D39 => P76 | D40 => P77 | D41 => P78 | D42 => P79 | D43 => P80 | D44 => P81 | D45 => P82 | D46 => P83 | D47 => P84 | D48 => P85 | D49 => P86 | D50 => P87 | D51 => P88 | D52 => P89 | D53 => P90 | D54 => P91 | D55 => P92 | D56 => P93 | D57 => P94 | D58 => P95 | D59 => P96 | D60 => P97 | D61 => P98 | D62 => P99 | D63 => P100 end
  | D37 => match b with D0 => P38 | D1 => P39 | D2 => P40 | D3 => P41 | D4 => P42 | D5 => P43 | D6 => P44 | D7 => P45 | D8 => P46 | D9 => P47 | D10 => P48 | D11 => P49 | D12 => P50 | D13 => P51 | D14 => P52 | D15 => P53 | D16 => P54 | D17 => P55 | D18 => P56 | D19 => P57 | D20 => P58 | D21 => P59 | D22 => P60 | D23 => P61 | D24 => P62 | D25 => P63 | D26 => P64 | D27 => P65 | D28 => P66 | D29 => P67 | D30 => P68 | D31 => P69 | D32 => P70 | D33 => P71 | D34 => P72 | D35 => P73 | D36 => P74 | D37 => P75 | D38 => P76 | D39 => P77 | D40 => P78 | D41 => P79 | D42 => P80 | D43 => P81 | D44 => P82 | D45 => P83 | D46 => P84 | D47 => P85 | D48 => P86 | D49 => P87 | D50 => P88 | D51 => P89 | D52 => P90 | D53 => P91 | D54 => P92 | D55 => P93 | D56 => P94 | D57 => P95 | D58 => P96 | D59 => P97 | D60 => P98 | D61 => P99 | D62 => P100 | D63 => P101 end
  | D38 => match b with D0 => P39 | D1 => P40 | D2 => P41 | D3 => P42 | D4 => P43 | D5 => P44 | D6 => P45 | D7 => P46 | D8 => P47 | D9 => P48 | D10 => P49 | D11 => P50 | D12 => P51 | D13 => P52 | D14 => P53 | D15 => P54 | D16 => P55 | D17 => P56 | D18 => P57 | D19 => P58 | D20 => P59 | D21 => P60 | D22 => P61 | D23 => P62 | D24 => P63 | D25 => P64 | D26 => P65 | D27 => P66 | D28 => P67 | D29 => P68 | D30 => P69 | D31 => P70 | D32 => P71 | D33 => P72 | D34 => P73 | D35 => P74 | D36 => P75 | D37 => P76 | D38 => P77 | D39 => P78 | D40 => P79 | D41 => P80 | D42 => P81 | D43 => P82 | D44 => P83 | D45 => P84 | D46 => P85 | D47 => P86 | D48 => P87 | D49 => P88 | D50 => P89 | D51 => P90 | D52 => P91 | D53 => P92 | D54 => P93 | D55 => P94 | D56 => P95 | D57 => P96 | D58 => P97 | D59 => P98 | D60 => P99 | D61 => P100 | D62 => P101 | D63 => P102 end
  | D39 => match b with D0 => P40 | D1 => P41 | D2 => P42 | D3 => P43 | D4 => P44 | D5 => P45 | D6 => P46 | D7 => P47 | D8 => P48 | D9 => P49 | D10 => P50 | D11 => P51 | D12 => P52 | D13 => P53 | D14 => P54 | D15 => P55 | D16 => P56 | D17 => P57 | D18 => P58 | D19 => P59 | D20 => P60 | D21 => P61 | D22 => P62 | D23 => P63 | D24 => P64 | D25 => P65 | D26 => P66 | D27 => P67 | D28 => P68 | D29 => P69 | D30 => P70 | D31 => P71 | D32 => P72 | D33 => P73 | D34 => P74 | D35 => P75 | D36 => P76 | D37 => P77 | D38 => P78 | D39 => P79 | D40 => P80 | D41 => P81 | D42 => P82 | D43 => P83 | D44 => P84 | D45 => P85 | D46 => P86 | D47 => P87 | D48 => P88 | D49 => P89 | D50 => P90 | D51 => P91 | D52 => P92 | D53 => P93 | D54 => P94 | D55 => P95 | D56 => P96 | D57 => P97 | D58 => P98 | D59 => P99 | D60 => P100 | D61 => P101 | D62 => P102 | D63 => P103 end
  | D40 => match b with D0 => P41 | D1 => P42 | D2 => P43 | D3 => P44 | D4 => P45 | D5 => P46 | D6 => P47 | D7 => P48 | D8 => P49 | D9 => P50 | D10 => P51 | D11 => P52 | D12 => P53 | D13 => P54 | D14 => P55 | D15 => P56 | D16 => P57 | D17 => P58 | D18 => P59 | D19 => P60 | D20 => P61 | D21 => P62 | D22 => P63 | D23 => P64 | D24 => P65 | D25 => P66 | D26 => P67 | D27 => P68 | D28 => P69 | D29 => P70 | D30 => P71 | D31 => P72 | D32 => P73 | D33 => P74 | D34 => P75 | D35 => P76 | D36 => P77 | D37 => P78 | D38 => P79 | D39 => P80 | D40 => P81 | D41 => P82 | D42 => P83 | D43 => P84 | D44 => P85 | D45 => P86 | D46 => P87 | D47 => P88 | D48 => P89 | D49 => P90 | D50 => P91 | D51 => P92 | D52 => P93 | D53 => P94 | D54 => P95 | D55 => P96 | D56 => P97 | D57 => P98 | D58 => P99 | D59 => P100 | D60 => P101 | D61 => P102 | D62 => P103 | D63 => P104 end
  | D41 => match b with D0 => P42 | D1 => P43 | D2 => P44 | D3 => P45 | D4 => P46 | D5 => P47 | D6 => P48 | D7 => P49 | D8 => P50 | D9 => P51 | D10 => P52 | D11 => P53 | D12 => P54 | D13 => P55 | D14 => P56 | D15 => P57 | D16 => P58 | D17 => P59 | D18 => P60 | D19 => P61 | D20 => P62 | D21 => P63 | D22 => P64 | D23 => P65 | D24 => P66 | D25 => P67 | D26 => P68 | D27 => P69 | D28 => P70 | D29 => P71 | D30 => P72 | D31 => P73 | D32 => P74 | D33 => P75 | D34 => P76 | D35 => P77 | D36 => P78 | D37 => P79 | D38 => P80 | D39 => P81 | D40 => P82 | D41 => P83 | D42 => P84 | D43 => P85 | D44 => P86 | D45 => P87 | D46 => P88 | D47 => P89 | D48 => P90 | D49 => P91 | D50 => P92 | D51 => P93 | D52 => P94 | D53 => P95 | D54 => P96 | D55 => P97 | D56 => P98 | D57 => P99 | D58 => P100 | D59 => P101 | D60 => P102 | D61 => P103 | D62 => P104 | D63 => P105 end
  | D42 => match b with D0 => P43 | D1 => P44 | D2 => P45 | D3 => P46 | D4 => P47 | D5 => P48 | D6 => P49 | D7 => P50 | D8 => P51 | D9 => P52 | D10 => P53 | D11 => P54 | D12 => P55 | D13 => P56 | D14 => P57 | D15 => P58 | D16 => P59 | D17 => P60 | D18 => P61 | D19 => P62 | D20 => P63 | D21 => P64 | D22 => P65 | D23 => P66 | D24 => P67 | D25 => P68 | D26 => P69 | D27 => P70 | D28 => P71 | D29 => P72 | D30 => P73 | D31 => P74 | D32 => P75 | D33 => P76 | D34 => P77 | D35 => P78 | D36 => P79 | D37 => P80 | D38 => P81 | D39 => P82 | D40 => P83 | D41 => P84 | D42 => P85 | D43 => P86 | D44 => P87 | D45 => P88 | D46 => P89 | D47 => P90 | D48 => P91 | D49 => P92 | D50 => P93 | D51 => P94 | D52 => P95 | D53 => P96 | D54 => P97 | D55 => P98 | D56 => P99 | D57 => P100 | D58 => P101 | D59 => P102 | D60 => P103 | D61 => P104 | D62 => P105 | D63 => P106 end
  | D43 => match b with D0 => P44 | D1 => P45 | D2 => P46 | D3 => P47 | D4 => P48 | D5 => P49 | D6 => P50 | D7 => P51 | D8 => P52 | D9 => P53 | D10 => P54 | D11 => P55 | D12 => P56 | D13 => P57 | D14 => P58 | D15 => P59 | D16 => P60 | D17 => P61 | D18 => P62 | D19 => P63 | D20 => P64 | D21 => P65 | D22 => P66 | D23 => P67 | D24 => P68 | D25 => P69 | D26 => P70 | D27 => P71 | D28 => P72 | D29 => P73 | D30 => P74 | D31 => P75 | D32 => P76 | D33 => P77 | D34 => P78 | D35 => P79 | D36 => P80 | D37 => P81 | D38 => P82 | D39 => P83 | D40 => P84 | D41 => P85 | D42 => P86 | D43 => P87 | D44 => P88 | D45 => P89 | D46 => P90 | D47 => P91 | D48 => P92 | D49 => P93 | D50 => P94 | D51 => P95 | D52 => P96 | D53 => P97 | D54 => P98 | D55 => P99 | D56 => P100 | D57 => P101 | D58 => P102 | D59 => P103 | D60 => P104 | D61 => P105 | D62 => P106 | D63 => P107 end
  | D44 => match b with D0 => P45 | D1 => P46 | D2 => P47 | D3 => P48 | D4 => P49 | D5 => P50 | D6 => P51 | D7 => P52 | D8 => P53 | D9 => P54 | D10 => P55 | D11 => P56 | D12 => P57 | D13 => P58 | D14 => P59 | D15 => P60 | D16 => P61 | D17 => P62 | D18 => P63 | D19 => P64 | D20 => P65 | D21 => P66 | D22 => P67 | D23 => P68 | D24 => P69 | D25 => P70 | D26 => P71 | D27 => P72 | D28 => P73 | D29 => P74 | D30 => P75 | D31 => P76 | D32 => P77 | D33 => P78 | D34 => P79 | D35 => P80 | D36 => P81 | D37 => P82 | D38 => P83 | D39 => P84 | D40 => P85 | D41 => P86 | D42 => P87 | D43 => P88 | D44 => P89 | D45 => P90 | D46 => P91 | D47 => P92 | D48 => P93 | D49 => P94 | D50 => P95 | D51 => P96 | D52 => P97 | D53 => P98 | D54 => P99 | D55 => P100 | D56 => P101 | D57 => P102 | D58 => P103 | D59 => P104 | D60 => P105 | D61 => P106 | D62 => P107 | D63 => P108 end
  | D45 => match b with D0 => P46 | D1 => P47 | D2 => P48 | D3 => P49 | D4 => P50 | D5 => P51 | D6 => P52 | D7 => P53 | D8 => P54 | D9 => P55 | D10 => P56 | D11 => P57 | D12 => P58 | D13 => P59 | D14 => P60 | D15 => P61 | D16 => P62 | D17 => P63 | D18 => P64 | D19 => P65 | D20 => P66 | D21 => P67 | D22 => P68 | D23 => P69 | D24 => P70 | D25 => P71 | D26 => P72 | D27 => P73 | D28 => P74 | D29 => P75 | D30 => P76 | D31 => P77 | D32 => P78 | D33 => P79 | D34 => P80 | D35 => P81 | D36 => P82 | D37 => P83 | D38 => P84 | D39 => P85 | D40 => P86 | D41 => P87 | D42 => P88 | D43 => P89 | D44 => P90 | D45 => P91 | D46 => P92 | D47 => P93 | D48 => P94 | D49 => P95 | D50 => P96 | D51 => P97 | D52 => P98 | D53 => P99 | D54 => P100 | D55 => P101 | D56 => P102 | D57 => P103 | D58 => P104 | D59 => P105 | D60 => P106 | D61 => P107 | D62 => P108 | D63 => P109 end
  | D46 => match b with D0 => P47 | D1 => P48 | D2 => P49 | D3 => P50 | D4 => P51 | D5 => P52 | D6 => P53 | D7 => P54 | D8 => P55 | D9 => P56 | D10 => P57 | D11 => P58 | D12 => P59 | D13 => P60 | D14 => P61 | D15 => P62 | D16 => P63 | D17 => P64 | D18 => P65 | D19 => P66 | D20 => P67 | D21 => P68 | D22 => P69 | D23 => P70 | D24 => P71 | D25 => P72 | D26 => P73 | D27 => P74 | D28 => P75 | D29 => P76 | D30 => P77 | D31 => P78 | D32 => P79 | D33 => P80 | D34 => P81 | D35 => P82 | D36 => P83 | D37 => P84 | D38 => P85 | D39 => P86 | D40 => P87 | D41 => P88 | D42 => P89 | D43 => P90 | D44 => P91 | D45 => P92 | D46 => P93 | D47 => P94 | D48 => P95 | D49 => P96 | D50 => P97 | D51 => P98 | D52 => P99 | D53 => P100 | D54 => P101 | D55 => P102 | D56 => P103 | D57 => P104 | D58 => P105 | D59 => P106 | D60 => P107 | D61 => P108 | D62 => P109 | D63 => P110 end
  | D47 => match b with D0 => P48 | D1 => P49 | D2 => P50 | D3 => P51 | D4 => P52 | D5 => P53 | D6 => P54 | D7 => P55 | D8 => P56 | D9 => P57 | D10 => P58 | D11 => P59 | D12 => P60 | D13 => P61 | D14 => P62 | D15 => P63 | D16 => P64 | D17 => P65 | D18 => P66 | D19 => P67 | D20 => P68 | D21 => P69 | D22 => P70 | D23 => P71 | D24 => P72 | D25 => P73 | D26 => P74 | D27 => P75 | D28 => P76 | D29 => P77 | D30 => P78 | D31 => P79 | D32 => P80 | D33 => P81 | D34 => P82 | D35 => P83 | D36 => P84 | D37 => P85 | D38 => P86 | D39 => P87 | D40 => P88 | D41 => P89 | D42 => P90 | D43 => P91 | D44 => P92 | D45 => P93 | D46 => P94 | D47 => P95 | D48 => P96 | D49 => P97 | D50 => P98 | D51 => P99 | D52 => P100 | D53 => P101 | D54 => P102 | D55 => P103 | D56 => P104 | D57 => P105 | D58 => P106 | D59 => P107 | D60 => P108 | D61 => P109 | D62 => P110 | D63 => P111 end
  | D48 => match b with D0 => P49 | D1 => P50 | D2 => P51 | D3 => P52 | D4 => P53 | D5 => P54 | D6 => P55 | D7 => P56 | D8 => P57 | D9 => P58 | D10 => P59 | D11 => P60 | D12 => P61 | D13 => P62 | D14 => P63 | D15 => P64 | D16 => P65 | D17 => P66 | D18 => P67 | D19 => P68 | D20 => P69 | D21 => P70 | D22 => P71 | D23 => P72 | D24 => P73 | D25 => P74 | D26 => P75 | D27 => P76 | D28 => P77 | D29 => P78 | D30 => P79 | D31 => P80 | D32 => P81 | D33 => P82 | D34 => P83 | D35 => P84 | D36 => P85 | D37 => P86 | D38 => P87 | D39 => P88 | D40 => P89 | D41 => P90 | D42 => P91 | D43 => P92 | D44 => P93 | D45 => P94 | D46 => P95 | D47 => P96 | D48 => P97 | D49 => P98 | D50 => P99 | D51 => P100 | D52 => P101 | D53 => P102 | D54 => P103 | D55 => P104 | D56 => P105 | D57 => P106 | D58 => P107 | D59 => P108 | D60 => P109 | D61 => P110 | D62 => P111 | D63 => P112 end
  | D49 => match b with D0 => P50 | D1 => P51 | D2 => P52 | D3 => P53 | D4 => P54 | D5 => P55 | D6 => P56 | D7 => P57 | D8 => P58 | D9 => P59 | D10 => P60 | D11 => P61 | D12 => P62 | D13 => P63 | D14 => P64 | D15 => P65 | D16 => P66 | D17 => P67 | D18 => P68 | D19 => P69 | D20 => P70 | D21 => P71 | D22 => P72 | D23 => P73 | D24 => P74 | D25 => P75 | D26 => P76 | D27 => P77 | D28 => P78 | D29 => P79 | D30 => P80 | D31 => P81 | D32 => P82 | D33 => P83 | D34 => P84 | D35 => P85 | D36 => P86 | D37 => P87 | D38 => P88 | D39 => P89 | D40 => P90 | D41 => P91 | D42 => P92 | D43 => P93 | D44 => P94 | D45 => P95 | D46 => P96 | D47 => P97 | D48 => P98 | D49 => P99 | D50 => P100 | D51 => P101 | D52 => P102 | D53 => P103 | D54 => P104 | D55 => P105 | D56 => P106 | D57 => P107 | D58 => P108 | D59 => P109 | D60 => P110 | D61 => P111 | D62 => P112 | D63 => P113 end
  | D50 => match b with D0 => P51 | D1 => P52 | D2 => P53 | D3 => P54 | D4 => P55 | D5 => P56 | D6 => P57 | D7 => P58 | D8 => P59 | D9 => P60 | D10 => P61 | D11 => P62 | D12 => P63 | D13 => P64 | D14 => P65 | D15 => P66 | D16 => P67 | D17 => P68 | D18 => P69 | D19 => P70 | D20 => P71 | D21 => P72 | D22 => P73 | D23 => P74 | D24 => P75 | D25 => P76 | D26 => P77 | D27 => P78 | D28 => P79 | D29 => P80 | D30 => P81 | D31 => P82 | D32 => P83 | D33 => P84 | D34 => P85 | D35 => P86 | D36 => P87 | D37 => P88 | D38 => P89 | D39 => P90 | D40 => P91 | D41 => P92 | D42 => P93 | D43 => P94 | D44 => P95 | D45 => P96 | D46 => P97 | D47 => P98 | D48 => P99 | D49 => P100 | D50 => P101 | D51 => P102 | D52 => P103 | D53 => P104 | D54 => P105 | D55 => P106 | D56 => P107 | D57 => P108 | D58 => P109 | D59 => P110 | D60 => P111 | D61 => P112 | D62 => P113 | D63 => P114 end
  | D51 => match b with D0 => P52 | D1 => P53 | D2 => P54 | D3 => P55 | D4 => P56 | D5 => P57 | D6 => P58 | D7 => P59 | D8 => P60 | D9 => P61 | D10 => P62 | D11 => P63 | D12 => P64 | D13 => P65 | D14 => P66 | D15 => P67 | D16 => P68 | D17 => P69 | D18 => P70 | D19 => P71 | D20 => P72 | D21 => P73 | D22 => P74 | D23 => P75 | D24 => P76 | D25 => P77 | D26 => P78 | D27 => P79 | D28 => P80 | D29 => P81 | D30 => P82 | D31 => P83 | D32 => P84 | D33 => P85 | D34 => P86 | D35 => P87 | D36 => P88 | D37 => P89 | D38 => P90 | D39 => P91 | D40 => P92 | D41 => P93 | D42 => P94 | D43 => P95 | D44 => P96 | D45 => P97 | D46 => P98 | D47 => P99 | D48 => P100 | D49 => P101 | D50 => P102 | D51 => P103 | D52 => P104 | D53 => P105 | D54 => P106 | D55 => P107 | D56 => P108 | D57 => P109 | D58 => P110 | D59 => P111 | D60 => P112 | D61 => P113 | D62 => P114 | D63 => P115 end
  | D52 => match b with D0 => P53 | D1 => P54 | D2 => P55 | D3 => P56 | D4 => P57 | D5 => P58 | D6 => P59 | D7 => P60 | D8 => P61 | D9 => P62 | D10 => P63 | D11 => P64 | D12 => P65 | D13 => P66 | D14 => P67 | D15 => P68 | D16 => P69 | D17 => P70 | D18 => P71 | D19 => P72 | D20 => P73 | D21 => P74 | D22 => P75 | D23 => P76 | D24 => P77 | D25 => P78 | D26 => P79 | D27 => P80 | D28 => P81 | D29 => P82 | D30 => P83 | D31 => P84 | D32 => P85 | D33 => P86 | D34 => P87 | D35 => P88 | D36 => P89 | D37 => P90 | D38 => P91 | D39 => P92 | D40 => P93 | D41 => P94 | D42 => P95 | D43 => P96 | D44 => P97 | D45 => P98 | D46 => P99 | D47 => P100 | D48 => P101 | D49 => P102 | D50 => P103 | D51 => P104 | D52 => P105 | D53 => P106 | D54 => P107 | D55 => P108 | D56 => P109 | D57 => P110 | D58 => P111 | D59 => P112 | D60 => P113 | D61 => P114 | D62 => P115 | D63 => P116 end
  | D53 => match b with D0 => P54 | D1 => P55 | D2 => P56 | D3 => P57 | D4 => P58 | D5 => P59 | D6 => P60 | D7 => P61 | D8 => P62 | D9 => P63 | D10 => P64 | D11 => P65 | D12 => P66 | D13 => P67 | D14 => P68 | D15 => P69 | D16 => P70 | D17 => P71 | D18 => P72 | D19 => P73 | D20 => P74 | D21 => P75 | D22 => P76 | D23 => P77 | D24 => P78 | D25 => P79 | D26 => P80 | D27 => P81 | D28 => P82 | D29 => P83 | D30 => P84 | D31 => P85 | D32 => P86 | D33 => P87 | D34 => P88 | D35 => P89 | D36 => P90 | D37 => P91 | D38 => P92 | D39 => P93 | D40 => P94 | D41 => P95 | D42 => P96 | D43 => P97 | D44 => P98 | D45 => P99 | D46 => P100 | D47 => P101 | D48 => P102 | D49 => P103 | D50 => P104 | D51 => P105 | D52 => P106 | D53 => P107 | D54 => P108 | D55 => P109 | D56 => P110 | D57 => P111 | D58 => P112 | D59 => P113 | D60 => P114 | D61 => P115 | D62 => P116 | D63 => P117 end
  | D54 => match b with D0 => P55 | D1 => P56 | D2 => P57 | D3 => P58 | D4 => P59 | D5 => P60 | D6 => P61 | D7 => P62 | D8 => P63 | D9 => P64 | D10 => P65 | D11 => P66 | D12 => P67 | D13 => P68 | D14 => P69 | D15 => P70 | D16 => P71 | D17 => P72 | D18 => P73 | D19 => P74 | D20 => P75 | D21 => P76 | D22 => P77 | D23 => P78 | D24 => P79 | D25 => P80 | D26 => P81 | D27 => P82 | D28 => P83 | D29 => P84 | D30 => P85 | D31 => P86 | D32 => P87 | D33 => P88 | D34 => P89 | D35 => P90 | D36 => P91 | D37 => P92 | D38 => P93 | D39 => P94 | D40 => P95 | D41 => P96 | D42 => P97 | D43 => P98 | D44 => P99 | D45 => P100 | D46 => P101 | D47 => P102 | D48 => P103 | D49 => P104 | D50 => P105 | D51 => P106 | D52 => P107 | D53 => P108 | D54 => P109 | D55 => P110 | D56 => P111 | D57 => P112 | D58 => P113 | D59 => P114 | D60 => P115 | D61 => P116 | D62 => P117 | D63 => P118 end
  | D55 => match b with D0 => P56 | D1 => P57 | D2 => P58 | D3 => P59 | D4 => P60 | D5 => P61 | D6 => P62 | D7 => P63 | D8 => P64 | D9 => P65 | D10 => P66 | D11 => P67 | D12 => P68 | D13 => P69 | D14 => P70 | D15 => P71 | D16 => P72 | D17 => P73 | D18 => P74 | D19 => P75 | D20 => P76 | D21 => P77 | D22 => P78 | D23 => P79 | D24 => P80 | D25 => P81 | D26 => P82 | D27 => P83 | D28 => P84 | D29 => P85 | D30 => P86 | D31 => P87 | D32 => P88 | D33 => P89 | D34 => P90 | D35 => P91 | D36 => P92 | D37 => P93 | D38 => P94 | D39 => P95 | D40 => P96 | D41 => P97 | D42 => P98 | D43 => P99 | D44 => P100 | D45 => P101 | D46 => P102 | D47 => P103 | D48 => P104 | D49 => P105 | D50 => P106 | D51 => P107 | D52 => P108 | D53 => P109 | D54 => P110 | D55 => P111 | D56 => P112 | D57 => P113 | D58 => P114 | D59 => P115 | D60 => P116 | D61 => P117 | D62 => P118 | D63 => P119 end
  | D56 => match b with D0 => P57 | D1 => P58 | D2 => P59 | D3 => P60 | D4 => P61 | D5 => P62 | D6 => P63 | D7 => P64 | D8 => P65 | D9 => P66 | D10 => P67 | D11 => P68 | D12 => P69 | D13 => P70 | D14 => P71 | D15 => P72 | D16 => P73 | D17 => P74 | D18 => P75 | D19 => P76 | D20 => P77 | D21 => P78 | D22 => P79 | D23 => P80 | D24 => P81 | D25 => P82 | D26 => P83 | D27 => P84 | D28 => P85 | D29 => P86 | D30 => P87 | D31 => P88 | D32 => P89 | D33 => P90 | D34 => P91 | D35 => P92 | D36 => P93 | D37 => P94 | D38 => P95 | D39 => P96 | D40 => P97 | D41 => P98 | D42 => P99 | D43 => P100 | D44 => P101 | D45 => P102 | D46 => P103 | D47 => P104 | D48 => P105 | D49 => P106 | D50 => P107 | D51 => P108 | D52 => P109 | D53 => P110 | D54 => P111 | D55 => P112 | D56 => P113 | D57 => P114 | D58 => P115 | D59 => P116 | D60 => P117 | D61 => P118 | D62 => P119 | D63 => P120 end
  | D57 => match b with D0 => P58 | D1 => P59 | D2 => P60 | D3 => P61 | D4 => P62 | D5 => P63 | D6 => P64 | D7 => P65 | D8 => P66 | D9 => P67 | D10 => P68 | D11 => P69 | D12 => P70 | D13 => P71 | D14 => P72 | D15 => P73 | D16 => P74 | D17 => P75 | D18 => P76 | D19 => P77 | D20 => P78 | D21 => P79 | D22 => P80 | D23 => P81 | D24 => P82 | D25 => P83 | D26 => P84 | D27 => P85 | D28 => P86 | D29 => P87 | D30 => P88 | D31 => P89 | D32 => P90 | D33 => P91 | D34 => P92 | D35 => P93 | D36 => P94 | D37 => P95 | D38 => P96 | D39 => P97 | D40 => P98 | D41 => P99 | D42 => P100 | D43 => P101 | D44 => P102 | D45 => P103 | D46 => P104 | D47 => P105 | D48 => P106 | D49 => P107 | D50 => P108 | D51 => P109 | D52 => P110 | D53 => P111 | D54 => P112 | D55 => P113 | D56 => P114 | D57 => P115 | D58 => P116 | D59 => P117 | D60 => P118 | D61 => P119 | D62 => P120 | D63 => P121 end
  | D58 => match b with D0 => P59 | D1 => P60 | D2 => P61 | D3 => P62 | D4 => P63 | D5 => P64 | D6 => P65 | D7 => P66 | D8 => P67 | D9 => P68 | D10 => P69 | D11 => P70 | D12 => P71 | D13 => P72 | D14 => P73 | D15 => P74 | D16 => P75 | D17 => P76 | D18 => P77 | D19 => P78 | D20 => P79 | D21 => P80 | D22 => P81 | D23 => P82 | D24 => P83 | D25 => P84 | D26 => P85 | D27 => P86 | D28 => P87 | D29 => P88 | D30 => P89 | D31 => P90 | D32 => P91 | D33 => P92 | D34 => P93 | D35 => P94 | D36 => P95 | D37 => P96 | D38 => P97 | D39 => P98 | D40 => P99 | D41 => P100 | D42 => P101 | D43 => P102 | D44 => P103 | D45 => P104 | D46 => P105 | D47 => P106 | D48 => P107 | D49 => P108 | D50 => P109 | D51 => P110 | D52 => P111 | D53 => P112 | D54 => P113 | D55 => P114 | D56 => P115 | D57 => P116 | D58 => P117 | D59 => P118 | D60 => P119 | D61 => P120 | D62 => P121 | D63 => P122 end
  | D59 => match b with D0 => P60 | D1 => P61 | D2 => P62 | D3 => P63 | D4 => P64 | D5 => P65 | D6 => P66 | D7 => P67 | D8 => P68 | D9 => P69 | D10 => P70 | D11 => P71 | D12 => P72 | D13 => P73 | D14 => P74 | D15 => P75 | D16 => P76 | D17 => P77 | D18 => P78 | D19 => P79 | D20 => P80 | D21 => P81 | D22 => P82 | D23 => P83 | D24 => P84 | D25 => P85 | D26 => P86 | D27 => P87 | D28 => P88 | D29 => P89 | D30 => P90 | D31 => P91 | D32 => P92 | D33 => P93 | D34 => P94 | D35 => P95 | D36 => P96 | D37 => P97 | D38 => P98 | D39 => P99 | D40 => P100 | D41 => P101 | D42 => P102 | D43 => P103 | D44 => P104 | D45 => P105 | D46 => P106 | D47 => P107 | D48 => P108 | D49 => P109 | D50 => P110 | D51 => P111 | D52 => P112 | D53 => P113 | D54 => P114 | D55 => P115 | D56 => P116 | D57 => P117 | D58 => P118 | D59 => P119 | D60 => P120 | D61 => P121 | D62 => P122 | D63 => P123 end
  | D60 => match b with D0 => P61 | D1 => P62 | D2 => P63 | D3 => P64 | D4 => P65 | D5 => P66 | D6 => P67 | D7 => P68 | D8 => P69 | D9 => P70 | D10 => P71 | D11 => P72 | D12 => P73 | D13 => P74 | D14 => P75 | D15 => P76 | D16 => P77 | D17 => P78 | D18 => P79 | D19 => P80 | D20 => P81 | D21 => P82 | D22 => P83 | D23 => P84 | D24 => P85 | D25 => P86 | D26 => P87 | D27 => P88 | D28 => P89 | D29 => P90 | D30 => P91 | D31 => P92 | D32 => P93 | D33 => P94 | D34 => P95 | D35 => P96 | D36 => P97 | D37 => P98 | D38 => P99 | D39 => P100 | D40 => P101 | D41 => P102 | D42 => P103 | D43 => P104 | D44 => P105 | D45 => P106 | D46 => P107 | D47 => P108 | D48 => P109 | D49 => P110 | D50 => P111 | D51 => P112 | D52 => P113 | D53 => P114 | D54 => P115 | D55 => P116 | D56 => P117 | D57 => P118 | D58 => P119 | D59 => P120 | D60 => P121 | D61 => P122 | D62 => P123 | D63 => P124 end
  | D61 => match b with D0 => P62 | D1 => P63 | D2 => P64 | D3 => P65 | D4 => P66 | D5 => P67 | D6 => P68 | D7 => P69 | D8 => P70 | D9 => P71 | D10 => P72 | D11 => P73 | D12 => P74 | D13 => P75 | D14 => P76 | D15 => P77 | D16 => P78 | D17 => P79 | D18 => P80 | D19 => P81 | D20 => P82 | D21 => P83 | D22 => P84 | D23 => P85 | D24 => P86 | D25 => P87 | D26 => P88 | D27 => P89 | D28 => P90 | D29 => P91 | D30 => P92 | D31 => P93 | D32 => P94 | D33 => P95 | D34 => P96 | D35 => P97 | D36 => P98 | D37 => P99 | D38 => P100 | D39 => P101 | D40 => P102 | D41 => P103 | D42 => P104 | D43 => P105 | D44 => P106 | D45 => P107 | D46 => P108 | D47 => P109 | D48 => P110 | D49 => P111 | D50 => P112 | D51 => P113 | D52 => P114 | D53 => P115 | D54 => P116 | D55 => P117 | D56 => P118 | D57 => P119 | D58 => P120 | D59 => P121 | D60 => P122 | D61 => P123 | D62 => P124 | D63 => P125 end
  | D62 => match b with D0 => P63 | D1 => P64 | D2 => P65 | D3 => P66 | D4 => P67 | D5 => P68 | D6 => P69 | D7 => P70 | D8 => P71 | D9 => P72 | D10 => P73 | D11 => P74 | D12 => P75 | D13 => P76 | D14 => P77 | D15 => P78 | D16 => P79 | D17 => P80 | D18 => P81 | D19 => P82 | D20 => P83 | D21 => P84 | D22 => P85 | D23 => P86 | D24 => P87 | D25 => P88 | D26 => P89 | D27 => P90 | D28 => P91 | D29 => P92 | D30 => P93 | D31 => P94 | D32 => P95 | D33 => P96 | D34 => P97 | D35 => P98 | D36 => P99 | D37 => P100 | D38 => P101 | D39 => P102 | D40 => P103 | D41 => P104 | D42 => P105 | D43 => P106 | D44 => P107 | D45 => P108 | D46 => P109 | D47 => P110 | D48 => P111 | D49 => P112 | D50 => P113 | D51 => P114 | D52 => P115 | D53 => P116 | D54 => P117 | D55 => P118 | D56 => P119 | D57 => P120 | D58 => P121 | D59 => P122 | D60 => P123 | D61 => P124 | D62 => P125 | D63 => P126 end
  | D63 => match b with D0 => P64 | D1 => P65 | D2 => P66 | D3 => P67 | D4 => P68 | D5 => P69 | D6 => P70 | D7 => P71 | D8 => P72 | D9 => P73 | D10 => P74 | D11 => P75 | D12 => P76 | D13 => P77 | D14 => P78 | D15 => P79 | D16 => P80 | D17 => P81 | D18 => P82 | D19 => P83 | D20 => P84 | D21 => P85 | D22 => P86 | D23 => P87 | D24 => P88 | D25 => P89 | D26 => P90 | D27 => P91 | D28 => P92 | D29 => P93 | D30 => P94 | D31 => P95 | D32 => P96 | D33 => P97 | D34 => P98 | D35 => P99 | D36 => P100 | D37 => P101 | D38 => P102 | D39 => P103 | D40 => P104 | D41 => P105 | D42 => P106 | D43 => P107 | D44 => P108 | D45 => P109 | D46 => P110 | D47 => P111 | D48 => P112 | D49 => P113 | D50 => P114 | D51 => P115 | D52 => P116 | D53 => P117 | D54 => P118 | D55 => P119 | D56 => P120 | D57 => P121 | D58 => P122 | D59 => P123 | D60 => P124 | D61 => P125 | D62 => P126 | D63 => P127 end
  end else match a with
  | D0 => match b with D0 => P0 | D1 => P1 | D2 => P2 | D3 => P3 | D4 => P4 | D5 => P5 | D6 => P6 | D7 => P7 | D8 => P8 | D9 => P9 | D10 => P10 | D11 => P11 | D12 => P12 | D13 => P13 | D14 => P14 | D15 => P15 | D16 => P16 | D17 => P17 | D18 => P18 | D19 => P19 | D20 => P20 | D21 => P21 | D22 => P22 | D23 => P23 | D24 => P24 | D25 => P25 | D26 => P26 | D27 => P27 | D28 => P28 | D29 => P29 | D30 => P30 | D31 => P31 | D32 => P32 | D33 => P33 | D34 => P34 | D35 => P35 | D36 => P36 | D37 => P37 | D38 => P38 | D39 => P39 | D40 => P40 | D41 => P41 | D42 => P42 | D43 => P43 | D44 => P44 | D45 => P45 | D46 => P46 | D47 => P47 | D48 => P48 | D49 => P49 | D50 => P50 | D51 => P51 | D52 => P52 | D53 => P53 | D54 => P54 | D55 => P55 | D56 => P56 | D57 => P57 | D58 => P58 | D59 => P59 | D60 => P60 | D61 => P61 | D62 => P62 | D63 => P63 end
  | D1 => match b with D0 => P1 | D1 => P2 | D2 => P3 | D3 => P4 | D4 => P5 | D5 => P6 | D6 => P7 | D7 => P8 | D8 => P9 | D9 => P10 | D10 => P11 | D11 => P12 | D12 => P13 | D13 => P14 | D14 => P15 | D15 => P16 | D16 => P17 | D17 => P18 | D18 => P19 | D19 => P20 | D20 => P21 | D21 => P22 | D22 => P23 | D23 => P24 | D24 => P25 | D25 => P26 | D26 => P27 | D27 => P28 | D28 => P29 | D29 => P30 | D30 => P31 | D31 => P32 | D32 => P33 | D33 => P34 | D34 => P35 | D35 => P36 | D36 => P37 | D37 => P38 | D38 => P39 | D39 => P40 | D40 => P41 | D41 => P42 | D42 => P43 | D43 => P44 | D44 => P45 | D45 => P46 | D46 => P47 | D47 => P48 | D48 => P49 | D49 => P50 | D50 => P51 | D51 => P52 | D52 => P53 | D53 => P54 | D54 => P55 | D55 => P56 | D56 => P57 | D57 => P58 | D58 => P59 | D59 => P60 | D60 => P61 | D61 => P62 | D62 => P63 | D63 => P64 end
  | D2 => match b with D0 => P2 | D1 => P3 | D2 => P4 | D3 => P5 | D4 => P6 | D5 => P7 | D6 => P8 | D7 => P9 | D8 => P10 | D9 => P11 | D10 => P12 | D11 => P13 | D12 => P14 | D13 => P15 | D14 => P16 | D15 => P17 | D16 => P18 | D17 => P19 | D18 => P20 | D19 => P21 | D20 => P22 | D21 => P23 | D22 => P24 | D23 => P25 | D24 => P26 | D25 => P27 | D26 => P28 | D27 => P29 | D28 => P30 | D29 => P31 | D30 => P32 | D31 => P33 | D32 => P34 | D33 => P35 | D34 => P36 | D35 => P37 | D36 => P38 | D37 => P39 | D38 => P40 | D39 => P41 | D40 => P42 | D41 => P43 | D42 => P44 | D43 => P45 | D44 => P46 | D45 => P47 | D46 => P48 | D47 => P49 | D48 => P50 | D49 => P51 | D50 => P52 | D51 => P53 | D52 => P54 | D53 => P55 | D54 => P56 | D55 => P57 | D56 => P58 | D57 => P59 | D58 => P60 | D59 => P61 | D60 => P62 | D61 => P63 | D62 => P64 | D63 => P65 end
  | D3 => match b with D0 => P3 | D1 => P4 | D2 => P5 | D3 => P6 | D4 => P7 | D5 => P8 | D6 => P9 | D7 => P10 | D8 => P11 | D9 => P12 | D10 => P13 | D11 => P14 | D12 => P15 | D13 => P16 | D14 => P17 | D15 => P18 | D16 => P19 | D17 => P20 | D18 => P21 | D19 => P22 | D20 => P23 | D21 => P24 | D22 => P25 | D23 => P26 | D24 => P27 | D25 => P28 | D26 => P29 | D27 => P30 | D28 => P31 | D29 => P32 | D30 => P33 | D31 => P34 | D32 => P35 | D33 => P36 | D34 => P37 | D35 => P38 | D36 => P39 | D37 => P40 | D38 => P41 | D39 => P42 | D40 => P43 | D41 => P44 | D42 => P45 | D43 => P46 | D44 => P47 | D45 => P48 | D46 => P49 | D47 => P50 | D48 => P51 | D49 => P52 | D50 => P53 | D51 => P54 | D52 => P55 | D53 => P56 | D54 => P57 | D55 => P58 | D56 => P59 | D57 => P60 | D58 => P61 | D59 => P62 | D60 => P63 | D61 => P64 | D62 => P65 | D63 => P66 end
  | D4 => match b with D0 => P4 | D1 => P5 | D2 => P6 | D3 => P7 | D4 => P8 | D5 => P9 | D6 => P10 | D7 => P11 | D8 => P12 | D9 => P13 | D10 => P14 | D11 => P15 | D12 => P16 | D13 => P17 | D14 => P18 | D15 => P19 | D16 => P20 | D17 => P21 | D18 => P22 | D19 => P23 | D20 => P24 | D21 => P25 | D22 => P26 | D23 => P27 | D24 => P28 | D25 => P29 | D26 => P30 | D27 => P31 | D28 => P32 | D29 => P33 | D30 => P34 | D31 => P35 | D32 => P36 | D33 => P37 | D34 => P38 | D35 => P39 | D36 => P40 | D37 => P41 | D38 => P42 | D39 => P43 | D40 => P44 | D41 => P45 | D42 => P46 | D43 => P47 | D44 => P48 | D45 => P49 | D46 => P50 | D47 => P51 | D48 => P52 | D49 => P53 | D50 => P54 | D51 => P55 | D52 => P56 | D53 => P57 | D54 => P58 | D55 => P59 | D56 => P60 | D57 => P61 | D58 => P62 | D59 => P63 | D60 => P64 | D61 => P65 | D62 => P66 | D63 => P67 end
  | D5 => match b with D0 => P5 | D1 => P6 | D2 => P7 | D3 => P8 | D4 => P9 | D5 => P10 | D6 => P11 | D7 => P12 | D8 => P13 | D9 => P14 | D10 => P15 | D11 => P16 | D12 => P17 | D13 => P18 | D14 => P19 | D15 => P20 | D16 => P21 | D17 => P22 | D18 => P23 | D19 => P24 | D20 => P25 | D21 => P26 | D22 => P27 | D23 => P28 | D24 => P29 | D25 => P30 | D26 => P31 | D27 => P32 | D28 => P33 | D29 => P34 | D30 => P35 | D31 => P36 | D32 => P37 | D33 => P38 | D34 => P39 | D35 => P40 | D36 => P41 | D37 => P42 | D38 => P43 | D39 => P44 | D40 => P45 | D41 => P46 | D42 => P47 | D43 => P48 | D44 => P49 | D45 => P50 | D46 => P51 | D47 => P52 | D48 => P53 | D49 => P54 | D50 => P55 | D51 => P56 | D52 => P57 | D53 => P58 | D54 => P59 | D55 => P60 | D56 => P61 | D57 => P62 | D58 => P63 | D59 => P64 | D60 => P65 | D61 => P66 | D62 => P67 | D63 => P68 end
  | D6 => match b with D0 => P6 | D1 => P7 | D2 => P8 | D3 => P9 | D4 => P10 | D5 => P11 | D6 => P12 | D7 => P13 | D8 => P14 | D9 => P15 | D10 => P16 | D11 => P17 | D12 => P18 | D13 => P19 | D14 => P20 | D15 => P21 | D16 => P22 | D17 => P23 | D18 => P24 | D19 => P25 | D20 => P26 | D21 => P27 | D22 => P28 | D23 => P29 | D24 => P30 | D25 => P31 | D26 => P32 | D27 => P33 | D28 => P34 | D29 => P35 | D30 => P36 | D31 => P37 | D32 => P38 | D33 => P39 | D34 => P40 | D35 => P41 | D36 => P42 | D37 => P43 | D38 => P44 | D39 => P45 | D40 => P46 | D41 => P47 | D42 => P48 | D43 => P49 | D44 => P50 | D45 => P51 | D46 => P52 | D47 => P53 | D48 => P54 | D49 => P55 | D50 => P56 | D51 => P57 | D52 => P58 | D53 => P59 | D54 => P60 | D55 => P61 | D56 => P62 | D57 => P63 | D58 => P64 | D59 => P65 | D60 => P66 | D61 => P67 | D62 => P68 | D63 => P69 end
  | D7 => match b with D0 => P7 | D1 => P8 | D2 => P9 | D3 => P10 | D4 => P11 | D5 => P12 | D6 => P13 | D7 => P14 | D8 => P15 | D9 => P16 | D10 => P17 | D11 => P18 | D12 => P19 | D13 => P20 | D14 => P21 | D15 => P22 | D16 => P23 | D17 => P24 | D18 => P25 | D19 => P26 | D20 => P27 | D21 => P28 | D22 => P29 | D23 => P30 | D24 => P31 | D25 => P32 | D26 => P33 | D27 => P34 | D28 => P35 | D29 => P36 | D30 => P37 | D31 => P38 | D32 => P39 | D33 => P40 | D34 => P41 | D35 => P42 | D36 => P43 | D37 => P44 | D38 => P45 | D39 => P46 | D40 => P47 | D41 => P48 | D42 => P49 | D43 => P50 | D44 => P51 | D45 => P52 | D46 => P53 | D47 => P54 | D48 => P55 | D49 => P56 | D50 => P57 | D51 => P58 | D52 => P59 | D53 => P60 | D54 => P61 | D55 => P62 | D56 => P63 | D57 => P64 | D58 => P65 | D59 => P66 | D60 => P67 | D61 => P68 | D62 => P69 | D63 => P70 end
  | D8 => match b with D0 => P8 | D1 => P9 | D2 => P10 | D3 => P11 | D4 => P12 | D5 => P13 | D6 => P14 | D7 => P15 | D8 => P16 | D9 => P17 | D10 => P18 | D11 => P19 | D12 => P20 | D13 => P21 | D14 => P22 | D15 => P23 | D16 => P24 | D17 => P25 | D18 => P26 | D19 => P27 | D20 => P28 | D21 => P29 | D22 => P30 | D23 => P31 | D24 => P32 | D25 => P33 | D26 => P34 | D27 => P35 | D28 => P36 | D29 => P37 | D30 => P38 | D31 => P39 | D32 => P40 | D33 => P41 | D34 => P42 | D35 => P43 | D36 => P44 | D37 => P45 | D38 => P46 | D39 => P47 | D40 => P48 | D41 => P49 | D42 => P50 | D43 => P51 | D44 => P52 | D45 => P53 | D46 => P54 | D47 => P55 | D48 => P56 | D49 => P57 | D50 => P58 | D51 => P59 | D52 => P60 | D53 => P61 | D54 => P62 | D55 => P63 | D56 => P64 | D57 => P65 | D58 => P66 | D59 => P67 | D60 => P68 | D61 => P69 | D62 => P70 | D63 => P71 end
  | D9 => match b with D0 => P9 | D1 => P10 | D2 => P11 | D3 => P12 | D4 => P13 | D5 => P14 | D6 => P15 | D7 => P16 | D8 => P17 | D9 => P18 | D10 => P19 | D11 => P20 | D12 => P21 | D13 => P22 | D14 => P23 | D15 => P24 | D16 => P25 | D17 => P26 | D18 => P27 | D19 => P28 | D20 => P29 | D21 => P30 | D22 => P31 | D23 => P32 | D24 => P33 | D25 => P34 | D26 => P35 | D27 => P36 | D28 => P37 | D29 => P38 | D30 => P39 | D31 => P40 | D32 => P41 | D33 => P42 | D34 => P43 | D35 => P44 | D36 => P45 | D37 => P46 | D38 => P47 | D39 => P48 | D40 => P49 | D41 => P50 | D42 => P51 | D43 => P52 | D44 => P53 | D45 => P54 | D46 => P55 | D47 => P56 | D48 => P57 | D49 => P58 | D50 => P59 | D51 => P60 | D52 => P61 | D53 => P62 | D54 => P63 | D55 => P64 | D56 => P65 | D57 => P66 | D58 => P67 | D59 => P68 | D60 => P69 | D61 => P70 | D62 => P71 | D63 => P72 end
  | D10 => match b with D0 => P10 | D1 => P11 | D2 => P12 | D3 => P13 | D4 => P14 | D5 => P15 | D6 => P16 | D7 => P17 | D8 => P18 | D9 => P19 | D10 => P20 | D11 => P21 | D12 => P22 | D13 => P23 | D14 => P24 | D15 => P25 | D16 => P26 | D17 => P27 | D18 => P28 | D19 => P29 | D20 => P30 | D21 => P31 | D22 => P32 | D23 => P33 | D24 => P34 | D25 => P35 | D26 => P36 | D27 => P37 | D28 => P38 | D29 => P39 | D30 => P40 | D31 => P41 | D32 => P42 | D33 => P43 | D34 => P44 | D35 => P45 | D36 => P46 | D37 => P47 | D38 => P48 | D39 => P49 | D40 => P50 | D41 => P51 | D42 => P52 | D43 => P53 | D44 => P54 | D45 => P55 | D46 => P56 | D47 => P57 | D48 => P58 | D49 => P59 | D50 => P60 | D51 => P61 | D52 => P62 | D53 => P63 | D54 => P64 | D55 => P65 | D56 => P66 | D57 => P67 | D58 => P68 | D59 => P69 | D60 => P70 | D61 => P71 | D62 => P72 | D63 => P73 end
  | D11 => match b with D0 => P11 | D1 => P12 | D2 => P13 | D3 => P14 | D4 => P15 | D5 => P16 | D6 => P17 | D7 => P18 | D8 => P19 | D9 => P20 | D10 => P21 | D11 => P22 | D12 => P23 | D13 => P24 | D14 => P25 | D15 => P26 | D16 => P27 | D17 => P28 | D18 => P29 | D19 => P30 | D20 => P31 | D21 => P32 | D22 => P33 | D23 => P34 | D24 => P35 | D25 => P36 | D26 => P37 | D27 => P38 | D28 => P39 | D29 => P40 | D30 => P41 | D31 => P42 | D32 => P43 | D33 => P44 | D34 => P45 | D35 => P46 | D36 => P47 | D37 => P48 | D38 => P49 | D39 => P50 | D40 => P51 | D41 => P52 | D42 => P53 | D43 => P54 | D44 => P55 | D45 => P56 | D46 => P57 | D47 => P58 | D48 => P59 | D49 => P60 | D50 => P61 | D51 => P62 | D52 => P63 | D53 => P64 | D54 => P65 | D55 => P66 | D56 => P67 | D57 => P68 | D58 => P69 | D59 => P70 | D60 => P71 | D61 => P72 | D62 => P73 | D63 => P74 end
  | D12 => match b with D0 => P12 | D1 => P13 | D2 => P14 | D3 => P15 | D4 => P16 | D5 => P17 | D6 => P18 | D7 => P19 | D8 => P20 | D9 => P21 | D10 => P22 | D11 => P23 | D12 => P24 | D13 => P25 | D14 => P26 | D15 => P27 | D16 => P28 | D17 => P29 | D18 => P30 | D19 => P31 | D20 => P32 | D21 => P33 | D22 => P34 | D23 => P35 | D24 => P36 | D25 => P37 | D26 => P38 | D27 => P39 | D28 => P40 | D29 => P41 | D30 => P42 | D31 => P43 | D32 => P44 | D33 => P45 | D34 => P46 | D35 => P47 | D36 => P48 | D37 => P49 | D38 => P50 | D39 => P51 | D40 => P52 | D41 => P53 | D42 => P54 | D43 => P55 | D44 => P56 | D45 => P57 | D46 => P58 | D47 => P59 | D48 => P60 | D49 => P61 | D50 => P62 | D51 => P63 | D52 => P64 | D53 => P65 | D54 => P66 | D55 => P67 | D56 => P68 | D57 => P69 | D58 => P70 | D59 => P71 | D60 => P72 | D61 => P73 | D62 => P74 | D63 => P75 end
  | D13 => match b with D0 => P13 | D1 => P14 | D2 => P15 | D3 => P16 | D4 => P17 | D5 => P18 | D6 => P19 | D7 => P20 | D8 => P21 | D9 => P22 | D10 => P23 | D11 => P24 | D12 => P25 | D13 => P26 | D14 => P27 | D15 => P28 | D16 => P29 | D17 => P30 | D18 => P31 | D19 => P32 | D20 => P33 | D21 => P34 | D22 => P35 | D23 => P36 | D24 => P37 | D25 => P38 | D26 => P39 | D27 => P40 | D28 => P41 | D29 => P42 | D30 => P43 | D31 => P44 | D32 => P45 | D33 => P46 | D34 => P47 | D35 => P48 | D36 => P49 | D37 => P50 | D38 => P51 | D39 => P52 | D40 => P53 | D41 => P54 | D42 => P55 | D43 => P56 | D44 => P57 | D45 => P58 | D46 => P59 | D47 => P60 | D48 => P61 | D49 => P62 | D50 => P63 | D51 => P64 | D52 => P65 | D53 => P66 | D54 => P67 | D55 => P68 | D56 => P69 | D57 => P70 | D58 => P71 | D59 => P72 | D60 => P73 | D61 => P74 | D62 => P75 | D63 => P76 end
  | D14 => match b with D0 => P14 | D1 => P15 | D2 => P16 | D3 => P17 | D4 => P18 | D5 => P19 | D6 => P20 | D7 => P21 | D8 => P22 | D9 => P23 | D10 => P24 | D11 => P25 | D12 => P26 | D13 => P27 | D14 => P28 | D15 => P29 | D16 => P30 | D17 => P31 | D18 => P32 | D19 => P33 | D20 => P34 | D21 => P35 | D22 => P36 | D23 => P37 | D24 => P38 | D25 => P39 | D26 => P40 | D27 => P41 | D28 => P42 | D29 => P43 | D30 => P44 | D31 => P45 | D32 => P46 | D33 => P47 | D34 => P48 | D35 => P49 | D36 => P50 | D37 => P51 | D38 => P52 | D39 => P53 | D40 => P54 | D41 => P55 | D42 => P56 | D43 => P57 | D44 => P58 | D45 => P59 | D46 => P60 | D47 => P61 | D48 => P62 | D49 => P63 | D50 => P64 | D51 => P65 | D52 => P66 | D53 => P67 | D54 => P68 | D55 => P69 | D56 => P70 | D57 => P71 | D58 => P72 | D59 => P73 | D60 => P74 | D61 => P75 | D62 => P76 | D63 => P77 end
  | D15 => match b with D0 => P15 | D1 => P16 | D2 => P17 | D3 => P18 | D4 => P19 | D5 => P20 | D6 => P21 | D7 => P22 | D8 => P23 | D9 => P24 | D10 => P25 | D11 => P26 | D12 => P27 | D13 => P28 | D14 => P29 | D15 => P30 | D16 => P31 | D17 => P32 | D18 => P33 | D19 => P34 | D20 => P35 | D21 => P36 | D22 => P37 | D23 => P38 | D24 => P39 | D25 => P40 | D26 => P41 | D27 => P42 | D28 => P43 | D29 => P44 | D30 => P45 | D31 => P46 | D32 => P47 | D33 => P48 | D34 => P49 | D35 => P50 | D36 => P51 | D37 => P52 | D38 => P53 | D39 => P54 | D40 => P55 | D41 => P56 | D42 => P57 | D43 => P58 | D44 => P59 | D45 => P60 | D46 => P61 | D47 => P62 | D48 => P63 | D49 => P64 | D50 => P65 | D51 => P66 | D52 => P67 | D53 => P68 | D54 => P69 | D55 => P70 | D56 => P71 | D57 => P72 | D58 => P73 | D59 => P74 | D60 => P75 | D61 => P76 | D62 => P77 | D63 => P78 end
  | D16 => match b with D0 => P16 | D1 => P17 | D2 => P18 | D3 => P19 | D4 => P20 | D5 => P21 | D6 => P22 | D7 => P23 | D8 => P24 | D9 => P25 | D10 => P26 | D11 => P27 | D12 => P28 | D13 => P29 | D14 => P30 | D15 => P31 | D16 => P32 | D17 => P33 | D18 => P34 | D19 => P35 | D20 => P36 | D21 => P37 | D22 => P38 | D23 => P39 | D24 => P40 | D25 => P41 | D26 => P42 | D27 => P43 | D28 => P44 | D29 => P45 | D30 => P46 | D31 => P47 | D32 => P48 | D33 => P49 | D34 => P50 | D35 => P51 | D36 => P52 | D37 => P53 | D38 => P54 | D39 => P55 | D40 => P56 | D41 => P57 | D42 => P58 | D43 => P59 | D44 => P60 | D45 => P61 | D46 => P62 | D47 => P63 | D48 => P64 | D49 => P65 | D50 => P66 | D51 => P67 | D52 => P68 | D53 => P69 | D54 => P70 | D55 => P71 | D56 => P72 | D57 => P73 | D58 => P74 | D59 => P75 | D60 => P76 | D61 => P77 | D62 => P78 | D63 => P79 end
  | D17 => match b with D0 => P17 | D1 => P18 | D2 => P19 | D3 => P20 | D4 => P21 | D5 => P22 | D6 => P23 | D7 => P24 | D8 => P25 | D9 => P26 | D10 => P27 | D11 => P28 | D12 => P29 | D13 => P30 | D14 => P31 | D15 => P32 | D16 => P33 | D17 => P34 | D18 => P35 | D19 => P36 | D20 => P37 | D21 => P38 | D22 => P39 | D23 => P40 | D24 => P41 | D25 => P42 | D26 => P43 | D27 => P44 | D28 => P45 | D29 => P46 | D30 => P47 | D31 => P48 | D32 => P49 | D33 => P50 | D34 => P51 | D35 => P52 | D36 => P53 | D37 => P54 | D38 => P55 | D39 => P56 | D40 => P57 | D41 => P58 | D42 => P59 | D43 => P60 | D44 => P61 | D45 => P62 | D46 => P63 | D47 => P64 | D48 => P65 | D49 => P66 | D50 => P67 | D51 => P68 | D52 => P69 | D53 => P70 | D54 => P71 | D55 => P72 | D56 => P73 | D57 => P74 | D58 => P75 | D59 => P76 | D60 => P77 | D61 => P78 | D62 => P79 | D63 => P80 end
  | D18 => match b with D0 => P18 | D1 => P19 | D2 => P20 | D3 => P21 | D4 => P22 | D5 => P23 | D6 => P24 | D7 => P25 | D8 => P26 | D9 => P27 | D10 => P28 | D11 => P29 | D12 => P30 | D13 => P31 | D14 => P32 | D15 => P33 | D16 => P34 | D17 => P35 | D18 => P36 | D19 => P37 | D20 => P38 | D21 => P39 | D22 => P40 | D23 => P41 | D24 => P42 | D25 => P43 | D26 => P44 | D27 => P45 | D28 => P46 | D29 => P47 | D30 => P48 | D31 => P49 | D32 => P50 | D33 => P51 | D34 => P52 | D35 => P53 | D36 => P54 | D37 => P55 | D38 => P56 | D39 => P57 | D40 => P58 | D41 => P59 | D42 => P60 | D43 => P61 | D44 => P62 | D45 => P63 | D46 => P64 | D47 => P65 | D48 => P66 | D49 => P67 | D50 => P68 | D51 => P69 | D52 => P70 | D53 => P71 | D54 => P72 | D55 => P73 | D56 => P74 | D57 => P75 | D58 => P76 | D59 => P77 | D60 => P78 | D61 => P79 | D62 => P80 | D63 => P81 end
  | D19 => match b with D0 => P19 | D1 => P20 | D2 => P21 | D3 => P22 | D4 => P23 | D5 => P24 | D6 => P25 | D7 => P26 | D8 => P27 | D9 => P28 | D10 => P29 | D11 => P30 | D12 => P31 | D13 => P32 | D14 => P33 | D15 => P34 | D16 => P35 | D17 => P36 | D18 => P37 | D19 => P38 | D20 => P39 | D21 => P40 | D22 => P41 | D23 => P42 | D24 => P43 | D25 => P44 | D26 => P45 | D27 => P46 | D28 => P47 | D29 => P48 | D30 => P49 | D31 => P50 | D32 => P51 | D33 => P52 | D34 => P53 | D35 => P54 | D36 => P55 | D37 => P56 | D38 => P57 | D39 => P58 | D40 => P59 | D41 => P60 | D42 => P61 | D43 => P62 | D44 => P63 | D45 => P64 | D46 => P65 | D47 => P66 | D48 => P67 | D49 => P68 | D50 => P69 | D51 => P70 | D52 => P71 | D53 => P72 | D54 => P73 | D55 => P74 | D56 => P75 | D57 => P76 | D58 => P77 | D59 => P78 | D60 => P79 | D61 => P80 | D62 => P81 | D63 => P82 end
  | D20 => match b with D0 => P20 | D1 => P21 | D2 => P22 | D3 => P23 | D4 => P24 | D5 => P25 | D6 => P26 | D7 => P27 | D8 => P28 | D9 => P29 | D10 => P30 | D11 => P31 | D12 => P32 | D13 => P33 | D14 => P34 | D15 => P35 | D16 => P36 | D17 => P37 | D18 => P38 | D19 => P39 | D20 => P40 | D21 => P41 | D22 => P42 | D23 => P43 | D24 => P44 | D25 => P45 | D26 => P46 | D27 => P47 | D28 => P48 | D29 => P49 | D30 => P50 | D31 => P51 | D32 => P52 | D33 => P53 | D34 => P54 | D35 => P55 | D36 => P56 | D37 => P57 | D38 => P58 | D39 => P59 | D40 => P60 | D41 => P61 | D42 => P62 | D43 => P63 | D44 => P64 | D45 => P65 | D46 => P66 | D47 => P67 | D48 => P68 | D49 => P69 | D50 => P70 | D51 => P71 | D52 => P72 | D53 => P73 | D54 => P74 | D55 => P75 | D56 => P76 | D57 => P77 | D58 => P78 | D59 => P79 | D60 => P80 | D61 => P81 | D62 => P82 | D63 => P83 end
  | D21 => match b with D0 => P21 | D1 => P22 | D2 => P23 | D3 => P24 | D4 => P25 | D5 => P26 | D6 => P27 | D7 => P28 | D8 => P29 | D9 => P30 | D10 => P31 | D11 => P32 | D12 => P33 | D13 => P34 | D14 => P35 | D15 => P36 | D16 => P37 | D17 => P38 | D18 => P39 | D19 => P40 | D20 => P41 | D21 => P42 | D22 => P43 | D23 => P44 | D24 => P45 | D25 => P46 | D26 => P47 | D27 => P48 | D28 => P49 | D29 => P50 | D30 => P51 | D31 => P52 | D32 => P53 | D33 => P54 | D34 => P55 | D35 => P56 | D36 => P57 | D37 => P58 | D38 => P59 | D39 => P60 | D40 => P61 | D41 => P62 | D42 => P63 | D43 => P64 | D44 => P65 | D45 => P66 | D46 => P67 | D47 => P68 | D48 => P69 | D49 => P70 | D50 => P71 | D51 => P72 | D52 => P73 | D53 => P74 | D54 => P75 | D55 => P76 | D56 => P77 | D57 => P78 | D58 => P79 | D59 => P80 | D60 => P81 | D61 => P82 | D62 => P83 | D63 => P84 end
  | D22 => match b with D0 => P22 | D1 => P23 | D2 => P24 | D3 => P25 | D4 => P26 | D5 => P27 | D6 => P28 | D7 => P29 | D8 => P30 | D9 => P31 | D10 => P32 | D11 => P33 | D12 => P34 | D13 => P35 | D14 => P36 | D15 => P37 | D16 => P38 | D17 => P39 | D18 => P40 | D19 => P41 | D20 => P42 | D21 => P43 | D22 => P44 | D23 => P45 | D24 => P46 | D25 => P47 | D26 => P48 | D27 => P49 | D28 => P50 | D29 => P51 | D30 => P52 | D31 => P53 | D32 => P54 | D33 => P55 | D34 => P56 | D35 => P57 | D36 => P58 | D37 => P59 | D38 => P60 | D39 => P61 | D40 => P62 | D41 => P63 | D42 => P64 | D43 => P65 | D44 => P66 | D45 => P67 | D46 => P68 | D47 => P69 | D48 => P70 | D49 => P71 | D50 => P72 | D51 => P73 | D52 => P74 | D53 => P75 | D54 => P76 | D55 => P77 | D56 => P78 | D57 => P79 | D58 => P80 | D59 => P81 | D60 => P82 | D61 => P83 | D62 => P84 | D63 => P85 end
  | D23 => match b with D0 => P23 | D1 => P24 | D2 => P25 | D3 => P26 | D4 => P27 | D5 => P28 | D6 => P29 | D7 => P30 | D8 => P31 | D9 => P32 | D10 => P33 | D11 => P34 | D12 => P35 | D13 => P36 | D14 => P37 | D15 => P38 | D16 => P39 | D17 => P40 | D18 => P41 | D19 => P42 | D20 => P43 | D21 => P44 | D22 => P45 | D23 => P46 | D24 => P47 | D25 => P48 | D26 => P49 | D27 => P50 | D28 => P51 | D29 => P52 | D30 => P53 | D31 => P54 | D32 => P55 | D33 => P56 | D34 => P57 | D35 => P58 | D36 => P59 | D37 => P60 | D38 => P61 | D39 => P62 | D40 => P63 | D41 => P64 | D42 => P65 | D43 => P66 | D44 => P67 | D45 => P68 | D46 => P69 | D47 => P70 | D48 => P71 | D49 => P72 | D50 => P73 | D51 => P74 | D52 => P75 | D53 => P76 | D54 => P77 | D55 => P78 | D56 => P79 | D57 => P80 | D58 => P81 | D59 => P82 | D60 => P83 | D61 => P84 | D62 => P85 | D63 => P86 end
  | D24 => match b with D0 => P24 | D1 => P25 | D2 => P26 | D3 => P27 | D4 => P28 | D5 => P29 | D6 => P30 | D7 => P31 | D8 => P32 | D9 => P33 | D10 => P34 | D11 => P35 | D12 => P36 | D13 => P37 | D14 => P38 | D15 => P39 | D16 => P40 | D17 => P41 | D18 => P42 | D19 => P43 | D20 => P44 | D21 => P45 | D22 => P46 | D23 => P47 | D24 => P48 | D25 => P49 | D26 => P50 | D27 => P51 | D28 => P52 | D29 => P53 | D30 => P54 | D31 => P55 | D32 => P56 | D33 => P57 | D34 => P58 | D35 => P59 | D36 => P60 | D37 => P61 | D38 => P62 | D39 => P63 | D40 => P64 | D41 => P65 | D42 => P66 | D43 => P67 | D44 => P68 | D45 => P69 | D46 => P70 | D47 => P71 | D48 => P72 | D49 => P73 | D50 => P74 | D51 => P75 | D52 => P76 | D53 => P77 | D54 => P78 | D55 => P79 | D56 => P80 | D57 => P81 | D58 => P82 | D59 => P83 | D60 => P84 | D61 => P85 | D62 => P86 | D63 => P87 end
  | D25 => match b with D0 => P25 | D1 => P26 | D2 => P27 | D3 => P28 | D4 => P29 | D5 => P30 | D6 => P31 | D7 => P32 | D8 => P33 | D9 => P34 | D10 => P35 | D11 => P36 | D12 => P37 | D13 => P38 | D14 => P39 | D15 => P40 | D16 => P41 | D17 => P42 | D18 => P43 | D19 => P44 | D20 => P45 | D21 => P46 | D22 => P47 | D23 => P48 | D24 => P49 | D25 => P50 | D26 => P51 | D27 => P52 | D28 => P53 | D29 => P54 | D30 => P55 | D31 => P56 | D32 => P57 | D33 => P58 | D34 => P59 | D35 => P60 | D36 => P61 | D37 => P62 | D38 => P63 | D39 => P64 | D40 => P65 | D41 => P66 | D42 => P67 | D43 => P68 | D44 => P69 | D45 => P70 | D46 => P71 | D47 => P72 | D48 => P73 | D49 => P74 | D50 => P75 | D51 => P76 | D52 => P77 | D53 => P78 | D54 => P79 | D55 => P80 | D56 => P81 | D57 => P82 | D58 => P83 | D59 => P84 | D60 => P85 | D61 => P86 | D62 => P87 | D63 => P88 end
  | D26 => match b with D0 => P26 | D1 => P27 | D2 => P28 | D3 => P29 | D4 => P30 | D5 => P31 | D6 => P32 | D7 => P33 | D8 => P34 | D9 => P35 | D10 => P36 | D11 => P37 | D12 => P38 | D13 => P39 | D14 => P40 | D15 => P41 | D16 => P42 | D17 => P43 | D18 => P44 | D19 => P45 | D20 => P46 | D21 => P47 | D22 => P48 | D23 => P49 | D24 => P50 | D25 => P51 | D26 => P52 | D27 => P53 | D28 => P54 | D29 => P55 | D30 => P56 | D31 => P57 | D32 => P58 | D33 => P59 | D34 => P60 | D35 => P61 | D36 => P62 | D37 => P63 | D38 => P64 | D39 => P65 | D40 => P66 | D41 => P67 | D42 => P68 | D43 => P69 | D44 => P70 | D45 => P71 | D46 => P72 | D47 => P73 | D48 => P74 | D49 => P75 | D50 => P76 | D51 => P77 | D52 => P78 | D53 => P79 | D54 => P80 | D55 => P81 | D56 => P82 | D57 => P83 | D58 => P84 | D59 => P85 | D60 => P86 | D61 => P87 | D62 => P88 | D63 => P89 end
  | D27 => match b with D0 => P27 | D1 => P28 | D2 => P29 | D3 => P30 | D4 => P31 | D5 => P32 | D6 => P33 | D7 => P34 | D8 => P35 | D9 => P36 | D10 => P37 | D11 => P38 | D12 => P39 | D13 => P40 | D14 => P41 | D15 => P42 | D16 => P43 | D17 => P44 | D18 => P45 | D19 => P46 | D20 => P47 | D21 => P48 | D22 => P49 | D23 => P50 | D24 => P51 | D25 => P52 | D26 => P53 | D27 => P54 | D28 => P55 | D29 => P56 | D30 => P57 | D31 => P58 | D32 => P59 | D33 => P60 | D34 => P61 | D35 => P62 | D36 => P63 | D37 => P64 | D38 => P65 | D39 => P66 | D40 => P67 | D41 => P68 | D42 => P69 | D43 => P70 | D44 => P71 | D45 => P72 | D46 => P73 | D47 => P74 | D48 => P75 | D49 => P76 | D50 => P77 | D51 => P78 | D52 => P79 | D53 => P80 | D54 => P81 | D55 => P82 | D56 => P83 | D57 => P84 | D58 => P85 | D59 => P86 | D60 => P87 | D61 => P88 | D62 => P89 | D63 => P90 end
  | D28 => match b with D0 => P28 | D1 => P29 | D2 => P30 | D3 => P31 | D4 => P32 | D5 => P33 | D6 => P34 | D7 => P35 | D8 => P36 | D9 => P37 | D10 => P38 | D11 => P39 | D12 => P40 | D13 => P41 | D14 => P42 | D15 => P43 | D16 => P44 | D17 => P45 | D18 => P46 | D19 => P47 | D20 => P48 | D21 => P49 | D22 => P50 | D23 => P51 | D24 => P52 | D25 => P53 | D26 => P54 | D27 => P55 | D28 => P56 | D29 => P57 | D30 => P58 | D31 => P59 | D32 => P60 | D33 => P61 | D34 => P62 | D35 => P63 | D36 => P64 | D37 => P65 | D38 => P66 | D39 => P67 | D40 => P68 | D41 => P69 | D42 => P70 | D43 => P71 | D44 => P72 | D45 => P73 | D46 => P74 | D47 => P75 | D48 => P76 | D49 => P77 | D50 => P78 | D51 => P79 | D52 => P80 | D53 => P81 | D54 => P82 | D55 => P83 | D56 => P84 | D57 => P85 | D58 => P86 | D59 => P87 | D60 => P88 | D61 => P89 | D62 => P90 | D63 => P91 end
  | D29 => match b with D0 => P29 | D1 => P30 | D2 => P31 | D3 => P32 | D4 => P33 | D5 => P34 | D6 => P35 | D7 => P36 | D8 => P37 | D9 => P38 | D10 => P39 | D11 => P40 | D12 => P41 | D13 => P42 | D14 => P43 | D15 => P44 | D16 => P45 | D17 => P46 | D18 => P47 | D19 => P48 | D20 => P49 | D21 => P50 | D22 => P51 | D23 => P52 | D24 => P53 | D25 => P54 | D26 => P55 | D27 => P56 | D28 => P57 | D29 => P58 | D30 => P59 | D31 => P60 | D32 => P61 | D33 => P62 | D34 => P63 | D35 => P64 | D36 => P65 | D37 => P66 | D38 => P67 | D39 => P68 | D40 => P69 | D41 => P70 | D42 => P71 | D43 => P72 | D44 => P73 | D45 => P74 | D46 => P75 | D47 => P76 | D48 => P77 | D49 => P78 | D50 => P79 | D51 => P80 | D52 => P81 | D53 => P82 | D54 => P83 | D55 => P84 | D56 => P85 | D57 => P86 | D58 => P87 | D59 => P88 | D60 => P89 | D61 => P90 | D62 => P91 | D63 => P92 end
  | D30 => match b with D0 => P30 | D1 => P31 | D2 => P32 | D3 => P33 | D4 => P34 | D5 => P35 | D6 => P36 | D7 => P37 | D8 => P38 | D9 => P39 | D10 => P40 | D11 => P41 | D12 => P42 | D13 => P43 | D14 => P44 | D15 => P45 | D16 => P46 | D17 => P47 | D18 => P48 | D19 => P49 | D20 => P50 | D21 => P51 | D22 => P52 | D23 => P53 | D24 => P54 | D25 => P55 | D26 => P56 | D27 => P57 | D28 => P58 | D29 => P59 | D30 => P60 | D31 => P61 | D32 => P62 | D33 => P63 | D34 => P64 | D35 => P65 | D36 => P66 | D37 => P67 | D38 => P68 | D39 => P69 | D40 => P70 | D41 => P71 | D42 => P72 | D43 => P73 | D44 => P74 | D45 => P75 | D46 => P76 | D47 => P77 | D48 => P78 | D49 => P79 | D50 => P80 | D51 => P81 | D52 => P82 | D53 => P83 | D54 => P84 | D55 => P85 | D56 => P86 | D57 => P87 | D58 => P88 | D59 => P89 | D60 => P90 | D61 => P91 | D62 => P92 | D63 => P93 end
  | D31 => match b with D0 => P31 | D1 => P32 | D2 => P33 | D3 => P34 | D4 => P35 | D5 => P36 | D6 => P37 | D7 => P38 | D8 => P39 | D9 => P40 | D10 => P41 | D11 => P42 | D12 => P43 | D13 => P44 | D14 => P45 | D15 => P46 | D16 => P47 | D17 => P48 | D18 => P49 | D19 => P50 | D20 => P51 | D21 => P52 | D22 => P53 | D23 => P54 | D24 => P55 | D25 => P56 | D26 => P57 | D27 => P58 | D28 => P59 | D29 => P60 | D30 => P61 | D31 => P62 | D32 => P63 | D33 => P64 | D34 => P65 | D35 => P66 | D36 => P67 | D37 => P68 | D38 => P69 | D39 => P70 | D40 => P71 | D41 => P72 | D42 => P73 | D43 => P74 | D44 => P75 | D45 => P76 | D46 => P77 | D47 => P78 | D48 => P79 | D49 => P80 | D50 => P81 | D51 => P82 | D52 => P83 | D53 => P84 | D54 => P85 | D55 => P86 | D56 => P87 | D57 => P88 | D58 => P89 | D59 => P90 | D60 => P91 | D61 => P92 | D62 => P93 | D63 => P94 end
  | D32 => match b with D0 => P32 | D1 => P33 | D2 => P34 | D3 => P35 | D4 => P36 | D5 => P37 | D6 => P38 | D7 => P39 | D8 => P40 | D9 => P41 | D10 => P42 | D11 => P43 | D12 => P44 | D13 => P45 | D14 => P46 | D15 => P47 | D16 => P48 | D17 => P49 | D18 => P50 | D19 => P51 | D20 => P52 | D21 => P53 | D22 => P54 | D23 => P55 | D24 => P56 | D25 => P57 | D26 => P58 | D27 => P59 | D28 => P60 | D29 => P61 | D30 => P62 | D31 => P63 | D32 => P64 | D33 => P65 | D34 => P66 | D35 => P67 | D36 => P68 | D37 => P69 | D38 => P70 | D39 => P71 | D40 => P72 | D41 => P73 | D42 => P74 | D43 => P75 | D44 => P76 | D45 => P77 | D46 => P78 | D47 => P79 | D48 => P80 | D49 => P81 | D50 => P82 | D51 => P83 | D52 => P84 | D53 => P85 | D54 => P86 | D55 => P87 | D56 => P88 | D57 => P89 | D58 => P90 | D59 => P91 | D60 => P92 | D61 => P93 | D62 => P94 | D63 => P95 end
  | D33 => match b with D0 => P33 | D1 => P34 | D2 => P35 | D3 => P36 | D4 => P37 | D5 => P38 | D6 => P39 | D7 => P40 | D8 => P41 | D9 => P42 | D10 => P43 | D11 => P44 | D12 => P45 | D13 => P46 | D14 => P47 | D15 => P48 | D16 => P49 | D17 => P50 | D18 => P51 | D19 => P52 | D20 => P53 | D21 => P54 | D22 => P55 | D23 => P56 | D24 => P57 | D25 => P58 | D26 => P59 | D27 => P60 | D28 => P61 | D29 => P62 | D30 => P63 | D31 => P64 | D32 => P65 | D33 => P66 | D34 => P67 | D35 => P68 | D36 => P69 | D37 => P70 | D38 => P71 | D39 => P72 | D40 => P73 | D41 => P74 | D42 => P75 | D43 => P76 | D44 => P77 | D45 => P78 | D46 => P79 | D47 => P80 | D48 => P81 | D49 => P82 | D50 => P83 | D51 => P84 | D52 => P85 | D53 => P86 | D54 => P87 | D55 => P88 | D56 => P89 | D57 => P90 | D58 => P91 | D59 => P92 | D60 => P93 | D61 => P94 | D62 => P95 | D63 => P96 end
  | D34 => match b with D0 => P34 | D1 => P35 | D2 => P36 | D3 => P37 | D4 => P38 | D5 => P39 | D6 => P40 | D7 => P41 | D8 => P42 | D9 => P43 | D10 => P44 | D11 => P45 | D12 => P46 | D13 => P47 | D14 => P48 | D15 => P49 | D16 => P50 | D17 => P51 | D18 => P52 | D19 => P53 | D20 => P54 | D21 => P55 | D22 => P56 | D23 => P57 | D24 => P58 | D25 => P59 | D26 => P60 | D27 => P61 | D28 => P62 | D29 => P63 | D30 => P64 | D31 => P65 | D32 => P66 | D33 => P67 | D34 => P68 | D35 => P69 | D36 => P70 | D37 => P71 | D38 => P72 | D39 => P73 | D40 => P74 | D41 => P75 | D42 => P76 | D43 => P77 | D44 => P78 | D45 => P79 | D46 => P80 | D47 => P81 | D48 => P82 | D49 => P83 | D50 => P84 | D51 => P85 | D52 => P86 | D53 => P87 | D54 => P88 | D55 => P89 | D56 => P90 | D57 => P91 | D58 => P92 | D59 => P93 | D60 => P94 | D61 => P95 | D62 => P96 | D63 => P97 end
  | D35 => match b with D0 => P35 | D1 => P36 | D2 => P37 | D3 => P38 | D4 => P39 | D5 => P40 | D6 => P41 | D7 => P42 | D8 => P43 | D9 => P44 | D10 => P45 | D11 => P46 | D12 => P47 | D13 => P48 | D14 => P49 | D15 => P50 | D16 => P51 | D17 => P52 | D18 => P53 | D19 => P54 | D20 => P55 | D21 => P56 | D22 => P57 | D23 => P58 | D24 => P59 | D25 => P60 | D26 => P61 | D27 => P62 | D28 => P63 | D29 => P64 | D30 => P65 | D31 => P66 | D32 => P67 | D33 => P68 | D34 => P69 | D35 => P70 | D36 => P71 | D37 => P72 | D38 => P73 | D39 => P74 | D40 => P75 | D41 => P76 | D42 => P77 | D43 => P78 | D44 => P79 | D45 => P80 | D46 => P81 | D47 => P82 | D48 => P83 | D49 => P84 | D50 => P85 | D51 => P86 | D52 => P87 | D53 => P88 | D54 => P89 | D55 => P90 | D56 => P91 | D57 => P92 | D58 => P93 | D59 => P94 | D60 => P95 | D61 => P96 | D62 => P97 | D63 => P98 end
  | D36 => match b with D0 => P36 | D1 => P37 | D2 => P38 | D3 => P39 | D4 => P40 | D5 => P41 | D6 => P42 | D7 => P43 | D8 => P44 | D9 => P45 | D10 => P46 | D11 => P47 | D12 => P48 | D13 => P49 | D14 => P50 | D15 => P51 | D16 => P52 | D17 => P53 | D18 => P54 | D19 => P55 | D20 => P56 | D21 => P57 | D22 => P58 | D23 => P59 | D24 => P60 | D25 => P61 | D26 => P62 | D27 => P63 | D28 => P64 | D29 => P65 | D30 => P66 | D31 => P67 | D32 => P68 | D33 => P69 | D34 => P70 | D35 => P71 | D36 => P72 | D37 => P73 | D38 => P74 | D39 => P75 | D40 => P76 | D41 => P77 | D42 => P78 | D43 => P79 | D44 => P80 | D45 => P81 | D46 => P82 | D47 => P83 | D48 => P84 | D49 => P85 | D50 => P86 | D51 => P87 | D52 => P88 | D53 => P89 | D54 => P90 | D55 => P91 | D56 => P92 | D57 => P93 | D58 => P94 | D59 => P95 | D60 => P96 | D61 => P97 | D62 => P98 | D63 => P99 end
  | D37 => match b with D0 => P37 | D1 => P38 | D2 => P39 | D3 => P40 | D4 => P41 | D5 => P42 | D6 => P43 | D7 => P44 | D8 => P45 | D9 => P46 | D10 => P47 | D11 => P48 | D12 => P49 | D13 => P50 | D14 => P51 | D15 => P52 | D16 => P53 | D17 => P54 | D18 => P55 | D19 => P56 | D20 => P57 | D21 => P58 | D22 => P59 | D23 => P60 | D24 => P61 | D25 => P62 | D26 => P63 | D27 => P64 | D28 => P65 | D29 => P66 | D30 => P67 | D31 => P68 | D32 => P69 | D33 => P70 | D34 => P71 | D35 => P72 | D36 => P73 | D37 => P74 | D38 => P75 | D39 => P76 | D40 => P77 | D41 => P78 | D42 => P79 | D43 => P80 | D44 => P81 | D45 => P82 | D46 => P83 | D47 => P84 | D48 => P85 | D49 => P86 | D50 => P87 | D51 => P88 | D52 => P89 | D53 => P90 | D54 => P91 | D55 => P92 | D56 => P93 | D57 => P94 | D58 => P95 | D59 => P96 | D60 => P97 | D61 => P98 | D62 => P99 | D63 => P100 end
  | D38 => match b with D0 => P38 | D1 => P39 | D2 => P40 | D3 => P41 | D4 => P42 | D5 => P43 | D6 => P44 | D7 => P45 | D8 => P46 | D9 => P47 | D10 => P48 | D11 => P49 | D12 => P50 | D13 => P51 | D14 => P52 | D15 => P53 | D16 => P54 | D17 => P55 | D18 => P56 | D19 => P57 | D20 => P58 | D21 => P59 | D22 => P60 | D23 => P61 | D24 => P62 | D25 => P63 | D26 => P64 | D27 => P65 | D28 => P66 | D29 => P67 | D30 => P68 | D31 => P69 | D32 => P70 | D33 => P71 | D34 => P72 | D35 => P73 | D36 => P74 | D37 => P75 | D38 => P76 | D39 => P77 | D40 => P78 | D41 => P79 | D42 => P80 | D43 => P81 | D44 => P82 | D45 => P83 | D46 => P84 | D47 => P85 | D48 => P86 | D49 => P87 | D50 => P88 | D51 => P89 | D52 => P90 | D53 => P91 | D54 => P92 | D55 => P93 | D56 => P94 | D57 => P95 | D58 => P96 | D59 => P97 | D60 => P98 | D61 => P99 | D62 => P100 | D63 => P101 end
  | D39 => match b with D0 => P39 | D1 => P40 | D2 => P41 | D3 => P42 | D4 => P43 | D5 => P44 | D6 => P45 | D7 => P46 | D8 => P47 | D9 => P48 | D10 => P49 | D11 => P50 | D12 => P51 | D13 => P52 | D14 => P53 | D15 => P54 | D16 => P55 | D17 => P56 | D18 => P57 | D19 => P58 | D20 => P59 | D21 => P60 | D22 => P61 | D23 => P62 | D24 => P63 | D25 => P64 | D26 => P65 | D27 => P66 | D28 => P67 | D29 => P68 | D30 => P69 | D31 => P70 | D32 => P71 | D33 => P72 | D34 => P73 | D35 => P74 | D36 => P75 | D37 => P76 | D38 => P77 | D39 => P78 | D40 => P79 | D41 => P80 | D42 => P81 | D43 => P82 | D44 => P83 | D45 => P84 | D46 => P85 | D47 => P86 | D48 => P87 | D49 => P88 | D50 => P89 | D51 => P90 | D52 => P91 | D53 => P92 | D54 => P93 | D55 => P94 | D56 => P95 | D57 => P96 | D58 => P97 | D59 => P98 | D60 => P99 | D61 => P100 | D62 => P101 | D63 => P102 end
  | D40 => match b with D0 => P40 | D1 => P41 | D2 => P42 | D3 => P43 | D4 => P44 | D5 => P45 | D6 => P46 | D7 => P47 | D8 => P48 | D9 => P49 | D10 => P50 | D11 => P51 | D12 => P52 | D13 => P53 | D14 => P54 | D15 => P55 | D16 => P56 | D17 => P57 | D18 => P58 | D19 => P59 | D20 => P60 | D21 => P61 | D22 => P62 | D23 => P63 | D24 => P64 | D25 => P65 | D26 => P66 | D27 => P67 | D28 => P68 | D29 => P69 | D30 => P70 | D31 => P71 | D32 => P72 | D33 => P73 | D34 => P74 | D35 => P75 | D36 => P76 | D37 => P77 | D38 => P78 | D39 => P79 | D40 => P80 | D41 => P81 | D42 => P82 | D43 => P83 | D44 => P84 | D45 => P85 | D46 => P86 | D47 => P87 | D48 => P88 | D49 => P89 | D50 => P90 | D51 => P91 | D52 => P92 | D53 => P93 | D54 => P94 | D55 => P95 | D56 => P96 | D57 => P97 | D58 => P98 | D59 => P99 | D60 => P100 | D61 => P101 | D62 => P102 | D63 => P103 end
  | D41 => match b with D0 => P41 | D1 => P42 | D2 => P43 | D3 => P44 | D4 => P45 | D5 => P46 | D6 => P47 | D7 => P48 | D8 => P49 | D9 => P50 | D10 => P51 | D11 => P52 | D12 => P53 | D13 => P54 | D14 => P55 | D15 => P56 | D16 => P57 | D17 => P58 | D18 => P59 | D19 => P60 | D20 => P61 | D21 => P62 | D22 => P63 | D23 => P64 | D24 => P65 | D25 => P66 | D26 => P67 | D27 => P68 | D28 => P69 | D29 => P70 | D30 => P71 | D31 => P72 | D32 => P73 | D33 => P74 | D34 => P75 | D35 => P76 | D36 => P77 | D37 => P78 | D38 => P79 | D39 => P80 | D40 => P81 | D41 => P82 | D42 => P83 | D43 => P84 | D44 => P85 | D45 => P86 | D46 => P87 | D47 => P88 | D48 => P89 | D49 => P90 | D50 => P91 | D51 => P92 | D52 => P93 | D53 => P94 | D54 => P95 | D55 => P96 | D56 => P97 | D57 => P98 | D58 => P99 | D59 => P100 | D60 => P101 | D61 => P102 | D62 => P103 | D63 => P104 end
  | D42 => match b with D0 => P42 | D1 => P43 | D2 => P44 | D3 => P45 | D4 => P46 | D5 => P47 | D6 => P48 | D7 => P49 | D8 => P50 | D9 => P51 | D10 => P52 | D11 => P53 | D12 => P54 | D13 => P55 | D14 => P56 | D15 => P57 | D16 => P58 | D17 => P59 | D18 => P60 | D19 => P61 | D20 => P62 | D21 => P63 | D22 => P64 | D23 => P65 | D24 => P66 | D25 => P67 | D26 => P68 | D27 => P69 | D28 => P70 | D29 => P71 | D30 => P72 | D31 => P73 | D32 => P74 | D33 => P75 | D34 => P76 | D35 => P77 | D36 => P78 | D37 => P79 | D38 => P80 | D39 => P81 | D40 => P82 | D41 => P83 | D42 => P84 | D43 => P85 | D44 => P86 | D45 => P87 | D46 => P88 | D47 => P89 | D48 => P90 | D49 => P91 | D50 => P92 | D51 => P93 | D52 => P94 | D53 => P95 | D54 => P96 | D55 => P97 | D56 => P98 | D57 => P99 | D58 => P100 | D59 => P101 | D60 => P102 | D61 => P103 | D62 => P104 | D63 => P105 end
  | D43 => match b with D0 => P43 | D1 => P44 | D2 => P45 | D3 => P46 | D4 => P47 | D5 => P48 | D6 => P49 | D7 => P50 | D8 => P51 | D9 => P52 | D10 => P53 | D11 => P54 | D12 => P55 | D13 => P56 | D14 => P57 | D15 => P58 | D16 => P59 | D17 => P60 | D18 => P61 | D19 => P62 | D20 => P63 | D21 => P64 | D22 => P65 | D23 => P66 | D24 => P67 | D25 => P68 | D26 => P69 | D27 => P70 | D28 => P71 | D29 => P72 | D30 => P73 | D31 => P74 | D32 => P75 | D33 => P76 | D34 => P77 | D35 => P78 | D36 => P79 | D37 => P80 | D38 => P81 | D39 => P82 | D40 => P83 | D41 => P84 | D42 => P85 | D43 => P86 | D44 => P87 | D45 => P88 | D46 => P89 | D47 => P90 | D48 => P91 | D49 => P92 | D50 => P93 | D51 => P94 | D52 => P95 | D53 => P96 | D54 => P97 | D55 => P98 | D56 => P99 | D57 => P100 | D58 => P101 | D59 => P102 | D60 => P103 | D61 => P104 | D62 => P105 | D63 => P106 end
  | D44 => match b with D0 => P44 | D1 => P45 | D2 => P46 | D3 => P47 | D4 => P48 | D5 => P49 | D6 => P50 | D7 => P51 | D8 => P52 | D9 => P53 | D10 => P54 | D11 => P55 | D12 => P56 | D13 => P57 | D14 => P58 | D15 => P59 | D16 => P60 | D17 => P61 | D18 => P62 | D19 => P63 | D20 => P64 | D21 => P65 | D22 => P66 | D23 => P67 | D24 => P68 | D25 => P69 | D26 => P70 | D27 => P71 | D28 => P72 | D29 => P73 | D30 => P74 | D31 => P75 | D32 => P76 | D33 => P77 | D34 => P78 | D35 => P79 | D36 => P80 | D37 => P81 | D38 => P82 | D39 => P83 | D40 => P84 | D41 => P85 | D42 => P86 | D43 => P87 | D44 => P88 | D45 => P89 | D46 => P90 | D47 => P91 | D48 => P92 | D49 => P93 | D50 => P94 | D51 => P95 | D52 => P96 | D53 => P97 | D54 => P98 | D55 => P99 | D56 => P100 | D57 => P101 | D58 => P102 | D59 => P103 | D60 => P104 | D61 => P105 | D62 => P106 | D63 => P107 end
  | D45 => match b with D0 => P45 | D1 => P46 | D2 => P47 | D3 => P48 | D4 => P49 | D5 => P50 | D6 => P51 | D7 => P52 | D8 => P53 | D9 => P54 | D10 => P55 | D11 => P56 | D12 => P57 | D13 => P58 | D14 => P59 | D15 => P60 | D16 => P61 | D17 => P62 | D18 => P63 | D19 => P64 | D20 => P65 | D21 => P66 | D22 => P67 | D23 => P68 | D24 => P69 | D25 => P70 | D26 => P71 | D27 => P72 | D28 => P73 | D29 => P74 | D30 => P75 | D31 => P76 | D32 => P77 | D33 => P78 | D34 => P79 | D35 => P80 | D36 => P81 | D37 => P82 | D38 => P83 | D39 => P84 | D40 => P85 | D41 => P86 | D42 => P87 | D43 => P88 | D44 => P89 | D45 => P90 | D46 => P91 | D47 => P92 | D48 => P93 | D49 => P94 | D50 => P95 | D51 => P96 | D52 => P97 | D53 => P98 | D54 => P99 | D55 => P100 | D56 => P101 | D57 => P102 | D58 => P103 | D59 => P104 | D60 => P105 | D61 => P106 | D62 => P107 | D63 => P108 end
  | D46 => match b with D0 => P46 | D1 => P47 | D2 => P48 | D3 => P49 | D4 => P50 | D5 => P51 | D6 => P52 | D7 => P53 | D8 => P54 | D9 => P55 | D10 => P56 | D11 => P57 | D12 => P58 | D13 => P59 | D14 => P60 | D15 => P61 | D16 => P62 | D17 => P63 | D18 => P64 | D19 => P65 | D20 => P66 | D21 => P67 | D22 => P68 | D23 => P69 | D24 => P70 | D25 => P71 | D26 => P72 | D27 => P73 | D28 => P74 | D29 => P75 | D30 => P76 | D31 => P77 | D32 => P78 | D33 => P79 | D34 => P80 | D35 => P81 | D36 => P82 | D37 => P83 | D38 => P84 | D39 => P85 | D40 => P86 | D41 => P87 | D42 => P88 | D43 => P89 | D44 => P90 | D45 => P91 | D46 => P92 | D47 => P93 | D48 => P94 | D49 => P95 | D50 => P96 | D51 => P97 | D52 => P98 | D53 => P99 | D54 => P100 | D55 => P101 | D56 => P102 | D57 => P103 | D58 => P104 | D59 => P105 | D60 => P106 | D61 => P107 | D62 => P108 | D63 => P109 end
  | D47 => match b with D0 => P47 | D1 => P48 | D2 => P49 | D3 => P50 | D4 => P51 | D5 => P52 | D6 => P53 | D7 => P54 | D8 => P55 | D9 => P56 | D10 => P57 | D11 => P58 | D12 => P59 | D13 => P60 | D14 => P61 | D15 => P62 | D16 => P63 | D17 => P64 | D18 => P65 | D19 => P66 | D20 => P67 | D21 => P68 | D22 => P69 | D23 => P70 | D24 => P71 | D25 => P72 | D26 => P73 | D27 => P74 | D28 => P75 | D29 => P76 | D30 => P77 | D31 => P78 | D32 => P79 | D33 => P80 | D34 => P81 | D35 => P82 | D36 => P83 | D37 => P84 | D38 => P85 | D39 => P86 | D40 => P87 | D41 => P88 | D42 => P89 | D43 => P90 | D44 => P91 | D45 => P92 | D46 => P93 | D47 => P94 | D48 => P95 | D49 => P96 | D50 => P97 | D51 => P98 | D52 => P99 | D53 => P100 | D54 => P101 | D55 => P102 | D56 => P103 | D57 => P104 | D58 => P105 | D59 => P106 | D60 => P107 | D61 => P108 | D62 => P109 | D63 => P110 end
  | D48 => match b with D0 => P48 | D1 => P49 | D2 => P50 | D3 => P51 | D4 => P52 | D5 => P53 | D6 => P54 | D7 => P55 | D8 => P56 | D9 => P57 | D10 => P58 | D11 => P59 | D12 => P60 | D13 => P61 | D14 => P62 | D15 => P63 | D16 => P64 | D17 => P65 | D18 => P66 | D19 => P67 | D20 => P68 | D21 => P69 | D22 => P70 | D23 => P71 | D24 => P72 | D25 => P73 | D26 => P74 | D27 => P75 | D28 => P76 | D29 => P77 | D30 => P78 | D31 => P79 | D32 => P80 | D33 => P81 | D34 => P82 | D35 => P83 | D36 => P84 | D37 => P85 | D38 => P86 | D39 => P87 | D40 => P88 | D41 => P89 | D42 => P90 | D43 => P91 | D44 => P92 | D45 => P93 | D46 => P94 | D47 => P95 | D48 => P96 | D49 => P97 | D50 => P98 | D51 => P99 | D52 => P100 | D53 => P101 | D54 => P102 | D55 => P103 | D56 => P104 | D57 => P105 | D58 => P106 | D59 => P107 | D60 => P108 | D61 => P109 | D62 => P110 | D63 => P111 end
  | D49 => match b with D0 => P49 | D1 => P50 | D2 => P51 | D3 => P52 | D4 => P53 | D5 => P54 | D6 => P55 | D7 => P56 | D8 => P57 | D9 => P58 | D10 => P59 | D11 => P60 | D12 => P61 | D13 => P62 | D14 => P63 | D15 => P64 | D16 => P65 | D17 => P66 | D18 => P67 | D19 => P68 | D20 => P69 | D21 => P70 | D22 => P71 | D23 => P72 | D24 => P73 | D25 => P74 | D26 => P75 | D27 => P76 | D28 => P77 | D29 => P78 | D30 => P79 | D31 => P80 | D32 => P81 | D33 => P82 | D34 => P83 | D35 => P84 | D36 => P85 | D37 => P86 | D38 => P87 | D39 => P88 | D40 => P89 | D41 => P90 | D42 => P91 | D43 => P92 | D44 => P93 | D45 => P94 | D46 => P95 | D47 => P96 | D48 => P97 | D49 => P98 | D50 => P99 | D51 => P100 | D52 => P101 | D53 => P102 | D54 => P103 | D55 => P104 | D56 => P105 | D57 => P106 | D58 => P107 | D59 => P108 | D60 => P109 | D61 => P110 | D62 => P111 | D63 => P112 end
  | D50 => match b with D0 => P50 | D1 => P51 | D2 => P52 | D3 => P53 | D4 => P54 | D5 => P55 | D6 => P56 | D7 => P57 | D8 => P58 | D9 => P59 | D10 => P60 | D11 => P61 | D12 => P62 | D13 => P63 | D14 => P64 | D15 => P65 | D16 => P66 | D17 => P67 | D18 => P68 | D19 => P69 | D20 => P70 | D21 => P71 | D22 => P72 | D23 => P73 | D24 => P74 | D25 => P75 | D26 => P76 | D27 => P77 | D28 => P78 | D29 => P79 | D30 => P80 | D31 => P81 | D32 => P82 | D33 => P83 | D34 => P84 | D35 => P85 | D36 => P86 | D37 => P87 | D38 => P88 | D39 => P89 | D40 => P90 | D41 => P91 | D42 => P92 | D43 => P93 | D44 => P94 | D45 => P95 | D46 => P96 | D47 => P97 | D48 => P98 | D49 => P99 | D50 => P100 | D51 => P101 | D52 => P102 | D53 => P103 | D54 => P104 | D55 => P105 | D56 => P106 | D57 => P107 | D58 => P108 | D59 => P109 | D60 => P110 | D61 => P111 | D62 => P112 | D63 => P113 end
  | D51 => match b with D0 => P51 | D1 => P52 | D2 => P53 | D3 => P54 | D4 => P55 | D5 => P56 | D6 => P57 | D7 => P58 | D8 => P59 | D9 => P60 | D10 => P61 | D11 => P62 | D12 => P63 | D13 => P64 | D14 => P65 | D15 => P66 | D16 => P67 | D17 => P68 | D18 => P69 | D19 => P70 | D20 => P71 | D21 => P72 | D22 => P73 | D23 => P74 | D24 => P75 | D25 => P76 | D26 => P77 | D27 => P78 | D28 => P79 | D29 => P80 | D30 => P81 | D31 => P82 | D32 => P83 | D33 => P84 | D34 => P85 | D35 => P86 | D36 => P87 | D37 => P88 | D38 => P89 | D39 => P90 | D40 => P91 | D41 => P92 | D42 => P93 | D43 => P94 | D44 => P95 | D45 => P96 | D46 => P97 | D47 => P98 | D48 => P99 | D49 => P100 | D50 => P101 | D51 => P102 | D52 => P103 | D53 => P104 | D54 => P105 | D55 => P106 | D56 => P107 | D57 => P108 | D58 => P109 | D59 => P110 | D60 => P111 | D61 => P112 | D62 => P113 | D63 => P114 end
  | D52 => match b with D0 => P52 | D1 => P53 | D2 => P54 | D3 => P55 | D4 => P56 | D5 => P57 | D6 => P58 | D7 => P59 | D8 => P60 | D9 => P61 | D10 => P62 | D11 => P63 | D12 => P64 | D13 => P65 | D14 => P66 | D15 => P67 | D16 => P68 | D17 => P69 | D18 => P70 | D19 => P71 | D20 => P72 | D21 => P73 | D22 => P74 | D23 => P75 | D24 => P76 | D25 => P77 | D26 => P78 | D27 => P79 | D28 => P80 | D29 => P81 | D30 => P82 | D31 => P83 | D32 => P84 | D33 => P85 | D34 => P86 | D35 => P87 | D36 => P88 | D37 => P89 | D38 => P90 | D39 => P91 | D40 => P92 | D41 => P93 | D42 => P94 | D43 => P95 | D44 => P96 | D45 => P97 | D46 => P98 | D47 => P99 | D48 => P100 | D49 => P101 | D50 => P102 | D51 => P103 | D52 => P104 | D53 => P105 | D54 => P106 | D55 => P107 | D56 => P108 | D57 => P109 | D58 => P110 | D59 => P111 | D60 => P112 | D61 => P113 | D62 => P114 | D63 => P115 end
  | D53 => match b with D0 => P53 | D1 => P54 | D2 => P55 | D3 => P56 | D4 => P57 | D5 => P58 | D6 => P59 | D7 => P60 | D8 => P61 | D9 => P62 | D10 => P63 | D11 => P64 | D12 => P65 | D13 => P66 | D14 => P67 | D15 => P68 | D16 => P69 | D17 => P70 | D18 => P71 | D19 => P72 | D20 => P73 | D21 => P74 | D22 => P75 | D23 => P76 | D24 => P77 | D25 => P78 | D26 => P79 | D27 => P80 | D28 => P81 | D29 => P82 | D30 => P83 | D31 => P84 | D32 => P85 | D33 => P86 | D34 => P87 | D35 => P88 | D36 => P89 | D37 => P90 | D38 => P91 | D39 => P92 | D40 => P93 | D41 => P94 | D42 => P95 | D43 => P96 | D44 => P97 | D45 => P98 | D46 => P99 | D47 => P100 | D48 => P101 | D49 => P102 | D50 => P103 | D51 => P104 | D52 => P105 | D53 => P106 | D54 => P107 | D55 => P108 | D56 => P109 | D57 => P110 | D58 => P111 | D59 => P112 | D60 => P113 | D61 => P114 | D62 => P115 | D63 => P116 end
  | D54 => match b with D0 => P54 | D1 => P55 | D2 => P56 | D3 => P57 | D4 => P58 | D5 => P59 | D6 => P60 | D7 => P61 | D8 => P62 | D9 => P63 | D10 => P64 | D11 => P65 | D12 => P66 | D13 => P67 | D14 => P68 | D15 => P69 | D16 => P70 | D17 => P71 | D18 => P72 | D19 => P73 | D20 => P74 | D21 => P75 | D22 => P76 | D23 => P77 | D24 => P78 | D25 => P79 | D26 => P80 | D27 => P81 | D28 => P82 | D29 => P83 | D30 => P84 | D31 => P85 | D32 => P86 | D33 => P87 | D34 => P88 | D35 => P89 | D36 => P90 | D37 => P91 | D38 => P92 | D39 => P93 | D40 => P94 | D41 => P95 | D42 => P96 | D43 => P97 | D44 => P98 | D45 => P99 | D46 => P100 | D47 => P101 | D48 => P102 | D49 => P103 | D50 => P104 | D51 => P105 | D52 => P106 | D53 => P107 | D54 => P108 | D55 => P109 | D56 => P110 | D57 => P111 | D58 => P112 | D59 => P113 | D60 => P114 | D61 => P115 | D62 => P116 | D63 => P117 end
  | D55 => match b with D0 => P55 | D1 => P56 | D2 => P57 | D3 => P58 | D4 => P59 | D5 => P60 | D6 => P61 | D7 => P62 | D8 => P63 | D9 => P64 | D10 => P65 | D11 => P66 | D12 => P67 | D13 => P68 | D14 => P69 | D15 => P70 | D16 => P71 | D17 => P72 | D18 => P73 | D19 => P74 | D20 => P75 | D21 => P76 | D22 => P77 | D23 => P78 | D24 => P79 | D25 => P80 | D26 => P81 | D27 => P82 | D28 => P83 | D29 => P84 | D30 => P85 | D31 => P86 | D32 => P87 | D33 => P88 | D34 => P89 | D35 => P90 | D36 => P91 | D37 => P92 | D38 => P93 | D39 => P94 | D40 => P95 | D41 => P96 | D42 => P97 | D43 => P98 | D44 => P99 | D45 => P100 | D46 => P101 | D47 => P102 | D48 => P103 | D49 => P104 | D50 => P105 | D51 => P106 | D52 => P107 | D53 => P108 | D54 => P109 | D55 => P110 | D56 => P111 | D57 => P112 | D58 => P113 | D59 => P114 | D60 => P115 | D61 => P116 | D62 => P117 | D63 => P118 end
  | D56 => match b with D0 => P56 | D1 => P57 | D2 => P58 | D3 => P59 | D4 => P60 | D5 => P61 | D6 => P62 | D7 => P63 | D8 => P64 | D9 => P65 | D10 => P66 | D11 => P67 | D12 => P68 | D13 => P69 | D14 => P70 | D15 => P71 | D16 => P72 | D17 => P73 | D18 => P74 | D19 => P75 | D20 => P76 | D21 => P77 | D22 => P78 | D23 => P79 | D24 => P80 | D25 => P81 | D26 => P82 | D27 => P83 | D28 => P84 | D29 => P85 | D30 => P86 | D31 => P87 | D32 => P88 | D33 => P89 | D34 => P90 | D35 => P91 | D36 => P92 | D37 => P93 | D38 => P94 | D39 => P95 | D40 => P96 | D41 => P97 | D42 => P98 | D43 => P99 | D44 => P100 | D45 => P101 | D46 => P102 | D47 => P103 | D48 => P104 | D49 => P105 | D50 => P106 | D51 => P107 | D52 => P108 | D53 => P109 | D54 => P110 | D55 => P111 | D56 => P112 | D57 => P113 | D58 => P114 | D59 => P115 | D60 => P116 | D61 => P117 | D62 => P118 | D63 => P119 end
  | D57 => match b with D0 => P57 | D1 => P58 | D2 => P59 | D3 => P60 | D4 => P61 | D5 => P62 | D6 => P63 | D7 => P64 | D8 => P65 | D9 => P66 | D10 => P67 | D11 => P68 | D12 => P69 | D13 => P70 | D14 => P71 | D15 => P72 | D16 => P73 | D17 => P74 | D18 => P75 | D19 => P76 | D20 => P77 | D21 => P78 | D22 => P79 | D23 => P80 | D24 => P81 | D25 => P82 | D26 => P83 | D27 => P84 | D28 => P85 | D29 => P86 | D30 => P87 | D31 => P88 | D32 => P89 | D33 => P90 | D34 => P91 | D35 => P92 | D36 => P93 | D37 => P94 | D38 => P95 | D39 => P96 | D40 => P97 | D41 => P98 | D42 => P99 | D43 => P100 | D44 => P101 | D45 => P102 | D46 => P103 | D47 => P104 | D48 => P105 | D49 => P106 | D50 => P107 | D51 => P108 | D52 => P109 | D53 => P110 | D54 => P111 | D55 => P112 | D56 => P113 | D57 => P114 | D58 => P115 | D59 => P116 | D60 => P117 | D61 => P118 | D62 => P119 | D63 => P120 end
  | D58 => match b with D0 => P58 | D1 => P59 | D2 => P60 | D3 => P61 | D4 => P62 | D5 => P63 | D6 => P64 | D7 => P65 | D8 => P66 | D9 => P67 | D10 => P68 | D11 => P69 | D12 => P70 | D13 => P71 | D14 => P72 | D15 => P73 | D16 => P74 | D17 => P75 | D18 => P76 | D19 => P77 | D20 => P78 | D21 => P79 | D22 => P80 | D23 => P81 | D24 => P82 | D25 => P83 | D26 => P84 | D27 => P85 | D28 => P86 | D29 => P87 | D30 => P88 | D31 => P89 | D32 => P90 | D33 => P91 | D34 => P92 | D35 => P93 | D36 => P94 | D37 => P95 | D38 => P96 | D39 => P97 | D40 => P98 | D41 => P99 | D42 => P100 | D43 => P101 | D44 => P102 | D45 => P103 | D46 => P104 | D47 => P105 | D48 => P106 | D49 => P107 | D50 => P108 | D51 => P109 | D52 => P110 | D53 => P111 | D54 => P112 | D55 => P113 | D56 => P114 | D57 => P115 | D58 => P116 | D59 => P117 | D60 => P118 | D61 => P119 | D62 => P120 | D63 => P121 end
  | D59 => match b with D0 => P59 | D1 => P60 | D2 => P61 | D3 => P62 | D4 => P63 | D5 => P64 | D6 => P65 | D7 => P66 | D8 => P67 | D9 => P68 | D10 => P69 | D11 => P70 | D12 => P71 | D13 => P72 | D14 => P73 | D15 => P74 | D16 => P75 | D17 => P76 | D18 => P77 | D19 => P78 | D20 => P79 | D21 => P80 | D22 => P81 | D23 => P82 | D24 => P83 | D25 => P84 | D26 => P85 | D27 => P86 | D28 => P87 | D29 => P88 | D30 => P89 | D31 => P90 | D32 => P91 | D33 => P92 | D34 => P93 | D35 => P94 | D36 => P95 | D37 => P96 | D38 => P97 | D39 => P98 | D40 => P99 | D41 => P100 | D42 => P101 | D43 => P102 | D44 => P103 | D45 => P104 | D46 => P105 | D47 => P106 | D48 => P107 | D49 => P108 | D50 => P109 | D51 => P110 | D52 => P111 | D53 => P112 | D54 => P113 | D55 => P114 | D56 => P115 | D57 => P116 | D58 => P117 | D59 => P118 | D60 => P119 | D61 => P120 | D62 => P121 | D63 => P122 end
  | D60 => match b with D0 => P60 | D1 => P61 | D2 => P62 | D3 => P63 | D4 => P64 | D5 => P65 | D6 => P66 | D7 => P67 | D8 => P68 | D9 => P69 | D10 => P70 | D11 => P71 | D12 => P72 | D13 => P73 | D14 => P74 | D15 => P75 | D16 => P76 | D17 => P77 | D18 => P78 | D19 => P79 | D20 => P80 | D21 => P81 | D22 => P82 | D23 => P83 | D24 => P84 | D25 => P85 | D26 => P86 | D27 => P87 | D28 => P88 | D29 => P89 | D30 => P90 | D31 => P91 | D32 => P92 | D33 => P93 | D34 => P94 | D35 => P95 | D36 => P96 | D37 => P97 | D38 => P98 | D39 => P99 | D40 => P100 | D41 => P101 | D42 => P102 | D43 => P103 | D44 => P104 | D45 => P105 | D46 => P106 | D47 => P107 | D48 => P108 | D49 => P109 | D50 => P110 | D51 => P111 | D52 => P112 | D53 => P113 | D54 => P114 | D55 => P115 | D56 => P116 | D57 => P117 | D58 => P118 | D59 => P119 | D60 => P120 | D61 => P121 | D62 => P122 | D63 => P123 end
  | D61 => match b with D0 => P61 | D1 => P62 | D2 => P63 | D3 => P64 | D4 => P65 | D5 => P66 | D6 => P67 | D7 => P68 | D8 => P69 | D9 => P70 | D10 => P71 | D11 => P72 | D12 => P73 | D13 => P74 | D14 => P75 | D15 => P76 | D16 => P77 | D17 => P78 | D18 => P79 | D19 => P80 | D20 => P81 | D21 => P82 | D22 => P83 | D23 => P84 | D24 => P85 | D25 => P86 | D26 => P87 | D27 => P88 | D28 => P89 | D29 => P90 | D30 => P91 | D31 => P92 | D32 => P93 | D33 => P94 | D34 => P95 | D35 => P96 | D36 => P97 | D37 => P98 | D38 => P99 | D39 => P100 | D40 => P101 | D41 => P102 | D42 => P103 | D43 => P104 | D44 => P105 | D45 => P106 | D46 => P107 | D47 => P108 | D48 => P109 | D49 => P110 | D50 => P111 | D51 => P112 | D52 => P113 | D53 => P114 | D54 => P115 | D55 => P116 | D56 => P117 | D57 => P118 | D58 => P119 | D59 => P120 | D60 => P121 | D61 => P122 | D62 => P123 | D63 => P124 end
  | D62 => match b with D0 => P62 | D1 => P63 | D2 => P64 | D3 => P65 | D4 => P66 | D5 => P67 | D6 => P68 | D7 => P69 | D8 => P70 | D9 => P71 | D10 => P72 | D11 => P73 | D12 => P74 | D13 => P75 | D14 => P76 | D15 => P77 | D16 => P78 | D17 => P79 | D18 => P80 | D19 => P81 | D20 => P82 | D21 => P83 | D22 => P84 | D23 => P85 | D24 => P86 | D25 => P87 | D26 => P88 | D27 => P89 | D28 => P90 | D29 => P91 | D30 => P92 | D31 => P93 | D32 => P94 | D33 => P95 | D34 => P96 | D35 => P97 | D36 => P98 | D37 => P99 | D38 => P100 | D39 => P101 | D40 => P102 | D41 => P103 | D42 => P104 | D43 => P105 | D44 => P106 | D45 => P107 | D46 => P108 | D47 => P109 | D48 => P110 | D49 => P111 | D50 => P112 | D51 => P113 | D52 => P114 | D53 => P115 | D54 => P116 | D55 => P117 | D56 => P118 | D57 => P119 | D58 => P120 | D59 => P121 | D60 => P122 | D61 => P123 | D62 => P124 | D63 => P125 end
  | D63 => match b with D0 => P63 | D1 => P64 | D2 => P65 | D3 => P66 | D4 => P67 | D5 => P68 | D6 => P69 | D7 => P70 | D8 => P71 | D9 => P72 | D10 => P73 | D11 => P74 | D12 => P75 | D13 => P76 | D14 => P77 | D15 => P78 | D16 => P79 | D17 => P80 | D18 => P81 | D19 => P82 | D20 => P83 | D21 => P84 | D22 => P85 | D23 => P86 | D24 => P87 | D25 => P88 | D26 => P89 | D27 => P90 | D28 => P91 | D29 => P92 | D30 => P93 | D31 => P94 | D32 => P95 | D33 => P96 | D34 => P97 | D35 => P98 | D36 => P99 | D37 => P100 | D38 => P101 | D39 => P102 | D40 => P103 | D41 => P104 | D42 => P105 | D43 => P106 | D44 => P107 | D45 => P108 | D46 => P109 | D47 => P110 | D48 => P111 | D49 => P112 | D50 => P113 | D51 => P114 | D52 => P115 | D53 => P116 | D54 => P117 | D55 => P118 | D56 => P119 | D57 => P120 | D58 => P121 | D59 => P122 | D60 => P123 | D61 => P124 | D62 => P125 | D63 => P126 end
  end.

Definition sub64b (br : bool) (a b : D64) : R128 :=
  if br then match a with
  | D0 => match b with D0 => P127 | D1 => P126 | D2 => P125 | D3 => P124 | D4 => P123 | D5 => P122 | D6 => P121 | D7 => P120 | D8 => P119 | D9 => P118 | D10 => P117 | D11 => P116 | D12 => P115 | D13 => P114 | D14 => P113 | D15 => P112 | D16 => P111 | D17 => P110 | D18 => P109 | D19 => P108 | D20 => P107 | D21 => P106 | D22 => P105 | D23 => P104 | D24 => P103 | D25 => P102 | D26 => P101 | D27 => P100 | D28 => P99 | D29 => P98 | D30 => P97 | D31 => P96 | D32 => P95 | D33 => P94 | D34 => P93 | D35 => P92 | D36 => P91 | D37 => P90 | D38 => P89 | D39 => P88 | D40 => P87 | D41 => P86 | D42 => P85 | D43 => P84 | D44 => P83 | D45 => P82 | D46 => P81 | D47 => P80 | D48 => P79 | D49 => P78 | D50 => P77 | D51 => P76 | D52 => P75 | D53 => P74 | D54 => P73 | D55 => P72 | D56 => P71 | D57 => P70 | D58 => P69 | D59 => P68 | D60 => P67 | D61 => P66 | D62 => P65 | D63 => P64 end
  | D1 => match b with D0 => P0 | D1 => P127 | D2 => P126 | D3 => P125 | D4 => P124 | D5 => P123 | D6 => P122 | D7 => P121 | D8 => P120 | D9 => P119 | D10 => P118 | D11 => P117 | D12 => P116 | D13 => P115 | D14 => P114 | D15 => P113 | D16 => P112 | D17 => P111 | D18 => P110 | D19 => P109 | D20 => P108 | D21 => P107 | D22 => P106 | D23 => P105 | D24 => P104 | D25 => P103 | D26 => P102 | D27 => P101 | D28 => P100 | D29 => P99 | D30 => P98 | D31 => P97 | D32 => P96 | D33 => P95 | D34 => P94 | D35 => P93 | D36 => P92 | D37 => P91 | D38 => P90 | D39 => P89 | D40 => P88 | D41 => P87 | D42 => P86 | D43 => P85 | D44 => P84 | D45 => P83 | D46 => P82 | D47 => P81 | D48 => P80 | D49 => P79 | D50 => P78 | D51 => P77 | D52 => P76 | D53 => P75 | D54 => P74 | D55 => P73 | D56 => P72 | D57 => P71 | D58 => P70 | D59 => P69 | D60 => P68 | D61 => P67 | D62 => P66 | D63 => P65 end
  | D2 => match b with D0 => P1 | D1 => P0 | D2 => P127 | D3 => P126 | D4 => P125 | D5 => P124 | D6 => P123 | D7 => P122 | D8 => P121 | D9 => P120 | D10 => P119 | D11 => P118 | D12 => P117 | D13 => P116 | D14 => P115 | D15 => P114 | D16 => P113 | D17 => P112 | D18 => P111 | D19 => P110 | D20 => P109 | D21 => P108 | D22 => P107 | D23 => P106 | D24 => P105 | D25 => P104 | D26 => P103 | D27 => P102 | D28 => P101 | D29 => P100 | D30 => P99 | D31 => P98 | D32 => P97 | D33 => P96 | D34 => P95 | D35 => P94 | D36 => P93 | D37 => P92 | D38 => P91 | D39 => P90 | D40 => P89 | D41 => P88 | D42 => P87 | D43 => P86 | D44 => P85 | D45 => P84 | D46 => P83 | D47 => P82 | D48 => P81 | D49 => P80 | D50 => P79 | D51 => P78 | D52 => P77 | D53 => P76 | D54 => P75 | D55 => P74 | D56 => P73 | D57 => P72 | D58 => P71 | D59 => P70 | D60 => P69 | D61 => P68 | D62 => P67 | D63 => P66 end
  | D3 => match b with D0 => P2 | D1 => P1 | D2 => P0 | D3 => P127 | D4 => P126 | D5 => P125 | D6 => P124 | D7 => P123 | D8 => P122 | D9 => P121 | D10 => P120 | D11 => P119 | D12 => P118 | D13 => P117 | D14 => P116 | D15 => P115 | D16 => P114 | D17 => P113 | D18 => P112 | D19 => P111 | D20 => P110 | D21 => P109 | D22 => P108 | D23 => P107 | D24 => P106 | D25 => P105 | D26 => P104 | D27 => P103 | D28 => P102 | D29 => P101 | D30 => P100 | D31 => P99 | D32 => P98 | D33 => P97 | D34 => P96 | D35 => P95 | D36 => P94 | D37 => P93 | D38 => P92 | D39 => P91 | D40 => P90 | D41 => P89 | D42 => P88 | D43 => P87 | D44 => P86 | D45 => P85 | D46 => P84 | D47 => P83 | D48 => P82 | D49 => P81 | D50 => P80 | D51 => P79 | D52 => P78 | D53 => P77 | D54 => P76 | D55 => P75 | D56 => P74 | D57 => P73 | D58 => P72 | D59 => P71 | D60 => P70 | D61 => P69 | D62 => P68 | D63 => P67 end
  | D4 => match b with D0 => P3 | D1 => P2 | D2 => P1 | D3 => P0 | D4 => P127 | D5 => P126 | D6 => P125 | D7 => P124 | D8 => P123 | D9 => P122 | D10 => P121 | D11 => P120 | D12 => P119 | D13 => P118 | D14 => P117 | D15 => P116 | D16 => P115 | D17 => P114 | D18 => P113 | D19 => P112 | D20 => P111 | D21 => P110 | D22 => P109 | D23 => P108 | D24 => P107 | D25 => P106 | D26 => P105 | D27 => P104 | D28 => P103 | D29 => P102 | D30 => P101 | D31 => P100 | D32 => P99 | D33 => P98 | D34 => P97 | D35 => P96 | D36 => P95 | D37 => P94 | D38 => P93 | D39 => P92 | D40 => P91 | D41 => P90 | D42 => P89 | D43 => P88 | D44 => P87 | D45 => P86 | D46 => P85 | D47 => P84 | D48 => P83 | D49 => P82 | D50 => P81 | D51 => P80 | D52 => P79 | D53 => P78 | D54 => P77 | D55 => P76 | D56 => P75 | D57 => P74 | D58 => P73 | D59 => P72 | D60 => P71 | D61 => P70 | D62 => P69 | D63 => P68 end
  | D5 => match b with D0 => P4 | D1 => P3 | D2 => P2 | D3 => P1 | D4 => P0 | D5 => P127 | D6 => P126 | D7 => P125 | D8 => P124 | D9 => P123 | D10 => P122 | D11 => P121 | D12 => P120 | D13 => P119 | D14 => P118 | D15 => P117 | D16 => P116 | D17 => P115 | D18 => P114 | D19 => P113 | D20 => P112 | D21 => P111 | D22 => P110 | D23 => P109 | D24 => P108 | D25 => P107 | D26 => P106 | D27 => P105 | D28 => P104 | D29 => P103 | D30 => P102 | D31 => P101 | D32 => P100 | D33 => P99 | D34 => P98 | D35 => P97 | D36 => P96 | D37 => P95 | D38 => P94 | D39 => P93 | D40 => P92 | D41 => P91 | D42 => P90 | D43 => P89 | D44 => P88 | D45 => P87 | D46 => P86 | D47 => P85 | D48 => P84 | D49 => P83 | D50 => P82 | D51 => P81 | D52 => P80 | D53 => P79 | D54 => P78 | D55 => P77 | D56 => P76 | D57 => P75 | D58 => P74 | D59 => P73 | D60 => P72 | D61 => P71 | D62 => P70 | D63 => P69 end
  | D6 => match b with D0 => P5 | D1 => P4 | D2 => P3 | D3 => P2 | D4 => P1 | D5 => P0 | D6 => P127 | D7 => P126 | D8 => P125 | D9 => P124 | D10 => P123 | D11 => P122 | D12 => P121 | D13 => P120 | D14 => P119 | D15 => P118 | D16 => P117 | D17 => P116 | D18 => P115 | D19 => P114 | D20 => P113 | D21 => P112 | D22 => P111 | D23 => P110 | D24 => P109 | D25 => P108 | D26 => P107 | D27 => P106 | D28 => P105 | D29 => P104 | D30 => P103 | D31 => P102 | D32 => P101 | D33 => P100 | D34 => P99 | D35 => P98 | D36 => P97 | D37 => P96 | D38 => P95 | D39 => P94 | D40 => P93 | D41 => P92 | D42 => P91 | D43 => P90 | D44 => P89 | D45 => P88 | D46 => P87 | D47 => P86 | D48 => P85 | D49 => P84 | D50 => P83 | D51 => P82 | D52 => P81 | D53 => P80 | D54 => P79 | D55 => P78 | D56 => P77 | D57 => P76 | D58 => P75 | D59 => P74 | D60 => P73 | D61 => P72 | D62 => P71 | D63 => P70 end
  | D7 => match b with D0 => P6 | D1 => P5 | D2 => P4 | D3 => P3 | D4 => P2 | D5 => P1 | D6 => P0 | D7 => P127 | D8 => P126 | D9 => P125 | D10 => P124 | D11 => P123 | D12 => P122 | D13 => P121 | D14 => P120 | D15 => P119 | D16 => P118 | D17 => P117 | D18 => P116 | D19 => P115 | D20 => P114 | D21 => P113 | D22 => P112 | D23 => P111 | D24 => P110 | D25 => P109 | D26 => P108 | D27 => P107 | D28 => P106 | D29 => P105 | D30 => P104 | D31 => P103 | D32 => P102 | D33 => P101 | D34 => P100 | D35 => P99 | D36 => P98 | D37 => P97 | D38 => P96 | D39 => P95 | D40 => P94 | D41 => P93 | D42 => P92 | D43 => P91 | D44 => P90 | D45 => P89 | D46 => P88 | D47 => P87 | D48 => P86 | D49 => P85 | D50 => P84 | D51 => P83 | D52 => P82 | D53 => P81 | D54 => P80 | D55 => P79 | D56 => P78 | D57 => P77 | D58 => P76 | D59 => P75 | D60 => P74 | D61 => P73 | D62 => P72 | D63 => P71 end
  | D8 => match b with D0 => P7 | D1 => P6 | D2 => P5 | D3 => P4 | D4 => P3 | D5 => P2 | D6 => P1 | D7 => P0 | D8 => P127 | D9 => P126 | D10 => P125 | D11 => P124 | D12 => P123 | D13 => P122 | D14 => P121 | D15 => P120 | D16 => P119 | D17 => P118 | D18 => P117 | D19 => P116 | D20 => P115 | D21 => P114 | D22 => P113 | D23 => P112 | D24 => P111 | D25 => P110 | D26 => P109 | D27 => P108 | D28 => P107 | D29 => P106 | D30 => P105 | D31 => P104 | D32 => P103 | D33 => P102 | D34 => P101 | D35 => P100 | D36 => P99 | D37 => P98 | D38 => P97 | D39 => P96 | D40 => P95 | D41 => P94 | D42 => P93 | D43 => P92 | D44 => P91 | D45 => P90 | D46 => P89 | D47 => P88 | D48 => P87 | D49 => P86 | D50 => P85 | D51 => P84 | D52 => P83 | D53 => P82 | D54 => P81 | D55 => P80 | D56 => P79 | D57 => P78 | D58 => P77 | D59 => P76 | D60 => P75 | D61 => P74 | D62 => P73 | D63 => P72 end
  | D9 => match b with D0 => P8 | D1 => P7 | D2 => P6 | D3 => P5 | D4 => P4 | D5 => P3 | D6 => P2 | D7 => P1 | D8 => P0 | D9 => P127 | D10 => P126 | D11 => P125 | D12 => P124 | D13 => P123 | D14 => P122 | D15 => P121 | D16 => P120 | D17 => P119 | D18 => P118 | D19 => P117 | D20 => P116 | D21 => P115 | D22 => P114 | D23 => P113 | D24 => P112 | D25 => P111 | D26 => P110 | D27 => P109 | D28 => P108 | D29 => P107 | D30 => P106 | D31 => P105 | D32 => P104 | D33 => P103 | D34 => P102 | D35 => P101 | D36 => P100 | D37 => P99 | D38 => P98 | D39 => P97 | D40 => P96 | D41 => P95 | D42 => P94 | D43 => P93 | D44 => P92 | D45 => P91 | D46 => P90 | D47 => P89 | D48 => P88 | D49 => P87 | D50 => P86 | D51 => P85 | D52 => P84 | D53 => P83 | D54 => P82 | D55 => P81 | D56 => P80 | D57 => P79 | D58 => P78 | D59 => P77 | D60 => P76 | D61 => P75 | D62 => P74 | D63 => P73 end
  | D10 => match b with D0 => P9 | D1 => P8 | D2 => P7 | D3 => P6 | D4 => P5 | D5 => P4 | D6 => P3 | D7 => P2 | D8 => P1 | D9 => P0 | D10 => P127 | D11 => P126 | D12 => P125 | D13 => P124 | D14 => P123 | D15 => P122 | D16 => P121 | D17 => P120 | D18 => P119 | D19 => P118 | D20 => P117 | D21 => P116 | D22 => P115 | D23 => P114 | D24 => P113 | D25 => P112 | D26 => P111 | D27 => P110 | D28 => P109 | D29 => P108 | D30 => P107 | D31 => P106 | D32 => P105 | D33 => P104 | D34 => P103 | D35 => P102 | D36 => P101 | D37 => P100 | D38 => P99 | D39 => P98 | D40 => P97 | D41 => P96 | D42 => P95 | D43 => P94 | D44 => P93 | D45 => P92 | D46 => P91 | D47 => P90 | D48 => P89 | D49 => P88 | D50 => P87 | D51 => P86 | D52 => P85 | D53 => P84 | D54 => P83 | D55 => P82 | D56 => P81 | D57 => P80 | D58 => P79 | D59 => P78 | D60 => P77 | D61 => P76 | D62 => P75 | D63 => P74 end
  | D11 => match b with D0 => P10 | D1 => P9 | D2 => P8 | D3 => P7 | D4 => P6 | D5 => P5 | D6 => P4 | D7 => P3 | D8 => P2 | D9 => P1 | D10 => P0 | D11 => P127 | D12 => P126 | D13 => P125 | D14 => P124 | D15 => P123 | D16 => P122 | D17 => P121 | D18 => P120 | D19 => P119 | D20 => P118 | D21 => P117 | D22 => P116 | D23 => P115 | D24 => P114 | D25 => P113 | D26 => P112 | D27 => P111 | D28 => P110 | D29 => P109 | D30 => P108 | D31 => P107 | D32 => P106 | D33 => P105 | D34 => P104 | D35 => P103 | D36 => P102 | D37 => P101 | D38 => P100 | D39 => P99 | D40 => P98 | D41 => P97 | D42 => P96 | D43 => P95 | D44 => P94 | D45 => P93 | D46 => P92 | D47 => P91 | D48 => P90 | D49 => P89 | D50 => P88 | D51 => P87 | D52 => P86 | D53 => P85 | D54 => P84 | D55 => P83 | D56 => P82 | D57 => P81 | D58 => P80 | D59 => P79 | D60 => P78 | D61 => P77 | D62 => P76 | D63 => P75 end
  | D12 => match b with D0 => P11 | D1 => P10 | D2 => P9 | D3 => P8 | D4 => P7 | D5 => P6 | D6 => P5 | D7 => P4 | D8 => P3 | D9 => P2 | D10 => P1 | D11 => P0 | D12 => P127 | D13 => P126 | D14 => P125 | D15 => P124 | D16 => P123 | D17 => P122 | D18 => P121 | D19 => P120 | D20 => P119 | D21 => P118 | D22 => P117 | D23 => P116 | D24 => P115 | D25 => P114 | D26 => P113 | D27 => P112 | D28 => P111 | D29 => P110 | D30 => P109 | D31 => P108 | D32 => P107 | D33 => P106 | D34 => P105 | D35 => P104 | D36 => P103 | D37 => P102 | D38 => P101 | D39 => P100 | D40 => P99 | D41 => P98 | D42 => P97 | D43 => P96 | D44 => P95 | D45 => P94 | D46 => P93 | D47 => P92 | D48 => P91 | D49 => P90 | D50 => P89 | D51 => P88 | D52 => P87 | D53 => P86 | D54 => P85 | D55 => P84 | D56 => P83 | D57 => P82 | D58 => P81 | D59 => P80 | D60 => P79 | D61 => P78 | D62 => P77 | D63 => P76 end
  | D13 => match b with D0 => P12 | D1 => P11 | D2 => P10 | D3 => P9 | D4 => P8 | D5 => P7 | D6 => P6 | D7 => P5 | D8 => P4 | D9 => P3 | D10 => P2 | D11 => P1 | D12 => P0 | D13 => P127 | D14 => P126 | D15 => P125 | D16 => P124 | D17 => P123 | D18 => P122 | D19 => P121 | D20 => P120 | D21 => P119 | D22 => P118 | D23 => P117 | D24 => P116 | D25 => P115 | D26 => P114 | D27 => P113 | D28 => P112 | D29 => P111 | D30 => P110 | D31 => P109 | D32 => P108 | D33 => P107 | D34 => P106 | D35 => P105 | D36 => P104 | D37 => P103 | D38 => P102 | D39 => P101 | D40 => P100 | D41 => P99 | D42 => P98 | D43 => P97 | D44 => P96 | D45 => P95 | D46 => P94 | D47 => P93 | D48 => P92 | D49 => P91 | D50 => P90 | D51 => P89 | D52 => P88 | D53 => P87 | D54 => P86 | D55 => P85 | D56 => P84 | D57 => P83 | D58 => P82 | D59 => P81 | D60 => P80 | D61 => P79 | D62 => P78 | D63 => P77 end
  | D14 => match b with D0 => P13 | D1 => P12 | D2 => P11 | D3 => P10 | D4 => P9 | D5 => P8 | D6 => P7 | D7 => P6 | D8 => P5 | D9 => P4 | D10 => P3 | D11 => P2 | D12 => P1 | D13 => P0 | D14 => P127 | D15 => P126 | D16 => P125 | D17 => P124 | D18 => P123 | D19 => P122 | D20 => P121 | D21 => P120 | D22 => P119 | D23 => P118 | D24 => P117 | D25 => P116 | D26 => P115 | D27 => P114 | D28 => P113 | D29 => P112 | D30 => P111 | D31 => P110 | D32 => P109 | D33 => P108 | D34 => P107 | D35 => P106 | D36 => P105 | D37 => P104 | D38 => P103 | D39 => P102 | D40 => P101 | D41 => P100 | D42 => P99 | D43 => P98 | D44 => P97 | D45 => P96 | D46 => P95 | D47 => P94 | D48 => P93 | D49 => P92 | D50 => P91 | D51 => P90 | D52 => P89 | D53 => P88 | D54 => P87 | D55 => P86 | D56 => P85 | D57 => P84 | D58 => P83 | D59 => P82 | D60 => P81 | D61 => P80 | D62 => P79 | D63 => P78 end
  | D15 => match b with D0 => P14 | D1 => P13 | D2 => P12 | D3 => P11 | D4 => P10 | D5 => P9 | D6 => P8 | D7 => P7 | D8 => P6 | D9 => P5 | D10 => P4 | D11 => P3 | D12 => P2 | D13 => P1 | D14 => P0 | D15 => P127 | D16 => P126 | D17 => P125 | D18 => P124 | D19 => P123 | D20 => P122 | D21 => P121 | D22 => P120 | D23 => P119 | D24 => P118 | D25 => P117 | D26 => P116 | D27 => P115 | D28 => P114 | D29 => P113 | D30 => P112 | D31 => P111 | D32 => P110 | D33 => P109 | D34 => P108 | D35 => P107 | D36 => P106 | D37 => P105 | D38 => P104 | D39 => P103 | D40 => P102 | D41 => P101 | D42 => P100 | D43 => P99 | D44 => P98 | D45 => P97 | D46 => P96 | D47 => P95 | D48 => P94 | D49 => P93 | D50 => P92 | D51 => P91 | D52 => P90 | D53 => P89 | D54 => P88 | D55 => P87 | D56 => P86 | D57 => P85 | D58 => P84 | D59 => P83 | D60 => P82 | D61 => P81 | D62 => P80 | D63 => P79 end
  | D16 => match b with D0 => P15 | D1 => P14 | D2 => P13 | D3 => P12 | D4 => P11 | D5 => P10 | D6 => P9 | D7 => P8 | D8 => P7 | D9 => P6 | D10 => P5 | D11 => P4 | D12 => P3 | D13 => P2 | D14 => P1 | D15 => P0 | D16 => P127 | D17 => P126 | D18 => P125 | D19 => P124 | D20 => P123 | D21 => P122 | D22 => P121 | D23 => P120 | D24 => P119 | D25 => P118 | D26 => P117 | D27 => P116 | D28 => P115 | D29 => P114 | D30 => P113 | D31 => P112 | D32 => P111 | D33 => P110 | D34 => P109 | D35 => P108 | D36 => P107 | D37 => P106 | D38 => P105 | D39 => P104 | D40 => P103 | D41 => P102 | D42 => P101 | D43 => P100 | D44 => P99 | D45 => P98 | D46 => P97 | D47 => P96 | D48 => P95 | D49 => P94 | D50 => P93 | D51 => P92 | D52 => P91 | D53 => P90 | D54 => P89 | D55 => P88 | D56 => P87 | D57 => P86 | D58 => P85 | D59 => P84 | D60 => P83 | D61 => P82 | D62 => P81 | D63 => P80 end
  | D17 => match b with D0 => P16 | D1 => P15 | D2 => P14 | D3 => P13 | D4 => P12 | D5 => P11 | D6 => P10 | D7 => P9 | D8 => P8 | D9 => P7 | D10 => P6 | D11 => P5 | D12 => P4 | D13 => P3 | D14 => P2 | D15 => P1 | D16 => P0 | D17 => P127 | D18 => P126 | D19 => P125 | D20 => P124 | D21 => P123 | D22 => P122 | D23 => P121 | D24 => P120 | D25 => P119 | D26 => P118 | D27 => P117 | D28 => P116 | D29 => P115 | D30 => P114 | D31 => P113 | D32 => P112 | D33 => P111 | D34 => P110 | D35 => P109 | D36 => P108 | D37 => P107 | D38 => P106 | D39 => P105 | D40 => P104 | D41 => P103 | D42 => P102 | D43 => P101 | D44 => P100 | D45 => P99 | D46 => P98 | D47 => P97 | D48 => P96 | D49 => P95 | D50 => P94 | D51 => P93 | D52 => P92 | D53 => P91 | D54 => P90 | D55 => P89 | D56 => P88 | D57 => P87 | D58 => P86 | D59 => P85 | D60 => P84 | D61 => P83 | D62 => P82 | D63 => P81 end
  | D18 => match b with D0 => P17 | D1 => P16 | D2 => P15 | D3 => P14 | D4 => P13 | D5 => P12 | D6 => P11 | D7 => P10 | D8 => P9 | D9 => P8 | D10 => P7 | D11 => P6 | D12 => P5 | D13 => P4 | D14 => P3 | D15 => P2 | D16 => P1 | D17 => P0 | D18 => P127 | D19 => P126 | D20 => P125 | D21 => P124 | D22 => P123 | D23 => P122 | D24 => P121 | D25 => P120 | D26 => P119 | D27 => P118 | D28 => P117 | D29 => P116 | D30 => P115 | D31 => P114 | D32 => P113 | D33 => P112 | D34 => P111 | D35 => P110 | D36 => P109 | D37 => P108 | D38 => P107 | D39 => P106 | D40 => P105 | D41 => P104 | D42 => P103 | D43 => P102 | D44 => P101 | D45 => P100 | D46 => P99 | D47 => P98 | D48 => P97 | D49 => P96 | D50 => P95 | D51 => P94 | D52 => P93 | D53 => P92 | D54 => P91 | D55 => P90 | D56 => P89 | D57 => P88 | D58 => P87 | D59 => P86 | D60 => P85 | D61 => P84 | D62 => P83 | D63 => P82 end
  | D19 => match b with D0 => P18 | D1 => P17 | D2 => P16 | D3 => P15 | D4 => P14 | D5 => P13 | D6 => P12 | D7 => P11 | D8 => P10 | D9 => P9 | D10 => P8 | D11 => P7 | D12 => P6 | D13 => P5 | D14 => P4 | D15 => P3 | D16 => P2 | D17 => P1 | D18 => P0 | D19 => P127 | D20 => P126 | D21 => P125 | D22 => P124 | D23 => P123 | D24 => P122 | D25 => P121 | D26 => P120 | D27 => P119 | D28 => P118 | D29 => P117 | D30 => P116 | D31 => P115 | D32 => P114 | D33 => P113 | D34 => P112 | D35 => P111 | D36 => P110 | D37 => P109 | D38 => P108 | D39 => P107 | D40 => P106 | D41 => P105 | D42 => P104 | D43 => P103 | D44 => P102 | D45 => P101 | D46 => P100 | D47 => P99 | D48 => P98 | D49 => P97 | D50 => P96 | D51 => P95 | D52 => P94 | D53 => P93 | D54 => P92 | D55 => P91 | D56 => P90 | D57 => P89 | D58 => P88 | D59 => P87 | D60 => P86 | D61 => P85 | D62 => P84 | D63 => P83 end
  | D20 => match b with D0 => P19 | D1 => P18 | D2 => P17 | D3 => P16 | D4 => P15 | D5 => P14 | D6 => P13 | D7 => P12 | D8 => P11 | D9 => P10 | D10 => P9 | D11 => P8 | D12 => P7 | D13 => P6 | D14 => P5 | D15 => P4 | D16 => P3 | D17 => P2 | D18 => P1 | D19 => P0 | D20 => P127 | D21 => P126 | D22 => P125 | D23 => P124 | D24 => P123 | D25 => P122 | D26 => P121 | D27 => P120 | D28 => P119 | D29 => P118 | D30 => P117 | D31 => P116 | D32 => P115 | D33 => P114 | D34 => P113 | D35 => P112 | D36 => P111 | D37 => P110 | D38 => P109 | D39 => P108 | D40 => P107 | D41 => P106 | D42 => P105 | D43 => P104 | D44 => P103 | D45 => P102 | D46 => P101 | D47 => P100 | D48 => P99 | D49 => P98 | D50 => P97 | D51 => P96 | D52 => P95 | D53 => P94 | D54 => P93 | D55 => P92 | D56 => P91 | D57 => P90 | D58 => P89 | D59 => P88 | D60 => P87 | D61 => P86 | D62 => P85 | D63 => P84 end
  | D21 => match b with D0 => P20 | D1 => P19 | D2 => P18 | D3 => P17 | D4 => P16 | D5 => P15 | D6 => P14 | D7 => P13 | D8 => P12 | D9 => P11 | D10 => P10 | D11 => P9 | D12 => P8 | D13 => P7 | D14 => P6 | D15 => P5 | D16 => P4 | D17 => P3 | D18 => P2 | D19 => P1 | D20 => P0 | D21 => P127 | D22 => P126 | D23 => P125 | D24 => P124 | D25 => P123 | D26 => P122 | D27 => P121 | D28 => P120 | D29 => P119 | D30 => P118 | D31 => P117 | D32 => P116 | D33 => P115 | D34 => P114 | D35 => P113 | D36 => P112 | D37 => P111 | D38 => P110 | D39 => P109 | D40 => P108 | D41 => P107 | D42 => P106 | D43 => P105 | D44 => P104 | D45 => P103 | D46 => P102 | D47 => P101 | D48 => P100 | D49 => P99 | D50 => P98 | D51 => P97 | D52 => P96 | D53 => P95 | D54 => P94 | D55 => P93 | D56 => P92 | D57 => P91 | D58 => P90 | D59 => P89 | D60 => P88 | D61 => P87 | D62 => P86 | D63 => P85 end
  | D22 => match b with D0 => P21 | D1 => P20 | D2 => P19 | D3 => P18 | D4 => P17 | D5 => P16 | D6 => P15 | D7 => P14 | D8 => P13 | D9 => P12 | D10 => P11 | D11 => P10 | D12 => P9 | D13 => P8 | D14 => P7 | D15 => P6 | D16 => P5 | D17 => P4 | D18 => P3 | D19 => P2 | D20 => P1 | D21 => P0 | D22 => P127 | D23 => P126 | D24 => P125 | D25 => P124 | D26 => P123 | D27 => P122 | D28 => P121 | D29 => P120 | D30 => P119 | D31 => P118 | D32 => P117 | D33 => P116 | D34 => P115 | D35 => P114 | D36 => P113 | D37 => P112 | D38 => P111 | D39 => P110 | D40 => P109 | D41 => P108 | D42 => P107 | D43 => P106 | D44 => P105 | D45 => P104 | D46 => P103 | D47 => P102 | D48 => P101 | D49 => P100 | D50 => P99 | D51 => P98 | D52 => P97 | D53 => P96 | D54 => P95 | D55 => P94 | D56 => P93 | D57 => P92 | D58 => P91 | D59 => P90 | D60 => P89 | D61 => P88 | D62 => P87 | D63 => P86 end
  | D23 => match b with D0 => P22 | D1 => P21 | D2 => P20 | D3 => P19 | D4 => P18 | D5 => P17 | D6 => P16 | D7 => P15 | D8 => P14 | D9 => P13 | D10 => P12 | D11 => P11 | D12 => P10 | D13 => P9 | D14 => P8 | D15 => P7 | D16 => P6 | D17 => P5 | D18 => P4 | D19 => P3 | D20 => P2 | D21 => P1 | D22 => P0 | D23 => P127 | D24 => P126 | D25 => P125 | D26 => P124 | D27 => P123 | D28 => P122 | D29 => P121 | D30 => P120 | D31 => P119 | D32 => P118 | D33 => P117 | D34 => P116 | D35 => P115 | D36 => P114 | D37 => P113 | D38 => P112 | D39 => P111 | D40 => P110 | D41 => P109 | D42 => P108 | D43 => P107 | D44 => P106 | D45 => P105 | D46 => P104 | D47 => P103 | D48 => P102 | D49 => P101 | D50 => P100 | D51 => P99 | D52 => P98 | D53 => P97 | D54 => P96 | D55 => P95 | D56 => P94 | D57 => P93 | D58 => P92 | D59 => P91 | D60 => P90 | D61 => P89 | D62 => P88 | D63 => P87 end
  | D24 => match b with D0 => P23 | D1 => P22 | D2 => P21 | D3 => P20 | D4 => P19 | D5 => P18 | D6 => P17 | D7 => P16 | D8 => P15 | D9 => P14 | D10 => P13 | D11 => P12 | D12 => P11 | D13 => P10 | D14 => P9 | D15 => P8 | D16 => P7 | D17 => P6 | D18 => P5 | D19 => P4 | D20 => P3 | D21 => P2 | D22 => P1 | D23 => P0 | D24 => P127 | D25 => P126 | D26 => P125 | D27 => P124 | D28 => P123 | D29 => P122 | D30 => P121 | D31 => P120 | D32 => P119 | D33 => P118 | D34 => P117 | D35 => P116 | D36 => P115 | D37 => P114 | D38 => P113 | D39 => P112 | D40 => P111 | D41 => P110 | D42 => P109 | D43 => P108 | D44 => P107 | D45 => P106 | D46 => P105 | D47 => P104 | D48 => P103 | D49 => P102 | D50 => P101 | D51 => P100 | D52 => P99 | D53 => P98 | D54 => P97 | D55 => P96 | D56 => P95 | D57 => P94 | D58 => P93 | D59 => P92 | D60 => P91 | D61 => P90 | D62 => P89 | D63 => P88 end
  | D25 => match b with D0 => P24 | D1 => P23 | D2 => P22 | D3 => P21 | D4 => P20 | D5 => P19 | D6 => P18 | D7 => P17 | D8 => P16 | D9 => P15 | D10 => P14 | D11 => P13 | D12 => P12 | D13 => P11 | D14 => P10 | D15 => P9 | D16 => P8 | D17 => P7 | D18 => P6 | D19 => P5 | D20 => P4 | D21 => P3 | D22 => P2 | D23 => P1 | D24 => P0 | D25 => P127 | D26 => P126 | D27 => P125 | D28 => P124 | D29 => P123 | D30 => P122 | D31 => P121 | D32 => P120 | D33 => P119 | D34 => P118 | D35 => P117 | D36 => P116 | D37 => P115 | D38 => P114 | D39 => P113 | D40 => P112 | D41 => P111 | D42 => P110 | D43 => P109 | D44 => P108 | D45 => P107 | D46 => P106 | D47 => P105 | D48 => P104 | D49 => P103 | D50 => P102 | D51 => P101 | D52 => P100 | D53 => P99 | D54 => P98 | D55 => P97 | D56 => P96 | D57 => P95 | D58 => P94 | D59 => P93 | D60 => P92 | D61 => P91 | D62 => P90 | D63 => P89 end
  | D26 => match b with D0 => P25 | D1 => P24 | D2 => P23 | D3 => P22 | D4 => P21 | D5 => P20 | D6 => P19 | D7 => P18 | D8 => P17 | D9 => P16 | D10 => P15 | D11 => P14 | D12 => P13 | D13 => P12 | D14 => P11 | D15 => P10 | D16 => P9 | D17 => P8 | D18 => P7 | D19 => P6 | D20 => P5 | D21 => P4 | D22 => P3 | D23 => P2 | D24 => P1 | D25 => P0 | D26 => P127 | D27 => P126 | D28 => P125 | D29 => P124 | D30 => P123 | D31 => P122 | D32 => P121 | D33 => P120 | D34 => P119 | D35 => P118 | D36 => P117 | D37 => P116 | D38 => P115 | D39 => P114 | D40 => P113 | D41 => P112 | D42 => P111 | D43 => P110 | D44 => P109 | D45 => P108 | D46 => P107 | D47 => P106 | D48 => P105 | D49 => P104 | D50 => P103 | D51 => P102 | D52 => P101 | D53 => P100 | D54 => P99 | D55 => P98 | D56 => P97 | D57 => P96 | D58 => P95 | D59 => P94 | D60 => P93 | D61 => P92 | D62 => P91 | D63 => P90 end
  | D27 => match b with D0 => P26 | D1 => P25 | D2 => P24 | D3 => P23 | D4 => P22 | D5 => P21 | D6 => P20 | D7 => P19 | D8 => P18 | D9 => P17 | D10 => P16 | D11 => P15 | D12 => P14 | D13 => P13 | D14 => P12 | D15 => P11 | D16 => P10 | D17 => P9 | D18 => P8 | D19 => P7 | D20 => P6 | D21 => P5 | D22 => P4 | D23 => P3 | D24 => P2 | D25 => P1 | D26 => P0 | D27 => P127 | D28 => P126 | D29 => P125 | D30 => P124 | D31 => P123 | D32 => P122 | D33 => P121 | D34 => P120 | D35 => P119 | D36 => P118 | D37 => P117 | D38 => P116 | D39 => P115 | D40 => P114 | D41 => P113 | D42 => P112 | D43 => P111 | D44 => P110 | D45 => P109 | D46 => P108 | D47 => P107 | D48 => P106 | D49 => P105 | D50 => P104 | D51 => P103 | D52 => P102 | D53 => P101 | D54 => P100 | D55 => P99 | D56 => P98 | D57 => P97 | D58 => P96 | D59 => P95 | D60 => P94 | D61 => P93 | D62 => P92 | D63 => P91 end
  | D28 => match b with D0 => P27 | D1 => P26 | D2 => P25 | D3 => P24 | D4 => P23 | D5 => P22 | D6 => P21 | D7 => P20 | D8 => P19 | D9 => P18 | D10 => P17 | D11 => P16 | D12 => P15 | D13 => P14 | D14 => P13 | D15 => P12 | D16 => P11 | D17 => P10 | D18 => P9 | D19 => P8 | D20 => P7 | D21 => P6 | D22 => P5 | D23 => P4 | D24 => P3 | D25 => P2 | D26 => P1 | D27 => P0 | D28 => P127 | D29 => P126 | D30 => P125 | D31 => P124 | D32 => P123 | D33 => P122 | D34 => P121 | D35 => P120 | D36 => P119 | D37 => P118 | D38 => P117 | D39 => P116 | D40 => P115 | D41 => P114 | D42 => P113 | D43 => P112 | D44 => P111 | D45 => P110 | D46 => P109 | D47 => P108 | D48 => P107 | D49 => P106 | D50 => P105 | D51 => P104 | D52 => P103 | D53 => P102 | D54 => P101 | D55 => P100 | D56 => P99 | D57 => P98 | D58 => P97 | D59 => P96 | D60 => P95 | D61 => P94 | D62 => P93 | D63 => P92 end
  | D29 => match b with D0 => P28 | D1 => P27 | D2 => P26 | D3 => P25 | D4 => P24 | D5 => P23 | D6 => P22 | D7 => P21 | D8 => P20 | D9 => P19 | D10 => P18 | D11 => P17 | D12 => P16 | D13 => P15 | D14 => P14 | D15 => P13 | D16 => P12 | D17 => P11 | D18 => P10 | D19 => P9 | D20 => P8 | D21 => P7 | D22 => P6 | D23 => P5 | D24 => P4 | D25 => P3 | D26 => P2 | D27 => P1 | D28 => P0 | D29 => P127 | D30 => P126 | D31 => P125 | D32 => P124 | D33 => P123 | D34 => P122 | D35 => P121 | D36 => P120 | D37 => P119 | D38 => P118 | D39 => P117 | D40 => P116 | D41 => P115 | D42 => P114 | D43 => P113 | D44 => P112 | D45 => P111 | D46 => P110 | D47 => P109 | D48 => P108 | D49 => P107 | D50 => P106 | D51 => P105 | D52 => P104 | D53 => P103 | D54 => P102 | D55 => P101 | D56 => P100 | D57 => P99 | D58 => P98 | D59 => P97 | D60 => P96 | D61 => P95 | D62 => P94 | D63 => P93 end
  | D30 => match b with D0 => P29 | D1 => P28 | D2 => P27 | D3 => P26 | D4 => P25 | D5 => P24 | D6 => P23 | D7 => P22 | D8 => P21 | D9 => P20 | D10 => P19 | D11 => P18 | D12 => P17 | D13 => P16 | D14 => P15 | D15 => P14 | D16 => P13 | D17 => P12 | D18 => P11 | D19 => P10 | D20 => P9 | D21 => P8 | D22 => P7 | D23 => P6 | D24 => P5 | D25 => P4 | D26 => P3 | D27 => P2 | D28 => P1 | D29 => P0 | D30 => P127 | D31 => P126 | D32 => P125 | D33 => P124 | D34 => P123 | D35 => P122 | D36 => P121 | D37 => P120 | D38 => P119 | D39 => P118 | D40 => P117 | D41 => P116 | D42 => P115 | D43 => P114 | D44 => P113 | D45 => P112 | D46 => P111 | D47 => P110 | D48 => P109 | D49 => P108 | D50 => P107 | D51 => P106 | D52 => P105 | D53 => P104 | D54 => P103 | D55 => P102 | D56 => P101 | D57 => P100 | D58 => P99 | D59 => P98 | D60 => P97 | D61 => P96 | D62 => P95 | D63 => P94 end
  | D31 => match b with D0 => P30 | D1 => P29 | D2 => P28 | D3 => P27 | D4 => P26 | D5 => P25 | D6 => P24 | D7 => P23 | D8 => P22 | D9 => P21 | D10 => P20 | D11 => P19 | D12 => P18 | D13 => P17 | D14 => P16 | D15 => P15 | D16 => P14 | D17 => P13 | D18 => P12 | D19 => P11 | D20 => P10 | D21 => P9 | D22 => P8 | D23 => P7 | D24 => P6 | D25 => P5 | D26 => P4 | D27 => P3 | D28 => P2 | D29 => P1 | D30 => P0 | D31 => P127 | D32 => P126 | D33 => P125 | D34 => P124 | D35 => P123 | D36 => P122 | D37 => P121 | D38 => P120 | D39 => P119 | D40 => P118 | D41 => P117 | D42 => P116 | D43 => P115 | D44 => P114 | D45 => P113 | D46 => P112 | D47 => P111 | D48 => P110 | D49 => P109 | D50 => P108 | D51 => P107 | D52 => P106 | D53 => P105 | D54 => P104 | D55 => P103 | D56 => P102 | D57 => P101 | D58 => P100 | D59 => P99 | D60 => P98 | D61 => P97 | D62 => P96 | D63 => P95 end
  | D32 => match b with D0 => P31 | D1 => P30 | D2 => P29 | D3 => P28 | D4 => P27 | D5 => P26 | D6 => P25 | D7 => P24 | D8 => P23 | D9 => P22 | D10 => P21 | D11 => P20 | D12 => P19 | D13 => P18 | D14 => P17 | D15 => P16 | D16 => P15 | D17 => P14 | D18 => P13 | D19 => P12 | D20 => P11 | D21 => P10 | D22 => P9 | D23 => P8 | D24 => P7 | D25 => P6 | D26 => P5 | D27 => P4 | D28 => P3 | D29 => P2 | D30 => P1 | D31 => P0 | D32 => P127 | D33 => P126 | D34 => P125 | D35 => P124 | D36 => P123 | D37 => P122 | D38 => P121 | D39 => P120 | D40 => P119 | D41 => P118 | D42 => P117 | D43 => P116 | D44 => P115 | D45 => P114 | D46 => P113 | D47 => P112 | D48 => P111 | D49 => P110 | D50 => P109 | D51 => P108 | D52 => P107 | D53 => P106 | D54 => P105 | D55 => P104 | D56 => P103 | D57 => P102 | D58 => P101 | D59 => P100 | D60 => P99 | D61 => P98 | D62 => P97 | D63 => P96 end
  | D33 => match b with D0 => P32 | D1 => P31 | D2 => P30 | D3 => P29 | D4 => P28 | D5 => P27 | D6 => P26 | D7 => P25 | D8 => P24 | D9 => P23 | D10 => P22 | D11 => P21 | D12 => P20 | D13 => P19 | D14 => P18 | D15 => P17 | D16 => P16 | D17 => P15 | D18 => P14 | D19 => P13 | D20 => P12 | D21 => P11 | D22 => P10 | D23 => P9 | D24 => P8 | D25 => P7 | D26 => P6 | D27 => P5 | D28 => P4 | D29 => P3 | D30 => P2 | D31 => P1 | D32 => P0 | D33 => P127 | D34 => P126 | D35 => P125 | D36 => P124 | D37 => P123 | D38 => P122 | D39 => P121 | D40 => P120 | D41 => P119 | D42 => P118 | D43 => P117 | D44 => P116 | D45 => P115 | D46 => P114 | D47 => P113 | D48 => P112 | D49 => P111 | D50 => P110 | D51 => P109 | D52 => P108 | D53 => P107 | D54 => P106 | D55 => P105 | D56 => P104 | D57 => P103 | D58 => P102 | D59 => P101 | D60 => P100 | D61 => P99 | D62 => P98 | D63 => P97 end
  | D34 => match b with D0 => P33 | D1 => P32 | D2 => P31 | D3 => P30 | D4 => P29 | D5 => P28 | D6 => P27 | D7 => P26 | D8 => P25 | D9 => P24 | D10 => P23 | D11 => P22 | D12 => P21 | D13 => P20 | D14 => P19 | D15 => P18 | D16 => P17 | D17 => P16 | D18 => P15 | D19 => P14 | D20 => P13 | D21 => P12 | D22 => P11 | D23 => P10 | D24 => P9 | D25 => P8 | D26 => P7 | D27 => P6 | D28 => P5 | D29 => P4 | D30 => P3 | D31 => P2 | D32 => P1 | D33 => P0 | D34 => P127 | D35 => P126 | D36 => P125 | D37 => P124 | D38 => P123 | D39 => P122 | D40 => P121 | D41 => P120 | D42 => P119 | D43 => P118 | D44 => P117 | D45 => P116 | D46 => P115 | D47 => P114 | D48 => P113 | D49 => P112 | D50 => P111 | D51 => P110 | D52 => P109 | D53 => P108 | D54 => P107 | D55 => P106 | D56 => P105 | D57 => P104 | D58 => P103 | D59 => P102 | D60 => P101 | D61 => P100 | D62 => P99 | D63 => P98 end
  | D35 => match b with D0 => P34 | D1 => P33 | D2 => P32 | D3 => P31 | D4 => P30 | D5 => P29 | D6 => P28 | D7 => P27 | D8 => P26 | D9 => P25 | D10 => P24 | D11 => P23 | D12 => P22 | D13 => P21 | D14 => P20 | D15 => P19 | D16 => P18 | D17 => P17 | D18 => P16 | D19 => P15 | D20 => P14 | D21 => P13 | D22 => P12 | D23 => P11 | D24 => P10 | D25 => P9 | D26 => P8 | D27 => P7 | D28 => P6 | D29 => P5 | D30 => P4 | D31 => P3 | D32 => P2 | D33 => P1 | D34 => P0 | D35 => P127 | D36 => P126 | D37 => P125 | D38 => P124 | D39 => P123 | D40 => P122 | D41 => P121 | D42 => P120 | D43 => P119 | D44 => P118 | D45 => P117 | D46 => P116 | D47 => P115 | D48 => P114 | D49 => P113 | D50 => P112 | D51 => P111 | D52 => P110 | D53 => P109 | D54 => P108 | D55 => P107 | D56 => P106 | D57 => P105 | D58 => P104 | D59 => P103 | D60 => P102 | D61 => P101 | D62 => P100 | D63 => P99 end
  | D36 => match b with D0 => P35 | D1 => P34 | D2 => P33 | D3 => P32 | D4 => P31 | D5 => P30 | D6 => P29 | D7 => P28 | D8 => P27 | D9 => P26 | D10 => P25 | D11 => P24 | D12 => P23 | D13 => P22 | D14 => P21 | D15 => P20 | D16 => P19 | D17 => P18 | D18 => P17 | D19 => P16 | D20 => P15 | D21 => P14 | D22 => P13 | D23 => P12 | D24 => P11 | D25 => P10 | D26 => P9 | D27 => P8 | D28 => P7 | D29 => P6 | D30 => P5 | D31 => P4 | D32 => P3 | D33 => P2 | D34 => P1 | D35 => P0 | D36 => P127 | D37 => P126 | D38 => P125 | D39 => P124 | D40 => P123 | D41 => P122 | D42 => P121 | D43 => P120 | D44 => P119 | D45 => P118 | D46 => P117 | D47 => P116 | D48 => P115 | D49 => P114 | D50 => P113 | D51 => P112 | D52 => P111 | D53 => P110 | D54 => P109 | D55 => P108 | D56 => P107 | D57 => P106 | D58 => P105 | D59 => P104 | D60 => P103 | D61 => P102 | D62 => P101 | D63 => P100 end
  | D37 => match b with D0 => P36 | D1 => P35 | D2 => P34 | D3 => P33 | D4 => P32 | D5 => P31 | D6 => P30 | D7 => P29 | D8 => P28 | D9 => P27 | D10 => P26 | D11 => P25 | D12 => P24 | D13 => P23 | D14 => P22 | D15 => P21 | D16 => P20 | D17 => P19 | D18 => P18 | D19 => P17 | D20 => P16 | D21 => P15 | D22 => P14 | D23 => P13 | D24 => P12 | D25 => P11 | D26 => P10 | D27 => P9 | D28 => P8 | D29 => P7 | D30 => P6 | D31 => P5 | D32 => P4 | D33 => P3 | D34 => P2 | D35 => P1 | D36 => P0 | D37 => P127 | D38 => P126 | D39 => P125 | D40 => P124 | D41 => P123 | D42 => P122 | D43 => P121 | D44 => P120 | D45 => P119 | D46 => P118 | D47 => P117 | D48 => P116 | D49 => P115 | D50 => P114 | D51 => P113 | D52 => P112 | D53 => P111 | D54 => P110 | D55 => P109 | D56 => P108 | D57 => P107 | D58 => P106 | D59 => P105 | D60 => P104 | D61 => P103 | D62 => P102 | D63 => P101 end
  | D38 => match b with D0 => P37 | D1 => P36 | D2 => P35 | D3 => P34 | D4 => P33 | D5 => P32 | D6 => P31 | D7 => P30 | D8 => P29 | D9 => P28 | D10 => P27 | D11 => P26 | D12 => P25 | D13 => P24 | D14 => P23 | D15 => P22 | D16 => P21 | D17 => P20 | D18 => P19 | D19 => P18 | D20 => P17 | D21 => P16 | D22 => P15 | D23 => P14 | D24 => P13 | D25 => P12 | D26 => P11 | D27 => P10 | D28 => P9 | D29 => P8 | D30 => P7 | D31 => P6 | D32 => P5 | D33 => P4 | D34 => P3 | D35 => P2 | D36 => P1 | D37 => P0 | D38 => P127 | D39 => P126 | D40 => P125 | D41 => P124 | D42 => P123 | D43 => P122 | D44 => P121 | D45 => P120 | D46 => P119 | D47 => P118 | D48 => P117 | D49 => P116 | D50 => P115 | D51 => P114 | D52 => P113 | D53 => P112 | D54 => P111 | D55 => P110 | D56 => P109 | D57 => P108 | D58 => P107 | D59 => P106 | D60 => P105 | D61 => P104 | D62 => P103 | D63 => P102 end
  | D39 => match b with D0 => P38 | D1 => P37 | D2 => P36 | D3 => P35 | D4 => P34 | D5 => P33 | D6 => P32 | D7 => P31 | D8 => P30 | D9 => P29 | D10 => P28 | D11 => P27 | D12 => P26 | D13 => P25 | D14 => P24 | D15 => P23 | D16 => P22 | D17 => P21 | D18 => P20 | D19 => P19 | D20 => P18 | D21 => P17 | D22 => P16 | D23 => P15 | D24 => P14 | D25 => P13 | D26 => P12 | D27 => P11 | D28 => P10 | D29 => P9 | D30 => P8 | D31 => P7 | D32 => P6 | D33 => P5 | D34 => P4 | D35 => P3 | D36 => P2 | D37 => P1 | D38 => P0 | D39 => P127 | D40 => P126 | D41 => P125 | D42 => P124 | D43 => P123 | D44 => P122 | D45 => P121 | D46 => P120 | D47 => P119 | D48 => P118 | D49 => P117 | D50 => P116 | D51 => P115 | D52 => P114 | D53 => P113 | D54 => P112 | D55 => P111 | D56 => P110 | D57 => P109 | D58 => P108 | D59 => P107 | D60 => P106 | D61 => P105 | D62 => P104 | D63 => P103 end
  | D40 => match b with D0 => P39 | D1 => P38 | D2 => P37 | D3 => P36 | D4 => P35 | D5 => P34 | D6 => P33 | D7 => P32 | D8 => P31 | D9 => P30 | D10 => P29 | D11 => P28 | D12 => P27 | D13 => P26 | D14 => P25 | D15 => P24 | D16 => P23 | D17 => P22 | D18 => P21 | D19 => P20 | D20 => P19 | D21 => P18 | D22 => P17 | D23 => P16 | D24 => P15 | D25 => P14 | D26 => P13 | D27 => P12 | D28 => P11 | D29 => P10 | D30 => P9 | D31 => P8 | D32 => P7 | D33 => P6 | D34 => P5 | D35 => P4 | D36 => P3 | D37 => P2 | D38 => P1 | D39 => P0 | D40 => P127 | D41 => P126 | D42 => P125 | D43 => P124 | D44 => P123 | D45 => P122 | D46 => P121 | D47 => P120 | D48 => P119 | D49 => P118 | D50 => P117 | D51 => P116 | D52 => P115 | D53 => P114 | D54 => P113 | D55 => P112 | D56 => P111 | D57 => P110 | D58 => P109 | D59 => P108 | D60 => P107 | D61 => P106 | D62 => P105 | D63 => P104 end
  | D41 => match b with D0 => P40 | D1 => P39 | D2 => P38 | D3 => P37 | D4 => P36 | D5 => P35 | D6 => P34 | D7 => P33 | D8 => P32 | D9 => P31 | D10 => P30 | D11 => P29 | D12 => P28 | D13 => P27 | D14 => P26 | D15 => P25 | D16 => P24 | D17 => P23 | D18 => P22 | D19 => P21 | D20 => P20 | D21 => P19 | D22 => P18 | D23 => P17 | D24 => P16 | D25 => P15 | D26 => P14 | D27 => P13 | D28 => P12 | D29 => P11 | D30 => P10 | D31 => P9 | D32 => P8 | D33 => P7 | D34 => P6 | D35 => P5 | D36 => P4 | D37 => P3 | D38 => P2 | D39 => P1 | D40 => P0 | D41 => P127 | D42 => P126 | D43 => P125 | D44 => P124 | D45 => P123 | D46 => P122 | D47 => P121 | D48 => P120 | D49 => P119 | D50 => P118 | D51 => P117 | D52 => P116 | D53 => P115 | D54 => P114 | D55 => P113 | D56 => P112 | D57 => P111 | D58 => P110 | D59 => P109 | D60 => P108 | D61 => P107 | D62 => P106 | D63 => P105 end
  | D42 => match b with D0 => P41 | D1 => P40 | D2 => P39 | D3 => P38 | D4 => P37 | D5 => P36 | D6 => P35 | D7 => P34 | D8 => P33 | D9 => P32 | D10 => P31 | D11 => P30 | D12 => P29 | D13 => P28 | D14 => P27 | D15 => P26 | D16 => P25 | D17 => P24 | D18 => P23 | D19 => P22 | D20 => P21 | D21 => P20 | D22 => P19 | D23 => P18 | D24 => P17 | D25 => P16 | D26 => P15 | D27 => P14 | D28 => P13 | D29 => P12 | D30 => P11 | D31 => P10 | D32 => P9 | D33 => P8 | D34 => P7 | D35 => P6 | D36 => P5 | D37 => P4 | D38 => P3 | D39 => P2 | D40 => P1 | D41 => P0 | D42 => P127 | D43 => P126 | D44 => P125 | D45 => P124 | D46 => P123 | D47 => P122 | D48 => P121 | D49 => P120 | D50 => P119 | D51 => P118 | D52 => P117 | D53 => P116 | D54 => P115 | D55 => P114 | D56 => P113 | D57 => P112 | D58 => P111 | D59 => P110 | D60 => P109 | D61 => P108 | D62 => P107 | D63 => P106 end
  | D43 => match b with D0 => P42 | D1 => P41 | D2 => P40 | D3 => P39 | D4 => P38 | D5 => P37 | D6 => P36 | D7 => P35 | D8 => P34 | D9 => P33 | D10 => P32 | D11 => P31 | D12 => P30 | D13 => P29 | D14 => P28 | D15 => P27 | D16 => P26 | D17 => P25 | D18 => P24 | D19 => P23 | D20 => P22 | D21 => P21 | D22 => P20 | D23 => P19 | D24 => P18 | D25 => P17 | D26 => P16 | D27 => P15 | D28 => P14 | D29 => P13 | D30 => P12 | D31 => P11 | D32 => P10 | D33 => P9 | D34 => P8 | D35 => P7 | D36 => P6 | D37 => P5 | D38 => P4 | D39 => P3 | D40 => P2 | D41 => P1 | D42 => P0 | D43 => P127 | D44 => P126 | D45 => P125 | D46 => P124 | D47 => P123 | D48 => P122 | D49 => P121 | D50 => P120 | D51 => P119 | D52 => P118 | D53 => P117 | D54 => P116 | D55 => P115 | D56 => P114 | D57 => P113 | D58 => P112 | D59 => P111 | D60 => P110 | D61 => P109 | D62 => P108 | D63 => P107 end
  | D44 => match b with D0 => P43 | D1 => P42 | D2 => P41 | D3 => P40 | D4 => P39 | D5 => P38 | D6 => P37 | D7 => P36 | D8 => P35 | D9 => P34 | D10 => P33 | D11 => P32 | D12 => P31 | D13 => P30 | D14 => P29 | D15 => P28 | D16 => P27 | D17 => P26 | D18 => P25 | D19 => P24 | D20 => P23 | D21 => P22 | D22 => P21 | D23 => P20 | D24 => P19 | D25 => P18 | D26 => P17 | D27 => P16 | D28 => P15 | D29 => P14 | D30 => P13 | D31 => P12 | D32 => P11 | D33 => P10 | D34 => P9 | D35 => P8 | D36 => P7 | D37 => P6 | D38 => P5 | D39 => P4 | D40 => P3 | D41 => P2 | D42 => P1 | D43 => P0 | D44 => P127 | D45 => P126 | D46 => P125 | D47 => P124 | D48 => P123 | D49 => P122 | D50 => P121 | D51 => P120 | D52 => P119 | D53 => P118 | D54 => P117 | D55 => P116 | D56 => P115 | D57 => P114 | D58 => P113 | D59 => P112 | D60 => P111 | D61 => P110 | D62 => P109 | D63 => P108 end
  | D45 => match b with D0 => P44 | D1 => P43 | D2 => P42 | D3 => P41 | D4 => P40 | D5 => P39 | D6 => P38 | D7 => P37 | D8 => P36 | D9 => P35 | D10 => P34 | D11 => P33 | D12 => P32 | D13 => P31 | D14 => P30 | D15 => P29 | D16 => P28 | D17 => P27 | D18 => P26 | D19 => P25 | D20 => P24 | D21 => P23 | D22 => P22 | D23 => P21 | D24 => P20 | D25 => P19 | D26 => P18 | D27 => P17 | D28 => P16 | D29 => P15 | D30 => P14 | D31 => P13 | D32 => P12 | D33 => P11 | D34 => P10 | D35 => P9 | D36 => P8 | D37 => P7 | D38 => P6 | D39 => P5 | D40 => P4 | D41 => P3 | D42 => P2 | D43 => P1 | D44 => P0 | D45 => P127 | D46 => P126 | D47 => P125 | D48 => P124 | D49 => P123 | D50 => P122 | D51 => P121 | D52 => P120 | D53 => P119 | D54 => P118 | D55 => P117 | D56 => P116 | D57 => P115 | D58 => P114 | D59 => P113 | D60 => P112 | D61 => P111 | D62 => P110 | D63 => P109 end
  | D46 => match b with D0 => P45 | D1 => P44 | D2 => P43 | D3 => P42 | D4 => P41 | D5 => P40 | D6 => P39 | D7 => P38 | D8 => P37 | D9 => P36 | D10 => P35 | D11 => P34 | D12 => P33 | D13 => P32 | D14 => P31 | D15 => P30 | D16 => P29 | D17 => P28 | D18 => P27 | D19 => P26 | D20 => P25 | D21 => P24 | D22 => P23 | D23 => P22 | D24 => P21 | D25 => P20 | D26 => P19 | D27 => P18 | D28 => P17 | D29 => P16 | D30 => P15 | D31 => P14 | D32 => P13 | D33 => P12 | D34 => P11 | D35 => P10 | D36 => P9 | D37 => P8 | D38 => P7 | D39 => P6 | D40 => P5 | D41 => P4 | D42 => P3 | D43 => P2 | D44 => P1 | D45 => P0 | D46 => P127 | D47 => P126 | D48 => P125 | D49 => P124 | D50 => P123 | D51 => P122 | D52 => P121 | D53 => P120 | D54 => P119 | D55 => P118 | D56 => P117 | D57 => P116 | D58 => P115 | D59 => P114 | D60 => P113 | D61 => P112 | D62 => P111 | D63 => P110 end
  | D47 => match b with D0 => P46 | D1 => P45 | D2 => P44 | D3 => P43 | D4 => P42 | D5 => P41 | D6 => P40 | D7 => P39 | D8 => P38 | D9 => P37 | D10 => P36 | D11 => P35 | D12 => P34 | D13 => P33 | D14 => P32 | D15 => P31 | D16 => P30 | D17 => P29 | D18 => P28 | D19 => P27 | D20 => P26 | D21 => P25 | D22 => P24 | D23 => P23 | D24 => P22 | D25 => P21 | D26 => P20 | D27 => P19 | D28 => P18 | D29 => P17 | D30 => P16 | D31 => P15 | D32 => P14 | D33 => P13 | D34 => P12 | D35 => P11 | D36 => P10 | D37 => P9 | D38 => P8 | D39 => P7 | D40 => P6 | D41 => P5 | D42 => P4 | D43 => P3 | D44 => P2 | D45 => P1 | D46 => P0 | D47 => P127 | D48 => P126 | D49 => P125 | D50 => P124 | D51 => P123 | D52 => P122 | D53 => P121 | D54 => P120 | D55 => P119 | D56 => P118 | D57 => P117 | D58 => P116 | D59 => P115 | D60 => P114 | D61 => P113 | D62 => P112 | D63 => P111 end
  | D48 => match b with D0 => P47 | D1 => P46 | D2 => P45 | D3 => P44 | D4 => P43 | D5 => P42 | D6 => P41 | D7 => P40 | D8 => P39 | D9 => P38 | D10 => P37 | D11 => P36 | D12 => P35 | D13 => P34 | D14 => P33 | D15 => P32 | D16 => P31 | D17 => P30 | D18 => P29 | D19 => P28 | D20 => P27 | D21 => P26 | D22 => P25 | D23 => P24 | D24 => P23 | D25 => P22 | D26 => P21 | D27 => P20 | D28 => P19 | D29 => P18 | D30 => P17 | D31 => P16 | D32 => P15 | D33 => P14 | D34 => P13 | D35 => P12 | D36 => P11 | D37 => P10 | D38 => P9 | D39 => P8 | D40 => P7 | D41 => P6 | D42 => P5 | D43 => P4 | D44 => P3 | D45 => P2 | D46 => P1 | D47 => P0 | D48 => P127 | D49 => P126 | D50 => P125 | D51 => P124 | D52 => P123 | D53 => P122 | D54 => P121 | D55 => P120 | D56 => P119 | D57 => P118 | D58 => P117 | D59 => P116 | D60 => P115 | D61 => P114 | D62 => P113 | D63 => P112 end
  | D49 => match b with D0 => P48 | D1 => P47 | D2 => P46 | D3 => P45 | D4 => P44 | D5 => P43 | D6 => P42 | D7 => P41 | D8 => P40 | D9 => P39 | D10 => P38 | D11 => P37 | D12 => P36 | D13 => P35 | D14 => P34 | D15 => P33 | D16 => P32 | D17 => P31 | D18 => P30 | D19 => P29 | D20 => P28 | D21 => P27 | D22 => P26 | D23 => P25 | D24 => P24 | D25 => P23 | D26 => P22 | D27 => P21 | D28 => P20 | D29 => P19 | D30 => P18 | D31 => P17 | D32 => P16 | D33 => P15 | D34 => P14 | D35 => P13 | D36 => P12 | D37 => P11 | D38 => P10 | D39 => P9 | D40 => P8 | D41 => P7 | D42 => P6 | D43 => P5 | D44 => P4 | D45 => P3 | D46 => P2 | D47 => P1 | D48 => P0 | D49 => P127 | D50 => P126 | D51 => P125 | D52 => P124 | D53 => P123 | D54 => P122 | D55 => P121 | D56 => P120 | D57 => P119 | D58 => P118 | D59 => P117 | D60 => P116 | D61 => P115 | D62 => P114 | D63 => P113 end
  | D50 => match b with D0 => P49 | D1 => P48 | D2 => P47 | D3 => P46 | D4 => P45 | D5 => P44 | D6 => P43 | D7 => P42 | D8 => P41 | D9 => P40 | D10 => P39 | D11 => P38 | D12 => P37 | D13 => P36 | D14 => P35 | D15 => P34 | D16 => P33 | D17 => P32 | D18 => P31 | D19 => P30 | D20 => P29 | D21 => P28 | D22 => P27 | D23 => P26 | D24 => P25 | D25 => P24 | D26 => P23 | D27 => P22 | D28 => P21 | D29 => P20 | D30 => P19 | D31 => P18 | D32 => P17 | D33 => P16 | D34 => P15 | D35 => P14 | D36 => P13 | D37 => P12 | D38 => P11 | D39 => P10 | D40 => P9 | D41 => P8 | D42 => P7 | D43 => P6 | D44 => P5 | D45 => P4 | D46 => P3 | D47 => P2 | D48 => P1 | D49 => P0 | D50 => P127 | D51 => P126 | D52 => P125 | D53 => P124 | D54 => P123 | D55 => P122 | D56 => P121 | D57 => P120 | D58 => P119 | D59 => P118 | D60 => P117 | D61 => P116 | D62 => P115 | D63 => P114 end
  | D51 => match b with D0 => P50 | D1 => P49 | D2 => P48 | D3 => P47 | D4 => P46 | D5 => P45 | D6 => P44 | D7 => P43 | D8 => P42 | D9 => P41 | D10 => P40 | D11 => P39 | D12 => P38 | D13 => P37 | D14 => P36 | D15 => P35 | D16 => P34 | D17 => P33 | D18 => P32 | D19 => P31 | D20 => P30 | D21 => P29 | D22 => P28 | D23 => P27 | D24 => P26 | D25 => P25 | D26 => P24 | D27 => P23 | D28 => P22 | D29 => P21 | D30 => P20 | D31 => P19 | D32 => P18 | D33 => P17 | D34 => P16 | D35 => P15 | D36 => P14 | D37 => P13 | D38 => P12 | D39 => P11 | D40 => P10 | D41 => P9 | D42 => P8 | D43 => P7 | D44 => P6 | D45 => P5 | D46 => P4 | D47 => P3 | D48 => P2 | D49 => P1 | D50 => P0 | D51 => P127 | D52 => P126 | D53 => P125 | D54 => P124 | D55 => P123 | D56 => P122 | D57 => P121 | D58 => P120 | D59 => P119 | D60 => P118 | D61 => P117 | D62 => P116 | D63 => P115 end
  | D52 => match b with D0 => P51 | D1 => P50 | D2 => P49 | D3 => P48 | D4 => P47 | D5 => P46 | D6 => P45 | D7 => P44 | D8 => P43 | D9 => P42 | D10 => P41 | D11 => P40 | D12 => P39 | D13 => P38 | D14 => P37 | D15 => P36 | D16 => P35 | D17 => P34 | D18 => P33 | D19 => P32 | D20 => P31 | D21 => P30 | D22 => P29 | D23 => P28 | D24 => P27 | D25 => P26 | D26 => P25 | D27 => P24 | D28 => P23 | D29 => P22 | D30 => P21 | D31 => P20 | D32 => P19 | D33 => P18 | D34 => P17 | D35 => P16 | D36 => P15 | D37 => P14 | D38 => P13 | D39 => P12 | D40 => P11 | D41 => P10 | D42 => P9 | D43 => P8 | D44 => P7 | D45 => P6 | D46 => P5 | D47 => P4 | D48 => P3 | D49 => P2 | D50 => P1 | D51 => P0 | D52 => P127 | D53 => P126 | D54 => P125 | D55 => P124 | D56 => P123 | D57 => P122 | D58 => P121 | D59 => P120 | D60 => P119 | D61 => P118 | D62 => P117 | D63 => P116 end
  | D53 => match b with D0 => P52 | D1 => P51 | D2 => P50 | D3 => P49 | D4 => P48 | D5 => P47 | D6 => P46 | D7 => P45 | D8 => P44 | D9 => P43 | D10 => P42 | D11 => P41 | D12 => P40 | D13 => P39 | D14 => P38 | D15 => P37 | D16 => P36 | D17 => P35 | D18 => P34 | D19 => P33 | D20 => P32 | D21 => P31 | D22 => P30 | D23 => P29 | D24 => P28 | D25 => P27 | D26 => P26 | D27 => P25 | D28 => P24 | D29 => P23 | D30 => P22 | D31 => P21 | D32 => P20 | D33 => P19 | D34 => P18 | D35 => P17 | D36 => P16 | D37 => P15 | D38 => P14 | D39 => P13 | D40 => P12 | D41 => P11 | D42 => P10 | D43 => P9 | D44 => P8 | D45 => P7 | D46 => P6 | D47 => P5 | D48 => P4 | D49 => P3 | D50 => P2 | D51 => P1 | D52 => P0 | D53 => P127 | D54 => P126 | D55 => P125 | D56 => P124 | D57 => P123 | D58 => P122 | D59 => P121 | D60 => P120 | D61 => P119 | D62 => P118 | D63 => P117 end
  | D54 => match b with D0 => P53 | D1 => P52 | D2 => P51 | D3 => P50 | D4 => P49 | D5 => P48 | D6 => P47 | D7 => P46 | D8 => P45 | D9 => P44 | D10 => P43 | D11 => P42 | D12 => P41 | D13 => P40 | D14 => P39 | D15 => P38 | D16 => P37 | D17 => P36 | D18 => P35 | D19 => P34 | D20 => P33 | D21 => P32 | D22 => P31 | D23 => P30 | D24 => P29 | D25 => P28 | D26 => P27 | D27 => P26 | D28 => P25 | D29 => P24 | D30 => P23 | D31 => P22 | D32 => P21 | D33 => P20 | D34 => P19 | D35 => P18 | D36 => P17 | D37 => P16 | D38 => P15 | D39 => P14 | D40 => P13 | D41 => P12 | D42 => P11 | D43 => P10 | D44 => P9 | D45 => P8 | D46 => P7 | D47 => P6 | D48 => P5 | D49 => P4 | D50 => P3 | D51 => P2 | D52 => P1 | D53 => P0 | D54 => P127 | D55 => P126 | D56 => P125 | D57 => P124 | D58 => P123 | D59 => P122 | D60 => P121 | D61 => P120 | D62 => P119 | D63 => P118 end
  | D55 => match b with D0 => P54 | D1 => P53 | D2 => P52 | D3 => P51 | D4 => P50 | D5 => P49 | D6 => P48 | D7 => P47 | D8 => P46 | D9 => P45 | D10 => P44 | D11 => P43 | D12 => P42 | D13 => P41 | D14 => P40 | D15 => P39 | D16 => P38 | D17 => P37 | D18 => P36 | D19 => P35 | D20 => P34 | D21 => P33 | D22 => P32 | D23 => P31 | D24 => P30 | D25 => P29 | D26 => P28 | D27 => P27 | D28 => P26 | D29 => P25 | D30 => P24 | D31 => P23 | D32 => P22 | D33 => P21 | D34 => P20 | D35 => P19 | D36 => P18 | D37 => P17 | D38 => P16 | D39 => P15 | D40 => P14 | D41 => P13 | D42 => P12 | D43 => P11 | D44 => P10 | D45 => P9 | D46 => P8 | D47 => P7 | D48 => P6 | D49 => P5 | D50 => P4 | D51 => P3 | D52 => P2 | D53 => P1 | D54 => P0 | D55 => P127 | D56 => P126 | D57 => P125 | D58 => P124 | D59 => P123 | D60 => P122 | D61 => P121 | D62 => P120 | D63 => P119 end
  | D56 => match b with D0 => P55 | D1 => P54 | D2 => P53 | D3 => P52 | D4 => P51 | D5 => P50 | D6 => P49 | D7 => P48 | D8 => P47 | D9 => P46 | D10 => P45 | D11 => P44 | D12 => P43 | D13 => P42 | D14 => P41 | D15 => P40 | D16 => P39 | D17 => P38 | D18 => P37 | D19 => P36 | D20 => P35 | D21 => P34 | D22 => P33 | D23 => P32 | D24 => P31 | D25 => P30 | D26 => P29 | D27 => P28 | D28 => P27 | D29 => P26 | D30 => P25 | D31 => P24 | D32 => P23 | D33 => P22 | D34 => P21 | D35 => P20 | D36 => P19 | D37 => P18 | D38 => P17 | D39 => P16 | D40 => P15 | D41 => P14 | D42 => P13 | D43 => P12 | D44 => P11 | D45 => P10 | D46 => P9 | D47 => P8 | D48 => P7 | D49 => P6 | D50 => P5 | D51 => P4 | D52 => P3 | D53 => P2 | D54 => P1 | D55 => P0 | D56 => P127 | D57 => P126 | D58 => P125 | D59 => P124 | D60 => P123 | D61 => P122 | D62 => P121 | D63 => P120 end
  | D57 => match b with D0 => P56 | D1 => P55 | D2 => P54 | D3 => P53 | D4 => P52 | D5 => P51 | D6 => P50 | D7 => P49 | D8 => P48 | D9 => P47 | D10 => P46 | D11 => P45 | D12 => P44 | D13 => P43 | D14 => P42 | D15 => P41 | D16 => P40 | D17 => P39 | D18 => P38 | D19 => P37 | D20 => P36 | D21 => P35 | D22 => P34 | D23 => P33 | D24 => P32 | D25 => P31 | D26 => P30 | D27 => P29 | D28 => P28 | D29 => P27 | D30 => P26 | D31 => P25 | D32 => P24 | D33 => P23 | D34 => P22 | D35 => P21 | D36 => P20 | D37 => P19 | D38 => P18 | D39 => P17 | D40 => P16 | D41 => P15 | D42 => P14 | D43 => P13 | D44 => P12 | D45 => P11 | D46 => P10 | D47 => P9 | D48 => P8 | D49 => P7 | D50 => P6 | D51 => P5 | D52 => P4 | D53 => P3 | D54 => P2 | D55 => P1 | D56 => P0 | D57 => P127 | D58 => P126 | D59 => P125 | D60 => P124 | D61 => P123 | D62 => P122 | D63 => P121 end
  | D58 => match b with D0 => P57 | D1 => P56 | D2 => P55 | D3 => P54 | D4 => P53 | D5 => P52 | D6 => P51 | D7 => P50 | D8 => P49 | D9 => P48 | D10 => P47 | D11 => P46 | D12 => P45 | D13 => P44 | D14 => P43 | D15 => P42 | D16 => P41 | D17 => P40 | D18 => P39 | D19 => P38 | D20 => P37 | D21 => P36 | D22 => P35 | D23 => P34 | D24 => P33 | D25 => P32 | D26 => P31 | D27 => P30 | D28 => P29 | D29 => P28 | D30 => P27 | D31 => P26 | D32 => P25 | D33 => P24 | D34 => P23 | D35 => P22 | D36 => P21 | D37 => P20 | D38 => P19 | D39 => P18 | D40 => P17 | D41 => P16 | D42 => P15 | D43 => P14 | D44 => P13 | D45 => P12 | D46 => P11 | D47 => P10 | D48 => P9 | D49 => P8 | D50 => P7 | D51 => P6 | D52 => P5 | D53 => P4 | D54 => P3 | D55 => P2 | D56 => P1 | D57 => P0 | D58 => P127 | D59 => P126 | D60 => P125 | D61 => P124 | D62 => P123 | D63 => P122 end
  | D59 => match b with D0 => P58 | D1 => P57 | D2 => P56 | D3 => P55 | D4 => P54 | D5 => P53 | D6 => P52 | D7 => P51 | D8 => P50 | D9 => P49 | D10 => P48 | D11 => P47 | D12 => P46 | D13 => P45 | D14 => P44 | D15 => P43 | D16 => P42 | D17 => P41 | D18 => P40 | D19 => P39 | D20 => P38 | D21 => P37 | D22 => P36 | D23 => P35 | D24 => P34 | D25 => P33 | D26 => P32 | D27 => P31 | D28 => P30 | D29 => P29 | D30 => P28 | D31 => P27 | D32 => P26 | D33 => P25 | D34 => P24 | D35 => P23 | D36 => P22 | D37 => P21 | D38 => P20 | D39 => P19 | D40 => P18 | D41 => P17 | D42 => P16 | D43 => P15 | D44 => P14 | D45 => P13 | D46 => P12 | D47 => P11 | D48 => P10 | D49 => P9 | D50 => P8 | D51 => P7 | D52 => P6 | D53 => P5 | D54 => P4 | D55 => P3 | D56 => P2 | D57 => P1 | D58 => P0 | D59 => P127 | D60 => P126 | D61 => P125 | D62 => P124 | D63 => P123 end
  | D60 => match b with D0 => P59 | D1 => P58 | D2 => P57 | D3 => P56 | D4 => P55 | D5 => P54 | D6 => P53 | D7 => P52 | D8 => P51 | D9 => P50 | D10 => P49 | D11 => P48 | D12 => P47 | D13 => P46 | D14 => P45 | D15 => P44 | D16 => P43 | D17 => P42 | D18 => P41 | D19 => P40 | D20 => P39 | D21 => P38 | D22 => P37 | D23 => P36 | D24 => P35 | D25 => P34 | D26 => P33 | D27 => P32 | D28 => P31 | D29 => P30 | D30 => P29 | D31 => P28 | D32 => P27 | D33 => P26 | D34 => P25 | D35 => P24 | D36 => P23 | D37 => P22 | D38 => P21 | D39 => P20 | D40 => P19 | D41 => P18 | D42 => P17 | D43 => P16 | D44 => P15 | D45 => P14 | D46 => P13 | D47 => P12 | D48 => P11 | D49 => P10 | D50 => P9 | D51 => P8 | D52 => P7 | D53 => P6 | D54 => P5 | D55 => P4 | D56 => P3 | D57 => P2 | D58 => P1 | D59 => P0 | D60 => P127 | D61 => P126 | D62 => P125 | D63 => P124 end
  | D61 => match b with D0 => P60 | D1 => P59 | D2 => P58 | D3 => P57 | D4 => P56 | D5 => P55 | D6 => P54 | D7 => P53 | D8 => P52 | D9 => P51 | D10 => P50 | D11 => P49 | D12 => P48 | D13 => P47 | D14 => P46 | D15 => P45 | D16 => P44 | D17 => P43 | D18 => P42 | D19 => P41 | D20 => P40 | D21 => P39 | D22 => P38 | D23 => P37 | D24 => P36 | D25 => P35 | D26 => P34 | D27 => P33 | D28 => P32 | D29 => P31 | D30 => P30 | D31 => P29 | D32 => P28 | D33 => P27 | D34 => P26 | D35 => P25 | D36 => P24 | D37 => P23 | D38 => P22 | D39 => P21 | D40 => P20 | D41 => P19 | D42 => P18 | D43 => P17 | D44 => P16 | D45 => P15 | D46 => P14 | D47 => P13 | D48 => P12 | D49 => P11 | D50 => P10 | D51 => P9 | D52 => P8 | D53 => P7 | D54 => P6 | D55 => P5 | D56 => P4 | D57 => P3 | D58 => P2 | D59 => P1 | D60 => P0 | D61 => P127 | D62 => P126 | D63 => P125 end
  | D62 => match b with D0 => P61 | D1 => P60 | D2 => P59 | D3 => P58 | D4 => P57 | D5 => P56 | D6 => P55 | D7 => P54 | D8 => P53 | D9 => P52 | D10 => P51 | D11 => P50 | D12 => P49 | D13 => P48 | D14 => P47 | D15 => P46 | D16 => P45 | D17 => P44 | D18 => P43 | D19 => P42 | D20 => P41 | D21 => P40 | D22 => P39 | D23 => P38 | D24 => P37 | D25 => P36 | D26 => P35 | D27 => P34 | D28 => P33 | D29 => P32 | D30 => P31 | D31 => P30 | D32 => P29 | D33 => P28 | D34 => P27 | D35 => P26 | D36 => P25 | D37 => P24 | D38 => P23 | D39 => P22 | D40 => P21 | D41 => P20 | D42 => P19 | D43 => P18 | D44 => P17 | D45 => P16 | D46 => P15 | D47 => P14 | D48 => P13 | D49 => P12 | D50 => P11 | D51 => P10 | D52 => P9 | D53 => P8 | D54 => P7 | D55 => P6 | D56 => P5 | D57 => P4 | D58 => P3 | D59 => P2 | D60 => P1 | D61 => P0 | D62 => P127 | D63 => P126 end
  | D63 => match b with D0 => P62 | D1 => P61 | D2 => P60 | D3 => P59 | D4 => P58 | D5 => P57 | D6 => P56 | D7 => P55 | D8 => P54 | D9 => P53 | D10 => P52 | D11 => P51 | D12 => P50 | D13 => P49 | D14 => P48 | D15 => P47 | D16 => P46 | D17 => P45 | D18 => P44 | D19 => P43 | D20 => P42 | D21 => P41 | D22 => P40 | D23 => P39 | D24 => P38 | D25 => P37 | D26 => P36 | D27 => P35 | D28 => P34 | D29 => P33 | D30 => P32 | D31 => P31 | D32 => P30 | D33 => P29 | D34 => P28 | D35 => P27 | D36 => P26 | D37 => P25 | D38 => P24 | D39 => P23 | D40 => P22 | D41 => P21 | D42 => P20 | D43 => P19 | D44 => P18 | D45 => P17 | D46 => P16 | D47 => P15 | D48 => P14 | D49 => P13 | D50 => P12 | D51 => P11 | D52 => P10 | D53 => P9 | D54 => P8 | D55 => P7 | D56 => P6 | D57 => P5 | D58 => P4 | D59 => P3 | D60 => P2 | D61 => P1 | D62 => P0 | D63 => P127 end
  end else match a with
  | D0 => match b with D0 => P0 | D1 => P127 | D2 => P126 | D3 => P125 | D4 => P124 | D5 => P123 | D6 => P122 | D7 => P121 | D8 => P120 | D9 => P119 | D10 => P118 | D11 => P117 | D12 => P116 | D13 => P115 | D14 => P114 | D15 => P113 | D16 => P112 | D17 => P111 | D18 => P110 | D19 => P109 | D20 => P108 | D21 => P107 | D22 => P106 | D23 => P105 | D24 => P104 | D25 => P103 | D26 => P102 | D27 => P101 | D28 => P100 | D29 => P99 | D30 => P98 | D31 => P97 | D32 => P96 | D33 => P95 | D34 => P94 | D35 => P93 | D36 => P92 | D37 => P91 | D38 => P90 | D39 => P89 | D40 => P88 | D41 => P87 | D42 => P86 | D43 => P85 | D44 => P84 | D45 => P83 | D46 => P82 | D47 => P81 | D48 => P80 | D49 => P79 | D50 => P78 | D51 => P77 | D52 => P76 | D53 => P75 | D54 => P74 | D55 => P73 | D56 => P72 | D57 => P71 | D58 => P70 | D59 => P69 | D60 => P68 | D61 => P67 | D62 => P66 | D63 => P65 end
  | D1 => match b with D0 => P1 | D1 => P0 | D2 => P127 | D3 => P126 | D4 => P125 | D5 => P124 | D6 => P123 | D7 => P122 | D8 => P121 | D9 => P120 | D10 => P119 | D11 => P118 | D12 => P117 | D13 => P116 | D14 => P115 | D15 => P114 | D16 => P113 | D17 => P112 | D18 => P111 | D19 => P110 | D20 => P109 | D21 => P108 | D22 => P107 | D23 => P106 | D24 => P105 | D25 => P104 | D26 => P103 | D27 => P102 | D28 => P101 | D29 => P100 | D30 => P99 | D31 => P98 | D32 => P97 | D33 => P96 | D34 => P95 | D35 => P94 | D36 => P93 | D37 => P92 | D38 => P91 | D39 => P90 | D40 => P89 | D41 => P88 | D42 => P87 | D43 => P86 | D44 => P85 | D45 => P84 | D46 => P83 | D47 => P82 | D48 => P81 | D49 => P80 | D50 => P79 | D51 => P78 | D52 => P77 | D53 => P76 | D54 => P75 | D55 => P74 | D56 => P73 | D57 => P72 | D58 => P71 | D59 => P70 | D60 => P69 | D61 => P68 | D62 => P67 | D63 => P66 end
  | D2 => match b with D0 => P2 | D1 => P1 | D2 => P0 | D3 => P127 | D4 => P126 | D5 => P125 | D6 => P124 | D7 => P123 | D8 => P122 | D9 => P121 | D10 => P120 | D11 => P119 | D12 => P118 | D13 => P117 | D14 => P116 | D15 => P115 | D16 => P114 | D17 => P113 | D18 => P112 | D19 => P111 | D20 => P110 | D21 => P109 | D22 => P108 | D23 => P107 | D24 => P106 | D25 => P105 | D26 => P104 | D27 => P103 | D28 => P102 | D29 => P101 | D30 => P100 | D31 => P99 | D32 => P98 | D33 => P97 | D34 => P96 | D35 => P95 | D36 => P94 | D37 => P93 | D38 => P92 | D39 => P91 | D40 => P90 | D41 => P89 | D42 => P88 | D43 => P87 | D44 => P86 | D45 => P85 | D46 => P84 | D47 => P83 | D48 => P82 | D49 => P81 | D50 => P80 | D51 => P79 | D52 => P78 | D53 => P77 | D54 => P76 | D55 => P75 | D56 => P74 | D57 => P73 | D58 => P72 | D59 => P71 | D60 => P70 | D61 => P69 | D62 => P68 | D63 => P67 end
  | D3 => match b with D0 => P3 | D1 => P2 | D2 => P1 | D3 => P0 | D4 => P127 | D5 => P126 | D6 => P125 | D7 => P124 | D8 => P123 | D9 => P122 | D10 => P121 | D11 => P120 | D12 => P119 | D13 => P118 | D14 => P117 | D15 => P116 | D16 => P115 | D17 => P114 | D18 => P113 | D19 => P112 | D20 => P111 | D21 => P110 | D22 => P109 | D23 => P108 | D24 => P107 | D25 => P106 | D26 => P105 | D27 => P104 | D28 => P103 | D29 => P102 | D30 => P101 | D31 => P100 | D32 => P99 | D33 => P98 | D34 => P97 | D35 => P96 | D36 => P95 | D37 => P94 | D38 => P93 | D39 => P92 | D40 => P91 | D41 => P90 | D42 => P89 | D43 => P88 | D44 => P87 | D45 => P86 | D46 => P85 | D47 => P84 | D48 => P83 | D49 => P82 | D50 => P81 | D51 => P80 | D52 => P79 | D53 => P78 | D54 => P77 | D55 => P76 | D56 => P75 | D57 => P74 | D58 => P73 | D59 => P72 | D60 => P71 | D61 => P70 | D62 => P69 | D63 => P68 end
  | D4 => match b with D0 => P4 | D1 => P3 | D2 => P2 | D3 => P1 | D4 => P0 | D5 => P127 | D6 => P126 | D7 => P125 | D8 => P124 | D9 => P123 | D10 => P122 | D11 => P121 | D12 => P120 | D13 => P119 | D14 => P118 | D15 => P117 | D16 => P116 | D17 => P115 | D18 => P114 | D19 => P113 | D20 => P112 | D21 => P111 | D22 => P110 | D23 => P109 | D24 => P108 | D25 => P107 | D26 => P106 | D27 => P105 | D28 => P104 | D29 => P103 | D30 => P102 | D31 => P101 | D32 => P100 | D33 => P99 | D34 => P98 | D35 => P97 | D36 => P96 | D37 => P95 | D38 => P94 | D39 => P93 | D40 => P92 | D41 => P91 | D42 => P90 | D43 => P89 | D44 => P88 | D45 => P87 | D46 => P86 | D47 => P85 | D48 => P84 | D49 => P83 | D50 => P82 | D51 => P81 | D52 => P80 | D53 => P79 | D54 => P78 | D55 => P77 | D56 => P76 | D57 => P75 | D58 => P74 | D59 => P73 | D60 => P72 | D61 => P71 | D62 => P70 | D63 => P69 end
  | D5 => match b with D0 => P5 | D1 => P4 | D2 => P3 | D3 => P2 | D4 => P1 | D5 => P0 | D6 => P127 | D7 => P126 | D8 => P125 | D9 => P124 | D10 => P123 | D11 => P122 | D12 => P121 | D13 => P120 | D14 => P119 | D15 => P118 | D16 => P117 | D17 => P116 | D18 => P115 | D19 => P114 | D20 => P113 | D21 => P112 | D22 => P111 | D23 => P110 | D24 => P109 | D25 => P108 | D26 => P107 | D27 => P106 | D28 => P105 | D29 => P104 | D30 => P103 | D31 => P102 | D32 => P101 | D33 => P100 | D34 => P99 | D35 => P98 | D36 => P97 | D37 => P96 | D38 => P95 | D39 => P94 | D40 => P93 | D41 => P92 | D42 => P91 | D43 => P90 | D44 => P89 | D45 => P88 | D46 => P87 | D47 => P86 | D48 => P85 | D49 => P84 | D50 => P83 | D51 => P82 | D52 => P81 | D53 => P80 | D54 => P79 | D55 => P78 | D56 => P77 | D57 => P76 | D58 => P75 | D59 => P74 | D60 => P73 | D61 => P72 | D62 => P71 | D63 => P70 end
  | D6 => match b with D0 => P6 | D1 => P5 | D2 => P4 | D3 => P3 | D4 => P2 | D5 => P1 | D6 => P0 | D7 => P127 | D8 => P126 | D9 => P125 | D10 => P124 | D11 => P123 | D12 => P122 | D13 => P121 | D14 => P120 | D15 => P119 | D16 => P118 | D17 => P117 | D18 => P116 | D19 => P115 | D20 => P114 | D21 => P113 | D22 => P112 | D23 => P111 | D24 => P110 | D25 => P109 | D26 => P108 | D27 => P107 | D28 => P106 | D29 => P105 | D30 => P104 | D31 => P103 | D32 => P102 | D33 => P101 | D34 => P100 | D35 => P99 | D36 => P98 | D37 => P97 | D38 => P96 | D39 => P95 | D40 => P94 | D41 => P93 | D42 => P92 | D43 => P91 | D44 => P90 | D45 => P89 | D46 => P88 | D47 => P87 | D48 => P86 | D49 => P85 | D50 => P84 | D51 => P83 | D52 => P82 | D53 => P81 | D54 => P80 | D55 => P79 | D56 => P78 | D57 => P77 | D58 => P76 | D59 => P75 | D60 => P74 | D61 => P73 | D62 => P72 | D63 => P71 end
  | D7 => match b with D0 => P7 | D1 => P6 | D2 => P5 | D3 => P4 | D4 => P3 | D5 => P2 | D6 => P1 | D7 => P0 | D8 => P127 | D9 => P126 | D10 => P125 | D11 => P124 | D12 => P123 | D13 => P122 | D14 => P121 | D15 => P120 | D16 => P119 | D17 => P118 | D18 => P117 | D19 => P116 | D20 => P115 | D21 => P114 | D22 => P113 | D23 => P112 | D24 => P111 | D25 => P110 | D26 => P109 | D27 => P108 | D28 => P107 | D29 => P106 | D30 => P105 | D31 => P104 | D32 => P103 | D33 => P102 | D34 => P101 | D35 => P100 | D36 => P99 | D37 => P98 | D38 => P97 | D39 => P96 | D40 => P95 | D41 => P94 | D42 => P93 | D43 => P92 | D44 => P91 | D45 => P90 | D46 => P89 | D47 => P88 | D48 => P87 | D49 => P86 | D50 => P85 | D51 => P84 | D52 => P83 | D53 => P82 | D54 => P81 | D55 => P80 | D56 => P79 | D57 => P78 | D58 => P77 | D59 => P76 | D60 => P75 | D61 => P74 | D62 => P73 | D63 => P72 end
  | D8 => match b with D0 => P8 | D1 => P7 | D2 => P6 | D3 => P5 | D4 => P4 | D5 => P3 | D6 => P2 | D7 => P1 | D8 => P0 | D9 => P127 | D10 => P126 | D11 => P125 | D12 => P124 | D13 => P123 | D14 => P122 | D15 => P121 | D16 => P120 | D17 => P119 | D18 => P118 | D19 => P117 | D20 => P116 | D21 => P115 | D22 => P114 | D23 => P113 | D24 => P112 | D25 => P111 | D26 => P110 | D27 => P109 | D28 => P108 | D29 => P107 | D30 => P106 | D31 => P105 | D32 => P104 | D33 => P103 | D34 => P102 | D35 => P101 | D36 => P100 | D37 => P99 | D38 => P98 | D39 => P97 | D40 => P96 | D41 => P95 | D42 => P94 | D43 => P93 | D44 => P92 | D45 => P91 | D46 => P90 | D47 => P89 | D48 => P88 | D49 => P87 | D50 => P86 | D51 => P85 | D52 => P84 | D53 => P83 | D54 => P82 | D55 => P81 | D56 => P80 | D57 => P79 | D58 => P78 | D59 => P77 | D60 => P76 | D61 => P75 | D62 => P74 | D63 => P73 end
  | D9 => match b with D0 => P9 | D1 => P8 | D2 => P7 | D3 => P6 | D4 => P5 | D5 => P4 | D6 => P3 | D7 => P2 | D8 => P1 | D9 => P0 | D10 => P127 | D11 => P126 | D12 => P125 | D13 => P124 | D14 => P123 | D15 => P122 | D16 => P121 | D17 => P120 | D18 => P119 | D19 => P118 | D20 => P117 | D21 => P116 | D22 => P115 | D23 => P114 | D24 => P113 | D25 => P112 | D26 => P111 | D27 => P110 | D28 => P109 | D29 => P108 | D30 => P107 | D31 => P106 | D32 => P105 | D33 => P104 | D34 => P103 | D35 => P102 | D36 => P101 | D37 => P100 | D38 => P99 | D39 => P98 | D40 => P97 | D41 => P96 | D42 => P95 | D43 => P94 | D44 => P93 | D45 => P92 | D46 => P91 | D47 => P90 | D48 => P89 | D49 => P88 | D50 => P87 | D51 => P86 | D52 => P85 | D53 => P84 | D54 => P83 | D55 => P82 | D56 => P81 | D57 => P80 | D58 => P79 | D59 => P78 | D60 => P77 | D61 => P76 | D62 => P75 | D63 => P74 end
  | D10 => match b with D0 => P10 | D1 => P9 | D2 => P8 | D3 => P7 | D4 => P6 | D5 => P5 | D6 => P4 | D7 => P3 | D8 => P2 | D9 => P1 | D10 => P0 | D11 => P127 | D12 => P126 | D13 => P125 | D14 => P124 | D15 => P123 | D16 => P122 | D17 => P121 | D18 => P120 | D19 => P119 | D20 => P118 | D21 => P117 | D22 => P116 | D23 => P115 | D24 => P114 | D25 => P113 | D26 => P112 | D27 => P111 | D28 => P110 | D29 => P109 | D30 => P108 | D31 => P107 | D32 => P106 | D33 => P105 | D34 => P104 | D35 => P103 | D36 => P102 | D37 => P101 | D38 => P100 | D39 => P99 | D40 => P98 | D41 => P97 | D42 => P96 | D43 => P95 | D44 => P94 | D45 => P93 | D46 => P92 | D47 => P91 | D48 => P90 | D49 => P89 | D50 => P88 | D51 => P87 | D52 => P86 | D53 => P85 | D54 => P84 | D55 => P83 | D56 => P82 | D57 => P81 | D58 => P80 | D59 => P79 | D60 => P78 | D61 => P77 | D62 => P76 | D63 => P75 end
  | D11 => match b with D0 => P11 | D1 => P10 | D2 => P9 | D3 => P8 | D4 => P7 | D5 => P6 | D6 => P5 | D7 => P4 | D8 => P3 | D9 => P2 | D10 => P1 | D11 => P0 | D12 => P127 | D13 => P126 | D14 => P125 | D15 => P124 | D16 => P123 | D17 => P122 | D18 => P121 | D19 => P120 | D20 => P119 | D21 => P118 | D22 => P117 | D23 => P116 | D24 => P115 | D25 => P114 | D26 => P113 | D27 => P112 | D28 => P111 | D29 => P110 | D30 => P109 | D31 => P108 | D32 => P107 | D33 => P106 | D34 => P105 | D35 => P104 | D36 => P103 | D37 => P102 | D38 => P101 | D39 => P100 | D40 => P99 | D41 => P98 | D42 => P97 | D43 => P96 | D44 => P95 | D45 => P94 | D46 => P93 | D47 => P92 | D48 => P91 | D49 => P90 | D50 => P89 | D51 => P88 | D52 => P87 | D53 => P86 | D54 => P85 | D55 => P84 | D56 => P83 | D57 => P82 | D58 => P81 | D59 => P80 | D60 => P79 | D61 => P78 | D62 => P77 | D63 => P76 end
  | D12 => match b with D0 => P12 | D1 => P11 | D2 => P10 | D3 => P9 | D4 => P8 | D5 => P7 | D6 => P6 | D7 => P5 | D8 => P4 | D9 => P3 | D10 => P2 | D11 => P1 | D12 => P0 | D13 => P127 | D14 => P126 | D15 => P125 | D16 => P124 | D17 => P123 | D18 => P122 | D19 => P121 | D20 => P120 | D21 => P119 | D22 => P118 | D23 => P117 | D24 => P116 | D25 => P115 | D26 => P114 | D27 => P113 | D28 => P112 | D29 => P111 | D30 => P110 | D31 => P109 | D32 => P108 | D33 => P107 | D34 => P106 | D35 => P105 | D36 => P104 | D37 => P103 | D38 => P102 | D39 => P101 | D40 => P100 | D41 => P99 | D42 => P98 | D43 => P97 | D44 => P96 | D45 => P95 | D46 => P94 | D47 => P93 | D48 => P92 | D49 => P91 | D50 => P90 | D51 => P89 | D52 => P88 | D53 => P87 | D54 => P86 | D55 => P85 | D56 => P84 | D57 => P83 | D58 => P82 | D59 => P81 | D60 => P80 | D61 => P79 | D62 => P78 | D63 => P77 end
  | D13 => match b with D0 => P13 | D1 => P12 | D2 => P11 | D3 => P10 | D4 => P9 | D5 => P8 | D6 => P7 | D7 => P6 | D8 => P5 | D9 => P4 | D10 => P3 | D11 => P2 | D12 => P1 | D13 => P0 | D14 => P127 | D15 => P126 | D16 => P125 | D17 => P124 | D18 => P123 | D19 => P122 | D20 => P121 | D21 => P120 | D22 => P119 | D23 => P118 | D24 => P117 | D25 => P116 | D26 => P115 | D27 => P114 | D28 => P113 | D29 => P112 | D30 => P111 | D31 => P110 | D32 => P109 | D33 => P108 | D34 => P107 | D35 => P106 | D36 => P105 | D37 => P104 | D38 => P103 | D39 => P102 | D40 => P101 | D41 => P100 | D42 => P99 | D43 => P98 | D44 => P97 | D45 => P96 | D46 => P95 | D47 => P94 | D48 => P93 | D49 => P92 | D50 => P91 | D51 => P90 | D52 => P89 | D53 => P88 | D54 => P87 | D55 => P86 | D56 => P85 | D57 => P84 | D58 => P83 | D59 => P82 | D60 => P81 | D61 => P80 | D62 => P79 | D63 => P78 end
  | D14 => match b with D0 => P14 | D1 => P13 | D2 => P12 | D3 => P11 | D4 => P10 | D5 => P9 | D6 => P8 | D7 => P7 | D8 => P6 | D9 => P5 | D10 => P4 | D11 => P3 | D12 => P2 | D13 => P1 | D14 => P0 | D15 => P127 | D16 => P126 | D17 => P125 | D18 => P124 | D19 => P123 | D20 => P122 | D21 => P121 | D22 => P120 | D23 => P119 | D24 => P118 | D25 => P117 | D26 => P116 | D27 => P115 | D28 => P114 | D29 => P113 | D30 => P112 | D31 => P111 | D32 => P110 | D33 => P109 | D34 => P108 | D35 => P107 | D36 => P106 | D37 => P105 | D38 => P104 | D39 => P103 | D40 => P102 | D41 => P101 | D42 => P100 | D43 => P99 | D44 => P98 | D45 => P97 | D46 => P96 | D47 => P95 | D48 => P94 | D49 => P93 | D50 => P92 | D51 => P91 | D52 => P90 | D53 => P89 | D54 => P88 | D55 => P87 | D56 => P86 | D57 => P85 | D58 => P84 | D59 => P83 | D60 => P82 | D61 => P81 | D62 => P80 | D63 => P79 end
  | D15 => match b with D0 => P15 | D1 => P14 | D2 => P13 | D3 => P12 | D4 => P11 | D5 => P10 | D6 => P9 | D7 => P8 | D8 => P7 | D9 => P6 | D10 => P5 | D11 => P4 | D12 => P3 | D13 => P2 | D14 => P1 | D15 => P0 | D16 => P127 | D17 => P126 | D18 => P125 | D19 => P124 | D20 => P123 | D21 => P122 | D22 => P121 | D23 => P120 | D24 => P119 | D25 => P118 | D26 => P117 | D27 => P116 | D28 => P115 | D29 => P114 | D30 => P113 | D31 => P112 | D32 => P111 | D33 => P110 | D34 => P109 | D35 => P108 | D36 => P107 | D37 => P106 | D38 => P105 | D39 => P104 | D40 => P103 | D41 => P102 | D42 => P101 | D43 => P100 | D44 => P99 | D45 => P98 | D46 => P97 | D47 => P96 | D48 => P95 | D49 => P94 | D50 => P93 | D51 => P92 | D52 => P91 | D53 => P90 | D54 => P89 | D55 => P88 | D56 => P87 | D57 => P86 | D58 => P85 | D59 => P84 | D60 => P83 | D61 => P82 | D62 => P81 | D63 => P80 end
  | D16 => match b with D0 => P16 | D1 => P15 | D2 => P14 | D3 => P13 | D4 => P12 | D5 => P11 | D6 => P10 | D7 => P9 | D8 => P8 | D9 => P7 | D10 => P6 | D11 => P5 | D12 => P4 | D13 => P3 | D14 => P2 | D15 => P1 | D16 => P0 | D17 => P127 | D18 => P126 | D19 => P125 | D20 => P124 | D21 => P123 | D22 => P122 | D23 => P121 | D24 => P120 | D25 => P119 | D26 => P118 | D27 => P117 | D28 => P116 | D29 => P115 | D30 => P114 | D31 => P113 | D32 => P112 | D33 => P111 | D34 => P110 | D35 => P109 | D36 => P108 | D37 => P107 | D38 => P106 | D39 => P105 | D40 => P104 | D41 => P103 | D42 => P102 | D43 => P101 | D44 => P100 | D45 => P99 | D46 => P98 | D47 => P97 | D48 => P96 | D49 => P95 | D50 => P94 | D51 => P93 | D52 => P92 | D53 => P91 | D54 => P90 | D55 => P89 | D56 => P88 | D57 => P87 | D58 => P86 | D59 => P85 | D60 => P84 | D61 => P83 | D62 => P82 | D63 => P81 end
  | D17 => match b with D0 => P17 | D1 => P16 | D2 => P15 | D3 => P14 | D4 => P13 | D5 => P12 | D6 => P11 | D7 => P10 | D8 => P9 | D9 => P8 | D10 => P7 | D11 => P6 | D12 => P5 | D13 => P4 | D14 => P3 | D15 => P2 | D16 => P1 | D17 => P0 | D18 => P127 | D19 => P126 | D20 => P125 | D21 => P124 | D22 => P123 | D23 => P122 | D24 => P121 | D25 => P120 | D26 => P119 | D27 => P118 | D28 => P117 | D29 => P116 | D30 => P115 | D31 => P114 | D32 => P113 | D33 => P112 | D34 => P111 | D35 => P110 | D36 => P109 | D37 => P108 | D38 => P107 | D39 => P106 | D40 => P105 | D41 => P104 | D42 => P103 | D43 => P102 | D44 => P101 | D45 => P100 | D46 => P99 | D47 => P98 | D48 => P97 | D49 => P96 | D50 => P95 | D51 => P94 | D52 => P93 | D53 => P92 | D54 => P91 | D55 => P90 | D56 => P89 | D57 => P88 | D58 => P87 | D59 => P86 | D60 => P85 | D61 => P84 | D62 => P83 | D63 => P82 end
  | D18 => match b with D0 => P18 | D1 => P17 | D2 => P16 | D3 => P15 | D4 => P14 | D5 => P13 | D6 => P12 | D7 => P11 | D8 => P10 | D9 => P9 | D10 => P8 | D11 => P7 | D12 => P6 | D13 => P5 | D14 => P4 | D15 => P3 | D16 => P2 | D17 => P1 | D18 => P0 | D19 => P127 | D20 => P126 | D21 => P125 | D22 => P124 | D23 => P123 | D24 => P122 | D25 => P121 | D26 => P120 | D27 => P119 | D28 => P118 | D29 => P117 | D30 => P116 | D31 => P115 | D32 => P114 | D33 => P113 | D34 => P112 | D35 => P111 | D36 => P110 | D37 => P109 | D38 => P108 | D39 => P107 | D40 => P106 | D41 => P105 | D42 => P104 | D43 => P103 | D44 => P102 | D45 => P101 | D46 => P100 | D47 => P99 | D48 => P98 | D49 => P97 | D50 => P96 | D51 => P95 | D52 => P94 | D53 => P93 | D54 => P92 | D55 => P91 | D56 => P90 | D57 => P89 | D58 => P88 | D59 => P87 | D60 => P86 | D61 => P85 | D62 => P84 | D63 => P83 end
  | D19 => match b with D0 => P19 | D1 => P18 | D2 => P17 | D3 => P16 | D4 => P15 | D5 => P14 | D6 => P13 | D7 => P12 | D8 => P11 | D9 => P10 | D10 => P9 | D11 => P8 | D12 => P7 | D13 => P6 | D14 => P5 | D15 => P4 | D16 => P3 | D17 => P2 | D18 => P1 | D19 => P0 | D20 => P127 | D21 => P126 | D22 => P125 | D23 => P124 | D24 => P123 | D25 => P122 | D26 => P121 | D27 => P120 | D28 => P119 | D29 => P118 | D30 => P117 | D31 => P116 | D32 => P115 | D33 => P114 | D34 => P113 | D35 => P112 | D36 => P111 | D37 => P110 | D38 => P109 | D39 => P108 | D40 => P107 | D41 => P106 | D42 => P105 | D43 => P104 | D44 => P103 | D45 => P102 | D46 => P101 | D47 => P100 | D48 => P99 | D49 => P98 | D50 => P97 | D51 => P96 | D52 => P95 | D53 => P94 | D54 => P93 | D55 => P92 | D56 => P91 | D57 => P90 | D58 => P89 | D59 => P88 | D60 => P87 | D61 => P86 | D62 => P85 | D63 => P84 end
  | D20 => match b with D0 => P20 | D1 => P19 | D2 => P18 | D3 => P17 | D4 => P16 | D5 => P15 | D6 => P14 | D7 => P13 | D8 => P12 | D9 => P11 | D10 => P10 | D11 => P9 | D12 => P8 | D13 => P7 | D14 => P6 | D15 => P5 | D16 => P4 | D17 => P3 | D18 => P2 | D19 => P1 | D20 => P0 | D21 => P127 | D22 => P126 | D23 => P125 | D24 => P124 | D25 => P123 | D26 => P122 | D27 => P121 | D28 => P120 | D29 => P119 | D30 => P118 | D31 => P117 | D32 => P116 | D33 => P115 | D34 => P114 | D35 => P113 | D36 => P112 | D37 => P111 | D38 => P110 | D39 => P109 | D40 => P108 | D41 => P107 | D42 => P106 | D43 => P105 | D44 => P104 | D45 => P103 | D46 => P102 | D47 => P101 | D48 => P100 | D49 => P99 | D50 => P98 | D51 => P97 | D52 => P96 | D53 => P95 | D54 => P94 | D55 => P93 | D56 => P92 | D57 => P91 | D58 => P90 | D59 => P89 | D60 => P88 | D61 => P87 | D62 => P86 | D63 => P85 end
  | D21 => match b with D0 => P21 | D1 => P20 | D2 => P19 | D3 => P18 | D4 => P17 | D5 => P16 | D6 => P15 | D7 => P14 | D8 => P13 | D9 => P12 | D10 => P11 | D11 => P10 | D12 => P9 | D13 => P8 | D14 => P7 | D15 => P6 | D16 => P5 | D17 => P4 | D18 => P3 | D19 => P2 | D20 => P1 | D21 => P0 | D22 => P127 | D23 => P126 | D24 => P125 | D25 => P124 | D26 => P123 | D27 => P122 | D28 => P121 | D29 => P120 | D30 => P119 | D31 => P118 | D32 => P117 | D33 => P116 | D34 => P115 | D35 => P114 | D36 => P113 | D37 => P112 | D38 => P111 | D39 => P110 | D40 => P109 | D41 => P108 | D42 => P107 | D43 => P106 | D44 => P105 | D45 => P104 | D46 => P103 | D47 => P102 | D48 => P101 | D49 => P100 | D50 => P99 | D51 => P98 | D52 => P97 | D53 => P96 | D54 => P95 | D55 => P94 | D56 => P93 | D57 => P92 | D58 => P91 | D59 => P90 | D60 => P89 | D61 => P88 | D62 => P87 | D63 => P86 end
  | D22 => match b with D0 => P22 | D1 => P21 | D2 => P20 | D3 => P19 | D4 => P18 | D5 => P17 | D6 => P16 | D7 => P15 | D8 => P14 | D9 => P13 | D10 => P12 | D11 => P11 | D12 => P10 | D13 => P9 | D14 => P8 | D15 => P7 | D16 => P6 | D17 => P5 | D18 => P4 | D19 => P3 | D20 => P2 | D21 => P1 | D22 => P0 | D23 => P127 | D24 => P126 | D25 => P125 | D26 => P124 | D27 => P123 | D28 => P122 | D29 => P121 | D30 => P120 | D31 => P119 | D32 => P118 | D33 => P117 | D34 => P116 | D35 => P115 | D36 => P114 | D37 => P113 | D38 => P112 | D39 => P111 | D40 => P110 | D41 => P109 | D42 => P108 | D43 => P107 | D44 => P106 | D45 => P105 | D46 => P104 | D47 => P103 | D48 => P102 | D49 => P101 | D50 => P100 | D51 => P99 | D52 => P98 | D53 => P97 | D54 => P96 | D55 => P95 | D56 => P94 | D57 => P93 | D58 => P92 | D59 => P91 | D60 => P90 | D61 => P89 | D62 => P88 | D63 => P87 end
  | D23 => match b with D0 => P23 | D1 => P22 | D2 => P21 | D3 => P20 | D4 => P19 | D5 => P18 | D6 => P17 | D7 => P16 | D8 => P15 | D9 => P14 | D10 => P13 | D11 => P12 | D12 => P11 | D13 => P10 | D14 => P9 | D15 => P8 | D16 => P7 | D17 => P6 | D18 => P5 | D19 => P4 | D20 => P3 | D21 => P2 | D22 => P1 | D23 => P0 | D24 => P127 | D25 => P126 | D26 => P125 | D27 => P124 | D28 => P123 | D29 => P122 | D30 => P121 | D31 => P120 | D32 => P119 | D33 => P118 | D34 => P117 | D35 => P116 | D36 => P115 | D37 => P114 | D38 => P113 | D39 => P112 | D40 => P111 | D41 => P110 | D42 => P109 | D43 => P108 | D44 => P107 | D45 => P106 | D46 => P105 | D47 => P104 | D48 => P103 | D49 => P102 | D50 => P101 | D51 => P100 | D52 => P99 | D53 => P98 | D54 => P97 | D55 => P96 | D56 => P95 | D57 => P94 | D58 => P93 | D59 => P92 | D60 => P91 | D61 => P90 | D62 => P89 | D63 => P88 end
  | D24 => match b with D0 => P24 | D1 => P23 | D2 => P22 | D3 => P21 | D4 => P20 | D5 => P19 | D6 => P18 | D7 => P17 | D8 => P16 | D9 => P15 | D10 => P14 | D11 => P13 | D12 => P12 | D13 => P11 | D14 => P10 | D15 => P9 | D16 => P8 | D17 => P7 | D18 => P6 | D19 => P5 | D20 => P4 | D21 => P3 | D22 => P2 | D23 => P1 | D24 => P0 | D25 => P127 | D26 => P126 | D27 => P125 | D28 => P124 | D29 => P123 | D30 => P122 | D31 => P121 | D32 => P120 | D33 => P119 | D34 => P118 | D35 => P117 | D36 => P116 | D37 => P115 | D38 => P114 | D39 => P113 | D40 => P112 | D41 => P111 | D42 => P110 | D43 => P109 | D44 => P108 | D45 => P107 | D46 => P106 | D47 => P105 | D48 => P104 | D49 => P103 | D50 => P102 | D51 => P101 | D52 => P100 | D53 => P99 | D54 => P98 | D55 => P97 | D56 => P96 | D57 => P95 | D58 => P94 | D59 => P93 | D60 => P92 | D61 => P91 | D62 => P90 | D63 => P89 end
  | D25 => match b with D0 => P25 | D1 => P24 | D2 => P23 | D3 => P22 | D4 => P21 | D5 => P20 | D6 => P19 | D7 => P18 | D8 => P17 | D9 => P16 | D10 => P15 | D11 => P14 | D12 => P13 | D13 => P12 | D14 => P11 | D15 => P10 | D16 => P9 | D17 => P8 | D18 => P7 | D19 => P6 | D20 => P5 | D21 => P4 | D22 => P3 | D23 => P2 | D24 => P1 | D25 => P0 | D26 => P127 | D27 => P126 | D28 => P125 | D29 => P124 | D30 => P123 | D31 => P122 | D32 => P121 | D33 => P120 | D34 => P119 | D35 => P118 | D36 => P117 | D37 => P116 | D38 => P115 | D39 => P114 | D40 => P113 | D41 => P112 | D42 => P111 | D43 => P110 | D44 => P109 | D45 => P108 | D46 => P107 | D47 => P106 | D48 => P105 | D49 => P104 | D50 => P103 | D51 => P102 | D52 => P101 | D53 => P100 | D54 => P99 | D55 => P98 | D56 => P97 | D57 => P96 | D58 => P95 | D59 => P94 | D60 => P93 | D61 => P92 | D62 => P91 | D63 => P90 end
  | D26 => match b with D0 => P26 | D1 => P25 | D2 => P24 | D3 => P23 | D4 => P22 | D5 => P21 | D6 => P20 | D7 => P19 | D8 => P18 | D9 => P17 | D10 => P16 | D11 => P15 | D12 => P14 | D13 => P13 | D14 => P12 | D15 => P11 | D16 => P10 | D17 => P9 | D18 => P8 | D19 => P7 | D20 => P6 | D21 => P5 | D22 => P4 | D23 => P3 | D24 => P2 | D25 => P1 | D26 => P0 | D27 => P127 | D28 => P126 | D29 => P125 | D30 => P124 | D31 => P123 | D32 => P122 | D33 => P121 | D34 => P120 | D35 => P119 | D36 => P118 | D37 => P117 | D38 => P116 | D39 => P115 | D40 => P114 | D41 => P113 | D42 => P112 | D43 => P111 | D44 => P110 | D45 => P109 | D46 => P108 | D47 => P107 | D48 => P106 | D49 => P105 | D50 => P104 | D51 => P103 | D52 => P102 | D53 => P101 | D54 => P100 | D55 => P99 | D56 => P98 | D57 => P97 | D58 => P96 | D59 => P95 | D60 => P94 | D61 => P93 | D62 => P92 | D63 => P91 end
  | D27 => match b with D0 => P27 | D1 => P26 | D2 => P25 | D3 => P24 | D4 => P23 | D5 => P22 | D6 => P21 | D7 => P20 | D8 => P19 | D9 => P18 | D10 => P17 | D11 => P16 | D12 => P15 | D13 => P14 | D14 => P13 | D15 => P12 | D16 => P11 | D17 => P10 | D18 => P9 | D19 => P8 | D20 => P7 | D21 => P6 | D22 => P5 | D23 => P4 | D24 => P3 | D25 => P2 | D26 => P1 | D27 => P0 | D28 => P127 | D29 => P126 | D30 => P125 | D31 => P124 | D32 => P123 | D33 => P122 | D34 => P121 | D35 => P120 | D36 => P119 | D37 => P118 | D38 => P117 | D39 => P116 | D40 => P115 | D41 => P114 | D42 => P113 | D43 => P112 | D44 => P111 | D45 => P110 | D46 => P109 | D47 => P108 | D48 => P107 | D49 => P106 | D50 => P105 | D51 => P104 | D52 => P103 | D53 => P102 | D54 => P101 | D55 => P100 | D56 => P99 | D57 => P98 | D58 => P97 | D59 => P96 | D60 => P95 | D61 => P94 | D62 => P93 | D63 => P92 end
  | D28 => match b with D0 => P28 | D1 => P27 | D2 => P26 | D3 => P25 | D4 => P24 | D5 => P23 | D6 => P22 | D7 => P21 | D8 => P20 | D9 => P19 | D10 => P18 | D11 => P17 | D12 => P16 | D13 => P15 | D14 => P14 | D15 => P13 | D16 => P12 | D17 => P11 | D18 => P10 | D19 => P9 | D20 => P8 | D21 => P7 | D22 => P6 | D23 => P5 | D24 => P4 | D25 => P3 | D26 => P2 | D27 => P1 | D28 => P0 | D29 => P127 | D30 => P126 | D31 => P125 | D32 => P124 | D33 => P123 | D34 => P122 | D35 => P121 | D36 => P120 | D37 => P119 | D38 => P118 | D39 => P117 | D40 => P116 | D41 => P115 | D42 => P114 | D43 => P113 | D44 => P112 | D45 => P111 | D46 => P110 | D47 => P109 | D48 => P108 | D49 => P107 | D50 => P106 | D51 => P105 | D52 => P104 | D53 => P103 | D54 => P102 | D55 => P101 | D56 => P100 | D57 => P99 | D58 => P98 | D59 => P97 | D60 => P96 | D61 => P95 | D62 => P94 | D63 => P93 end
  | D29 => match b with D0 => P29 | D1 => P28 | D2 => P27 | D3 => P26 | D4 => P25 | D5 => P24 | D6 => P23 | D7 => P22 | D8 => P21 | D9 => P20 | D10 => P19 | D11 => P18 | D12 => P17 | D13 => P16 | D14 => P15 | D15 => P14 | D16 => P13 | D17 => P12 | D18 => P11 | D19 => P10 | D20 => P9 | D21 => P8 | D22 => P7 | D23 => P6 | D24 => P5 | D25 => P4 | D26 => P3 | D27 => P2 | D28 => P1 | D29 => P0 | D30 => P127 | D31 => P126 | D32 => P125 | D33 => P124 | D34 => P123 | D35 => P122 | D36 => P121 | D37 => P120 | D38 => P119 | D39 => P118 | D40 => P117 | D41 => P116 | D42 => P115 | D43 => P114 | D44 => P113 | D45 => P112 | D46 => P111 | D47 => P110 | D48 => P109 | D49 => P108 | D50 => P107 | D51 => P106 | D52 => P105 | D53 => P104 | D54 => P103 | D55 => P102 | D56 => P101 | D57 => P100 | D58 => P99 | D59 => P98 | D60 => P97 | D61 => P96 | D62 => P95 | D63 => P94 end
  | D30 => match b with D0 => P30 | D1 => P29 | D2 => P28 | D3 => P27 | D4 => P26 | D5 => P25 | D6 => P24 | D7 => P23 | D8 => P22 | D9 => P21 | D10 => P20 | D11 => P19 | D12 => P18 | D13 => P17 | D14 => P16 | D15 => P15 | D16 => P14 | D17 => P13 | D18 => P12 | D19 => P11 | D20 => P10 | D21 => P9 | D22 => P8 | D23 => P7 | D24 => P6 | D25 => P5 | D26 => P4 | D27 => P3 | D28 => P2 | D29 => P1 | D30 => P0 | D31 => P127 | D32 => P126 | D33 => P125 | D34 => P124 | D35 => P123 | D36 => P122 | D37 => P121 | D38 => P120 | D39 => P119 | D40 => P118 | D41 => P117 | D42 => P116 | D43 => P115 | D44 => P114 | D45 => P113 | D46 => P112 | D47 => P111 | D48 => P110 | D49 => P109 | D50 => P108 | D51 => P107 | D52 => P106 | D53 => P105 | D54 => P104 | D55 => P103 | D56 => P102 | D57 => P101 | D58 => P100 | D59 => P99 | D60 => P98 | D61 => P97 | D62 => P96 | D63 => P95 end
  | D31 => match b with D0 => P31 | D1 => P30 | D2 => P29 | D3 => P28 | D4 => P27 | D5 => P26 | D6 => P25 | D7 => P24 | D8 => P23 | D9 => P22 | D10 => P21 | D11 => P20 | D12 => P19 | D13 => P18 | D14 => P17 | D15 => P16 | D16 => P15 | D17 => P14 | D18 => P13 | D19 => P12 | D20 => P11 | D21 => P10 | D22 => P9 | D23 => P8 | D24 => P7 | D25 => P6 | D26 => P5 | D27 => P4 | D28 => P3 | D29 => P2 | D30 => P1 | D31 => P0 | D32 => P127 | D33 => P126 | D34 => P125 | D35 => P124 | D36 => P123 | D37 => P122 | D38 => P121 | D39 => P120 | D40 => P119 | D41 => P118 | D42 => P117 | D43 => P116 | D44 => P115 | D45 => P114 | D46 => P113 | D47 => P112 | D48 => P111 | D49 => P110 | D50 => P109 | D51 => P108 | D52 => P107 | D53 => P106 | D54 => P105 | D55 => P104 | D56 => P103 | D57 => P102 | D58 => P101 | D59 => P100 | D60 => P99 | D61 => P98 | D62 => P97 | D63 => P96 end
  | D32 => match b with D0 => P32 | D1 => P31 | D2 => P30 | D3 => P29 | D4 => P28 | D5 => P27 | D6 => P26 | D7 => P25 | D8 => P24 | D9 => P23 | D10 => P22 | D11 => P21 | D12 => P20 | D13 => P19 | D14 => P18 | D15 => P17 | D16 => P16 | D17 => P15 | D18 => P14 | D19 => P13 | D20 => P12 | D21 => P11 | D22 => P10 | D23 => P9 | D24 => P8 | D25 => P7 | D26 => P6 | D27 => P5 | D28 => P4 | D29 => P3 | D30 => P2 | D31 => P1 | D32 => P0 | D33 => P127 | D34 => P126 | D35 => P125 | D36 => P124 | D37 => P123 | D38 => P122 | D39 => P121 | D40 => P120 | D41 => P119 | D42 => P118 | D43 => P117 | D44 => P116 | D45 => P115 | D46 => P114 | D47 => P113 | D48 => P112 | D49 => P111 | D50 => P110 | D51 => P109 | D52 => P108 | D53 => P107 | D54 => P106 | D55 => P105 | D56 => P104 | D57 => P103 | D58 => P102 | D59 => P101 | D60 => P100 | D61 => P99 | D62 => P98 | D63 => P97 end
  | D33 => match b with D0 => P33 | D1 => P32 | D2 => P31 | D3 => P30 | D4 => P29 | D5 => P28 | D6 => P27 | D7 => P26 | D8 => P25 | D9 => P24 | D10 => P23 | D11 => P22 | D12 => P21 | D13 => P20 | D14 => P19 | D15 => P18 | D16 => P17 | D17 => P16 | D18 => P15 | D19 => P14 | D20 => P13 | D21 => P12 | D22 => P11 | D23 => P10 | D24 => P9 | D25 => P8 | D26 => P7 | D27 => P6 | D28 => P5 | D29 => P4 | D30 => P3 | D31 => P2 | D32 => P1 | D33 => P0 | D34 => P127 | D35 => P126 | D36 => P125 | D37 => P124 | D38 => P123 | D39 => P122 | D40 => P121 | D41 => P120 | D42 => P119 | D43 => P118 | D44 => P117 | D45 => P116 | D46 => P115 | D47 => P114 | D48 => P113 | D49 => P112 | D50 => P111 | D51 => P110 | D52 => P109 | D53 => P108 | D54 => P107 | D55 => P106 | D56 => P105 | D57 => P104 | D58 => P103 | D59 => P102 | D60 => P101 | D61 => P100 | D62 => P99 | D63 => P98 end
  | D34 => match b with D0 => P34 | D1 => P33 | D2 => P32 | D3 => P31 | D4 => P30 | D5 => P29 | D6 => P28 | D7 => P27 | D8 => P26 | D9 => P25 | D10 => P24 | D11 => P23 | D12 => P22 | D13 => P21 | D14 => P20 | D15 => P19 | D16 => P18 | D17 => P17 | D18 => P16 | D19 => P15 | D20 => P14 | D21 => P13 | D22 => P12 | D23 => P11 | D24 => P10 | D25 => P9 | D26 => P8 | D27 => P7 | D28 => P6 | D29 => P5 | D30 => P4 | D31 => P3 | D32 => P2 | D33 => P1 | D34 => P0 | D35 => P127 | D36 => P126 | D37 => P125 | D38 => P124 | D39 => P123 | D40 => P122 | D41 => P121 | D42 => P120 | D43 => P119 | D44 => P118 | D45 => P117 | D46 => P116 | D47 => P115 | D48 => P114 | D49 => P113 | D50 => P112 | D51 => P111 | D52 => P110 | D53 => P109 | D54 => P108 | D55 => P107 | D56 => P106 | D57 => P105 | D58 => P104 | D59 => P103 | D60 => P102 | D61 => P101 | D62 => P100 | D63 => P99 end
  | D35 => match b with D0 => P35 | D1 => P34 | D2 => P33 | D3 => P32 | D4 => P31 | D5 => P30 | D6 => P29 | D7 => P28 | D8 => P27 | D9 => P26 | D10 => P25 | D11 => P24 | D12 => P23 | D13 => P22 | D14 => P21 | D15 => P20 | D16 => P19 | D17 => P18 | D18 => P17 | D19 => P16 | D20 => P15 | D21 => P14 | D22 => P13 | D23 => P12 | D24 => P11 | D25 => P10 | D26 => P9 | D27 => P8 | D28 => P7 | D29 => P6 | D30 => P5 | D31 => P4 | D32 => P3 | D33 => P2 | D34 => P1 | D35 => P0 | D36 => P127 | D37 => P126 | D38 => P125 | D39 => P124 | D40 => P123 | D41 => P122 | D42 => P121 | D43 => P120 | D44 => P119 | D45 => P118 | D46 => P117 | D47 => P116 | D48 => P115 | D49 => P114 | D50 => P113 | D51 => P112 | D52 => P111 | D53 => P110 | D54 => P109 | D55 => P108 | D56 => P107 | D57 => P106 | D58 => P105 | D59 => P104 | D60 => P103 | D61 => P102 | D62 => P101 | D63 => P100 end
  | D36 => match b with D0 => P36 | D1 => P35 | D2 => P34 | D3 => P33 | D4 => P32 | D5 => P31 | D6 => P30 | D7 => P29 | D8 => P28 | D9 => P27 | D10 => P26 | D11 => P25 | D12 => P24 | D13 => P23 | D14 => P22 | D15 => P21 | D16 => P20 | D17 => P19 | D18 => P18 | D19 => P17 | D20 => P16 | D21 => P15 | D22 => P14 | D23 => P13 | D24 => P12 | D25 => P11 | D26 => P10 | D27 => P9 | D28 => P8 | D29 => P7 | D30 => P6 | D31 => P5 | D32 => P4 | D33 => P3 | D34 => P2 | D35 => P1 | D36 => P0 | D37 => P127 | D38 => P126 | D39 => P125 | D40 => P124 | D41 => P123 | D42 => P122 | D43 => P121 | D44 => P120 | D45 => P119 | D46 => P118 | D47 => P117 | D48 => P116 | D49 => P115 | D50 => P114 | D51 => P113 | D52 => P112 | D53 => P111 | D54 => P110 | D55 => P109 | D56 => P108 | D57 => P107 | D58 => P106 | D59 => P105 | D60 => P104 | D61 => P103 | D62 => P102 | D63 => P101 end
  | D37 => match b with D0 => P37 | D1 => P36 | D2 => P35 | D3 => P34 | D4 => P33 | D5 => P32 | D6 => P31 | D7 => P30 | D8 => P29 | D9 => P28 | D10 => P27 | D11 => P26 | D12 => P25 | D13 => P24 | D14 => P23 | D15 => P22 | D16 => P21 | D17 => P20 | D18 => P19 | D19 => P18 | D20 => P17 | D21 => P16 | D22 => P15 | D23 => P14 | D24 => P13 | D25 => P12 | D26 => P11 | D27 => P10 | D28 => P9 | D29 => P8 | D30 => P7 | D31 => P6 | D32 => P5 | D33 => P4 | D34 => P3 | D35 => P2 | D36 => P1 | D37 => P0 | D38 => P127 | D39 => P126 | D40 => P125 | D41 => P124 | D42 => P123 | D43 => P122 | D44 => P121 | D45 => P120 | D46 => P119 | D47 => P118 | D48 => P117 | D49 => P116 | D50 => P115 | D51 => P114 | D52 => P113 | D53 => P112 | D54 => P111 | D55 => P110 | D56 => P109 | D57 => P108 | D58 => P107 | D59 => P106 | D60 => P105 | D61 => P104 | D62 => P103 | D63 => P102 end
  | D38 => match b with D0 => P38 | D1 => P37 | D2 => P36 | D3 => P35 | D4 => P34 | D5 => P33 | D6 => P32 | D7 => P31 | D8 => P30 | D9 => P29 | D10 => P28 | D11 => P27 | D12 => P26 | D13 => P25 | D14 => P24 | D15 => P23 | D16 => P22 | D17 => P21 | D18 => P20 | D19 => P19 | D20 => P18 | D21 => P17 | D22 => P16 | D23 => P15 | D24 => P14 | D25 => P13 | D26 => P12 | D27 => P11 | D28 => P10 | D29 => P9 | D30 => P8 | D31 => P7 | D32 => P6 | D33 => P5 | D34 => P4 | D35 => P3 | D36 => P2 | D37 => P1 | D38 => P0 | D39 => P127 | D40 => P126 | D41 => P125 | D42 => P124 | D43 => P123 | D44 => P122 | D45 => P121 | D46 => P120 | D47 => P119 | D48 => P118 | D49 => P117 | D50 => P116 | D51 => P115 | D52 => P114 | D53 => P113 | D54 => P112 | D55 => P111 | D56 => P110 | D57 => P109 | D58 => P108 | D59 => P107 | D60 => P106 | D61 => P105 | D62 => P104 | D63 => P103 end
  | D39 => match b with D0 => P39 | D1 => P38 | D2 => P37 | D3 => P36 | D4 => P35 | D5 => P34 | D6 => P33 | D7 => P32 | D8 => P31 | D9 => P30 | D10 => P29 | D11 => P28 | D12 => P27 | D13 => P26 | D14 => P25 | D15 => P24 | D16 => P23 | D17 => P22 | D18 => P21 | D19 => P20 | D20 => P19 | D21 => P18 | D22 => P17 | D23 => P16 | D24 => P15 | D25 => P14 | D26 => P13 | D27 => P12 | D28 => P11 | D29 => P10 | D30 => P9 | D31 => P8 | D32 => P7 | D33 => P6 | D34 => P5 | D35 => P4 | D36 => P3 | D37 => P2 | D38 => P1 | D39 => P0 | D40 => P127 | D41 => P126 | D42 => P125 | D43 => P124 | D44 => P123 | D45 => P122 | D46 => P121 | D47 => P120 | D48 => P119 | D49 => P118 | D50 => P117 | D51 => P116 | D52 => P115 | D53 => P114 | D54 => P113 | D55 => P112 | D56 => P111 | D57 => P110 | D58 => P109 | D59 => P108 | D60 => P107 | D61 => P106 | D62 => P105 | D63 => P104 end
  | D40 => match b with D0 => P40 | D1 => P39 | D2 => P38 | D3 => P37 | D4 => P36 | D5 => P35 | D6 => P34 | D7 => P33 | D8 => P32 | D9 => P31 | D10 => P30 | D11 => P29 | D12 => P28 | D13 => P27 | D14 => P26 | D15 => P25 | D16 => P24 | D17 => P23 | D18 => P22 | D19 => P21 | D20 => P20 | D21 => P19 | D22 => P18 | D23 => P17 | D24 => P16 | D25 => P15 | D26 => P14 | D27 => P13 | D28 => P12 | D29 => P11 | D30 => P10 | D31 => P9 | D32 => P8 | D33 => P7 | D34 => P6 | D35 => P5 | D36 => P4 | D37 => P3 | D38 => P2 | D39 => P1 | D40 => P0 | D41 => P127 | D42 => P126 | D43 => P125 | D44 => P124 | D45 => P123 | D46 => P122 | D47 => P121 | D48 => P120 | D49 => P119 | D50 => P118 | D51 => P117 | D52 => P116 | D53 => P115 | D54 => P114 | D55 => P113 | D56 => P112 | D57 => P111 | D58 => P110 | D59 => P109 | D60 => P108 | D61 => P107 | D62 => P106 | D63 => P105 end
  | D41 => match b with D0 => P41 | D1 => P40 | D2 => P39 | D3 => P38 | D4 => P37 | D5 => P36 | D6 => P35 | D7 => P34 | D8 => P33 | D9 => P32 | D10 => P31 | D11 => P30 | D12 => P29 | D13 => P28 | D14 => P27 | D15 => P26 | D16 => P25 | D17 => P24 | D18 => P23 | D19 => P22 | D20 => P21 | D21 => P20 | D22 => P19 | D23 => P18 | D24 => P17 | D25 => P16 | D26 => P15 | D27 => P14 | D28 => P13 | D29 => P12 | D30 => P11 | D31 => P10 | D32 => P9 | D33 => P8 | D34 => P7 | D35 => P6 | D36 => P5 | D37 => P4 | D38 => P3 | D39 => P2 | D40 => P1 | D41 => P0 | D42 => P127 | D43 => P126 | D44 => P125 | D45 => P124 | D46 => P123 | D47 => P122 | D48 => P121 | D49 => P120 | D50 => P119 | D51 => P118 | D52 => P117 | D53 => P116 | D54 => P115 | D55 => P114 | D56 => P113 | D57 => P112 | D58 => P111 | D59 => P110 | D60 => P109 | D61 => P108 | D62 => P107 | D63 => P106 end
  | D42 => match b with D0 => P42 | D1 => P41 | D2 => P40 | D3 => P39 | D4 => P38 | D5 => P37 | D6 => P36 | D7 => P35 | D8 => P34 | D9 => P33 | D10 => P32 | D11 => P31 | D12 => P30 | D13 => P29 | D14 => P28 | D15 => P27 | D16 => P26 | D17 => P25 | D18 => P24 | D19 => P23 | D20 => P22 | D21 => P21 | D22 => P20 | D23 => P19 | D24 => P18 | D25 => P17 | D26 => P16 | D27 => P15 | D28 => P14 | D29 => P13 | D30 => P12 | D31 => P11 | D32 => P10 | D33 => P9 | D34 => P8 | D35 => P7 | D36 => P6 | D37 => P5 | D38 => P4 | D39 => P3 | D40 => P2 | D41 => P1 | D42 => P0 | D43 => P127 | D44 => P126 | D45 => P125 | D46 => P124 | D47 => P123 | D48 => P122 | D49 => P121 | D50 => P120 | D51 => P119 | D52 => P118 | D53 => P117 | D54 => P116 | D55 => P115 | D56 => P114 | D57 => P113 | D58 => P112 | D59 => P111 | D60 => P110 | D61 => P109 | D62 => P108 | D63 => P107 end
  | D43 => match b with D0 => P43 | D1 => P42 | D2 => P41 | D3 => P40 | D4 => P39 | D5 => P38 | D6 => P37 | D7 => P36 | D8 => P35 | D9 => P34 | D10 => P33 | D11 => P32 | D12 => P31 | D13 => P30 | D14 => P29 | D15 => P28 | D16 => P27 | D17 => P26 | D18 => P25 | D19 => P24 | D20 => P23 | D21 => P22 | D22 => P21 | D23 => P20 | D24 => P19 | D25 => P18 | D26 => P17 | D27 => P16 | D28 => P15 | D29 => P14 | D30 => P13 | D31 => P12 | D32 => P11 | D33 => P10 | D34 => P9 | D35 => P8 | D36 => P7 | D37 => P6 | D38 => P5 | D39 => P4 | D40 => P3 | D41 => P2 | D42 => P1 | D43 => P0 | D44 => P127 | D45 => P126 | D46 => P125 | D47 => P124 | D48 => P123 | D49 => P122 | D50 => P121 | D51 => P120 | D52 => P119 | D53 => P118 | D54 => P117 | D55 => P116 | D56 => P115 | D57 => P114 | D58 => P113 | D59 => P112 | D60 => P111 | D61 => P110 | D62 => P109 | D63 => P108 end
  | D44 => match b with D0 => P44 | D1 => P43 | D2 => P42 | D3 => P41 | D4 => P40 | D5 => P39 | D6 => P38 | D7 => P37 | D8 => P36 | D9 => P35 | D10 => P34 | D11 => P33 | D12 => P32 | D13 => P31 | D14 => P30 | D15 => P29 | D16 => P28 | D17 => P27 | D18 => P26 | D19 => P25 | D20 => P24 | D21 => P23 | D22 => P22 | D23 => P21 | D24 => P20 | D25 => P19 | D26 => P18 | D27 => P17 | D28 => P16 | D29 => P15 | D30 => P14 | D31 => P13 | D32 => P12 | D33 => P11 | D34 => P10 | D35 => P9 | D36 => P8 | D37 => P7 | D38 => P6 | D39 => P5 | D40 => P4 | D41 => P3 | D42 => P2 | D43 => P1 | D44 => P0 | D45 => P127 | D46 => P126 | D47 => P125 | D48 => P124 | D49 => P123 | D50 => P122 | D51 => P121 | D52 => P120 | D53 => P119 | D54 => P118 | D55 => P117 | D56 => P116 | D57 => P115 | D58 => P114 | D59 => P113 | D60 => P112 | D61 => P111 | D62 => P110 | D63 => P109 end
  | D45 => match b with D0 => P45 | D1 => P44 | D2 => P43 | D3 => P42 | D4 => P41 | D5 => P40 | D6 => P39 | D7 => P38 | D8 => P37 | D9 => P36 | D10 => P35 | D11 => P34 | D12 => P33 | D13 => P32 | D14 => P31 | D15 => P30 | D16 => P29 | D17 => P28 | D18 => P27 | D19 => P26 | D20 => P25 | D21 => P24 | D22 => P23 | D23 => P22 | D24 => P21 | D25 => P20 | D26 => P19 | D27 => P18 | D28 => P17 | D29 => P16 | D30 => P15 | D31 => P14 | D32 => P13 | D33 => P12 | D34 => P11 | D35 => P10 | D36 => P9 | D37 => P8 | D38 => P7 | D39 => P6 | D40 => P5 | D41 => P4 | D42 => P3 | D43 => P2 | D44 => P1 | D45 => P0 | D46 => P127 | D47 => P126 | D48 => P125 | D49 => P124 | D50 => P123 | D51 => P122 | D52 => P121 | D53 => P120 | D54 => P119 | D55 => P118 | D56 => P117 | D57 => P116 | D58 => P115 | D59 => P114 | D60 => P113 | D61 => P112 | D62 => P111 | D63 => P110 end
  | D46 => match b with D0 => P46 | D1 => P45 | D2 => P44 | D3 => P43 | D4 => P42 | D5 => P41 | D6 => P40 | D7 => P39 | D8 => P38 | D9 => P37 | D10 => P36 | D11 => P35 | D12 => P34 | D13 => P33 | D14 => P32 | D15 => P31 | D16 => P30 | D17 => P29 | D18 => P28 | D19 => P27 | D20 => P26 | D21 => P25 | D22 => P24 | D23 => P23 | D24 => P22 | D25 => P21 | D26 => P20 | D27 => P19 | D28 => P18 | D29 => P17 | D30 => P16 | D31 => P15 | D32 => P14 | D33 => P13 | D34 => P12 | D35 => P11 | D36 => P10 | D37 => P9 | D38 => P8 | D39 => P7 | D40 => P6 | D41 => P5 | D42 => P4 | D43 => P3 | D44 => P2 | D45 => P1 | D46 => P0 | D47 => P127 | D48 => P126 | D49 => P125 | D50 => P124 | D51 => P123 | D52 => P122 | D53 => P121 | D54 => P120 | D55 => P119 | D56 => P118 | D57 => P117 | D58 => P116 | D59 => P115 | D60 => P114 | D61 => P113 | D62 => P112 | D63 => P111 end
  | D47 => match b with D0 => P47 | D1 => P46 | D2 => P45 | D3 => P44 | D4 => P43 | D5 => P42 | D6 => P41 | D7 => P40 | D8 => P39 | D9 => P38 | D10 => P37 | D11 => P36 | D12 => P35 | D13 => P34 | D14 => P33 | D15 => P32 | D16 => P31 | D17 => P30 | D18 => P29 | D19 => P28 | D20 => P27 | D21 => P26 | D22 => P25 | D23 => P24 | D24 => P23 | D25 => P22 | D26 => P21 | D27 => P20 | D28 => P19 | D29 => P18 | D30 => P17 | D31 => P16 | D32 => P15 | D33 => P14 | D34 => P13 | D35 => P12 | D36 => P11 | D37 => P10 | D38 => P9 | D39 => P8 | D40 => P7 | D41 => P6 | D42 => P5 | D43 => P4 | D44 => P3 | D45 => P2 | D46 => P1 | D47 => P0 | D48 => P127 | D49 => P126 | D50 => P125 | D51 => P124 | D52 => P123 | D53 => P122 | D54 => P121 | D55 => P120 | D56 => P119 | D57 => P118 | D58 => P117 | D59 => P116 | D60 => P115 | D61 => P114 | D62 => P113 | D63 => P112 end
  | D48 => match b with D0 => P48 | D1 => P47 | D2 => P46 | D3 => P45 | D4 => P44 | D5 => P43 | D6 => P42 | D7 => P41 | D8 => P40 | D9 => P39 | D10 => P38 | D11 => P37 | D12 => P36 | D13 => P35 | D14 => P34 | D15 => P33 | D16 => P32 | D17 => P31 | D18 => P30 | D19 => P29 | D20 => P28 | D21 => P27 | D22 => P26 | D23 => P25 | D24 => P24 | D25 => P23 | D26 => P22 | D27 => P21 | D28 => P20 | D29 => P19 | D30 => P18 | D31 => P17 | D32 => P16 | D33 => P15 | D34 => P14 | D35 => P13 | D36 => P12 | D37 => P11 | D38 => P10 | D39 => P9 | D40 => P8 | D41 => P7 | D42 => P6 | D43 => P5 | D44 => P4 | D45 => P3 | D46 => P2 | D47 => P1 | D48 => P0 | D49 => P127 | D50 => P126 | D51 => P125 | D52 => P124 | D53 => P123 | D54 => P122 | D55 => P121 | D56 => P120 | D57 => P119 | D58 => P118 | D59 => P117 | D60 => P116 | D61 => P115 | D62 => P114 | D63 => P113 end
  | D49 => match b with D0 => P49 | D1 => P48 | D2 => P47 | D3 => P46 | D4 => P45 | D5 => P44 | D6 => P43 | D7 => P42 | D8 => P41 | D9 => P40 | D10 => P39 | D11 => P38 | D12 => P37 | D13 => P36 | D14 => P35 | D15 => P34 | D16 => P33 | D17 => P32 | D18 => P31 | D19 => P30 | D20 => P29 | D21 => P28 | D22 => P27 | D23 => P26 | D24 => P25 | D25 => P24 | D26 => P23 | D27 => P22 | D28 => P21 | D29 => P20 | D30 => P19 | D31 => P18 | D32 => P17 | D33 => P16 | D34 => P15 | D35 => P14 | D36 => P13 | D37 => P12 | D38 => P11 | D39 => P10 | D40 => P9 | D41 => P8 | D42 => P7 | D43 => P6 | D44 => P5 | D45 => P4 | D46 => P3 | D47 => P2 | D48 => P1 | D49 => P0 | D50 => P127 | D51 => P126 | D52 => P125 | D53 => P124 | D54 => P123 | D55 => P122 | D56 => P121 | D57 => P120 | D58 => P119 | D59 => P118 | D60 => P117 | D61 => P116 | D62 => P115 | D63 => P114 end
  | D50 => match b with D0 => P50 | D1 => P49 | D2 => P48 | D3 => P47 | D4 => P46 | D5 => P45 | D6 => P44 | D7 => P43 | D8 => P42 | D9 => P41 | D10 => P40 | D11 => P39 | D12 => P38 | D13 => P37 | D14 => P36 | D15 => P35 | D16 => P34 | D17 => P33 | D18 => P32 | D19 => P31 | D20 => P30 | D21 => P29 | D22 => P28 | D23 => P27 | D24 => P26 | D25 => P25 | D26 => P24 | D27 => P23 | D28 => P22 | D29 => P21 | D30 => P20 | D31 => P19 | D32 => P18 | D33 => P17 | D34 => P16 | D35 => P15 | D36 => P14 | D37 => P13 | D38 => P12 | D39 => P11 | D40 => P10 | D41 => P9 | D42 => P8 | D43 => P7 | D44 => P6 | D45 => P5 | D46 => P4 | D47 => P3 | D48 => P2 | D49 => P1 | D50 => P0 | D51 => P127 | D52 => P126 | D53 => P125 | D54 => P124 | D55 => P123 | D56 => P122 | D57 => P121 | D58 => P120 | D59 => P119 | D60 => P118 | D61 => P117 | D62 => P116 | D63 => P115 end
  | D51 => match b with D0 => P51 | D1 => P50 | D2 => P49 | D3 => P48 | D4 => P47 | D5 => P46 | D6 => P45 | D7 => P44 | D8 => P43 | D9 => P42 | D10 => P41 | D11 => P40 | D12 => P39 | D13 => P38 | D14 => P37 | D15 => P36 | D16 => P35 | D17 => P34 | D18 => P33 | D19 => P32 | D20 => P31 | D21 => P30 | D22 => P29 | D23 => P28 | D24 => P27 | D25 => P26 | D26 => P25 | D27 => P24 | D28 => P23 | D29 => P22 | D30 => P21 | D31 => P20 | D32 => P19 | D33 => P18 | D34 => P17 | D35 => P16 | D36 => P15 | D37 => P14 | D38 => P13 | D39 => P12 | D40 => P11 | D41 => P10 | D42 => P9 | D43 => P8 | D44 => P7 | D45 => P6 | D46 => P5 | D47 => P4 | D48 => P3 | D49 => P2 | D50 => P1 | D51 => P0 | D52 => P127 | D53 => P126 | D54 => P125 | D55 => P124 | D56 => P123 | D57 => P122 | D58 => P121 | D59 => P120 | D60 => P119 | D61 => P118 | D62 => P117 | D63 => P116 end
  | D52 => match b with D0 => P52 | D1 => P51 | D2 => P50 | D3 => P49 | D4 => P48 | D5 => P47 | D6 => P46 | D7 => P45 | D8 => P44 | D9 => P43 | D10 => P42 | D11 => P41 | D12 => P40 | D13 => P39 | D14 => P38 | D15 => P37 | D16 => P36 | D17 => P35 | D18 => P34 | D19 => P33 | D20 => P32 | D21 => P31 | D22 => P30 | D23 => P29 | D24 => P28 | D25 => P27 | D26 => P26 | D27 => P25 | D28 => P24 | D29 => P23 | D30 => P22 | D31 => P21 | D32 => P20 | D33 => P19 | D34 => P18 | D35 => P17 | D36 => P16 | D37 => P15 | D38 => P14 | D39 => P13 | D40 => P12 | D41 => P11 | D42 => P10 | D43 => P9 | D44 => P8 | D45 => P7 | D46 => P6 | D47 => P5 | D48 => P4 | D49 => P3 | D50 => P2 | D51 => P1 | D52 => P0 | D53 => P127 | D54 => P126 | D55 => P125 | D56 => P124 | D57 => P123 | D58 => P122 | D59 => P121 | D60 => P120 | D61 => P119 | D62 => P118 | D63 => P117 end
  | D53 => match b with D0 => P53 | D1 => P52 | D2 => P51 | D3 => P50 | D4 => P49 | D5 => P48 | D6 => P47 | D7 => P46 | D8 => P45 | D9 => P44 | D10 => P43 | D11 => P42 | D12 => P41 | D13 => P40 | D14 => P39 | D15 => P38 | D16 => P37 | D17 => P36 | D18 => P35 | D19 => P34 | D20 => P33 | D21 => P32 | D22 => P31 | D23 => P30 | D24 => P29 | D25 => P28 | D26 => P27 | D27 => P26 | D28 => P25 | D29 => P24 | D30 => P23 | D31 => P22 | D32 => P21 | D33 => P20 | D34 => P19 | D35 => P18 | D36 => P17 | D37 => P16 | D38 => P15 | D39 => P14 | D40 => P13 | D41 => P12 | D42 => P11 | D43 => P10 | D44 => P9 | D45 => P8 | D46 => P7 | D47 => P6 | D48 => P5 | D49 => P4 | D50 => P3 | D51 => P2 | D52 => P1 | D53 => P0 | D54 => P127 | D55 => P126 | D56 => P125 | D57 => P124 | D58 => P123 | D59 => P122 | D60 => P121 | D61 => P120 | D62 => P119 | D63 => P118 end
  | D54 => match b with D0 => P54 | D1 => P53 | D2 => P52 | D3 => P51 | D4 => P50 | D5 => P49 | D6 => P48 | D7 => P47 | D8 => P46 | D9 => P45 | D10 => P44 | D11 => P43 | D12 => P42 | D13 => P41 | D14 => P40 | D15 => P39 | D16 => P38 | D17 => P37 | D18 => P36 | D19 => P35 | D20 => P34 | D21 => P33 | D22 => P32 | D23 => P31 | D24 => P30 | D25 => P29 | D26 => P28 | D27 => P27 | D28 => P26 | D29 => P25 | D30 => P24 | D31 => P23 | D32 => P22 | D33 => P21 | D34 => P20 | D35 => P19 | D36 => P18 | D37 => P17 | D38 => P16 | D39 => P15 | D40 => P14 | D41 => P13 | D42 => P12 | D43 => P11 | D44 => P10 | D45 => P9 | D46 => P8 | D47 => P7 | D48 => P6 | D49 => P5 | D50 => P4 | D51 => P3 | D52 => P2 | D53 => P1 | D54 => P0 | D55 => P127 | D56 => P126 | D57 => P125 | D58 => P124 | D59 => P123 | D60 => P122 | D61 => P121 | D62 => P120 | D63 => P119 end
  | D55 => match b with D0 => P55 | D1 => P54 | D2 => P53 | D3 => P52 | D4 => P51 | D5 => P50 | D6 => P49 | D7 => P48 | D8 => P47 | D9 => P46 | D10 => P45 | D11 => P44 | D12 => P43 | D13 => P42 | D14 => P41 | D15 => P40 | D16 => P39 | D17 => P38 | D18 => P37 | D19 => P36 | D20 => P35 | D21 => P34 | D22 => P33 | D23 => P32 | D24 => P31 | D25 => P30 | D26 => P29 | D27 => P28 | D28 => P27 | D29 => P26 | D30 => P25 | D31 => P24 | D32 => P23 | D33 => P22 | D34 => P21 | D35 => P20 | D36 => P19 | D37 => P18 | D38 => P17 | D39 => P16 | D40 => P15 | D41 => P14 | D42 => P13 | D43 => P12 | D44 => P11 | D45 => P10 | D46 => P9 | D47 => P8 | D48 => P7 | D49 => P6 | D50 => P5 | D51 => P4 | D52 => P3 | D53 => P2 | D54 => P1 | D55 => P0 | D56 => P127 | D57 => P126 | D58 => P125 | D59 => P124 | D60 => P123 | D61 => P122 | D62 => P121 | D63 => P120 end
  | D56 => match b with D0 => P56 | D1 => P55 | D2 => P54 | D3 => P53 | D4 => P52 | D5 => P51 | D6 => P50 | D7 => P49 | D8 => P48 | D9 => P47 | D10 => P46 | D11 => P45 | D12 => P44 | D13 => P43 | D14 => P42 | D15 => P41 | D16 => P40 | D17 => P39 | D18 => P38 | D19 => P37 | D20 => P36 | D21 => P35 | D22 => P34 | D23 => P33 | D24 => P32 | D25 => P31 | D26 => P30 | D27 => P29 | D28 => P28 | D29 => P27 | D30 => P26 | D31 => P25 | D32 => P24 | D33 => P23 | D34 => P22 | D35 => P21 | D36 => P20 | D37 => P19 | D38 => P18 | D39 => P17 | D40 => P16 | D41 => P15 | D42 => P14 | D43 => P13 | D44 => P12 | D45 => P11 | D46 => P10 | D47 => P9 | D48 => P8 | D49 => P7 | D50 => P6 | D51 => P5 | D52 => P4 | D53 => P3 | D54 => P2 | D55 => P1 | D56 => P0 | D57 => P127 | D58 => P126 | D59 => P125 | D60 => P124 | D61 => P123 | D62 => P122 | D63 => P121 end
  | D57 => match b with D0 => P57 | D1 => P56 | D2 => P55 | D3 => P54 | D4 => P53 | D5 => P52 | D6 => P51 | D7 => P50 | D8 => P49 | D9 => P48 | D10 => P47 | D11 => P46 | D12 => P45 | D13 => P44 | D14 => P43 | D15 => P42 | D16 => P41 | D17 => P40 | D18 => P39 | D19 => P38 | D20 => P37 | D21 => P36 | D22 => P35 | D23 => P34 | D24 => P33 | D25 => P32 | D26 => P31 | D27 => P30 | D28 => P29 | D29 => P28 | D30 => P27 | D31 => P26 | D32 => P25 | D33 => P24 | D34 => P23 | D35 => P22 | D36 => P21 | D37 => P20 | D38 => P19 | D39 => P18 | D40 => P17 | D41 => P16 | D42 => P15 | D43 => P14 | D44 => P13 | D45 => P12 | D46 => P11 | D47 => P10 | D48 => P9 | D49 => P8 | D50 => P7 | D51 => P6 | D52 => P5 | D53 => P4 | D54 => P3 | D55 => P2 | D56 => P1 | D57 => P0 | D58 => P127 | D59 => P126 | D60 => P125 | D61 => P124 | D62 => P123 | D63 => P122 end
  | D58 => match b with D0 => P58 | D1 => P57 | D2 => P56 | D3 => P55 | D4 => P54 | D5 => P53 | D6 => P52 | D7 => P51 | D8 => P50 | D9 => P49 | D10 => P48 | D11 => P47 | D12 => P46 | D13 => P45 | D14 => P44 | D15 => P43 | D16 => P42 | D17 => P41 | D18 => P40 | D19 => P39 | D20 => P38 | D21 => P37 | D22 => P36 | D23 => P35 | D24 => P34 | D25 => P33 | D26 => P32 | D27 => P31 | D28 => P30 | D29 => P29 | D30 => P28 | D31 => P27 | D32 => P26 | D33 => P25 | D34 => P24 | D35 => P23 | D36 => P22 | D37 => P21 | D38 => P20 | D39 => P19 | D40 => P18 | D41 => P17 | D42 => P16 | D43 => P15 | D44 => P14 | D45 => P13 | D46 => P12 | D47 => P11 | D48 => P10 | D49 => P9 | D50 => P8 | D51 => P7 | D52 => P6 | D53 => P5 | D54 => P4 | D55 => P3 | D56 => P2 | D57 => P1 | D58 => P0 | D59 => P127 | D60 => P126 | D61 => P125 | D62 => P124 | D63 => P123 end
  | D59 => match b with D0 => P59 | D1 => P58 | D2 => P57 | D3 => P56 | D4 => P55 | D5 => P54 | D6 => P53 | D7 => P52 | D8 => P51 | D9 => P50 | D10 => P49 | D11 => P48 | D12 => P47 | D13 => P46 | D14 => P45 | D15 => P44 | D16 => P43 | D17 => P42 | D18 => P41 | D19 => P40 | D20 => P39 | D21 => P38 | D22 => P37 | D23 => P36 | D24 => P35 | D25 => P34 | D26 => P33 | D27 => P32 | D28 => P31 | D29 => P30 | D30 => P29 | D31 => P28 | D32 => P27 | D33 => P26 | D34 => P25 | D35 => P24 | D36 => P23 | D37 => P22 | D38 => P21 | D39 => P20 | D40 => P19 | D41 => P18 | D42 => P17 | D43 => P16 | D44 => P15 | D45 => P14 | D46 => P13 | D47 => P12 | D48 => P11 | D49 => P10 | D50 => P9 | D51 => P8 | D52 => P7 | D53 => P6 | D54 => P5 | D55 => P4 | D56 => P3 | D57 => P2 | D58 => P1 | D59 => P0 | D60 => P127 | D61 => P126 | D62 => P125 | D63 => P124 end
  | D60 => match b with D0 => P60 | D1 => P59 | D2 => P58 | D3 => P57 | D4 => P56 | D5 => P55 | D6 => P54 | D7 => P53 | D8 => P52 | D9 => P51 | D10 => P50 | D11 => P49 | D12 => P48 | D13 => P47 | D14 => P46 | D15 => P45 | D16 => P44 | D17 => P43 | D18 => P42 | D19 => P41 | D20 => P40 | D21 => P39 | D22 => P38 | D23 => P37 | D24 => P36 | D25 => P35 | D26 => P34 | D27 => P33 | D28 => P32 | D29 => P31 | D30 => P30 | D31 => P29 | D32 => P28 | D33 => P27 | D34 => P26 | D35 => P25 | D36 => P24 | D37 => P23 | D38 => P22 | D39 => P21 | D40 => P20 | D41 => P19 | D42 => P18 | D43 => P17 | D44 => P16 | D45 => P15 | D46 => P14 | D47 => P13 | D48 => P12 | D49 => P11 | D50 => P10 | D51 => P9 | D52 => P8 | D53 => P7 | D54 => P6 | D55 => P5 | D56 => P4 | D57 => P3 | D58 => P2 | D59 => P1 | D60 => P0 | D61 => P127 | D62 => P126 | D63 => P125 end
  | D61 => match b with D0 => P61 | D1 => P60 | D2 => P59 | D3 => P58 | D4 => P57 | D5 => P56 | D6 => P55 | D7 => P54 | D8 => P53 | D9 => P52 | D10 => P51 | D11 => P50 | D12 => P49 | D13 => P48 | D14 => P47 | D15 => P46 | D16 => P45 | D17 => P44 | D18 => P43 | D19 => P42 | D20 => P41 | D21 => P40 | D22 => P39 | D23 => P38 | D24 => P37 | D25 => P36 | D26 => P35 | D27 => P34 | D28 => P33 | D29 => P32 | D30 => P31 | D31 => P30 | D32 => P29 | D33 => P28 | D34 => P27 | D35 => P26 | D36 => P25 | D37 => P24 | D38 => P23 | D39 => P22 | D40 => P21 | D41 => P20 | D42 => P19 | D43 => P18 | D44 => P17 | D45 => P16 | D46 => P15 | D47 => P14 | D48 => P13 | D49 => P12 | D50 => P11 | D51 => P10 | D52 => P9 | D53 => P8 | D54 => P7 | D55 => P6 | D56 => P5 | D57 => P4 | D58 => P3 | D59 => P2 | D60 => P1 | D61 => P0 | D62 => P127 | D63 => P126 end
  | D62 => match b with D0 => P62 | D1 => P61 | D2 => P60 | D3 => P59 | D4 => P58 | D5 => P57 | D6 => P56 | D7 => P55 | D8 => P54 | D9 => P53 | D10 => P52 | D11 => P51 | D12 => P50 | D13 => P49 | D14 => P48 | D15 => P47 | D16 => P46 | D17 => P45 | D18 => P44 | D19 => P43 | D20 => P42 | D21 => P41 | D22 => P40 | D23 => P39 | D24 => P38 | D25 => P37 | D26 => P36 | D27 => P35 | D28 => P34 | D29 => P33 | D30 => P32 | D31 => P31 | D32 => P30 | D33 => P29 | D34 => P28 | D35 => P27 | D36 => P26 | D37 => P25 | D38 => P24 | D39 => P23 | D40 => P22 | D41 => P21 | D42 => P20 | D43 => P19 | D44 => P18 | D45 => P17 | D46 => P16 | D47 => P15 | D48 => P14 | D49 => P13 | D50 => P12 | D51 => P11 | D52 => P10 | D53 => P9 | D54 => P8 | D55 => P7 | D56 => P6 | D57 => P5 | D58 => P4 | D59 => P3 | D60 => P2 | D61 => P1 | D62 => P0 | D63 => P127 end
  | D63 => match b with D0 => P63 | D1 => P62 | D2 => P61 | D3 => P60 | D4 => P59 | D5 => P58 | D6 => P57 | D7 => P56 | D8 => P55 | D9 => P54 | D10 => P53 | D11 => P52 | D12 => P51 | D13 => P50 | D14 => P49 | D15 => P48 | D16 => P47 | D17 => P46 | D18 => P45 | D19 => P44 | D20 => P43 | D21 => P42 | D22 => P41 | D23 => P40 | D24 => P39 | D25 => P38 | D26 => P37 | D27 => P36 | D28 => P35 | D29 => P34 | D30 => P33 | D31 => P32 | D32 => P31 | D33 => P30 | D34 => P29 | D35 => P28 | D36 => P27 | D37 => P26 | D38 => P25 | D39 => P24 | D40 => P23 | D41 => P22 | D42 => P21 | D43 => P20 | D44 => P19 | D45 => P18 | D46 => P17 | D47 => P16 | D48 => P15 | D49 => P14 | D50 => P13 | D51 => P12 | D52 => P11 | D53 => P10 | D54 => P9 | D55 => P8 | D56 => P7 | D57 => P6 | D58 => P5 | D59 => P4 | D60 => P3 | D61 => P2 | D62 => P1 | D63 => P0 end
  end.

Definition sub2x64 (br : C6) (a b : D64) : R256 :=
  match br with
  | C0 => match a with
    | D0 => match b with D0 => W0 | D1 => W126 | D2 => W124 | D3 => W122 | D4 => W120 | D5 => W118 | D6 => W116 | D7 => W114 | D8 => W112 | D9 => W110 | D10 => W108 | D11 => W106 | D12 => W104 | D13 => W102 | D14 => W100 | D15 => W98 | D16 => W96 | D17 => W94 | D18 => W92 | D19 => W90 | D20 => W88 | D21 => W86 | D22 => W84 | D23 => W82 | D24 => W80 | D25 => W78 | D26 => W76 | D27 => W74 | D28 => W72 | D29 => W70 | D30 => W68 | D31 => W66 | D32 => W64 | D33 => W190 | D34 => W188 | D35 => W186 | D36 => W184 | D37 => W182 | D38 => W180 | D39 => W178 | D40 => W176 | D41 => W174 | D42 => W172 | D43 => W170 | D44 => W168 | D45 => W166 | D46 => W164 | D47 => W162 | D48 => W160 | D49 => W158 | D50 => W156 | D51 => W154 | D52 => W152 | D53 => W150 | D54 => W148 | D55 => W146 | D56 => W144 | D57 => W142 | D58 => W140 | D59 => W138 | D60 => W136 | D61 => W134 | D62 => W132 | D63 => W130 end
    | D1 => match b with D0 => W1 | D1 => W127 | D2 => W125 | D3 => W123 | D4 => W121 | D5 => W119 | D6 => W117 | D7 => W115 | D8 => W113 | D9 => W111 | D10 => W109 | D11 => W107 | D12 => W105 | D13 => W103 | D14 => W101 | D15 => W99 | D16 => W97 | D17 => W95 | D18 => W93 | D19 => W91 | D20 => W89 | D21 => W87 | D22 => W85 | D23 => W83 | D24 => W81 | D25 => W79 | D26 => W77 | D27 => W75 | D28 => W73 | D29 => W71 | D30 => W69 | D31 => W67 | D32 => W65 | D33 => W191 | D34 => W189 | D35 => W187 | D36 => W185 | D37 => W183 | D38 => W181 | D39 => W179 | D40 => W177 | D41 => W175 | D42 => W173 | D43 => W171 | D44 => W169 | D45 => W167 | D46 => W165 | D47 => W163 | D48 => W161 | D49 => W159 | D50 => W157 | D51 => W155 | D52 => W153 | D53 => W151 | D54 => W149 | D55 => W147 | D56 => W145 | D57 => W143 | D58 => W141 | D59 => W139 | D60 => W137 | D61 => W135 | D62 => W133 | D63 => W131 end
    | D2 => match b with D0 => W2 | D1 => W0 | D2 => W126 | D3 => W124 | D4 => W122 | D5 => W120 | D6 => W118 | D7 => W116 | D8 => W114 | D9 => W112 | D10 => W110 | D11 => W108 | D12 => W106 | D13 => W104 | D14 => W102 | D15 => W100 | D16 => W98 | D17 => W96 | D18 => W94 | D19 => W92 | D20 => W90 | D21 => W88 | D22 => W86 | D23 => W84 | D24 => W82 | D25 => W80 | D26 => W78 | D27 => W76 | D28 => W74 | D29 => W72 | D30 => W70 | D31 => W68 | D32 => W66 | D33 => W64 | D34 => W190 | D35 => W188 | D36 => W186 | D37 => W184 | D38 => W182 | D39 => W180 | D40 => W178 | D41 => W176 | D42 => W174 | D43 => W172 | D44 => W170 | D45 => W168 | D46 => W166 | D47 => W164 | D48 => W162 | D49 => W160 | D50 => W158 | D51 => W156 | D52 => W154 | D53 => W152 | D54 => W150 | D55 => W148 | D56 => W146 | D57 => W144 | D58 => W142 | D59 => W140 | D60 => W138 | D61 => W136 | D62 => W134 | D63 => W132 end
    | D3 => match b with D0 => W3 | D1 => W1 | D2 => W127 | D3 => W125 | D4 => W123 | D5 => W121 | D6 => W119 | D7 => W117 | D8 => W115 | D9 => W113 | D10 => W111 | D11 => W109 | D12 => W107 | D13 => W105 | D14 => W103 | D15 => W101 | D16 => W99 | D17 => W97 | D18 => W95 | D19 => W93 | D20 => W91 | D21 => W89 | D22 => W87 | D23 => W85 | D24 => W83 | D25 => W81 | D26 => W79 | D27 => W77 | D28 => W75 | D29 => W73 | D30 => W71 | D31 => W69 | D32 => W67 | D33 => W65 | D34 => W191 | D35 => W189 | D36 => W187 | D37 => W185 | D38 => W183 | D39 => W181 | D40 => W179 | D41 => W177 | D42 => W175 | D43 => W173 | D44 => W171 | D45 => W169 | D46 => W167 | D47 => W165 | D48 => W163 | D49 => W161 | D50 => W159 | D51 => W157 | D52 => W155 | D53 => W153 | D54 => W151 | D55 => W149 | D56 => W147 | D57 => W145 | D58 => W143 | D59 => W141 | D60 => W139 | D61 => W137 | D62 => W135 | D63 => W133 end
    | D4 => match b with D0 => W4 | D1 => W2 | D2 => W0 | D3 => W126 | D4 => W124 | D5 => W122 | D6 => W120 | D7 => W118 | D8 => W116 | D9 => W114 | D10 => W112 | D11 => W110 | D12 => W108 | D13 => W106 | D14 => W104 | D15 => W102 | D16 => W100 | D17 => W98 | D18 => W96 | D19 => W94 | D20 => W92 | D21 => W90 | D22 => W88 | D23 => W86 | D24 => W84 | D25 => W82 | D26 => W80 | D27 => W78 | D28 => W76 | D29 => W74 | D30 => W72 | D31 => W70 | D32 => W68 | D33 => W66 | D34 => W64 | D35 => W190 | D36 => W188 | D37 => W186 | D38 => W184 | D39 => W182 | D40 => W180 | D41 => W178 | D42 => W176 | D43 => W174 | D44 => W172 | D45 => W170 | D46 => W168 | D47 => W166 | D48 => W164 | D49 => W162 | D50 => W160 | D51 => W158 | D52 => W156 | D53 => W154 | D54 => W152 | D55 => W150 | D56 => W148 | D57 => W146 | D58 => W144 | D59 => W142 | D60 => W140 | D61 => W138 | D62 => W136 | D63 => W134 end
    | D5 => match b with D0 => W5 | D1 => W3 | D2 => W1 | D3 => W127 | D4 => W125 | D5 => W123 | D6 => W121 | D7 => W119 | D8 => W117 | D9 => W115 | D10 => W113 | D11 => W111 | D12 => W109 | D13 => W107 | D14 => W105 | D15 => W103 | D16 => W101 | D17 => W99 | D18 => W97 | D19 => W95 | D20 => W93 | D21 => W91 | D22 => W89 | D23 => W87 | D24 => W85 | D25 => W83 | D26 => W81 | D27 => W79 | D28 => W77 | D29 => W75 | D30 => W73 | D31 => W71 | D32 => W69 | D33 => W67 | D34 => W65 | D35 => W191 | D36 => W189 | D37 => W187 | D38 => W185 | D39 => W183 | D40 => W181 | D41 => W179 | D42 => W177 | D43 => W175 | D44 => W173 | D45 => W171 | D46 => W169 | D47 => W167 | D48 => W165 | D49 => W163 | D50 => W161 | D51 => W159 | D52 => W157 | D53 => W155 | D54 => W153 | D55 => W151 | D56 => W149 | D57 => W147 | D58 => W145 | D59 => W143 | D60 => W141 | D61 => W139 | D62 => W137 | D63 => W135 end
    | D6 => match b with D0 => W6 | D1 => W4 | D2 => W2 | D3 => W0 | D4 => W126 | D5 => W124 | D6 => W122 | D7 => W120 | D8 => W118 | D9 => W116 | D10 => W114 | D11 => W112 | D12 => W110 | D13 => W108 | D14 => W106 | D15 => W104 | D16 => W102 | D17 => W100 | D18 => W98 | D19 => W96 | D20 => W94 | D21 => W92 | D22 => W90 | D23 => W88 | D24 => W86 | D25 => W84 | D26 => W82 | D27 => W80 | D28 => W78 | D29 => W76 | D30 => W74 | D31 => W72 | D32 => W70 | D33 => W68 | D34 => W66 | D35 => W64 | D36 => W190 | D37 => W188 | D38 => W186 | D39 => W184 | D40 => W182 | D41 => W180 | D42 => W178 | D43 => W176 | D44 => W174 | D45 => W172 | D46 => W170 | D47 => W168 | D48 => W166 | D49 => W164 | D50 => W162 | D51 => W160 | D52 => W158 | D53 => W156 | D54 => W154 | D55 => W152 | D56 => W150 | D57 => W148 | D58 => W146 | D59 => W144 | D60 => W142 | D61 => W140 | D62 => W138 | D63 => W136 end
    | D7 => match b with D0 => W7 | D1 => W5 | D2 => W3 | D3 => W1 | D4 => W127 | D5 => W125 | D6 => W123 | D7 => W121 | D8 => W119 | D9 => W117 | D10 => W115 | D11 => W113 | D12 => W111 | D13 => W109 | D14 => W107 | D15 => W105 | D16 => W103 | D17 => W101 | D18 => W99 | D19 => W97 | D20 => W95 | D21 => W93 | D22 => W91 | D23 => W89 | D24 => W87 | D25 => W85 | D26 => W83 | D27 => W81 | D28 => W79 | D29 => W77 | D30 => W75 | D31 => W73 | D32 => W71 | D33 => W69 | D34 => W67 | D35 => W65 | D36 => W191 | D37 => W189 | D38 => W187 | D39 => W185 | D40 => W183 | D41 => W181 | D42 => W179 | D43 => W177 | D44 => W175 | D45 => W173 | D46 => W171 | D47 => W169 | D48 => W167 | D49 => W165 | D50 => W163 | D51 => W161 | D52 => W159 | D53 => W157 | D54 => W155 | D55 => W153 | D56 => W151 | D57 => W149 | D58 => W147 | D59 => W145 | D60 => W143 | D61 => W141 | D62 => W139 | D63 => W137 end
    | D8 => match b with D0 => W8 | D1 => W6 | D2 => W4 | D3 => W2 | D4 => W0 | D5 => W126 | D6 => W124 | D7 => W122 | D8 => W120 | D9 => W118 | D10 => W116 | D11 => W114 | D12 => W112 | D13 => W110 | D14 => W108 | D15 => W106 | D16 => W104 | D17 => W102 | D18 => W100 | D19 => W98 | D20 => W96 | D21 => W94 | D22 => W92 | D23 => W90 | D24 => W88 | D25 => W86 | D26 => W84 | D27 => W82 | D28 => W80 | D29 => W78 | D30 => W76 | D31 => W74 | D32 => W72 | D33 => W70 | D34 => W68 | D35 => W66 | D36 => W64 | D37 => W190 | D38 => W188 | D39 => W186 | D40 => W184 | D41 => W182 | D42 => W180 | D43 => W178 | D44 => W176 | D45 => W174 | D46 => W172 | D47 => W170 | D48 => W168 | D49 => W166 | D50 => W164 | D51 => W162 | D52 => W160 | D53 => W158 | D54 => W156 | D55 => W154 | D56 => W152 | D57 => W150 | D58 => W148 | D59 => W146 | D60 => W144 | D61 => W142 | D62 => W140 | D63 => W138 end
    | D9 => match b with D0 => W9 | D1 => W7 | D2 => W5 | D3 => W3 | D4 => W1 | D5 => W127 | D6 => W125 | D7 => W123 | D8 => W121 | D9 => W119 | D10 => W117 | D11 => W115 | D12 => W113 | D13 => W111 | D14 => W109 | D15 => W107 | D16 => W105 | D17 => W103 | D18 => W101 | D19 => W99 | D20 => W97 | D21 => W95 | D22 => W93 | D23 => W91 | D24 => W89 | D25 => W87 | D26 => W85 | D27 => W83 | D28 => W81 | D29 => W79 | D30 => W77 | D31 => W75 | D32 => W73 | D33 => W71 | D34 => W69 | D35 => W67 | D36 => W65 | D37 => W191 | D38 => W189 | D39 => W187 | D40 => W185 | D41 => W183 | D42 => W181 | D43 => W179 | D44 => W177 | D45 => W175 | D46 => W173 | D47 => W171 | D48 => W169 | D49 => W167 | D50 => W165 | D51 => W163 | D52 => W161 | D53 => W159 | D54 => W157 | D55 => W155 | D56 => W153 | D57 => W151 | D58 => W149 | D59 => W147 | D60 => W145 | D61 => W143 | D62 => W141 | D63 => W139 end
    | D10 => match b with D0 => W10 | D1 => W8 | D2 => W6 | D3 => W4 | D4 => W2 | D5 => W0 | D6 => W126 | D7 => W124 | D8 => W122 | D9 => W120 | D10 => W118 | D11 => W116 | D12 => W114 | D13 => W112 | D14 => W110 | D15 => W108 | D16 => W106 | D17 => W104 | D18 => W102 | D19 => W100 | D20 => W98 | D21 => W96 | D22 => W94 | D23 => W92 | D24 => W90 | D25 => W88 | D26 => W86 | D27 => W84 | D28 => W82 | D29 => W80 | D30 => W78 | D31 => W76 | D32 => W74 | D33 => W72 | D34 => W70 | D35 => W68 | D36 => W66 | D37 => W64 | D38 => W190 | D39 => W188 | D40 => W186 | D41 => W184 | D42 => W182 | D43 => W180 | D44 => W178 | D45 => W176 | D46 => W174 | D47 => W172 | D48 => W170 | D49 => W168 | D50 => W166 | D51 => W164 | D52 => W162 | D53 => W160 | D54 => W158 | D55 => W156 | D56 => W154 | D57 => W152 | D58 => W150 | D59 => W148 | D60 => W146 | D61 => W144 | D62 => W142 | D63 => W140 end
    | D11 => match b with D0 => W11 | D1 => W9 | D2 => W7 | D3 => W5 | D4 => W3 | D5 => W1 | D6 => W127 | D7 => W125 | D8 => W123 | D9 => W121 | D10 => W119 | D11 => W117 | D12 => W115 | D13 => W113 | D14 => W111 | D15 => W109 | D16 => W107 | D17 => W105 | D18 => W103 | D19 => W101 | D20 => W99 | D21 => W97 | D22 => W95 | D23 => W93 | D24 => W91 | D25 => W89 | D26 => W87 | D27 => W85 | D28 => W83 | D29 => W81 | D30 => W79 | D31 => W77 | D32 => W75 | D33 => W73 | D34 => W71 | D35 => W69 | D36 => W67 | D37 => W65 | D38 => W191 | D39 => W189 | D40 => W187 | D41 => W185 | D42 => W183 | D43 => W181 | D44 => W179 | D45 => W177 | D46 => W175 | D47 => W173 | D48 => W171 | D49 => W169 | D50 => W167 | D51 => W165 | D52 => W163 | D53 => W161 | D54 => W159 | D55 => W157 | D56 => W155 | D57 => W153 | D58 => W151 | D59 => W149 | D60 => W147 | D61 => W145 | D62 => W143 | D63 => W141 end
    | D12 => match b with D0 => W12 | D1 => W10 | D2 => W8 | D3 => W6 | D4 => W4 | D5 => W2 | D6 => W0 | D7 => W126 | D8 => W124 | D9 => W122 | D10 => W120 | D11 => W118 | D12 => W116 | D13 => W114 | D14 => W112 | D15 => W110 | D16 => W108 | D17 => W106 | D18 => W104 | D19 => W102 | D20 => W100 | D21 => W98 | D22 => W96 | D23 => W94 | D24 => W92 | D25 => W90 | D26 => W88 | D27 => W86 | D28 => W84 | D29 => W82 | D30 => W80 | D31 => W78 | D32 => W76 | D33 => W74 | D34 => W72 | D35 => W70 | D36 => W68 | D37 => W66 | D38 => W64 | D39 => W190 | D40 => W188 | D41 => W186 | D42 => W184 | D43 => W182 | D44 => W180 | D45 => W178 | D46 => W176 | D47 => W174 | D48 => W172 | D49 => W170 | D50 => W168 | D51 => W166 | D52 => W164 | D53 => W162 | D54 => W160 | D55 => W158 | D56 => W156 | D57 => W154 | D58 => W152 | D59 => W150 | D60 => W148 | D61 => W146 | D62 => W144 | D63 => W142 end
    | D13 => match b with D0 => W13 | D1 => W11 | D2 => W9 | D3 => W7 | D4 => W5 | D5 => W3 | D6 => W1 | D7 => W127 | D8 => W125 | D9 => W123 | D10 => W121 | D11 => W119 | D12 => W117 | D13 => W115 | D14 => W113 | D15 => W111 | D16 => W109 | D17 => W107 | D18 => W105 | D19 => W103 | D20 => W101 | D21 => W99 | D22 => W97 | D23 => W95 | D24 => W93 | D25 => W91 | D26 => W89 | D27 => W87 | D28 => W85 | D29 => W83 | D30 => W81 | D31 => W79 | D32 => W77 | D33 => W75 | D34 => W73 | D35 => W71 | D36 => W69 | D37 => W67 | D38 => W65 | D39 => W191 | D40 => W189 | D41 => W187 | D42 => W185 | D43 => W183 | D44 => W181 | D45 => W179 | D46 => W177 | D47 => W175 | D48 => W173 | D49 => W171 | D50 => W169 | D51 => W167 | D52 => W165 | D53 => W163 | D54 => W161 | D55 => W159 | D56 => W157 | D57 => W155 | D58 => W153 | D59 => W151 | D60 => W149 | D61 => W147 | D62 => W145 | D63 => W143 end
    | D14 => match b with D0 => W14 | D1 => W12 | D2 => W10 | D3 => W8 | D4 => W6 | D5 => W4 | D6 => W2 | D7 => W0 | D8 => W126 | D9 => W124 | D10 => W122 | D11 => W120 | D12 => W118 | D13 => W116 | D14 => W114 | D15 => W112 | D16 => W110 | D17 => W108 | D18 => W106 | D19 => W104 | D20 => W102 | D21 => W100 | D22 => W98 | D23 => W96 | D24 => W94 | D25 => W92 | D26 => W90 | D27 => W88 | D28 => W86 | D29 => W84 | D30 => W82 | D31 => W80 | D32 => W78 | D33 => W76 | D34 => W74 | D35 => W72 | D36 => W70 | D37 => W68 | D38 => W66 | D39 => W64 | D40 => W190 | D41 => W188 | D42 => W186 | D43 => W184 | D44 => W182 | D45 => W180 | D46 => W178 | D47 => W176 | D48 => W174 | D49 => W172 | D50 => W170 | D51 => W168 | D52 => W166 | D53 => W164 | D54 => W162 | D55 => W160 | D56 => W158 | D57 => W156 | D58 => W154 | D59 => W152 | D60 => W150 | D61 => W148 | D62 => W146 | D63 => W144 end
    | D15 => match b with D0 => W15 | D1 => W13 | D2 => W11 | D3 => W9 | D4 => W7 | D5 => W5 | D6 => W3 | D7 => W1 | D8 => W127 | D9 => W125 | D10 => W123 | D11 => W121 | D12 => W119 | D13 => W117 | D14 => W115 | D15 => W113 | D16 => W111 | D17 => W109 | D18 => W107 | D19 => W105 | D20 => W103 | D21 => W101 | D22 => W99 | D23 => W97 | D24 => W95 | D25 => W93 | D26 => W91 | D27 => W89 | D28 => W87 | D29 => W85 | D30 => W83 | D31 => W81 | D32 => W79 | D33 => W77 | D34 => W75 | D35 => W73 | D36 => W71 | D37 => W69 | D38 => W67 | D39 => W65 | D40 => W191 | D41 => W189 | D42 => W187 | D43 => W185 | D44 => W183 | D45 => W181 | D46 => W179 | D47 => W177 | D48 => W175 | D49 => W173 | D50 => W171 | D51 => W169 | D52 => W167 | D53 => W165 | D54 => W163 | D55 => W161 | D56 => W159 | D57 => W157 | D58 => W155 | D59 => W153 | D60 => W151 | D61 => W149 | D62 => W147 | D63 => W145 end
    | D16 => match b with D0 => W16 | D1 => W14 | D2 => W12 | D3 => W10 | D4 => W8 | D5 => W6 | D6 => W4 | D7 => W2 | D8 => W0 | D9 => W126 | D10 => W124 | D11 => W122 | D12 => W120 | D13 => W118 | D14 => W116 | D15 => W114 | D16 => W112 | D17 => W110 | D18 => W108 | D19 => W106 | D20 => W104 | D21 => W102 | D22 => W100 | D23 => W98 | D24 => W96 | D25 => W94 | D26 => W92 | D27 => W90 | D28 => W88 | D29 => W86 | D30 => W84 | D31 => W82 | D32 => W80 | D33 => W78 | D34 => W76 | D35 => W74 | D36 => W72 | D37 => W70 | D38 => W68 | D39 => W66 | D40 => W64 | D41 => W190 | D42 => W188 | D43 => W186 | D44 => W184 | D45 => W182 | D46 => W180 | D47 => W178 | D48 => W176 | D49 => W174 | D50 => W172 | D51 => W170 | D52 => W168 | D53 => W166 | D54 => W164 | D55 => W162 | D56 => W160 | D57 => W158 | D58 => W156 | D59 => W154 | D60 => W152 | D61 => W150 | D62 => W148 | D63 => W146 end
    | D17 => match b with D0 => W17 | D1 => W15 | D2 => W13 | D3 => W11 | D4 => W9 | D5 => W7 | D6 => W5 | D7 => W3 | D8 => W1 | D9 => W127 | D10 => W125 | D11 => W123 | D12 => W121 | D13 => W119 | D14 => W117 | D15 => W115 | D16 => W113 | D17 => W111 | D18 => W109 | D19 => W107 | D20 => W105 | D21 => W103 | D22 => W101 | D23 => W99 | D24 => W97 | D25 => W95 | D26 => W93 | D27 => W91 | D28 => W89 | D29 => W87 | D30 => W85 | D31 => W83 | D32 => W81 | D33 => W79 | D34 => W77 | D35 => W75 | D36 => W73 | D37 => W71 | D38 => W69 | D39 => W67 | D40 => W65 | D41 => W191 | D42 => W189 | D43 => W187 | D44 => W185 | D45 => W183 | D46 => W181 | D47 => W179 | D48 => W177 | D49 => W175 | D50 => W173 | D51 => W171 | D52 => W169 | D53 => W167 | D54 => W165 | D55 => W163 | D56 => W161 | D57 => W159 | D58 => W157 | D59 => W155 | D60 => W153 | D61 => W151 | D62 => W149 | D63 => W147 end
    | D18 => match b with D0 => W18 | D1 => W16 | D2 => W14 | D3 => W12 | D4 => W10 | D5 => W8 | D6 => W6 | D7 => W4 | D8 => W2 | D9 => W0 | D10 => W126 | D11 => W124 | D12 => W122 | D13 => W120 | D14 => W118 | D15 => W116 | D16 => W114 | D17 => W112 | D18 => W110 | D19 => W108 | D20 => W106 | D21 => W104 | D22 => W102 | D23 => W100 | D24 => W98 | D25 => W96 | D26 => W94 | D27 => W92 | D28 => W90 | D29 => W88 | D30 => W86 | D31 => W84 | D32 => W82 | D33 => W80 | D34 => W78 | D35 => W76 | D36 => W74 | D37 => W72 | D38 => W70 | D39 => W68 | D40 => W66 | D41 => W64 | D42 => W190 | D43 => W188 | D44 => W186 | D45 => W184 | D46 => W182 | D47 => W180 | D48 => W178 | D49 => W176 | D50 => W174 | D51 => W172 | D52 => W170 | D53 => W168 | D54 => W166 | D55 => W164 | D56 => W162 | D57 => W160 | D58 => W158 | D59 => W156 | D60 => W154 | D61 => W152 | D62 => W150 | D63 => W148 end
    | D19 => match b with D0 => W19 | D1 => W17 | D2 => W15 | D3 => W13 | D4 => W11 | D5 => W9 | D6 => W7 | D7 => W5 | D8 => W3 | D9 => W1 | D10 => W127 | D11 => W125 | D12 => W123 | D13 => W121 | D14 => W119 | D15 => W117 | D16 => W115 | D17 => W113 | D18 => W111 | D19 => W109 | D20 => W107 | D21 => W105 | D22 => W103 | D23 => W101 | D24 => W99 | D25 => W97 | D26 => W95 | D27 => W93 | D28 => W91 | D29 => W89 | D30 => W87 | D31 => W85 | D32 => W83 | D33 => W81 | D34 => W79 | D35 => W77 | D36 => W75 | D37 => W73 | D38 => W71 | D39 => W69 | D40 => W67 | D41 => W65 | D42 => W191 | D43 => W189 | D44 => W187 | D45 => W185 | D46 => W183 | D47 => W181 | D48 => W179 | D49 => W177 | D50 => W175 | D51 => W173 | D52 => W171 | D53 => W169 | D54 => W167 | D55 => W165 | D56 => W163 | D57 => W161 | D58 => W159 | D59 => W157 | D60 => W155 | D61 => W153 | D62 => W151 | D63 => W149 end
    | D20 => match b with D0 => W20 | D1 => W18 | D2 => W16 | D3 => W14 | D4 => W12 | D5 => W10 | D6 => W8 | D7 => W6 | D8 => W4 | D9 => W2 | D10 => W0 | D11 => W126 | D12 => W124 | D13 => W122 | D14 => W120 | D15 => W118 | D16 => W116 | D17 => W114 | D18 => W112 | D19 => W110 | D20 => W108 | D21 => W106 | D22 => W104 | D23 => W102 | D24 => W100 | D25 => W98 | D26 => W96 | D27 => W94 | D28 => W92 | D29 => W90 | D30 => W88 | D31 => W86 | D32 => W84 | D33 => W82 | D34 => W80 | D35 => W78 | D36 => W76 | D37 => W74 | D38 => W72 | D39 => W70 | D40 => W68 | D41 => W66 | D42 => W64 | D43 => W190 | D44 => W188 | D45 => W186 | D46 => W184 | D47 => W182 | D48 => W180 | D49 => W178 | D50 => W176 | D51 => W174 | D52 => W172 | D53 => W170 | D54 => W168 | D55 => W166 | D56 => W164 | D57 => W162 | D58 => W160 | D59 => W158 | D60 => W156 | D61 => W154 | D62 => W152 | D63 => W150 end
    | D21 => match b with D0 => W21 | D1 => W19 | D2 => W17 | D3 => W15 | D4 => W13 | D5 => W11 | D6 => W9 | D7 => W7 | D8 => W5 | D9 => W3 | D10 => W1 | D11 => W127 | D12 => W125 | D13 => W123 | D14 => W121 | D15 => W119 | D16 => W117 | D17 => W115 | D18 => W113 | D19 => W111 | D20 => W109 | D21 => W107 | D22 => W105 | D23 => W103 | D24 => W101 | D25 => W99 | D26 => W97 | D27 => W95 | D28 => W93 | D29 => W91 | D30 => W89 | D31 => W87 | D32 => W85 | D33 => W83 | D34 => W81 | D35 => W79 | D36 => W77 | D37 => W75 | D38 => W73 | D39 => W71 | D40 => W69 | D41 => W67 | D42 => W65 | D43 => W191 | D44 => W189 | D45 => W187 | D46 => W185 | D47 => W183 | D48 => W181 | D49 => W179 | D50 => W177 | D51 => W175 | D52 => W173 | D53 => W171 | D54 => W169 | D55 => W167 | D56 => W165 | D57 => W163 | D58 => W161 | D59 => W159 | D60 => W157 | D61 => W155 | D62 => W153 | D63 => W151 end
    | D22 => match b with D0 => W22 | D1 => W20 | D2 => W18 | D3 => W16 | D4 => W14 | D5 => W12 | D6 => W10 | D7 => W8 | D8 => W6 | D9 => W4 | D10 => W2 | D11 => W0 | D12 => W126 | D13 => W124 | D14 => W122 | D15 => W120 | D16 => W118 | D17 => W116 | D18 => W114 | D19 => W112 | D20 => W110 | D21 => W108 | D22 => W106 | D23 => W104 | D24 => W102 | D25 => W100 | D26 => W98 | D27 => W96 | D28 => W94 | D29 => W92 | D30 => W90 | D31 => W88 | D32 => W86 | D33 => W84 | D34 => W82 | D35 => W80 | D36 => W78 | D37 => W76 | D38 => W74 | D39 => W72 | D40 => W70 | D41 => W68 | D42 => W66 | D43 => W64 | D44 => W190 | D45 => W188 | D46 => W186 | D47 => W184 | D48 => W182 | D49 => W180 | D50 => W178 | D51 => W176 | D52 => W174 | D53 => W172 | D54 => W170 | D55 => W168 | D56 => W166 | D57 => W164 | D58 => W162 | D59 => W160 | D60 => W158 | D61 => W156 | D62 => W154 | D63 => W152 end
    | D23 => match b with D0 => W23 | D1 => W21 | D2 => W19 | D3 => W17 | D4 => W15 | D5 => W13 | D6 => W11 | D7 => W9 | D8 => W7 | D9 => W5 | D10 => W3 | D11 => W1 | D12 => W127 | D13 => W125 | D14 => W123 | D15 => W121 | D16 => W119 | D17 => W117 | D18 => W115 | D19 => W113 | D20 => W111 | D21 => W109 | D22 => W107 | D23 => W105 | D24 => W103 | D25 => W101 | D26 => W99 | D27 => W97 | D28 => W95 | D29 => W93 | D30 => W91 | D31 => W89 | D32 => W87 | D33 => W85 | D34 => W83 | D35 => W81 | D36 => W79 | D37 => W77 | D38 => W75 | D39 => W73 | D40 => W71 | D41 => W69 | D42 => W67 | D43 => W65 | D44 => W191 | D45 => W189 | D46 => W187 | D47 => W185 | D48 => W183 | D49 => W181 | D50 => W179 | D51 => W177 | D52 => W175 | D53 => W173 | D54 => W171 | D55 => W169 | D56 => W167 | D57 => W165 | D58 => W163 | D59 => W161 | D60 => W159 | D61 => W157 | D62 => W155 | D63 => W153 end
    | D24 => match b with D0 => W24 | D1 => W22 | D2 => W20 | D3 => W18 | D4 => W16 | D5 => W14 | D6 => W12 | D7 => W10 | D8 => W8 | D9 => W6 | D10 => W4 | D11 => W2 | D12 => W0 | D13 => W126 | D14 => W124 | D15 => W122 | D16 => W120 | D17 => W118 | D18 => W116 | D19 => W114 | D20 => W112 | D21 => W110 | D22 => W108 | D23 => W106 | D24 => W104 | D25 => W102 | D26 => W100 | D27 => W98 | D28 => W96 | D29 => W94 | D30 => W92 | D31 => W90 | D32 => W88 | D33 => W86 | D34 => W84 | D35 => W82 | D36 => W80 | D37 => W78 | D38 => W76 | D39 => W74 | D40 => W72 | D41 => W70 | D42 => W68 | D43 => W66 | D44 => W64 | D45 => W190 | D46 => W188 | D47 => W186 | D48 => W184 | D49 => W182 | D50 => W180 | D51 => W178 | D52 => W176 | D53 => W174 | D54 => W172 | D55 => W170 | D56 => W168 | D57 => W166 | D58 => W164 | D59 => W162 | D60 => W160 | D61 => W158 | D62 => W156 | D63 => W154 end
    | D25 => match b with D0 => W25 | D1 => W23 | D2 => W21 | D3 => W19 | D4 => W17 | D5 => W15 | D6 => W13 | D7 => W11 | D8 => W9 | D9 => W7 | D10 => W5 | D11 => W3 | D12 => W1 | D13 => W127 | D14 => W125 | D15 => W123 | D16 => W121 | D17 => W119 | D18 => W117 | D19 => W115 | D20 => W113 | D21 => W111 | D22 => W109 | D23 => W107 | D24 => W105 | D25 => W103 | D26 => W101 | D27 => W99 | D28 => W97 | D29 => W95 | D30 => W93 | D31 => W91 | D32 => W89 | D33 => W87 | D34 => W85 | D35 => W83 | D36 => W81 | D37 => W79 | D38 => W77 | D39 => W75 | D40 => W73 | D41 => W71 | D42 => W69 | D43 => W67 | D44 => W65 | D45 => W191 | D46 => W189 | D47 => W187 | D48 => W185 | D49 => W183 | D50 => W181 | D51 => W179 | D52 => W177 | D53 => W175 | D54 => W173 | D55 => W171 | D56 => W169 | D57 => W167 | D58 => W165 | D59 => W163 | D60 => W161 | D61 => W159 | D62 => W157 | D63 => W155 end
    | D26 => match b with D0 => W26 | D1 => W24 | D2 => W22 | D3 => W20 | D4 => W18 | D5 => W16 | D6 => W14 | D7 => W12 | D8 => W10 | D9 => W8 | D10 => W6 | D11 => W4 | D12 => W2 | D13 => W0 | D14 => W126 | D15 => W124 | D16 => W122 | D17 => W120 | D18 => W118 | D19 => W116 | D20 => W114 | D21 => W112 | D22 => W110 | D23 => W108 | D24 => W106 | D25 => W104 | D26 => W102 | D27 => W100 | D28 => W98 | D29 => W96 | D30 => W94 | D31 => W92 | D32 => W90 | D33 => W88 | D34 => W86 | D35 => W84 | D36 => W82 | D37 => W80 | D38 => W78 | D39 => W76 | D40 => W74 | D41 => W72 | D42 => W70 | D43 => W68 | D44 => W66 | D45 => W64 | D46 => W190 | D47 => W188 | D48 => W186 | D49 => W184 | D50 => W182 | D51 => W180 | D52 => W178 | D53 => W176 | D54 => W174 | D55 => W172 | D56 => W170 | D57 => W168 | D58 => W166 | D59 => W164 | D60 => W162 | D61 => W160 | D62 => W158 | D63 => W156 end
    | D27 => match b with D0 => W27 | D1 => W25 | D2 => W23 | D3 => W21 | D4 => W19 | D5 => W17 | D6 => W15 | D7 => W13 | D8 => W11 | D9 => W9 | D10 => W7 | D11 => W5 | D12 => W3 | D13 => W1 | D14 => W127 | D15 => W125 | D16 => W123 | D17 => W121 | D18 => W119 | D19 => W117 | D20 => W115 | D21 => W113 | D22 => W111 | D23 => W109 | D24 => W107 | D25 => W105 | D26 => W103 | D27 => W101 | D28 => W99 | D29 => W97 | D30 => W95 | D31 => W93 | D32 => W91 | D33 => W89 | D34 => W87 | D35 => W85 | D36 => W83 | D37 => W81 | D38 => W79 | D39 => W77 | D40 => W75 | D41 => W73 | D42 => W71 | D43 => W69 | D44 => W67 | D45 => W65 | D46 => W191 | D47 => W189 | D48 => W187 | D49 => W185 | D50 => W183 | D51 => W181 | D52 => W179 | D53 => W177 | D54 => W175 | D55 => W173 | D56 => W171 | D57 => W169 | D58 => W167 | D59 => W165 | D60 => W163 | D61 => W161 | D62 => W159 | D63 => W157 end
    | D28 => match b with D0 => W28 | D1 => W26 | D2 => W24 | D3 => W22 | D4 => W20 | D5 => W18 | D6 => W16 | D7 => W14 | D8 => W12 | D9 => W10 | D10 => W8 | D11 => W6 | D12 => W4 | D13 => W2 | D14 => W0 | D15 => W126 | D16 => W124 | D17 => W122 | D18 => W120 | D19 => W118 | D20 => W116 | D21 => W114 | D22 => W112 | D23 => W110 | D24 => W108 | D25 => W106 | D26 => W104 | D27 => W102 | D28 => W100 | D29 => W98 | D30 => W96 | D31 => W94 | D32 => W92 | D33 => W90 | D34 => W88 | D35 => W86 | D36 => W84 | D37 => W82 | D38 => W80 | D39 => W78 | D40 => W76 | D41 => W74 | D42 => W72 | D43 => W70 | D44 => W68 | D45 => W66 | D46 => W64 | D47 => W190 | D48 => W188 | D49 => W186 | D50 => W184 | D51 => W182 | D52 => W180 | D53 => W178 | D54 => W176 | D55 => W174 | D56 => W172 | D57 => W170 | D58 => W168 | D59 => W166 | D60 => W164 | D61 => W162 | D62 => W160 | D63 => W158 end
    | D29 => match b with D0 => W29 | D1 => W27 | D2 => W25 | D3 => W23 | D4 => W21 | D5 => W19 | D6 => W17 | D7 => W15 | D8 => W13 | D9 => W11 | D10 => W9 | D11 => W7 | D12 => W5 | D13 => W3 | D14 => W1 | D15 => W127 | D16 => W125 | D17 => W123 | D18 => W121 | D19 => W119 | D20 => W117 | D21 => W115 | D22 => W113 | D23 => W111 | D24 => W109 | D25 => W107 | D26 => W105 | D27 => W103 | D28 => W101 | D29 => W99 | D30 => W97 | D31 => W95 | D32 => W93 | D33 => W91 | D34 => W89 | D35 => W87 | D36 => W85 | D37 => W83 | D38 => W81 | D39 => W79 | D40 => W77 | D41 => W75 | D42 => W73 | D43 => W71 | D44 => W69 | D45 => W67 | D46 => W65 | D47 => W191 | D48 => W189 | D49 => W187 | D50 => W185 | D51 => W183 | D52 => W181 | D53 => W179 | D54 => W177 | D55 => W175 | D56 => W173 | D57 => W171 | D58 => W169 | D59 => W167 | D60 => W165 | D61 => W163 | D62 => W161 | D63 => W159 end
    | D30 => match b with D0 => W30 | D1 => W28 | D2 => W26 | D3 => W24 | D4 => W22 | D5 => W20 | D6 => W18 | D7 => W16 | D8 => W14 | D9 => W12 | D10 => W10 | D11 => W8 | D12 => W6 | D13 => W4 | D14 => W2 | D15 => W0 | D16 => W126 | D17 => W124 | D18 => W122 | D19 => W120 | D20 => W118 | D21 => W116 | D22 => W114 | D23 => W112 | D24 => W110 | D25 => W108 | D26 => W106 | D27 => W104 | D28 => W102 | D29 => W100 | D30 => W98 | D31 => W96 | D32 => W94 | D33 => W92 | D34 => W90 | D35 => W88 | D36 => W86 | D37 => W84 | D38 => W82 | D39 => W80 | D40 => W78 | D41 => W76 | D42 => W74 | D43 => W72 | D44 => W70 | D45 => W68 | D46 => W66 | D47 => W64 | D48 => W190 | D49 => W188 | D50 => W186 | D51 => W184 | D52 => W182 | D53 => W180 | D54 => W178 | D55 => W176 | D56 => W174 | D57 => W172 | D58 => W170 | D59 => W168 | D60 => W166 | D61 => W164 | D62 => W162 | D63 => W160 end
    | D31 => match b with D0 => W31 | D1 => W29 | D2 => W27 | D3 => W25 | D4 => W23 | D5 => W21 | D6 => W19 | D7 => W17 | D8 => W15 | D9 => W13 | D10 => W11 | D11 => W9 | D12 => W7 | D13 => W5 | D14 => W3 | D15 => W1 | D16 => W127 | D17 => W125 | D18 => W123 | D19 => W121 | D20 => W119 | D21 => W117 | D22 => W115 | D23 => W113 | D24 => W111 | D25 => W109 | D26 => W107 | D27 => W105 | D28 => W103 | D29 => W101 | D30 => W99 | D31 => W97 | D32 => W95 | D33 => W93 | D34 => W91 | D35 => W89 | D36 => W87 | D37 => W85 | D38 => W83 | D39 => W81 | D40 => W79 | D41 => W77 | D42 => W75 | D43 => W73 | D44 => W71 | D45 => W69 | D46 => W67 | D47 => W65 | D48 => W191 | D49 => W189 | D50 => W187 | D51 => W185 | D52 => W183 | D53 => W181 | D54 => W179 | D55 => W177 | D56 => W175 | D57 => W173 | D58 => W171 | D59 => W169 | D60 => W167 | D61 => W165 | D62 => W163 | D63 => W161 end
    | D32 => match b with D0 => W32 | D1 => W30 | D2 => W28 | D3 => W26 | D4 => W24 | D5 => W22 | D6 => W20 | D7 => W18 | D8 => W16 | D9 => W14 | D10 => W12 | D11 => W10 | D12 => W8 | D13 => W6 | D14 => W4 | D15 => W2 | D16 => W0 | D17 => W126 | D18 => W124 | D19 => W122 | D20 => W120 | D21 => W118 | D22 => W116 | D23 => W114 | D24 => W112 | D25 => W110 | D26 => W108 | D27 => W106 | D28 => W104 | D29 => W102 | D30 => W100 | D31 => W98 | D32 => W96 | D33 => W94 | D34 => W92 | D35 => W90 | D36 => W88 | D37 => W86 | D38 => W84 | D39 => W82 | D40 => W80 | D41 => W78 | D42 => W76 | D43 => W74 | D44 => W72 | D45 => W70 | D46 => W68 | D47 => W66 | D48 => W64 | D49 => W190 | D50 => W188 | D51 => W186 | D52 => W184 | D53 => W182 | D54 => W180 | D55 => W178 | D56 => W176 | D57 => W174 | D58 => W172 | D59 => W170 | D60 => W168 | D61 => W166 | D62 => W164 | D63 => W162 end
    | D33 => match b with D0 => W33 | D1 => W31 | D2 => W29 | D3 => W27 | D4 => W25 | D5 => W23 | D6 => W21 | D7 => W19 | D8 => W17 | D9 => W15 | D10 => W13 | D11 => W11 | D12 => W9 | D13 => W7 | D14 => W5 | D15 => W3 | D16 => W1 | D17 => W127 | D18 => W125 | D19 => W123 | D20 => W121 | D21 => W119 | D22 => W117 | D23 => W115 | D24 => W113 | D25 => W111 | D26 => W109 | D27 => W107 | D28 => W105 | D29 => W103 | D30 => W101 | D31 => W99 | D32 => W97 | D33 => W95 | D34 => W93 | D35 => W91 | D36 => W89 | D37 => W87 | D38 => W85 | D39 => W83 | D40 => W81 | D41 => W79 | D42 => W77 | D43 => W75 | D44 => W73 | D45 => W71 | D46 => W69 | D47 => W67 | D48 => W65 | D49 => W191 | D50 => W189 | D51 => W187 | D52 => W185 | D53 => W183 | D54 => W181 | D55 => W179 | D56 => W177 | D57 => W175 | D58 => W173 | D59 => W171 | D60 => W169 | D61 => W167 | D62 => W165 | D63 => W163 end
    | D34 => match b with D0 => W34 | D1 => W32 | D2 => W30 | D3 => W28 | D4 => W26 | D5 => W24 | D6 => W22 | D7 => W20 | D8 => W18 | D9 => W16 | D10 => W14 | D11 => W12 | D12 => W10 | D13 => W8 | D14 => W6 | D15 => W4 | D16 => W2 | D17 => W0 | D18 => W126 | D19 => W124 | D20 => W122 | D21 => W120 | D22 => W118 | D23 => W116 | D24 => W114 | D25 => W112 | D26 => W110 | D27 => W108 | D28 => W106 | D29 => W104 | D30 => W102 | D31 => W100 | D32 => W98 | D33 => W96 | D34 => W94 | D35 => W92 | D36 => W90 | D37 => W88 | D38 => W86 | D39 => W84 | D40 => W82 | D41 => W80 | D42 => W78 | D43 => W76 | D44 => W74 | D45 => W72 | D46 => W70 | D47 => W68 | D48 => W66 | D49 => W64 | D50 => W190 | D51 => W188 | D52 => W186 | D53 => W184 | D54 => W182 | D55 => W180 | D56 => W178 | D57 => W176 | D58 => W174 | D59 => W172 | D60 => W170 | D61 => W168 | D62 => W166 | D63 => W164 end
    | D35 => match b with D0 => W35 | D1 => W33 | D2 => W31 | D3 => W29 | D4 => W27 | D5 => W25 | D6 => W23 | D7 => W21 | D8 => W19 | D9 => W17 | D10 => W15 | D11 => W13 | D12 => W11 | D13 => W9 | D14 => W7 | D15 => W5 | D16 => W3 | D17 => W1 | D18 => W127 | D19 => W125 | D20 => W123 | D21 => W121 | D22 => W119 | D23 => W117 | D24 => W115 | D25 => W113 | D26 => W111 | D27 => W109 | D28 => W107 | D29 => W105 | D30 => W103 | D31 => W101 | D32 => W99 | D33 => W97 | D34 => W95 | D35 => W93 | D36 => W91 | D37 => W89 | D38 => W87 | D39 => W85 | D40 => W83 | D41 => W81 | D42 => W79 | D43 => W77 | D44 => W75 | D45 => W73 | D46 => W71 | D47 => W69 | D48 => W67 | D49 => W65 | D50 => W191 | D51 => W189 | D52 => W187 | D53 => W185 | D54 => W183 | D55 => W181 | D56 => W179 | D57 => W177 | D58 => W175 | D59 => W173 | D60 => W171 | D61 => W169 | D62 => W167 | D63 => W165 end
    | D36 => match b with D0 => W36 | D1 => W34 | D2 => W32 | D3 => W30 | D4 => W28 | D5 => W26 | D6 => W24 | D7 => W22 | D8 => W20 | D9 => W18 | D10 => W16 | D11 => W14 | D12 => W12 | D13 => W10 | D14 => W8 | D15 => W6 | D16 => W4 | D17 => W2 | D18 => W0 | D19 => W126 | D20 => W124 | D21 => W122 | D22 => W120 | D23 => W118 | D24 => W116 | D25 => W114 | D26 => W112 | D27 => W110 | D28 => W108 | D29 => W106 | D30 => W104 | D31 => W102 | D32 => W100 | D33 => W98 | D34 => W96 | D35 => W94 | D36 => W92 | D37 => W90 | D38 => W88 | D39 => W86 | D40 => W84 | D41 => W82 | D42 => W80 | D43 => W78 | D44 => W76 | D45 => W74 | D46 => W72 | D47 => W70 | D48 => W68 | D49 => W66 | D50 => W64 | D51 => W190 | D52 => W188 | D53 => W186 | D54 => W184 | D55 => W182 | D56 => W180 | D57 => W178 | D58 => W176 | D59 => W174 | D60 => W172 | D61 => W170 | D62 => W168 | D63 => W166 end
    | D37 => match b with D0 => W37 | D1 => W35 | D2 => W33 | D3 => W31 | D4 => W29 | D5 => W27 | D6 => W25 | D7 => W23 | D8 => W21 | D9 => W19 | D10 => W17 | D11 => W15 | D12 => W13 | D13 => W11 | D14 => W9 | D15 => W7 | D16 => W5 | D17 => W3 | D18 => W1 | D19 => W127 | D20 => W125 | D21 => W123 | D22 => W121 | D23 => W119 | D24 => W117 | D25 => W115 | D26 => W113 | D27 => W111 | D28 => W109 | D29 => W107 | D30 => W105 | D31 => W103 | D32 => W101 | D33 => W99 | D34 => W97 | D35 => W95 | D36 => W93 | D37 => W91 | D38 => W89 | D39 => W87 | D40 => W85 | D41 => W83 | D42 => W81 | D43 => W79 | D44 => W77 | D45 => W75 | D46 => W73 | D47 => W71 | D48 => W69 | D49 => W67 | D50 => W65 | D51 => W191 | D52 => W189 | D53 => W187 | D54 => W185 | D55 => W183 | D56 => W181 | D57 => W179 | D58 => W177 | D59 => W175 | D60 => W173 | D61 => W171 | D62 => W169 | D63 => W167 end
    | D38 => match b with D0 => W38 | D1 => W36 | D2 => W34 | D3 => W32 | D4 => W30 | D5 => W28 | D6 => W26 | D7 => W24 | D8 => W22 | D9 => W20 | D10 => W18 | D11 => W16 | D12 => W14 | D13 => W12 | D14 => W10 | D15 => W8 | D16 => W6 | D17 => W4 | D18 => W2 | D19 => W0 | D20 => W126 | D21 => W124 | D22 => W122 | D23 => W120 | D24 => W118 | D25 => W116 | D26 => W114 | D27 => W112 | D28 => W110 | D29 => W108 | D30 => W106 | D31 => W104 | D32 => W102 | D33 => W100 | D34 => W98 | D35 => W96 | D36 => W94 | D37 => W92 | D38 => W90 | D39 => W88 | D40 => W86 | D41 => W84 | D42 => W82 | D43 => W80 | D44 => W78 | D45 => W76 | D46 => W74 | D47 => W72 | D48 => W70 | D49 => W68 | D50 => W66 | D51 => W64 | D52 => W190 | D53 => W188 | D54 => W186 | D55 => W184 | D56 => W182 | D57 => W180 | D58 => W178 | D59 => W176 | D60 => W174 | D61 => W172 | D62 => W170 | D63 => W168 end
    | D39 => match b with D0 => W39 | D1 => W37 | D2 => W35 | D3 => W33 | D4 => W31 | D5 => W29 | D6 => W27 | D7 => W25 | D8 => W23 | D9 => W21 | D10 => W19 | D11 => W17 | D12 => W15 | D13 => W13 | D14 => W11 | D15 => W9 | D16 => W7 | D17 => W5 | D18 => W3 | D19 => W1 | D20 => W127 | D21 => W125 | D22 => W123 | D23 => W121 | D24 => W119 | D25 => W117 | D26 => W115 | D27 => W113 | D28 => W111 | D29 => W109 | D30 => W107 | D31 => W105 | D32 => W103 | D33 => W101 | D34 => W99 | D35 => W97 | D36 => W95 | D37 => W93 | D38 => W91 | D39 => W89 | D40 => W87 | D41 => W85 | D42 => W83 | D43 => W81 | D44 => W79 | D45 => W77 | D46 => W75 | D47 => W73 | D48 => W71 | D49 => W69 | D50 => W67 | D51 => W65 | D52 => W191 | D53 => W189 | D54 => W187 | D55 => W185 | D56 => W183 | D57 => W181 | D58 => W179 | D59 => W177 | D60 => W175 | D61 => W173 | D62 => W171 | D63 => W169 end
    | D40 => match b with D0 => W40 | D1 => W38 | D2 => W36 | D3 => W34 | D4 => W32 | D5 => W30 | D6 => W28 | D7 => W26 | D8 => W24 | D9 => W22 | D10 => W20 | D11 => W18 | D12 => W16 | D13 => W14 | D14 => W12 | D15 => W10 | D16 => W8 | D17 => W6 | D18 => W4 | D19 => W2 | D20 => W0 | D21 => W126 | D22 => W124 | D23 => W122 | D24 => W120 | D25 => W118 | D26 => W116 | D27 => W114 | D28 => W112 | D29 => W110 | D30 => W108 | D31 => W106 | D32 => W104 | D33 => W102 | D34 => W100 | D35 => W98 | D36 => W96 | D37 => W94 | D38 => W92 | D39 => W90 | D40 => W88 | D41 => W86 | D42 => W84 | D43 => W82 | D44 => W80 | D45 => W78 | D46 => W76 | D47 => W74 | D48 => W72 | D49 => W70 | D50 => W68 | D51 => W66 | D52 => W64 | D53 => W190 | D54 => W188 | D55 => W186 | D56 => W184 | D57 => W182 | D58 => W180 | D59 => W178 | D60 => W176 | D61 => W174 | D62 => W172 | D63 => W170 end
    | D41 => match b with D0 => W41 | D1 => W39 | D2 => W37 | D3 => W35 | D4 => W33 | D5 => W31 | D6 => W29 | D7 => W27 | D8 => W25 | D9 => W23 | D10 => W21 | D11 => W19 | D12 => W17 | D13 => W15 | D14 => W13 | D15 => W11 | D16 => W9 | D17 => W7 | D18 => W5 | D19 => W3 | D20 => W1 | D21 => W127 | D22 => W125 | D23 => W123 | D24 => W121 | D25 => W119 | D26 => W117 | D27 => W115 | D28 => W113 | D29 => W111 | D30 => W109 | D31 => W107 | D32 => W105 | D33 => W103 | D34 => W101 | D35 => W99 | D36 => W97 | D37 => W95 | D38 => W93 | D39 => W91 | D40 => W89 | D41 => W87 | D42 => W85 | D43 => W83 | D44 => W81 | D45 => W79 | D46 => W77 | D47 => W75 | D48 => W73 | D49 => W71 | D50 => W69 | D51 => W67 | D52 => W65 | D53 => W191 | D54 => W189 | D55 => W187 | D56 => W185 | D57 => W183 | D58 => W181 | D59 => W179 | D60 => W177 | D61 => W175 | D62 => W173 | D63 => W171 end
    | D42 => match b with D0 => W42 | D1 => W40 | D2 => W38 | D3 => W36 | D4 => W34 | D5 => W32 | D6 => W30 | D7 => W28 | D8 => W26 | D9 => W24 | D10 => W22 | D11 => W20 | D12 => W18 | D13 => W16 | D14 => W14 | D15 => W12 | D16 => W10 | D17 => W8 | D18 => W6 | D19 => W4 | D20 => W2 | D21 => W0 | D22 => W126 | D23 => W124 | D24 => W122 | D25 => W120 | D26 => W118 | D27 => W116 | D28 => W114 | D29 => W112 | D30 => W110 | D31 => W108 | D32 => W106 | D33 => W104 | D34 => W102 | D35 => W100 | D36 => W98 | D37 => W96 | D38 => W94 | D39 => W92 | D40 => W90 | D41 => W88 | D42 => W86 | D43 => W84 | D44 => W82 | D45 => W80 | D46 => W78 | D47 => W76 | D48 => W74 | D49 => W72 | D50 => W70 | D51 => W68 | D52 => W66 | D53 => W64 | D54 => W190 | D55 => W188 | D56 => W186 | D57 => W184 | D58 => W182 | D59 => W180 | D60 => W178 | D61 => W176 | D62 => W174 | D63 => W172 end
    | D43 => match b with D0 => W43 | D1 => W41 | D2 => W39 | D3 => W37 | D4 => W35 | D5 => W33 | D6 => W31 | D7 => W29 | D8 => W27 | D9 => W25 | D10 => W23 | D11 => W21 | D12 => W19 | D13 => W17 | D14 => W15 | D15 => W13 | D16 => W11 | D17 => W9 | D18 => W7 | D19 => W5 | D20 => W3 | D21 => W1 | D22 => W127 | D23 => W125 | D24 => W123 | D25 => W121 | D26 => W119 | D27 => W117 | D28 => W115 | D29 => W113 | D30 => W111 | D31 => W109 | D32 => W107 | D33 => W105 | D34 => W103 | D35 => W101 | D36 => W99 | D37 => W97 | D38 => W95 | D39 => W93 | D40 => W91 | D41 => W89 | D42 => W87 | D43 => W85 | D44 => W83 | D45 => W81 | D46 => W79 | D47 => W77 | D48 => W75 | D49 => W73 | D50 => W71 | D51 => W69 | D52 => W67 | D53 => W65 | D54 => W191 | D55 => W189 | D56 => W187 | D57 => W185 | D58 => W183 | D59 => W181 | D60 => W179 | D61 => W177 | D62 => W175 | D63 => W173 end
    | D44 => match b with D0 => W44 | D1 => W42 | D2 => W40 | D3 => W38 | D4 => W36 | D5 => W34 | D6 => W32 | D7 => W30 | D8 => W28 | D9 => W26 | D10 => W24 | D11 => W22 | D12 => W20 | D13 => W18 | D14 => W16 | D15 => W14 | D16 => W12 | D17 => W10 | D18 => W8 | D19 => W6 | D20 => W4 | D21 => W2 | D22 => W0 | D23 => W126 | D24 => W124 | D25 => W122 | D26 => W120 | D27 => W118 | D28 => W116 | D29 => W114 | D30 => W112 | D31 => W110 | D32 => W108 | D33 => W106 | D34 => W104 | D35 => W102 | D36 => W100 | D37 => W98 | D38 => W96 | D39 => W94 | D40 => W92 | D41 => W90 | D42 => W88 | D43 => W86 | D44 => W84 | D45 => W82 | D46 => W80 | D47 => W78 | D48 => W76 | D49 => W74 | D50 => W72 | D51 => W70 | D52 => W68 | D53 => W66 | D54 => W64 | D55 => W190 | D56 => W188 | D57 => W186 | D58 => W184 | D59 => W182 | D60 => W180 | D61 => W178 | D62 => W176 | D63 => W174 end
    | D45 => match b with D0 => W45 | D1 => W43 | D2 => W41 | D3 => W39 | D4 => W37 | D5 => W35 | D6 => W33 | D7 => W31 | D8 => W29 | D9 => W27 | D10 => W25 | D11 => W23 | D12 => W21 | D13 => W19 | D14 => W17 | D15 => W15 | D16 => W13 | D17 => W11 | D18 => W9 | D19 => W7 | D20 => W5 | D21 => W3 | D22 => W1 | D23 => W127 | D24 => W125 | D25 => W123 | D26 => W121 | D27 => W119 | D28 => W117 | D29 => W115 | D30 => W113 | D31 => W111 | D32 => W109 | D33 => W107 | D34 => W105 | D35 => W103 | D36 => W101 | D37 => W99 | D38 => W97 | D39 => W95 | D40 => W93 | D41 => W91 | D42 => W89 | D43 => W87 | D44 => W85 | D45 => W83 | D46 => W81 | D47 => W79 | D48 => W77 | D49 => W75 | D50 => W73 | D51 => W71 | D52 => W69 | D53 => W67 | D54 => W65 | D55 => W191 | D56 => W189 | D57 => W187 | D58 => W185 | D59 => W183 | D60 => W181 | D61 => W179 | D62 => W177 | D63 => W175 end
    | D46 => match b with D0 => W46 | D1 => W44 | D2 => W42 | D3 => W40 | D4 => W38 | D5 => W36 | D6 => W34 | D7 => W32 | D8 => W30 | D9 => W28 | D10 => W26 | D11 => W24 | D12 => W22 | D13 => W20 | D14 => W18 | D15 => W16 | D16 => W14 | D17 => W12 | D18 => W10 | D19 => W8 | D20 => W6 | D21 => W4 | D22 => W2 | D23 => W0 | D24 => W126 | D25 => W124 | D26 => W122 | D27 => W120 | D28 => W118 | D29 => W116 | D30 => W114 | D31 => W112 | D32 => W110 | D33 => W108 | D34 => W106 | D35 => W104 | D36 => W102 | D37 => W100 | D38 => W98 | D39 => W96 | D40 => W94 | D41 => W92 | D42 => W90 | D43 => W88 | D44 => W86 | D45 => W84 | D46 => W82 | D47 => W80 | D48 => W78 | D49 => W76 | D50 => W74 | D51 => W72 | D52 => W70 | D53 => W68 | D54 => W66 | D55 => W64 | D56 => W190 | D57 => W188 | D58 => W186 | D59 => W184 | D60 => W182 | D61 => W180 | D62 => W178 | D63 => W176 end
    | D47 => match b with D0 => W47 | D1 => W45 | D2 => W43 | D3 => W41 | D4 => W39 | D5 => W37 | D6 => W35 | D7 => W33 | D8 => W31 | D9 => W29 | D10 => W27 | D11 => W25 | D12 => W23 | D13 => W21 | D14 => W19 | D15 => W17 | D16 => W15 | D17 => W13 | D18 => W11 | D19 => W9 | D20 => W7 | D21 => W5 | D22 => W3 | D23 => W1 | D24 => W127 | D25 => W125 | D26 => W123 | D27 => W121 | D28 => W119 | D29 => W117 | D30 => W115 | D31 => W113 | D32 => W111 | D33 => W109 | D34 => W107 | D35 => W105 | D36 => W103 | D37 => W101 | D38 => W99 | D39 => W97 | D40 => W95 | D41 => W93 | D42 => W91 | D43 => W89 | D44 => W87 | D45 => W85 | D46 => W83 | D47 => W81 | D48 => W79 | D49 => W77 | D50 => W75 | D51 => W73 | D52 => W71 | D53 => W69 | D54 => W67 | D55 => W65 | D56 => W191 | D57 => W189 | D58 => W187 | D59 => W185 | D60 => W183 | D61 => W181 | D62 => W179 | D63 => W177 end
    | D48 => match b with D0 => W48 | D1 => W46 | D2 => W44 | D3 => W42 | D4 => W40 | D5 => W38 | D6 => W36 | D7 => W34 | D8 => W32 | D9 => W30 | D10 => W28 | D11 => W26 | D12 => W24 | D13 => W22 | D14 => W20 | D15 => W18 | D16 => W16 | D17 => W14 | D18 => W12 | D19 => W10 | D20 => W8 | D21 => W6 | D22 => W4 | D23 => W2 | D24 => W0 | D25 => W126 | D26 => W124 | D27 => W122 | D28 => W120 | D29 => W118 | D30 => W116 | D31 => W114 | D32 => W112 | D33 => W110 | D34 => W108 | D35 => W106 | D36 => W104 | D37 => W102 | D38 => W100 | D39 => W98 | D40 => W96 | D41 => W94 | D42 => W92 | D43 => W90 | D44 => W88 | D45 => W86 | D46 => W84 | D47 => W82 | D48 => W80 | D49 => W78 | D50 => W76 | D51 => W74 | D52 => W72 | D53 => W70 | D54 => W68 | D55 => W66 | D56 => W64 | D57 => W190 | D58 => W188 | D59 => W186 | D60 => W184 | D61 => W182 | D62 => W180 | D63 => W178 end
    | D49 => match b with D0 => W49 | D1 => W47 | D2 => W45 | D3 => W43 | D4 => W41 | D5 => W39 | D6 => W37 | D7 => W35 | D8 => W33 | D9 => W31 | D10 => W29 | D11 => W27 | D12 => W25 | D13 => W23 | D14 => W21 | D15 => W19 | D16 => W17 | D17 => W15 | D18 => W13 | D19 => W11 | D20 => W9 | D21 => W7 | D22 => W5 | D23 => W3 | D24 => W1 | D25 => W127 | D26 => W125 | D27 => W123 | D28 => W121 | D29 => W119 | D30 => W117 | D31 => W115 | D32 => W113 | D33 => W111 | D34 => W109 | D35 => W107 | D36 => W105 | D37 => W103 | D38 => W101 | D39 => W99 | D40 => W97 | D41 => W95 | D42 => W93 | D43 => W91 | D44 => W89 | D45 => W87 | D46 => W85 | D47 => W83 | D48 => W81 | D49 => W79 | D50 => W77 | D51 => W75 | D52 => W73 | D53 => W71 | D54 => W69 | D55 => W67 | D56 => W65 | D57 => W191 | D58 => W189 | D59 => W187 | D60 => W185 | D61 => W183 | D62 => W181 | D63 => W179 end
    | D50 => match b with D0 => W50 | D1 => W48 | D2 => W46 | D3 => W44 | D4 => W42 | D5 => W40 | D6 => W38 | D7 => W36 | D8 => W34 | D9 => W32 | D10 => W30 | D11 => W28 | D12 => W26 | D13 => W24 | D14 => W22 | D15 => W20 | D16 => W18 | D17 => W16 | D18 => W14 | D19 => W12 | D20 => W10 | D21 => W8 | D22 => W6 | D23 => W4 | D24 => W2 | D25 => W0 | D26 => W126 | D27 => W124 | D28 => W122 | D29 => W120 | D30 => W118 | D31 => W116 | D32 => W114 | D33 => W112 | D34 => W110 | D35 => W108 | D36 => W106 | D37 => W104 | D38 => W102 | D39 => W100 | D40 => W98 | D41 => W96 | D42 => W94 | D43 => W92 | D44 => W90 | D45 => W88 | D46 => W86 | D47 => W84 | D48 => W82 | D49 => W80 | D50 => W78 | D51 => W76 | D52 => W74 | D53 => W72 | D54 => W70 | D55 => W68 | D56 => W66 | D57 => W64 | D58 => W190 | D59 => W188 | D60 => W186 | D61 => W184 | D62 => W182 | D63 => W180 end
    | D51 => match b with D0 => W51 | D1 => W49 | D2 => W47 | D3 => W45 | D4 => W43 | D5 => W41 | D6 => W39 | D7 => W37 | D8 => W35 | D9 => W33 | D10 => W31 | D11 => W29 | D12 => W27 | D13 => W25 | D14 => W23 | D15 => W21 | D16 => W19 | D17 => W17 | D18 => W15 | D19 => W13 | D20 => W11 | D21 => W9 | D22 => W7 | D23 => W5 | D24 => W3 | D25 => W1 | D26 => W127 | D27 => W125 | D28 => W123 | D29 => W121 | D30 => W119 | D31 => W117 | D32 => W115 | D33 => W113 | D34 => W111 | D35 => W109 | D36 => W107 | D37 => W105 | D38 => W103 | D39 => W101 | D40 => W99 | D41 => W97 | D42 => W95 | D43 => W93 | D44 => W91 | D45 => W89 | D46 => W87 | D47 => W85 | D48 => W83 | D49 => W81 | D50 => W79 | D51 => W77 | D52 => W75 | D53 => W73 | D54 => W71 | D55 => W69 | D56 => W67 | D57 => W65 | D58 => W191 | D59 => W189 | D60 => W187 | D61 => W185 | D62 => W183 | D63 => W181 end
    | D52 => match b with D0 => W52 | D1 => W50 | D2 => W48 | D3 => W46 | D4 => W44 | D5 => W42 | D6 => W40 | D7 => W38 | D8 => W36 | D9 => W34 | D10 => W32 | D11 => W30 | D12 => W28 | D13 => W26 | D14 => W24 | D15 => W22 | D16 => W20 | D17 => W18 | D18 => W16 | D19 => W14 | D20 => W12 | D21 => W10 | D22 => W8 | D23 => W6 | D24 => W4 | D25 => W2 | D26 => W0 | D27 => W126 | D28 => W124 | D29 => W122 | D30 => W120 | D31 => W118 | D32 => W116 | D33 => W114 | D34 => W112 | D35 => W110 | D36 => W108 | D37 => W106 | D38 => W104 | D39 => W102 | D40 => W100 | D41 => W98 | D42 => W96 | D43 => W94 | D44 => W92 | D45 => W90 | D46 => W88 | D47 => W86 | D48 => W84 | D49 => W82 | D50 => W80 | D51 => W78 | D52 => W76 | D53 => W74 | D54 => W72 | D55 => W70 | D56 => W68 | D57 => W66 | D58 => W64 | D59 => W190 | D60 => W188 | D61 => W186 | D62 => W184 | D63 => W182 end
    | D53 => match b with D0 => W53 | D1 => W51 | D2 => W49 | D3 => W47 | D4 => W45 | D5 => W43 | D6 => W41 | D7 => W39 | D8 => W37 | D9 => W35 | D10 => W33 | D11 => W31 | D12 => W29 | D13 => W27 | D14 => W25 | D15 => W23 | D16 => W21 | D17 => W19 | D18 => W17 | D19 => W15 | D20 => W13 | D21 => W11 | D22 => W9 | D23 => W7 | D24 => W5 | D25 => W3 | D26 => W1 | D27 => W127 | D28 => W125 | D29 => W123 | D30 => W121 | D31 => W119 | D32 => W117 | D33 => W115 | D34 => W113 | D35 => W111 | D36 => W109 | D37 => W107 | D38 => W105 | D39 => W103 | D40 => W101 | D41 => W99 | D42 => W97 | D43 => W95 | D44 => W93 | D45 => W91 | D46 => W89 | D47 => W87 | D48 => W85 | D49 => W83 | D50 => W81 | D51 => W79 | D52 => W77 | D53 => W75 | D54 => W73 | D55 => W71 | D56 => W69 | D57 => W67 | D58 => W65 | D59 => W191 | D60 => W189 | D61 => W187 | D62 => W185 | D63 => W183 end
    | D54 => match b with D0 => W54 | D1 => W52 | D2 => W50 | D3 => W48 | D4 => W46 | D5 => W44 | D6 => W42 | D7 => W40 | D8 => W38 | D9 => W36 | D10 => W34 | D11 => W32 | D12 => W30 | D13 => W28 | D14 => W26 | D15 => W24 | D16 => W22 | D17 => W20 | D18 => W18 | D19 => W16 | D20 => W14 | D21 => W12 | D22 => W10 | D23 => W8 | D24 => W6 | D25 => W4 | D26 => W2 | D27 => W0 | D28 => W126 | D29 => W124 | D30 => W122 | D31 => W120 | D32 => W118 | D33 => W116 | D34 => W114 | D35 => W112 | D36 => W110 | D37 => W108 | D38 => W106 | D39 => W104 | D40 => W102 | D41 => W100 | D42 => W98 | D43 => W96 | D44 => W94 | D45 => W92 | D46 => W90 | D47 => W88 | D48 => W86 | D49 => W84 | D50 => W82 | D51 => W80 | D52 => W78 | D53 => W76 | D54 => W74 | D55 => W72 | D56 => W70 | D57 => W68 | D58 => W66 | D59 => W64 | D60 => W190 | D61 => W188 | D62 => W186 | D63 => W184 end
    | D55 => match b with D0 => W55 | D1 => W53 | D2 => W51 | D3 => W49 | D4 => W47 | D5 => W45 | D6 => W43 | D7 => W41 | D8 => W39 | D9 => W37 | D10 => W35 | D11 => W33 | D12 => W31 | D13 => W29 | D14 => W27 | D15 => W25 | D16 => W23 | D17 => W21 | D18 => W19 | D19 => W17 | D20 => W15 | D21 => W13 | D22 => W11 | D23 => W9 | D24 => W7 | D25 => W5 | D26 => W3 | D27 => W1 | D28 => W127 | D29 => W125 | D30 => W123 | D31 => W121 | D32 => W119 | D33 => W117 | D34 => W115 | D35 => W113 | D36 => W111 | D37 => W109 | D38 => W107 | D39 => W105 | D40 => W103 | D41 => W101 | D42 => W99 | D43 => W97 | D44 => W95 | D45 => W93 | D46 => W91 | D47 => W89 | D48 => W87 | D49 => W85 | D50 => W83 | D51 => W81 | D52 => W79 | D53 => W77 | D54 => W75 | D55 => W73 | D56 => W71 | D57 => W69 | D58 => W67 | D59 => W65 | D60 => W191 | D61 => W189 | D62 => W187 | D63 => W185 end
    | D56 => match b with D0 => W56 | D1 => W54 | D2 => W52 | D3 => W50 | D4 => W48 | D5 => W46 | D6 => W44 | D7 => W42 | D8 => W40 | D9 => W38 | D10 => W36 | D11 => W34 | D12 => W32 | D13 => W30 | D14 => W28 | D15 => W26 | D16 => W24 | D17 => W22 | D18 => W20 | D19 => W18 | D20 => W16 | D21 => W14 | D22 => W12 | D23 => W10 | D24 => W8 | D25 => W6 | D26 => W4 | D27 => W2 | D28 => W0 | D29 => W126 | D30 => W124 | D31 => W122 | D32 => W120 | D33 => W118 | D34 => W116 | D35 => W114 | D36 => W112 | D37 => W110 | D38 => W108 | D39 => W106 | D40 => W104 | D41 => W102 | D42 => W100 | D43 => W98 | D44 => W96 | D45 => W94 | D46 => W92 | D47 => W90 | D48 => W88 | D49 => W86 | D50 => W84 | D51 => W82 | D52 => W80 | D53 => W78 | D54 => W76 | D55 => W74 | D56 => W72 | D57 => W70 | D58 => W68 | D59 => W66 | D60 => W64 | D61 => W190 | D62 => W188 | D63 => W186 end
    | D57 => match b with D0 => W57 | D1 => W55 | D2 => W53 | D3 => W51 | D4 => W49 | D5 => W47 | D6 => W45 | D7 => W43 | D8 => W41 | D9 => W39 | D10 => W37 | D11 => W35 | D12 => W33 | D13 => W31 | D14 => W29 | D15 => W27 | D16 => W25 | D17 => W23 | D18 => W21 | D19 => W19 | D20 => W17 | D21 => W15 | D22 => W13 | D23 => W11 | D24 => W9 | D25 => W7 | D26 => W5 | D27 => W3 | D28 => W1 | D29 => W127 | D30 => W125 | D31 => W123 | D32 => W121 | D33 => W119 | D34 => W117 | D35 => W115 | D36 => W113 | D37 => W111 | D38 => W109 | D39 => W107 | D40 => W105 | D41 => W103 | D42 => W101 | D43 => W99 | D44 => W97 | D45 => W95 | D46 => W93 | D47 => W91 | D48 => W89 | D49 => W87 | D50 => W85 | D51 => W83 | D52 => W81 | D53 => W79 | D54 => W77 | D55 => W75 | D56 => W73 | D57 => W71 | D58 => W69 | D59 => W67 | D60 => W65 | D61 => W191 | D62 => W189 | D63 => W187 end
    | D58 => match b with D0 => W58 | D1 => W56 | D2 => W54 | D3 => W52 | D4 => W50 | D5 => W48 | D6 => W46 | D7 => W44 | D8 => W42 | D9 => W40 | D10 => W38 | D11 => W36 | D12 => W34 | D13 => W32 | D14 => W30 | D15 => W28 | D16 => W26 | D17 => W24 | D18 => W22 | D19 => W20 | D20 => W18 | D21 => W16 | D22 => W14 | D23 => W12 | D24 => W10 | D25 => W8 | D26 => W6 | D27 => W4 | D28 => W2 | D29 => W0 | D30 => W126 | D31 => W124 | D32 => W122 | D33 => W120 | D34 => W118 | D35 => W116 | D36 => W114 | D37 => W112 | D38 => W110 | D39 => W108 | D40 => W106 | D41 => W104 | D42 => W102 | D43 => W100 | D44 => W98 | D45 => W96 | D46 => W94 | D47 => W92 | D48 => W90 | D49 => W88 | D50 => W86 | D51 => W84 | D52 => W82 | D53 => W80 | D54 => W78 | D55 => W76 | D56 => W74 | D57 => W72 | D58 => W70 | D59 => W68 | D60 => W66 | D61 => W64 | D62 => W190 | D63 => W188 end
    | D59 => match b with D0 => W59 | D1 => W57 | D2 => W55 | D3 => W53 | D4 => W51 | D5 => W49 | D6 => W47 | D7 => W45 | D8 => W43 | D9 => W41 | D10 => W39 | D11 => W37 | D12 => W35 | D13 => W33 | D14 => W31 | D15 => W29 | D16 => W27 | D17 => W25 | D18 => W23 | D19 => W21 | D20 => W19 | D21 => W17 | D22 => W15 | D23 => W13 | D24 => W11 | D25 => W9 | D26 => W7 | D27 => W5 | D28 => W3 | D29 => W1 | D30 => W127 | D31 => W125 | D32 => W123 | D33 => W121 | D34 => W119 | D35 => W117 | D36 => W115 | D37 => W113 | D38 => W111 | D39 => W109 | D40 => W107 | D41 => W105 | D42 => W103 | D43 => W101 | D44 => W99 | D45 => W97 | D46 => W95 | D47 => W93 | D48 => W91 | D49 => W89 | D50 => W87 | D51 => W85 | D52 => W83 | D53 => W81 | D54 => W79 | D55 => W77 | D56 => W75 | D57 => W73 | D58 => W71 | D59 => W69 | D60 => W67 | D61 => W65 | D62 => W191 | D63 => W189 end
    | D60 => match b with D0 => W60 | D1 => W58 | D2 => W56 | D3 => W54 | D4 => W52 | D5 => W50 | D6 => W48 | D7 => W46 | D8 => W44 | D9 => W42 | D10 => W40 | D11 => W38 | D12 => W36 | D13 => W34 | D14 => W32 | D15 => W30 | D16 => W28 | D17 => W26 | D18 => W24 | D19 => W22 | D20 => W20 | D21 => W18 | D22 => W16 | D23 => W14 | D24 => W12 | D25 => W10 | D26 => W8 | D27 => W6 | D28 => W4 | D29 => W2 | D30 => W0 | D31 => W126 | D32 => W124 | D33 => W122 | D34 => W120 | D35 => W118 | D36 => W116 | D37 => W114 | D38 => W112 | D39 => W110 | D40 => W108 | D41 => W106 | D42 => W104 | D43 => W102 | D44 => W100 | D45 => W98 | D46 => W96 | D47 => W94 | D48 => W92 | D49 => W90 | D50 => W88 | D51 => W86 | D52 => W84 | D53 => W82 | D54 => W80 | D55 => W78 | D56 => W76 | D57 => W74 | D58 => W72 | D59 => W70 | D60 => W68 | D61 => W66 | D62 => W64 | D63 => W190 end
    | D61 => match b with D0 => W61 | D1 => W59 | D2 => W57 | D3 => W55 | D4 => W53 | D5 => W51 | D6 => W49 | D7 => W47 | D8 => W45 | D9 => W43 | D10 => W41 | D11 => W39 | D12 => W37 | D13 => W35 | D14 => W33 | D15 => W31 | D16 => W29 | D17 => W27 | D18 => W25 | D19 => W23 | D20 => W21 | D21 => W19 | D22 => W17 | D23 => W15 | D24 => W13 | D25 => W11 | D26 => W9 | D27 => W7 | D28 => W5 | D29 => W3 | D30 => W1 | D31 => W127 | D32 => W125 | D33 => W123 | D34 => W121 | D35 => W119 | D36 => W117 | D37 => W115 | D38 => W113 | D39 => W111 | D40 => W109 | D41 => W107 | D42 => W105 | D43 => W103 | D44 => W101 | D45 => W99 | D46 => W97 | D47 => W95 | D48 => W93 | D49 => W91 | D50 => W89 | D51 => W87 | D52 => W85 | D53 => W83 | D54 => W81 | D55 => W79 | D56 => W77 | D57 => W75 | D58 => W73 | D59 => W71 | D60 => W69 | D61 => W67 | D62 => W65 | D63 => W191 end
    | D62 => match b with D0 => W62 | D1 => W60 | D2 => W58 | D3 => W56 | D4 => W54 | D5 => W52 | D6 => W50 | D7 => W48 | D8 => W46 | D9 => W44 | D10 => W42 | D11 => W40 | D12 => W38 | D13 => W36 | D14 => W34 | D15 => W32 | D16 => W30 | D17 => W28 | D18 => W26 | D19 => W24 | D20 => W22 | D21 => W20 | D22 => W18 | D23 => W16 | D24 => W14 | D25 => W12 | D26 => W10 | D27 => W8 | D28 => W6 | D29 => W4 | D30 => W2 | D31 => W0 | D32 => W126 | D33 => W124 | D34 => W122 | D35 => W120 | D36 => W118 | D37 => W116 | D38 => W114 | D39 => W112 | D40 => W110 | D41 => W108 | D42 => W106 | D43 => W104 | D44 => W102 | D45 => W100 | D46 => W98 | D47 => W96 | D48 => W94 | D49 => W92 | D50 => W90 | D51 => W88 | D52 => W86 | D53 => W84 | D54 => W82 | D55 => W80 | D56 => W78 | D57 => W76 | D58 => W74 | D59 => W72 | D60 => W70 | D61 => W68 | D62 => W66 | D63 => W64 end
    | D63 => match b with D0 => W63 | D1 => W61 | D2 => W59 | D3 => W57 | D4 => W55 | D5 => W53 | D6 => W51 | D7 => W49 | D8 => W47 | D9 => W45 | D10 => W43 | D11 => W41 | D12 => W39 | D13 => W37 | D14 => W35 | D15 => W33 | D16 => W31 | D17 => W29 | D18 => W27 | D19 => W25 | D20 => W23 | D21 => W21 | D22 => W19 | D23 => W17 | D24 => W15 | D25 => W13 | D26 => W11 | D27 => W9 | D28 => W7 | D29 => W5 | D30 => W3 | D31 => W1 | D32 => W127 | D33 => W125 | D34 => W123 | D35 => W121 | D36 => W119 | D37 => W117 | D38 => W115 | D39 => W113 | D40 => W111 | D41 => W109 | D42 => W107 | D43 => W105 | D44 => W103 | D45 => W101 | D46 => W99 | D47 => W97 | D48 => W95 | D49 => W93 | D50 => W91 | D51 => W89 | D52 => W87 | D53 => W85 | D54 => W83 | D55 => W81 | D56 => W79 | D57 => W77 | D58 => W75 | D59 => W73 | D60 => W71 | D61 => W69 | D62 => W67 | D63 => W65 end
    end
  | C1 => match a with
    | D0 => match b with D0 => W127 | D1 => W125 | D2 => W123 | D3 => W121 | D4 => W119 | D5 => W117 | D6 => W115 | D7 => W113 | D8 => W111 | D9 => W109 | D10 => W107 | D11 => W105 | D12 => W103 | D13 => W101 | D14 => W99 | D15 => W97 | D16 => W95 | D17 => W93 | D18 => W91 | D19 => W89 | D20 => W87 | D21 => W85 | D22 => W83 | D23 => W81 | D24 => W79 | D25 => W77 | D26 => W75 | D27 => W73 | D28 => W71 | D29 => W69 | D30 => W67 | D31 => W65 | D32 => W191 | D33 => W189 | D34 => W187 | D35 => W185 | D36 => W183 | D37 => W181 | D38 => W179 | D39 => W177 | D40 => W175 | D41 => W173 | D42 => W171 | D43 => W169 | D44 => W167 | D45 => W165 | D46 => W163 | D47 => W161 | D48 => W159 | D49 => W157 | D50 => W155 | D51 => W153 | D52 => W151 | D53 => W149 | D54 => W147 | D55 => W145 | D56 => W143 | D57 => W141 | D58 => W139 | D59 => W137 | D60 => W135 | D61 => W133 | D62 => W131 | D63 => W129 end
    | D1 => match b with D0 => W0 | D1 => W126 | D2 => W124 | D3 => W122 | D4 => W120 | D5 => W118 | D6 => W116 | D7 => W114 | D8 => W112 | D9 => W110 | D10 => W108 | D11 => W106 | D12 => W104 | D13 => W102 | D14 => W100 | D15 => W98 | D16 => W96 | D17 => W94 | D18 => W92 | D19 => W90 | D20 => W88 | D21 => W86 | D22 => W84 | D23 => W82 | D24 => W80 | D25 => W78 | D26 => W76 | D27 => W74 | D28 => W72 | D29 => W70 | D30 => W68 | D31 => W66 | D32 => W64 | D33 => W190 | D34 => W188 | D35 => W186 | D36 => W184 | D37 => W182 | D38 => W180 | D39 => W178 | D40 => W176 | D41 => W174 | D42 => W172 | D43 => W170 | D44 => W168 | D45 => W166 | D46 => W164 | D47 => W162 | D48 => W160 | D49 => W158 | D50 => W156 | D51 => W154 | D52 => W152 | D53 => W150 | D54 => W148 | D55 => W146 | D56 => W144 | D57 => W142 | D58 => W140 | D59 => W138 | D60 => W136 | D61 => W134 | D62 => W132 | D63 => W130 end
    | D2 => match b with D0 => W1 | D1 => W127 | D2 => W125 | D3 => W123 | D4 => W121 | D5 => W119 | D6 => W117 | D7 => W115 | D8 => W113 | D9 => W111 | D10 => W109 | D11 => W107 | D12 => W105 | D13 => W103 | D14 => W101 | D15 => W99 | D16 => W97 | D17 => W95 | D18 => W93 | D19 => W91 | D20 => W89 | D21 => W87 | D22 => W85 | D23 => W83 | D24 => W81 | D25 => W79 | D26 => W77 | D27 => W75 | D28 => W73 | D29 => W71 | D30 => W69 | D31 => W67 | D32 => W65 | D33 => W191 | D34 => W189 | D35 => W187 | D36 => W185 | D37 => W183 | D38 => W181 | D39 => W179 | D40 => W177 | D41 => W175 | D42 => W173 | D43 => W171 | D44 => W169 | D45 => W167 | D46 => W165 | D47 => W163 | D48 => W161 | D49 => W159 | D50 => W157 | D51 => W155 | D52 => W153 | D53 => W151 | D54 => W149 | D55 => W147 | D56 => W145 | D57 => W143 | D58 => W141 | D59 => W139 | D60 => W137 | D61 => W135 | D62 => W133 | D63 => W131 end
    | D3 => match b with D0 => W2 | D1 => W0 | D2 => W126 | D3 => W124 | D4 => W122 | D5 => W120 | D6 => W118 | D7 => W116 | D8 => W114 | D9 => W112 | D10 => W110 | D11 => W108 | D12 => W106 | D13 => W104 | D14 => W102 | D15 => W100 | D16 => W98 | D17 => W96 | D18 => W94 | D19 => W92 | D20 => W90 | D21 => W88 | D22 => W86 | D23 => W84 | D24 => W82 | D25 => W80 | D26 => W78 | D27 => W76 | D28 => W74 | D29 => W72 | D30 => W70 | D31 => W68 | D32 => W66 | D33 => W64 | D34 => W190 | D35 => W188 | D36 => W186 | D37 => W184 | D38 => W182 | D39 => W180 | D40 => W178 | D41 => W176 | D42 => W174 | D43 => W172 | D44 => W170 | D45 => W168 | D46 => W166 | D47 => W164 | D48 => W162 | D49 => W160 | D50 => W158 | D51 => W156 | D52 => W154 | D53 => W152 | D54 => W150 | D55 => W148 | D56 => W146 | D57 => W144 | D58 => W142 | D59 => W140 | D60 => W138 | D61 => W136 | D62 => W134 | D63 => W132 end
    | D4 => match b with D0 => W3 | D1 => W1 | D2 => W127 | D3 => W125 | D4 => W123 | D5 => W121 | D6 => W119 | D7 => W117 | D8 => W115 | D9 => W113 | D10 => W111 | D11 => W109 | D12 => W107 | D13 => W105 | D14 => W103 | D15 => W101 | D16 => W99 | D17 => W97 | D18 => W95 | D19 => W93 | D20 => W91 | D21 => W89 | D22 => W87 | D23 => W85 | D24 => W83 | D25 => W81 | D26 => W79 | D27 => W77 | D28 => W75 | D29 => W73 | D30 => W71 | D31 => W69 | D32 => W67 | D33 => W65 | D34 => W191 | D35 => W189 | D36 => W187 | D37 => W185 | D38 => W183 | D39 => W181 | D40 => W179 | D41 => W177 | D42 => W175 | D43 => W173 | D44 => W171 | D45 => W169 | D46 => W167 | D47 => W165 | D48 => W163 | D49 => W161 | D50 => W159 | D51 => W157 | D52 => W155 | D53 => W153 | D54 => W151 | D55 => W149 | D56 => W147 | D57 => W145 | D58 => W143 | D59 => W141 | D60 => W139 | D61 => W137 | D62 => W135 | D63 => W133 end
    | D5 => match b with D0 => W4 | D1 => W2 | D2 => W0 | D3 => W126 | D4 => W124 | D5 => W122 | D6 => W120 | D7 => W118 | D8 => W116 | D9 => W114 | D10 => W112 | D11 => W110 | D12 => W108 | D13 => W106 | D14 => W104 | D15 => W102 | D16 => W100 | D17 => W98 | D18 => W96 | D19 => W94 | D20 => W92 | D21 => W90 | D22 => W88 | D23 => W86 | D24 => W84 | D25 => W82 | D26 => W80 | D27 => W78 | D28 => W76 | D29 => W74 | D30 => W72 | D31 => W70 | D32 => W68 | D33 => W66 | D34 => W64 | D35 => W190 | D36 => W188 | D37 => W186 | D38 => W184 | D39 => W182 | D40 => W180 | D41 => W178 | D42 => W176 | D43 => W174 | D44 => W172 | D45 => W170 | D46 => W168 | D47 => W166 | D48 => W164 | D49 => W162 | D50 => W160 | D51 => W158 | D52 => W156 | D53 => W154 | D54 => W152 | D55 => W150 | D56 => W148 | D57 => W146 | D58 => W144 | D59 => W142 | D60 => W140 | D61 => W138 | D62 => W136 | D63 => W134 end
    | D6 => match b with D0 => W5 | D1 => W3 | D2 => W1 | D3 => W127 | D4 => W125 | D5 => W123 | D6 => W121 | D7 => W119 | D8 => W117 | D9 => W115 | D10 => W113 | D11 => W111 | D12 => W109 | D13 => W107 | D14 => W105 | D15 => W103 | D16 => W101 | D17 => W99 | D18 => W97 | D19 => W95 | D20 => W93 | D21 => W91 | D22 => W89 | D23 => W87 | D24 => W85 | D25 => W83 | D26 => W81 | D27 => W79 | D28 => W77 | D29 => W75 | D30 => W73 | D31 => W71 | D32 => W69 | D33 => W67 | D34 => W65 | D35 => W191 | D36 => W189 | D37 => W187 | D38 => W185 | D39 => W183 | D40 => W181 | D41 => W179 | D42 => W177 | D43 => W175 | D44 => W173 | D45 => W171 | D46 => W169 | D47 => W167 | D48 => W165 | D49 => W163 | D50 => W161 | D51 => W159 | D52 => W157 | D53 => W155 | D54 => W153 | D55 => W151 | D56 => W149 | D57 => W147 | D58 => W145 | D59 => W143 | D60 => W141 | D61 => W139 | D62 => W137 | D63 => W135 end
    | D7 => match b with D0 => W6 | D1 => W4 | D2 => W2 | D3 => W0 | D4 => W126 | D5 => W124 | D6 => W122 | D7 => W120 | D8 => W118 | D9 => W116 | D10 => W114 | D11 => W112 | D12 => W110 | D13 => W108 | D14 => W106 | D15 => W104 | D16 => W102 | D17 => W100 | D18 => W98 | D19 => W96 | D20 => W94 | D21 => W92 | D22 => W90 | D23 => W88 | D24 => W86 | D25 => W84 | D26 => W82 | D27 => W80 | D28 => W78 | D29 => W76 | D30 => W74 | D31 => W72 | D32 => W70 | D33 => W68 | D34 => W66 | D35 => W64 | D36 => W190 | D37 => W188 | D38 => W186 | D39 => W184 | D40 => W182 | D41 => W180 | D42 => W178 | D43 => W176 | D44 => W174 | D45 => W172 | D46 => W170 | D47 => W168 | D48 => W166 | D49 => W164 | D50 => W162 | D51 => W160 | D52 => W158 | D53 => W156 | D54 => W154 | D55 => W152 | D56 => W150 | D57 => W148 | D58 => W146 | D59 => W144 | D60 => W142 | D61 => W140 | D62 => W138 | D63 => W136 end
    | D8 => match b with D0 => W7 | D1 => W5 | D2 => W3 | D3 => W1 | D4 => W127 | D5 => W125 | D6 => W123 | D7 => W121 | D8 => W119 | D9 => W117 | D10 => W115 | D11 => W113 | D12 => W111 | D13 => W109 | D14 => W107 | D15 => W105 | D16 => W103 | D17 => W101 | D18 => W99 | D19 => W97 | D20 => W95 | D21 => W93 | D22 => W91 | D23 => W89 | D24 => W87 | D25 => W85 | D26 => W83 | D27 => W81 | D28 => W79 | D29 => W77 | D30 => W75 | D31 => W73 | D32 => W71 | D33 => W69 | D34 => W67 | D35 => W65 | D36 => W191 | D37 => W189 | D38 => W187 | D39 => W185 | D40 => W183 | D41 => W181 | D42 => W179 | D43 => W177 | D44 => W175 | D45 => W173 | D46 => W171 | D47 => W169 | D48 => W167 | D49 => W165 | D50 => W163 | D51 => W161 | D52 => W159 | D53 => W157 | D54 => W155 | D55 => W153 | D56 => W151 | D57 => W149 | D58 => W147 | D59 => W145 | D60 => W143 | D61 => W141 | D62 => W139 | D63 => W137 end
    | D9 => match b with D0 => W8 | D1 => W6 | D2 => W4 | D3 => W2 | D4 => W0 | D5 => W126 | D6 => W124 | D7 => W122 | D8 => W120 | D9 => W118 | D10 => W116 | D11 => W114 | D12 => W112 | D13 => W110 | D14 => W108 | D15 => W106 | D16 => W104 | D17 => W102 | D18 => W100 | D19 => W98 | D20 => W96 | D21 => W94 | D22 => W92 | D23 => W90 | D24 => W88 | D25 => W86 | D26 => W84 | D27 => W82 | D28 => W80 | D29 => W78 | D30 => W76 | D31 => W74 | D32 => W72 | D33 => W70 | D34 => W68 | D35 => W66 | D36 => W64 | D37 => W190 | D38 => W188 | D39 => W186 | D40 => W184 | D41 => W182 | D42 => W180 | D43 => W178 | D44 => W176 | D45 => W174 | D46 => W172 | D47 => W170 | D48 => W168 | D49 => W166 | D50 => W164 | D51 => W162 | D52 => W160 | D53 => W158 | D54 => W156 | D55 => W154 | D56 => W152 | D57 => W150 | D58 => W148 | D59 => W146 | D60 => W144 | D61 => W142 | D62 => W140 | D63 => W138 end
    | D10 => match b with D0 => W9 | D1 => W7 | D2 => W5 | D3 => W3 | D4 => W1 | D5 => W127 | D6 => W125 | D7 => W123 | D8 => W121 | D9 => W119 | D10 => W117 | D11 => W115 | D12 => W113 | D13 => W111 | D14 => W109 | D15 => W107 | D16 => W105 | D17 => W103 | D18 => W101 | D19 => W99 | D20 => W97 | D21 => W95 | D22 => W93 | D23 => W91 | D24 => W89 | D25 => W87 | D26 => W85 | D27 => W83 | D28 => W81 | D29 => W79 | D30 => W77 | D31 => W75 | D32 => W73 | D33 => W71 | D34 => W69 | D35 => W67 | D36 => W65 | D37 => W191 | D38 => W189 | D39 => W187 | D40 => W185 | D41 => W183 | D42 => W181 | D43 => W179 | D44 => W177 | D45 => W175 | D46 => W173 | D47 => W171 | D48 => W169 | D49 => W167 | D50 => W165 | D51 => W163 | D52 => W161 | D53 => W159 | D54 => W157 | D55 => W155 | D56 => W153 | D57 => W151 | D58 => W149 | D59 => W147 | D60 => W145 | D61 => W143 | D62 => W141 | D63 => W139 end
    | D11 => match b with D0 => W10 | D1 => W8 | D2 => W6 | D3 => W4 | D4 => W2 | D5 => W0 | D6 => W126 | D7 => W124 | D8 => W122 | D9 => W120 | D10 => W118 | D11 => W116 | D12 => W114 | D13 => W112 | D14 => W110 | D15 => W108 | D16 => W106 | D17 => W104 | D18 => W102 | D19 => W100 | D20 => W98 | D21 => W96 | D22 => W94 | D23 => W92 | D24 => W90 | D25 => W88 | D26 => W86 | D27 => W84 | D28 => W82 | D29 => W80 | D30 => W78 | D31 => W76 | D32 => W74 | D33 => W72 | D34 => W70 | D35 => W68 | D36 => W66 | D37 => W64 | D38 => W190 | D39 => W188 | D40 => W186 | D41 => W184 | D42 => W182 | D43 => W180 | D44 => W178 | D45 => W176 | D46 => W174 | D47 => W172 | D48 => W170 | D49 => W168 | D50 => W166 | D51 => W164 | D52 => W162 | D53 => W160 | D54 => W158 | D55 => W156 | D56 => W154 | D57 => W152 | D58 => W150 | D59 => W148 | D60 => W146 | D61 => W144 | D62 => W142 | D63 => W140 end
    | D12 => match b with D0 => W11 | D1 => W9 | D2 => W7 | D3 => W5 | D4 => W3 | D5 => W1 | D6 => W127 | D7 => W125 | D8 => W123 | D9 => W121 | D10 => W119 | D11 => W117 | D12 => W115 | D13 => W113 | D14 => W111 | D15 => W109 | D16 => W107 | D17 => W105 | D18 => W103 | D19 => W101 | D20 => W99 | D21 => W97 | D22 => W95 | D23 => W93 | D24 => W91 | D25 => W89 | D26 => W87 | D27 => W85 | D28 => W83 | D29 => W81 | D30 => W79 | D31 => W77 | D32 => W75 | D33 => W73 | D34 => W71 | D35 => W69 | D36 => W67 | D37 => W65 | D38 => W191 | D39 => W189 | D40 => W187 | D41 => W185 | D42 => W183 | D43 => W181 | D44 => W179 | D45 => W177 | D46 => W175 | D47 => W173 | D48 => W171 | D49 => W169 | D50 => W167 | D51 => W165 | D52 => W163 | D53 => W161 | D54 => W159 | D55 => W157 | D56 => W155 | D57 => W153 | D58 => W151 | D59 => W149 | D60 => W147 | D61 => W145 | D62 => W143 | D63 => W141 end
    | D13 => match b with D0 => W12 | D1 => W10 | D2 => W8 | D3 => W6 | D4 => W4 | D5 => W2 | D6 => W0 | D7 => W126 | D8 => W124 | D9 => W122 | D10 => W120 | D11 => W118 | D12 => W116 | D13 => W114 | D14 => W112 | D15 => W110 | D16 => W108 | D17 => W106 | D18 => W104 | D19 => W102 | D20 => W100 | D21 => W98 | D22 => W96 | D23 => W94 | D24 => W92 | D25 => W90 | D26 => W88 | D27 => W86 | D28 => W84 | D29 => W82 | D30 => W80 | D31 => W78 | D32 => W76 | D33 => W74 | D34 => W72 | D35 => W70 | D36 => W68 | D37 => W66 | D38 => W64 | D39 => W190 | D40 => W188 | D41 => W186 | D42 => W184 | D43 => W182 | D44 => W180 | D45 => W178 | D46 => W176 | D47 => W174 | D48 => W172 | D49 => W170 | D50 => W168 | D51 => W166 | D52 => W164 | D53 => W162 | D54 => W160 | D55 => W158 | D56 => W156 | D57 => W154 | D58 => W152 | D59 => W150 | D60 => W148 | D61 => W146 | D62 => W144 | D63 => W142 end
    | D14 => match b with D0 => W13 | D1 => W11 | D2 => W9 | D3 => W7 | D4 => W5 | D5 => W3 | D6 => W1 | D7 => W127 | D8 => W125 | D9 => W123 | D10 => W121 | D11 => W119 | D12 => W117 | D13 => W115 | D14 => W113 | D15 => W111 | D16 => W109 | D17 => W107 | D18 => W105 | D19 => W103 | D20 => W101 | D21 => W99 | D22 => W97 | D23 => W95 | D24 => W93 | D25 => W91 | D26 => W89 | D27 => W87 | D28 => W85 | D29 => W83 | D30 => W81 | D31 => W79 | D32 => W77 | D33 => W75 | D34 => W73 | D35 => W71 | D36 => W69 | D37 => W67 | D38 => W65 | D39 => W191 | D40 => W189 | D41 => W187 | D42 => W185 | D43 => W183 | D44 => W181 | D45 => W179 | D46 => W177 | D47 => W175 | D48 => W173 | D49 => W171 | D50 => W169 | D51 => W167 | D52 => W165 | D53 => W163 | D54 => W161 | D55 => W159 | D56 => W157 | D57 => W155 | D58 => W153 | D59 => W151 | D60 => W149 | D61 => W147 | D62 => W145 | D63 => W143 end
    | D15 => match b with D0 => W14 | D1 => W12 | D2 => W10 | D3 => W8 | D4 => W6 | D5 => W4 | D6 => W2 | D7 => W0 | D8 => W126 | D9 => W124 | D10 => W122 | D11 => W120 | D12 => W118 | D13 => W116 | D14 => W114 | D15 => W112 | D16 => W110 | D17 => W108 | D18 => W106 | D19 => W104 | D20 => W102 | D21 => W100 | D22 => W98 | D23 => W96 | D24 => W94 | D25 => W92 | D26 => W90 | D27 => W88 | D28 => W86 | D29 => W84 | D30 => W82 | D31 => W80 | D32 => W78 | D33 => W76 | D34 => W74 | D35 => W72 | D36 => W70 | D37 => W68 | D38 => W66 | D39 => W64 | D40 => W190 | D41 => W188 | D42 => W186 | D43 => W184 | D44 => W182 | D45 => W180 | D46 => W178 | D47 => W176 | D48 => W174 | D49 => W172 | D50 => W170 | D51 => W168 | D52 => W166 | D53 => W164 | D54 => W162 | D55 => W160 | D56 => W158 | D57 => W156 | D58 => W154 | D59 => W152 | D60 => W150 | D61 => W148 | D62 => W146 | D63 => W144 end
    | D16 => match b with D0 => W15 | D1 => W13 | D2 => W11 | D3 => W9 | D4 => W7 | D5 => W5 | D6 => W3 | D7 => W1 | D8 => W127 | D9 => W125 | D10 => W123 | D11 => W121 | D12 => W119 | D13 => W117 | D14 => W115 | D15 => W113 | D16 => W111 | D17 => W109 | D18 => W107 | D19 => W105 | D20 => W103 | D21 => W101 | D22 => W99 | D23 => W97 | D24 => W95 | D25 => W93 | D26 => W91 | D27 => W89 | D28 => W87 | D29 => W85 | D30 => W83 | D31 => W81 | D32 => W79 | D33 => W77 | D34 => W75 | D35 => W73 | D36 => W71 | D37 => W69 | D38 => W67 | D39 => W65 | D40 => W191 | D41 => W189 | D42 => W187 | D43 => W185 | D44 => W183 | D45 => W181 | D46 => W179 | D47 => W177 | D48 => W175 | D49 => W173 | D50 => W171 | D51 => W169 | D52 => W167 | D53 => W165 | D54 => W163 | D55 => W161 | D56 => W159 | D57 => W157 | D58 => W155 | D59 => W153 | D60 => W151 | D61 => W149 | D62 => W147 | D63 => W145 end
    | D17 => match b with D0 => W16 | D1 => W14 | D2 => W12 | D3 => W10 | D4 => W8 | D5 => W6 | D6 => W4 | D7 => W2 | D8 => W0 | D9 => W126 | D10 => W124 | D11 => W122 | D12 => W120 | D13 => W118 | D14 => W116 | D15 => W114 | D16 => W112 | D17 => W110 | D18 => W108 | D19 => W106 | D20 => W104 | D21 => W102 | D22 => W100 | D23 => W98 | D24 => W96 | D25 => W94 | D26 => W92 | D27 => W90 | D28 => W88 | D29 => W86 | D30 => W84 | D31 => W82 | D32 => W80 | D33 => W78 | D34 => W76 | D35 => W74 | D36 => W72 | D37 => W70 | D38 => W68 | D39 => W66 | D40 => W64 | D41 => W190 | D42 => W188 | D43 => W186 | D44 => W184 | D45 => W182 | D46 => W180 | D47 => W178 | D48 => W176 | D49 => W174 | D50 => W172 | D51 => W170 | D52 => W168 | D53 => W166 | D54 => W164 | D55 => W162 | D56 => W160 | D57 => W158 | D58 => W156 | D59 => W154 | D60 => W152 | D61 => W150 | D62 => W148 | D63 => W146 end
    | D18 => match b with D0 => W17 | D1 => W15 | D2 => W13 | D3 => W11 | D4 => W9 | D5 => W7 | D6 => W5 | D7 => W3 | D8 => W1 | D9 => W127 | D10 => W125 | D11 => W123 | D12 => W121 | D13 => W119 | D14 => W117 | D15 => W115 | D16 => W113 | D17 => W111 | D18 => W109 | D19 => W107 | D20 => W105 | D21 => W103 | D22 => W101 | D23 => W99 | D24 => W97 | D25 => W95 | D26 => W93 | D27 => W91 | D28 => W89 | D29 => W87 | D30 => W85 | D31 => W83 | D32 => W81 | D33 => W79 | D34 => W77 | D35 => W75 | D36 => W73 | D37 => W71 | D38 => W69 | D39 => W67 | D40 => W65 | D41 => W191 | D42 => W189 | D43 => W187 | D44 => W185 | D45 => W183 | D46 => W181 | D47 => W179 | D48 => W177 | D49 => W175 | D50 => W173 | D51 => W171 | D52 => W169 | D53 => W167 | D54 => W165 | D55 => W163 | D56 => W161 | D57 => W159 | D58 => W157 | D59 => W155 | D60 => W153 | D61 => W151 | D62 => W149 | D63 => W147 end
    | D19 => match b with D0 => W18 | D1 => W16 | D2 => W14 | D3 => W12 | D4 => W10 | D5 => W8 | D6 => W6 | D7 => W4 | D8 => W2 | D9 => W0 | D10 => W126 | D11 => W124 | D12 => W122 | D13 => W120 | D14 => W118 | D15 => W116 | D16 => W114 | D17 => W112 | D18 => W110 | D19 => W108 | D20 => W106 | D21 => W104 | D22 => W102 | D23 => W100 | D24 => W98 | D25 => W96 | D26 => W94 | D27 => W92 | D28 => W90 | D29 => W88 | D30 => W86 | D31 => W84 | D32 => W82 | D33 => W80 | D34 => W78 | D35 => W76 | D36 => W74 | D37 => W72 | D38 => W70 | D39 => W68 | D40 => W66 | D41 => W64 | D42 => W190 | D43 => W188 | D44 => W186 | D45 => W184 | D46 => W182 | D47 => W180 | D48 => W178 | D49 => W176 | D50 => W174 | D51 => W172 | D52 => W170 | D53 => W168 | D54 => W166 | D55 => W164 | D56 => W162 | D57 => W160 | D58 => W158 | D59 => W156 | D60 => W154 | D61 => W152 | D62 => W150 | D63 => W148 end
    | D20 => match b with D0 => W19 | D1 => W17 | D2 => W15 | D3 => W13 | D4 => W11 | D5 => W9 | D6 => W7 | D7 => W5 | D8 => W3 | D9 => W1 | D10 => W127 | D11 => W125 | D12 => W123 | D13 => W121 | D14 => W119 | D15 => W117 | D16 => W115 | D17 => W113 | D18 => W111 | D19 => W109 | D20 => W107 | D21 => W105 | D22 => W103 | D23 => W101 | D24 => W99 | D25 => W97 | D26 => W95 | D27 => W93 | D28 => W91 | D29 => W89 | D30 => W87 | D31 => W85 | D32 => W83 | D33 => W81 | D34 => W79 | D35 => W77 | D36 => W75 | D37 => W73 | D38 => W71 | D39 => W69 | D40 => W67 | D41 => W65 | D42 => W191 | D43 => W189 | D44 => W187 | D45 => W185 | D46 => W183 | D47 => W181 | D48 => W179 | D49 => W177 | D50 => W175 | D51 => W173 | D52 => W171 | D53 => W169 | D54 => W167 | D55 => W165 | D56 => W163 | D57 => W161 | D58 => W159 | D59 => W157 | D60 => W155 | D61 => W153 | D62 => W151 | D63 => W149 end
    | D21 => match b with D0 => W20 | D1 => W18 | D2 => W16 | D3 => W14 | D4 => W12 | D5 => W10 | D6 => W8 | D7 => W6 | D8 => W4 | D9 => W2 | D10 => W0 | D11 => W126 | D12 => W124 | D13 => W122 | D14 => W120 | D15 => W118 | D16 => W116 | D17 => W114 | D18 => W112 | D19 => W110 | D20 => W108 | D21 => W106 | D22 => W104 | D23 => W102 | D24 => W100 | D25 => W98 | D26 => W96 | D27 => W94 | D28 => W92 | D29 => W90 | D30 => W88 | D31 => W86 | D32 => W84 | D33 => W82 | D34 => W80 | D35 => W78 | D36 => W76 | D37 => W74 | D38 => W72 | D39 => W70 | D40 => W68 | D41 => W66 | D42 => W64 | D43 => W190 | D44 => W188 | D45 => W186 | D46 => W184 | D47 => W182 | D48 => W180 | D49 => W178 | D50 => W176 | D51 => W174 | D52 => W172 | D53 => W170 | D54 => W168 | D55 => W166 | D56 => W164 | D57 => W162 | D58 => W160 | D59 => W158 | D60 => W156 | D61 => W154 | D62 => W152 | D63 => W150 end
    | D22 => match b with D0 => W21 | D1 => W19 | D2 => W17 | D3 => W15 | D4 => W13 | D5 => W11 | D6 => W9 | D7 => W7 | D8 => W5 | D9 => W3 | D10 => W1 | D11 => W127 | D12 => W125 | D13 => W123 | D14 => W121 | D15 => W119 | D16 => W117 | D17 => W115 | D18 => W113 | D19 => W111 | D20 => W109 | D21 => W107 | D22 => W105 | D23 => W103 | D24 => W101 | D25 => W99 | D26 => W97 | D27 => W95 | D28 => W93 | D29 => W91 | D30 => W89 | D31 => W87 | D32 => W85 | D33 => W83 | D34 => W81 | D35 => W79 | D36 => W77 | D37 => W75 | D38 => W73 | D39 => W71 | D40 => W69 | D41 => W67 | D42 => W65 | D43 => W191 | D44 => W189 | D45 => W187 | D46 => W185 | D47 => W183 | D48 => W181 | D49 => W179 | D50 => W177 | D51 => W175 | D52 => W173 | D53 => W171 | D54 => W169 | D55 => W167 | D56 => W165 | D57 => W163 | D58 => W161 | D59 => W159 | D60 => W157 | D61 => W155 | D62 => W153 | D63 => W151 end
    | D23 => match b with D0 => W22 | D1 => W20 | D2 => W18 | D3 => W16 | D4 => W14 | D5 => W12 | D6 => W10 | D7 => W8 | D8 => W6 | D9 => W4 | D10 => W2 | D11 => W0 | D12 => W126 | D13 => W124 | D14 => W122 | D15 => W120 | D16 => W118 | D17 => W116 | D18 => W114 | D19 => W112 | D20 => W110 | D21 => W108 | D22 => W106 | D23 => W104 | D24 => W102 | D25 => W100 | D26 => W98 | D27 => W96 | D28 => W94 | D29 => W92 | D30 => W90 | D31 => W88 | D32 => W86 | D33 => W84 | D34 => W82 | D35 => W80 | D36 => W78 | D37 => W76 | D38 => W74 | D39 => W72 | D40 => W70 | D41 => W68 | D42 => W66 | D43 => W64 | D44 => W190 | D45 => W188 | D46 => W186 | D47 => W184 | D48 => W182 | D49 => W180 | D50 => W178 | D51 => W176 | D52 => W174 | D53 => W172 | D54 => W170 | D55 => W168 | D56 => W166 | D57 => W164 | D58 => W162 | D59 => W160 | D60 => W158 | D61 => W156 | D62 => W154 | D63 => W152 end
    | D24 => match b with D0 => W23 | D1 => W21 | D2 => W19 | D3 => W17 | D4 => W15 | D5 => W13 | D6 => W11 | D7 => W9 | D8 => W7 | D9 => W5 | D10 => W3 | D11 => W1 | D12 => W127 | D13 => W125 | D14 => W123 | D15 => W121 | D16 => W119 | D17 => W117 | D18 => W115 | D19 => W113 | D20 => W111 | D21 => W109 | D22 => W107 | D23 => W105 | D24 => W103 | D25 => W101 | D26 => W99 | D27 => W97 | D28 => W95 | D29 => W93 | D30 => W91 | D31 => W89 | D32 => W87 | D33 => W85 | D34 => W83 | D35 => W81 | D36 => W79 | D37 => W77 | D38 => W75 | D39 => W73 | D40 => W71 | D41 => W69 | D42 => W67 | D43 => W65 | D44 => W191 | D45 => W189 | D46 => W187 | D47 => W185 | D48 => W183 | D49 => W181 | D50 => W179 | D51 => W177 | D52 => W175 | D53 => W173 | D54 => W171 | D55 => W169 | D56 => W167 | D57 => W165 | D58 => W163 | D59 => W161 | D60 => W159 | D61 => W157 | D62 => W155 | D63 => W153 end
    | D25 => match b with D0 => W24 | D1 => W22 | D2 => W20 | D3 => W18 | D4 => W16 | D5 => W14 | D6 => W12 | D7 => W10 | D8 => W8 | D9 => W6 | D10 => W4 | D11 => W2 | D12 => W0 | D13 => W126 | D14 => W124 | D15 => W122 | D16 => W120 | D17 => W118 | D18 => W116 | D19 => W114 | D20 => W112 | D21 => W110 | D22 => W108 | D23 => W106 | D24 => W104 | D25 => W102 | D26 => W100 | D27 => W98 | D28 => W96 | D29 => W94 | D30 => W92 | D31 => W90 | D32 => W88 | D33 => W86 | D34 => W84 | D35 => W82 | D36 => W80 | D37 => W78 | D38 => W76 | D39 => W74 | D40 => W72 | D41 => W70 | D42 => W68 | D43 => W66 | D44 => W64 | D45 => W190 | D46 => W188 | D47 => W186 | D48 => W184 | D49 => W182 | D50 => W180 | D51 => W178 | D52 => W176 | D53 => W174 | D54 => W172 | D55 => W170 | D56 => W168 | D57 => W166 | D58 => W164 | D59 => W162 | D60 => W160 | D61 => W158 | D62 => W156 | D63 => W154 end
    | D26 => match b with D0 => W25 | D1 => W23 | D2 => W21 | D3 => W19 | D4 => W17 | D5 => W15 | D6 => W13 | D7 => W11 | D8 => W9 | D9 => W7 | D10 => W5 | D11 => W3 | D12 => W1 | D13 => W127 | D14 => W125 | D15 => W123 | D16 => W121 | D17 => W119 | D18 => W117 | D19 => W115 | D20 => W113 | D21 => W111 | D22 => W109 | D23 => W107 | D24 => W105 | D25 => W103 | D26 => W101 | D27 => W99 | D28 => W97 | D29 => W95 | D30 => W93 | D31 => W91 | D32 => W89 | D33 => W87 | D34 => W85 | D35 => W83 | D36 => W81 | D37 => W79 | D38 => W77 | D39 => W75 | D40 => W73 | D41 => W71 | D42 => W69 | D43 => W67 | D44 => W65 | D45 => W191 | D46 => W189 | D47 => W187 | D48 => W185 | D49 => W183 | D50 => W181 | D51 => W179 | D52 => W177 | D53 => W175 | D54 => W173 | D55 => W171 | D56 => W169 | D57 => W167 | D58 => W165 | D59 => W163 | D60 => W161 | D61 => W159 | D62 => W157 | D63 => W155 end
    | D27 => match b with D0 => W26 | D1 => W24 | D2 => W22 | D3 => W20 | D4 => W18 | D5 => W16 | D6 => W14 | D7 => W12 | D8 => W10 | D9 => W8 | D10 => W6 | D11 => W4 | D12 => W2 | D13 => W0 | D14 => W126 | D15 => W124 | D16 => W122 | D17 => W120 | D18 => W118 | D19 => W116 | D20 => W114 | D21 => W112 | D22 => W110 | D23 => W108 | D24 => W106 | D25 => W104 | D26 => W102 | D27 => W100 | D28 => W98 | D29 => W96 | D30 => W94 | D31 => W92 | D32 => W90 | D33 => W88 | D34 => W86 | D35 => W84 | D36 => W82 | D37 => W80 | D38 => W78 | D39 => W76 | D40 => W74 | D41 => W72 | D42 => W70 | D43 => W68 | D44 => W66 | D45 => W64 | D46 => W190 | D47 => W188 | D48 => W186 | D49 => W184 | D50 => W182 | D51 => W180 | D52 => W178 | D53 => W176 | D54 => W174 | D55 => W172 | D56 => W170 | D57 => W168 | D58 => W166 | D59 => W164 | D60 => W162 | D61 => W160 | D62 => W158 | D63 => W156 end
    | D28 => match b with D0 => W27 | D1 => W25 | D2 => W23 | D3 => W21 | D4 => W19 | D5 => W17 | D6 => W15 | D7 => W13 | D8 => W11 | D9 => W9 | D10 => W7 | D11 => W5 | D12 => W3 | D13 => W1 | D14 => W127 | D15 => W125 | D16 => W123 | D17 => W121 | D18 => W119 | D19 => W117 | D20 => W115 | D21 => W113 | D22 => W111 | D23 => W109 | D24 => W107 | D25 => W105 | D26 => W103 | D27 => W101 | D28 => W99 | D29 => W97 | D30 => W95 | D31 => W93 | D32 => W91 | D33 => W89 | D34 => W87 | D35 => W85 | D36 => W83 | D37 => W81 | D38 => W79 | D39 => W77 | D40 => W75 | D41 => W73 | D42 => W71 | D43 => W69 | D44 => W67 | D45 => W65 | D46 => W191 | D47 => W189 | D48 => W187 | D49 => W185 | D50 => W183 | D51 => W181 | D52 => W179 | D53 => W177 | D54 => W175 | D55 => W173 | D56 => W171 | D57 => W169 | D58 => W167 | D59 => W165 | D60 => W163 | D61 => W161 | D62 => W159 | D63 => W157 end
    | D29 => match b with D0 => W28 | D1 => W26 | D2 => W24 | D3 => W22 | D4 => W20 | D5 => W18 | D6 => W16 | D7 => W14 | D8 => W12 | D9 => W10 | D10 => W8 | D11 => W6 | D12 => W4 | D13 => W2 | D14 => W0 | D15 => W126 | D16 => W124 | D17 => W122 | D18 => W120 | D19 => W118 | D20 => W116 | D21 => W114 | D22 => W112 | D23 => W110 | D24 => W108 | D25 => W106 | D26 => W104 | D27 => W102 | D28 => W100 | D29 => W98 | D30 => W96 | D31 => W94 | D32 => W92 | D33 => W90 | D34 => W88 | D35 => W86 | D36 => W84 | D37 => W82 | D38 => W80 | D39 => W78 | D40 => W76 | D41 => W74 | D42 => W72 | D43 => W70 | D44 => W68 | D45 => W66 | D46 => W64 | D47 => W190 | D48 => W188 | D49 => W186 | D50 => W184 | D51 => W182 | D52 => W180 | D53 => W178 | D54 => W176 | D55 => W174 | D56 => W172 | D57 => W170 | D58 => W168 | D59 => W166 | D60 => W164 | D61 => W162 | D62 => W160 | D63 => W158 end
    | D30 => match b with D0 => W29 | D1 => W27 | D2 => W25 | D3 => W23 | D4 => W21 | D5 => W19 | D6 => W17 | D7 => W15 | D8 => W13 | D9 => W11 | D10 => W9 | D11 => W7 | D12 => W5 | D13 => W3 | D14 => W1 | D15 => W127 | D16 => W125 | D17 => W123 | D18 => W121 | D19 => W119 | D20 => W117 | D21 => W115 | D22 => W113 | D23 => W111 | D24 => W109 | D25 => W107 | D26 => W105 | D27 => W103 | D28 => W101 | D29 => W99 | D30 => W97 | D31 => W95 | D32 => W93 | D33 => W91 | D34 => W89 | D35 => W87 | D36 => W85 | D37 => W83 | D38 => W81 | D39 => W79 | D40 => W77 | D41 => W75 | D42 => W73 | D43 => W71 | D44 => W69 | D45 => W67 | D46 => W65 | D47 => W191 | D48 => W189 | D49 => W187 | D50 => W185 | D51 => W183 | D52 => W181 | D53 => W179 | D54 => W177 | D55 => W175 | D56 => W173 | D57 => W171 | D58 => W169 | D59 => W167 | D60 => W165 | D61 => W163 | D62 => W161 | D63 => W159 end
    | D31 => match b with D0 => W30 | D1 => W28 | D2 => W26 | D3 => W24 | D4 => W22 | D5 => W20 | D6 => W18 | D7 => W16 | D8 => W14 | D9 => W12 | D10 => W10 | D11 => W8 | D12 => W6 | D13 => W4 | D14 => W2 | D15 => W0 | D16 => W126 | D17 => W124 | D18 => W122 | D19 => W120 | D20 => W118 | D21 => W116 | D22 => W114 | D23 => W112 | D24 => W110 | D25 => W108 | D26 => W106 | D27 => W104 | D28 => W102 | D29 => W100 | D30 => W98 | D31 => W96 | D32 => W94 | D33 => W92 | D34 => W90 | D35 => W88 | D36 => W86 | D37 => W84 | D38 => W82 | D39 => W80 | D40 => W78 | D41 => W76 | D42 => W74 | D43 => W72 | D44 => W70 | D45 => W68 | D46 => W66 | D47 => W64 | D48 => W190 | D49 => W188 | D50 => W186 | D51 => W184 | D52 => W182 | D53 => W180 | D54 => W178 | D55 => W176 | D56 => W174 | D57 => W172 | D58 => W170 | D59 => W168 | D60 => W166 | D61 => W164 | D62 => W162 | D63 => W160 end
    | D32 => match b with D0 => W31 | D1 => W29 | D2 => W27 | D3 => W25 | D4 => W23 | D5 => W21 | D6 => W19 | D7 => W17 | D8 => W15 | D9 => W13 | D10 => W11 | D11 => W9 | D12 => W7 | D13 => W5 | D14 => W3 | D15 => W1 | D16 => W127 | D17 => W125 | D18 => W123 | D19 => W121 | D20 => W119 | D21 => W117 | D22 => W115 | D23 => W113 | D24 => W111 | D25 => W109 | D26 => W107 | D27 => W105 | D28 => W103 | D29 => W101 | D30 => W99 | D31 => W97 | D32 => W95 | D33 => W93 | D34 => W91 | D35 => W89 | D36 => W87 | D37 => W85 | D38 => W83 | D39 => W81 | D40 => W79 | D41 => W77 | D42 => W75 | D43 => W73 | D44 => W71 | D45 => W69 | D46 => W67 | D47 => W65 | D48 => W191 | D49 => W189 | D50 => W187 | D51 => W185 | D52 => W183 | D53 => W181 | D54 => W179 | D55 => W177 | D56 => W175 | D57 => W173 | D58 => W171 | D59 => W169 | D60 => W167 | D61 => W165 | D62 => W163 | D63 => W161 end
    | D33 => match b with D0 => W32 | D1 => W30 | D2 => W28 | D3 => W26 | D4 => W24 | D5 => W22 | D6 => W20 | D7 => W18 | D8 => W16 | D9 => W14 | D10 => W12 | D11 => W10 | D12 => W8 | D13 => W6 | D14 => W4 | D15 => W2 | D16 => W0 | D17 => W126 | D18 => W124 | D19 => W122 | D20 => W120 | D21 => W118 | D22 => W116 | D23 => W114 | D24 => W112 | D25 => W110 | D26 => W108 | D27 => W106 | D28 => W104 | D29 => W102 | D30 => W100 | D31 => W98 | D32 => W96 | D33 => W94 | D34 => W92 | D35 => W90 | D36 => W88 | D37 => W86 | D38 => W84 | D39 => W82 | D40 => W80 | D41 => W78 | D42 => W76 | D43 => W74 | D44 => W72 | D45 => W70 | D46 => W68 | D47 => W66 | D48 => W64 | D49 => W190 | D50 => W188 | D51 => W186 | D52 => W184 | D53 => W182 | D54 => W180 | D55 => W178 | D56 => W176 | D57 => W174 | D58 => W172 | D59 => W170 | D60 => W168 | D61 => W166 | D62 => W164 | D63 => W162 end
    | D34 => match b with D0 => W33 | D1 => W31 | D2 => W29 | D3 => W27 | D4 => W25 | D5 => W23 | D6 => W21 | D7 => W19 | D8 => W17 | D9 => W15 | D10 => W13 | D11 => W11 | D12 => W9 | D13 => W7 | D14 => W5 | D15 => W3 | D16 => W1 | D17 => W127 | D18 => W125 | D19 => W123 | D20 => W121 | D21 => W119 | D22 => W117 | D23 => W115 | D24 => W113 | D25 => W111 | D26 => W109 | D27 => W107 | D28 => W105 | D29 => W103 | D30 => W101 | D31 => W99 | D32 => W97 | D33 => W95 | D34 => W93 | D35 => W91 | D36 => W89 | D37 => W87 | D38 => W85 | D39 => W83 | D40 => W81 | D41 => W79 | D42 => W77 | D43 => W75 | D44 => W73 | D45 => W71 | D46 => W69 | D47 => W67 | D48 => W65 | D49 => W191 | D50 => W189 | D51 => W187 | D52 => W185 | D53 => W183 | D54 => W181 | D55 => W179 | D56 => W177 | D57 => W175 | D58 => W173 | D59 => W171 | D60 => W169 | D61 => W167 | D62 => W165 | D63 => W163 end
    | D35 => match b with D0 => W34 | D1 => W32 | D2 => W30 | D3 => W28 | D4 => W26 | D5 => W24 | D6 => W22 | D7 => W20 | D8 => W18 | D9 => W16 | D10 => W14 | D11 => W12 | D12 => W10 | D13 => W8 | D14 => W6 | D15 => W4 | D16 => W2 | D17 => W0 | D18 => W126 | D19 => W124 | D20 => W122 | D21 => W120 | D22 => W118 | D23 => W116 | D24 => W114 | D25 => W112 | D26 => W110 | D27 => W108 | D28 => W106 | D29 => W104 | D30 => W102 | D31 => W100 | D32 => W98 | D33 => W96 | D34 => W94 | D35 => W92 | D36 => W90 | D37 => W88 | D38 => W86 | D39 => W84 | D40 => W82 | D41 => W80 | D42 => W78 | D43 => W76 | D44 => W74 | D45 => W72 | D46 => W70 | D47 => W68 | D48 => W66 | D49 => W64 | D50 => W190 | D51 => W188 | D52 => W186 | D53 => W184 | D54 => W182 | D55 => W180 | D56 => W178 | D57 => W176 | D58 => W174 | D59 => W172 | D60 => W170 | D61 => W168 | D62 => W166 | D63 => W164 end
    | D36 => match b with D0 => W35 | D1 => W33 | D2 => W31 | D3 => W29 | D4 => W27 | D5 => W25 | D6 => W23 | D7 => W21 | D8 => W19 | D9 => W17 | D10 => W15 | D11 => W13 | D12 => W11 | D13 => W9 | D14 => W7 | D15 => W5 | D16 => W3 | D17 => W1 | D18 => W127 | D19 => W125 | D20 => W123 | D21 => W121 | D22 => W119 | D23 => W117 | D24 => W115 | D25 => W113 | D26 => W111 | D27 => W109 | D28 => W107 | D29 => W105 | D30 => W103 | D31 => W101 | D32 => W99 | D33 => W97 | D34 => W95 | D35 => W93 | D36 => W91 | D37 => W89 | D38 => W87 | D39 => W85 | D40 => W83 | D41 => W81 | D42 => W79 | D43 => W77 | D44 => W75 | D45 => W73 | D46 => W71 | D47 => W69 | D48 => W67 | D49 => W65 | D50 => W191 | D51 => W189 | D52 => W187 | D53 => W185 | D54 => W183 | D55 => W181 | D56 => W179 | D57 => W177 | D58 => W175 | D59 => W173 | D60 => W171 | D61 => W169 | D62 => W167 | D63 => W165 end
    | D37 => match b with D0 => W36 | D1 => W34 | D2 => W32 | D3 => W30 | D4 => W28 | D5 => W26 | D6 => W24 | D7 => W22 | D8 => W20 | D9 => W18 | D10 => W16 | D11 => W14 | D12 => W12 | D13 => W10 | D14 => W8 | D15 => W6 | D16 => W4 | D17 => W2 | D18 => W0 | D19 => W126 | D20 => W124 | D21 => W122 | D22 => W120 | D23 => W118 | D24 => W116 | D25 => W114 | D26 => W112 | D27 => W110 | D28 => W108 | D29 => W106 | D30 => W104 | D31 => W102 | D32 => W100 | D33 => W98 | D34 => W96 | D35 => W94 | D36 => W92 | D37 => W90 | D38 => W88 | D39 => W86 | D40 => W84 | D41 => W82 | D42 => W80 | D43 => W78 | D44 => W76 | D45 => W74 | D46 => W72 | D47 => W70 | D48 => W68 | D49 => W66 | D50 => W64 | D51 => W190 | D52 => W188 | D53 => W186 | D54 => W184 | D55 => W182 | D56 => W180 | D57 => W178 | D58 => W176 | D59 => W174 | D60 => W172 | D61 => W170 | D62 => W168 | D63 => W166 end
    | D38 => match b with D0 => W37 | D1 => W35 | D2 => W33 | D3 => W31 | D4 => W29 | D5 => W27 | D6 => W25 | D7 => W23 | D8 => W21 | D9 => W19 | D10 => W17 | D11 => W15 | D12 => W13 | D13 => W11 | D14 => W9 | D15 => W7 | D16 => W5 | D17 => W3 | D18 => W1 | D19 => W127 | D20 => W125 | D21 => W123 | D22 => W121 | D23 => W119 | D24 => W117 | D25 => W115 | D26 => W113 | D27 => W111 | D28 => W109 | D29 => W107 | D30 => W105 | D31 => W103 | D32 => W101 | D33 => W99 | D34 => W97 | D35 => W95 | D36 => W93 | D37 => W91 | D38 => W89 | D39 => W87 | D40 => W85 | D41 => W83 | D42 => W81 | D43 => W79 | D44 => W77 | D45 => W75 | D46 => W73 | D47 => W71 | D48 => W69 | D49 => W67 | D50 => W65 | D51 => W191 | D52 => W189 | D53 => W187 | D54 => W185 | D55 => W183 | D56 => W181 | D57 => W179 | D58 => W177 | D59 => W175 | D60 => W173 | D61 => W171 | D62 => W169 | D63 => W167 end
    | D39 => match b with D0 => W38 | D1 => W36 | D2 => W34 | D3 => W32 | D4 => W30 | D5 => W28 | D6 => W26 | D7 => W24 | D8 => W22 | D9 => W20 | D10 => W18 | D11 => W16 | D12 => W14 | D13 => W12 | D14 => W10 | D15 => W8 | D16 => W6 | D17 => W4 | D18 => W2 | D19 => W0 | D20 => W126 | D21 => W124 | D22 => W122 | D23 => W120 | D24 => W118 | D25 => W116 | D26 => W114 | D27 => W112 | D28 => W110 | D29 => W108 | D30 => W106 | D31 => W104 | D32 => W102 | D33 => W100 | D34 => W98 | D35 => W96 | D36 => W94 | D37 => W92 | D38 => W90 | D39 => W88 | D40 => W86 | D41 => W84 | D42 => W82 | D43 => W80 | D44 => W78 | D45 => W76 | D46 => W74 | D47 => W72 | D48 => W70 | D49 => W68 | D50 => W66 | D51 => W64 | D52 => W190 | D53 => W188 | D54 => W186 | D55 => W184 | D56 => W182 | D57 => W180 | D58 => W178 | D59 => W176 | D60 => W174 | D61 => W172 | D62 => W170 | D63 => W168 end
    | D40 => match b with D0 => W39 | D1 => W37 | D2 => W35 | D3 => W33 | D4 => W31 | D5 => W29 | D6 => W27 | D7 => W25 | D8 => W23 | D9 => W21 | D10 => W19 | D11 => W17 | D12 => W15 | D13 => W13 | D14 => W11 | D15 => W9 | D16 => W7 | D17 => W5 | D18 => W3 | D19 => W1 | D20 => W127 | D21 => W125 | D22 => W123 | D23 => W121 | D24 => W119 | D25 => W117 | D26 => W115 | D27 => W113 | D28 => W111 | D29 => W109 | D30 => W107 | D31 => W105 | D32 => W103 | D33 => W101 | D34 => W99 | D35 => W97 | D36 => W95 | D37 => W93 | D38 => W91 | D39 => W89 | D40 => W87 | D41 => W85 | D42 => W83 | D43 => W81 | D44 => W79 | D45 => W77 | D46 => W75 | D47 => W73 | D48 => W71 | D49 => W69 | D50 => W67 | D51 => W65 | D52 => W191 | D53 => W189 | D54 => W187 | D55 => W185 | D56 => W183 | D57 => W181 | D58 => W179 | D59 => W177 | D60 => W175 | D61 => W173 | D62 => W171 | D63 => W169 end
    | D41 => match b with D0 => W40 | D1 => W38 | D2 => W36 | D3 => W34 | D4 => W32 | D5 => W30 | D6 => W28 | D7 => W26 | D8 => W24 | D9 => W22 | D10 => W20 | D11 => W18 | D12 => W16 | D13 => W14 | D14 => W12 | D15 => W10 | D16 => W8 | D17 => W6 | D18 => W4 | D19 => W2 | D20 => W0 | D21 => W126 | D22 => W124 | D23 => W122 | D24 => W120 | D25 => W118 | D26 => W116 | D27 => W114 | D28 => W112 | D29 => W110 | D30 => W108 | D31 => W106 | D32 => W104 | D33 => W102 | D34 => W100 | D35 => W98 | D36 => W96 | D37 => W94 | D38 => W92 | D39 => W90 | D40 => W88 | D41 => W86 | D42 => W84 | D43 => W82 | D44 => W80 | D45 => W78 | D46 => W76 | D47 => W74 | D48 => W72 | D49 => W70 | D50 => W68 | D51 => W66 | D52 => W64 | D53 => W190 | D54 => W188 | D55 => W186 | D56 => W184 | D57 => W182 | D58 => W180 | D59 => W178 | D60 => W176 | D61 => W174 | D62 => W172 | D63 => W170 end
    | D42 => match b with D0 => W41 | D1 => W39 | D2 => W37 | D3 => W35 | D4 => W33 | D5 => W31 | D6 => W29 | D7 => W27 | D8 => W25 | D9 => W23 | D10 => W21 | D11 => W19 | D12 => W17 | D13 => W15 | D14 => W13 | D15 => W11 | D16 => W9 | D17 => W7 | D18 => W5 | D19 => W3 | D20 => W1 | D21 => W127 | D22 => W125 | D23 => W123 | D24 => W121 | D25 => W119 | D26 => W117 | D27 => W115 | D28 => W113 | D29 => W111 | D30 => W109 | D31 => W107 | D32 => W105 | D33 => W103 | D34 => W101 | D35 => W99 | D36 => W97 | D37 => W95 | D38 => W93 | D39 => W91 | D40 => W89 | D41 => W87 | D42 => W85 | D43 => W83 | D44 => W81 | D45 => W79 | D46 => W77 | D47 => W75 | D48 => W73 | D49 => W71 | D50 => W69 | D51 => W67 | D52 => W65 | D53 => W191 | D54 => W189 | D55 => W187 | D56 => W185 | D57 => W183 | D58 => W181 | D59 => W179 | D60 => W177 | D61 => W175 | D62 => W173 | D63 => W171 end
    | D43 => match b with D0 => W42 | D1 => W40 | D2 => W38 | D3 => W36 | D4 => W34 | D5 => W32 | D6 => W30 | D7 => W28 | D8 => W26 | D9 => W24 | D10 => W22 | D11 => W20 | D12 => W18 | D13 => W16 | D14 => W14 | D15 => W12 | D16 => W10 | D17 => W8 | D18 => W6 | D19 => W4 | D20 => W2 | D21 => W0 | D22 => W126 | D23 => W124 | D24 => W122 | D25 => W120 | D26 => W118 | D27 => W116 | D28 => W114 | D29 => W112 | D30 => W110 | D31 => W108 | D32 => W106 | D33 => W104 | D34 => W102 | D35 => W100 | D36 => W98 | D37 => W96 | D38 => W94 | D39 => W92 | D40 => W90 | D41 => W88 | D42 => W86 | D43 => W84 | D44 => W82 | D45 => W80 | D46 => W78 | D47 => W76 | D48 => W74 | D49 => W72 | D50 => W70 | D51 => W68 | D52 => W66 | D53 => W64 | D54 => W190 | D55 => W188 | D56 => W186 | D57 => W184 | D58 => W182 | D59 => W180 | D60 => W178 | D61 => W176 | D62 => W174 | D63 => W172 end
    | D44 => match b with D0 => W43 | D1 => W41 | D2 => W39 | D3 => W37 | D4 => W35 | D5 => W33 | D6 => W31 | D7 => W29 | D8 => W27 | D9 => W25 | D10 => W23 | D11 => W21 | D12 => W19 | D13 => W17 | D14 => W15 | D15 => W13 | D16 => W11 | D17 => W9 | D18 => W7 | D19 => W5 | D20 => W3 | D21 => W1 | D22 => W127 | D23 => W125 | D24 => W123 | D25 => W121 | D26 => W119 | D27 => W117 | D28 => W115 | D29 => W113 | D30 => W111 | D31 => W109 | D32 => W107 | D33 => W105 | D34 => W103 | D35 => W101 | D36 => W99 | D37 => W97 | D38 => W95 | D39 => W93 | D40 => W91 | D41 => W89 | D42 => W87 | D43 => W85 | D44 => W83 | D45 => W81 | D46 => W79 | D47 => W77 | D48 => W75 | D49 => W73 | D50 => W71 | D51 => W69 | D52 => W67 | D53 => W65 | D54 => W191 | D55 => W189 | D56 => W187 | D57 => W185 | D58 => W183 | D59 => W181 | D60 => W179 | D61 => W177 | D62 => W175 | D63 => W173 end
    | D45 => match b with D0 => W44 | D1 => W42 | D2 => W40 | D3 => W38 | D4 => W36 | D5 => W34 | D6 => W32 | D7 => W30 | D8 => W28 | D9 => W26 | D10 => W24 | D11 => W22 | D12 => W20 | D13 => W18 | D14 => W16 | D15 => W14 | D16 => W12 | D17 => W10 | D18 => W8 | D19 => W6 | D20 => W4 | D21 => W2 | D22 => W0 | D23 => W126 | D24 => W124 | D25 => W122 | D26 => W120 | D27 => W118 | D28 => W116 | D29 => W114 | D30 => W112 | D31 => W110 | D32 => W108 | D33 => W106 | D34 => W104 | D35 => W102 | D36 => W100 | D37 => W98 | D38 => W96 | D39 => W94 | D40 => W92 | D41 => W90 | D42 => W88 | D43 => W86 | D44 => W84 | D45 => W82 | D46 => W80 | D47 => W78 | D48 => W76 | D49 => W74 | D50 => W72 | D51 => W70 | D52 => W68 | D53 => W66 | D54 => W64 | D55 => W190 | D56 => W188 | D57 => W186 | D58 => W184 | D59 => W182 | D60 => W180 | D61 => W178 | D62 => W176 | D63 => W174 end
    | D46 => match b with D0 => W45 | D1 => W43 | D2 => W41 | D3 => W39 | D4 => W37 | D5 => W35 | D6 => W33 | D7 => W31 | D8 => W29 | D9 => W27 | D10 => W25 | D11 => W23 | D12 => W21 | D13 => W19 | D14 => W17 | D15 => W15 | D16 => W13 | D17 => W11 | D18 => W9 | D19 => W7 | D20 => W5 | D21 => W3 | D22 => W1 | D23 => W127 | D24 => W125 | D25 => W123 | D26 => W121 | D27 => W119 | D28 => W117 | D29 => W115 | D30 => W113 | D31 => W111 | D32 => W109 | D33 => W107 | D34 => W105 | D35 => W103 | D36 => W101 | D37 => W99 | D38 => W97 | D39 => W95 | D40 => W93 | D41 => W91 | D42 => W89 | D43 => W87 | D44 => W85 | D45 => W83 | D46 => W81 | D47 => W79 | D48 => W77 | D49 => W75 | D50 => W73 | D51 => W71 | D52 => W69 | D53 => W67 | D54 => W65 | D55 => W191 | D56 => W189 | D57 => W187 | D58 => W185 | D59 => W183 | D60 => W181 | D61 => W179 | D62 => W177 | D63 => W175 end
    | D47 => match b with D0 => W46 | D1 => W44 | D2 => W42 | D3 => W40 | D4 => W38 | D5 => W36 | D6 => W34 | D7 => W32 | D8 => W30 | D9 => W28 | D10 => W26 | D11 => W24 | D12 => W22 | D13 => W20 | D14 => W18 | D15 => W16 | D16 => W14 | D17 => W12 | D18 => W10 | D19 => W8 | D20 => W6 | D21 => W4 | D22 => W2 | D23 => W0 | D24 => W126 | D25 => W124 | D26 => W122 | D27 => W120 | D28 => W118 | D29 => W116 | D30 => W114 | D31 => W112 | D32 => W110 | D33 => W108 | D34 => W106 | D35 => W104 | D36 => W102 | D37 => W100 | D38 => W98 | D39 => W96 | D40 => W94 | D41 => W92 | D42 => W90 | D43 => W88 | D44 => W86 | D45 => W84 | D46 => W82 | D47 => W80 | D48 => W78 | D49 => W76 | D50 => W74 | D51 => W72 | D52 => W70 | D53 => W68 | D54 => W66 | D55 => W64 | D56 => W190 | D57 => W188 | D58 => W186 | D59 => W184 | D60 => W182 | D61 => W180 | D62 => W178 | D63 => W176 end
    | D48 => match b with D0 => W47 | D1 => W45 | D2 => W43 | D3 => W41 | D4 => W39 | D5 => W37 | D6 => W35 | D7 => W33 | D8 => W31 | D9 => W29 | D10 => W27 | D11 => W25 | D12 => W23 | D13 => W21 | D14 => W19 | D15 => W17 | D16 => W15 | D17 => W13 | D18 => W11 | D19 => W9 | D20 => W7 | D21 => W5 | D22 => W3 | D23 => W1 | D24 => W127 | D25 => W125 | D26 => W123 | D27 => W121 | D28 => W119 | D29 => W117 | D30 => W115 | D31 => W113 | D32 => W111 | D33 => W109 | D34 => W107 | D35 => W105 | D36 => W103 | D37 => W101 | D38 => W99 | D39 => W97 | D40 => W95 | D41 => W93 | D42 => W91 | D43 => W89 | D44 => W87 | D45 => W85 | D46 => W83 | D47 => W81 | D48 => W79 | D49 => W77 | D50 => W75 | D51 => W73 | D52 => W71 | D53 => W69 | D54 => W67 | D55 => W65 | D56 => W191 | D57 => W189 | D58 => W187 | D59 => W185 | D60 => W183 | D61 => W181 | D62 => W179 | D63 => W177 end
    | D49 => match b with D0 => W48 | D1 => W46 | D2 => W44 | D3 => W42 | D4 => W40 | D5 => W38 | D6 => W36 | D7 => W34 | D8 => W32 | D9 => W30 | D10 => W28 | D11 => W26 | D12 => W24 | D13 => W22 | D14 => W20 | D15 => W18 | D16 => W16 | D17 => W14 | D18 => W12 | D19 => W10 | D20 => W8 | D21 => W6 | D22 => W4 | D23 => W2 | D24 => W0 | D25 => W126 | D26 => W124 | D27 => W122 | D28 => W120 | D29 => W118 | D30 => W116 | D31 => W114 | D32 => W112 | D33 => W110 | D34 => W108 | D35 => W106 | D36 => W104 | D37 => W102 | D38 => W100 | D39 => W98 | D40 => W96 | D41 => W94 | D42 => W92 | D43 => W90 | D44 => W88 | D45 => W86 | D46 => W84 | D47 => W82 | D48 => W80 | D49 => W78 | D50 => W76 | D51 => W74 | D52 => W72 | D53 => W70 | D54 => W68 | D55 => W66 | D56 => W64 | D57 => W190 | D58 => W188 | D59 => W186 | D60 => W184 | D61 => W182 | D62 => W180 | D63 => W178 end
    | D50 => match b with D0 => W49 | D1 => W47 | D2 => W45 | D3 => W43 | D4 => W41 | D5 => W39 | D6 => W37 | D7 => W35 | D8 => W33 | D9 => W31 | D10 => W29 | D11 => W27 | D12 => W25 | D13 => W23 | D14 => W21 | D15 => W19 | D16 => W17 | D17 => W15 | D18 => W13 | D19 => W11 | D20 => W9 | D21 => W7 | D22 => W5 | D23 => W3 | D24 => W1 | D25 => W127 | D26 => W125 | D27 => W123 | D28 => W121 | D29 => W119 | D30 => W117 | D31 => W115 | D32 => W113 | D33 => W111 | D34 => W109 | D35 => W107 | D36 => W105 | D37 => W103 | D38 => W101 | D39 => W99 | D40 => W97 | D41 => W95 | D42 => W93 | D43 => W91 | D44 => W89 | D45 => W87 | D46 => W85 | D47 => W83 | D48 => W81 | D49 => W79 | D50 => W77 | D51 => W75 | D52 => W73 | D53 => W71 | D54 => W69 | D55 => W67 | D56 => W65 | D57 => W191 | D58 => W189 | D59 => W187 | D60 => W185 | D61 => W183 | D62 => W181 | D63 => W179 end
    | D51 => match b with D0 => W50 | D1 => W48 | D2 => W46 | D3 => W44 | D4 => W42 | D5 => W40 | D6 => W38 | D7 => W36 | D8 => W34 | D9 => W32 | D10 => W30 | D11 => W28 | D12 => W26 | D13 => W24 | D14 => W22 | D15 => W20 | D16 => W18 | D17 => W16 | D18 => W14 | D19 => W12 | D20 => W10 | D21 => W8 | D22 => W6 | D23 => W4 | D24 => W2 | D25 => W0 | D26 => W126 | D27 => W124 | D28 => W122 | D29 => W120 | D30 => W118 | D31 => W116 | D32 => W114 | D33 => W112 | D34 => W110 | D35 => W108 | D36 => W106 | D37 => W104 | D38 => W102 | D39 => W100 | D40 => W98 | D41 => W96 | D42 => W94 | D43 => W92 | D44 => W90 | D45 => W88 | D46 => W86 | D47 => W84 | D48 => W82 | D49 => W80 | D50 => W78 | D51 => W76 | D52 => W74 | D53 => W72 | D54 => W70 | D55 => W68 | D56 => W66 | D57 => W64 | D58 => W190 | D59 => W188 | D60 => W186 | D61 => W184 | D62 => W182 | D63 => W180 end
    | D52 => match b with D0 => W51 | D1 => W49 | D2 => W47 | D3 => W45 | D4 => W43 | D5 => W41 | D6 => W39 | D7 => W37 | D8 => W35 | D9 => W33 | D10 => W31 | D11 => W29 | D12 => W27 | D13 => W25 | D14 => W23 | D15 => W21 | D16 => W19 | D17 => W17 | D18 => W15 | D19 => W13 | D20 => W11 | D21 => W9 | D22 => W7 | D23 => W5 | D24 => W3 | D25 => W1 | D26 => W127 | D27 => W125 | D28 => W123 | D29 => W121 | D30 => W119 | D31 => W117 | D32 => W115 | D33 => W113 | D34 => W111 | D35 => W109 | D36 => W107 | D37 => W105 | D38 => W103 | D39 => W101 | D40 => W99 | D41 => W97 | D42 => W95 | D43 => W93 | D44 => W91 | D45 => W89 | D46 => W87 | D47 => W85 | D48 => W83 | D49 => W81 | D50 => W79 | D51 => W77 | D52 => W75 | D53 => W73 | D54 => W71 | D55 => W69 | D56 => W67 | D57 => W65 | D58 => W191 | D59 => W189 | D60 => W187 | D61 => W185 | D62 => W183 | D63 => W181 end
    | D53 => match b with D0 => W52 | D1 => W50 | D2 => W48 | D3 => W46 | D4 => W44 | D5 => W42 | D6 => W40 | D7 => W38 | D8 => W36 | D9 => W34 | D10 => W32 | D11 => W30 | D12 => W28 | D13 => W26 | D14 => W24 | D15 => W22 | D16 => W20 | D17 => W18 | D18 => W16 | D19 => W14 | D20 => W12 | D21 => W10 | D22 => W8 | D23 => W6 | D24 => W4 | D25 => W2 | D26 => W0 | D27 => W126 | D28 => W124 | D29 => W122 | D30 => W120 | D31 => W118 | D32 => W116 | D33 => W114 | D34 => W112 | D35 => W110 | D36 => W108 | D37 => W106 | D38 => W104 | D39 => W102 | D40 => W100 | D41 => W98 | D42 => W96 | D43 => W94 | D44 => W92 | D45 => W90 | D46 => W88 | D47 => W86 | D48 => W84 | D49 => W82 | D50 => W80 | D51 => W78 | D52 => W76 | D53 => W74 | D54 => W72 | D55 => W70 | D56 => W68 | D57 => W66 | D58 => W64 | D59 => W190 | D60 => W188 | D61 => W186 | D62 => W184 | D63 => W182 end
    | D54 => match b with D0 => W53 | D1 => W51 | D2 => W49 | D3 => W47 | D4 => W45 | D5 => W43 | D6 => W41 | D7 => W39 | D8 => W37 | D9 => W35 | D10 => W33 | D11 => W31 | D12 => W29 | D13 => W27 | D14 => W25 | D15 => W23 | D16 => W21 | D17 => W19 | D18 => W17 | D19 => W15 | D20 => W13 | D21 => W11 | D22 => W9 | D23 => W7 | D24 => W5 | D25 => W3 | D26 => W1 | D27 => W127 | D28 => W125 | D29 => W123 | D30 => W121 | D31 => W119 | D32 => W117 | D33 => W115 | D34 => W113 | D35 => W111 | D36 => W109 | D37 => W107 | D38 => W105 | D39 => W103 | D40 => W101 | D41 => W99 | D42 => W97 | D43 => W95 | D44 => W93 | D45 => W91 | D46 => W89 | D47 => W87 | D48 => W85 | D49 => W83 | D50 => W81 | D51 => W79 | D52 => W77 | D53 => W75 | D54 => W73 | D55 => W71 | D56 => W69 | D57 => W67 | D58 => W65 | D59 => W191 | D60 => W189 | D61 => W187 | D62 => W185 | D63 => W183 end
    | D55 => match b with D0 => W54 | D1 => W52 | D2 => W50 | D3 => W48 | D4 => W46 | D5 => W44 | D6 => W42 | D7 => W40 | D8 => W38 | D9 => W36 | D10 => W34 | D11 => W32 | D12 => W30 | D13 => W28 | D14 => W26 | D15 => W24 | D16 => W22 | D17 => W20 | D18 => W18 | D19 => W16 | D20 => W14 | D21 => W12 | D22 => W10 | D23 => W8 | D24 => W6 | D25 => W4 | D26 => W2 | D27 => W0 | D28 => W126 | D29 => W124 | D30 => W122 | D31 => W120 | D32 => W118 | D33 => W116 | D34 => W114 | D35 => W112 | D36 => W110 | D37 => W108 | D38 => W106 | D39 => W104 | D40 => W102 | D41 => W100 | D42 => W98 | D43 => W96 | D44 => W94 | D45 => W92 | D46 => W90 | D47 => W88 | D48 => W86 | D49 => W84 | D50 => W82 | D51 => W80 | D52 => W78 | D53 => W76 | D54 => W74 | D55 => W72 | D56 => W70 | D57 => W68 | D58 => W66 | D59 => W64 | D60 => W190 | D61 => W188 | D62 => W186 | D63 => W184 end
    | D56 => match b with D0 => W55 | D1 => W53 | D2 => W51 | D3 => W49 | D4 => W47 | D5 => W45 | D6 => W43 | D7 => W41 | D8 => W39 | D9 => W37 | D10 => W35 | D11 => W33 | D12 => W31 | D13 => W29 | D14 => W27 | D15 => W25 | D16 => W23 | D17 => W21 | D18 => W19 | D19 => W17 | D20 => W15 | D21 => W13 | D22 => W11 | D23 => W9 | D24 => W7 | D25 => W5 | D26 => W3 | D27 => W1 | D28 => W127 | D29 => W125 | D30 => W123 | D31 => W121 | D32 => W119 | D33 => W117 | D34 => W115 | D35 => W113 | D36 => W111 | D37 => W109 | D38 => W107 | D39 => W105 | D40 => W103 | D41 => W101 | D42 => W99 | D43 => W97 | D44 => W95 | D45 => W93 | D46 => W91 | D47 => W89 | D48 => W87 | D49 => W85 | D50 => W83 | D51 => W81 | D52 => W79 | D53 => W77 | D54 => W75 | D55 => W73 | D56 => W71 | D57 => W69 | D58 => W67 | D59 => W65 | D60 => W191 | D61 => W189 | D62 => W187 | D63 => W185 end
    | D57 => match b with D0 => W56 | D1 => W54 | D2 => W52 | D3 => W50 | D4 => W48 | D5 => W46 | D6 => W44 | D7 => W42 | D8 => W40 | D9 => W38 | D10 => W36 | D11 => W34 | D12 => W32 | D13 => W30 | D14 => W28 | D15 => W26 | D16 => W24 | D17 => W22 | D18 => W20 | D19 => W18 | D20 => W16 | D21 => W14 | D22 => W12 | D23 => W10 | D24 => W8 | D25 => W6 | D26 => W4 | D27 => W2 | D28 => W0 | D29 => W126 | D30 => W124 | D31 => W122 | D32 => W120 | D33 => W118 | D34 => W116 | D35 => W114 | D36 => W112 | D37 => W110 | D38 => W108 | D39 => W106 | D40 => W104 | D41 => W102 | D42 => W100 | D43 => W98 | D44 => W96 | D45 => W94 | D46 => W92 | D47 => W90 | D48 => W88 | D49 => W86 | D50 => W84 | D51 => W82 | D52 => W80 | D53 => W78 | D54 => W76 | D55 => W74 | D56 => W72 | D57 => W70 | D58 => W68 | D59 => W66 | D60 => W64 | D61 => W190 | D62 => W188 | D63 => W186 end
    | D58 => match b with D0 => W57 | D1 => W55 | D2 => W53 | D3 => W51 | D4 => W49 | D5 => W47 | D6 => W45 | D7 => W43 | D8 => W41 | D9 => W39 | D10 => W37 | D11 => W35 | D12 => W33 | D13 => W31 | D14 => W29 | D15 => W27 | D16 => W25 | D17 => W23 | D18 => W21 | D19 => W19 | D20 => W17 | D21 => W15 | D22 => W13 | D23 => W11 | D24 => W9 | D25 => W7 | D26 => W5 | D27 => W3 | D28 => W1 | D29 => W127 | D30 => W125 | D31 => W123 | D32 => W121 | D33 => W119 | D34 => W117 | D35 => W115 | D36 => W113 | D37 => W111 | D38 => W109 | D39 => W107 | D40 => W105 | D41 => W103 | D42 => W101 | D43 => W99 | D44 => W97 | D45 => W95 | D46 => W93 | D47 => W91 | D48 => W89 | D49 => W87 | D50 => W85 | D51 => W83 | D52 => W81 | D53 => W79 | D54 => W77 | D55 => W75 | D56 => W73 | D57 => W71 | D58 => W69 | D59 => W67 | D60 => W65 | D61 => W191 | D62 => W189 | D63 => W187 end
    | D59 => match b with D0 => W58 | D1 => W56 | D2 => W54 | D3 => W52 | D4 => W50 | D5 => W48 | D6 => W46 | D7 => W44 | D8 => W42 | D9 => W40 | D10 => W38 | D11 => W36 | D12 => W34 | D13 => W32 | D14 => W30 | D15 => W28 | D16 => W26 | D17 => W24 | D18 => W22 | D19 => W20 | D20 => W18 | D21 => W16 | D22 => W14 | D23 => W12 | D24 => W10 | D25 => W8 | D26 => W6 | D27 => W4 | D28 => W2 | D29 => W0 | D30 => W126 | D31 => W124 | D32 => W122 | D33 => W120 | D34 => W118 | D35 => W116 | D36 => W114 | D37 => W112 | D38 => W110 | D39 => W108 | D40 => W106 | D41 => W104 | D42 => W102 | D43 => W100 | D44 => W98 | D45 => W96 | D46 => W94 | D47 => W92 | D48 => W90 | D49 => W88 | D50 => W86 | D51 => W84 | D52 => W82 | D53 => W80 | D54 => W78 | D55 => W76 | D56 => W74 | D57 => W72 | D58 => W70 | D59 => W68 | D60 => W66 | D61 => W64 | D62 => W190 | D63 => W188 end
    | D60 => match b with D0 => W59 | D1 => W57 | D2 => W55 | D3 => W53 | D4 => W51 | D5 => W49 | D6 => W47 | D7 => W45 | D8 => W43 | D9 => W41 | D10 => W39 | D11 => W37 | D12 => W35 | D13 => W33 | D14 => W31 | D15 => W29 | D16 => W27 | D17 => W25 | D18 => W23 | D19 => W21 | D20 => W19 | D21 => W17 | D22 => W15 | D23 => W13 | D24 => W11 | D25 => W9 | D26 => W7 | D27 => W5 | D28 => W3 | D29 => W1 | D30 => W127 | D31 => W125 | D32 => W123 | D33 => W121 | D34 => W119 | D35 => W117 | D36 => W115 | D37 => W113 | D38 => W111 | D39 => W109 | D40 => W107 | D41 => W105 | D42 => W103 | D43 => W101 | D44 => W99 | D45 => W97 | D46 => W95 | D47 => W93 | D48 => W91 | D49 => W89 | D50 => W87 | D51 => W85 | D52 => W83 | D53 => W81 | D54 => W79 | D55 => W77 | D56 => W75 | D57 => W73 | D58 => W71 | D59 => W69 | D60 => W67 | D61 => W65 | D62 => W191 | D63 => W189 end
    | D61 => match b with D0 => W60 | D1 => W58 | D2 => W56 | D3 => W54 | D4 => W52 | D5 => W50 | D6 => W48 | D7 => W46 | D8 => W44 | D9 => W42 | D10 => W40 | D11 => W38 | D12 => W36 | D13 => W34 | D14 => W32 | D15 => W30 | D16 => W28 | D17 => W26 | D18 => W24 | D19 => W22 | D20 => W20 | D21 => W18 | D22 => W16 | D23 => W14 | D24 => W12 | D25 => W10 | D26 => W8 | D27 => W6 | D28 => W4 | D29 => W2 | D30 => W0 | D31 => W126 | D32 => W124 | D33 => W122 | D34 => W120 | D35 => W118 | D36 => W116 | D37 => W114 | D38 => W112 | D39 => W110 | D40 => W108 | D41 => W106 | D42 => W104 | D43 => W102 | D44 => W100 | D45 => W98 | D46 => W96 | D47 => W94 | D48 => W92 | D49 => W90 | D50 => W88 | D51 => W86 | D52 => W84 | D53 => W82 | D54 => W80 | D55 => W78 | D56 => W76 | D57 => W74 | D58 => W72 | D59 => W70 | D60 => W68 | D61 => W66 | D62 => W64 | D63 => W190 end
    | D62 => match b with D0 => W61 | D1 => W59 | D2 => W57 | D3 => W55 | D4 => W53 | D5 => W51 | D6 => W49 | D7 => W47 | D8 => W45 | D9 => W43 | D10 => W41 | D11 => W39 | D12 => W37 | D13 => W35 | D14 => W33 | D15 => W31 | D16 => W29 | D17 => W27 | D18 => W25 | D19 => W23 | D20 => W21 | D21 => W19 | D22 => W17 | D23 => W15 | D24 => W13 | D25 => W11 | D26 => W9 | D27 => W7 | D28 => W5 | D29 => W3 | D30 => W1 | D31 => W127 | D32 => W125 | D33 => W123 | D34 => W121 | D35 => W119 | D36 => W117 | D37 => W115 | D38 => W113 | D39 => W111 | D40 => W109 | D41 => W107 | D42 => W105 | D43 => W103 | D44 => W101 | D45 => W99 | D46 => W97 | D47 => W95 | D48 => W93 | D49 => W91 | D50 => W89 | D51 => W87 | D52 => W85 | D53 => W83 | D54 => W81 | D55 => W79 | D56 => W77 | D57 => W75 | D58 => W73 | D59 => W71 | D60 => W69 | D61 => W67 | D62 => W65 | D63 => W191 end
    | D63 => match b with D0 => W62 | D1 => W60 | D2 => W58 | D3 => W56 | D4 => W54 | D5 => W52 | D6 => W50 | D7 => W48 | D8 => W46 | D9 => W44 | D10 => W42 | D11 => W40 | D12 => W38 | D13 => W36 | D14 => W34 | D15 => W32 | D16 => W30 | D17 => W28 | D18 => W26 | D19 => W24 | D20 => W22 | D21 => W20 | D22 => W18 | D23 => W16 | D24 => W14 | D25 => W12 | D26 => W10 | D27 => W8 | D28 => W6 | D29 => W4 | D30 => W2 | D31 => W0 | D32 => W126 | D33 => W124 | D34 => W122 | D35 => W120 | D36 => W118 | D37 => W116 | D38 => W114 | D39 => W112 | D40 => W110 | D41 => W108 | D42 => W106 | D43 => W104 | D44 => W102 | D45 => W100 | D46 => W98 | D47 => W96 | D48 => W94 | D49 => W92 | D50 => W90 | D51 => W88 | D52 => W86 | D53 => W84 | D54 => W82 | D55 => W80 | D56 => W78 | D57 => W76 | D58 => W74 | D59 => W72 | D60 => W70 | D61 => W68 | D62 => W66 | D63 => W64 end
    end
  | C2 => match a with
    | D0 => match b with D0 => W126 | D1 => W124 | D2 => W122 | D3 => W120 | D4 => W118 | D5 => W116 | D6 => W114 | D7 => W112 | D8 => W110 | D9 => W108 | D10 => W106 | D11 => W104 | D12 => W102 | D13 => W100 | D14 => W98 | D15 => W96 | D16 => W94 | D17 => W92 | D18 => W90 | D19 => W88 | D20 => W86 | D21 => W84 | D22 => W82 | D23 => W80 | D24 => W78 | D25 => W76 | D26 => W74 | D27 => W72 | D28 => W70 | D29 => W68 | D30 => W66 | D31 => W64 | D32 => W190 | D33 => W188 | D34 => W186 | D35 => W184 | D36 => W182 | D37 => W180 | D38 => W178 | D39 => W176 | D40 => W174 | D41 => W172 | D42 => W170 | D43 => W168 | D44 => W166 | D45 => W164 | D46 => W162 | D47 => W160 | D48 => W158 | D49 => W156 | D50 => W154 | D51 => W152 | D52 => W150 | D53 => W148 | D54 => W146 | D55 => W144 | D56 => W142 | D57 => W140 | D58 => W138 | D59 => W136 | D60 => W134 | D61 => W132 | D62 => W130 | D63 => W128 end
    | D1 => match b with D0 => W127 | D1 => W125 | D2 => W123 | D3 => W121 | D4 => W119 | D5 => W117 | D6 => W115 | D7 => W113 | D8 => W111 | D9 => W109 | D10 => W107 | D11 => W105 | D12 => W103 | D13 => W101 | D14 => W99 | D15 => W97 | D16 => W95 | D17 => W93 | D18 => W91 | D19 => W89 | D20 => W87 | D21 => W85 | D22 => W83 | D23 => W81 | D24 => W79 | D25 => W77 | D26 => W75 | D27 => W73 | D28 => W71 | D29 => W69 | D30 => W67 | D31 => W65 | D32 => W191 | D33 => W189 | D34 => W187 | D35 => W185 | D36 => W183 | D37 => W181 | D38 => W179 | D39 => W177 | D40 => W175 | D41 => W173 | D42 => W171 | D43 => W169 | D44 => W167 | D45 => W165 | D46 => W163 | D47 => W161 | D48 => W159 | D49 => W157 | D50 => W155 | D51 => W153 | D52 => W151 | D53 => W149 | D54 => W147 | D55 => W145 | D56 => W143 | D57 => W141 | D58 => W139 | D59 => W137 | D60 => W135 | D61 => W133 | D62 => W131 | D63 => W129 end
    | D2 => match b with D0 => W0 | D1 => W126 | D2 => W124 | D3 => W122 | D4 => W120 | D5 => W118 | D6 => W116 | D7 => W114 | D8 => W112 | D9 => W110 | D10 => W108 | D11 => W106 | D12 => W104 | D13 => W102 | D14 => W100 | D15 => W98 | D16 => W96 | D17 => W94 | D18 => W92 | D19 => W90 | D20 => W88 | D21 => W86 | D22 => W84 | D23 => W82 | D24 => W80 | D25 => W78 | D26 => W76 | D27 => W74 | D28 => W72 | D29 => W70 | D30 => W68 | D31 => W66 | D32 => W64 | D33 => W190 | D34 => W188 | D35 => W186 | D36 => W184 | D37 => W182 | D38 => W180 | D39 => W178 | D40 => W176 | D41 => W174 | D42 => W172 | D43 => W170 | D44 => W168 | D45 => W166 | D46 => W164 | D47 => W162 | D48 => W160 | D49 => W158 | D50 => W156 | D51 => W154 | D52 => W152 | D53 => W150 | D54 => W148 | D55 => W146 | D56 => W144 | D57 => W142 | D58 => W140 | D59 => W138 | D60 => W136 | D61 => W134 | D62 => W132 | D63 => W130 end
    | D3 => match b with D0 => W1 | D1 => W127 | D2 => W125 | D3 => W123 | D4 => W121 | D5 => W119 | D6 => W117 | D7 => W115 | D8 => W113 | D9 => W111 | D10 => W109 | D11 => W107 | D12 => W105 | D13 => W103 | D14 => W101 | D15 => W99 | D16 => W97 | D17 => W95 | D18 => W93 | D19 => W91 | D20 => W89 | D21 => W87 | D22 => W85 | D23 => W83 | D24 => W81 | D25 => W79 | D26 => W77 | D27 => W75 | D28 => W73 | D29 => W71 | D30 => W69 | D31 => W67 | D32 => W65 | D33 => W191 | D34 => W189 | D35 => W187 | D36 => W185 | D37 => W183 | D38 => W181 | D39 => W179 | D40 => W177 | D41 => W175 | D42 => W173 | D43 => W171 | D44 => W169 | D45 => W167 | D46 => W165 | D47 => W163 | D48 => W161 | D49 => W159 | D50 => W157 | D51 => W155 | D52 => W153 | D53 => W151 | D54 => W149 | D55 => W147 | D56 => W145 | D57 => W143 | D58 => W141 | D59 => W139 | D60 => W137 | D61 => W135 | D62 => W133 | D63 => W131 end
    | D4 => match b with D0 => W2 | D1 => W0 | D2 => W126 | D3 => W124 | D4 => W122 | D5 => W120 | D6 => W118 | D7 => W116 | D8 => W114 | D9 => W112 | D10 => W110 | D11 => W108 | D12 => W106 | D13 => W104 | D14 => W102 | D15 => W100 | D16 => W98 | D17 => W96 | D18 => W94 | D19 => W92 | D20 => W90 | D21 => W88 | D22 => W86 | D23 => W84 | D24 => W82 | D25 => W80 | D26 => W78 | D27 => W76 | D28 => W74 | D29 => W72 | D30 => W70 | D31 => W68 | D32 => W66 | D33 => W64 | D34 => W190 | D35 => W188 | D36 => W186 | D37 => W184 | D38 => W182 | D39 => W180 | D40 => W178 | D41 => W176 | D42 => W174 | D43 => W172 | D44 => W170 | D45 => W168 | D46 => W166 | D47 => W164 | D48 => W162 | D49 => W160 | D50 => W158 | D51 => W156 | D52 => W154 | D53 => W152 | D54 => W150 | D55 => W148 | D56 => W146 | D57 => W144 | D58 => W142 | D59 => W140 | D60 => W138 | D61 => W136 | D62 => W134 | D63 => W132 end
    | D5 => match b with D0 => W3 | D1 => W1 | D2 => W127 | D3 => W125 | D4 => W123 | D5 => W121 | D6 => W119 | D7 => W117 | D8 => W115 | D9 => W113 | D10 => W111 | D11 => W109 | D12 => W107 | D13 => W105 | D14 => W103 | D15 => W101 | D16 => W99 | D17 => W97 | D18 => W95 | D19 => W93 | D20 => W91 | D21 => W89 | D22 => W87 | D23 => W85 | D24 => W83 | D25 => W81 | D26 => W79 | D27 => W77 | D28 => W75 | D29 => W73 | D30 => W71 | D31 => W69 | D32 => W67 | D33 => W65 | D34 => W191 | D35 => W189 | D36 => W187 | D37 => W185 | D38 => W183 | D39 => W181 | D40 => W179 | D41 => W177 | D42 => W175 | D43 => W173 | D44 => W171 | D45 => W169 | D46 => W167 | D47 => W165 | D48 => W163 | D49 => W161 | D50 => W159 | D51 => W157 | D52 => W155 | D53 => W153 | D54 => W151 | D55 => W149 | D56 => W147 | D57 => W145 | D58 => W143 | D59 => W141 | D60 => W139 | D61 => W137 | D62 => W135 | D63 => W133 end
    | D6 => match b with D0 => W4 | D1 => W2 | D2 => W0 | D3 => W126 | D4 => W124 | D5 => W122 | D6 => W120 | D7 => W118 | D8 => W116 | D9 => W114 | D10 => W112 | D11 => W110 | D12 => W108 | D13 => W106 | D14 => W104 | D15 => W102 | D16 => W100 | D17 => W98 | D18 => W96 | D19 => W94 | D20 => W92 | D21 => W90 | D22 => W88 | D23 => W86 | D24 => W84 | D25 => W82 | D26 => W80 | D27 => W78 | D28 => W76 | D29 => W74 | D30 => W72 | D31 => W70 | D32 => W68 | D33 => W66 | D34 => W64 | D35 => W190 | D36 => W188 | D37 => W186 | D38 => W184 | D39 => W182 | D40 => W180 | D41 => W178 | D42 => W176 | D43 => W174 | D44 => W172 | D45 => W170 | D46 => W168 | D47 => W166 | D48 => W164 | D49 => W162 | D50 => W160 | D51 => W158 | D52 => W156 | D53 => W154 | D54 => W152 | D55 => W150 | D56 => W148 | D57 => W146 | D58 => W144 | D59 => W142 | D60 => W140 | D61 => W138 | D62 => W136 | D63 => W134 end
    | D7 => match b with D0 => W5 | D1 => W3 | D2 => W1 | D3 => W127 | D4 => W125 | D5 => W123 | D6 => W121 | D7 => W119 | D8 => W117 | D9 => W115 | D10 => W113 | D11 => W111 | D12 => W109 | D13 => W107 | D14 => W105 | D15 => W103 | D16 => W101 | D17 => W99 | D18 => W97 | D19 => W95 | D20 => W93 | D21 => W91 | D22 => W89 | D23 => W87 | D24 => W85 | D25 => W83 | D26 => W81 | D27 => W79 | D28 => W77 | D29 => W75 | D30 => W73 | D31 => W71 | D32 => W69 | D33 => W67 | D34 => W65 | D35 => W191 | D36 => W189 | D37 => W187 | D38 => W185 | D39 => W183 | D40 => W181 | D41 => W179 | D42 => W177 | D43 => W175 | D44 => W173 | D45 => W171 | D46 => W169 | D47 => W167 | D48 => W165 | D49 => W163 | D50 => W161 | D51 => W159 | D52 => W157 | D53 => W155 | D54 => W153 | D55 => W151 | D56 => W149 | D57 => W147 | D58 => W145 | D59 => W143 | D60 => W141 | D61 => W139 | D62 => W137 | D63 => W135 end
    | D8 => match b with D0 => W6 | D1 => W4 | D2 => W2 | D3 => W0 | D4 => W126 | D5 => W124 | D6 => W122 | D7 => W120 | D8 => W118 | D9 => W116 | D10 => W114 | D11 => W112 | D12 => W110 | D13 => W108 | D14 => W106 | D15 => W104 | D16 => W102 | D17 => W100 | D18 => W98 | D19 => W96 | D20 => W94 | D21 => W92 | D22 => W90 | D23 => W88 | D24 => W86 | D25 => W84 | D26 => W82 | D27 => W80 | D28 => W78 | D29 => W76 | D30 => W74 | D31 => W72 | D32 => W70 | D33 => W68 | D34 => W66 | D35 => W64 | D36 => W190 | D37 => W188 | D38 => W186 | D39 => W184 | D40 => W182 | D41 => W180 | D42 => W178 | D43 => W176 | D44 => W174 | D45 => W172 | D46 => W170 | D47 => W168 | D48 => W166 | D49 => W164 | D50 => W162 | D51 => W160 | D52 => W158 | D53 => W156 | D54 => W154 | D55 => W152 | D56 => W150 | D57 => W148 | D58 => W146 | D59 => W144 | D60 => W142 | D61 => W140 | D62 => W138 | D63 => W136 end
    | D9 => match b with D0 => W7 | D1 => W5 | D2 => W3 | D3 => W1 | D4 => W127 | D5 => W125 | D6 => W123 | D7 => W121 | D8 => W119 | D9 => W117 | D10 => W115 | D11 => W113 | D12 => W111 | D13 => W109 | D14 => W107 | D15 => W105 | D16 => W103 | D17 => W101 | D18 => W99 | D19 => W97 | D20 => W95 | D21 => W93 | D22 => W91 | D23 => W89 | D24 => W87 | D25 => W85 | D26 => W83 | D27 => W81 | D28 => W79 | D29 => W77 | D30 => W75 | D31 => W73 | D32 => W71 | D33 => W69 | D34 => W67 | D35 => W65 | D36 => W191 | D37 => W189 | D38 => W187 | D39 => W185 | D40 => W183 | D41 => W181 | D42 => W179 | D43 => W177 | D44 => W175 | D45 => W173 | D46 => W171 | D47 => W169 | D48 => W167 | D49 => W165 | D50 => W163 | D51 => W161 | D52 => W159 | D53 => W157 | D54 => W155 | D55 => W153 | D56 => W151 | D57 => W149 | D58 => W147 | D59 => W145 | D60 => W143 | D61 => W141 | D62 => W139 | D63 => W137 end
    | D10 => match b with D0 => W8 | D1 => W6 | D2 => W4 | D3 => W2 | D4 => W0 | D5 => W126 | D6 => W124 | D7 => W122 | D8 => W120 | D9 => W118 | D10 => W116 | D11 => W114 | D12 => W112 | D13 => W110 | D14 => W108 | D15 => W106 | D16 => W104 | D17 => W102 | D18 => W100 | D19 => W98 | D20 => W96 | D21 => W94 | D22 => W92 | D23 => W90 | D24 => W88 | D25 => W86 | D26 => W84 | D27 => W82 | D28 => W80 | D29 => W78 | D30 => W76 | D31 => W74 | D32 => W72 | D33 => W70 | D34 => W68 | D35 => W66 | D36 => W64 | D37 => W190 | D38 => W188 | D39 => W186 | D40 => W184 | D41 => W182 | D42 => W180 | D43 => W178 | D44 => W176 | D45 => W174 | D46 => W172 | D47 => W170 | D48 => W168 | D49 => W166 | D50 => W164 | D51 => W162 | D52 => W160 | D53 => W158 | D54 => W156 | D55 => W154 | D56 => W152 | D57 => W150 | D58 => W148 | D59 => W146 | D60 => W144 | D61 => W142 | D62 => W140 | D63 => W138 end
    | D11 => match b with D0 => W9 | D1 => W7 | D2 => W5 | D3 => W3 | D4 => W1 | D5 => W127 | D6 => W125 | D7 => W123 | D8 => W121 | D9 => W119 | D10 => W117 | D11 => W115 | D12 => W113 | D13 => W111 | D14 => W109 | D15 => W107 | D16 => W105 | D17 => W103 | D18 => W101 | D19 => W99 | D20 => W97 | D21 => W95 | D22 => W93 | D23 => W91 | D24 => W89 | D25 => W87 | D26 => W85 | D27 => W83 | D28 => W81 | D29 => W79 | D30 => W77 | D31 => W75 | D32 => W73 | D33 => W71 | D34 => W69 | D35 => W67 | D36 => W65 | D37 => W191 | D38 => W189 | D39 => W187 | D40 => W185 | D41 => W183 | D42 => W181 | D43 => W179 | D44 => W177 | D45 => W175 | D46 => W173 | D47 => W171 | D48 => W169 | D49 => W167 | D50 => W165 | D51 => W163 | D52 => W161 | D53 => W159 | D54 => W157 | D55 => W155 | D56 => W153 | D57 => W151 | D58 => W149 | D59 => W147 | D60 => W145 | D61 => W143 | D62 => W141 | D63 => W139 end
    | D12 => match b with D0 => W10 | D1 => W8 | D2 => W6 | D3 => W4 | D4 => W2 | D5 => W0 | D6 => W126 | D7 => W124 | D8 => W122 | D9 => W120 | D10 => W118 | D11 => W116 | D12 => W114 | D13 => W112 | D14 => W110 | D15 => W108 | D16 => W106 | D17 => W104 | D18 => W102 | D19 => W100 | D20 => W98 | D21 => W96 | D22 => W94 | D23 => W92 | D24 => W90 | D25 => W88 | D26 => W86 | D27 => W84 | D28 => W82 | D29 => W80 | D30 => W78 | D31 => W76 | D32 => W74 | D33 => W72 | D34 => W70 | D35 => W68 | D36 => W66 | D37 => W64 | D38 => W190 | D39 => W188 | D40 => W186 | D41 => W184 | D42 => W182 | D43 => W180 | D44 => W178 | D45 => W176 | D46 => W174 | D47 => W172 | D48 => W170 | D49 => W168 | D50 => W166 | D51 => W164 | D52 => W162 | D53 => W160 | D54 => W158 | D55 => W156 | D56 => W154 | D57 => W152 | D58 => W150 | D59 => W148 | D60 => W146 | D61 => W144 | D62 => W142 | D63 => W140 end
    | D13 => match b with D0 => W11 | D1 => W9 | D2 => W7 | D3 => W5 | D4 => W3 | D5 => W1 | D6 => W127 | D7 => W125 | D8 => W123 | D9 => W121 | D10 => W119 | D11 => W117 | D12 => W115 | D13 => W113 | D14 => W111 | D15 => W109 | D16 => W107 | D17 => W105 | D18 => W103 | D19 => W101 | D20 => W99 | D21 => W97 | D22 => W95 | D23 => W93 | D24 => W91 | D25 => W89 | D26 => W87 | D27 => W85 | D28 => W83 | D29 => W81 | D30 => W79 | D31 => W77 | D32 => W75 | D33 => W73 | D34 => W71 | D35 => W69 | D36 => W67 | D37 => W65 | D38 => W191 | D39 => W189 | D40 => W187 | D41 => W185 | D42 => W183 | D43 => W181 | D44 => W179 | D45 => W177 | D46 => W175 | D47 => W173 | D48 => W171 | D49 => W169 | D50 => W167 | D51 => W165 | D52 => W163 | D53 => W161 | D54 => W159 | D55 => W157 | D56 => W155 | D57 => W153 | D58 => W151 | D59 => W149 | D60 => W147 | D61 => W145 | D62 => W143 | D63 => W141 end
    | D14 => match b with D0 => W12 | D1 => W10 | D2 => W8 | D3 => W6 | D4 => W4 | D5 => W2 | D6 => W0 | D7 => W126 | D8 => W124 | D9 => W122 | D10 => W120 | D11 => W118 | D12 => W116 | D13 => W114 | D14 => W112 | D15 => W110 | D16 => W108 | D17 => W106 | D18 => W104 | D19 => W102 | D20 => W100 | D21 => W98 | D22 => W96 | D23 => W94 | D24 => W92 | D25 => W90 | D26 => W88 | D27 => W86 | D28 => W84 | D29 => W82 | D30 => W80 | D31 => W78 | D32 => W76 | D33 => W74 | D34 => W72 | D35 => W70 | D36 => W68 | D37 => W66 | D38 => W64 | D39 => W190 | D40 => W188 | D41 => W186 | D42 => W184 | D43 => W182 | D44 => W180 | D45 => W178 | D46 => W176 | D47 => W174 | D48 => W172 | D49 => W170 | D50 => W168 | D51 => W166 | D52 => W164 | D53 => W162 | D54 => W160 | D55 => W158 | D56 => W156 | D57 => W154 | D58 => W152 | D59 => W150 | D60 => W148 | D61 => W146 | D62 => W144 | D63 => W142 end
    | D15 => match b with D0 => W13 | D1 => W11 | D2 => W9 | D3 => W7 | D4 => W5 | D5 => W3 | D6 => W1 | D7 => W127 | D8 => W125 | D9 => W123 | D10 => W121 | D11 => W119 | D12 => W117 | D13 => W115 | D14 => W113 | D15 => W111 | D16 => W109 | D17 => W107 | D18 => W105 | D19 => W103 | D20 => W101 | D21 => W99 | D22 => W97 | D23 => W95 | D24 => W93 | D25 => W91 | D26 => W89 | D27 => W87 | D28 => W85 | D29 => W83 | D30 => W81 | D31 => W79 | D32 => W77 | D33 => W75 | D34 => W73 | D35 => W71 | D36 => W69 | D37 => W67 | D38 => W65 | D39 => W191 | D40 => W189 | D41 => W187 | D42 => W185 | D43 => W183 | D44 => W181 | D45 => W179 | D46 => W177 | D47 => W175 | D48 => W173 | D49 => W171 | D50 => W169 | D51 => W167 | D52 => W165 | D53 => W163 | D54 => W161 | D55 => W159 | D56 => W157 | D57 => W155 | D58 => W153 | D59 => W151 | D60 => W149 | D61 => W147 | D62 => W145 | D63 => W143 end
    | D16 => match b with D0 => W14 | D1 => W12 | D2 => W10 | D3 => W8 | D4 => W6 | D5 => W4 | D6 => W2 | D7 => W0 | D8 => W126 | D9 => W124 | D10 => W122 | D11 => W120 | D12 => W118 | D13 => W116 | D14 => W114 | D15 => W112 | D16 => W110 | D17 => W108 | D18 => W106 | D19 => W104 | D20 => W102 | D21 => W100 | D22 => W98 | D23 => W96 | D24 => W94 | D25 => W92 | D26 => W90 | D27 => W88 | D28 => W86 | D29 => W84 | D30 => W82 | D31 => W80 | D32 => W78 | D33 => W76 | D34 => W74 | D35 => W72 | D36 => W70 | D37 => W68 | D38 => W66 | D39 => W64 | D40 => W190 | D41 => W188 | D42 => W186 | D43 => W184 | D44 => W182 | D45 => W180 | D46 => W178 | D47 => W176 | D48 => W174 | D49 => W172 | D50 => W170 | D51 => W168 | D52 => W166 | D53 => W164 | D54 => W162 | D55 => W160 | D56 => W158 | D57 => W156 | D58 => W154 | D59 => W152 | D60 => W150 | D61 => W148 | D62 => W146 | D63 => W144 end
    | D17 => match b with D0 => W15 | D1 => W13 | D2 => W11 | D3 => W9 | D4 => W7 | D5 => W5 | D6 => W3 | D7 => W1 | D8 => W127 | D9 => W125 | D10 => W123 | D11 => W121 | D12 => W119 | D13 => W117 | D14 => W115 | D15 => W113 | D16 => W111 | D17 => W109 | D18 => W107 | D19 => W105 | D20 => W103 | D21 => W101 | D22 => W99 | D23 => W97 | D24 => W95 | D25 => W93 | D26 => W91 | D27 => W89 | D28 => W87 | D29 => W85 | D30 => W83 | D31 => W81 | D32 => W79 | D33 => W77 | D34 => W75 | D35 => W73 | D36 => W71 | D37 => W69 | D38 => W67 | D39 => W65 | D40 => W191 | D41 => W189 | D42 => W187 | D43 => W185 | D44 => W183 | D45 => W181 | D46 => W179 | D47 => W177 | D48 => W175 | D49 => W173 | D50 => W171 | D51 => W169 | D52 => W167 | D53 => W165 | D54 => W163 | D55 => W161 | D56 => W159 | D57 => W157 | D58 => W155 | D59 => W153 | D60 => W151 | D61 => W149 | D62 => W147 | D63 => W145 end
    | D18 => match b with D0 => W16 | D1 => W14 | D2 => W12 | D3 => W10 | D4 => W8 | D5 => W6 | D6 => W4 | D7 => W2 | D8 => W0 | D9 => W126 | D10 => W124 | D11 => W122 | D12 => W120 | D13 => W118 | D14 => W116 | D15 => W114 | D16 => W112 | D17 => W110 | D18 => W108 | D19 => W106 | D20 => W104 | D21 => W102 | D22 => W100 | D23 => W98 | D24 => W96 | D25 => W94 | D26 => W92 | D27 => W90 | D28 => W88 | D29 => W86 | D30 => W84 | D31 => W82 | D32 => W80 | D33 => W78 | D34 => W76 | D35 => W74 | D36 => W72 | D37 => W70 | D38 => W68 | D39 => W66 | D40 => W64 | D41 => W190 | D42 => W188 | D43 => W186 | D44 => W184 | D45 => W182 | D46 => W180 | D47 => W178 | D48 => W176 | D49 => W174 | D50 => W172 | D51 => W170 | D52 => W168 | D53 => W166 | D54 => W164 | D55 => W162 | D56 => W160 | D57 => W158 | D58 => W156 | D59 => W154 | D60 => W152 | D61 => W150 | D62 => W148 | D63 => W146 end
    | D19 => match b with D0 => W17 | D1 => W15 | D2 => W13 | D3 => W11 | D4 => W9 | D5 => W7 | D6 => W5 | D7 => W3 | D8 => W1 | D9 => W127 | D10 => W125 | D11 => W123 | D12 => W121 | D13 => W119 | D14 => W117 | D15 => W115 | D16 => W113 | D17 => W111 | D18 => W109 | D19 => W107 | D20 => W105 | D21 => W103 | D22 => W101 | D23 => W99 | D24 => W97 | D25 => W95 | D26 => W93 | D27 => W91 | D28 => W89 | D29 => W87 | D30 => W85 | D31 => W83 | D32 => W81 | D33 => W79 | D34 => W77 | D35 => W75 | D36 => W73 | D37 => W71 | D38 => W69 | D39 => W67 | D40 => W65 | D41 => W191 | D42 => W189 | D43 => W187 | D44 => W185 | D45 => W183 | D46 => W181 | D47 => W179 | D48 => W177 | D49 => W175 | D50 => W173 | D51 => W171 | D52 => W169 | D53 => W167 | D54 => W165 | D55 => W163 | D56 => W161 | D57 => W159 | D58 => W157 | D59 => W155 | D60 => W153 | D61 => W151 | D62 => W149 | D63 => W147 end
    | D20 => match b with D0 => W18 | D1 => W16 | D2 => W14 | D3 => W12 | D4 => W10 | D5 => W8 | D6 => W6 | D7 => W4 | D8 => W2 | D9 => W0 | D10 => W126 | D11 => W124 | D12 => W122 | D13 => W120 | D14 => W118 | D15 => W116 | D16 => W114 | D17 => W112 | D18 => W110 | D19 => W108 | D20 => W106 | D21 => W104 | D22 => W102 | D23 => W100 | D24 => W98 | D25 => W96 | D26 => W94 | D27 => W92 | D28 => W90 | D29 => W88 | D30 => W86 | D31 => W84 | D32 => W82 | D33 => W80 | D34 => W78 | D35 => W76 | D36 => W74 | D37 => W72 | D38 => W70 | D39 => W68 | D40 => W66 | D41 => W64 | D42 => W190 | D43 => W188 | D44 => W186 | D45 => W184 | D46 => W182 | D47 => W180 | D48 => W178 | D49 => W176 | D50 => W174 | D51 => W172 | D52 => W170 | D53 => W168 | D54 => W166 | D55 => W164 | D56 => W162 | D57 => W160 | D58 => W158 | D59 => W156 | D60 => W154 | D61 => W152 | D62 => W150 | D63 => W148 end
    | D21 => match b with D0 => W19 | D1 => W17 | D2 => W15 | D3 => W13 | D4 => W11 | D5 => W9 | D6 => W7 | D7 => W5 | D8 => W3 | D9 => W1 | D10 => W127 | D11 => W125 | D12 => W123 | D13 => W121 | D14 => W119 | D15 => W117 | D16 => W115 | D17 => W113 | D18 => W111 | D19 => W109 | D20 => W107 | D21 => W105 | D22 => W103 | D23 => W101 | D24 => W99 | D25 => W97 | D26 => W95 | D27 => W93 | D28 => W91 | D29 => W89 | D30 => W87 | D31 => W85 | D32 => W83 | D33 => W81 | D34 => W79 | D35 => W77 | D36 => W75 | D37 => W73 | D38 => W71 | D39 => W69 | D40 => W67 | D41 => W65 | D42 => W191 | D43 => W189 | D44 => W187 | D45 => W185 | D46 => W183 | D47 => W181 | D48 => W179 | D49 => W177 | D50 => W175 | D51 => W173 | D52 => W171 | D53 => W169 | D54 => W167 | D55 => W165 | D56 => W163 | D57 => W161 | D58 => W159 | D59 => W157 | D60 => W155 | D61 => W153 | D62 => W151 | D63 => W149 end
    | D22 => match b with D0 => W20 | D1 => W18 | D2 => W16 | D3 => W14 | D4 => W12 | D5 => W10 | D6 => W8 | D7 => W6 | D8 => W4 | D9 => W2 | D10 => W0 | D11 => W126 | D12 => W124 | D13 => W122 | D14 => W120 | D15 => W118 | D16 => W116 | D17 => W114 | D18 => W112 | D19 => W110 | D20 => W108 | D21 => W106 | D22 => W104 | D23 => W102 | D24 => W100 | D25 => W98 | D26 => W96 | D27 => W94 | D28 => W92 | D29 => W90 | D30 => W88 | D31 => W86 | D32 => W84 | D33 => W82 | D34 => W80 | D35 => W78 | D36 => W76 | D37 => W74 | D38 => W72 | D39 => W70 | D40 => W68 | D41 => W66 | D42 => W64 | D43 => W190 | D44 => W188 | D45 => W186 | D46 => W184 | D47 => W182 | D48 => W180 | D49 => W178 | D50 => W176 | D51 => W174 | D52 => W172 | D53 => W170 | D54 => W168 | D55 => W166 | D56 => W164 | D57 => W162 | D58 => W160 | D59 => W158 | D60 => W156 | D61 => W154 | D62 => W152 | D63 => W150 end
    | D23 => match b with D0 => W21 | D1 => W19 | D2 => W17 | D3 => W15 | D4 => W13 | D5 => W11 | D6 => W9 | D7 => W7 | D8 => W5 | D9 => W3 | D10 => W1 | D11 => W127 | D12 => W125 | D13 => W123 | D14 => W121 | D15 => W119 | D16 => W117 | D17 => W115 | D18 => W113 | D19 => W111 | D20 => W109 | D21 => W107 | D22 => W105 | D23 => W103 | D24 => W101 | D25 => W99 | D26 => W97 | D27 => W95 | D28 => W93 | D29 => W91 | D30 => W89 | D31 => W87 | D32 => W85 | D33 => W83 | D34 => W81 | D35 => W79 | D36 => W77 | D37 => W75 | D38 => W73 | D39 => W71 | D40 => W69 | D41 => W67 | D42 => W65 | D43 => W191 | D44 => W189 | D45 => W187 | D46 => W185 | D47 => W183 | D48 => W181 | D49 => W179 | D50 => W177 | D51 => W175 | D52 => W173 | D53 => W171 | D54 => W169 | D55 => W167 | D56 => W165 | D57 => W163 | D58 => W161 | D59 => W159 | D60 => W157 | D61 => W155 | D62 => W153 | D63 => W151 end
    | D24 => match b with D0 => W22 | D1 => W20 | D2 => W18 | D3 => W16 | D4 => W14 | D5 => W12 | D6 => W10 | D7 => W8 | D8 => W6 | D9 => W4 | D10 => W2 | D11 => W0 | D12 => W126 | D13 => W124 | D14 => W122 | D15 => W120 | D16 => W118 | D17 => W116 | D18 => W114 | D19 => W112 | D20 => W110 | D21 => W108 | D22 => W106 | D23 => W104 | D24 => W102 | D25 => W100 | D26 => W98 | D27 => W96 | D28 => W94 | D29 => W92 | D30 => W90 | D31 => W88 | D32 => W86 | D33 => W84 | D34 => W82 | D35 => W80 | D36 => W78 | D37 => W76 | D38 => W74 | D39 => W72 | D40 => W70 | D41 => W68 | D42 => W66 | D43 => W64 | D44 => W190 | D45 => W188 | D46 => W186 | D47 => W184 | D48 => W182 | D49 => W180 | D50 => W178 | D51 => W176 | D52 => W174 | D53 => W172 | D54 => W170 | D55 => W168 | D56 => W166 | D57 => W164 | D58 => W162 | D59 => W160 | D60 => W158 | D61 => W156 | D62 => W154 | D63 => W152 end
    | D25 => match b with D0 => W23 | D1 => W21 | D2 => W19 | D3 => W17 | D4 => W15 | D5 => W13 | D6 => W11 | D7 => W9 | D8 => W7 | D9 => W5 | D10 => W3 | D11 => W1 | D12 => W127 | D13 => W125 | D14 => W123 | D15 => W121 | D16 => W119 | D17 => W117 | D18 => W115 | D19 => W113 | D20 => W111 | D21 => W109 | D22 => W107 | D23 => W105 | D24 => W103 | D25 => W101 | D26 => W99 | D27 => W97 | D28 => W95 | D29 => W93 | D30 => W91 | D31 => W89 | D32 => W87 | D33 => W85 | D34 => W83 | D35 => W81 | D36 => W79 | D37 => W77 | D38 => W75 | D39 => W73 | D40 => W71 | D41 => W69 | D42 => W67 | D43 => W65 | D44 => W191 | D45 => W189 | D46 => W187 | D47 => W185 | D48 => W183 | D49 => W181 | D50 => W179 | D51 => W177 | D52 => W175 | D53 => W173 | D54 => W171 | D55 => W169 | D56 => W167 | D57 => W165 | D58 => W163 | D59 => W161 | D60 => W159 | D61 => W157 | D62 => W155 | D63 => W153 end
    | D26 => match b with D0 => W24 | D1 => W22 | D2 => W20 | D3 => W18 | D4 => W16 | D5 => W14 | D6 => W12 | D7 => W10 | D8 => W8 | D9 => W6 | D10 => W4 | D11 => W2 | D12 => W0 | D13 => W126 | D14 => W124 | D15 => W122 | D16 => W120 | D17 => W118 | D18 => W116 | D19 => W114 | D20 => W112 | D21 => W110 | D22 => W108 | D23 => W106 | D24 => W104 | D25 => W102 | D26 => W100 | D27 => W98 | D28 => W96 | D29 => W94 | D30 => W92 | D31 => W90 | D32 => W88 | D33 => W86 | D34 => W84 | D35 => W82 | D36 => W80 | D37 => W78 | D38 => W76 | D39 => W74 | D40 => W72 | D41 => W70 | D42 => W68 | D43 => W66 | D44 => W64 | D45 => W190 | D46 => W188 | D47 => W186 | D48 => W184 | D49 => W182 | D50 => W180 | D51 => W178 | D52 => W176 | D53 => W174 | D54 => W172 | D55 => W170 | D56 => W168 | D57 => W166 | D58 => W164 | D59 => W162 | D60 => W160 | D61 => W158 | D62 => W156 | D63 => W154 end
    | D27 => match b with D0 => W25 | D1 => W23 | D2 => W21 | D3 => W19 | D4 => W17 | D5 => W15 | D6 => W13 | D7 => W11 | D8 => W9 | D9 => W7 | D10 => W5 | D11 => W3 | D12 => W1 | D13 => W127 | D14 => W125 | D15 => W123 | D16 => W121 | D17 => W119 | D18 => W117 | D19 => W115 | D20 => W113 | D21 => W111 | D22 => W109 | D23 => W107 | D24 => W105 | D25 => W103 | D26 => W101 | D27 => W99 | D28 => W97 | D29 => W95 | D30 => W93 | D31 => W91 | D32 => W89 | D33 => W87 | D34 => W85 | D35 => W83 | D36 => W81 | D37 => W79 | D38 => W77 | D39 => W75 | D40 => W73 | D41 => W71 | D42 => W69 | D43 => W67 | D44 => W65 | D45 => W191 | D46 => W189 | D47 => W187 | D48 => W185 | D49 => W183 | D50 => W181 | D51 => W179 | D52 => W177 | D53 => W175 | D54 => W173 | D55 => W171 | D56 => W169 | D57 => W167 | D58 => W165 | D59 => W163 | D60 => W161 | D61 => W159 | D62 => W157 | D63 => W155 end
    | D28 => match b with D0 => W26 | D1 => W24 | D2 => W22 | D3 => W20 | D4 => W18 | D5 => W16 | D6 => W14 | D7 => W12 | D8 => W10 | D9 => W8 | D10 => W6 | D11 => W4 | D12 => W2 | D13 => W0 | D14 => W126 | D15 => W124 | D16 => W122 | D17 => W120 | D18 => W118 | D19 => W116 | D20 => W114 | D21 => W112 | D22 => W110 | D23 => W108 | D24 => W106 | D25 => W104 | D26 => W102 | D27 => W100 | D28 => W98 | D29 => W96 | D30 => W94 | D31 => W92 | D32 => W90 | D33 => W88 | D34 => W86 | D35 => W84 | D36 => W82 | D37 => W80 | D38 => W78 | D39 => W76 | D40 => W74 | D41 => W72 | D42 => W70 | D43 => W68 | D44 => W66 | D45 => W64 | D46 => W190 | D47 => W188 | D48 => W186 | D49 => W184 | D50 => W182 | D51 => W180 | D52 => W178 | D53 => W176 | D54 => W174 | D55 => W172 | D56 => W170 | D57 => W168 | D58 => W166 | D59 => W164 | D60 => W162 | D61 => W160 | D62 => W158 | D63 => W156 end
    | D29 => match b with D0 => W27 | D1 => W25 | D2 => W23 | D3 => W21 | D4 => W19 | D5 => W17 | D6 => W15 | D7 => W13 | D8 => W11 | D9 => W9 | D10 => W7 | D11 => W5 | D12 => W3 | D13 => W1 | D14 => W127 | D15 => W125 | D16 => W123 | D17 => W121 | D18 => W119 | D19 => W117 | D20 => W115 | D21 => W113 | D22 => W111 | D23 => W109 | D24 => W107 | D25 => W105 | D26 => W103 | D27 => W101 | D28 => W99 | D29 => W97 | D30 => W95 | D31 => W93 | D32 => W91 | D33 => W89 | D34 => W87 | D35 => W85 | D36 => W83 | D37 => W81 | D38 => W79 | D39 => W77 | D40 => W75 | D41 => W73 | D42 => W71 | D43 => W69 | D44 => W67 | D45 => W65 | D46 => W191 | D47 => W189 | D48 => W187 | D49 => W185 | D50 => W183 | D51 => W181 | D52 => W179 | D53 => W177 | D54 => W175 | D55 => W173 | D56 => W171 | D57 => W169 | D58 => W167 | D59 => W165 | D60 => W163 | D61 => W161 | D62 => W159 | D63 => W157 end
    | D30 => match b with D0 => W28 | D1 => W26 | D2 => W24 | D3 => W22 | D4 => W20 | D5 => W18 | D6 => W16 | D7 => W14 | D8 => W12 | D9 => W10 | D10 => W8 | D11 => W6 | D12 => W4 | D13 => W2 | D14 => W0 | D15 => W126 | D16 => W124 | D17 => W122 | D18 => W120 | D19 => W118 | D20 => W116 | D21 => W114 | D22 => W112 | D23 => W110 | D24 => W108 | D25 => W106 | D26 => W104 | D27 => W102 | D28 => W100 | D29 => W98 | D30 => W96 | D31 => W94 | D32 => W92 | D33 => W90 | D34 => W88 | D35 => W86 | D36 => W84 | D37 => W82 | D38 => W80 | D39 => W78 | D40 => W76 | D41 => W74 | D42 => W72 | D43 => W70 | D44 => W68 | D45 => W66 | D46 => W64 | D47 => W190 | D48 => W188 | D49 => W186 | D50 => W184 | D51 => W182 | D52 => W180 | D53 => W178 | D54 => W176 | D55 => W174 | D56 => W172 | D57 => W170 | D58 => W168 | D59 => W166 | D60 => W164 | D61 => W162 | D62 => W160 | D63 => W158 end
    | D31 => match b with D0 => W29 | D1 => W27 | D2 => W25 | D3 => W23 | D4 => W21 | D5 => W19 | D6 => W17 | D7 => W15 | D8 => W13 | D9 => W11 | D10 => W9 | D11 => W7 | D12 => W5 | D13 => W3 | D14 => W1 | D15 => W127 | D16 => W125 | D17 => W123 | D18 => W121 | D19 => W119 | D20 => W117 | D21 => W115 | D22 => W113 | D23 => W111 | D24 => W109 | D25 => W107 | D26 => W105 | D27 => W103 | D28 => W101 | D29 => W99 | D30 => W97 | D31 => W95 | D32 => W93 | D33 => W91 | D34 => W89 | D35 => W87 | D36 => W85 | D37 => W83 | D38 => W81 | D39 => W79 | D40 => W77 | D41 => W75 | D42 => W73 | D43 => W71 | D44 => W69 | D45 => W67 | D46 => W65 | D47 => W191 | D48 => W189 | D49 => W187 | D50 => W185 | D51 => W183 | D52 => W181 | D53 => W179 | D54 => W177 | D55 => W175 | D56 => W173 | D57 => W171 | D58 => W169 | D59 => W167 | D60 => W165 | D61 => W163 | D62 => W161 | D63 => W159 end
    | D32 => match b with D0 => W30 | D1 => W28 | D2 => W26 | D3 => W24 | D4 => W22 | D5 => W20 | D6 => W18 | D7 => W16 | D8 => W14 | D9 => W12 | D10 => W10 | D11 => W8 | D12 => W6 | D13 => W4 | D14 => W2 | D15 => W0 | D16 => W126 | D17 => W124 | D18 => W122 | D19 => W120 | D20 => W118 | D21 => W116 | D22 => W114 | D23 => W112 | D24 => W110 | D25 => W108 | D26 => W106 | D27 => W104 | D28 => W102 | D29 => W100 | D30 => W98 | D31 => W96 | D32 => W94 | D33 => W92 | D34 => W90 | D35 => W88 | D36 => W86 | D37 => W84 | D38 => W82 | D39 => W80 | D40 => W78 | D41 => W76 | D42 => W74 | D43 => W72 | D44 => W70 | D45 => W68 | D46 => W66 | D47 => W64 | D48 => W190 | D49 => W188 | D50 => W186 | D51 => W184 | D52 => W182 | D53 => W180 | D54 => W178 | D55 => W176 | D56 => W174 | D57 => W172 | D58 => W170 | D59 => W168 | D60 => W166 | D61 => W164 | D62 => W162 | D63 => W160 end
    | D33 => match b with D0 => W31 | D1 => W29 | D2 => W27 | D3 => W25 | D4 => W23 | D5 => W21 | D6 => W19 | D7 => W17 | D8 => W15 | D9 => W13 | D10 => W11 | D11 => W9 | D12 => W7 | D13 => W5 | D14 => W3 | D15 => W1 | D16 => W127 | D17 => W125 | D18 => W123 | D19 => W121 | D20 => W119 | D21 => W117 | D22 => W115 | D23 => W113 | D24 => W111 | D25 => W109 | D26 => W107 | D27 => W105 | D28 => W103 | D29 => W101 | D30 => W99 | D31 => W97 | D32 => W95 | D33 => W93 | D34 => W91 | D35 => W89 | D36 => W87 | D37 => W85 | D38 => W83 | D39 => W81 | D40 => W79 | D41 => W77 | D42 => W75 | D43 => W73 | D44 => W71 | D45 => W69 | D46 => W67 | D47 => W65 | D48 => W191 | D49 => W189 | D50 => W187 | D51 => W185 | D52 => W183 | D53 => W181 | D54 => W179 | D55 => W177 | D56 => W175 | D57 => W173 | D58 => W171 | D59 => W169 | D60 => W167 | D61 => W165 | D62 => W163 | D63 => W161 end
    | D34 => match b with D0 => W32 | D1 => W30 | D2 => W28 | D3 => W26 | D4 => W24 | D5 => W22 | D6 => W20 | D7 => W18 | D8 => W16 | D9 => W14 | D10 => W12 | D11 => W10 | D12 => W8 | D13 => W6 | D14 => W4 | D15 => W2 | D16 => W0 | D17 => W126 | D18 => W124 | D19 => W122 | D20 => W120 | D21 => W118 | D22 => W116 | D23 => W114 | D24 => W112 | D25 => W110 | D26 => W108 | D27 => W106 | D28 => W104 | D29 => W102 | D30 => W100 | D31 => W98 | D32 => W96 | D33 => W94 | D34 => W92 | D35 => W90 | D36 => W88 | D37 => W86 | D38 => W84 | D39 => W82 | D40 => W80 | D41 => W78 | D42 => W76 | D43 => W74 | D44 => W72 | D45 => W70 | D46 => W68 | D47 => W66 | D48 => W64 | D49 => W190 | D50 => W188 | D51 => W186 | D52 => W184 | D53 => W182 | D54 => W180 | D55 => W178 | D56 => W176 | D57 => W174 | D58 => W172 | D59 => W170 | D60 => W168 | D61 => W166 | D62 => W164 | D63 => W162 end
    | D35 => match b with D0 => W33 | D1 => W31 | D2 => W29 | D3 => W27 | D4 => W25 | D5 => W23 | D6 => W21 | D7 => W19 | D8 => W17 | D9 => W15 | D10 => W13 | D11 => W11 | D12 => W9 | D13 => W7 | D14 => W5 | D15 => W3 | D16 => W1 | D17 => W127 | D18 => W125 | D19 => W123 | D20 => W121 | D21 => W119 | D22 => W117 | D23 => W115 | D24 => W113 | D25 => W111 | D26 => W109 | D27 => W107 | D28 => W105 | D29 => W103 | D30 => W101 | D31 => W99 | D32 => W97 | D33 => W95 | D34 => W93 | D35 => W91 | D36 => W89 | D37 => W87 | D38 => W85 | D39 => W83 | D40 => W81 | D41 => W79 | D42 => W77 | D43 => W75 | D44 => W73 | D45 => W71 | D46 => W69 | D47 => W67 | D48 => W65 | D49 => W191 | D50 => W189 | D51 => W187 | D52 => W185 | D53 => W183 | D54 => W181 | D55 => W179 | D56 => W177 | D57 => W175 | D58 => W173 | D59 => W171 | D60 => W169 | D61 => W167 | D62 => W165 | D63 => W163 end
    | D36 => match b with D0 => W34 | D1 => W32 | D2 => W30 | D3 => W28 | D4 => W26 | D5 => W24 | D6 => W22 | D7 => W20 | D8 => W18 | D9 => W16 | D10 => W14 | D11 => W12 | D12 => W10 | D13 => W8 | D14 => W6 | D15 => W4 | D16 => W2 | D17 => W0 | D18 => W126 | D19 => W124 | D20 => W122 | D21 => W120 | D22 => W118 | D23 => W116 | D24 => W114 | D25 => W112 | D26 => W110 | D27 => W108 | D28 => W106 | D29 => W104 | D30 => W102 | D31 => W100 | D32 => W98 | D33 => W96 | D34 => W94 | D35 => W92 | D36 => W90 | D37 => W88 | D38 => W86 | D39 => W84 | D40 => W82 | D41 => W80 | D42 => W78 | D43 => W76 | D44 => W74 | D45 => W72 | D46 => W70 | D47 => W68 | D48 => W66 | D49 => W64 | D50 => W190 | D51 => W188 | D52 => W186 | D53 => W184 | D54 => W182 | D55 => W180 | D56 => W178 | D57 => W176 | D58 => W174 | D59 => W172 | D60 => W170 | D61 => W168 | D62 => W166 | D63 => W164 end
    | D37 => match b with D0 => W35 | D1 => W33 | D2 => W31 | D3 => W29 | D4 => W27 | D5 => W25 | D6 => W23 | D7 => W21 | D8 => W19 | D9 => W17 | D10 => W15 | D11 => W13 | D12 => W11 | D13 => W9 | D14 => W7 | D15 => W5 | D16 => W3 | D17 => W1 | D18 => W127 | D19 => W125 | D20 => W123 | D21 => W121 | D22 => W119 | D23 => W117 | D24 => W115 | D25 => W113 | D26 => W111 | D27 => W109 | D28 => W107 | D29 => W105 | D30 => W103 | D31 => W101 | D32 => W99 | D33 => W97 | D34 => W95 | D35 => W93 | D36 => W91 | D37 => W89 | D38 => W87 | D39 => W85 | D40 => W83 | D41 => W81 | D42 => W79 | D43 => W77 | D44 => W75 | D45 => W73 | D46 => W71 | D47 => W69 | D48 => W67 | D49 => W65 | D50 => W191 | D51 => W189 | D52 => W187 | D53 => W185 | D54 => W183 | D55 => W181 | D56 => W179 | D57 => W177 | D58 => W175 | D59 => W173 | D60 => W171 | D61 => W169 | D62 => W167 | D63 => W165 end
    | D38 => match b with D0 => W36 | D1 => W34 | D2 => W32 | D3 => W30 | D4 => W28 | D5 => W26 | D6 => W24 | D7 => W22 | D8 => W20 | D9 => W18 | D10 => W16 | D11 => W14 | D12 => W12 | D13 => W10 | D14 => W8 | D15 => W6 | D16 => W4 | D17 => W2 | D18 => W0 | D19 => W126 | D20 => W124 | D21 => W122 | D22 => W120 | D23 => W118 | D24 => W116 | D25 => W114 | D26 => W112 | D27 => W110 | D28 => W108 | D29 => W106 | D30 => W104 | D31 => W102 | D32 => W100 | D33 => W98 | D34 => W96 | D35 => W94 | D36 => W92 | D37 => W90 | D38 => W88 | D39 => W86 | D40 => W84 | D41 => W82 | D42 => W80 | D43 => W78 | D44 => W76 | D45 => W74 | D46 => W72 | D47 => W70 | D48 => W68 | D49 => W66 | D50 => W64 | D51 => W190 | D52 => W188 | D53 => W186 | D54 => W184 | D55 => W182 | D56 => W180 | D57 => W178 | D58 => W176 | D59 => W174 | D60 => W172 | D61 => W170 | D62 => W168 | D63 => W166 end
    | D39 => match b with D0 => W37 | D1 => W35 | D2 => W33 | D3 => W31 | D4 => W29 | D5 => W27 | D6 => W25 | D7 => W23 | D8 => W21 | D9 => W19 | D10 => W17 | D11 => W15 | D12 => W13 | D13 => W11 | D14 => W9 | D15 => W7 | D16 => W5 | D17 => W3 | D18 => W1 | D19 => W127 | D20 => W125 | D21 => W123 | D22 => W121 | D23 => W119 | D24 => W117 | D25 => W115 | D26 => W113 | D27 => W111 | D28 => W109 | D29 => W107 | D30 => W105 | D31 => W103 | D32 => W101 | D33 => W99 | D34 => W97 | D35 => W95 | D36 => W93 | D37 => W91 | D38 => W89 | D39 => W87 | D40 => W85 | D41 => W83 | D42 => W81 | D43 => W79 | D44 => W77 | D45 => W75 | D46 => W73 | D47 => W71 | D48 => W69 | D49 => W67 | D50 => W65 | D51 => W191 | D52 => W189 | D53 => W187 | D54 => W185 | D55 => W183 | D56 => W181 | D57 => W179 | D58 => W177 | D59 => W175 | D60 => W173 | D61 => W171 | D62 => W169 | D63 => W167 end
    | D40 => match b with D0 => W38 | D1 => W36 | D2 => W34 | D3 => W32 | D4 => W30 | D5 => W28 | D6 => W26 | D7 => W24 | D8 => W22 | D9 => W20 | D10 => W18 | D11 => W16 | D12 => W14 | D13 => W12 | D14 => W10 | D15 => W8 | D16 => W6 | D17 => W4 | D18 => W2 | D19 => W0 | D20 => W126 | D21 => W124 | D22 => W122 | D23 => W120 | D24 => W118 | D25 => W116 | D26 => W114 | D27 => W112 | D28 => W110 | D29 => W108 | D30 => W106 | D31 => W104 | D32 => W102 | D33 => W100 | D34 => W98 | D35 => W96 | D36 => W94 | D37 => W92 | D38 => W90 | D39 => W88 | D40 => W86 | D41 => W84 | D42 => W82 | D43 => W80 | D44 => W78 | D45 => W76 | D46 => W74 | D47 => W72 | D48 => W70 | D49 => W68 | D50 => W66 | D51 => W64 | D52 => W190 | D53 => W188 | D54 => W186 | D55 => W184 | D56 => W182 | D57 => W180 | D58 => W178 | D59 => W176 | D60 => W174 | D61 => W172 | D62 => W170 | D63 => W168 end
    | D41 => match b with D0 => W39 | D1 => W37 | D2 => W35 | D3 => W33 | D4 => W31 | D5 => W29 | D6 => W27 | D7 => W25 | D8 => W23 | D9 => W21 | D10 => W19 | D11 => W17 | D12 => W15 | D13 => W13 | D14 => W11 | D15 => W9 | D16 => W7 | D17 => W5 | D18 => W3 | D19 => W1 | D20 => W127 | D21 => W125 | D22 => W123 | D23 => W121 | D24 => W119 | D25 => W117 | D26 => W115 | D27 => W113 | D28 => W111 | D29 => W109 | D30 => W107 | D31 => W105 | D32 => W103 | D33 => W101 | D34 => W99 | D35 => W97 | D36 => W95 | D37 => W93 | D38 => W91 | D39 => W89 | D40 => W87 | D41 => W85 | D42 => W83 | D43 => W81 | D44 => W79 | D45 => W77 | D46 => W75 | D47 => W73 | D48 => W71 | D49 => W69 | D50 => W67 | D51 => W65 | D52 => W191 | D53 => W189 | D54 => W187 | D55 => W185 | D56 => W183 | D57 => W181 | D58 => W179 | D59 => W177 | D60 => W175 | D61 => W173 | D62 => W171 | D63 => W169 end
    | D42 => match b with D0 => W40 | D1 => W38 | D2 => W36 | D3 => W34 | D4 => W32 | D5 => W30 | D6 => W28 | D7 => W26 | D8 => W24 | D9 => W22 | D10 => W20 | D11 => W18 | D12 => W16 | D13 => W14 | D14 => W12 | D15 => W10 | D16 => W8 | D17 => W6 | D18 => W4 | D19 => W2 | D20 => W0 | D21 => W126 | D22 => W124 | D23 => W122 | D24 => W120 | D25 => W118 | D26 => W116 | D27 => W114 | D28 => W112 | D29 => W110 | D30 => W108 | D31 => W106 | D32 => W104 | D33 => W102 | D34 => W100 | D35 => W98 | D36 => W96 | D37 => W94 | D38 => W92 | D39 => W90 | D40 => W88 | D41 => W86 | D42 => W84 | D43 => W82 | D44 => W80 | D45 => W78 | D46 => W76 | D47 => W74 | D48 => W72 | D49 => W70 | D50 => W68 | D51 => W66 | D52 => W64 | D53 => W190 | D54 => W188 | D55 => W186 | D56 => W184 | D57 => W182 | D58 => W180 | D59 => W178 | D60 => W176 | D61 => W174 | D62 => W172 | D63 => W170 end
    | D43 => match b with D0 => W41 | D1 => W39 | D2 => W37 | D3 => W35 | D4 => W33 | D5 => W31 | D6 => W29 | D7 => W27 | D8 => W25 | D9 => W23 | D10 => W21 | D11 => W19 | D12 => W17 | D13 => W15 | D14 => W13 | D15 => W11 | D16 => W9 | D17 => W7 | D18 => W5 | D19 => W3 | D20 => W1 | D21 => W127 | D22 => W125 | D23 => W123 | D24 => W121 | D25 => W119 | D26 => W117 | D27 => W115 | D28 => W113 | D29 => W111 | D30 => W109 | D31 => W107 | D32 => W105 | D33 => W103 | D34 => W101 | D35 => W99 | D36 => W97 | D37 => W95 | D38 => W93 | D39 => W91 | D40 => W89 | D41 => W87 | D42 => W85 | D43 => W83 | D44 => W81 | D45 => W79 | D46 => W77 | D47 => W75 | D48 => W73 | D49 => W71 | D50 => W69 | D51 => W67 | D52 => W65 | D53 => W191 | D54 => W189 | D55 => W187 | D56 => W185 | D57 => W183 | D58 => W181 | D59 => W179 | D60 => W177 | D61 => W175 | D62 => W173 | D63 => W171 end
    | D44 => match b with D0 => W42 | D1 => W40 | D2 => W38 | D3 => W36 | D4 => W34 | D5 => W32 | D6 => W30 | D7 => W28 | D8 => W26 | D9 => W24 | D10 => W22 | D11 => W20 | D12 => W18 | D13 => W16 | D14 => W14 | D15 => W12 | D16 => W10 | D17 => W8 | D18 => W6 | D19 => W4 | D20 => W2 | D21 => W0 | D22 => W126 | D23 => W124 | D24 => W122 | D25 => W120 | D26 => W118 | D27 => W116 | D28 => W114 | D29 => W112 | D30 => W110 | D31 => W108 | D32 => W106 | D33 => W104 | D34 => W102 | D35 => W100 | D36 => W98 | D37 => W96 | D38 => W94 | D39 => W92 | D40 => W90 | D41 => W88 | D42 => W86 | D43 => W84 | D44 => W82 | D45 => W80 | D46 => W78 | D47 => W76 | D48 => W74 | D49 => W72 | D50 => W70 | D51 => W68 | D52 => W66 | D53 => W64 | D54 => W190 | D55 => W188 | D56 => W186 | D57 => W184 | D58 => W182 | D59 => W180 | D60 => W178 | D61 => W176 | D62 => W174 | D63 => W172 end
    | D45 => match b with D0 => W43 | D1 => W41 | D2 => W39 | D3 => W37 | D4 => W35 | D5 => W33 | D6 => W31 | D7 => W29 | D8 => W27 | D9 => W25 | D10 => W23 | D11 => W21 | D12 => W19 | D13 => W17 | D14 => W15 | D15 => W13 | D16 => W11 | D17 => W9 | D18 => W7 | D19 => W5 | D20 => W3 | D21 => W1 | D22 => W127 | D23 => W125 | D24 => W123 | D25 => W121 | D26 => W119 | D27 => W117 | D28 => W115 | D29 => W113 | D30 => W111 | D31 => W109 | D32 => W107 | D33 => W105 | D34 => W103 | D35 => W101 | D36 => W99 | D37 => W97 | D38 => W95 | D39 => W93 | D40 => W91 | D41 => W89 | D42 => W87 | D43 => W85 | D44 => W83 | D45 => W81 | D46 => W79 | D47 => W77 | D48 => W75 | D49 => W73 | D50 => W71 | D51 => W69 | D52 => W67 | D53 => W65 | D54 => W191 | D55 => W189 | D56 => W187 | D57 => W185 | D58 => W183 | D59 => W181 | D60 => W179 | D61 => W177 | D62 => W175 | D63 => W173 end
    | D46 => match b with D0 => W44 | D1 => W42 | D2 => W40 | D3 => W38 | D4 => W36 | D5 => W34 | D6 => W32 | D7 => W30 | D8 => W28 | D9 => W26 | D10 => W24 | D11 => W22 | D12 => W20 | D13 => W18 | D14 => W16 | D15 => W14 | D16 => W12 | D17 => W10 | D18 => W8 | D19 => W6 | D20 => W4 | D21 => W2 | D22 => W0 | D23 => W126 | D24 => W124 | D25 => W122 | D26 => W120 | D27 => W118 | D28 => W116 | D29 => W114 | D30 => W112 | D31 => W110 | D32 => W108 | D33 => W106 | D34 => W104 | D35 => W102 | D36 => W100 | D37 => W98 | D38 => W96 | D39 => W94 | D40 => W92 | D41 => W90 | D42 => W88 | D43 => W86 | D44 => W84 | D45 => W82 | D46 => W80 | D47 => W78 | D48 => W76 | D49 => W74 | D50 => W72 | D51 => W70 | D52 => W68 | D53 => W66 | D54 => W64 | D55 => W190 | D56 => W188 | D57 => W186 | D58 => W184 | D59 => W182 | D60 => W180 | D61 => W178 | D62 => W176 | D63 => W174 end
    | D47 => match b with D0 => W45 | D1 => W43 | D2 => W41 | D3 => W39 | D4 => W37 | D5 => W35 | D6 => W33 | D7 => W31 | D8 => W29 | D9 => W27 | D10 => W25 | D11 => W23 | D12 => W21 | D13 => W19 | D14 => W17 | D15 => W15 | D16 => W13 | D17 => W11 | D18 => W9 | D19 => W7 | D20 => W5 | D21 => W3 | D22 => W1 | D23 => W127 | D24 => W125 | D25 => W123 | D26 => W121 | D27 => W119 | D28 => W117 | D29 => W115 | D30 => W113 | D31 => W111 | D32 => W109 | D33 => W107 | D34 => W105 | D35 => W103 | D36 => W101 | D37 => W99 | D38 => W97 | D39 => W95 | D40 => W93 | D41 => W91 | D42 => W89 | D43 => W87 | D44 => W85 | D45 => W83 | D46 => W81 | D47 => W79 | D48 => W77 | D49 => W75 | D50 => W73 | D51 => W71 | D52 => W69 | D53 => W67 | D54 => W65 | D55 => W191 | D56 => W189 | D57 => W187 | D58 => W185 | D59 => W183 | D60 => W181 | D61 => W179 | D62 => W177 | D63 => W175 end
    | D48 => match b with D0 => W46 | D1 => W44 | D2 => W42 | D3 => W40 | D4 => W38 | D5 => W36 | D6 => W34 | D7 => W32 | D8 => W30 | D9 => W28 | D10 => W26 | D11 => W24 | D12 => W22 | D13 => W20 | D14 => W18 | D15 => W16 | D16 => W14 | D17 => W12 | D18 => W10 | D19 => W8 | D20 => W6 | D21 => W4 | D22 => W2 | D23 => W0 | D24 => W126 | D25 => W124 | D26 => W122 | D27 => W120 | D28 => W118 | D29 => W116 | D30 => W114 | D31 => W112 | D32 => W110 | D33 => W108 | D34 => W106 | D35 => W104 | D36 => W102 | D37 => W100 | D38 => W98 | D39 => W96 | D40 => W94 | D41 => W92 | D42 => W90 | D43 => W88 | D44 => W86 | D45 => W84 | D46 => W82 | D47 => W80 | D48 => W78 | D49 => W76 | D50 => W74 | D51 => W72 | D52 => W70 | D53 => W68 | D54 => W66 | D55 => W64 | D56 => W190 | D57 => W188 | D58 => W186 | D59 => W184 | D60 => W182 | D61 => W180 | D62 => W178 | D63 => W176 end
    | D49 => match b with D0 => W47 | D1 => W45 | D2 => W43 | D3 => W41 | D4 => W39 | D5 => W37 | D6 => W35 | D7 => W33 | D8 => W31 | D9 => W29 | D10 => W27 | D11 => W25 | D12 => W23 | D13 => W21 | D14 => W19 | D15 => W17 | D16 => W15 | D17 => W13 | D18 => W11 | D19 => W9 | D20 => W7 | D21 => W5 | D22 => W3 | D23 => W1 | D24 => W127 | D25 => W125 | D26 => W123 | D27 => W121 | D28 => W119 | D29 => W117 | D30 => W115 | D31 => W113 | D32 => W111 | D33 => W109 | D34 => W107 | D35 => W105 | D36 => W103 | D37 => W101 | D38 => W99 | D39 => W97 | D40 => W95 | D41 => W93 | D42 => W91 | D43 => W89 | D44 => W87 | D45 => W85 | D46 => W83 | D47 => W81 | D48 => W79 | D49 => W77 | D50 => W75 | D51 => W73 | D52 => W71 | D53 => W69 | D54 => W67 | D55 => W65 | D56 => W191 | D57 => W189 | D58 => W187 | D59 => W185 | D60 => W183 | D61 => W181 | D62 => W179 | D63 => W177 end
    | D50 => match b with D0 => W48 | D1 => W46 | D2 => W44 | D3 => W42 | D4 => W40 | D5 => W38 | D6 => W36 | D7 => W34 | D8 => W32 | D9 => W30 | D10 => W28 | D11 => W26 | D12 => W24 | D13 => W22 | D14 => W20 | D15 => W18 | D16 => W16 | D17 => W14 | D18 => W12 | D19 => W10 | D20 => W8 | D21 => W6 | D22 => W4 | D23 => W2 | D24 => W0 | D25 => W126 | D26 => W124 | D27 => W122 | D28 => W120 | D29 => W118 | D30 => W116 | D31 => W114 | D32 => W112 | D33 => W110 | D34 => W108 | D35 => W106 | D36 => W104 | D37 => W102 | D38 => W100 | D39 => W98 | D40 => W96 | D41 => W94 | D42 => W92 | D43 => W90 | D44 => W88 | D45 => W86 | D46 => W84 | D47 => W82 | D48 => W80 | D49 => W78 | D50 => W76 | D51 => W74 | D52 => W72 | D53 => W70 | D54 => W68 | D55 => W66 | D56 => W64 | D57 => W190 | D58 => W188 | D59 => W186 | D60 => W184 | D61 => W182 | D62 => W180 | D63 => W178 end
    | D51 => match b with D0 => W49 | D1 => W47 | D2 => W45 | D3 => W43 | D4 => W41 | D5 => W39 | D6 => W37 | D7 => W35 | D8 => W33 | D9 => W31 | D10 => W29 | D11 => W27 | D12 => W25 | D13 => W23 | D14 => W21 | D15 => W19 | D16 => W17 | D17 => W15 | D18 => W13 | D19 => W11 | D20 => W9 | D21 => W7 | D22 => W5 | D23 => W3 | D24 => W1 | D25 => W127 | D26 => W125 | D27 => W123 | D28 => W121 | D29 => W119 | D30 => W117 | D31 => W115 | D32 => W113 | D33 => W111 | D34 => W109 | D35 => W107 | D36 => W105 | D37 => W103 | D38 => W101 | D39 => W99 | D40 => W97 | D41 => W95 | D42 => W93 | D43 => W91 | D44 => W89 | D45 => W87 | D46 => W85 | D47 => W83 | D48 => W81 | D49 => W79 | D50 => W77 | D51 => W75 | D52 => W73 | D53 => W71 | D54 => W69 | D55 => W67 | D56 => W65 | D57 => W191 | D58 => W189 | D59 => W187 | D60 => W185 | D61 => W183 | D62 => W181 | D63 => W179 end
    | D52 => match b with D0 => W50 | D1 => W48 | D2 => W46 | D3 => W44 | D4 => W42 | D5 => W40 | D6 => W38 | D7 => W36 | D8 => W34 | D9 => W32 | D10 => W30 | D11 => W28 | D12 => W26 | D13 => W24 | D14 => W22 | D15 => W20 | D16 => W18 | D17 => W16 | D18 => W14 | D19 => W12 | D20 => W10 | D21 => W8 | D22 => W6 | D23 => W4 | D24 => W2 | D25 => W0 | D26 => W126 | D27 => W124 | D28 => W122 | D29 => W120 | D30 => W118 | D31 => W116 | D32 => W114 | D33 => W112 | D34 => W110 | D35 => W108 | D36 => W106 | D37 => W104 | D38 => W102 | D39 => W100 | D40 => W98 | D41 => W96 | D42 => W94 | D43 => W92 | D44 => W90 | D45 => W88 | D46 => W86 | D47 => W84 | D48 => W82 | D49 => W80 | D50 => W78 | D51 => W76 | D52 => W74 | D53 => W72 | D54 => W70 | D55 => W68 | D56 => W66 | D57 => W64 | D58 => W190 | D59 => W188 | D60 => W186 | D61 => W184 | D62 => W182 | D63 => W180 end
    | D53 => match b with D0 => W51 | D1 => W49 | D2 => W47 | D3 => W45 | D4 => W43 | D5 => W41 | D6 => W39 | D7 => W37 | D8 => W35 | D9 => W33 | D10 => W31 | D11 => W29 | D12 => W27 | D13 => W25 | D14 => W23 | D15 => W21 | D16 => W19 | D17 => W17 | D18 => W15 | D19 => W13 | D20 => W11 | D21 => W9 | D22 => W7 | D23 => W5 | D24 => W3 | D25 => W1 | D26 => W127 | D27 => W125 | D28 => W123 | D29 => W121 | D30 => W119 | D31 => W117 | D32 => W115 | D33 => W113 | D34 => W111 | D35 => W109 | D36 => W107 | D37 => W105 | D38 => W103 | D39 => W101 | D40 => W99 | D41 => W97 | D42 => W95 | D43 => W93 | D44 => W91 | D45 => W89 | D46 => W87 | D47 => W85 | D48 => W83 | D49 => W81 | D50 => W79 | D51 => W77 | D52 => W75 | D53 => W73 | D54 => W71 | D55 => W69 | D56 => W67 | D57 => W65 | D58 => W191 | D59 => W189 | D60 => W187 | D61 => W185 | D62 => W183 | D63 => W181 end
    | D54 => match b with D0 => W52 | D1 => W50 | D2 => W48 | D3 => W46 | D4 => W44 | D5 => W42 | D6 => W40 | D7 => W38 | D8 => W36 | D9 => W34 | D10 => W32 | D11 => W30 | D12 => W28 | D13 => W26 | D14 => W24 | D15 => W22 | D16 => W20 | D17 => W18 | D18 => W16 | D19 => W14 | D20 => W12 | D21 => W10 | D22 => W8 | D23 => W6 | D24 => W4 | D25 => W2 | D26 => W0 | D27 => W126 | D28 => W124 | D29 => W122 | D30 => W120 | D31 => W118 | D32 => W116 | D33 => W114 | D34 => W112 | D35 => W110 | D36 => W108 | D37 => W106 | D38 => W104 | D39 => W102 | D40 => W100 | D41 => W98 | D42 => W96 | D43 => W94 | D44 => W92 | D45 => W90 | D46 => W88 | D47 => W86 | D48 => W84 | D49 => W82 | D50 => W80 | D51 => W78 | D52 => W76 | D53 => W74 | D54 => W72 | D55 => W70 | D56 => W68 | D57 => W66 | D58 => W64 | D59 => W190 | D60 => W188 | D61 => W186 | D62 => W184 | D63 => W182 end
    | D55 => match b with D0 => W53 | D1 => W51 | D2 => W49 | D3 => W47 | D4 => W45 | D5 => W43 | D6 => W41 | D7 => W39 | D8 => W37 | D9 => W35 | D10 => W33 | D11 => W31 | D12 => W29 | D13 => W27 | D14 => W25 | D15 => W23 | D16 => W21 | D17 => W19 | D18 => W17 | D19 => W15 | D20 => W13 | D21 => W11 | D22 => W9 | D23 => W7 | D24 => W5 | D25 => W3 | D26 => W1 | D27 => W127 | D28 => W125 | D29 => W123 | D30 => W121 | D31 => W119 | D32 => W117 | D33 => W115 | D34 => W113 | D35 => W111 | D36 => W109 | D37 => W107 | D38 => W105 | D39 => W103 | D40 => W101 | D41 => W99 | D42 => W97 | D43 => W95 | D44 => W93 | D45 => W91 | D46 => W89 | D47 => W87 | D48 => W85 | D49 => W83 | D50 => W81 | D51 => W79 | D52 => W77 | D53 => W75 | D54 => W73 | D55 => W71 | D56 => W69 | D57 => W67 | D58 => W65 | D59 => W191 | D60 => W189 | D61 => W187 | D62 => W185 | D63 => W183 end
    | D56 => match b with D0 => W54 | D1 => W52 | D2 => W50 | D3 => W48 | D4 => W46 | D5 => W44 | D6 => W42 | D7 => W40 | D8 => W38 | D9 => W36 | D10 => W34 | D11 => W32 | D12 => W30 | D13 => W28 | D14 => W26 | D15 => W24 | D16 => W22 | D17 => W20 | D18 => W18 | D19 => W16 | D20 => W14 | D21 => W12 | D22 => W10 | D23 => W8 | D24 => W6 | D25 => W4 | D26 => W2 | D27 => W0 | D28 => W126 | D29 => W124 | D30 => W122 | D31 => W120 | D32 => W118 | D33 => W116 | D34 => W114 | D35 => W112 | D36 => W110 | D37 => W108 | D38 => W106 | D39 => W104 | D40 => W102 | D41 => W100 | D42 => W98 | D43 => W96 | D44 => W94 | D45 => W92 | D46 => W90 | D47 => W88 | D48 => W86 | D49 => W84 | D50 => W82 | D51 => W80 | D52 => W78 | D53 => W76 | D54 => W74 | D55 => W72 | D56 => W70 | D57 => W68 | D58 => W66 | D59 => W64 | D60 => W190 | D61 => W188 | D62 => W186 | D63 => W184 end
    | D57 => match b with D0 => W55 | D1 => W53 | D2 => W51 | D3 => W49 | D4 => W47 | D5 => W45 | D6 => W43 | D7 => W41 | D8 => W39 | D9 => W37 | D10 => W35 | D11 => W33 | D12 => W31 | D13 => W29 | D14 => W27 | D15 => W25 | D16 => W23 | D17 => W21 | D18 => W19 | D19 => W17 | D20 => W15 | D21 => W13 | D22 => W11 | D23 => W9 | D24 => W7 | D25 => W5 | D26 => W3 | D27 => W1 | D28 => W127 | D29 => W125 | D30 => W123 | D31 => W121 | D32 => W119 | D33 => W117 | D34 => W115 | D35 => W113 | D36 => W111 | D37 => W109 | D38 => W107 | D39 => W105 | D40 => W103 | D41 => W101 | D42 => W99 | D43 => W97 | D44 => W95 | D45 => W93 | D46 => W91 | D47 => W89 | D48 => W87 | D49 => W85 | D50 => W83 | D51 => W81 | D52 => W79 | D53 => W77 | D54 => W75 | D55 => W73 | D56 => W71 | D57 => W69 | D58 => W67 | D59 => W65 | D60 => W191 | D61 => W189 | D62 => W187 | D63 => W185 end
    | D58 => match b with D0 => W56 | D1 => W54 | D2 => W52 | D3 => W50 | D4 => W48 | D5 => W46 | D6 => W44 | D7 => W42 | D8 => W40 | D9 => W38 | D10 => W36 | D11 => W34 | D12 => W32 | D13 => W30 | D14 => W28 | D15 => W26 | D16 => W24 | D17 => W22 | D18 => W20 | D19 => W18 | D20 => W16 | D21 => W14 | D22 => W12 | D23 => W10 | D24 => W8 | D25 => W6 | D26 => W4 | D27 => W2 | D28 => W0 | D29 => W126 | D30 => W124 | D31 => W122 | D32 => W120 | D33 => W118 | D34 => W116 | D35 => W114 | D36 => W112 | D37 => W110 | D38 => W108 | D39 => W106 | D40 => W104 | D41 => W102 | D42 => W100 | D43 => W98 | D44 => W96 | D45 => W94 | D46 => W92 | D47 => W90 | D48 => W88 | D49 => W86 | D50 => W84 | D51 => W82 | D52 => W80 | D53 => W78 | D54 => W76 | D55 => W74 | D56 => W72 | D57 => W70 | D58 => W68 | D59 => W66 | D60 => W64 | D61 => W190 | D62 => W188 | D63 => W186 end
    | D59 => match b with D0 => W57 | D1 => W55 | D2 => W53 | D3 => W51 | D4 => W49 | D5 => W47 | D6 => W45 | D7 => W43 | D8 => W41 | D9 => W39 | D10 => W37 | D11 => W35 | D12 => W33 | D13 => W31 | D14 => W29 | D15 => W27 | D16 => W25 | D17 => W23 | D18 => W21 | D19 => W19 | D20 => W17 | D21 => W15 | D22 => W13 | D23 => W11 | D24 => W9 | D25 => W7 | D26 => W5 | D27 => W3 | D28 => W1 | D29 => W127 | D30 => W125 | D31 => W123 | D32 => W121 | D33 => W119 | D34 => W117 | D35 => W115 | D36 => W113 | D37 => W111 | D38 => W109 | D39 => W107 | D40 => W105 | D41 => W103 | D42 => W101 | D43 => W99 | D44 => W97 | D45 => W95 | D46 => W93 | D47 => W91 | D48 => W89 | D49 => W87 | D50 => W85 | D51 => W83 | D52 => W81 | D53 => W79 | D54 => W77 | D55 => W75 | D56 => W73 | D57 => W71 | D58 => W69 | D59 => W67 | D60 => W65 | D61 => W191 | D62 => W189 | D63 => W187 end
    | D60 => match b with D0 => W58 | D1 => W56 | D2 => W54 | D3 => W52 | D4 => W50 | D5 => W48 | D6 => W46 | D7 => W44 | D8 => W42 | D9 => W40 | D10 => W38 | D11 => W36 | D12 => W34 | D13 => W32 | D14 => W30 | D15 => W28 | D16 => W26 | D17 => W24 | D18 => W22 | D19 => W20 | D20 => W18 | D21 => W16 | D22 => W14 | D23 => W12 | D24 => W10 | D25 => W8 | D26 => W6 | D27 => W4 | D28 => W2 | D29 => W0 | D30 => W126 | D31 => W124 | D32 => W122 | D33 => W120 | D34 => W118 | D35 => W116 | D36 => W114 | D37 => W112 | D38 => W110 | D39 => W108 | D40 => W106 | D41 => W104 | D42 => W102 | D43 => W100 | D44 => W98 | D45 => W96 | D46 => W94 | D47 => W92 | D48 => W90 | D49 => W88 | D50 => W86 | D51 => W84 | D52 => W82 | D53 => W80 | D54 => W78 | D55 => W76 | D56 => W74 | D57 => W72 | D58 => W70 | D59 => W68 | D60 => W66 | D61 => W64 | D62 => W190 | D63 => W188 end
    | D61 => match b with D0 => W59 | D1 => W57 | D2 => W55 | D3 => W53 | D4 => W51 | D5 => W49 | D6 => W47 | D7 => W45 | D8 => W43 | D9 => W41 | D10 => W39 | D11 => W37 | D12 => W35 | D13 => W33 | D14 => W31 | D15 => W29 | D16 => W27 | D17 => W25 | D18 => W23 | D19 => W21 | D20 => W19 | D21 => W17 | D22 => W15 | D23 => W13 | D24 => W11 | D25 => W9 | D26 => W7 | D27 => W5 | D28 => W3 | D29 => W1 | D30 => W127 | D31 => W125 | D32 => W123 | D33 => W121 | D34 => W119 | D35 => W117 | D36 => W115 | D37 => W113 | D38 => W111 | D39 => W109 | D40 => W107 | D41 => W105 | D42 => W103 | D43 => W101 | D44 => W99 | D45 => W97 | D46 => W95 | D47 => W93 | D48 => W91 | D49 => W89 | D50 => W87 | D51 => W85 | D52 => W83 | D53 => W81 | D54 => W79 | D55 => W77 | D56 => W75 | D57 => W73 | D58 => W71 | D59 => W69 | D60 => W67 | D61 => W65 | D62 => W191 | D63 => W189 end
    | D62 => match b with D0 => W60 | D1 => W58 | D2 => W56 | D3 => W54 | D4 => W52 | D5 => W50 | D6 => W48 | D7 => W46 | D8 => W44 | D9 => W42 | D10 => W40 | D11 => W38 | D12 => W36 | D13 => W34 | D14 => W32 | D15 => W30 | D16 => W28 | D17 => W26 | D18 => W24 | D19 => W22 | D20 => W20 | D21 => W18 | D22 => W16 | D23 => W14 | D24 => W12 | D25 => W10 | D26 => W8 | D27 => W6 | D28 => W4 | D29 => W2 | D30 => W0 | D31 => W126 | D32 => W124 | D33 => W122 | D34 => W120 | D35 => W118 | D36 => W116 | D37 => W114 | D38 => W112 | D39 => W110 | D40 => W108 | D41 => W106 | D42 => W104 | D43 => W102 | D44 => W100 | D45 => W98 | D46 => W96 | D47 => W94 | D48 => W92 | D49 => W90 | D50 => W88 | D51 => W86 | D52 => W84 | D53 => W82 | D54 => W80 | D55 => W78 | D56 => W76 | D57 => W74 | D58 => W72 | D59 => W70 | D60 => W68 | D61 => W66 | D62 => W64 | D63 => W190 end
    | D63 => match b with D0 => W61 | D1 => W59 | D2 => W57 | D3 => W55 | D4 => W53 | D5 => W51 | D6 => W49 | D7 => W47 | D8 => W45 | D9 => W43 | D10 => W41 | D11 => W39 | D12 => W37 | D13 => W35 | D14 => W33 | D15 => W31 | D16 => W29 | D17 => W27 | D18 => W25 | D19 => W23 | D20 => W21 | D21 => W19 | D22 => W17 | D23 => W15 | D24 => W13 | D25 => W11 | D26 => W9 | D27 => W7 | D28 => W5 | D29 => W3 | D30 => W1 | D31 => W127 | D32 => W125 | D33 => W123 | D34 => W121 | D35 => W119 | D36 => W117 | D37 => W115 | D38 => W113 | D39 => W111 | D40 => W109 | D41 => W107 | D42 => W105 | D43 => W103 | D44 => W101 | D45 => W99 | D46 => W97 | D47 => W95 | D48 => W93 | D49 => W91 | D50 => W89 | D51 => W87 | D52 => W85 | D53 => W83 | D54 => W81 | D55 => W79 | D56 => W77 | D57 => W75 | D58 => W73 | D59 => W71 | D60 => W69 | D61 => W67 | D62 => W65 | D63 => W191 end
    end
  | _ => W0
  end.

Definition subHalf64 (br q_hi : bool) (a d0 : D64) : R128 :=
  if br then
    if q_hi then match a with
    | D0 => match d0 with D0 => P95 | D1 => P95 | D2 => P94 | D3 => P94 | D4 => P93 | D5 => P93 | D6 => P92 | D7 => P92 | D8 => P91 | D9 => P91 | D10 => P90 | D11 => P90 | D12 => P89 | D13 => P89 | D14 => P88 | D15 => P88 | D16 => P87 | D17 => P87 | D18 => P86 | D19 => P86 | D20 => P85 | D21 => P85 | D22 => P84 | D23 => P84 | D24 => P83 | D25 => P83 | D26 => P82 | D27 => P82 | D28 => P81 | D29 => P81 | D30 => P80 | D31 => P80 | D32 => P79 | D33 => P79 | D34 => P78 | D35 => P78 | D36 => P77 | D37 => P77 | D38 => P76 | D39 => P76 | D40 => P75 | D41 => P75 | D42 => P74 | D43 => P74 | D44 => P73 | D45 => P73 | D46 => P72 | D47 => P72 | D48 => P71 | D49 => P71 | D50 => P70 | D51 => P70 | D52 => P69 | D53 => P69 | D54 => P68 | D55 => P68 | D56 => P67 | D57 => P67 | D58 => P66 | D59 => P66 | D60 => P65 | D61 => P65 | D62 => P64 | D63 => P64 end
    | D1 => match d0 with D0 => P96 | D1 => P96 | D2 => P95 | D3 => P95 | D4 => P94 | D5 => P94 | D6 => P93 | D7 => P93 | D8 => P92 | D9 => P92 | D10 => P91 | D11 => P91 | D12 => P90 | D13 => P90 | D14 => P89 | D15 => P89 | D16 => P88 | D17 => P88 | D18 => P87 | D19 => P87 | D20 => P86 | D21 => P86 | D22 => P85 | D23 => P85 | D24 => P84 | D25 => P84 | D26 => P83 | D27 => P83 | D28 => P82 | D29 => P82 | D30 => P81 | D31 => P81 | D32 => P80 | D33 => P80 | D34 => P79 | D35 => P79 | D36 => P78 | D37 => P78 | D38 => P77 | D39 => P77 | D40 => P76 | D41 => P76 | D42 => P75 | D43 => P75 | D44 => P74 | D45 => P74 | D46 => P73 | D47 => P73 | D48 => P72 | D49 => P72 | D50 => P71 | D51 => P71 | D52 => P70 | D53 => P70 | D54 => P69 | D55 => P69 | D56 => P68 | D57 => P68 | D58 => P67 | D59 => P67 | D60 => P66 | D61 => P66 | D62 => P65 | D63 => P65 end
    | D2 => match d0 with D0 => P97 | D1 => P97 | D2 => P96 | D3 => P96 | D4 => P95 | D5 => P95 | D6 => P94 | D7 => P94 | D8 => P93 | D9 => P93 | D10 => P92 | D11 => P92 | D12 => P91 | D13 => P91 | D14 => P90 | D15 => P90 | D16 => P89 | D17 => P89 | D18 => P88 | D19 => P88 | D20 => P87 | D21 => P87 | D22 => P86 | D23 => P86 | D24 => P85 | D25 => P85 | D26 => P84 | D27 => P84 | D28 => P83 | D29 => P83 | D30 => P82 | D31 => P82 | D32 => P81 | D33 => P81 | D34 => P80 | D35 => P80 | D36 => P79 | D37 => P79 | D38 => P78 | D39 => P78 | D40 => P77 | D41 => P77 | D42 => P76 | D43 => P76 | D44 => P75 | D45 => P75 | D46 => P74 | D47 => P74 | D48 => P73 | D49 => P73 | D50 => P72 | D51 => P72 | D52 => P71 | D53 => P71 | D54 => P70 | D55 => P70 | D56 => P69 | D57 => P69 | D58 => P68 | D59 => P68 | D60 => P67 | D61 => P67 | D62 => P66 | D63 => P66 end
    | D3 => match d0 with D0 => P98 | D1 => P98 | D2 => P97 | D3 => P97 | D4 => P96 | D5 => P96 | D6 => P95 | D7 => P95 | D8 => P94 | D9 => P94 | D10 => P93 | D11 => P93 | D12 => P92 | D13 => P92 | D14 => P91 | D15 => P91 | D16 => P90 | D17 => P90 | D18 => P89 | D19 => P89 | D20 => P88 | D21 => P88 | D22 => P87 | D23 => P87 | D24 => P86 | D25 => P86 | D26 => P85 | D27 => P85 | D28 => P84 | D29 => P84 | D30 => P83 | D31 => P83 | D32 => P82 | D33 => P82 | D34 => P81 | D35 => P81 | D36 => P80 | D37 => P80 | D38 => P79 | D39 => P79 | D40 => P78 | D41 => P78 | D42 => P77 | D43 => P77 | D44 => P76 | D45 => P76 | D46 => P75 | D47 => P75 | D48 => P74 | D49 => P74 | D50 => P73 | D51 => P73 | D52 => P72 | D53 => P72 | D54 => P71 | D55 => P71 | D56 => P70 | D57 => P70 | D58 => P69 | D59 => P69 | D60 => P68 | D61 => P68 | D62 => P67 | D63 => P67 end
    | D4 => match d0 with D0 => P99 | D1 => P99 | D2 => P98 | D3 => P98 | D4 => P97 | D5 => P97 | D6 => P96 | D7 => P96 | D8 => P95 | D9 => P95 | D10 => P94 | D11 => P94 | D12 => P93 | D13 => P93 | D14 => P92 | D15 => P92 | D16 => P91 | D17 => P91 | D18 => P90 | D19 => P90 | D20 => P89 | D21 => P89 | D22 => P88 | D23 => P88 | D24 => P87 | D25 => P87 | D26 => P86 | D27 => P86 | D28 => P85 | D29 => P85 | D30 => P84 | D31 => P84 | D32 => P83 | D33 => P83 | D34 => P82 | D35 => P82 | D36 => P81 | D37 => P81 | D38 => P80 | D39 => P80 | D40 => P79 | D41 => P79 | D42 => P78 | D43 => P78 | D44 => P77 | D45 => P77 | D46 => P76 | D47 => P76 | D48 => P75 | D49 => P75 | D50 => P74 | D51 => P74 | D52 => P73 | D53 => P73 | D54 => P72 | D55 => P72 | D56 => P71 | D57 => P71 | D58 => P70 | D59 => P70 | D60 => P69 | D61 => P69 | D62 => P68 | D63 => P68 end
    | D5 => match d0 with D0 => P100 | D1 => P100 | D2 => P99 | D3 => P99 | D4 => P98 | D5 => P98 | D6 => P97 | D7 => P97 | D8 => P96 | D9 => P96 | D10 => P95 | D11 => P95 | D12 => P94 | D13 => P94 | D14 => P93 | D15 => P93 | D16 => P92 | D17 => P92 | D18 => P91 | D19 => P91 | D20 => P90 | D21 => P90 | D22 => P89 | D23 => P89 | D24 => P88 | D25 => P88 | D26 => P87 | D27 => P87 | D28 => P86 | D29 => P86 | D30 => P85 | D31 => P85 | D32 => P84 | D33 => P84 | D34 => P83 | D35 => P83 | D36 => P82 | D37 => P82 | D38 => P81 | D39 => P81 | D40 => P80 | D41 => P80 | D42 => P79 | D43 => P79 | D44 => P78 | D45 => P78 | D46 => P77 | D47 => P77 | D48 => P76 | D49 => P76 | D50 => P75 | D51 => P75 | D52 => P74 | D53 => P74 | D54 => P73 | D55 => P73 | D56 => P72 | D57 => P72 | D58 => P71 | D59 => P71 | D60 => P70 | D61 => P70 | D62 => P69 | D63 => P69 end
    | D6 => match d0 with D0 => P101 | D1 => P101 | D2 => P100 | D3 => P100 | D4 => P99 | D5 => P99 | D6 => P98 | D7 => P98 | D8 => P97 | D9 => P97 | D10 => P96 | D11 => P96 | D12 => P95 | D13 => P95 | D14 => P94 | D15 => P94 | D16 => P93 | D17 => P93 | D18 => P92 | D19 => P92 | D20 => P91 | D21 => P91 | D22 => P90 | D23 => P90 | D24 => P89 | D25 => P89 | D26 => P88 | D27 => P88 | D28 => P87 | D29 => P87 | D30 => P86 | D31 => P86 | D32 => P85 | D33 => P85 | D34 => P84 | D35 => P84 | D36 => P83 | D37 => P83 | D38 => P82 | D39 => P82 | D40 => P81 | D41 => P81 | D42 => P80 | D43 => P80 | D44 => P79 | D45 => P79 | D46 => P78 | D47 => P78 | D48 => P77 | D49 => P77 | D50 => P76 | D51 => P76 | D52 => P75 | D53 => P75 | D54 => P74 | D55 => P74 | D56 => P73 | D57 => P73 | D58 => P72 | D59 => P72 | D60 => P71 | D61 => P71 | D62 => P70 | D63 => P70 end
    | D7 => match d0 with D0 => P102 | D1 => P102 | D2 => P101 | D3 => P101 | D4 => P100 | D5 => P100 | D6 => P99 | D7 => P99 | D8 => P98 | D9 => P98 | D10 => P97 | D11 => P97 | D12 => P96 | D13 => P96 | D14 => P95 | D15 => P95 | D16 => P94 | D17 => P94 | D18 => P93 | D19 => P93 | D20 => P92 | D21 => P92 | D22 => P91 | D23 => P91 | D24 => P90 | D25 => P90 | D26 => P89 | D27 => P89 | D28 => P88 | D29 => P88 | D30 => P87 | D31 => P87 | D32 => P86 | D33 => P86 | D34 => P85 | D35 => P85 | D36 => P84 | D37 => P84 | D38 => P83 | D39 => P83 | D40 => P82 | D41 => P82 | D42 => P81 | D43 => P81 | D44 => P80 | D45 => P80 | D46 => P79 | D47 => P79 | D48 => P78 | D49 => P78 | D50 => P77 | D51 => P77 | D52 => P76 | D53 => P76 | D54 => P75 | D55 => P75 | D56 => P74 | D57 => P74 | D58 => P73 | D59 => P73 | D60 => P72 | D61 => P72 | D62 => P71 | D63 => P71 end
    | D8 => match d0 with D0 => P103 | D1 => P103 | D2 => P102 | D3 => P102 | D4 => P101 | D5 => P101 | D6 => P100 | D7 => P100 | D8 => P99 | D9 => P99 | D10 => P98 | D11 => P98 | D12 => P97 | D13 => P97 | D14 => P96 | D15 => P96 | D16 => P95 | D17 => P95 | D18 => P94 | D19 => P94 | D20 => P93 | D21 => P93 | D22 => P92 | D23 => P92 | D24 => P91 | D25 => P91 | D26 => P90 | D27 => P90 | D28 => P89 | D29 => P89 | D30 => P88 | D31 => P88 | D32 => P87 | D33 => P87 | D34 => P86 | D35 => P86 | D36 => P85 | D37 => P85 | D38 => P84 | D39 => P84 | D40 => P83 | D41 => P83 | D42 => P82 | D43 => P82 | D44 => P81 | D45 => P81 | D46 => P80 | D47 => P80 | D48 => P79 | D49 => P79 | D50 => P78 | D51 => P78 | D52 => P77 | D53 => P77 | D54 => P76 | D55 => P76 | D56 => P75 | D57 => P75 | D58 => P74 | D59 => P74 | D60 => P73 | D61 => P73 | D62 => P72 | D63 => P72 end
    | D9 => match d0 with D0 => P104 | D1 => P104 | D2 => P103 | D3 => P103 | D4 => P102 | D5 => P102 | D6 => P101 | D7 => P101 | D8 => P100 | D9 => P100 | D10 => P99 | D11 => P99 | D12 => P98 | D13 => P98 | D14 => P97 | D15 => P97 | D16 => P96 | D17 => P96 | D18 => P95 | D19 => P95 | D20 => P94 | D21 => P94 | D22 => P93 | D23 => P93 | D24 => P92 | D25 => P92 | D26 => P91 | D27 => P91 | D28 => P90 | D29 => P90 | D30 => P89 | D31 => P89 | D32 => P88 | D33 => P88 | D34 => P87 | D35 => P87 | D36 => P86 | D37 => P86 | D38 => P85 | D39 => P85 | D40 => P84 | D41 => P84 | D42 => P83 | D43 => P83 | D44 => P82 | D45 => P82 | D46 => P81 | D47 => P81 | D48 => P80 | D49 => P80 | D50 => P79 | D51 => P79 | D52 => P78 | D53 => P78 | D54 => P77 | D55 => P77 | D56 => P76 | D57 => P76 | D58 => P75 | D59 => P75 | D60 => P74 | D61 => P74 | D62 => P73 | D63 => P73 end
    | D10 => match d0 with D0 => P105 | D1 => P105 | D2 => P104 | D3 => P104 | D4 => P103 | D5 => P103 | D6 => P102 | D7 => P102 | D8 => P101 | D9 => P101 | D10 => P100 | D11 => P100 | D12 => P99 | D13 => P99 | D14 => P98 | D15 => P98 | D16 => P97 | D17 => P97 | D18 => P96 | D19 => P96 | D20 => P95 | D21 => P95 | D22 => P94 | D23 => P94 | D24 => P93 | D25 => P93 | D26 => P92 | D27 => P92 | D28 => P91 | D29 => P91 | D30 => P90 | D31 => P90 | D32 => P89 | D33 => P89 | D34 => P88 | D35 => P88 | D36 => P87 | D37 => P87 | D38 => P86 | D39 => P86 | D40 => P85 | D41 => P85 | D42 => P84 | D43 => P84 | D44 => P83 | D45 => P83 | D46 => P82 | D47 => P82 | D48 => P81 | D49 => P81 | D50 => P80 | D51 => P80 | D52 => P79 | D53 => P79 | D54 => P78 | D55 => P78 | D56 => P77 | D57 => P77 | D58 => P76 | D59 => P76 | D60 => P75 | D61 => P75 | D62 => P74 | D63 => P74 end
    | D11 => match d0 with D0 => P106 | D1 => P106 | D2 => P105 | D3 => P105 | D4 => P104 | D5 => P104 | D6 => P103 | D7 => P103 | D8 => P102 | D9 => P102 | D10 => P101 | D11 => P101 | D12 => P100 | D13 => P100 | D14 => P99 | D15 => P99 | D16 => P98 | D17 => P98 | D18 => P97 | D19 => P97 | D20 => P96 | D21 => P96 | D22 => P95 | D23 => P95 | D24 => P94 | D25 => P94 | D26 => P93 | D27 => P93 | D28 => P92 | D29 => P92 | D30 => P91 | D31 => P91 | D32 => P90 | D33 => P90 | D34 => P89 | D35 => P89 | D36 => P88 | D37 => P88 | D38 => P87 | D39 => P87 | D40 => P86 | D41 => P86 | D42 => P85 | D43 => P85 | D44 => P84 | D45 => P84 | D46 => P83 | D47 => P83 | D48 => P82 | D49 => P82 | D50 => P81 | D51 => P81 | D52 => P80 | D53 => P80 | D54 => P79 | D55 => P79 | D56 => P78 | D57 => P78 | D58 => P77 | D59 => P77 | D60 => P76 | D61 => P76 | D62 => P75 | D63 => P75 end
    | D12 => match d0 with D0 => P107 | D1 => P107 | D2 => P106 | D3 => P106 | D4 => P105 | D5 => P105 | D6 => P104 | D7 => P104 | D8 => P103 | D9 => P103 | D10 => P102 | D11 => P102 | D12 => P101 | D13 => P101 | D14 => P100 | D15 => P100 | D16 => P99 | D17 => P99 | D18 => P98 | D19 => P98 | D20 => P97 | D21 => P97 | D22 => P96 | D23 => P96 | D24 => P95 | D25 => P95 | D26 => P94 | D27 => P94 | D28 => P93 | D29 => P93 | D30 => P92 | D31 => P92 | D32 => P91 | D33 => P91 | D34 => P90 | D35 => P90 | D36 => P89 | D37 => P89 | D38 => P88 | D39 => P88 | D40 => P87 | D41 => P87 | D42 => P86 | D43 => P86 | D44 => P85 | D45 => P85 | D46 => P84 | D47 => P84 | D48 => P83 | D49 => P83 | D50 => P82 | D51 => P82 | D52 => P81 | D53 => P81 | D54 => P80 | D55 => P80 | D56 => P79 | D57 => P79 | D58 => P78 | D59 => P78 | D60 => P77 | D61 => P77 | D62 => P76 | D63 => P76 end
    | D13 => match d0 with D0 => P108 | D1 => P108 | D2 => P107 | D3 => P107 | D4 => P106 | D5 => P106 | D6 => P105 | D7 => P105 | D8 => P104 | D9 => P104 | D10 => P103 | D11 => P103 | D12 => P102 | D13 => P102 | D14 => P101 | D15 => P101 | D16 => P100 | D17 => P100 | D18 => P99 | D19 => P99 | D20 => P98 | D21 => P98 | D22 => P97 | D23 => P97 | D24 => P96 | D25 => P96 | D26 => P95 | D27 => P95 | D28 => P94 | D29 => P94 | D30 => P93 | D31 => P93 | D32 => P92 | D33 => P92 | D34 => P91 | D35 => P91 | D36 => P90 | D37 => P90 | D38 => P89 | D39 => P89 | D40 => P88 | D41 => P88 | D42 => P87 | D43 => P87 | D44 => P86 | D45 => P86 | D46 => P85 | D47 => P85 | D48 => P84 | D49 => P84 | D50 => P83 | D51 => P83 | D52 => P82 | D53 => P82 | D54 => P81 | D55 => P81 | D56 => P80 | D57 => P80 | D58 => P79 | D59 => P79 | D60 => P78 | D61 => P78 | D62 => P77 | D63 => P77 end
    | D14 => match d0 with D0 => P109 | D1 => P109 | D2 => P108 | D3 => P108 | D4 => P107 | D5 => P107 | D6 => P106 | D7 => P106 | D8 => P105 | D9 => P105 | D10 => P104 | D11 => P104 | D12 => P103 | D13 => P103 | D14 => P102 | D15 => P102 | D16 => P101 | D17 => P101 | D18 => P100 | D19 => P100 | D20 => P99 | D21 => P99 | D22 => P98 | D23 => P98 | D24 => P97 | D25 => P97 | D26 => P96 | D27 => P96 | D28 => P95 | D29 => P95 | D30 => P94 | D31 => P94 | D32 => P93 | D33 => P93 | D34 => P92 | D35 => P92 | D36 => P91 | D37 => P91 | D38 => P90 | D39 => P90 | D40 => P89 | D41 => P89 | D42 => P88 | D43 => P88 | D44 => P87 | D45 => P87 | D46 => P86 | D47 => P86 | D48 => P85 | D49 => P85 | D50 => P84 | D51 => P84 | D52 => P83 | D53 => P83 | D54 => P82 | D55 => P82 | D56 => P81 | D57 => P81 | D58 => P80 | D59 => P80 | D60 => P79 | D61 => P79 | D62 => P78 | D63 => P78 end
    | D15 => match d0 with D0 => P110 | D1 => P110 | D2 => P109 | D3 => P109 | D4 => P108 | D5 => P108 | D6 => P107 | D7 => P107 | D8 => P106 | D9 => P106 | D10 => P105 | D11 => P105 | D12 => P104 | D13 => P104 | D14 => P103 | D15 => P103 | D16 => P102 | D17 => P102 | D18 => P101 | D19 => P101 | D20 => P100 | D21 => P100 | D22 => P99 | D23 => P99 | D24 => P98 | D25 => P98 | D26 => P97 | D27 => P97 | D28 => P96 | D29 => P96 | D30 => P95 | D31 => P95 | D32 => P94 | D33 => P94 | D34 => P93 | D35 => P93 | D36 => P92 | D37 => P92 | D38 => P91 | D39 => P91 | D40 => P90 | D41 => P90 | D42 => P89 | D43 => P89 | D44 => P88 | D45 => P88 | D46 => P87 | D47 => P87 | D48 => P86 | D49 => P86 | D50 => P85 | D51 => P85 | D52 => P84 | D53 => P84 | D54 => P83 | D55 => P83 | D56 => P82 | D57 => P82 | D58 => P81 | D59 => P81 | D60 => P80 | D61 => P80 | D62 => P79 | D63 => P79 end
    | D16 => match d0 with D0 => P111 | D1 => P111 | D2 => P110 | D3 => P110 | D4 => P109 | D5 => P109 | D6 => P108 | D7 => P108 | D8 => P107 | D9 => P107 | D10 => P106 | D11 => P106 | D12 => P105 | D13 => P105 | D14 => P104 | D15 => P104 | D16 => P103 | D17 => P103 | D18 => P102 | D19 => P102 | D20 => P101 | D21 => P101 | D22 => P100 | D23 => P100 | D24 => P99 | D25 => P99 | D26 => P98 | D27 => P98 | D28 => P97 | D29 => P97 | D30 => P96 | D31 => P96 | D32 => P95 | D33 => P95 | D34 => P94 | D35 => P94 | D36 => P93 | D37 => P93 | D38 => P92 | D39 => P92 | D40 => P91 | D41 => P91 | D42 => P90 | D43 => P90 | D44 => P89 | D45 => P89 | D46 => P88 | D47 => P88 | D48 => P87 | D49 => P87 | D50 => P86 | D51 => P86 | D52 => P85 | D53 => P85 | D54 => P84 | D55 => P84 | D56 => P83 | D57 => P83 | D58 => P82 | D59 => P82 | D60 => P81 | D61 => P81 | D62 => P80 | D63 => P80 end
    | D17 => match d0 with D0 => P112 | D1 => P112 | D2 => P111 | D3 => P111 | D4 => P110 | D5 => P110 | D6 => P109 | D7 => P109 | D8 => P108 | D9 => P108 | D10 => P107 | D11 => P107 | D12 => P106 | D13 => P106 | D14 => P105 | D15 => P105 | D16 => P104 | D17 => P104 | D18 => P103 | D19 => P103 | D20 => P102 | D21 => P102 | D22 => P101 | D23 => P101 | D24 => P100 | D25 => P100 | D26 => P99 | D27 => P99 | D28 => P98 | D29 => P98 | D30 => P97 | D31 => P97 | D32 => P96 | D33 => P96 | D34 => P95 | D35 => P95 | D36 => P94 | D37 => P94 | D38 => P93 | D39 => P93 | D40 => P92 | D41 => P92 | D42 => P91 | D43 => P91 | D44 => P90 | D45 => P90 | D46 => P89 | D47 => P89 | D48 => P88 | D49 => P88 | D50 => P87 | D51 => P87 | D52 => P86 | D53 => P86 | D54 => P85 | D55 => P85 | D56 => P84 | D57 => P84 | D58 => P83 | D59 => P83 | D60 => P82 | D61 => P82 | D62 => P81 | D63 => P81 end
    | D18 => match d0 with D0 => P113 | D1 => P113 | D2 => P112 | D3 => P112 | D4 => P111 | D5 => P111 | D6 => P110 | D7 => P110 | D8 => P109 | D9 => P109 | D10 => P108 | D11 => P108 | D12 => P107 | D13 => P107 | D14 => P106 | D15 => P106 | D16 => P105 | D17 => P105 | D18 => P104 | D19 => P104 | D20 => P103 | D21 => P103 | D22 => P102 | D23 => P102 | D24 => P101 | D25 => P101 | D26 => P100 | D27 => P100 | D28 => P99 | D29 => P99 | D30 => P98 | D31 => P98 | D32 => P97 | D33 => P97 | D34 => P96 | D35 => P96 | D36 => P95 | D37 => P95 | D38 => P94 | D39 => P94 | D40 => P93 | D41 => P93 | D42 => P92 | D43 => P92 | D44 => P91 | D45 => P91 | D46 => P90 | D47 => P90 | D48 => P89 | D49 => P89 | D50 => P88 | D51 => P88 | D52 => P87 | D53 => P87 | D54 => P86 | D55 => P86 | D56 => P85 | D57 => P85 | D58 => P84 | D59 => P84 | D60 => P83 | D61 => P83 | D62 => P82 | D63 => P82 end
    | D19 => match d0 with D0 => P114 | D1 => P114 | D2 => P113 | D3 => P113 | D4 => P112 | D5 => P112 | D6 => P111 | D7 => P111 | D8 => P110 | D9 => P110 | D10 => P109 | D11 => P109 | D12 => P108 | D13 => P108 | D14 => P107 | D15 => P107 | D16 => P106 | D17 => P106 | D18 => P105 | D19 => P105 | D20 => P104 | D21 => P104 | D22 => P103 | D23 => P103 | D24 => P102 | D25 => P102 | D26 => P101 | D27 => P101 | D28 => P100 | D29 => P100 | D30 => P99 | D31 => P99 | D32 => P98 | D33 => P98 | D34 => P97 | D35 => P97 | D36 => P96 | D37 => P96 | D38 => P95 | D39 => P95 | D40 => P94 | D41 => P94 | D42 => P93 | D43 => P93 | D44 => P92 | D45 => P92 | D46 => P91 | D47 => P91 | D48 => P90 | D49 => P90 | D50 => P89 | D51 => P89 | D52 => P88 | D53 => P88 | D54 => P87 | D55 => P87 | D56 => P86 | D57 => P86 | D58 => P85 | D59 => P85 | D60 => P84 | D61 => P84 | D62 => P83 | D63 => P83 end
    | D20 => match d0 with D0 => P115 | D1 => P115 | D2 => P114 | D3 => P114 | D4 => P113 | D5 => P113 | D6 => P112 | D7 => P112 | D8 => P111 | D9 => P111 | D10 => P110 | D11 => P110 | D12 => P109 | D13 => P109 | D14 => P108 | D15 => P108 | D16 => P107 | D17 => P107 | D18 => P106 | D19 => P106 | D20 => P105 | D21 => P105 | D22 => P104 | D23 => P104 | D24 => P103 | D25 => P103 | D26 => P102 | D27 => P102 | D28 => P101 | D29 => P101 | D30 => P100 | D31 => P100 | D32 => P99 | D33 => P99 | D34 => P98 | D35 => P98 | D36 => P97 | D37 => P97 | D38 => P96 | D39 => P96 | D40 => P95 | D41 => P95 | D42 => P94 | D43 => P94 | D44 => P93 | D45 => P93 | D46 => P92 | D47 => P92 | D48 => P91 | D49 => P91 | D50 => P90 | D51 => P90 | D52 => P89 | D53 => P89 | D54 => P88 | D55 => P88 | D56 => P87 | D57 => P87 | D58 => P86 | D59 => P86 | D60 => P85 | D61 => P85 | D62 => P84 | D63 => P84 end
    | D21 => match d0 with D0 => P116 | D1 => P116 | D2 => P115 | D3 => P115 | D4 => P114 | D5 => P114 | D6 => P113 | D7 => P113 | D8 => P112 | D9 => P112 | D10 => P111 | D11 => P111 | D12 => P110 | D13 => P110 | D14 => P109 | D15 => P109 | D16 => P108 | D17 => P108 | D18 => P107 | D19 => P107 | D20 => P106 | D21 => P106 | D22 => P105 | D23 => P105 | D24 => P104 | D25 => P104 | D26 => P103 | D27 => P103 | D28 => P102 | D29 => P102 | D30 => P101 | D31 => P101 | D32 => P100 | D33 => P100 | D34 => P99 | D35 => P99 | D36 => P98 | D37 => P98 | D38 => P97 | D39 => P97 | D40 => P96 | D41 => P96 | D42 => P95 | D43 => P95 | D44 => P94 | D45 => P94 | D46 => P93 | D47 => P93 | D48 => P92 | D49 => P92 | D50 => P91 | D51 => P91 | D52 => P90 | D53 => P90 | D54 => P89 | D55 => P89 | D56 => P88 | D57 => P88 | D58 => P87 | D59 => P87 | D60 => P86 | D61 => P86 | D62 => P85 | D63 => P85 end
    | D22 => match d0 with D0 => P117 | D1 => P117 | D2 => P116 | D3 => P116 | D4 => P115 | D5 => P115 | D6 => P114 | D7 => P114 | D8 => P113 | D9 => P113 | D10 => P112 | D11 => P112 | D12 => P111 | D13 => P111 | D14 => P110 | D15 => P110 | D16 => P109 | D17 => P109 | D18 => P108 | D19 => P108 | D20 => P107 | D21 => P107 | D22 => P106 | D23 => P106 | D24 => P105 | D25 => P105 | D26 => P104 | D27 => P104 | D28 => P103 | D29 => P103 | D30 => P102 | D31 => P102 | D32 => P101 | D33 => P101 | D34 => P100 | D35 => P100 | D36 => P99 | D37 => P99 | D38 => P98 | D39 => P98 | D40 => P97 | D41 => P97 | D42 => P96 | D43 => P96 | D44 => P95 | D45 => P95 | D46 => P94 | D47 => P94 | D48 => P93 | D49 => P93 | D50 => P92 | D51 => P92 | D52 => P91 | D53 => P91 | D54 => P90 | D55 => P90 | D56 => P89 | D57 => P89 | D58 => P88 | D59 => P88 | D60 => P87 | D61 => P87 | D62 => P86 | D63 => P86 end
    | D23 => match d0 with D0 => P118 | D1 => P118 | D2 => P117 | D3 => P117 | D4 => P116 | D5 => P116 | D6 => P115 | D7 => P115 | D8 => P114 | D9 => P114 | D10 => P113 | D11 => P113 | D12 => P112 | D13 => P112 | D14 => P111 | D15 => P111 | D16 => P110 | D17 => P110 | D18 => P109 | D19 => P109 | D20 => P108 | D21 => P108 | D22 => P107 | D23 => P107 | D24 => P106 | D25 => P106 | D26 => P105 | D27 => P105 | D28 => P104 | D29 => P104 | D30 => P103 | D31 => P103 | D32 => P102 | D33 => P102 | D34 => P101 | D35 => P101 | D36 => P100 | D37 => P100 | D38 => P99 | D39 => P99 | D40 => P98 | D41 => P98 | D42 => P97 | D43 => P97 | D44 => P96 | D45 => P96 | D46 => P95 | D47 => P95 | D48 => P94 | D49 => P94 | D50 => P93 | D51 => P93 | D52 => P92 | D53 => P92 | D54 => P91 | D55 => P91 | D56 => P90 | D57 => P90 | D58 => P89 | D59 => P89 | D60 => P88 | D61 => P88 | D62 => P87 | D63 => P87 end
    | D24 => match d0 with D0 => P119 | D1 => P119 | D2 => P118 | D3 => P118 | D4 => P117 | D5 => P117 | D6 => P116 | D7 => P116 | D8 => P115 | D9 => P115 | D10 => P114 | D11 => P114 | D12 => P113 | D13 => P113 | D14 => P112 | D15 => P112 | D16 => P111 | D17 => P111 | D18 => P110 | D19 => P110 | D20 => P109 | D21 => P109 | D22 => P108 | D23 => P108 | D24 => P107 | D25 => P107 | D26 => P106 | D27 => P106 | D28 => P105 | D29 => P105 | D30 => P104 | D31 => P104 | D32 => P103 | D33 => P103 | D34 => P102 | D35 => P102 | D36 => P101 | D37 => P101 | D38 => P100 | D39 => P100 | D40 => P99 | D41 => P99 | D42 => P98 | D43 => P98 | D44 => P97 | D45 => P97 | D46 => P96 | D47 => P96 | D48 => P95 | D49 => P95 | D50 => P94 | D51 => P94 | D52 => P93 | D53 => P93 | D54 => P92 | D55 => P92 | D56 => P91 | D57 => P91 | D58 => P90 | D59 => P90 | D60 => P89 | D61 => P89 | D62 => P88 | D63 => P88 end
    | D25 => match d0 with D0 => P120 | D1 => P120 | D2 => P119 | D3 => P119 | D4 => P118 | D5 => P118 | D6 => P117 | D7 => P117 | D8 => P116 | D9 => P116 | D10 => P115 | D11 => P115 | D12 => P114 | D13 => P114 | D14 => P113 | D15 => P113 | D16 => P112 | D17 => P112 | D18 => P111 | D19 => P111 | D20 => P110 | D21 => P110 | D22 => P109 | D23 => P109 | D24 => P108 | D25 => P108 | D26 => P107 | D27 => P107 | D28 => P106 | D29 => P106 | D30 => P105 | D31 => P105 | D32 => P104 | D33 => P104 | D34 => P103 | D35 => P103 | D36 => P102 | D37 => P102 | D38 => P101 | D39 => P101 | D40 => P100 | D41 => P100 | D42 => P99 | D43 => P99 | D44 => P98 | D45 => P98 | D46 => P97 | D47 => P97 | D48 => P96 | D49 => P96 | D50 => P95 | D51 => P95 | D52 => P94 | D53 => P94 | D54 => P93 | D55 => P93 | D56 => P92 | D57 => P92 | D58 => P91 | D59 => P91 | D60 => P90 | D61 => P90 | D62 => P89 | D63 => P89 end
    | D26 => match d0 with D0 => P121 | D1 => P121 | D2 => P120 | D3 => P120 | D4 => P119 | D5 => P119 | D6 => P118 | D7 => P118 | D8 => P117 | D9 => P117 | D10 => P116 | D11 => P116 | D12 => P115 | D13 => P115 | D14 => P114 | D15 => P114 | D16 => P113 | D17 => P113 | D18 => P112 | D19 => P112 | D20 => P111 | D21 => P111 | D22 => P110 | D23 => P110 | D24 => P109 | D25 => P109 | D26 => P108 | D27 => P108 | D28 => P107 | D29 => P107 | D30 => P106 | D31 => P106 | D32 => P105 | D33 => P105 | D34 => P104 | D35 => P104 | D36 => P103 | D37 => P103 | D38 => P102 | D39 => P102 | D40 => P101 | D41 => P101 | D42 => P100 | D43 => P100 | D44 => P99 | D45 => P99 | D46 => P98 | D47 => P98 | D48 => P97 | D49 => P97 | D50 => P96 | D51 => P96 | D52 => P95 | D53 => P95 | D54 => P94 | D55 => P94 | D56 => P93 | D57 => P93 | D58 => P92 | D59 => P92 | D60 => P91 | D61 => P91 | D62 => P90 | D63 => P90 end
    | D27 => match d0 with D0 => P122 | D1 => P122 | D2 => P121 | D3 => P121 | D4 => P120 | D5 => P120 | D6 => P119 | D7 => P119 | D8 => P118 | D9 => P118 | D10 => P117 | D11 => P117 | D12 => P116 | D13 => P116 | D14 => P115 | D15 => P115 | D16 => P114 | D17 => P114 | D18 => P113 | D19 => P113 | D20 => P112 | D21 => P112 | D22 => P111 | D23 => P111 | D24 => P110 | D25 => P110 | D26 => P109 | D27 => P109 | D28 => P108 | D29 => P108 | D30 => P107 | D31 => P107 | D32 => P106 | D33 => P106 | D34 => P105 | D35 => P105 | D36 => P104 | D37 => P104 | D38 => P103 | D39 => P103 | D40 => P102 | D41 => P102 | D42 => P101 | D43 => P101 | D44 => P100 | D45 => P100 | D46 => P99 | D47 => P99 | D48 => P98 | D49 => P98 | D50 => P97 | D51 => P97 | D52 => P96 | D53 => P96 | D54 => P95 | D55 => P95 | D56 => P94 | D57 => P94 | D58 => P93 | D59 => P93 | D60 => P92 | D61 => P92 | D62 => P91 | D63 => P91 end
    | D28 => match d0 with D0 => P123 | D1 => P123 | D2 => P122 | D3 => P122 | D4 => P121 | D5 => P121 | D6 => P120 | D7 => P120 | D8 => P119 | D9 => P119 | D10 => P118 | D11 => P118 | D12 => P117 | D13 => P117 | D14 => P116 | D15 => P116 | D16 => P115 | D17 => P115 | D18 => P114 | D19 => P114 | D20 => P113 | D21 => P113 | D22 => P112 | D23 => P112 | D24 => P111 | D25 => P111 | D26 => P110 | D27 => P110 | D28 => P109 | D29 => P109 | D30 => P108 | D31 => P108 | D32 => P107 | D33 => P107 | D34 => P106 | D35 => P106 | D36 => P105 | D37 => P105 | D38 => P104 | D39 => P104 | D40 => P103 | D41 => P103 | D42 => P102 | D43 => P102 | D44 => P101 | D45 => P101 | D46 => P100 | D47 => P100 | D48 => P99 | D49 => P99 | D50 => P98 | D51 => P98 | D52 => P97 | D53 => P97 | D54 => P96 | D55 => P96 | D56 => P95 | D57 => P95 | D58 => P94 | D59 => P94 | D60 => P93 | D61 => P93 | D62 => P92 | D63 => P92 end
    | D29 => match d0 with D0 => P124 | D1 => P124 | D2 => P123 | D3 => P123 | D4 => P122 | D5 => P122 | D6 => P121 | D7 => P121 | D8 => P120 | D9 => P120 | D10 => P119 | D11 => P119 | D12 => P118 | D13 => P118 | D14 => P117 | D15 => P117 | D16 => P116 | D17 => P116 | D18 => P115 | D19 => P115 | D20 => P114 | D21 => P114 | D22 => P113 | D23 => P113 | D24 => P112 | D25 => P112 | D26 => P111 | D27 => P111 | D28 => P110 | D29 => P110 | D30 => P109 | D31 => P109 | D32 => P108 | D33 => P108 | D34 => P107 | D35 => P107 | D36 => P106 | D37 => P106 | D38 => P105 | D39 => P105 | D40 => P104 | D41 => P104 | D42 => P103 | D43 => P103 | D44 => P102 | D45 => P102 | D46 => P101 | D47 => P101 | D48 => P100 | D49 => P100 | D50 => P99 | D51 => P99 | D52 => P98 | D53 => P98 | D54 => P97 | D55 => P97 | D56 => P96 | D57 => P96 | D58 => P95 | D59 => P95 | D60 => P94 | D61 => P94 | D62 => P93 | D63 => P93 end
    | D30 => match d0 with D0 => P125 | D1 => P125 | D2 => P124 | D3 => P124 | D4 => P123 | D5 => P123 | D6 => P122 | D7 => P122 | D8 => P121 | D9 => P121 | D10 => P120 | D11 => P120 | D12 => P119 | D13 => P119 | D14 => P118 | D15 => P118 | D16 => P117 | D17 => P117 | D18 => P116 | D19 => P116 | D20 => P115 | D21 => P115 | D22 => P114 | D23 => P114 | D24 => P113 | D25 => P113 | D26 => P112 | D27 => P112 | D28 => P111 | D29 => P111 | D30 => P110 | D31 => P110 | D32 => P109 | D33 => P109 | D34 => P108 | D35 => P108 | D36 => P107 | D37 => P107 | D38 => P106 | D39 => P106 | D40 => P105 | D41 => P105 | D42 => P104 | D43 => P104 | D44 => P103 | D45 => P103 | D46 => P102 | D47 => P102 | D48 => P101 | D49 => P101 | D50 => P100 | D51 => P100 | D52 => P99 | D53 => P99 | D54 => P98 | D55 => P98 | D56 => P97 | D57 => P97 | D58 => P96 | D59 => P96 | D60 => P95 | D61 => P95 | D62 => P94 | D63 => P94 end
    | D31 => match d0 with D0 => P126 | D1 => P126 | D2 => P125 | D3 => P125 | D4 => P124 | D5 => P124 | D6 => P123 | D7 => P123 | D8 => P122 | D9 => P122 | D10 => P121 | D11 => P121 | D12 => P120 | D13 => P120 | D14 => P119 | D15 => P119 | D16 => P118 | D17 => P118 | D18 => P117 | D19 => P117 | D20 => P116 | D21 => P116 | D22 => P115 | D23 => P115 | D24 => P114 | D25 => P114 | D26 => P113 | D27 => P113 | D28 => P112 | D29 => P112 | D30 => P111 | D31 => P111 | D32 => P110 | D33 => P110 | D34 => P109 | D35 => P109 | D36 => P108 | D37 => P108 | D38 => P107 | D39 => P107 | D40 => P106 | D41 => P106 | D42 => P105 | D43 => P105 | D44 => P104 | D45 => P104 | D46 => P103 | D47 => P103 | D48 => P102 | D49 => P102 | D50 => P101 | D51 => P101 | D52 => P100 | D53 => P100 | D54 => P99 | D55 => P99 | D56 => P98 | D57 => P98 | D58 => P97 | D59 => P97 | D60 => P96 | D61 => P96 | D62 => P95 | D63 => P95 end
    | D32 => match d0 with D0 => P127 | D1 => P127 | D2 => P126 | D3 => P126 | D4 => P125 | D5 => P125 | D6 => P124 | D7 => P124 | D8 => P123 | D9 => P123 | D10 => P122 | D11 => P122 | D12 => P121 | D13 => P121 | D14 => P120 | D15 => P120 | D16 => P119 | D17 => P119 | D18 => P118 | D19 => P118 | D20 => P117 | D21 => P117 | D22 => P116 | D23 => P116 | D24 => P115 | D25 => P115 | D26 => P114 | D27 => P114 | D28 => P113 | D29 => P113 | D30 => P112 | D31 => P112 | D32 => P111 | D33 => P111 | D34 => P110 | D35 => P110 | D36 => P109 | D37 => P109 | D38 => P108 | D39 => P108 | D40 => P107 | D41 => P107 | D42 => P106 | D43 => P106 | D44 => P105 | D45 => P105 | D46 => P104 | D47 => P104 | D48 => P103 | D49 => P103 | D50 => P102 | D51 => P102 | D52 => P101 | D53 => P101 | D54 => P100 | D55 => P100 | D56 => P99 | D57 => P99 | D58 => P98 | D59 => P98 | D60 => P97 | D61 => P97 | D62 => P96 | D63 => P96 end
    | D33 => match d0 with D0 => P0 | D1 => P0 | D2 => P127 | D3 => P127 | D4 => P126 | D5 => P126 | D6 => P125 | D7 => P125 | D8 => P124 | D9 => P124 | D10 => P123 | D11 => P123 | D12 => P122 | D13 => P122 | D14 => P121 | D15 => P121 | D16 => P120 | D17 => P120 | D18 => P119 | D19 => P119 | D20 => P118 | D21 => P118 | D22 => P117 | D23 => P117 | D24 => P116 | D25 => P116 | D26 => P115 | D27 => P115 | D28 => P114 | D29 => P114 | D30 => P113 | D31 => P113 | D32 => P112 | D33 => P112 | D34 => P111 | D35 => P111 | D36 => P110 | D37 => P110 | D38 => P109 | D39 => P109 | D40 => P108 | D41 => P108 | D42 => P107 | D43 => P107 | D44 => P106 | D45 => P106 | D46 => P105 | D47 => P105 | D48 => P104 | D49 => P104 | D50 => P103 | D51 => P103 | D52 => P102 | D53 => P102 | D54 => P101 | D55 => P101 | D56 => P100 | D57 => P100 | D58 => P99 | D59 => P99 | D60 => P98 | D61 => P98 | D62 => P97 | D63 => P97 end
    | D34 => match d0 with D0 => P1 | D1 => P1 | D2 => P0 | D3 => P0 | D4 => P127 | D5 => P127 | D6 => P126 | D7 => P126 | D8 => P125 | D9 => P125 | D10 => P124 | D11 => P124 | D12 => P123 | D13 => P123 | D14 => P122 | D15 => P122 | D16 => P121 | D17 => P121 | D18 => P120 | D19 => P120 | D20 => P119 | D21 => P119 | D22 => P118 | D23 => P118 | D24 => P117 | D25 => P117 | D26 => P116 | D27 => P116 | D28 => P115 | D29 => P115 | D30 => P114 | D31 => P114 | D32 => P113 | D33 => P113 | D34 => P112 | D35 => P112 | D36 => P111 | D37 => P111 | D38 => P110 | D39 => P110 | D40 => P109 | D41 => P109 | D42 => P108 | D43 => P108 | D44 => P107 | D45 => P107 | D46 => P106 | D47 => P106 | D48 => P105 | D49 => P105 | D50 => P104 | D51 => P104 | D52 => P103 | D53 => P103 | D54 => P102 | D55 => P102 | D56 => P101 | D57 => P101 | D58 => P100 | D59 => P100 | D60 => P99 | D61 => P99 | D62 => P98 | D63 => P98 end
    | D35 => match d0 with D0 => P2 | D1 => P2 | D2 => P1 | D3 => P1 | D4 => P0 | D5 => P0 | D6 => P127 | D7 => P127 | D8 => P126 | D9 => P126 | D10 => P125 | D11 => P125 | D12 => P124 | D13 => P124 | D14 => P123 | D15 => P123 | D16 => P122 | D17 => P122 | D18 => P121 | D19 => P121 | D20 => P120 | D21 => P120 | D22 => P119 | D23 => P119 | D24 => P118 | D25 => P118 | D26 => P117 | D27 => P117 | D28 => P116 | D29 => P116 | D30 => P115 | D31 => P115 | D32 => P114 | D33 => P114 | D34 => P113 | D35 => P113 | D36 => P112 | D37 => P112 | D38 => P111 | D39 => P111 | D40 => P110 | D41 => P110 | D42 => P109 | D43 => P109 | D44 => P108 | D45 => P108 | D46 => P107 | D47 => P107 | D48 => P106 | D49 => P106 | D50 => P105 | D51 => P105 | D52 => P104 | D53 => P104 | D54 => P103 | D55 => P103 | D56 => P102 | D57 => P102 | D58 => P101 | D59 => P101 | D60 => P100 | D61 => P100 | D62 => P99 | D63 => P99 end
    | D36 => match d0 with D0 => P3 | D1 => P3 | D2 => P2 | D3 => P2 | D4 => P1 | D5 => P1 | D6 => P0 | D7 => P0 | D8 => P127 | D9 => P127 | D10 => P126 | D11 => P126 | D12 => P125 | D13 => P125 | D14 => P124 | D15 => P124 | D16 => P123 | D17 => P123 | D18 => P122 | D19 => P122 | D20 => P121 | D21 => P121 | D22 => P120 | D23 => P120 | D24 => P119 | D25 => P119 | D26 => P118 | D27 => P118 | D28 => P117 | D29 => P117 | D30 => P116 | D31 => P116 | D32 => P115 | D33 => P115 | D34 => P114 | D35 => P114 | D36 => P113 | D37 => P113 | D38 => P112 | D39 => P112 | D40 => P111 | D41 => P111 | D42 => P110 | D43 => P110 | D44 => P109 | D45 => P109 | D46 => P108 | D47 => P108 | D48 => P107 | D49 => P107 | D50 => P106 | D51 => P106 | D52 => P105 | D53 => P105 | D54 => P104 | D55 => P104 | D56 => P103 | D57 => P103 | D58 => P102 | D59 => P102 | D60 => P101 | D61 => P101 | D62 => P100 | D63 => P100 end
    | D37 => match d0 with D0 => P4 | D1 => P4 | D2 => P3 | D3 => P3 | D4 => P2 | D5 => P2 | D6 => P1 | D7 => P1 | D8 => P0 | D9 => P0 | D10 => P127 | D11 => P127 | D12 => P126 | D13 => P126 | D14 => P125 | D15 => P125 | D16 => P124 | D17 => P124 | D18 => P123 | D19 => P123 | D20 => P122 | D21 => P122 | D22 => P121 | D23 => P121 | D24 => P120 | D25 => P120 | D26 => P119 | D27 => P119 | D28 => P118 | D29 => P118 | D30 => P117 | D31 => P117 | D32 => P116 | D33 => P116 | D34 => P115 | D35 => P115 | D36 => P114 | D37 => P114 | D38 => P113 | D39 => P113 | D40 => P112 | D41 => P112 | D42 => P111 | D43 => P111 | D44 => P110 | D45 => P110 | D46 => P109 | D47 => P109 | D48 => P108 | D49 => P108 | D50 => P107 | D51 => P107 | D52 => P106 | D53 => P106 | D54 => P105 | D55 => P105 | D56 => P104 | D57 => P104 | D58 => P103 | D59 => P103 | D60 => P102 | D61 => P102 | D62 => P101 | D63 => P101 end
    | D38 => match d0 with D0 => P5 | D1 => P5 | D2 => P4 | D3 => P4 | D4 => P3 | D5 => P3 | D6 => P2 | D7 => P2 | D8 => P1 | D9 => P1 | D10 => P0 | D11 => P0 | D12 => P127 | D13 => P127 | D14 => P126 | D15 => P126 | D16 => P125 | D17 => P125 | D18 => P124 | D19 => P124 | D20 => P123 | D21 => P123 | D22 => P122 | D23 => P122 | D24 => P121 | D25 => P121 | D26 => P120 | D27 => P120 | D28 => P119 | D29 => P119 | D30 => P118 | D31 => P118 | D32 => P117 | D33 => P117 | D34 => P116 | D35 => P116 | D36 => P115 | D37 => P115 | D38 => P114 | D39 => P114 | D40 => P113 | D41 => P113 | D42 => P112 | D43 => P112 | D44 => P111 | D45 => P111 | D46 => P110 | D47 => P110 | D48 => P109 | D49 => P109 | D50 => P108 | D51 => P108 | D52 => P107 | D53 => P107 | D54 => P106 | D55 => P106 | D56 => P105 | D57 => P105 | D58 => P104 | D59 => P104 | D60 => P103 | D61 => P103 | D62 => P102 | D63 => P102 end
    | D39 => match d0 with D0 => P6 | D1 => P6 | D2 => P5 | D3 => P5 | D4 => P4 | D5 => P4 | D6 => P3 | D7 => P3 | D8 => P2 | D9 => P2 | D10 => P1 | D11 => P1 | D12 => P0 | D13 => P0 | D14 => P127 | D15 => P127 | D16 => P126 | D17 => P126 | D18 => P125 | D19 => P125 | D20 => P124 | D21 => P124 | D22 => P123 | D23 => P123 | D24 => P122 | D25 => P122 | D26 => P121 | D27 => P121 | D28 => P120 | D29 => P120 | D30 => P119 | D31 => P119 | D32 => P118 | D33 => P118 | D34 => P117 | D35 => P117 | D36 => P116 | D37 => P116 | D38 => P115 | D39 => P115 | D40 => P114 | D41 => P114 | D42 => P113 | D43 => P113 | D44 => P112 | D45 => P112 | D46 => P111 | D47 => P111 | D48 => P110 | D49 => P110 | D50 => P109 | D51 => P109 | D52 => P108 | D53 => P108 | D54 => P107 | D55 => P107 | D56 => P106 | D57 => P106 | D58 => P105 | D59 => P105 | D60 => P104 | D61 => P104 | D62 => P103 | D63 => P103 end
    | D40 => match d0 with D0 => P7 | D1 => P7 | D2 => P6 | D3 => P6 | D4 => P5 | D5 => P5 | D6 => P4 | D7 => P4 | D8 => P3 | D9 => P3 | D10 => P2 | D11 => P2 | D12 => P1 | D13 => P1 | D14 => P0 | D15 => P0 | D16 => P127 | D17 => P127 | D18 => P126 | D19 => P126 | D20 => P125 | D21 => P125 | D22 => P124 | D23 => P124 | D24 => P123 | D25 => P123 | D26 => P122 | D27 => P122 | D28 => P121 | D29 => P121 | D30 => P120 | D31 => P120 | D32 => P119 | D33 => P119 | D34 => P118 | D35 => P118 | D36 => P117 | D37 => P117 | D38 => P116 | D39 => P116 | D40 => P115 | D41 => P115 | D42 => P114 | D43 => P114 | D44 => P113 | D45 => P113 | D46 => P112 | D47 => P112 | D48 => P111 | D49 => P111 | D50 => P110 | D51 => P110 | D52 => P109 | D53 => P109 | D54 => P108 | D55 => P108 | D56 => P107 | D57 => P107 | D58 => P106 | D59 => P106 | D60 => P105 | D61 => P105 | D62 => P104 | D63 => P104 end
    | D41 => match d0 with D0 => P8 | D1 => P8 | D2 => P7 | D3 => P7 | D4 => P6 | D5 => P6 | D6 => P5 | D7 => P5 | D8 => P4 | D9 => P4 | D10 => P3 | D11 => P3 | D12 => P2 | D13 => P2 | D14 => P1 | D15 => P1 | D16 => P0 | D17 => P0 | D18 => P127 | D19 => P127 | D20 => P126 | D21 => P126 | D22 => P125 | D23 => P125 | D24 => P124 | D25 => P124 | D26 => P123 | D27 => P123 | D28 => P122 | D29 => P122 | D30 => P121 | D31 => P121 | D32 => P120 | D33 => P120 | D34 => P119 | D35 => P119 | D36 => P118 | D37 => P118 | D38 => P117 | D39 => P117 | D40 => P116 | D41 => P116 | D42 => P115 | D43 => P115 | D44 => P114 | D45 => P114 | D46 => P113 | D47 => P113 | D48 => P112 | D49 => P112 | D50 => P111 | D51 => P111 | D52 => P110 | D53 => P110 | D54 => P109 | D55 => P109 | D56 => P108 | D57 => P108 | D58 => P107 | D59 => P107 | D60 => P106 | D61 => P106 | D62 => P105 | D63 => P105 end
    | D42 => match d0 with D0 => P9 | D1 => P9 | D2 => P8 | D3 => P8 | D4 => P7 | D5 => P7 | D6 => P6 | D7 => P6 | D8 => P5 | D9 => P5 | D10 => P4 | D11 => P4 | D12 => P3 | D13 => P3 | D14 => P2 | D15 => P2 | D16 => P1 | D17 => P1 | D18 => P0 | D19 => P0 | D20 => P127 | D21 => P127 | D22 => P126 | D23 => P126 | D24 => P125 | D25 => P125 | D26 => P124 | D27 => P124 | D28 => P123 | D29 => P123 | D30 => P122 | D31 => P122 | D32 => P121 | D33 => P121 | D34 => P120 | D35 => P120 | D36 => P119 | D37 => P119 | D38 => P118 | D39 => P118 | D40 => P117 | D41 => P117 | D42 => P116 | D43 => P116 | D44 => P115 | D45 => P115 | D46 => P114 | D47 => P114 | D48 => P113 | D49 => P113 | D50 => P112 | D51 => P112 | D52 => P111 | D53 => P111 | D54 => P110 | D55 => P110 | D56 => P109 | D57 => P109 | D58 => P108 | D59 => P108 | D60 => P107 | D61 => P107 | D62 => P106 | D63 => P106 end
    | D43 => match d0 with D0 => P10 | D1 => P10 | D2 => P9 | D3 => P9 | D4 => P8 | D5 => P8 | D6 => P7 | D7 => P7 | D8 => P6 | D9 => P6 | D10 => P5 | D11 => P5 | D12 => P4 | D13 => P4 | D14 => P3 | D15 => P3 | D16 => P2 | D17 => P2 | D18 => P1 | D19 => P1 | D20 => P0 | D21 => P0 | D22 => P127 | D23 => P127 | D24 => P126 | D25 => P126 | D26 => P125 | D27 => P125 | D28 => P124 | D29 => P124 | D30 => P123 | D31 => P123 | D32 => P122 | D33 => P122 | D34 => P121 | D35 => P121 | D36 => P120 | D37 => P120 | D38 => P119 | D39 => P119 | D40 => P118 | D41 => P118 | D42 => P117 | D43 => P117 | D44 => P116 | D45 => P116 | D46 => P115 | D47 => P115 | D48 => P114 | D49 => P114 | D50 => P113 | D51 => P113 | D52 => P112 | D53 => P112 | D54 => P111 | D55 => P111 | D56 => P110 | D57 => P110 | D58 => P109 | D59 => P109 | D60 => P108 | D61 => P108 | D62 => P107 | D63 => P107 end
    | D44 => match d0 with D0 => P11 | D1 => P11 | D2 => P10 | D3 => P10 | D4 => P9 | D5 => P9 | D6 => P8 | D7 => P8 | D8 => P7 | D9 => P7 | D10 => P6 | D11 => P6 | D12 => P5 | D13 => P5 | D14 => P4 | D15 => P4 | D16 => P3 | D17 => P3 | D18 => P2 | D19 => P2 | D20 => P1 | D21 => P1 | D22 => P0 | D23 => P0 | D24 => P127 | D25 => P127 | D26 => P126 | D27 => P126 | D28 => P125 | D29 => P125 | D30 => P124 | D31 => P124 | D32 => P123 | D33 => P123 | D34 => P122 | D35 => P122 | D36 => P121 | D37 => P121 | D38 => P120 | D39 => P120 | D40 => P119 | D41 => P119 | D42 => P118 | D43 => P118 | D44 => P117 | D45 => P117 | D46 => P116 | D47 => P116 | D48 => P115 | D49 => P115 | D50 => P114 | D51 => P114 | D52 => P113 | D53 => P113 | D54 => P112 | D55 => P112 | D56 => P111 | D57 => P111 | D58 => P110 | D59 => P110 | D60 => P109 | D61 => P109 | D62 => P108 | D63 => P108 end
    | D45 => match d0 with D0 => P12 | D1 => P12 | D2 => P11 | D3 => P11 | D4 => P10 | D5 => P10 | D6 => P9 | D7 => P9 | D8 => P8 | D9 => P8 | D10 => P7 | D11 => P7 | D12 => P6 | D13 => P6 | D14 => P5 | D15 => P5 | D16 => P4 | D17 => P4 | D18 => P3 | D19 => P3 | D20 => P2 | D21 => P2 | D22 => P1 | D23 => P1 | D24 => P0 | D25 => P0 | D26 => P127 | D27 => P127 | D28 => P126 | D29 => P126 | D30 => P125 | D31 => P125 | D32 => P124 | D33 => P124 | D34 => P123 | D35 => P123 | D36 => P122 | D37 => P122 | D38 => P121 | D39 => P121 | D40 => P120 | D41 => P120 | D42 => P119 | D43 => P119 | D44 => P118 | D45 => P118 | D46 => P117 | D47 => P117 | D48 => P116 | D49 => P116 | D50 => P115 | D51 => P115 | D52 => P114 | D53 => P114 | D54 => P113 | D55 => P113 | D56 => P112 | D57 => P112 | D58 => P111 | D59 => P111 | D60 => P110 | D61 => P110 | D62 => P109 | D63 => P109 end
    | D46 => match d0 with D0 => P13 | D1 => P13 | D2 => P12 | D3 => P12 | D4 => P11 | D5 => P11 | D6 => P10 | D7 => P10 | D8 => P9 | D9 => P9 | D10 => P8 | D11 => P8 | D12 => P7 | D13 => P7 | D14 => P6 | D15 => P6 | D16 => P5 | D17 => P5 | D18 => P4 | D19 => P4 | D20 => P3 | D21 => P3 | D22 => P2 | D23 => P2 | D24 => P1 | D25 => P1 | D26 => P0 | D27 => P0 | D28 => P127 | D29 => P127 | D30 => P126 | D31 => P126 | D32 => P125 | D33 => P125 | D34 => P124 | D35 => P124 | D36 => P123 | D37 => P123 | D38 => P122 | D39 => P122 | D40 => P121 | D41 => P121 | D42 => P120 | D43 => P120 | D44 => P119 | D45 => P119 | D46 => P118 | D47 => P118 | D48 => P117 | D49 => P117 | D50 => P116 | D51 => P116 | D52 => P115 | D53 => P115 | D54 => P114 | D55 => P114 | D56 => P113 | D57 => P113 | D58 => P112 | D59 => P112 | D60 => P111 | D61 => P111 | D62 => P110 | D63 => P110 end
    | D47 => match d0 with D0 => P14 | D1 => P14 | D2 => P13 | D3 => P13 | D4 => P12 | D5 => P12 | D6 => P11 | D7 => P11 | D8 => P10 | D9 => P10 | D10 => P9 | D11 => P9 | D12 => P8 | D13 => P8 | D14 => P7 | D15 => P7 | D16 => P6 | D17 => P6 | D18 => P5 | D19 => P5 | D20 => P4 | D21 => P4 | D22 => P3 | D23 => P3 | D24 => P2 | D25 => P2 | D26 => P1 | D27 => P1 | D28 => P0 | D29 => P0 | D30 => P127 | D31 => P127 | D32 => P126 | D33 => P126 | D34 => P125 | D35 => P125 | D36 => P124 | D37 => P124 | D38 => P123 | D39 => P123 | D40 => P122 | D41 => P122 | D42 => P121 | D43 => P121 | D44 => P120 | D45 => P120 | D46 => P119 | D47 => P119 | D48 => P118 | D49 => P118 | D50 => P117 | D51 => P117 | D52 => P116 | D53 => P116 | D54 => P115 | D55 => P115 | D56 => P114 | D57 => P114 | D58 => P113 | D59 => P113 | D60 => P112 | D61 => P112 | D62 => P111 | D63 => P111 end
    | D48 => match d0 with D0 => P15 | D1 => P15 | D2 => P14 | D3 => P14 | D4 => P13 | D5 => P13 | D6 => P12 | D7 => P12 | D8 => P11 | D9 => P11 | D10 => P10 | D11 => P10 | D12 => P9 | D13 => P9 | D14 => P8 | D15 => P8 | D16 => P7 | D17 => P7 | D18 => P6 | D19 => P6 | D20 => P5 | D21 => P5 | D22 => P4 | D23 => P4 | D24 => P3 | D25 => P3 | D26 => P2 | D27 => P2 | D28 => P1 | D29 => P1 | D30 => P0 | D31 => P0 | D32 => P127 | D33 => P127 | D34 => P126 | D35 => P126 | D36 => P125 | D37 => P125 | D38 => P124 | D39 => P124 | D40 => P123 | D41 => P123 | D42 => P122 | D43 => P122 | D44 => P121 | D45 => P121 | D46 => P120 | D47 => P120 | D48 => P119 | D49 => P119 | D50 => P118 | D51 => P118 | D52 => P117 | D53 => P117 | D54 => P116 | D55 => P116 | D56 => P115 | D57 => P115 | D58 => P114 | D59 => P114 | D60 => P113 | D61 => P113 | D62 => P112 | D63 => P112 end
    | D49 => match d0 with D0 => P16 | D1 => P16 | D2 => P15 | D3 => P15 | D4 => P14 | D5 => P14 | D6 => P13 | D7 => P13 | D8 => P12 | D9 => P12 | D10 => P11 | D11 => P11 | D12 => P10 | D13 => P10 | D14 => P9 | D15 => P9 | D16 => P8 | D17 => P8 | D18 => P7 | D19 => P7 | D20 => P6 | D21 => P6 | D22 => P5 | D23 => P5 | D24 => P4 | D25 => P4 | D26 => P3 | D27 => P3 | D28 => P2 | D29 => P2 | D30 => P1 | D31 => P1 | D32 => P0 | D33 => P0 | D34 => P127 | D35 => P127 | D36 => P126 | D37 => P126 | D38 => P125 | D39 => P125 | D40 => P124 | D41 => P124 | D42 => P123 | D43 => P123 | D44 => P122 | D45 => P122 | D46 => P121 | D47 => P121 | D48 => P120 | D49 => P120 | D50 => P119 | D51 => P119 | D52 => P118 | D53 => P118 | D54 => P117 | D55 => P117 | D56 => P116 | D57 => P116 | D58 => P115 | D59 => P115 | D60 => P114 | D61 => P114 | D62 => P113 | D63 => P113 end
    | D50 => match d0 with D0 => P17 | D1 => P17 | D2 => P16 | D3 => P16 | D4 => P15 | D5 => P15 | D6 => P14 | D7 => P14 | D8 => P13 | D9 => P13 | D10 => P12 | D11 => P12 | D12 => P11 | D13 => P11 | D14 => P10 | D15 => P10 | D16 => P9 | D17 => P9 | D18 => P8 | D19 => P8 | D20 => P7 | D21 => P7 | D22 => P6 | D23 => P6 | D24 => P5 | D25 => P5 | D26 => P4 | D27 => P4 | D28 => P3 | D29 => P3 | D30 => P2 | D31 => P2 | D32 => P1 | D33 => P1 | D34 => P0 | D35 => P0 | D36 => P127 | D37 => P127 | D38 => P126 | D39 => P126 | D40 => P125 | D41 => P125 | D42 => P124 | D43 => P124 | D44 => P123 | D45 => P123 | D46 => P122 | D47 => P122 | D48 => P121 | D49 => P121 | D50 => P120 | D51 => P120 | D52 => P119 | D53 => P119 | D54 => P118 | D55 => P118 | D56 => P117 | D57 => P117 | D58 => P116 | D59 => P116 | D60 => P115 | D61 => P115 | D62 => P114 | D63 => P114 end
    | D51 => match d0 with D0 => P18 | D1 => P18 | D2 => P17 | D3 => P17 | D4 => P16 | D5 => P16 | D6 => P15 | D7 => P15 | D8 => P14 | D9 => P14 | D10 => P13 | D11 => P13 | D12 => P12 | D13 => P12 | D14 => P11 | D15 => P11 | D16 => P10 | D17 => P10 | D18 => P9 | D19 => P9 | D20 => P8 | D21 => P8 | D22 => P7 | D23 => P7 | D24 => P6 | D25 => P6 | D26 => P5 | D27 => P5 | D28 => P4 | D29 => P4 | D30 => P3 | D31 => P3 | D32 => P2 | D33 => P2 | D34 => P1 | D35 => P1 | D36 => P0 | D37 => P0 | D38 => P127 | D39 => P127 | D40 => P126 | D41 => P126 | D42 => P125 | D43 => P125 | D44 => P124 | D45 => P124 | D46 => P123 | D47 => P123 | D48 => P122 | D49 => P122 | D50 => P121 | D51 => P121 | D52 => P120 | D53 => P120 | D54 => P119 | D55 => P119 | D56 => P118 | D57 => P118 | D58 => P117 | D59 => P117 | D60 => P116 | D61 => P116 | D62 => P115 | D63 => P115 end
    | D52 => match d0 with D0 => P19 | D1 => P19 | D2 => P18 | D3 => P18 | D4 => P17 | D5 => P17 | D6 => P16 | D7 => P16 | D8 => P15 | D9 => P15 | D10 => P14 | D11 => P14 | D12 => P13 | D13 => P13 | D14 => P12 | D15 => P12 | D16 => P11 | D17 => P11 | D18 => P10 | D19 => P10 | D20 => P9 | D21 => P9 | D22 => P8 | D23 => P8 | D24 => P7 | D25 => P7 | D26 => P6 | D27 => P6 | D28 => P5 | D29 => P5 | D30 => P4 | D31 => P4 | D32 => P3 | D33 => P3 | D34 => P2 | D35 => P2 | D36 => P1 | D37 => P1 | D38 => P0 | D39 => P0 | D40 => P127 | D41 => P127 | D42 => P126 | D43 => P126 | D44 => P125 | D45 => P125 | D46 => P124 | D47 => P124 | D48 => P123 | D49 => P123 | D50 => P122 | D51 => P122 | D52 => P121 | D53 => P121 | D54 => P120 | D55 => P120 | D56 => P119 | D57 => P119 | D58 => P118 | D59 => P118 | D60 => P117 | D61 => P117 | D62 => P116 | D63 => P116 end
    | D53 => match d0 with D0 => P20 | D1 => P20 | D2 => P19 | D3 => P19 | D4 => P18 | D5 => P18 | D6 => P17 | D7 => P17 | D8 => P16 | D9 => P16 | D10 => P15 | D11 => P15 | D12 => P14 | D13 => P14 | D14 => P13 | D15 => P13 | D16 => P12 | D17 => P12 | D18 => P11 | D19 => P11 | D20 => P10 | D21 => P10 | D22 => P9 | D23 => P9 | D24 => P8 | D25 => P8 | D26 => P7 | D27 => P7 | D28 => P6 | D29 => P6 | D30 => P5 | D31 => P5 | D32 => P4 | D33 => P4 | D34 => P3 | D35 => P3 | D36 => P2 | D37 => P2 | D38 => P1 | D39 => P1 | D40 => P0 | D41 => P0 | D42 => P127 | D43 => P127 | D44 => P126 | D45 => P126 | D46 => P125 | D47 => P125 | D48 => P124 | D49 => P124 | D50 => P123 | D51 => P123 | D52 => P122 | D53 => P122 | D54 => P121 | D55 => P121 | D56 => P120 | D57 => P120 | D58 => P119 | D59 => P119 | D60 => P118 | D61 => P118 | D62 => P117 | D63 => P117 end
    | D54 => match d0 with D0 => P21 | D1 => P21 | D2 => P20 | D3 => P20 | D4 => P19 | D5 => P19 | D6 => P18 | D7 => P18 | D8 => P17 | D9 => P17 | D10 => P16 | D11 => P16 | D12 => P15 | D13 => P15 | D14 => P14 | D15 => P14 | D16 => P13 | D17 => P13 | D18 => P12 | D19 => P12 | D20 => P11 | D21 => P11 | D22 => P10 | D23 => P10 | D24 => P9 | D25 => P9 | D26 => P8 | D27 => P8 | D28 => P7 | D29 => P7 | D30 => P6 | D31 => P6 | D32 => P5 | D33 => P5 | D34 => P4 | D35 => P4 | D36 => P3 | D37 => P3 | D38 => P2 | D39 => P2 | D40 => P1 | D41 => P1 | D42 => P0 | D43 => P0 | D44 => P127 | D45 => P127 | D46 => P126 | D47 => P126 | D48 => P125 | D49 => P125 | D50 => P124 | D51 => P124 | D52 => P123 | D53 => P123 | D54 => P122 | D55 => P122 | D56 => P121 | D57 => P121 | D58 => P120 | D59 => P120 | D60 => P119 | D61 => P119 | D62 => P118 | D63 => P118 end
    | D55 => match d0 with D0 => P22 | D1 => P22 | D2 => P21 | D3 => P21 | D4 => P20 | D5 => P20 | D6 => P19 | D7 => P19 | D8 => P18 | D9 => P18 | D10 => P17 | D11 => P17 | D12 => P16 | D13 => P16 | D14 => P15 | D15 => P15 | D16 => P14 | D17 => P14 | D18 => P13 | D19 => P13 | D20 => P12 | D21 => P12 | D22 => P11 | D23 => P11 | D24 => P10 | D25 => P10 | D26 => P9 | D27 => P9 | D28 => P8 | D29 => P8 | D30 => P7 | D31 => P7 | D32 => P6 | D33 => P6 | D34 => P5 | D35 => P5 | D36 => P4 | D37 => P4 | D38 => P3 | D39 => P3 | D40 => P2 | D41 => P2 | D42 => P1 | D43 => P1 | D44 => P0 | D45 => P0 | D46 => P127 | D47 => P127 | D48 => P126 | D49 => P126 | D50 => P125 | D51 => P125 | D52 => P124 | D53 => P124 | D54 => P123 | D55 => P123 | D56 => P122 | D57 => P122 | D58 => P121 | D59 => P121 | D60 => P120 | D61 => P120 | D62 => P119 | D63 => P119 end
    | D56 => match d0 with D0 => P23 | D1 => P23 | D2 => P22 | D3 => P22 | D4 => P21 | D5 => P21 | D6 => P20 | D7 => P20 | D8 => P19 | D9 => P19 | D10 => P18 | D11 => P18 | D12 => P17 | D13 => P17 | D14 => P16 | D15 => P16 | D16 => P15 | D17 => P15 | D18 => P14 | D19 => P14 | D20 => P13 | D21 => P13 | D22 => P12 | D23 => P12 | D24 => P11 | D25 => P11 | D26 => P10 | D27 => P10 | D28 => P9 | D29 => P9 | D30 => P8 | D31 => P8 | D32 => P7 | D33 => P7 | D34 => P6 | D35 => P6 | D36 => P5 | D37 => P5 | D38 => P4 | D39 => P4 | D40 => P3 | D41 => P3 | D42 => P2 | D43 => P2 | D44 => P1 | D45 => P1 | D46 => P0 | D47 => P0 | D48 => P127 | D49 => P127 | D50 => P126 | D51 => P126 | D52 => P125 | D53 => P125 | D54 => P124 | D55 => P124 | D56 => P123 | D57 => P123 | D58 => P122 | D59 => P122 | D60 => P121 | D61 => P121 | D62 => P120 | D63 => P120 end
    | D57 => match d0 with D0 => P24 | D1 => P24 | D2 => P23 | D3 => P23 | D4 => P22 | D5 => P22 | D6 => P21 | D7 => P21 | D8 => P20 | D9 => P20 | D10 => P19 | D11 => P19 | D12 => P18 | D13 => P18 | D14 => P17 | D15 => P17 | D16 => P16 | D17 => P16 | D18 => P15 | D19 => P15 | D20 => P14 | D21 => P14 | D22 => P13 | D23 => P13 | D24 => P12 | D25 => P12 | D26 => P11 | D27 => P11 | D28 => P10 | D29 => P10 | D30 => P9 | D31 => P9 | D32 => P8 | D33 => P8 | D34 => P7 | D35 => P7 | D36 => P6 | D37 => P6 | D38 => P5 | D39 => P5 | D40 => P4 | D41 => P4 | D42 => P3 | D43 => P3 | D44 => P2 | D45 => P2 | D46 => P1 | D47 => P1 | D48 => P0 | D49 => P0 | D50 => P127 | D51 => P127 | D52 => P126 | D53 => P126 | D54 => P125 | D55 => P125 | D56 => P124 | D57 => P124 | D58 => P123 | D59 => P123 | D60 => P122 | D61 => P122 | D62 => P121 | D63 => P121 end
    | D58 => match d0 with D0 => P25 | D1 => P25 | D2 => P24 | D3 => P24 | D4 => P23 | D5 => P23 | D6 => P22 | D7 => P22 | D8 => P21 | D9 => P21 | D10 => P20 | D11 => P20 | D12 => P19 | D13 => P19 | D14 => P18 | D15 => P18 | D16 => P17 | D17 => P17 | D18 => P16 | D19 => P16 | D20 => P15 | D21 => P15 | D22 => P14 | D23 => P14 | D24 => P13 | D25 => P13 | D26 => P12 | D27 => P12 | D28 => P11 | D29 => P11 | D30 => P10 | D31 => P10 | D32 => P9 | D33 => P9 | D34 => P8 | D35 => P8 | D36 => P7 | D37 => P7 | D38 => P6 | D39 => P6 | D40 => P5 | D41 => P5 | D42 => P4 | D43 => P4 | D44 => P3 | D45 => P3 | D46 => P2 | D47 => P2 | D48 => P1 | D49 => P1 | D50 => P0 | D51 => P0 | D52 => P127 | D53 => P127 | D54 => P126 | D55 => P126 | D56 => P125 | D57 => P125 | D58 => P124 | D59 => P124 | D60 => P123 | D61 => P123 | D62 => P122 | D63 => P122 end
    | D59 => match d0 with D0 => P26 | D1 => P26 | D2 => P25 | D3 => P25 | D4 => P24 | D5 => P24 | D6 => P23 | D7 => P23 | D8 => P22 | D9 => P22 | D10 => P21 | D11 => P21 | D12 => P20 | D13 => P20 | D14 => P19 | D15 => P19 | D16 => P18 | D17 => P18 | D18 => P17 | D19 => P17 | D20 => P16 | D21 => P16 | D22 => P15 | D23 => P15 | D24 => P14 | D25 => P14 | D26 => P13 | D27 => P13 | D28 => P12 | D29 => P12 | D30 => P11 | D31 => P11 | D32 => P10 | D33 => P10 | D34 => P9 | D35 => P9 | D36 => P8 | D37 => P8 | D38 => P7 | D39 => P7 | D40 => P6 | D41 => P6 | D42 => P5 | D43 => P5 | D44 => P4 | D45 => P4 | D46 => P3 | D47 => P3 | D48 => P2 | D49 => P2 | D50 => P1 | D51 => P1 | D52 => P0 | D53 => P0 | D54 => P127 | D55 => P127 | D56 => P126 | D57 => P126 | D58 => P125 | D59 => P125 | D60 => P124 | D61 => P124 | D62 => P123 | D63 => P123 end
    | D60 => match d0 with D0 => P27 | D1 => P27 | D2 => P26 | D3 => P26 | D4 => P25 | D5 => P25 | D6 => P24 | D7 => P24 | D8 => P23 | D9 => P23 | D10 => P22 | D11 => P22 | D12 => P21 | D13 => P21 | D14 => P20 | D15 => P20 | D16 => P19 | D17 => P19 | D18 => P18 | D19 => P18 | D20 => P17 | D21 => P17 | D22 => P16 | D23 => P16 | D24 => P15 | D25 => P15 | D26 => P14 | D27 => P14 | D28 => P13 | D29 => P13 | D30 => P12 | D31 => P12 | D32 => P11 | D33 => P11 | D34 => P10 | D35 => P10 | D36 => P9 | D37 => P9 | D38 => P8 | D39 => P8 | D40 => P7 | D41 => P7 | D42 => P6 | D43 => P6 | D44 => P5 | D45 => P5 | D46 => P4 | D47 => P4 | D48 => P3 | D49 => P3 | D50 => P2 | D51 => P2 | D52 => P1 | D53 => P1 | D54 => P0 | D55 => P0 | D56 => P127 | D57 => P127 | D58 => P126 | D59 => P126 | D60 => P125 | D61 => P125 | D62 => P124 | D63 => P124 end
    | D61 => match d0 with D0 => P28 | D1 => P28 | D2 => P27 | D3 => P27 | D4 => P26 | D5 => P26 | D6 => P25 | D7 => P25 | D8 => P24 | D9 => P24 | D10 => P23 | D11 => P23 | D12 => P22 | D13 => P22 | D14 => P21 | D15 => P21 | D16 => P20 | D17 => P20 | D18 => P19 | D19 => P19 | D20 => P18 | D21 => P18 | D22 => P17 | D23 => P17 | D24 => P16 | D25 => P16 | D26 => P15 | D27 => P15 | D28 => P14 | D29 => P14 | D30 => P13 | D31 => P13 | D32 => P12 | D33 => P12 | D34 => P11 | D35 => P11 | D36 => P10 | D37 => P10 | D38 => P9 | D39 => P9 | D40 => P8 | D41 => P8 | D42 => P7 | D43 => P7 | D44 => P6 | D45 => P6 | D46 => P5 | D47 => P5 | D48 => P4 | D49 => P4 | D50 => P3 | D51 => P3 | D52 => P2 | D53 => P2 | D54 => P1 | D55 => P1 | D56 => P0 | D57 => P0 | D58 => P127 | D59 => P127 | D60 => P126 | D61 => P126 | D62 => P125 | D63 => P125 end
    | D62 => match d0 with D0 => P29 | D1 => P29 | D2 => P28 | D3 => P28 | D4 => P27 | D5 => P27 | D6 => P26 | D7 => P26 | D8 => P25 | D9 => P25 | D10 => P24 | D11 => P24 | D12 => P23 | D13 => P23 | D14 => P22 | D15 => P22 | D16 => P21 | D17 => P21 | D18 => P20 | D19 => P20 | D20 => P19 | D21 => P19 | D22 => P18 | D23 => P18 | D24 => P17 | D25 => P17 | D26 => P16 | D27 => P16 | D28 => P15 | D29 => P15 | D30 => P14 | D31 => P14 | D32 => P13 | D33 => P13 | D34 => P12 | D35 => P12 | D36 => P11 | D37 => P11 | D38 => P10 | D39 => P10 | D40 => P9 | D41 => P9 | D42 => P8 | D43 => P8 | D44 => P7 | D45 => P7 | D46 => P6 | D47 => P6 | D48 => P5 | D49 => P5 | D50 => P4 | D51 => P4 | D52 => P3 | D53 => P3 | D54 => P2 | D55 => P2 | D56 => P1 | D57 => P1 | D58 => P0 | D59 => P0 | D60 => P127 | D61 => P127 | D62 => P126 | D63 => P126 end
    | D63 => match d0 with D0 => P30 | D1 => P30 | D2 => P29 | D3 => P29 | D4 => P28 | D5 => P28 | D6 => P27 | D7 => P27 | D8 => P26 | D9 => P26 | D10 => P25 | D11 => P25 | D12 => P24 | D13 => P24 | D14 => P23 | D15 => P23 | D16 => P22 | D17 => P22 | D18 => P21 | D19 => P21 | D20 => P20 | D21 => P20 | D22 => P19 | D23 => P19 | D24 => P18 | D25 => P18 | D26 => P17 | D27 => P17 | D28 => P16 | D29 => P16 | D30 => P15 | D31 => P15 | D32 => P14 | D33 => P14 | D34 => P13 | D35 => P13 | D36 => P12 | D37 => P12 | D38 => P11 | D39 => P11 | D40 => P10 | D41 => P10 | D42 => P9 | D43 => P9 | D44 => P8 | D45 => P8 | D46 => P7 | D47 => P7 | D48 => P6 | D49 => P6 | D50 => P5 | D51 => P5 | D52 => P4 | D53 => P4 | D54 => P3 | D55 => P3 | D56 => P2 | D57 => P2 | D58 => P1 | D59 => P1 | D60 => P0 | D61 => P0 | D62 => P127 | D63 => P127 end
    end else match a with
    | D0 => match d0 with D0 => P127 | D1 => P127 | D2 => P126 | D3 => P126 | D4 => P125 | D5 => P125 | D6 => P124 | D7 => P124 | D8 => P123 | D9 => P123 | D10 => P122 | D11 => P122 | D12 => P121 | D13 => P121 | D14 => P120 | D15 => P120 | D16 => P119 | D17 => P119 | D18 => P118 | D19 => P118 | D20 => P117 | D21 => P117 | D22 => P116 | D23 => P116 | D24 => P115 | D25 => P115 | D26 => P114 | D27 => P114 | D28 => P113 | D29 => P113 | D30 => P112 | D31 => P112 | D32 => P111 | D33 => P111 | D34 => P110 | D35 => P110 | D36 => P109 | D37 => P109 | D38 => P108 | D39 => P108 | D40 => P107 | D41 => P107 | D42 => P106 | D43 => P106 | D44 => P105 | D45 => P105 | D46 => P104 | D47 => P104 | D48 => P103 | D49 => P103 | D50 => P102 | D51 => P102 | D52 => P101 | D53 => P101 | D54 => P100 | D55 => P100 | D56 => P99 | D57 => P99 | D58 => P98 | D59 => P98 | D60 => P97 | D61 => P97 | D62 => P96 | D63 => P96 end
    | D1 => match d0 with D0 => P0 | D1 => P0 | D2 => P127 | D3 => P127 | D4 => P126 | D5 => P126 | D6 => P125 | D7 => P125 | D8 => P124 | D9 => P124 | D10 => P123 | D11 => P123 | D12 => P122 | D13 => P122 | D14 => P121 | D15 => P121 | D16 => P120 | D17 => P120 | D18 => P119 | D19 => P119 | D20 => P118 | D21 => P118 | D22 => P117 | D23 => P117 | D24 => P116 | D25 => P116 | D26 => P115 | D27 => P115 | D28 => P114 | D29 => P114 | D30 => P113 | D31 => P113 | D32 => P112 | D33 => P112 | D34 => P111 | D35 => P111 | D36 => P110 | D37 => P110 | D38 => P109 | D39 => P109 | D40 => P108 | D41 => P108 | D42 => P107 | D43 => P107 | D44 => P106 | D45 => P106 | D46 => P105 | D47 => P105 | D48 => P104 | D49 => P104 | D50 => P103 | D51 => P103 | D52 => P102 | D53 => P102 | D54 => P101 | D55 => P101 | D56 => P100 | D57 => P100 | D58 => P99 | D59 => P99 | D60 => P98 | D61 => P98 | D62 => P97 | D63 => P97 end
    | D2 => match d0 with D0 => P1 | D1 => P1 | D2 => P0 | D3 => P0 | D4 => P127 | D5 => P127 | D6 => P126 | D7 => P126 | D8 => P125 | D9 => P125 | D10 => P124 | D11 => P124 | D12 => P123 | D13 => P123 | D14 => P122 | D15 => P122 | D16 => P121 | D17 => P121 | D18 => P120 | D19 => P120 | D20 => P119 | D21 => P119 | D22 => P118 | D23 => P118 | D24 => P117 | D25 => P117 | D26 => P116 | D27 => P116 | D28 => P115 | D29 => P115 | D30 => P114 | D31 => P114 | D32 => P113 | D33 => P113 | D34 => P112 | D35 => P112 | D36 => P111 | D37 => P111 | D38 => P110 | D39 => P110 | D40 => P109 | D41 => P109 | D42 => P108 | D43 => P108 | D44 => P107 | D45 => P107 | D46 => P106 | D47 => P106 | D48 => P105 | D49 => P105 | D50 => P104 | D51 => P104 | D52 => P103 | D53 => P103 | D54 => P102 | D55 => P102 | D56 => P101 | D57 => P101 | D58 => P100 | D59 => P100 | D60 => P99 | D61 => P99 | D62 => P98 | D63 => P98 end
    | D3 => match d0 with D0 => P2 | D1 => P2 | D2 => P1 | D3 => P1 | D4 => P0 | D5 => P0 | D6 => P127 | D7 => P127 | D8 => P126 | D9 => P126 | D10 => P125 | D11 => P125 | D12 => P124 | D13 => P124 | D14 => P123 | D15 => P123 | D16 => P122 | D17 => P122 | D18 => P121 | D19 => P121 | D20 => P120 | D21 => P120 | D22 => P119 | D23 => P119 | D24 => P118 | D25 => P118 | D26 => P117 | D27 => P117 | D28 => P116 | D29 => P116 | D30 => P115 | D31 => P115 | D32 => P114 | D33 => P114 | D34 => P113 | D35 => P113 | D36 => P112 | D37 => P112 | D38 => P111 | D39 => P111 | D40 => P110 | D41 => P110 | D42 => P109 | D43 => P109 | D44 => P108 | D45 => P108 | D46 => P107 | D47 => P107 | D48 => P106 | D49 => P106 | D50 => P105 | D51 => P105 | D52 => P104 | D53 => P104 | D54 => P103 | D55 => P103 | D56 => P102 | D57 => P102 | D58 => P101 | D59 => P101 | D60 => P100 | D61 => P100 | D62 => P99 | D63 => P99 end
    | D4 => match d0 with D0 => P3 | D1 => P3 | D2 => P2 | D3 => P2 | D4 => P1 | D5 => P1 | D6 => P0 | D7 => P0 | D8 => P127 | D9 => P127 | D10 => P126 | D11 => P126 | D12 => P125 | D13 => P125 | D14 => P124 | D15 => P124 | D16 => P123 | D17 => P123 | D18 => P122 | D19 => P122 | D20 => P121 | D21 => P121 | D22 => P120 | D23 => P120 | D24 => P119 | D25 => P119 | D26 => P118 | D27 => P118 | D28 => P117 | D29 => P117 | D30 => P116 | D31 => P116 | D32 => P115 | D33 => P115 | D34 => P114 | D35 => P114 | D36 => P113 | D37 => P113 | D38 => P112 | D39 => P112 | D40 => P111 | D41 => P111 | D42 => P110 | D43 => P110 | D44 => P109 | D45 => P109 | D46 => P108 | D47 => P108 | D48 => P107 | D49 => P107 | D50 => P106 | D51 => P106 | D52 => P105 | D53 => P105 | D54 => P104 | D55 => P104 | D56 => P103 | D57 => P103 | D58 => P102 | D59 => P102 | D60 => P101 | D61 => P101 | D62 => P100 | D63 => P100 end
    | D5 => match d0 with D0 => P4 | D1 => P4 | D2 => P3 | D3 => P3 | D4 => P2 | D5 => P2 | D6 => P1 | D7 => P1 | D8 => P0 | D9 => P0 | D10 => P127 | D11 => P127 | D12 => P126 | D13 => P126 | D14 => P125 | D15 => P125 | D16 => P124 | D17 => P124 | D18 => P123 | D19 => P123 | D20 => P122 | D21 => P122 | D22 => P121 | D23 => P121 | D24 => P120 | D25 => P120 | D26 => P119 | D27 => P119 | D28 => P118 | D29 => P118 | D30 => P117 | D31 => P117 | D32 => P116 | D33 => P116 | D34 => P115 | D35 => P115 | D36 => P114 | D37 => P114 | D38 => P113 | D39 => P113 | D40 => P112 | D41 => P112 | D42 => P111 | D43 => P111 | D44 => P110 | D45 => P110 | D46 => P109 | D47 => P109 | D48 => P108 | D49 => P108 | D50 => P107 | D51 => P107 | D52 => P106 | D53 => P106 | D54 => P105 | D55 => P105 | D56 => P104 | D57 => P104 | D58 => P103 | D59 => P103 | D60 => P102 | D61 => P102 | D62 => P101 | D63 => P101 end
    | D6 => match d0 with D0 => P5 | D1 => P5 | D2 => P4 | D3 => P4 | D4 => P3 | D5 => P3 | D6 => P2 | D7 => P2 | D8 => P1 | D9 => P1 | D10 => P0 | D11 => P0 | D12 => P127 | D13 => P127 | D14 => P126 | D15 => P126 | D16 => P125 | D17 => P125 | D18 => P124 | D19 => P124 | D20 => P123 | D21 => P123 | D22 => P122 | D23 => P122 | D24 => P121 | D25 => P121 | D26 => P120 | D27 => P120 | D28 => P119 | D29 => P119 | D30 => P118 | D31 => P118 | D32 => P117 | D33 => P117 | D34 => P116 | D35 => P116 | D36 => P115 | D37 => P115 | D38 => P114 | D39 => P114 | D40 => P113 | D41 => P113 | D42 => P112 | D43 => P112 | D44 => P111 | D45 => P111 | D46 => P110 | D47 => P110 | D48 => P109 | D49 => P109 | D50 => P108 | D51 => P108 | D52 => P107 | D53 => P107 | D54 => P106 | D55 => P106 | D56 => P105 | D57 => P105 | D58 => P104 | D59 => P104 | D60 => P103 | D61 => P103 | D62 => P102 | D63 => P102 end
    | D7 => match d0 with D0 => P6 | D1 => P6 | D2 => P5 | D3 => P5 | D4 => P4 | D5 => P4 | D6 => P3 | D7 => P3 | D8 => P2 | D9 => P2 | D10 => P1 | D11 => P1 | D12 => P0 | D13 => P0 | D14 => P127 | D15 => P127 | D16 => P126 | D17 => P126 | D18 => P125 | D19 => P125 | D20 => P124 | D21 => P124 | D22 => P123 | D23 => P123 | D24 => P122 | D25 => P122 | D26 => P121 | D27 => P121 | D28 => P120 | D29 => P120 | D30 => P119 | D31 => P119 | D32 => P118 | D33 => P118 | D34 => P117 | D35 => P117 | D36 => P116 | D37 => P116 | D38 => P115 | D39 => P115 | D40 => P114 | D41 => P114 | D42 => P113 | D43 => P113 | D44 => P112 | D45 => P112 | D46 => P111 | D47 => P111 | D48 => P110 | D49 => P110 | D50 => P109 | D51 => P109 | D52 => P108 | D53 => P108 | D54 => P107 | D55 => P107 | D56 => P106 | D57 => P106 | D58 => P105 | D59 => P105 | D60 => P104 | D61 => P104 | D62 => P103 | D63 => P103 end
    | D8 => match d0 with D0 => P7 | D1 => P7 | D2 => P6 | D3 => P6 | D4 => P5 | D5 => P5 | D6 => P4 | D7 => P4 | D8 => P3 | D9 => P3 | D10 => P2 | D11 => P2 | D12 => P1 | D13 => P1 | D14 => P0 | D15 => P0 | D16 => P127 | D17 => P127 | D18 => P126 | D19 => P126 | D20 => P125 | D21 => P125 | D22 => P124 | D23 => P124 | D24 => P123 | D25 => P123 | D26 => P122 | D27 => P122 | D28 => P121 | D29 => P121 | D30 => P120 | D31 => P120 | D32 => P119 | D33 => P119 | D34 => P118 | D35 => P118 | D36 => P117 | D37 => P117 | D38 => P116 | D39 => P116 | D40 => P115 | D41 => P115 | D42 => P114 | D43 => P114 | D44 => P113 | D45 => P113 | D46 => P112 | D47 => P112 | D48 => P111 | D49 => P111 | D50 => P110 | D51 => P110 | D52 => P109 | D53 => P109 | D54 => P108 | D55 => P108 | D56 => P107 | D57 => P107 | D58 => P106 | D59 => P106 | D60 => P105 | D61 => P105 | D62 => P104 | D63 => P104 end
    | D9 => match d0 with D0 => P8 | D1 => P8 | D2 => P7 | D3 => P7 | D4 => P6 | D5 => P6 | D6 => P5 | D7 => P5 | D8 => P4 | D9 => P4 | D10 => P3 | D11 => P3 | D12 => P2 | D13 => P2 | D14 => P1 | D15 => P1 | D16 => P0 | D17 => P0 | D18 => P127 | D19 => P127 | D20 => P126 | D21 => P126 | D22 => P125 | D23 => P125 | D24 => P124 | D25 => P124 | D26 => P123 | D27 => P123 | D28 => P122 | D29 => P122 | D30 => P121 | D31 => P121 | D32 => P120 | D33 => P120 | D34 => P119 | D35 => P119 | D36 => P118 | D37 => P118 | D38 => P117 | D39 => P117 | D40 => P116 | D41 => P116 | D42 => P115 | D43 => P115 | D44 => P114 | D45 => P114 | D46 => P113 | D47 => P113 | D48 => P112 | D49 => P112 | D50 => P111 | D51 => P111 | D52 => P110 | D53 => P110 | D54 => P109 | D55 => P109 | D56 => P108 | D57 => P108 | D58 => P107 | D59 => P107 | D60 => P106 | D61 => P106 | D62 => P105 | D63 => P105 end
    | D10 => match d0 with D0 => P9 | D1 => P9 | D2 => P8 | D3 => P8 | D4 => P7 | D5 => P7 | D6 => P6 | D7 => P6 | D8 => P5 | D9 => P5 | D10 => P4 | D11 => P4 | D12 => P3 | D13 => P3 | D14 => P2 | D15 => P2 | D16 => P1 | D17 => P1 | D18 => P0 | D19 => P0 | D20 => P127 | D21 => P127 | D22 => P126 | D23 => P126 | D24 => P125 | D25 => P125 | D26 => P124 | D27 => P124 | D28 => P123 | D29 => P123 | D30 => P122 | D31 => P122 | D32 => P121 | D33 => P121 | D34 => P120 | D35 => P120 | D36 => P119 | D37 => P119 | D38 => P118 | D39 => P118 | D40 => P117 | D41 => P117 | D42 => P116 | D43 => P116 | D44 => P115 | D45 => P115 | D46 => P114 | D47 => P114 | D48 => P113 | D49 => P113 | D50 => P112 | D51 => P112 | D52 => P111 | D53 => P111 | D54 => P110 | D55 => P110 | D56 => P109 | D57 => P109 | D58 => P108 | D59 => P108 | D60 => P107 | D61 => P107 | D62 => P106 | D63 => P106 end
    | D11 => match d0 with D0 => P10 | D1 => P10 | D2 => P9 | D3 => P9 | D4 => P8 | D5 => P8 | D6 => P7 | D7 => P7 | D8 => P6 | D9 => P6 | D10 => P5 | D11 => P5 | D12 => P4 | D13 => P4 | D14 => P3 | D15 => P3 | D16 => P2 | D17 => P2 | D18 => P1 | D19 => P1 | D20 => P0 | D21 => P0 | D22 => P127 | D23 => P127 | D24 => P126 | D25 => P126 | D26 => P125 | D27 => P125 | D28 => P124 | D29 => P124 | D30 => P123 | D31 => P123 | D32 => P122 | D33 => P122 | D34 => P121 | D35 => P121 | D36 => P120 | D37 => P120 | D38 => P119 | D39 => P119 | D40 => P118 | D41 => P118 | D42 => P117 | D43 => P117 | D44 => P116 | D45 => P116 | D46 => P115 | D47 => P115 | D48 => P114 | D49 => P114 | D50 => P113 | D51 => P113 | D52 => P112 | D53 => P112 | D54 => P111 | D55 => P111 | D56 => P110 | D57 => P110 | D58 => P109 | D59 => P109 | D60 => P108 | D61 => P108 | D62 => P107 | D63 => P107 end
    | D12 => match d0 with D0 => P11 | D1 => P11 | D2 => P10 | D3 => P10 | D4 => P9 | D5 => P9 | D6 => P8 | D7 => P8 | D8 => P7 | D9 => P7 | D10 => P6 | D11 => P6 | D12 => P5 | D13 => P5 | D14 => P4 | D15 => P4 | D16 => P3 | D17 => P3 | D18 => P2 | D19 => P2 | D20 => P1 | D21 => P1 | D22 => P0 | D23 => P0 | D24 => P127 | D25 => P127 | D26 => P126 | D27 => P126 | D28 => P125 | D29 => P125 | D30 => P124 | D31 => P124 | D32 => P123 | D33 => P123 | D34 => P122 | D35 => P122 | D36 => P121 | D37 => P121 | D38 => P120 | D39 => P120 | D40 => P119 | D41 => P119 | D42 => P118 | D43 => P118 | D44 => P117 | D45 => P117 | D46 => P116 | D47 => P116 | D48 => P115 | D49 => P115 | D50 => P114 | D51 => P114 | D52 => P113 | D53 => P113 | D54 => P112 | D55 => P112 | D56 => P111 | D57 => P111 | D58 => P110 | D59 => P110 | D60 => P109 | D61 => P109 | D62 => P108 | D63 => P108 end
    | D13 => match d0 with D0 => P12 | D1 => P12 | D2 => P11 | D3 => P11 | D4 => P10 | D5 => P10 | D6 => P9 | D7 => P9 | D8 => P8 | D9 => P8 | D10 => P7 | D11 => P7 | D12 => P6 | D13 => P6 | D14 => P5 | D15 => P5 | D16 => P4 | D17 => P4 | D18 => P3 | D19 => P3 | D20 => P2 | D21 => P2 | D22 => P1 | D23 => P1 | D24 => P0 | D25 => P0 | D26 => P127 | D27 => P127 | D28 => P126 | D29 => P126 | D30 => P125 | D31 => P125 | D32 => P124 | D33 => P124 | D34 => P123 | D35 => P123 | D36 => P122 | D37 => P122 | D38 => P121 | D39 => P121 | D40 => P120 | D41 => P120 | D42 => P119 | D43 => P119 | D44 => P118 | D45 => P118 | D46 => P117 | D47 => P117 | D48 => P116 | D49 => P116 | D50 => P115 | D51 => P115 | D52 => P114 | D53 => P114 | D54 => P113 | D55 => P113 | D56 => P112 | D57 => P112 | D58 => P111 | D59 => P111 | D60 => P110 | D61 => P110 | D62 => P109 | D63 => P109 end
    | D14 => match d0 with D0 => P13 | D1 => P13 | D2 => P12 | D3 => P12 | D4 => P11 | D5 => P11 | D6 => P10 | D7 => P10 | D8 => P9 | D9 => P9 | D10 => P8 | D11 => P8 | D12 => P7 | D13 => P7 | D14 => P6 | D15 => P6 | D16 => P5 | D17 => P5 | D18 => P4 | D19 => P4 | D20 => P3 | D21 => P3 | D22 => P2 | D23 => P2 | D24 => P1 | D25 => P1 | D26 => P0 | D27 => P0 | D28 => P127 | D29 => P127 | D30 => P126 | D31 => P126 | D32 => P125 | D33 => P125 | D34 => P124 | D35 => P124 | D36 => P123 | D37 => P123 | D38 => P122 | D39 => P122 | D40 => P121 | D41 => P121 | D42 => P120 | D43 => P120 | D44 => P119 | D45 => P119 | D46 => P118 | D47 => P118 | D48 => P117 | D49 => P117 | D50 => P116 | D51 => P116 | D52 => P115 | D53 => P115 | D54 => P114 | D55 => P114 | D56 => P113 | D57 => P113 | D58 => P112 | D59 => P112 | D60 => P111 | D61 => P111 | D62 => P110 | D63 => P110 end
    | D15 => match d0 with D0 => P14 | D1 => P14 | D2 => P13 | D3 => P13 | D4 => P12 | D5 => P12 | D6 => P11 | D7 => P11 | D8 => P10 | D9 => P10 | D10 => P9 | D11 => P9 | D12 => P8 | D13 => P8 | D14 => P7 | D15 => P7 | D16 => P6 | D17 => P6 | D18 => P5 | D19 => P5 | D20 => P4 | D21 => P4 | D22 => P3 | D23 => P3 | D24 => P2 | D25 => P2 | D26 => P1 | D27 => P1 | D28 => P0 | D29 => P0 | D30 => P127 | D31 => P127 | D32 => P126 | D33 => P126 | D34 => P125 | D35 => P125 | D36 => P124 | D37 => P124 | D38 => P123 | D39 => P123 | D40 => P122 | D41 => P122 | D42 => P121 | D43 => P121 | D44 => P120 | D45 => P120 | D46 => P119 | D47 => P119 | D48 => P118 | D49 => P118 | D50 => P117 | D51 => P117 | D52 => P116 | D53 => P116 | D54 => P115 | D55 => P115 | D56 => P114 | D57 => P114 | D58 => P113 | D59 => P113 | D60 => P112 | D61 => P112 | D62 => P111 | D63 => P111 end
    | D16 => match d0 with D0 => P15 | D1 => P15 | D2 => P14 | D3 => P14 | D4 => P13 | D5 => P13 | D6 => P12 | D7 => P12 | D8 => P11 | D9 => P11 | D10 => P10 | D11 => P10 | D12 => P9 | D13 => P9 | D14 => P8 | D15 => P8 | D16 => P7 | D17 => P7 | D18 => P6 | D19 => P6 | D20 => P5 | D21 => P5 | D22 => P4 | D23 => P4 | D24 => P3 | D25 => P3 | D26 => P2 | D27 => P2 | D28 => P1 | D29 => P1 | D30 => P0 | D31 => P0 | D32 => P127 | D33 => P127 | D34 => P126 | D35 => P126 | D36 => P125 | D37 => P125 | D38 => P124 | D39 => P124 | D40 => P123 | D41 => P123 | D42 => P122 | D43 => P122 | D44 => P121 | D45 => P121 | D46 => P120 | D47 => P120 | D48 => P119 | D49 => P119 | D50 => P118 | D51 => P118 | D52 => P117 | D53 => P117 | D54 => P116 | D55 => P116 | D56 => P115 | D57 => P115 | D58 => P114 | D59 => P114 | D60 => P113 | D61 => P113 | D62 => P112 | D63 => P112 end
    | D17 => match d0 with D0 => P16 | D1 => P16 | D2 => P15 | D3 => P15 | D4 => P14 | D5 => P14 | D6 => P13 | D7 => P13 | D8 => P12 | D9 => P12 | D10 => P11 | D11 => P11 | D12 => P10 | D13 => P10 | D14 => P9 | D15 => P9 | D16 => P8 | D17 => P8 | D18 => P7 | D19 => P7 | D20 => P6 | D21 => P6 | D22 => P5 | D23 => P5 | D24 => P4 | D25 => P4 | D26 => P3 | D27 => P3 | D28 => P2 | D29 => P2 | D30 => P1 | D31 => P1 | D32 => P0 | D33 => P0 | D34 => P127 | D35 => P127 | D36 => P126 | D37 => P126 | D38 => P125 | D39 => P125 | D40 => P124 | D41 => P124 | D42 => P123 | D43 => P123 | D44 => P122 | D45 => P122 | D46 => P121 | D47 => P121 | D48 => P120 | D49 => P120 | D50 => P119 | D51 => P119 | D52 => P118 | D53 => P118 | D54 => P117 | D55 => P117 | D56 => P116 | D57 => P116 | D58 => P115 | D59 => P115 | D60 => P114 | D61 => P114 | D62 => P113 | D63 => P113 end
    | D18 => match d0 with D0 => P17 | D1 => P17 | D2 => P16 | D3 => P16 | D4 => P15 | D5 => P15 | D6 => P14 | D7 => P14 | D8 => P13 | D9 => P13 | D10 => P12 | D11 => P12 | D12 => P11 | D13 => P11 | D14 => P10 | D15 => P10 | D16 => P9 | D17 => P9 | D18 => P8 | D19 => P8 | D20 => P7 | D21 => P7 | D22 => P6 | D23 => P6 | D24 => P5 | D25 => P5 | D26 => P4 | D27 => P4 | D28 => P3 | D29 => P3 | D30 => P2 | D31 => P2 | D32 => P1 | D33 => P1 | D34 => P0 | D35 => P0 | D36 => P127 | D37 => P127 | D38 => P126 | D39 => P126 | D40 => P125 | D41 => P125 | D42 => P124 | D43 => P124 | D44 => P123 | D45 => P123 | D46 => P122 | D47 => P122 | D48 => P121 | D49 => P121 | D50 => P120 | D51 => P120 | D52 => P119 | D53 => P119 | D54 => P118 | D55 => P118 | D56 => P117 | D57 => P117 | D58 => P116 | D59 => P116 | D60 => P115 | D61 => P115 | D62 => P114 | D63 => P114 end
    | D19 => match d0 with D0 => P18 | D1 => P18 | D2 => P17 | D3 => P17 | D4 => P16 | D5 => P16 | D6 => P15 | D7 => P15 | D8 => P14 | D9 => P14 | D10 => P13 | D11 => P13 | D12 => P12 | D13 => P12 | D14 => P11 | D15 => P11 | D16 => P10 | D17 => P10 | D18 => P9 | D19 => P9 | D20 => P8 | D21 => P8 | D22 => P7 | D23 => P7 | D24 => P6 | D25 => P6 | D26 => P5 | D27 => P5 | D28 => P4 | D29 => P4 | D30 => P3 | D31 => P3 | D32 => P2 | D33 => P2 | D34 => P1 | D35 => P1 | D36 => P0 | D37 => P0 | D38 => P127 | D39 => P127 | D40 => P126 | D41 => P126 | D42 => P125 | D43 => P125 | D44 => P124 | D45 => P124 | D46 => P123 | D47 => P123 | D48 => P122 | D49 => P122 | D50 => P121 | D51 => P121 | D52 => P120 | D53 => P120 | D54 => P119 | D55 => P119 | D56 => P118 | D57 => P118 | D58 => P117 | D59 => P117 | D60 => P116 | D61 => P116 | D62 => P115 | D63 => P115 end
    | D20 => match d0 with D0 => P19 | D1 => P19 | D2 => P18 | D3 => P18 | D4 => P17 | D5 => P17 | D6 => P16 | D7 => P16 | D8 => P15 | D9 => P15 | D10 => P14 | D11 => P14 | D12 => P13 | D13 => P13 | D14 => P12 | D15 => P12 | D16 => P11 | D17 => P11 | D18 => P10 | D19 => P10 | D20 => P9 | D21 => P9 | D22 => P8 | D23 => P8 | D24 => P7 | D25 => P7 | D26 => P6 | D27 => P6 | D28 => P5 | D29 => P5 | D30 => P4 | D31 => P4 | D32 => P3 | D33 => P3 | D34 => P2 | D35 => P2 | D36 => P1 | D37 => P1 | D38 => P0 | D39 => P0 | D40 => P127 | D41 => P127 | D42 => P126 | D43 => P126 | D44 => P125 | D45 => P125 | D46 => P124 | D47 => P124 | D48 => P123 | D49 => P123 | D50 => P122 | D51 => P122 | D52 => P121 | D53 => P121 | D54 => P120 | D55 => P120 | D56 => P119 | D57 => P119 | D58 => P118 | D59 => P118 | D60 => P117 | D61 => P117 | D62 => P116 | D63 => P116 end
    | D21 => match d0 with D0 => P20 | D1 => P20 | D2 => P19 | D3 => P19 | D4 => P18 | D5 => P18 | D6 => P17 | D7 => P17 | D8 => P16 | D9 => P16 | D10 => P15 | D11 => P15 | D12 => P14 | D13 => P14 | D14 => P13 | D15 => P13 | D16 => P12 | D17 => P12 | D18 => P11 | D19 => P11 | D20 => P10 | D21 => P10 | D22 => P9 | D23 => P9 | D24 => P8 | D25 => P8 | D26 => P7 | D27 => P7 | D28 => P6 | D29 => P6 | D30 => P5 | D31 => P5 | D32 => P4 | D33 => P4 | D34 => P3 | D35 => P3 | D36 => P2 | D37 => P2 | D38 => P1 | D39 => P1 | D40 => P0 | D41 => P0 | D42 => P127 | D43 => P127 | D44 => P126 | D45 => P126 | D46 => P125 | D47 => P125 | D48 => P124 | D49 => P124 | D50 => P123 | D51 => P123 | D52 => P122 | D53 => P122 | D54 => P121 | D55 => P121 | D56 => P120 | D57 => P120 | D58 => P119 | D59 => P119 | D60 => P118 | D61 => P118 | D62 => P117 | D63 => P117 end
    | D22 => match d0 with D0 => P21 | D1 => P21 | D2 => P20 | D3 => P20 | D4 => P19 | D5 => P19 | D6 => P18 | D7 => P18 | D8 => P17 | D9 => P17 | D10 => P16 | D11 => P16 | D12 => P15 | D13 => P15 | D14 => P14 | D15 => P14 | D16 => P13 | D17 => P13 | D18 => P12 | D19 => P12 | D20 => P11 | D21 => P11 | D22 => P10 | D23 => P10 | D24 => P9 | D25 => P9 | D26 => P8 | D27 => P8 | D28 => P7 | D29 => P7 | D30 => P6 | D31 => P6 | D32 => P5 | D33 => P5 | D34 => P4 | D35 => P4 | D36 => P3 | D37 => P3 | D38 => P2 | D39 => P2 | D40 => P1 | D41 => P1 | D42 => P0 | D43 => P0 | D44 => P127 | D45 => P127 | D46 => P126 | D47 => P126 | D48 => P125 | D49 => P125 | D50 => P124 | D51 => P124 | D52 => P123 | D53 => P123 | D54 => P122 | D55 => P122 | D56 => P121 | D57 => P121 | D58 => P120 | D59 => P120 | D60 => P119 | D61 => P119 | D62 => P118 | D63 => P118 end
    | D23 => match d0 with D0 => P22 | D1 => P22 | D2 => P21 | D3 => P21 | D4 => P20 | D5 => P20 | D6 => P19 | D7 => P19 | D8 => P18 | D9 => P18 | D10 => P17 | D11 => P17 | D12 => P16 | D13 => P16 | D14 => P15 | D15 => P15 | D16 => P14 | D17 => P14 | D18 => P13 | D19 => P13 | D20 => P12 | D21 => P12 | D22 => P11 | D23 => P11 | D24 => P10 | D25 => P10 | D26 => P9 | D27 => P9 | D28 => P8 | D29 => P8 | D30 => P7 | D31 => P7 | D32 => P6 | D33 => P6 | D34 => P5 | D35 => P5 | D36 => P4 | D37 => P4 | D38 => P3 | D39 => P3 | D40 => P2 | D41 => P2 | D42 => P1 | D43 => P1 | D44 => P0 | D45 => P0 | D46 => P127 | D47 => P127 | D48 => P126 | D49 => P126 | D50 => P125 | D51 => P125 | D52 => P124 | D53 => P124 | D54 => P123 | D55 => P123 | D56 => P122 | D57 => P122 | D58 => P121 | D59 => P121 | D60 => P120 | D61 => P120 | D62 => P119 | D63 => P119 end
    | D24 => match d0 with D0 => P23 | D1 => P23 | D2 => P22 | D3 => P22 | D4 => P21 | D5 => P21 | D6 => P20 | D7 => P20 | D8 => P19 | D9 => P19 | D10 => P18 | D11 => P18 | D12 => P17 | D13 => P17 | D14 => P16 | D15 => P16 | D16 => P15 | D17 => P15 | D18 => P14 | D19 => P14 | D20 => P13 | D21 => P13 | D22 => P12 | D23 => P12 | D24 => P11 | D25 => P11 | D26 => P10 | D27 => P10 | D28 => P9 | D29 => P9 | D30 => P8 | D31 => P8 | D32 => P7 | D33 => P7 | D34 => P6 | D35 => P6 | D36 => P5 | D37 => P5 | D38 => P4 | D39 => P4 | D40 => P3 | D41 => P3 | D42 => P2 | D43 => P2 | D44 => P1 | D45 => P1 | D46 => P0 | D47 => P0 | D48 => P127 | D49 => P127 | D50 => P126 | D51 => P126 | D52 => P125 | D53 => P125 | D54 => P124 | D55 => P124 | D56 => P123 | D57 => P123 | D58 => P122 | D59 => P122 | D60 => P121 | D61 => P121 | D62 => P120 | D63 => P120 end
    | D25 => match d0 with D0 => P24 | D1 => P24 | D2 => P23 | D3 => P23 | D4 => P22 | D5 => P22 | D6 => P21 | D7 => P21 | D8 => P20 | D9 => P20 | D10 => P19 | D11 => P19 | D12 => P18 | D13 => P18 | D14 => P17 | D15 => P17 | D16 => P16 | D17 => P16 | D18 => P15 | D19 => P15 | D20 => P14 | D21 => P14 | D22 => P13 | D23 => P13 | D24 => P12 | D25 => P12 | D26 => P11 | D27 => P11 | D28 => P10 | D29 => P10 | D30 => P9 | D31 => P9 | D32 => P8 | D33 => P8 | D34 => P7 | D35 => P7 | D36 => P6 | D37 => P6 | D38 => P5 | D39 => P5 | D40 => P4 | D41 => P4 | D42 => P3 | D43 => P3 | D44 => P2 | D45 => P2 | D46 => P1 | D47 => P1 | D48 => P0 | D49 => P0 | D50 => P127 | D51 => P127 | D52 => P126 | D53 => P126 | D54 => P125 | D55 => P125 | D56 => P124 | D57 => P124 | D58 => P123 | D59 => P123 | D60 => P122 | D61 => P122 | D62 => P121 | D63 => P121 end
    | D26 => match d0 with D0 => P25 | D1 => P25 | D2 => P24 | D3 => P24 | D4 => P23 | D5 => P23 | D6 => P22 | D7 => P22 | D8 => P21 | D9 => P21 | D10 => P20 | D11 => P20 | D12 => P19 | D13 => P19 | D14 => P18 | D15 => P18 | D16 => P17 | D17 => P17 | D18 => P16 | D19 => P16 | D20 => P15 | D21 => P15 | D22 => P14 | D23 => P14 | D24 => P13 | D25 => P13 | D26 => P12 | D27 => P12 | D28 => P11 | D29 => P11 | D30 => P10 | D31 => P10 | D32 => P9 | D33 => P9 | D34 => P8 | D35 => P8 | D36 => P7 | D37 => P7 | D38 => P6 | D39 => P6 | D40 => P5 | D41 => P5 | D42 => P4 | D43 => P4 | D44 => P3 | D45 => P3 | D46 => P2 | D47 => P2 | D48 => P1 | D49 => P1 | D50 => P0 | D51 => P0 | D52 => P127 | D53 => P127 | D54 => P126 | D55 => P126 | D56 => P125 | D57 => P125 | D58 => P124 | D59 => P124 | D60 => P123 | D61 => P123 | D62 => P122 | D63 => P122 end
    | D27 => match d0 with D0 => P26 | D1 => P26 | D2 => P25 | D3 => P25 | D4 => P24 | D5 => P24 | D6 => P23 | D7 => P23 | D8 => P22 | D9 => P22 | D10 => P21 | D11 => P21 | D12 => P20 | D13 => P20 | D14 => P19 | D15 => P19 | D16 => P18 | D17 => P18 | D18 => P17 | D19 => P17 | D20 => P16 | D21 => P16 | D22 => P15 | D23 => P15 | D24 => P14 | D25 => P14 | D26 => P13 | D27 => P13 | D28 => P12 | D29 => P12 | D30 => P11 | D31 => P11 | D32 => P10 | D33 => P10 | D34 => P9 | D35 => P9 | D36 => P8 | D37 => P8 | D38 => P7 | D39 => P7 | D40 => P6 | D41 => P6 | D42 => P5 | D43 => P5 | D44 => P4 | D45 => P4 | D46 => P3 | D47 => P3 | D48 => P2 | D49 => P2 | D50 => P1 | D51 => P1 | D52 => P0 | D53 => P0 | D54 => P127 | D55 => P127 | D56 => P126 | D57 => P126 | D58 => P125 | D59 => P125 | D60 => P124 | D61 => P124 | D62 => P123 | D63 => P123 end
    | D28 => match d0 with D0 => P27 | D1 => P27 | D2 => P26 | D3 => P26 | D4 => P25 | D5 => P25 | D6 => P24 | D7 => P24 | D8 => P23 | D9 => P23 | D10 => P22 | D11 => P22 | D12 => P21 | D13 => P21 | D14 => P20 | D15 => P20 | D16 => P19 | D17 => P19 | D18 => P18 | D19 => P18 | D20 => P17 | D21 => P17 | D22 => P16 | D23 => P16 | D24 => P15 | D25 => P15 | D26 => P14 | D27 => P14 | D28 => P13 | D29 => P13 | D30 => P12 | D31 => P12 | D32 => P11 | D33 => P11 | D34 => P10 | D35 => P10 | D36 => P9 | D37 => P9 | D38 => P8 | D39 => P8 | D40 => P7 | D41 => P7 | D42 => P6 | D43 => P6 | D44 => P5 | D45 => P5 | D46 => P4 | D47 => P4 | D48 => P3 | D49 => P3 | D50 => P2 | D51 => P2 | D52 => P1 | D53 => P1 | D54 => P0 | D55 => P0 | D56 => P127 | D57 => P127 | D58 => P126 | D59 => P126 | D60 => P125 | D61 => P125 | D62 => P124 | D63 => P124 end
    | D29 => match d0 with D0 => P28 | D1 => P28 | D2 => P27 | D3 => P27 | D4 => P26 | D5 => P26 | D6 => P25 | D7 => P25 | D8 => P24 | D9 => P24 | D10 => P23 | D11 => P23 | D12 => P22 | D13 => P22 | D14 => P21 | D15 => P21 | D16 => P20 | D17 => P20 | D18 => P19 | D19 => P19 | D20 => P18 | D21 => P18 | D22 => P17 | D23 => P17 | D24 => P16 | D25 => P16 | D26 => P15 | D27 => P15 | D28 => P14 | D29 => P14 | D30 => P13 | D31 => P13 | D32 => P12 | D33 => P12 | D34 => P11 | D35 => P11 | D36 => P10 | D37 => P10 | D38 => P9 | D39 => P9 | D40 => P8 | D41 => P8 | D42 => P7 | D43 => P7 | D44 => P6 | D45 => P6 | D46 => P5 | D47 => P5 | D48 => P4 | D49 => P4 | D50 => P3 | D51 => P3 | D52 => P2 | D53 => P2 | D54 => P1 | D55 => P1 | D56 => P0 | D57 => P0 | D58 => P127 | D59 => P127 | D60 => P126 | D61 => P126 | D62 => P125 | D63 => P125 end
    | D30 => match d0 with D0 => P29 | D1 => P29 | D2 => P28 | D3 => P28 | D4 => P27 | D5 => P27 | D6 => P26 | D7 => P26 | D8 => P25 | D9 => P25 | D10 => P24 | D11 => P24 | D12 => P23 | D13 => P23 | D14 => P22 | D15 => P22 | D16 => P21 | D17 => P21 | D18 => P20 | D19 => P20 | D20 => P19 | D21 => P19 | D22 => P18 | D23 => P18 | D24 => P17 | D25 => P17 | D26 => P16 | D27 => P16 | D28 => P15 | D29 => P15 | D30 => P14 | D31 => P14 | D32 => P13 | D33 => P13 | D34 => P12 | D35 => P12 | D36 => P11 | D37 => P11 | D38 => P10 | D39 => P10 | D40 => P9 | D41 => P9 | D42 => P8 | D43 => P8 | D44 => P7 | D45 => P7 | D46 => P6 | D47 => P6 | D48 => P5 | D49 => P5 | D50 => P4 | D51 => P4 | D52 => P3 | D53 => P3 | D54 => P2 | D55 => P2 | D56 => P1 | D57 => P1 | D58 => P0 | D59 => P0 | D60 => P127 | D61 => P127 | D62 => P126 | D63 => P126 end
    | D31 => match d0 with D0 => P30 | D1 => P30 | D2 => P29 | D3 => P29 | D4 => P28 | D5 => P28 | D6 => P27 | D7 => P27 | D8 => P26 | D9 => P26 | D10 => P25 | D11 => P25 | D12 => P24 | D13 => P24 | D14 => P23 | D15 => P23 | D16 => P22 | D17 => P22 | D18 => P21 | D19 => P21 | D20 => P20 | D21 => P20 | D22 => P19 | D23 => P19 | D24 => P18 | D25 => P18 | D26 => P17 | D27 => P17 | D28 => P16 | D29 => P16 | D30 => P15 | D31 => P15 | D32 => P14 | D33 => P14 | D34 => P13 | D35 => P13 | D36 => P12 | D37 => P12 | D38 => P11 | D39 => P11 | D40 => P10 | D41 => P10 | D42 => P9 | D43 => P9 | D44 => P8 | D45 => P8 | D46 => P7 | D47 => P7 | D48 => P6 | D49 => P6 | D50 => P5 | D51 => P5 | D52 => P4 | D53 => P4 | D54 => P3 | D55 => P3 | D56 => P2 | D57 => P2 | D58 => P1 | D59 => P1 | D60 => P0 | D61 => P0 | D62 => P127 | D63 => P127 end
    | D32 => match d0 with D0 => P31 | D1 => P31 | D2 => P30 | D3 => P30 | D4 => P29 | D5 => P29 | D6 => P28 | D7 => P28 | D8 => P27 | D9 => P27 | D10 => P26 | D11 => P26 | D12 => P25 | D13 => P25 | D14 => P24 | D15 => P24 | D16 => P23 | D17 => P23 | D18 => P22 | D19 => P22 | D20 => P21 | D21 => P21 | D22 => P20 | D23 => P20 | D24 => P19 | D25 => P19 | D26 => P18 | D27 => P18 | D28 => P17 | D29 => P17 | D30 => P16 | D31 => P16 | D32 => P15 | D33 => P15 | D34 => P14 | D35 => P14 | D36 => P13 | D37 => P13 | D38 => P12 | D39 => P12 | D40 => P11 | D41 => P11 | D42 => P10 | D43 => P10 | D44 => P9 | D45 => P9 | D46 => P8 | D47 => P8 | D48 => P7 | D49 => P7 | D50 => P6 | D51 => P6 | D52 => P5 | D53 => P5 | D54 => P4 | D55 => P4 | D56 => P3 | D57 => P3 | D58 => P2 | D59 => P2 | D60 => P1 | D61 => P1 | D62 => P0 | D63 => P0 end
    | D33 => match d0 with D0 => P32 | D1 => P32 | D2 => P31 | D3 => P31 | D4 => P30 | D5 => P30 | D6 => P29 | D7 => P29 | D8 => P28 | D9 => P28 | D10 => P27 | D11 => P27 | D12 => P26 | D13 => P26 | D14 => P25 | D15 => P25 | D16 => P24 | D17 => P24 | D18 => P23 | D19 => P23 | D20 => P22 | D21 => P22 | D22 => P21 | D23 => P21 | D24 => P20 | D25 => P20 | D26 => P19 | D27 => P19 | D28 => P18 | D29 => P18 | D30 => P17 | D31 => P17 | D32 => P16 | D33 => P16 | D34 => P15 | D35 => P15 | D36 => P14 | D37 => P14 | D38 => P13 | D39 => P13 | D40 => P12 | D41 => P12 | D42 => P11 | D43 => P11 | D44 => P10 | D45 => P10 | D46 => P9 | D47 => P9 | D48 => P8 | D49 => P8 | D50 => P7 | D51 => P7 | D52 => P6 | D53 => P6 | D54 => P5 | D55 => P5 | D56 => P4 | D57 => P4 | D58 => P3 | D59 => P3 | D60 => P2 | D61 => P2 | D62 => P1 | D63 => P1 end
    | D34 => match d0 with D0 => P33 | D1 => P33 | D2 => P32 | D3 => P32 | D4 => P31 | D5 => P31 | D6 => P30 | D7 => P30 | D8 => P29 | D9 => P29 | D10 => P28 | D11 => P28 | D12 => P27 | D13 => P27 | D14 => P26 | D15 => P26 | D16 => P25 | D17 => P25 | D18 => P24 | D19 => P24 | D20 => P23 | D21 => P23 | D22 => P22 | D23 => P22 | D24 => P21 | D25 => P21 | D26 => P20 | D27 => P20 | D28 => P19 | D29 => P19 | D30 => P18 | D31 => P18 | D32 => P17 | D33 => P17 | D34 => P16 | D35 => P16 | D36 => P15 | D37 => P15 | D38 => P14 | D39 => P14 | D40 => P13 | D41 => P13 | D42 => P12 | D43 => P12 | D44 => P11 | D45 => P11 | D46 => P10 | D47 => P10 | D48 => P9 | D49 => P9 | D50 => P8 | D51 => P8 | D52 => P7 | D53 => P7 | D54 => P6 | D55 => P6 | D56 => P5 | D57 => P5 | D58 => P4 | D59 => P4 | D60 => P3 | D61 => P3 | D62 => P2 | D63 => P2 end
    | D35 => match d0 with D0 => P34 | D1 => P34 | D2 => P33 | D3 => P33 | D4 => P32 | D5 => P32 | D6 => P31 | D7 => P31 | D8 => P30 | D9 => P30 | D10 => P29 | D11 => P29 | D12 => P28 | D13 => P28 | D14 => P27 | D15 => P27 | D16 => P26 | D17 => P26 | D18 => P25 | D19 => P25 | D20 => P24 | D21 => P24 | D22 => P23 | D23 => P23 | D24 => P22 | D25 => P22 | D26 => P21 | D27 => P21 | D28 => P20 | D29 => P20 | D30 => P19 | D31 => P19 | D32 => P18 | D33 => P18 | D34 => P17 | D35 => P17 | D36 => P16 | D37 => P16 | D38 => P15 | D39 => P15 | D40 => P14 | D41 => P14 | D42 => P13 | D43 => P13 | D44 => P12 | D45 => P12 | D46 => P11 | D47 => P11 | D48 => P10 | D49 => P10 | D50 => P9 | D51 => P9 | D52 => P8 | D53 => P8 | D54 => P7 | D55 => P7 | D56 => P6 | D57 => P6 | D58 => P5 | D59 => P5 | D60 => P4 | D61 => P4 | D62 => P3 | D63 => P3 end
    | D36 => match d0 with D0 => P35 | D1 => P35 | D2 => P34 | D3 => P34 | D4 => P33 | D5 => P33 | D6 => P32 | D7 => P32 | D8 => P31 | D9 => P31 | D10 => P30 | D11 => P30 | D12 => P29 | D13 => P29 | D14 => P28 | D15 => P28 | D16 => P27 | D17 => P27 | D18 => P26 | D19 => P26 | D20 => P25 | D21 => P25 | D22 => P24 | D23 => P24 | D24 => P23 | D25 => P23 | D26 => P22 | D27 => P22 | D28 => P21 | D29 => P21 | D30 => P20 | D31 => P20 | D32 => P19 | D33 => P19 | D34 => P18 | D35 => P18 | D36 => P17 | D37 => P17 | D38 => P16 | D39 => P16 | D40 => P15 | D41 => P15 | D42 => P14 | D43 => P14 | D44 => P13 | D45 => P13 | D46 => P12 | D47 => P12 | D48 => P11 | D49 => P11 | D50 => P10 | D51 => P10 | D52 => P9 | D53 => P9 | D54 => P8 | D55 => P8 | D56 => P7 | D57 => P7 | D58 => P6 | D59 => P6 | D60 => P5 | D61 => P5 | D62 => P4 | D63 => P4 end
    | D37 => match d0 with D0 => P36 | D1 => P36 | D2 => P35 | D3 => P35 | D4 => P34 | D5 => P34 | D6 => P33 | D7 => P33 | D8 => P32 | D9 => P32 | D10 => P31 | D11 => P31 | D12 => P30 | D13 => P30 | D14 => P29 | D15 => P29 | D16 => P28 | D17 => P28 | D18 => P27 | D19 => P27 | D20 => P26 | D21 => P26 | D22 => P25 | D23 => P25 | D24 => P24 | D25 => P24 | D26 => P23 | D27 => P23 | D28 => P22 | D29 => P22 | D30 => P21 | D31 => P21 | D32 => P20 | D33 => P20 | D34 => P19 | D35 => P19 | D36 => P18 | D37 => P18 | D38 => P17 | D39 => P17 | D40 => P16 | D41 => P16 | D42 => P15 | D43 => P15 | D44 => P14 | D45 => P14 | D46 => P13 | D47 => P13 | D48 => P12 | D49 => P12 | D50 => P11 | D51 => P11 | D52 => P10 | D53 => P10 | D54 => P9 | D55 => P9 | D56 => P8 | D57 => P8 | D58 => P7 | D59 => P7 | D60 => P6 | D61 => P6 | D62 => P5 | D63 => P5 end
    | D38 => match d0 with D0 => P37 | D1 => P37 | D2 => P36 | D3 => P36 | D4 => P35 | D5 => P35 | D6 => P34 | D7 => P34 | D8 => P33 | D9 => P33 | D10 => P32 | D11 => P32 | D12 => P31 | D13 => P31 | D14 => P30 | D15 => P30 | D16 => P29 | D17 => P29 | D18 => P28 | D19 => P28 | D20 => P27 | D21 => P27 | D22 => P26 | D23 => P26 | D24 => P25 | D25 => P25 | D26 => P24 | D27 => P24 | D28 => P23 | D29 => P23 | D30 => P22 | D31 => P22 | D32 => P21 | D33 => P21 | D34 => P20 | D35 => P20 | D36 => P19 | D37 => P19 | D38 => P18 | D39 => P18 | D40 => P17 | D41 => P17 | D42 => P16 | D43 => P16 | D44 => P15 | D45 => P15 | D46 => P14 | D47 => P14 | D48 => P13 | D49 => P13 | D50 => P12 | D51 => P12 | D52 => P11 | D53 => P11 | D54 => P10 | D55 => P10 | D56 => P9 | D57 => P9 | D58 => P8 | D59 => P8 | D60 => P7 | D61 => P7 | D62 => P6 | D63 => P6 end
    | D39 => match d0 with D0 => P38 | D1 => P38 | D2 => P37 | D3 => P37 | D4 => P36 | D5 => P36 | D6 => P35 | D7 => P35 | D8 => P34 | D9 => P34 | D10 => P33 | D11 => P33 | D12 => P32 | D13 => P32 | D14 => P31 | D15 => P31 | D16 => P30 | D17 => P30 | D18 => P29 | D19 => P29 | D20 => P28 | D21 => P28 | D22 => P27 | D23 => P27 | D24 => P26 | D25 => P26 | D26 => P25 | D27 => P25 | D28 => P24 | D29 => P24 | D30 => P23 | D31 => P23 | D32 => P22 | D33 => P22 | D34 => P21 | D35 => P21 | D36 => P20 | D37 => P20 | D38 => P19 | D39 => P19 | D40 => P18 | D41 => P18 | D42 => P17 | D43 => P17 | D44 => P16 | D45 => P16 | D46 => P15 | D47 => P15 | D48 => P14 | D49 => P14 | D50 => P13 | D51 => P13 | D52 => P12 | D53 => P12 | D54 => P11 | D55 => P11 | D56 => P10 | D57 => P10 | D58 => P9 | D59 => P9 | D60 => P8 | D61 => P8 | D62 => P7 | D63 => P7 end
    | D40 => match d0 with D0 => P39 | D1 => P39 | D2 => P38 | D3 => P38 | D4 => P37 | D5 => P37 | D6 => P36 | D7 => P36 | D8 => P35 | D9 => P35 | D10 => P34 | D11 => P34 | D12 => P33 | D13 => P33 | D14 => P32 | D15 => P32 | D16 => P31 | D17 => P31 | D18 => P30 | D19 => P30 | D20 => P29 | D21 => P29 | D22 => P28 | D23 => P28 | D24 => P27 | D25 => P27 | D26 => P26 | D27 => P26 | D28 => P25 | D29 => P25 | D30 => P24 | D31 => P24 | D32 => P23 | D33 => P23 | D34 => P22 | D35 => P22 | D36 => P21 | D37 => P21 | D38 => P20 | D39 => P20 | D40 => P19 | D41 => P19 | D42 => P18 | D43 => P18 | D44 => P17 | D45 => P17 | D46 => P16 | D47 => P16 | D48 => P15 | D49 => P15 | D50 => P14 | D51 => P14 | D52 => P13 | D53 => P13 | D54 => P12 | D55 => P12 | D56 => P11 | D57 => P11 | D58 => P10 | D59 => P10 | D60 => P9 | D61 => P9 | D62 => P8 | D63 => P8 end
    | D41 => match d0 with D0 => P40 | D1 => P40 | D2 => P39 | D3 => P39 | D4 => P38 | D5 => P38 | D6 => P37 | D7 => P37 | D8 => P36 | D9 => P36 | D10 => P35 | D11 => P35 | D12 => P34 | D13 => P34 | D14 => P33 | D15 => P33 | D16 => P32 | D17 => P32 | D18 => P31 | D19 => P31 | D20 => P30 | D21 => P30 | D22 => P29 | D23 => P29 | D24 => P28 | D25 => P28 | D26 => P27 | D27 => P27 | D28 => P26 | D29 => P26 | D30 => P25 | D31 => P25 | D32 => P24 | D33 => P24 | D34 => P23 | D35 => P23 | D36 => P22 | D37 => P22 | D38 => P21 | D39 => P21 | D40 => P20 | D41 => P20 | D42 => P19 | D43 => P19 | D44 => P18 | D45 => P18 | D46 => P17 | D47 => P17 | D48 => P16 | D49 => P16 | D50 => P15 | D51 => P15 | D52 => P14 | D53 => P14 | D54 => P13 | D55 => P13 | D56 => P12 | D57 => P12 | D58 => P11 | D59 => P11 | D60 => P10 | D61 => P10 | D62 => P9 | D63 => P9 end
    | D42 => match d0 with D0 => P41 | D1 => P41 | D2 => P40 | D3 => P40 | D4 => P39 | D5 => P39 | D6 => P38 | D7 => P38 | D8 => P37 | D9 => P37 | D10 => P36 | D11 => P36 | D12 => P35 | D13 => P35 | D14 => P34 | D15 => P34 | D16 => P33 | D17 => P33 | D18 => P32 | D19 => P32 | D20 => P31 | D21 => P31 | D22 => P30 | D23 => P30 | D24 => P29 | D25 => P29 | D26 => P28 | D27 => P28 | D28 => P27 | D29 => P27 | D30 => P26 | D31 => P26 | D32 => P25 | D33 => P25 | D34 => P24 | D35 => P24 | D36 => P23 | D37 => P23 | D38 => P22 | D39 => P22 | D40 => P21 | D41 => P21 | D42 => P20 | D43 => P20 | D44 => P19 | D45 => P19 | D46 => P18 | D47 => P18 | D48 => P17 | D49 => P17 | D50 => P16 | D51 => P16 | D52 => P15 | D53 => P15 | D54 => P14 | D55 => P14 | D56 => P13 | D57 => P13 | D58 => P12 | D59 => P12 | D60 => P11 | D61 => P11 | D62 => P10 | D63 => P10 end
    | D43 => match d0 with D0 => P42 | D1 => P42 | D2 => P41 | D3 => P41 | D4 => P40 | D5 => P40 | D6 => P39 | D7 => P39 | D8 => P38 | D9 => P38 | D10 => P37 | D11 => P37 | D12 => P36 | D13 => P36 | D14 => P35 | D15 => P35 | D16 => P34 | D17 => P34 | D18 => P33 | D19 => P33 | D20 => P32 | D21 => P32 | D22 => P31 | D23 => P31 | D24 => P30 | D25 => P30 | D26 => P29 | D27 => P29 | D28 => P28 | D29 => P28 | D30 => P27 | D31 => P27 | D32 => P26 | D33 => P26 | D34 => P25 | D35 => P25 | D36 => P24 | D37 => P24 | D38 => P23 | D39 => P23 | D40 => P22 | D41 => P22 | D42 => P21 | D43 => P21 | D44 => P20 | D45 => P20 | D46 => P19 | D47 => P19 | D48 => P18 | D49 => P18 | D50 => P17 | D51 => P17 | D52 => P16 | D53 => P16 | D54 => P15 | D55 => P15 | D56 => P14 | D57 => P14 | D58 => P13 | D59 => P13 | D60 => P12 | D61 => P12 | D62 => P11 | D63 => P11 end
    | D44 => match d0 with D0 => P43 | D1 => P43 | D2 => P42 | D3 => P42 | D4 => P41 | D5 => P41 | D6 => P40 | D7 => P40 | D8 => P39 | D9 => P39 | D10 => P38 | D11 => P38 | D12 => P37 | D13 => P37 | D14 => P36 | D15 => P36 | D16 => P35 | D17 => P35 | D18 => P34 | D19 => P34 | D20 => P33 | D21 => P33 | D22 => P32 | D23 => P32 | D24 => P31 | D25 => P31 | D26 => P30 | D27 => P30 | D28 => P29 | D29 => P29 | D30 => P28 | D31 => P28 | D32 => P27 | D33 => P27 | D34 => P26 | D35 => P26 | D36 => P25 | D37 => P25 | D38 => P24 | D39 => P24 | D40 => P23 | D41 => P23 | D42 => P22 | D43 => P22 | D44 => P21 | D45 => P21 | D46 => P20 | D47 => P20 | D48 => P19 | D49 => P19 | D50 => P18 | D51 => P18 | D52 => P17 | D53 => P17 | D54 => P16 | D55 => P16 | D56 => P15 | D57 => P15 | D58 => P14 | D59 => P14 | D60 => P13 | D61 => P13 | D62 => P12 | D63 => P12 end
    | D45 => match d0 with D0 => P44 | D1 => P44 | D2 => P43 | D3 => P43 | D4 => P42 | D5 => P42 | D6 => P41 | D7 => P41 | D8 => P40 | D9 => P40 | D10 => P39 | D11 => P39 | D12 => P38 | D13 => P38 | D14 => P37 | D15 => P37 | D16 => P36 | D17 => P36 | D18 => P35 | D19 => P35 | D20 => P34 | D21 => P34 | D22 => P33 | D23 => P33 | D24 => P32 | D25 => P32 | D26 => P31 | D27 => P31 | D28 => P30 | D29 => P30 | D30 => P29 | D31 => P29 | D32 => P28 | D33 => P28 | D34 => P27 | D35 => P27 | D36 => P26 | D37 => P26 | D38 => P25 | D39 => P25 | D40 => P24 | D41 => P24 | D42 => P23 | D43 => P23 | D44 => P22 | D45 => P22 | D46 => P21 | D47 => P21 | D48 => P20 | D49 => P20 | D50 => P19 | D51 => P19 | D52 => P18 | D53 => P18 | D54 => P17 | D55 => P17 | D56 => P16 | D57 => P16 | D58 => P15 | D59 => P15 | D60 => P14 | D61 => P14 | D62 => P13 | D63 => P13 end
    | D46 => match d0 with D0 => P45 | D1 => P45 | D2 => P44 | D3 => P44 | D4 => P43 | D5 => P43 | D6 => P42 | D7 => P42 | D8 => P41 | D9 => P41 | D10 => P40 | D11 => P40 | D12 => P39 | D13 => P39 | D14 => P38 | D15 => P38 | D16 => P37 | D17 => P37 | D18 => P36 | D19 => P36 | D20 => P35 | D21 => P35 | D22 => P34 | D23 => P34 | D24 => P33 | D25 => P33 | D26 => P32 | D27 => P32 | D28 => P31 | D29 => P31 | D30 => P30 | D31 => P30 | D32 => P29 | D33 => P29 | D34 => P28 | D35 => P28 | D36 => P27 | D37 => P27 | D38 => P26 | D39 => P26 | D40 => P25 | D41 => P25 | D42 => P24 | D43 => P24 | D44 => P23 | D45 => P23 | D46 => P22 | D47 => P22 | D48 => P21 | D49 => P21 | D50 => P20 | D51 => P20 | D52 => P19 | D53 => P19 | D54 => P18 | D55 => P18 | D56 => P17 | D57 => P17 | D58 => P16 | D59 => P16 | D60 => P15 | D61 => P15 | D62 => P14 | D63 => P14 end
    | D47 => match d0 with D0 => P46 | D1 => P46 | D2 => P45 | D3 => P45 | D4 => P44 | D5 => P44 | D6 => P43 | D7 => P43 | D8 => P42 | D9 => P42 | D10 => P41 | D11 => P41 | D12 => P40 | D13 => P40 | D14 => P39 | D15 => P39 | D16 => P38 | D17 => P38 | D18 => P37 | D19 => P37 | D20 => P36 | D21 => P36 | D22 => P35 | D23 => P35 | D24 => P34 | D25 => P34 | D26 => P33 | D27 => P33 | D28 => P32 | D29 => P32 | D30 => P31 | D31 => P31 | D32 => P30 | D33 => P30 | D34 => P29 | D35 => P29 | D36 => P28 | D37 => P28 | D38 => P27 | D39 => P27 | D40 => P26 | D41 => P26 | D42 => P25 | D43 => P25 | D44 => P24 | D45 => P24 | D46 => P23 | D47 => P23 | D48 => P22 | D49 => P22 | D50 => P21 | D51 => P21 | D52 => P20 | D53 => P20 | D54 => P19 | D55 => P19 | D56 => P18 | D57 => P18 | D58 => P17 | D59 => P17 | D60 => P16 | D61 => P16 | D62 => P15 | D63 => P15 end
    | D48 => match d0 with D0 => P47 | D1 => P47 | D2 => P46 | D3 => P46 | D4 => P45 | D5 => P45 | D6 => P44 | D7 => P44 | D8 => P43 | D9 => P43 | D10 => P42 | D11 => P42 | D12 => P41 | D13 => P41 | D14 => P40 | D15 => P40 | D16 => P39 | D17 => P39 | D18 => P38 | D19 => P38 | D20 => P37 | D21 => P37 | D22 => P36 | D23 => P36 | D24 => P35 | D25 => P35 | D26 => P34 | D27 => P34 | D28 => P33 | D29 => P33 | D30 => P32 | D31 => P32 | D32 => P31 | D33 => P31 | D34 => P30 | D35 => P30 | D36 => P29 | D37 => P29 | D38 => P28 | D39 => P28 | D40 => P27 | D41 => P27 | D42 => P26 | D43 => P26 | D44 => P25 | D45 => P25 | D46 => P24 | D47 => P24 | D48 => P23 | D49 => P23 | D50 => P22 | D51 => P22 | D52 => P21 | D53 => P21 | D54 => P20 | D55 => P20 | D56 => P19 | D57 => P19 | D58 => P18 | D59 => P18 | D60 => P17 | D61 => P17 | D62 => P16 | D63 => P16 end
    | D49 => match d0 with D0 => P48 | D1 => P48 | D2 => P47 | D3 => P47 | D4 => P46 | D5 => P46 | D6 => P45 | D7 => P45 | D8 => P44 | D9 => P44 | D10 => P43 | D11 => P43 | D12 => P42 | D13 => P42 | D14 => P41 | D15 => P41 | D16 => P40 | D17 => P40 | D18 => P39 | D19 => P39 | D20 => P38 | D21 => P38 | D22 => P37 | D23 => P37 | D24 => P36 | D25 => P36 | D26 => P35 | D27 => P35 | D28 => P34 | D29 => P34 | D30 => P33 | D31 => P33 | D32 => P32 | D33 => P32 | D34 => P31 | D35 => P31 | D36 => P30 | D37 => P30 | D38 => P29 | D39 => P29 | D40 => P28 | D41 => P28 | D42 => P27 | D43 => P27 | D44 => P26 | D45 => P26 | D46 => P25 | D47 => P25 | D48 => P24 | D49 => P24 | D50 => P23 | D51 => P23 | D52 => P22 | D53 => P22 | D54 => P21 | D55 => P21 | D56 => P20 | D57 => P20 | D58 => P19 | D59 => P19 | D60 => P18 | D61 => P18 | D62 => P17 | D63 => P17 end
    | D50 => match d0 with D0 => P49 | D1 => P49 | D2 => P48 | D3 => P48 | D4 => P47 | D5 => P47 | D6 => P46 | D7 => P46 | D8 => P45 | D9 => P45 | D10 => P44 | D11 => P44 | D12 => P43 | D13 => P43 | D14 => P42 | D15 => P42 | D16 => P41 | D17 => P41 | D18 => P40 | D19 => P40 | D20 => P39 | D21 => P39 | D22 => P38 | D23 => P38 | D24 => P37 | D25 => P37 | D26 => P36 | D27 => P36 | D28 => P35 | D29 => P35 | D30 => P34 | D31 => P34 | D32 => P33 | D33 => P33 | D34 => P32 | D35 => P32 | D36 => P31 | D37 => P31 | D38 => P30 | D39 => P30 | D40 => P29 | D41 => P29 | D42 => P28 | D43 => P28 | D44 => P27 | D45 => P27 | D46 => P26 | D47 => P26 | D48 => P25 | D49 => P25 | D50 => P24 | D51 => P24 | D52 => P23 | D53 => P23 | D54 => P22 | D55 => P22 | D56 => P21 | D57 => P21 | D58 => P20 | D59 => P20 | D60 => P19 | D61 => P19 | D62 => P18 | D63 => P18 end
    | D51 => match d0 with D0 => P50 | D1 => P50 | D2 => P49 | D3 => P49 | D4 => P48 | D5 => P48 | D6 => P47 | D7 => P47 | D8 => P46 | D9 => P46 | D10 => P45 | D11 => P45 | D12 => P44 | D13 => P44 | D14 => P43 | D15 => P43 | D16 => P42 | D17 => P42 | D18 => P41 | D19 => P41 | D20 => P40 | D21 => P40 | D22 => P39 | D23 => P39 | D24 => P38 | D25 => P38 | D26 => P37 | D27 => P37 | D28 => P36 | D29 => P36 | D30 => P35 | D31 => P35 | D32 => P34 | D33 => P34 | D34 => P33 | D35 => P33 | D36 => P32 | D37 => P32 | D38 => P31 | D39 => P31 | D40 => P30 | D41 => P30 | D42 => P29 | D43 => P29 | D44 => P28 | D45 => P28 | D46 => P27 | D47 => P27 | D48 => P26 | D49 => P26 | D50 => P25 | D51 => P25 | D52 => P24 | D53 => P24 | D54 => P23 | D55 => P23 | D56 => P22 | D57 => P22 | D58 => P21 | D59 => P21 | D60 => P20 | D61 => P20 | D62 => P19 | D63 => P19 end
    | D52 => match d0 with D0 => P51 | D1 => P51 | D2 => P50 | D3 => P50 | D4 => P49 | D5 => P49 | D6 => P48 | D7 => P48 | D8 => P47 | D9 => P47 | D10 => P46 | D11 => P46 | D12 => P45 | D13 => P45 | D14 => P44 | D15 => P44 | D16 => P43 | D17 => P43 | D18 => P42 | D19 => P42 | D20 => P41 | D21 => P41 | D22 => P40 | D23 => P40 | D24 => P39 | D25 => P39 | D26 => P38 | D27 => P38 | D28 => P37 | D29 => P37 | D30 => P36 | D31 => P36 | D32 => P35 | D33 => P35 | D34 => P34 | D35 => P34 | D36 => P33 | D37 => P33 | D38 => P32 | D39 => P32 | D40 => P31 | D41 => P31 | D42 => P30 | D43 => P30 | D44 => P29 | D45 => P29 | D46 => P28 | D47 => P28 | D48 => P27 | D49 => P27 | D50 => P26 | D51 => P26 | D52 => P25 | D53 => P25 | D54 => P24 | D55 => P24 | D56 => P23 | D57 => P23 | D58 => P22 | D59 => P22 | D60 => P21 | D61 => P21 | D62 => P20 | D63 => P20 end
    | D53 => match d0 with D0 => P52 | D1 => P52 | D2 => P51 | D3 => P51 | D4 => P50 | D5 => P50 | D6 => P49 | D7 => P49 | D8 => P48 | D9 => P48 | D10 => P47 | D11 => P47 | D12 => P46 | D13 => P46 | D14 => P45 | D15 => P45 | D16 => P44 | D17 => P44 | D18 => P43 | D19 => P43 | D20 => P42 | D21 => P42 | D22 => P41 | D23 => P41 | D24 => P40 | D25 => P40 | D26 => P39 | D27 => P39 | D28 => P38 | D29 => P38 | D30 => P37 | D31 => P37 | D32 => P36 | D33 => P36 | D34 => P35 | D35 => P35 | D36 => P34 | D37 => P34 | D38 => P33 | D39 => P33 | D40 => P32 | D41 => P32 | D42 => P31 | D43 => P31 | D44 => P30 | D45 => P30 | D46 => P29 | D47 => P29 | D48 => P28 | D49 => P28 | D50 => P27 | D51 => P27 | D52 => P26 | D53 => P26 | D54 => P25 | D55 => P25 | D56 => P24 | D57 => P24 | D58 => P23 | D59 => P23 | D60 => P22 | D61 => P22 | D62 => P21 | D63 => P21 end
    | D54 => match d0 with D0 => P53 | D1 => P53 | D2 => P52 | D3 => P52 | D4 => P51 | D5 => P51 | D6 => P50 | D7 => P50 | D8 => P49 | D9 => P49 | D10 => P48 | D11 => P48 | D12 => P47 | D13 => P47 | D14 => P46 | D15 => P46 | D16 => P45 | D17 => P45 | D18 => P44 | D19 => P44 | D20 => P43 | D21 => P43 | D22 => P42 | D23 => P42 | D24 => P41 | D25 => P41 | D26 => P40 | D27 => P40 | D28 => P39 | D29 => P39 | D30 => P38 | D31 => P38 | D32 => P37 | D33 => P37 | D34 => P36 | D35 => P36 | D36 => P35 | D37 => P35 | D38 => P34 | D39 => P34 | D40 => P33 | D41 => P33 | D42 => P32 | D43 => P32 | D44 => P31 | D45 => P31 | D46 => P30 | D47 => P30 | D48 => P29 | D49 => P29 | D50 => P28 | D51 => P28 | D52 => P27 | D53 => P27 | D54 => P26 | D55 => P26 | D56 => P25 | D57 => P25 | D58 => P24 | D59 => P24 | D60 => P23 | D61 => P23 | D62 => P22 | D63 => P22 end
    | D55 => match d0 with D0 => P54 | D1 => P54 | D2 => P53 | D3 => P53 | D4 => P52 | D5 => P52 | D6 => P51 | D7 => P51 | D8 => P50 | D9 => P50 | D10 => P49 | D11 => P49 | D12 => P48 | D13 => P48 | D14 => P47 | D15 => P47 | D16 => P46 | D17 => P46 | D18 => P45 | D19 => P45 | D20 => P44 | D21 => P44 | D22 => P43 | D23 => P43 | D24 => P42 | D25 => P42 | D26 => P41 | D27 => P41 | D28 => P40 | D29 => P40 | D30 => P39 | D31 => P39 | D32 => P38 | D33 => P38 | D34 => P37 | D35 => P37 | D36 => P36 | D37 => P36 | D38 => P35 | D39 => P35 | D40 => P34 | D41 => P34 | D42 => P33 | D43 => P33 | D44 => P32 | D45 => P32 | D46 => P31 | D47 => P31 | D48 => P30 | D49 => P30 | D50 => P29 | D51 => P29 | D52 => P28 | D53 => P28 | D54 => P27 | D55 => P27 | D56 => P26 | D57 => P26 | D58 => P25 | D59 => P25 | D60 => P24 | D61 => P24 | D62 => P23 | D63 => P23 end
    | D56 => match d0 with D0 => P55 | D1 => P55 | D2 => P54 | D3 => P54 | D4 => P53 | D5 => P53 | D6 => P52 | D7 => P52 | D8 => P51 | D9 => P51 | D10 => P50 | D11 => P50 | D12 => P49 | D13 => P49 | D14 => P48 | D15 => P48 | D16 => P47 | D17 => P47 | D18 => P46 | D19 => P46 | D20 => P45 | D21 => P45 | D22 => P44 | D23 => P44 | D24 => P43 | D25 => P43 | D26 => P42 | D27 => P42 | D28 => P41 | D29 => P41 | D30 => P40 | D31 => P40 | D32 => P39 | D33 => P39 | D34 => P38 | D35 => P38 | D36 => P37 | D37 => P37 | D38 => P36 | D39 => P36 | D40 => P35 | D41 => P35 | D42 => P34 | D43 => P34 | D44 => P33 | D45 => P33 | D46 => P32 | D47 => P32 | D48 => P31 | D49 => P31 | D50 => P30 | D51 => P30 | D52 => P29 | D53 => P29 | D54 => P28 | D55 => P28 | D56 => P27 | D57 => P27 | D58 => P26 | D59 => P26 | D60 => P25 | D61 => P25 | D62 => P24 | D63 => P24 end
    | D57 => match d0 with D0 => P56 | D1 => P56 | D2 => P55 | D3 => P55 | D4 => P54 | D5 => P54 | D6 => P53 | D7 => P53 | D8 => P52 | D9 => P52 | D10 => P51 | D11 => P51 | D12 => P50 | D13 => P50 | D14 => P49 | D15 => P49 | D16 => P48 | D17 => P48 | D18 => P47 | D19 => P47 | D20 => P46 | D21 => P46 | D22 => P45 | D23 => P45 | D24 => P44 | D25 => P44 | D26 => P43 | D27 => P43 | D28 => P42 | D29 => P42 | D30 => P41 | D31 => P41 | D32 => P40 | D33 => P40 | D34 => P39 | D35 => P39 | D36 => P38 | D37 => P38 | D38 => P37 | D39 => P37 | D40 => P36 | D41 => P36 | D42 => P35 | D43 => P35 | D44 => P34 | D45 => P34 | D46 => P33 | D47 => P33 | D48 => P32 | D49 => P32 | D50 => P31 | D51 => P31 | D52 => P30 | D53 => P30 | D54 => P29 | D55 => P29 | D56 => P28 | D57 => P28 | D58 => P27 | D59 => P27 | D60 => P26 | D61 => P26 | D62 => P25 | D63 => P25 end
    | D58 => match d0 with D0 => P57 | D1 => P57 | D2 => P56 | D3 => P56 | D4 => P55 | D5 => P55 | D6 => P54 | D7 => P54 | D8 => P53 | D9 => P53 | D10 => P52 | D11 => P52 | D12 => P51 | D13 => P51 | D14 => P50 | D15 => P50 | D16 => P49 | D17 => P49 | D18 => P48 | D19 => P48 | D20 => P47 | D21 => P47 | D22 => P46 | D23 => P46 | D24 => P45 | D25 => P45 | D26 => P44 | D27 => P44 | D28 => P43 | D29 => P43 | D30 => P42 | D31 => P42 | D32 => P41 | D33 => P41 | D34 => P40 | D35 => P40 | D36 => P39 | D37 => P39 | D38 => P38 | D39 => P38 | D40 => P37 | D41 => P37 | D42 => P36 | D43 => P36 | D44 => P35 | D45 => P35 | D46 => P34 | D47 => P34 | D48 => P33 | D49 => P33 | D50 => P32 | D51 => P32 | D52 => P31 | D53 => P31 | D54 => P30 | D55 => P30 | D56 => P29 | D57 => P29 | D58 => P28 | D59 => P28 | D60 => P27 | D61 => P27 | D62 => P26 | D63 => P26 end
    | D59 => match d0 with D0 => P58 | D1 => P58 | D2 => P57 | D3 => P57 | D4 => P56 | D5 => P56 | D6 => P55 | D7 => P55 | D8 => P54 | D9 => P54 | D10 => P53 | D11 => P53 | D12 => P52 | D13 => P52 | D14 => P51 | D15 => P51 | D16 => P50 | D17 => P50 | D18 => P49 | D19 => P49 | D20 => P48 | D21 => P48 | D22 => P47 | D23 => P47 | D24 => P46 | D25 => P46 | D26 => P45 | D27 => P45 | D28 => P44 | D29 => P44 | D30 => P43 | D31 => P43 | D32 => P42 | D33 => P42 | D34 => P41 | D35 => P41 | D36 => P40 | D37 => P40 | D38 => P39 | D39 => P39 | D40 => P38 | D41 => P38 | D42 => P37 | D43 => P37 | D44 => P36 | D45 => P36 | D46 => P35 | D47 => P35 | D48 => P34 | D49 => P34 | D50 => P33 | D51 => P33 | D52 => P32 | D53 => P32 | D54 => P31 | D55 => P31 | D56 => P30 | D57 => P30 | D58 => P29 | D59 => P29 | D60 => P28 | D61 => P28 | D62 => P27 | D63 => P27 end
    | D60 => match d0 with D0 => P59 | D1 => P59 | D2 => P58 | D3 => P58 | D4 => P57 | D5 => P57 | D6 => P56 | D7 => P56 | D8 => P55 | D9 => P55 | D10 => P54 | D11 => P54 | D12 => P53 | D13 => P53 | D14 => P52 | D15 => P52 | D16 => P51 | D17 => P51 | D18 => P50 | D19 => P50 | D20 => P49 | D21 => P49 | D22 => P48 | D23 => P48 | D24 => P47 | D25 => P47 | D26 => P46 | D27 => P46 | D28 => P45 | D29 => P45 | D30 => P44 | D31 => P44 | D32 => P43 | D33 => P43 | D34 => P42 | D35 => P42 | D36 => P41 | D37 => P41 | D38 => P40 | D39 => P40 | D40 => P39 | D41 => P39 | D42 => P38 | D43 => P38 | D44 => P37 | D45 => P37 | D46 => P36 | D47 => P36 | D48 => P35 | D49 => P35 | D50 => P34 | D51 => P34 | D52 => P33 | D53 => P33 | D54 => P32 | D55 => P32 | D56 => P31 | D57 => P31 | D58 => P30 | D59 => P30 | D60 => P29 | D61 => P29 | D62 => P28 | D63 => P28 end
    | D61 => match d0 with D0 => P60 | D1 => P60 | D2 => P59 | D3 => P59 | D4 => P58 | D5 => P58 | D6 => P57 | D7 => P57 | D8 => P56 | D9 => P56 | D10 => P55 | D11 => P55 | D12 => P54 | D13 => P54 | D14 => P53 | D15 => P53 | D16 => P52 | D17 => P52 | D18 => P51 | D19 => P51 | D20 => P50 | D21 => P50 | D22 => P49 | D23 => P49 | D24 => P48 | D25 => P48 | D26 => P47 | D27 => P47 | D28 => P46 | D29 => P46 | D30 => P45 | D31 => P45 | D32 => P44 | D33 => P44 | D34 => P43 | D35 => P43 | D36 => P42 | D37 => P42 | D38 => P41 | D39 => P41 | D40 => P40 | D41 => P40 | D42 => P39 | D43 => P39 | D44 => P38 | D45 => P38 | D46 => P37 | D47 => P37 | D48 => P36 | D49 => P36 | D50 => P35 | D51 => P35 | D52 => P34 | D53 => P34 | D54 => P33 | D55 => P33 | D56 => P32 | D57 => P32 | D58 => P31 | D59 => P31 | D60 => P30 | D61 => P30 | D62 => P29 | D63 => P29 end
    | D62 => match d0 with D0 => P61 | D1 => P61 | D2 => P60 | D3 => P60 | D4 => P59 | D5 => P59 | D6 => P58 | D7 => P58 | D8 => P57 | D9 => P57 | D10 => P56 | D11 => P56 | D12 => P55 | D13 => P55 | D14 => P54 | D15 => P54 | D16 => P53 | D17 => P53 | D18 => P52 | D19 => P52 | D20 => P51 | D21 => P51 | D22 => P50 | D23 => P50 | D24 => P49 | D25 => P49 | D26 => P48 | D27 => P48 | D28 => P47 | D29 => P47 | D30 => P46 | D31 => P46 | D32 => P45 | D33 => P45 | D34 => P44 | D35 => P44 | D36 => P43 | D37 => P43 | D38 => P42 | D39 => P42 | D40 => P41 | D41 => P41 | D42 => P40 | D43 => P40 | D44 => P39 | D45 => P39 | D46 => P38 | D47 => P38 | D48 => P37 | D49 => P37 | D50 => P36 | D51 => P36 | D52 => P35 | D53 => P35 | D54 => P34 | D55 => P34 | D56 => P33 | D57 => P33 | D58 => P32 | D59 => P32 | D60 => P31 | D61 => P31 | D62 => P30 | D63 => P30 end
    | D63 => match d0 with D0 => P62 | D1 => P62 | D2 => P61 | D3 => P61 | D4 => P60 | D5 => P60 | D6 => P59 | D7 => P59 | D8 => P58 | D9 => P58 | D10 => P57 | D11 => P57 | D12 => P56 | D13 => P56 | D14 => P55 | D15 => P55 | D16 => P54 | D17 => P54 | D18 => P53 | D19 => P53 | D20 => P52 | D21 => P52 | D22 => P51 | D23 => P51 | D24 => P50 | D25 => P50 | D26 => P49 | D27 => P49 | D28 => P48 | D29 => P48 | D30 => P47 | D31 => P47 | D32 => P46 | D33 => P46 | D34 => P45 | D35 => P45 | D36 => P44 | D37 => P44 | D38 => P43 | D39 => P43 | D40 => P42 | D41 => P42 | D42 => P41 | D43 => P41 | D44 => P40 | D45 => P40 | D46 => P39 | D47 => P39 | D48 => P38 | D49 => P38 | D50 => P37 | D51 => P37 | D52 => P36 | D53 => P36 | D54 => P35 | D55 => P35 | D56 => P34 | D57 => P34 | D58 => P33 | D59 => P33 | D60 => P32 | D61 => P32 | D62 => P31 | D63 => P31 end
    end
  else
    if q_hi then match a with
    | D0 => match d0 with D0 => P96 | D1 => P96 | D2 => P95 | D3 => P95 | D4 => P94 | D5 => P94 | D6 => P93 | D7 => P93 | D8 => P92 | D9 => P92 | D10 => P91 | D11 => P91 | D12 => P90 | D13 => P90 | D14 => P89 | D15 => P89 | D16 => P88 | D17 => P88 | D18 => P87 | D19 => P87 | D20 => P86 | D21 => P86 | D22 => P85 | D23 => P85 | D24 => P84 | D25 => P84 | D26 => P83 | D27 => P83 | D28 => P82 | D29 => P82 | D30 => P81 | D31 => P81 | D32 => P80 | D33 => P80 | D34 => P79 | D35 => P79 | D36 => P78 | D37 => P78 | D38 => P77 | D39 => P77 | D40 => P76 | D41 => P76 | D42 => P75 | D43 => P75 | D44 => P74 | D45 => P74 | D46 => P73 | D47 => P73 | D48 => P72 | D49 => P72 | D50 => P71 | D51 => P71 | D52 => P70 | D53 => P70 | D54 => P69 | D55 => P69 | D56 => P68 | D57 => P68 | D58 => P67 | D59 => P67 | D60 => P66 | D61 => P66 | D62 => P65 | D63 => P65 end
    | D1 => match d0 with D0 => P97 | D1 => P97 | D2 => P96 | D3 => P96 | D4 => P95 | D5 => P95 | D6 => P94 | D7 => P94 | D8 => P93 | D9 => P93 | D10 => P92 | D11 => P92 | D12 => P91 | D13 => P91 | D14 => P90 | D15 => P90 | D16 => P89 | D17 => P89 | D18 => P88 | D19 => P88 | D20 => P87 | D21 => P87 | D22 => P86 | D23 => P86 | D24 => P85 | D25 => P85 | D26 => P84 | D27 => P84 | D28 => P83 | D29 => P83 | D30 => P82 | D31 => P82 | D32 => P81 | D33 => P81 | D34 => P80 | D35 => P80 | D36 => P79 | D37 => P79 | D38 => P78 | D39 => P78 | D40 => P77 | D41 => P77 | D42 => P76 | D43 => P76 | D44 => P75 | D45 => P75 | D46 => P74 | D47 => P74 | D48 => P73 | D49 => P73 | D50 => P72 | D51 => P72 | D52 => P71 | D53 => P71 | D54 => P70 | D55 => P70 | D56 => P69 | D57 => P69 | D58 => P68 | D59 => P68 | D60 => P67 | D61 => P67 | D62 => P66 | D63 => P66 end
    | D2 => match d0 with D0 => P98 | D1 => P98 | D2 => P97 | D3 => P97 | D4 => P96 | D5 => P96 | D6 => P95 | D7 => P95 | D8 => P94 | D9 => P94 | D10 => P93 | D11 => P93 | D12 => P92 | D13 => P92 | D14 => P91 | D15 => P91 | D16 => P90 | D17 => P90 | D18 => P89 | D19 => P89 | D20 => P88 | D21 => P88 | D22 => P87 | D23 => P87 | D24 => P86 | D25 => P86 | D26 => P85 | D27 => P85 | D28 => P84 | D29 => P84 | D30 => P83 | D31 => P83 | D32 => P82 | D33 => P82 | D34 => P81 | D35 => P81 | D36 => P80 | D37 => P80 | D38 => P79 | D39 => P79 | D40 => P78 | D41 => P78 | D42 => P77 | D43 => P77 | D44 => P76 | D45 => P76 | D46 => P75 | D47 => P75 | D48 => P74 | D49 => P74 | D50 => P73 | D51 => P73 | D52 => P72 | D53 => P72 | D54 => P71 | D55 => P71 | D56 => P70 | D57 => P70 | D58 => P69 | D59 => P69 | D60 => P68 | D61 => P68 | D62 => P67 | D63 => P67 end
    | D3 => match d0 with D0 => P99 | D1 => P99 | D2 => P98 | D3 => P98 | D4 => P97 | D5 => P97 | D6 => P96 | D7 => P96 | D8 => P95 | D9 => P95 | D10 => P94 | D11 => P94 | D12 => P93 | D13 => P93 | D14 => P92 | D15 => P92 | D16 => P91 | D17 => P91 | D18 => P90 | D19 => P90 | D20 => P89 | D21 => P89 | D22 => P88 | D23 => P88 | D24 => P87 | D25 => P87 | D26 => P86 | D27 => P86 | D28 => P85 | D29 => P85 | D30 => P84 | D31 => P84 | D32 => P83 | D33 => P83 | D34 => P82 | D35 => P82 | D36 => P81 | D37 => P81 | D38 => P80 | D39 => P80 | D40 => P79 | D41 => P79 | D42 => P78 | D43 => P78 | D44 => P77 | D45 => P77 | D46 => P76 | D47 => P76 | D48 => P75 | D49 => P75 | D50 => P74 | D51 => P74 | D52 => P73 | D53 => P73 | D54 => P72 | D55 => P72 | D56 => P71 | D57 => P71 | D58 => P70 | D59 => P70 | D60 => P69 | D61 => P69 | D62 => P68 | D63 => P68 end
    | D4 => match d0 with D0 => P100 | D1 => P100 | D2 => P99 | D3 => P99 | D4 => P98 | D5 => P98 | D6 => P97 | D7 => P97 | D8 => P96 | D9 => P96 | D10 => P95 | D11 => P95 | D12 => P94 | D13 => P94 | D14 => P93 | D15 => P93 | D16 => P92 | D17 => P92 | D18 => P91 | D19 => P91 | D20 => P90 | D21 => P90 | D22 => P89 | D23 => P89 | D24 => P88 | D25 => P88 | D26 => P87 | D27 => P87 | D28 => P86 | D29 => P86 | D30 => P85 | D31 => P85 | D32 => P84 | D33 => P84 | D34 => P83 | D35 => P83 | D36 => P82 | D37 => P82 | D38 => P81 | D39 => P81 | D40 => P80 | D41 => P80 | D42 => P79 | D43 => P79 | D44 => P78 | D45 => P78 | D46 => P77 | D47 => P77 | D48 => P76 | D49 => P76 | D50 => P75 | D51 => P75 | D52 => P74 | D53 => P74 | D54 => P73 | D55 => P73 | D56 => P72 | D57 => P72 | D58 => P71 | D59 => P71 | D60 => P70 | D61 => P70 | D62 => P69 | D63 => P69 end
    | D5 => match d0 with D0 => P101 | D1 => P101 | D2 => P100 | D3 => P100 | D4 => P99 | D5 => P99 | D6 => P98 | D7 => P98 | D8 => P97 | D9 => P97 | D10 => P96 | D11 => P96 | D12 => P95 | D13 => P95 | D14 => P94 | D15 => P94 | D16 => P93 | D17 => P93 | D18 => P92 | D19 => P92 | D20 => P91 | D21 => P91 | D22 => P90 | D23 => P90 | D24 => P89 | D25 => P89 | D26 => P88 | D27 => P88 | D28 => P87 | D29 => P87 | D30 => P86 | D31 => P86 | D32 => P85 | D33 => P85 | D34 => P84 | D35 => P84 | D36 => P83 | D37 => P83 | D38 => P82 | D39 => P82 | D40 => P81 | D41 => P81 | D42 => P80 | D43 => P80 | D44 => P79 | D45 => P79 | D46 => P78 | D47 => P78 | D48 => P77 | D49 => P77 | D50 => P76 | D51 => P76 | D52 => P75 | D53 => P75 | D54 => P74 | D55 => P74 | D56 => P73 | D57 => P73 | D58 => P72 | D59 => P72 | D60 => P71 | D61 => P71 | D62 => P70 | D63 => P70 end
    | D6 => match d0 with D0 => P102 | D1 => P102 | D2 => P101 | D3 => P101 | D4 => P100 | D5 => P100 | D6 => P99 | D7 => P99 | D8 => P98 | D9 => P98 | D10 => P97 | D11 => P97 | D12 => P96 | D13 => P96 | D14 => P95 | D15 => P95 | D16 => P94 | D17 => P94 | D18 => P93 | D19 => P93 | D20 => P92 | D21 => P92 | D22 => P91 | D23 => P91 | D24 => P90 | D25 => P90 | D26 => P89 | D27 => P89 | D28 => P88 | D29 => P88 | D30 => P87 | D31 => P87 | D32 => P86 | D33 => P86 | D34 => P85 | D35 => P85 | D36 => P84 | D37 => P84 | D38 => P83 | D39 => P83 | D40 => P82 | D41 => P82 | D42 => P81 | D43 => P81 | D44 => P80 | D45 => P80 | D46 => P79 | D47 => P79 | D48 => P78 | D49 => P78 | D50 => P77 | D51 => P77 | D52 => P76 | D53 => P76 | D54 => P75 | D55 => P75 | D56 => P74 | D57 => P74 | D58 => P73 | D59 => P73 | D60 => P72 | D61 => P72 | D62 => P71 | D63 => P71 end
    | D7 => match d0 with D0 => P103 | D1 => P103 | D2 => P102 | D3 => P102 | D4 => P101 | D5 => P101 | D6 => P100 | D7 => P100 | D8 => P99 | D9 => P99 | D10 => P98 | D11 => P98 | D12 => P97 | D13 => P97 | D14 => P96 | D15 => P96 | D16 => P95 | D17 => P95 | D18 => P94 | D19 => P94 | D20 => P93 | D21 => P93 | D22 => P92 | D23 => P92 | D24 => P91 | D25 => P91 | D26 => P90 | D27 => P90 | D28 => P89 | D29 => P89 | D30 => P88 | D31 => P88 | D32 => P87 | D33 => P87 | D34 => P86 | D35 => P86 | D36 => P85 | D37 => P85 | D38 => P84 | D39 => P84 | D40 => P83 | D41 => P83 | D42 => P82 | D43 => P82 | D44 => P81 | D45 => P81 | D46 => P80 | D47 => P80 | D48 => P79 | D49 => P79 | D50 => P78 | D51 => P78 | D52 => P77 | D53 => P77 | D54 => P76 | D55 => P76 | D56 => P75 | D57 => P75 | D58 => P74 | D59 => P74 | D60 => P73 | D61 => P73 | D62 => P72 | D63 => P72 end
    | D8 => match d0 with D0 => P104 | D1 => P104 | D2 => P103 | D3 => P103 | D4 => P102 | D5 => P102 | D6 => P101 | D7 => P101 | D8 => P100 | D9 => P100 | D10 => P99 | D11 => P99 | D12 => P98 | D13 => P98 | D14 => P97 | D15 => P97 | D16 => P96 | D17 => P96 | D18 => P95 | D19 => P95 | D20 => P94 | D21 => P94 | D22 => P93 | D23 => P93 | D24 => P92 | D25 => P92 | D26 => P91 | D27 => P91 | D28 => P90 | D29 => P90 | D30 => P89 | D31 => P89 | D32 => P88 | D33 => P88 | D34 => P87 | D35 => P87 | D36 => P86 | D37 => P86 | D38 => P85 | D39 => P85 | D40 => P84 | D41 => P84 | D42 => P83 | D43 => P83 | D44 => P82 | D45 => P82 | D46 => P81 | D47 => P81 | D48 => P80 | D49 => P80 | D50 => P79 | D51 => P79 | D52 => P78 | D53 => P78 | D54 => P77 | D55 => P77 | D56 => P76 | D57 => P76 | D58 => P75 | D59 => P75 | D60 => P74 | D61 => P74 | D62 => P73 | D63 => P73 end
    | D9 => match d0 with D0 => P105 | D1 => P105 | D2 => P104 | D3 => P104 | D4 => P103 | D5 => P103 | D6 => P102 | D7 => P102 | D8 => P101 | D9 => P101 | D10 => P100 | D11 => P100 | D12 => P99 | D13 => P99 | D14 => P98 | D15 => P98 | D16 => P97 | D17 => P97 | D18 => P96 | D19 => P96 | D20 => P95 | D21 => P95 | D22 => P94 | D23 => P94 | D24 => P93 | D25 => P93 | D26 => P92 | D27 => P92 | D28 => P91 | D29 => P91 | D30 => P90 | D31 => P90 | D32 => P89 | D33 => P89 | D34 => P88 | D35 => P88 | D36 => P87 | D37 => P87 | D38 => P86 | D39 => P86 | D40 => P85 | D41 => P85 | D42 => P84 | D43 => P84 | D44 => P83 | D45 => P83 | D46 => P82 | D47 => P82 | D48 => P81 | D49 => P81 | D50 => P80 | D51 => P80 | D52 => P79 | D53 => P79 | D54 => P78 | D55 => P78 | D56 => P77 | D57 => P77 | D58 => P76 | D59 => P76 | D60 => P75 | D61 => P75 | D62 => P74 | D63 => P74 end
    | D10 => match d0 with D0 => P106 | D1 => P106 | D2 => P105 | D3 => P105 | D4 => P104 | D5 => P104 | D6 => P103 | D7 => P103 | D8 => P102 | D9 => P102 | D10 => P101 | D11 => P101 | D12 => P100 | D13 => P100 | D14 => P99 | D15 => P99 | D16 => P98 | D17 => P98 | D18 => P97 | D19 => P97 | D20 => P96 | D21 => P96 | D22 => P95 | D23 => P95 | D24 => P94 | D25 => P94 | D26 => P93 | D27 => P93 | D28 => P92 | D29 => P92 | D30 => P91 | D31 => P91 | D32 => P90 | D33 => P90 | D34 => P89 | D35 => P89 | D36 => P88 | D37 => P88 | D38 => P87 | D39 => P87 | D40 => P86 | D41 => P86 | D42 => P85 | D43 => P85 | D44 => P84 | D45 => P84 | D46 => P83 | D47 => P83 | D48 => P82 | D49 => P82 | D50 => P81 | D51 => P81 | D52 => P80 | D53 => P80 | D54 => P79 | D55 => P79 | D56 => P78 | D57 => P78 | D58 => P77 | D59 => P77 | D60 => P76 | D61 => P76 | D62 => P75 | D63 => P75 end
    | D11 => match d0 with D0 => P107 | D1 => P107 | D2 => P106 | D3 => P106 | D4 => P105 | D5 => P105 | D6 => P104 | D7 => P104 | D8 => P103 | D9 => P103 | D10 => P102 | D11 => P102 | D12 => P101 | D13 => P101 | D14 => P100 | D15 => P100 | D16 => P99 | D17 => P99 | D18 => P98 | D19 => P98 | D20 => P97 | D21 => P97 | D22 => P96 | D23 => P96 | D24 => P95 | D25 => P95 | D26 => P94 | D27 => P94 | D28 => P93 | D29 => P93 | D30 => P92 | D31 => P92 | D32 => P91 | D33 => P91 | D34 => P90 | D35 => P90 | D36 => P89 | D37 => P89 | D38 => P88 | D39 => P88 | D40 => P87 | D41 => P87 | D42 => P86 | D43 => P86 | D44 => P85 | D45 => P85 | D46 => P84 | D47 => P84 | D48 => P83 | D49 => P83 | D50 => P82 | D51 => P82 | D52 => P81 | D53 => P81 | D54 => P80 | D55 => P80 | D56 => P79 | D57 => P79 | D58 => P78 | D59 => P78 | D60 => P77 | D61 => P77 | D62 => P76 | D63 => P76 end
    | D12 => match d0 with D0 => P108 | D1 => P108 | D2 => P107 | D3 => P107 | D4 => P106 | D5 => P106 | D6 => P105 | D7 => P105 | D8 => P104 | D9 => P104 | D10 => P103 | D11 => P103 | D12 => P102 | D13 => P102 | D14 => P101 | D15 => P101 | D16 => P100 | D17 => P100 | D18 => P99 | D19 => P99 | D20 => P98 | D21 => P98 | D22 => P97 | D23 => P97 | D24 => P96 | D25 => P96 | D26 => P95 | D27 => P95 | D28 => P94 | D29 => P94 | D30 => P93 | D31 => P93 | D32 => P92 | D33 => P92 | D34 => P91 | D35 => P91 | D36 => P90 | D37 => P90 | D38 => P89 | D39 => P89 | D40 => P88 | D41 => P88 | D42 => P87 | D43 => P87 | D44 => P86 | D45 => P86 | D46 => P85 | D47 => P85 | D48 => P84 | D49 => P84 | D50 => P83 | D51 => P83 | D52 => P82 | D53 => P82 | D54 => P81 | D55 => P81 | D56 => P80 | D57 => P80 | D58 => P79 | D59 => P79 | D60 => P78 | D61 => P78 | D62 => P77 | D63 => P77 end
    | D13 => match d0 with D0 => P109 | D1 => P109 | D2 => P108 | D3 => P108 | D4 => P107 | D5 => P107 | D6 => P106 | D7 => P106 | D8 => P105 | D9 => P105 | D10 => P104 | D11 => P104 | D12 => P103 | D13 => P103 | D14 => P102 | D15 => P102 | D16 => P101 | D17 => P101 | D18 => P100 | D19 => P100 | D20 => P99 | D21 => P99 | D22 => P98 | D23 => P98 | D24 => P97 | D25 => P97 | D26 => P96 | D27 => P96 | D28 => P95 | D29 => P95 | D30 => P94 | D31 => P94 | D32 => P93 | D33 => P93 | D34 => P92 | D35 => P92 | D36 => P91 | D37 => P91 | D38 => P90 | D39 => P90 | D40 => P89 | D41 => P89 | D42 => P88 | D43 => P88 | D44 => P87 | D45 => P87 | D46 => P86 | D47 => P86 | D48 => P85 | D49 => P85 | D50 => P84 | D51 => P84 | D52 => P83 | D53 => P83 | D54 => P82 | D55 => P82 | D56 => P81 | D57 => P81 | D58 => P80 | D59 => P80 | D60 => P79 | D61 => P79 | D62 => P78 | D63 => P78 end
    | D14 => match d0 with D0 => P110 | D1 => P110 | D2 => P109 | D3 => P109 | D4 => P108 | D5 => P108 | D6 => P107 | D7 => P107 | D8 => P106 | D9 => P106 | D10 => P105 | D11 => P105 | D12 => P104 | D13 => P104 | D14 => P103 | D15 => P103 | D16 => P102 | D17 => P102 | D18 => P101 | D19 => P101 | D20 => P100 | D21 => P100 | D22 => P99 | D23 => P99 | D24 => P98 | D25 => P98 | D26 => P97 | D27 => P97 | D28 => P96 | D29 => P96 | D30 => P95 | D31 => P95 | D32 => P94 | D33 => P94 | D34 => P93 | D35 => P93 | D36 => P92 | D37 => P92 | D38 => P91 | D39 => P91 | D40 => P90 | D41 => P90 | D42 => P89 | D43 => P89 | D44 => P88 | D45 => P88 | D46 => P87 | D47 => P87 | D48 => P86 | D49 => P86 | D50 => P85 | D51 => P85 | D52 => P84 | D53 => P84 | D54 => P83 | D55 => P83 | D56 => P82 | D57 => P82 | D58 => P81 | D59 => P81 | D60 => P80 | D61 => P80 | D62 => P79 | D63 => P79 end
    | D15 => match d0 with D0 => P111 | D1 => P111 | D2 => P110 | D3 => P110 | D4 => P109 | D5 => P109 | D6 => P108 | D7 => P108 | D8 => P107 | D9 => P107 | D10 => P106 | D11 => P106 | D12 => P105 | D13 => P105 | D14 => P104 | D15 => P104 | D16 => P103 | D17 => P103 | D18 => P102 | D19 => P102 | D20 => P101 | D21 => P101 | D22 => P100 | D23 => P100 | D24 => P99 | D25 => P99 | D26 => P98 | D27 => P98 | D28 => P97 | D29 => P97 | D30 => P96 | D31 => P96 | D32 => P95 | D33 => P95 | D34 => P94 | D35 => P94 | D36 => P93 | D37 => P93 | D38 => P92 | D39 => P92 | D40 => P91 | D41 => P91 | D42 => P90 | D43 => P90 | D44 => P89 | D45 => P89 | D46 => P88 | D47 => P88 | D48 => P87 | D49 => P87 | D50 => P86 | D51 => P86 | D52 => P85 | D53 => P85 | D54 => P84 | D55 => P84 | D56 => P83 | D57 => P83 | D58 => P82 | D59 => P82 | D60 => P81 | D61 => P81 | D62 => P80 | D63 => P80 end
    | D16 => match d0 with D0 => P112 | D1 => P112 | D2 => P111 | D3 => P111 | D4 => P110 | D5 => P110 | D6 => P109 | D7 => P109 | D8 => P108 | D9 => P108 | D10 => P107 | D11 => P107 | D12 => P106 | D13 => P106 | D14 => P105 | D15 => P105 | D16 => P104 | D17 => P104 | D18 => P103 | D19 => P103 | D20 => P102 | D21 => P102 | D22 => P101 | D23 => P101 | D24 => P100 | D25 => P100 | D26 => P99 | D27 => P99 | D28 => P98 | D29 => P98 | D30 => P97 | D31 => P97 | D32 => P96 | D33 => P96 | D34 => P95 | D35 => P95 | D36 => P94 | D37 => P94 | D38 => P93 | D39 => P93 | D40 => P92 | D41 => P92 | D42 => P91 | D43 => P91 | D44 => P90 | D45 => P90 | D46 => P89 | D47 => P89 | D48 => P88 | D49 => P88 | D50 => P87 | D51 => P87 | D52 => P86 | D53 => P86 | D54 => P85 | D55 => P85 | D56 => P84 | D57 => P84 | D58 => P83 | D59 => P83 | D60 => P82 | D61 => P82 | D62 => P81 | D63 => P81 end
    | D17 => match d0 with D0 => P113 | D1 => P113 | D2 => P112 | D3 => P112 | D4 => P111 | D5 => P111 | D6 => P110 | D7 => P110 | D8 => P109 | D9 => P109 | D10 => P108 | D11 => P108 | D12 => P107 | D13 => P107 | D14 => P106 | D15 => P106 | D16 => P105 | D17 => P105 | D18 => P104 | D19 => P104 | D20 => P103 | D21 => P103 | D22 => P102 | D23 => P102 | D24 => P101 | D25 => P101 | D26 => P100 | D27 => P100 | D28 => P99 | D29 => P99 | D30 => P98 | D31 => P98 | D32 => P97 | D33 => P97 | D34 => P96 | D35 => P96 | D36 => P95 | D37 => P95 | D38 => P94 | D39 => P94 | D40 => P93 | D41 => P93 | D42 => P92 | D43 => P92 | D44 => P91 | D45 => P91 | D46 => P90 | D47 => P90 | D48 => P89 | D49 => P89 | D50 => P88 | D51 => P88 | D52 => P87 | D53 => P87 | D54 => P86 | D55 => P86 | D56 => P85 | D57 => P85 | D58 => P84 | D59 => P84 | D60 => P83 | D61 => P83 | D62 => P82 | D63 => P82 end
    | D18 => match d0 with D0 => P114 | D1 => P114 | D2 => P113 | D3 => P113 | D4 => P112 | D5 => P112 | D6 => P111 | D7 => P111 | D8 => P110 | D9 => P110 | D10 => P109 | D11 => P109 | D12 => P108 | D13 => P108 | D14 => P107 | D15 => P107 | D16 => P106 | D17 => P106 | D18 => P105 | D19 => P105 | D20 => P104 | D21 => P104 | D22 => P103 | D23 => P103 | D24 => P102 | D25 => P102 | D26 => P101 | D27 => P101 | D28 => P100 | D29 => P100 | D30 => P99 | D31 => P99 | D32 => P98 | D33 => P98 | D34 => P97 | D35 => P97 | D36 => P96 | D37 => P96 | D38 => P95 | D39 => P95 | D40 => P94 | D41 => P94 | D42 => P93 | D43 => P93 | D44 => P92 | D45 => P92 | D46 => P91 | D47 => P91 | D48 => P90 | D49 => P90 | D50 => P89 | D51 => P89 | D52 => P88 | D53 => P88 | D54 => P87 | D55 => P87 | D56 => P86 | D57 => P86 | D58 => P85 | D59 => P85 | D60 => P84 | D61 => P84 | D62 => P83 | D63 => P83 end
    | D19 => match d0 with D0 => P115 | D1 => P115 | D2 => P114 | D3 => P114 | D4 => P113 | D5 => P113 | D6 => P112 | D7 => P112 | D8 => P111 | D9 => P111 | D10 => P110 | D11 => P110 | D12 => P109 | D13 => P109 | D14 => P108 | D15 => P108 | D16 => P107 | D17 => P107 | D18 => P106 | D19 => P106 | D20 => P105 | D21 => P105 | D22 => P104 | D23 => P104 | D24 => P103 | D25 => P103 | D26 => P102 | D27 => P102 | D28 => P101 | D29 => P101 | D30 => P100 | D31 => P100 | D32 => P99 | D33 => P99 | D34 => P98 | D35 => P98 | D36 => P97 | D37 => P97 | D38 => P96 | D39 => P96 | D40 => P95 | D41 => P95 | D42 => P94 | D43 => P94 | D44 => P93 | D45 => P93 | D46 => P92 | D47 => P92 | D48 => P91 | D49 => P91 | D50 => P90 | D51 => P90 | D52 => P89 | D53 => P89 | D54 => P88 | D55 => P88 | D56 => P87 | D57 => P87 | D58 => P86 | D59 => P86 | D60 => P85 | D61 => P85 | D62 => P84 | D63 => P84 end
    | D20 => match d0 with D0 => P116 | D1 => P116 | D2 => P115 | D3 => P115 | D4 => P114 | D5 => P114 | D6 => P113 | D7 => P113 | D8 => P112 | D9 => P112 | D10 => P111 | D11 => P111 | D12 => P110 | D13 => P110 | D14 => P109 | D15 => P109 | D16 => P108 | D17 => P108 | D18 => P107 | D19 => P107 | D20 => P106 | D21 => P106 | D22 => P105 | D23 => P105 | D24 => P104 | D25 => P104 | D26 => P103 | D27 => P103 | D28 => P102 | D29 => P102 | D30 => P101 | D31 => P101 | D32 => P100 | D33 => P100 | D34 => P99 | D35 => P99 | D36 => P98 | D37 => P98 | D38 => P97 | D39 => P97 | D40 => P96 | D41 => P96 | D42 => P95 | D43 => P95 | D44 => P94 | D45 => P94 | D46 => P93 | D47 => P93 | D48 => P92 | D49 => P92 | D50 => P91 | D51 => P91 | D52 => P90 | D53 => P90 | D54 => P89 | D55 => P89 | D56 => P88 | D57 => P88 | D58 => P87 | D59 => P87 | D60 => P86 | D61 => P86 | D62 => P85 | D63 => P85 end
    | D21 => match d0 with D0 => P117 | D1 => P117 | D2 => P116 | D3 => P116 | D4 => P115 | D5 => P115 | D6 => P114 | D7 => P114 | D8 => P113 | D9 => P113 | D10 => P112 | D11 => P112 | D12 => P111 | D13 => P111 | D14 => P110 | D15 => P110 | D16 => P109 | D17 => P109 | D18 => P108 | D19 => P108 | D20 => P107 | D21 => P107 | D22 => P106 | D23 => P106 | D24 => P105 | D25 => P105 | D26 => P104 | D27 => P104 | D28 => P103 | D29 => P103 | D30 => P102 | D31 => P102 | D32 => P101 | D33 => P101 | D34 => P100 | D35 => P100 | D36 => P99 | D37 => P99 | D38 => P98 | D39 => P98 | D40 => P97 | D41 => P97 | D42 => P96 | D43 => P96 | D44 => P95 | D45 => P95 | D46 => P94 | D47 => P94 | D48 => P93 | D49 => P93 | D50 => P92 | D51 => P92 | D52 => P91 | D53 => P91 | D54 => P90 | D55 => P90 | D56 => P89 | D57 => P89 | D58 => P88 | D59 => P88 | D60 => P87 | D61 => P87 | D62 => P86 | D63 => P86 end
    | D22 => match d0 with D0 => P118 | D1 => P118 | D2 => P117 | D3 => P117 | D4 => P116 | D5 => P116 | D6 => P115 | D7 => P115 | D8 => P114 | D9 => P114 | D10 => P113 | D11 => P113 | D12 => P112 | D13 => P112 | D14 => P111 | D15 => P111 | D16 => P110 | D17 => P110 | D18 => P109 | D19 => P109 | D20 => P108 | D21 => P108 | D22 => P107 | D23 => P107 | D24 => P106 | D25 => P106 | D26 => P105 | D27 => P105 | D28 => P104 | D29 => P104 | D30 => P103 | D31 => P103 | D32 => P102 | D33 => P102 | D34 => P101 | D35 => P101 | D36 => P100 | D37 => P100 | D38 => P99 | D39 => P99 | D40 => P98 | D41 => P98 | D42 => P97 | D43 => P97 | D44 => P96 | D45 => P96 | D46 => P95 | D47 => P95 | D48 => P94 | D49 => P94 | D50 => P93 | D51 => P93 | D52 => P92 | D53 => P92 | D54 => P91 | D55 => P91 | D56 => P90 | D57 => P90 | D58 => P89 | D59 => P89 | D60 => P88 | D61 => P88 | D62 => P87 | D63 => P87 end
    | D23 => match d0 with D0 => P119 | D1 => P119 | D2 => P118 | D3 => P118 | D4 => P117 | D5 => P117 | D6 => P116 | D7 => P116 | D8 => P115 | D9 => P115 | D10 => P114 | D11 => P114 | D12 => P113 | D13 => P113 | D14 => P112 | D15 => P112 | D16 => P111 | D17 => P111 | D18 => P110 | D19 => P110 | D20 => P109 | D21 => P109 | D22 => P108 | D23 => P108 | D24 => P107 | D25 => P107 | D26 => P106 | D27 => P106 | D28 => P105 | D29 => P105 | D30 => P104 | D31 => P104 | D32 => P103 | D33 => P103 | D34 => P102 | D35 => P102 | D36 => P101 | D37 => P101 | D38 => P100 | D39 => P100 | D40 => P99 | D41 => P99 | D42 => P98 | D43 => P98 | D44 => P97 | D45 => P97 | D46 => P96 | D47 => P96 | D48 => P95 | D49 => P95 | D50 => P94 | D51 => P94 | D52 => P93 | D53 => P93 | D54 => P92 | D55 => P92 | D56 => P91 | D57 => P91 | D58 => P90 | D59 => P90 | D60 => P89 | D61 => P89 | D62 => P88 | D63 => P88 end
    | D24 => match d0 with D0 => P120 | D1 => P120 | D2 => P119 | D3 => P119 | D4 => P118 | D5 => P118 | D6 => P117 | D7 => P117 | D8 => P116 | D9 => P116 | D10 => P115 | D11 => P115 | D12 => P114 | D13 => P114 | D14 => P113 | D15 => P113 | D16 => P112 | D17 => P112 | D18 => P111 | D19 => P111 | D20 => P110 | D21 => P110 | D22 => P109 | D23 => P109 | D24 => P108 | D25 => P108 | D26 => P107 | D27 => P107 | D28 => P106 | D29 => P106 | D30 => P105 | D31 => P105 | D32 => P104 | D33 => P104 | D34 => P103 | D35 => P103 | D36 => P102 | D37 => P102 | D38 => P101 | D39 => P101 | D40 => P100 | D41 => P100 | D42 => P99 | D43 => P99 | D44 => P98 | D45 => P98 | D46 => P97 | D47 => P97 | D48 => P96 | D49 => P96 | D50 => P95 | D51 => P95 | D52 => P94 | D53 => P94 | D54 => P93 | D55 => P93 | D56 => P92 | D57 => P92 | D58 => P91 | D59 => P91 | D60 => P90 | D61 => P90 | D62 => P89 | D63 => P89 end
    | D25 => match d0 with D0 => P121 | D1 => P121 | D2 => P120 | D3 => P120 | D4 => P119 | D5 => P119 | D6 => P118 | D7 => P118 | D8 => P117 | D9 => P117 | D10 => P116 | D11 => P116 | D12 => P115 | D13 => P115 | D14 => P114 | D15 => P114 | D16 => P113 | D17 => P113 | D18 => P112 | D19 => P112 | D20 => P111 | D21 => P111 | D22 => P110 | D23 => P110 | D24 => P109 | D25 => P109 | D26 => P108 | D27 => P108 | D28 => P107 | D29 => P107 | D30 => P106 | D31 => P106 | D32 => P105 | D33 => P105 | D34 => P104 | D35 => P104 | D36 => P103 | D37 => P103 | D38 => P102 | D39 => P102 | D40 => P101 | D41 => P101 | D42 => P100 | D43 => P100 | D44 => P99 | D45 => P99 | D46 => P98 | D47 => P98 | D48 => P97 | D49 => P97 | D50 => P96 | D51 => P96 | D52 => P95 | D53 => P95 | D54 => P94 | D55 => P94 | D56 => P93 | D57 => P93 | D58 => P92 | D59 => P92 | D60 => P91 | D61 => P91 | D62 => P90 | D63 => P90 end
    | D26 => match d0 with D0 => P122 | D1 => P122 | D2 => P121 | D3 => P121 | D4 => P120 | D5 => P120 | D6 => P119 | D7 => P119 | D8 => P118 | D9 => P118 | D10 => P117 | D11 => P117 | D12 => P116 | D13 => P116 | D14 => P115 | D15 => P115 | D16 => P114 | D17 => P114 | D18 => P113 | D19 => P113 | D20 => P112 | D21 => P112 | D22 => P111 | D23 => P111 | D24 => P110 | D25 => P110 | D26 => P109 | D27 => P109 | D28 => P108 | D29 => P108 | D30 => P107 | D31 => P107 | D32 => P106 | D33 => P106 | D34 => P105 | D35 => P105 | D36 => P104 | D37 => P104 | D38 => P103 | D39 => P103 | D40 => P102 | D41 => P102 | D42 => P101 | D43 => P101 | D44 => P100 | D45 => P100 | D46 => P99 | D47 => P99 | D48 => P98 | D49 => P98 | D50 => P97 | D51 => P97 | D52 => P96 | D53 => P96 | D54 => P95 | D55 => P95 | D56 => P94 | D57 => P94 | D58 => P93 | D59 => P93 | D60 => P92 | D61 => P92 | D62 => P91 | D63 => P91 end
    | D27 => match d0 with D0 => P123 | D1 => P123 | D2 => P122 | D3 => P122 | D4 => P121 | D5 => P121 | D6 => P120 | D7 => P120 | D8 => P119 | D9 => P119 | D10 => P118 | D11 => P118 | D12 => P117 | D13 => P117 | D14 => P116 | D15 => P116 | D16 => P115 | D17 => P115 | D18 => P114 | D19 => P114 | D20 => P113 | D21 => P113 | D22 => P112 | D23 => P112 | D24 => P111 | D25 => P111 | D26 => P110 | D27 => P110 | D28 => P109 | D29 => P109 | D30 => P108 | D31 => P108 | D32 => P107 | D33 => P107 | D34 => P106 | D35 => P106 | D36 => P105 | D37 => P105 | D38 => P104 | D39 => P104 | D40 => P103 | D41 => P103 | D42 => P102 | D43 => P102 | D44 => P101 | D45 => P101 | D46 => P100 | D47 => P100 | D48 => P99 | D49 => P99 | D50 => P98 | D51 => P98 | D52 => P97 | D53 => P97 | D54 => P96 | D55 => P96 | D56 => P95 | D57 => P95 | D58 => P94 | D59 => P94 | D60 => P93 | D61 => P93 | D62 => P92 | D63 => P92 end
    | D28 => match d0 with D0 => P124 | D1 => P124 | D2 => P123 | D3 => P123 | D4 => P122 | D5 => P122 | D6 => P121 | D7 => P121 | D8 => P120 | D9 => P120 | D10 => P119 | D11 => P119 | D12 => P118 | D13 => P118 | D14 => P117 | D15 => P117 | D16 => P116 | D17 => P116 | D18 => P115 | D19 => P115 | D20 => P114 | D21 => P114 | D22 => P113 | D23 => P113 | D24 => P112 | D25 => P112 | D26 => P111 | D27 => P111 | D28 => P110 | D29 => P110 | D30 => P109 | D31 => P109 | D32 => P108 | D33 => P108 | D34 => P107 | D35 => P107 | D36 => P106 | D37 => P106 | D38 => P105 | D39 => P105 | D40 => P104 | D41 => P104 | D42 => P103 | D43 => P103 | D44 => P102 | D45 => P102 | D46 => P101 | D47 => P101 | D48 => P100 | D49 => P100 | D50 => P99 | D51 => P99 | D52 => P98 | D53 => P98 | D54 => P97 | D55 => P97 | D56 => P96 | D57 => P96 | D58 => P95 | D59 => P95 | D60 => P94 | D61 => P94 | D62 => P93 | D63 => P93 end
    | D29 => match d0 with D0 => P125 | D1 => P125 | D2 => P124 | D3 => P124 | D4 => P123 | D5 => P123 | D6 => P122 | D7 => P122 | D8 => P121 | D9 => P121 | D10 => P120 | D11 => P120 | D12 => P119 | D13 => P119 | D14 => P118 | D15 => P118 | D16 => P117 | D17 => P117 | D18 => P116 | D19 => P116 | D20 => P115 | D21 => P115 | D22 => P114 | D23 => P114 | D24 => P113 | D25 => P113 | D26 => P112 | D27 => P112 | D28 => P111 | D29 => P111 | D30 => P110 | D31 => P110 | D32 => P109 | D33 => P109 | D34 => P108 | D35 => P108 | D36 => P107 | D37 => P107 | D38 => P106 | D39 => P106 | D40 => P105 | D41 => P105 | D42 => P104 | D43 => P104 | D44 => P103 | D45 => P103 | D46 => P102 | D47 => P102 | D48 => P101 | D49 => P101 | D50 => P100 | D51 => P100 | D52 => P99 | D53 => P99 | D54 => P98 | D55 => P98 | D56 => P97 | D57 => P97 | D58 => P96 | D59 => P96 | D60 => P95 | D61 => P95 | D62 => P94 | D63 => P94 end
    | D30 => match d0 with D0 => P126 | D1 => P126 | D2 => P125 | D3 => P125 | D4 => P124 | D5 => P124 | D6 => P123 | D7 => P123 | D8 => P122 | D9 => P122 | D10 => P121 | D11 => P121 | D12 => P120 | D13 => P120 | D14 => P119 | D15 => P119 | D16 => P118 | D17 => P118 | D18 => P117 | D19 => P117 | D20 => P116 | D21 => P116 | D22 => P115 | D23 => P115 | D24 => P114 | D25 => P114 | D26 => P113 | D27 => P113 | D28 => P112 | D29 => P112 | D30 => P111 | D31 => P111 | D32 => P110 | D33 => P110 | D34 => P109 | D35 => P109 | D36 => P108 | D37 => P108 | D38 => P107 | D39 => P107 | D40 => P106 | D41 => P106 | D42 => P105 | D43 => P105 | D44 => P104 | D45 => P104 | D46 => P103 | D47 => P103 | D48 => P102 | D49 => P102 | D50 => P101 | D51 => P101 | D52 => P100 | D53 => P100 | D54 => P99 | D55 => P99 | D56 => P98 | D57 => P98 | D58 => P97 | D59 => P97 | D60 => P96 | D61 => P96 | D62 => P95 | D63 => P95 end
    | D31 => match d0 with D0 => P127 | D1 => P127 | D2 => P126 | D3 => P126 | D4 => P125 | D5 => P125 | D6 => P124 | D7 => P124 | D8 => P123 | D9 => P123 | D10 => P122 | D11 => P122 | D12 => P121 | D13 => P121 | D14 => P120 | D15 => P120 | D16 => P119 | D17 => P119 | D18 => P118 | D19 => P118 | D20 => P117 | D21 => P117 | D22 => P116 | D23 => P116 | D24 => P115 | D25 => P115 | D26 => P114 | D27 => P114 | D28 => P113 | D29 => P113 | D30 => P112 | D31 => P112 | D32 => P111 | D33 => P111 | D34 => P110 | D35 => P110 | D36 => P109 | D37 => P109 | D38 => P108 | D39 => P108 | D40 => P107 | D41 => P107 | D42 => P106 | D43 => P106 | D44 => P105 | D45 => P105 | D46 => P104 | D47 => P104 | D48 => P103 | D49 => P103 | D50 => P102 | D51 => P102 | D52 => P101 | D53 => P101 | D54 => P100 | D55 => P100 | D56 => P99 | D57 => P99 | D58 => P98 | D59 => P98 | D60 => P97 | D61 => P97 | D62 => P96 | D63 => P96 end
    | D32 => match d0 with D0 => P0 | D1 => P0 | D2 => P127 | D3 => P127 | D4 => P126 | D5 => P126 | D6 => P125 | D7 => P125 | D8 => P124 | D9 => P124 | D10 => P123 | D11 => P123 | D12 => P122 | D13 => P122 | D14 => P121 | D15 => P121 | D16 => P120 | D17 => P120 | D18 => P119 | D19 => P119 | D20 => P118 | D21 => P118 | D22 => P117 | D23 => P117 | D24 => P116 | D25 => P116 | D26 => P115 | D27 => P115 | D28 => P114 | D29 => P114 | D30 => P113 | D31 => P113 | D32 => P112 | D33 => P112 | D34 => P111 | D35 => P111 | D36 => P110 | D37 => P110 | D38 => P109 | D39 => P109 | D40 => P108 | D41 => P108 | D42 => P107 | D43 => P107 | D44 => P106 | D45 => P106 | D46 => P105 | D47 => P105 | D48 => P104 | D49 => P104 | D50 => P103 | D51 => P103 | D52 => P102 | D53 => P102 | D54 => P101 | D55 => P101 | D56 => P100 | D57 => P100 | D58 => P99 | D59 => P99 | D60 => P98 | D61 => P98 | D62 => P97 | D63 => P97 end
    | D33 => match d0 with D0 => P1 | D1 => P1 | D2 => P0 | D3 => P0 | D4 => P127 | D5 => P127 | D6 => P126 | D7 => P126 | D8 => P125 | D9 => P125 | D10 => P124 | D11 => P124 | D12 => P123 | D13 => P123 | D14 => P122 | D15 => P122 | D16 => P121 | D17 => P121 | D18 => P120 | D19 => P120 | D20 => P119 | D21 => P119 | D22 => P118 | D23 => P118 | D24 => P117 | D25 => P117 | D26 => P116 | D27 => P116 | D28 => P115 | D29 => P115 | D30 => P114 | D31 => P114 | D32 => P113 | D33 => P113 | D34 => P112 | D35 => P112 | D36 => P111 | D37 => P111 | D38 => P110 | D39 => P110 | D40 => P109 | D41 => P109 | D42 => P108 | D43 => P108 | D44 => P107 | D45 => P107 | D46 => P106 | D47 => P106 | D48 => P105 | D49 => P105 | D50 => P104 | D51 => P104 | D52 => P103 | D53 => P103 | D54 => P102 | D55 => P102 | D56 => P101 | D57 => P101 | D58 => P100 | D59 => P100 | D60 => P99 | D61 => P99 | D62 => P98 | D63 => P98 end
    | D34 => match d0 with D0 => P2 | D1 => P2 | D2 => P1 | D3 => P1 | D4 => P0 | D5 => P0 | D6 => P127 | D7 => P127 | D8 => P126 | D9 => P126 | D10 => P125 | D11 => P125 | D12 => P124 | D13 => P124 | D14 => P123 | D15 => P123 | D16 => P122 | D17 => P122 | D18 => P121 | D19 => P121 | D20 => P120 | D21 => P120 | D22 => P119 | D23 => P119 | D24 => P118 | D25 => P118 | D26 => P117 | D27 => P117 | D28 => P116 | D29 => P116 | D30 => P115 | D31 => P115 | D32 => P114 | D33 => P114 | D34 => P113 | D35 => P113 | D36 => P112 | D37 => P112 | D38 => P111 | D39 => P111 | D40 => P110 | D41 => P110 | D42 => P109 | D43 => P109 | D44 => P108 | D45 => P108 | D46 => P107 | D47 => P107 | D48 => P106 | D49 => P106 | D50 => P105 | D51 => P105 | D52 => P104 | D53 => P104 | D54 => P103 | D55 => P103 | D56 => P102 | D57 => P102 | D58 => P101 | D59 => P101 | D60 => P100 | D61 => P100 | D62 => P99 | D63 => P99 end
    | D35 => match d0 with D0 => P3 | D1 => P3 | D2 => P2 | D3 => P2 | D4 => P1 | D5 => P1 | D6 => P0 | D7 => P0 | D8 => P127 | D9 => P127 | D10 => P126 | D11 => P126 | D12 => P125 | D13 => P125 | D14 => P124 | D15 => P124 | D16 => P123 | D17 => P123 | D18 => P122 | D19 => P122 | D20 => P121 | D21 => P121 | D22 => P120 | D23 => P120 | D24 => P119 | D25 => P119 | D26 => P118 | D27 => P118 | D28 => P117 | D29 => P117 | D30 => P116 | D31 => P116 | D32 => P115 | D33 => P115 | D34 => P114 | D35 => P114 | D36 => P113 | D37 => P113 | D38 => P112 | D39 => P112 | D40 => P111 | D41 => P111 | D42 => P110 | D43 => P110 | D44 => P109 | D45 => P109 | D46 => P108 | D47 => P108 | D48 => P107 | D49 => P107 | D50 => P106 | D51 => P106 | D52 => P105 | D53 => P105 | D54 => P104 | D55 => P104 | D56 => P103 | D57 => P103 | D58 => P102 | D59 => P102 | D60 => P101 | D61 => P101 | D62 => P100 | D63 => P100 end
    | D36 => match d0 with D0 => P4 | D1 => P4 | D2 => P3 | D3 => P3 | D4 => P2 | D5 => P2 | D6 => P1 | D7 => P1 | D8 => P0 | D9 => P0 | D10 => P127 | D11 => P127 | D12 => P126 | D13 => P126 | D14 => P125 | D15 => P125 | D16 => P124 | D17 => P124 | D18 => P123 | D19 => P123 | D20 => P122 | D21 => P122 | D22 => P121 | D23 => P121 | D24 => P120 | D25 => P120 | D26 => P119 | D27 => P119 | D28 => P118 | D29 => P118 | D30 => P117 | D31 => P117 | D32 => P116 | D33 => P116 | D34 => P115 | D35 => P115 | D36 => P114 | D37 => P114 | D38 => P113 | D39 => P113 | D40 => P112 | D41 => P112 | D42 => P111 | D43 => P111 | D44 => P110 | D45 => P110 | D46 => P109 | D47 => P109 | D48 => P108 | D49 => P108 | D50 => P107 | D51 => P107 | D52 => P106 | D53 => P106 | D54 => P105 | D55 => P105 | D56 => P104 | D57 => P104 | D58 => P103 | D59 => P103 | D60 => P102 | D61 => P102 | D62 => P101 | D63 => P101 end
    | D37 => match d0 with D0 => P5 | D1 => P5 | D2 => P4 | D3 => P4 | D4 => P3 | D5 => P3 | D6 => P2 | D7 => P2 | D8 => P1 | D9 => P1 | D10 => P0 | D11 => P0 | D12 => P127 | D13 => P127 | D14 => P126 | D15 => P126 | D16 => P125 | D17 => P125 | D18 => P124 | D19 => P124 | D20 => P123 | D21 => P123 | D22 => P122 | D23 => P122 | D24 => P121 | D25 => P121 | D26 => P120 | D27 => P120 | D28 => P119 | D29 => P119 | D30 => P118 | D31 => P118 | D32 => P117 | D33 => P117 | D34 => P116 | D35 => P116 | D36 => P115 | D37 => P115 | D38 => P114 | D39 => P114 | D40 => P113 | D41 => P113 | D42 => P112 | D43 => P112 | D44 => P111 | D45 => P111 | D46 => P110 | D47 => P110 | D48 => P109 | D49 => P109 | D50 => P108 | D51 => P108 | D52 => P107 | D53 => P107 | D54 => P106 | D55 => P106 | D56 => P105 | D57 => P105 | D58 => P104 | D59 => P104 | D60 => P103 | D61 => P103 | D62 => P102 | D63 => P102 end
    | D38 => match d0 with D0 => P6 | D1 => P6 | D2 => P5 | D3 => P5 | D4 => P4 | D5 => P4 | D6 => P3 | D7 => P3 | D8 => P2 | D9 => P2 | D10 => P1 | D11 => P1 | D12 => P0 | D13 => P0 | D14 => P127 | D15 => P127 | D16 => P126 | D17 => P126 | D18 => P125 | D19 => P125 | D20 => P124 | D21 => P124 | D22 => P123 | D23 => P123 | D24 => P122 | D25 => P122 | D26 => P121 | D27 => P121 | D28 => P120 | D29 => P120 | D30 => P119 | D31 => P119 | D32 => P118 | D33 => P118 | D34 => P117 | D35 => P117 | D36 => P116 | D37 => P116 | D38 => P115 | D39 => P115 | D40 => P114 | D41 => P114 | D42 => P113 | D43 => P113 | D44 => P112 | D45 => P112 | D46 => P111 | D47 => P111 | D48 => P110 | D49 => P110 | D50 => P109 | D51 => P109 | D52 => P108 | D53 => P108 | D54 => P107 | D55 => P107 | D56 => P106 | D57 => P106 | D58 => P105 | D59 => P105 | D60 => P104 | D61 => P104 | D62 => P103 | D63 => P103 end
    | D39 => match d0 with D0 => P7 | D1 => P7 | D2 => P6 | D3 => P6 | D4 => P5 | D5 => P5 | D6 => P4 | D7 => P4 | D8 => P3 | D9 => P3 | D10 => P2 | D11 => P2 | D12 => P1 | D13 => P1 | D14 => P0 | D15 => P0 | D16 => P127 | D17 => P127 | D18 => P126 | D19 => P126 | D20 => P125 | D21 => P125 | D22 => P124 | D23 => P124 | D24 => P123 | D25 => P123 | D26 => P122 | D27 => P122 | D28 => P121 | D29 => P121 | D30 => P120 | D31 => P120 | D32 => P119 | D33 => P119 | D34 => P118 | D35 => P118 | D36 => P117 | D37 => P117 | D38 => P116 | D39 => P116 | D40 => P115 | D41 => P115 | D42 => P114 | D43 => P114 | D44 => P113 | D45 => P113 | D46 => P112 | D47 => P112 | D48 => P111 | D49 => P111 | D50 => P110 | D51 => P110 | D52 => P109 | D53 => P109 | D54 => P108 | D55 => P108 | D56 => P107 | D57 => P107 | D58 => P106 | D59 => P106 | D60 => P105 | D61 => P105 | D62 => P104 | D63 => P104 end
    | D40 => match d0 with D0 => P8 | D1 => P8 | D2 => P7 | D3 => P7 | D4 => P6 | D5 => P6 | D6 => P5 | D7 => P5 | D8 => P4 | D9 => P4 | D10 => P3 | D11 => P3 | D12 => P2 | D13 => P2 | D14 => P1 | D15 => P1 | D16 => P0 | D17 => P0 | D18 => P127 | D19 => P127 | D20 => P126 | D21 => P126 | D22 => P125 | D23 => P125 | D24 => P124 | D25 => P124 | D26 => P123 | D27 => P123 | D28 => P122 | D29 => P122 | D30 => P121 | D31 => P121 | D32 => P120 | D33 => P120 | D34 => P119 | D35 => P119 | D36 => P118 | D37 => P118 | D38 => P117 | D39 => P117 | D40 => P116 | D41 => P116 | D42 => P115 | D43 => P115 | D44 => P114 | D45 => P114 | D46 => P113 | D47 => P113 | D48 => P112 | D49 => P112 | D50 => P111 | D51 => P111 | D52 => P110 | D53 => P110 | D54 => P109 | D55 => P109 | D56 => P108 | D57 => P108 | D58 => P107 | D59 => P107 | D60 => P106 | D61 => P106 | D62 => P105 | D63 => P105 end
    | D41 => match d0 with D0 => P9 | D1 => P9 | D2 => P8 | D3 => P8 | D4 => P7 | D5 => P7 | D6 => P6 | D7 => P6 | D8 => P5 | D9 => P5 | D10 => P4 | D11 => P4 | D12 => P3 | D13 => P3 | D14 => P2 | D15 => P2 | D16 => P1 | D17 => P1 | D18 => P0 | D19 => P0 | D20 => P127 | D21 => P127 | D22 => P126 | D23 => P126 | D24 => P125 | D25 => P125 | D26 => P124 | D27 => P124 | D28 => P123 | D29 => P123 | D30 => P122 | D31 => P122 | D32 => P121 | D33 => P121 | D34 => P120 | D35 => P120 | D36 => P119 | D37 => P119 | D38 => P118 | D39 => P118 | D40 => P117 | D41 => P117 | D42 => P116 | D43 => P116 | D44 => P115 | D45 => P115 | D46 => P114 | D47 => P114 | D48 => P113 | D49 => P113 | D50 => P112 | D51 => P112 | D52 => P111 | D53 => P111 | D54 => P110 | D55 => P110 | D56 => P109 | D57 => P109 | D58 => P108 | D59 => P108 | D60 => P107 | D61 => P107 | D62 => P106 | D63 => P106 end
    | D42 => match d0 with D0 => P10 | D1 => P10 | D2 => P9 | D3 => P9 | D4 => P8 | D5 => P8 | D6 => P7 | D7 => P7 | D8 => P6 | D9 => P6 | D10 => P5 | D11 => P5 | D12 => P4 | D13 => P4 | D14 => P3 | D15 => P3 | D16 => P2 | D17 => P2 | D18 => P1 | D19 => P1 | D20 => P0 | D21 => P0 | D22 => P127 | D23 => P127 | D24 => P126 | D25 => P126 | D26 => P125 | D27 => P125 | D28 => P124 | D29 => P124 | D30 => P123 | D31 => P123 | D32 => P122 | D33 => P122 | D34 => P121 | D35 => P121 | D36 => P120 | D37 => P120 | D38 => P119 | D39 => P119 | D40 => P118 | D41 => P118 | D42 => P117 | D43 => P117 | D44 => P116 | D45 => P116 | D46 => P115 | D47 => P115 | D48 => P114 | D49 => P114 | D50 => P113 | D51 => P113 | D52 => P112 | D53 => P112 | D54 => P111 | D55 => P111 | D56 => P110 | D57 => P110 | D58 => P109 | D59 => P109 | D60 => P108 | D61 => P108 | D62 => P107 | D63 => P107 end
    | D43 => match d0 with D0 => P11 | D1 => P11 | D2 => P10 | D3 => P10 | D4 => P9 | D5 => P9 | D6 => P8 | D7 => P8 | D8 => P7 | D9 => P7 | D10 => P6 | D11 => P6 | D12 => P5 | D13 => P5 | D14 => P4 | D15 => P4 | D16 => P3 | D17 => P3 | D18 => P2 | D19 => P2 | D20 => P1 | D21 => P1 | D22 => P0 | D23 => P0 | D24 => P127 | D25 => P127 | D26 => P126 | D27 => P126 | D28 => P125 | D29 => P125 | D30 => P124 | D31 => P124 | D32 => P123 | D33 => P123 | D34 => P122 | D35 => P122 | D36 => P121 | D37 => P121 | D38 => P120 | D39 => P120 | D40 => P119 | D41 => P119 | D42 => P118 | D43 => P118 | D44 => P117 | D45 => P117 | D46 => P116 | D47 => P116 | D48 => P115 | D49 => P115 | D50 => P114 | D51 => P114 | D52 => P113 | D53 => P113 | D54 => P112 | D55 => P112 | D56 => P111 | D57 => P111 | D58 => P110 | D59 => P110 | D60 => P109 | D61 => P109 | D62 => P108 | D63 => P108 end
    | D44 => match d0 with D0 => P12 | D1 => P12 | D2 => P11 | D3 => P11 | D4 => P10 | D5 => P10 | D6 => P9 | D7 => P9 | D8 => P8 | D9 => P8 | D10 => P7 | D11 => P7 | D12 => P6 | D13 => P6 | D14 => P5 | D15 => P5 | D16 => P4 | D17 => P4 | D18 => P3 | D19 => P3 | D20 => P2 | D21 => P2 | D22 => P1 | D23 => P1 | D24 => P0 | D25 => P0 | D26 => P127 | D27 => P127 | D28 => P126 | D29 => P126 | D30 => P125 | D31 => P125 | D32 => P124 | D33 => P124 | D34 => P123 | D35 => P123 | D36 => P122 | D37 => P122 | D38 => P121 | D39 => P121 | D40 => P120 | D41 => P120 | D42 => P119 | D43 => P119 | D44 => P118 | D45 => P118 | D46 => P117 | D47 => P117 | D48 => P116 | D49 => P116 | D50 => P115 | D51 => P115 | D52 => P114 | D53 => P114 | D54 => P113 | D55 => P113 | D56 => P112 | D57 => P112 | D58 => P111 | D59 => P111 | D60 => P110 | D61 => P110 | D62 => P109 | D63 => P109 end
    | D45 => match d0 with D0 => P13 | D1 => P13 | D2 => P12 | D3 => P12 | D4 => P11 | D5 => P11 | D6 => P10 | D7 => P10 | D8 => P9 | D9 => P9 | D10 => P8 | D11 => P8 | D12 => P7 | D13 => P7 | D14 => P6 | D15 => P6 | D16 => P5 | D17 => P5 | D18 => P4 | D19 => P4 | D20 => P3 | D21 => P3 | D22 => P2 | D23 => P2 | D24 => P1 | D25 => P1 | D26 => P0 | D27 => P0 | D28 => P127 | D29 => P127 | D30 => P126 | D31 => P126 | D32 => P125 | D33 => P125 | D34 => P124 | D35 => P124 | D36 => P123 | D37 => P123 | D38 => P122 | D39 => P122 | D40 => P121 | D41 => P121 | D42 => P120 | D43 => P120 | D44 => P119 | D45 => P119 | D46 => P118 | D47 => P118 | D48 => P117 | D49 => P117 | D50 => P116 | D51 => P116 | D52 => P115 | D53 => P115 | D54 => P114 | D55 => P114 | D56 => P113 | D57 => P113 | D58 => P112 | D59 => P112 | D60 => P111 | D61 => P111 | D62 => P110 | D63 => P110 end
    | D46 => match d0 with D0 => P14 | D1 => P14 | D2 => P13 | D3 => P13 | D4 => P12 | D5 => P12 | D6 => P11 | D7 => P11 | D8 => P10 | D9 => P10 | D10 => P9 | D11 => P9 | D12 => P8 | D13 => P8 | D14 => P7 | D15 => P7 | D16 => P6 | D17 => P6 | D18 => P5 | D19 => P5 | D20 => P4 | D21 => P4 | D22 => P3 | D23 => P3 | D24 => P2 | D25 => P2 | D26 => P1 | D27 => P1 | D28 => P0 | D29 => P0 | D30 => P127 | D31 => P127 | D32 => P126 | D33 => P126 | D34 => P125 | D35 => P125 | D36 => P124 | D37 => P124 | D38 => P123 | D39 => P123 | D40 => P122 | D41 => P122 | D42 => P121 | D43 => P121 | D44 => P120 | D45 => P120 | D46 => P119 | D47 => P119 | D48 => P118 | D49 => P118 | D50 => P117 | D51 => P117 | D52 => P116 | D53 => P116 | D54 => P115 | D55 => P115 | D56 => P114 | D57 => P114 | D58 => P113 | D59 => P113 | D60 => P112 | D61 => P112 | D62 => P111 | D63 => P111 end
    | D47 => match d0 with D0 => P15 | D1 => P15 | D2 => P14 | D3 => P14 | D4 => P13 | D5 => P13 | D6 => P12 | D7 => P12 | D8 => P11 | D9 => P11 | D10 => P10 | D11 => P10 | D12 => P9 | D13 => P9 | D14 => P8 | D15 => P8 | D16 => P7 | D17 => P7 | D18 => P6 | D19 => P6 | D20 => P5 | D21 => P5 | D22 => P4 | D23 => P4 | D24 => P3 | D25 => P3 | D26 => P2 | D27 => P2 | D28 => P1 | D29 => P1 | D30 => P0 | D31 => P0 | D32 => P127 | D33 => P127 | D34 => P126 | D35 => P126 | D36 => P125 | D37 => P125 | D38 => P124 | D39 => P124 | D40 => P123 | D41 => P123 | D42 => P122 | D43 => P122 | D44 => P121 | D45 => P121 | D46 => P120 | D47 => P120 | D48 => P119 | D49 => P119 | D50 => P118 | D51 => P118 | D52 => P117 | D53 => P117 | D54 => P116 | D55 => P116 | D56 => P115 | D57 => P115 | D58 => P114 | D59 => P114 | D60 => P113 | D61 => P113 | D62 => P112 | D63 => P112 end
    | D48 => match d0 with D0 => P16 | D1 => P16 | D2 => P15 | D3 => P15 | D4 => P14 | D5 => P14 | D6 => P13 | D7 => P13 | D8 => P12 | D9 => P12 | D10 => P11 | D11 => P11 | D12 => P10 | D13 => P10 | D14 => P9 | D15 => P9 | D16 => P8 | D17 => P8 | D18 => P7 | D19 => P7 | D20 => P6 | D21 => P6 | D22 => P5 | D23 => P5 | D24 => P4 | D25 => P4 | D26 => P3 | D27 => P3 | D28 => P2 | D29 => P2 | D30 => P1 | D31 => P1 | D32 => P0 | D33 => P0 | D34 => P127 | D35 => P127 | D36 => P126 | D37 => P126 | D38 => P125 | D39 => P125 | D40 => P124 | D41 => P124 | D42 => P123 | D43 => P123 | D44 => P122 | D45 => P122 | D46 => P121 | D47 => P121 | D48 => P120 | D49 => P120 | D50 => P119 | D51 => P119 | D52 => P118 | D53 => P118 | D54 => P117 | D55 => P117 | D56 => P116 | D57 => P116 | D58 => P115 | D59 => P115 | D60 => P114 | D61 => P114 | D62 => P113 | D63 => P113 end
    | D49 => match d0 with D0 => P17 | D1 => P17 | D2 => P16 | D3 => P16 | D4 => P15 | D5 => P15 | D6 => P14 | D7 => P14 | D8 => P13 | D9 => P13 | D10 => P12 | D11 => P12 | D12 => P11 | D13 => P11 | D14 => P10 | D15 => P10 | D16 => P9 | D17 => P9 | D18 => P8 | D19 => P8 | D20 => P7 | D21 => P7 | D22 => P6 | D23 => P6 | D24 => P5 | D25 => P5 | D26 => P4 | D27 => P4 | D28 => P3 | D29 => P3 | D30 => P2 | D31 => P2 | D32 => P1 | D33 => P1 | D34 => P0 | D35 => P0 | D36 => P127 | D37 => P127 | D38 => P126 | D39 => P126 | D40 => P125 | D41 => P125 | D42 => P124 | D43 => P124 | D44 => P123 | D45 => P123 | D46 => P122 | D47 => P122 | D48 => P121 | D49 => P121 | D50 => P120 | D51 => P120 | D52 => P119 | D53 => P119 | D54 => P118 | D55 => P118 | D56 => P117 | D57 => P117 | D58 => P116 | D59 => P116 | D60 => P115 | D61 => P115 | D62 => P114 | D63 => P114 end
    | D50 => match d0 with D0 => P18 | D1 => P18 | D2 => P17 | D3 => P17 | D4 => P16 | D5 => P16 | D6 => P15 | D7 => P15 | D8 => P14 | D9 => P14 | D10 => P13 | D11 => P13 | D12 => P12 | D13 => P12 | D14 => P11 | D15 => P11 | D16 => P10 | D17 => P10 | D18 => P9 | D19 => P9 | D20 => P8 | D21 => P8 | D22 => P7 | D23 => P7 | D24 => P6 | D25 => P6 | D26 => P5 | D27 => P5 | D28 => P4 | D29 => P4 | D30 => P3 | D31 => P3 | D32 => P2 | D33 => P2 | D34 => P1 | D35 => P1 | D36 => P0 | D37 => P0 | D38 => P127 | D39 => P127 | D40 => P126 | D41 => P126 | D42 => P125 | D43 => P125 | D44 => P124 | D45 => P124 | D46 => P123 | D47 => P123 | D48 => P122 | D49 => P122 | D50 => P121 | D51 => P121 | D52 => P120 | D53 => P120 | D54 => P119 | D55 => P119 | D56 => P118 | D57 => P118 | D58 => P117 | D59 => P117 | D60 => P116 | D61 => P116 | D62 => P115 | D63 => P115 end
    | D51 => match d0 with D0 => P19 | D1 => P19 | D2 => P18 | D3 => P18 | D4 => P17 | D5 => P17 | D6 => P16 | D7 => P16 | D8 => P15 | D9 => P15 | D10 => P14 | D11 => P14 | D12 => P13 | D13 => P13 | D14 => P12 | D15 => P12 | D16 => P11 | D17 => P11 | D18 => P10 | D19 => P10 | D20 => P9 | D21 => P9 | D22 => P8 | D23 => P8 | D24 => P7 | D25 => P7 | D26 => P6 | D27 => P6 | D28 => P5 | D29 => P5 | D30 => P4 | D31 => P4 | D32 => P3 | D33 => P3 | D34 => P2 | D35 => P2 | D36 => P1 | D37 => P1 | D38 => P0 | D39 => P0 | D40 => P127 | D41 => P127 | D42 => P126 | D43 => P126 | D44 => P125 | D45 => P125 | D46 => P124 | D47 => P124 | D48 => P123 | D49 => P123 | D50 => P122 | D51 => P122 | D52 => P121 | D53 => P121 | D54 => P120 | D55 => P120 | D56 => P119 | D57 => P119 | D58 => P118 | D59 => P118 | D60 => P117 | D61 => P117 | D62 => P116 | D63 => P116 end
    | D52 => match d0 with D0 => P20 | D1 => P20 | D2 => P19 | D3 => P19 | D4 => P18 | D5 => P18 | D6 => P17 | D7 => P17 | D8 => P16 | D9 => P16 | D10 => P15 | D11 => P15 | D12 => P14 | D13 => P14 | D14 => P13 | D15 => P13 | D16 => P12 | D17 => P12 | D18 => P11 | D19 => P11 | D20 => P10 | D21 => P10 | D22 => P9 | D23 => P9 | D24 => P8 | D25 => P8 | D26 => P7 | D27 => P7 | D28 => P6 | D29 => P6 | D30 => P5 | D31 => P5 | D32 => P4 | D33 => P4 | D34 => P3 | D35 => P3 | D36 => P2 | D37 => P2 | D38 => P1 | D39 => P1 | D40 => P0 | D41 => P0 | D42 => P127 | D43 => P127 | D44 => P126 | D45 => P126 | D46 => P125 | D47 => P125 | D48 => P124 | D49 => P124 | D50 => P123 | D51 => P123 | D52 => P122 | D53 => P122 | D54 => P121 | D55 => P121 | D56 => P120 | D57 => P120 | D58 => P119 | D59 => P119 | D60 => P118 | D61 => P118 | D62 => P117 | D63 => P117 end
    | D53 => match d0 with D0 => P21 | D1 => P21 | D2 => P20 | D3 => P20 | D4 => P19 | D5 => P19 | D6 => P18 | D7 => P18 | D8 => P17 | D9 => P17 | D10 => P16 | D11 => P16 | D12 => P15 | D13 => P15 | D14 => P14 | D15 => P14 | D16 => P13 | D17 => P13 | D18 => P12 | D19 => P12 | D20 => P11 | D21 => P11 | D22 => P10 | D23 => P10 | D24 => P9 | D25 => P9 | D26 => P8 | D27 => P8 | D28 => P7 | D29 => P7 | D30 => P6 | D31 => P6 | D32 => P5 | D33 => P5 | D34 => P4 | D35 => P4 | D36 => P3 | D37 => P3 | D38 => P2 | D39 => P2 | D40 => P1 | D41 => P1 | D42 => P0 | D43 => P0 | D44 => P127 | D45 => P127 | D46 => P126 | D47 => P126 | D48 => P125 | D49 => P125 | D50 => P124 | D51 => P124 | D52 => P123 | D53 => P123 | D54 => P122 | D55 => P122 | D56 => P121 | D57 => P121 | D58 => P120 | D59 => P120 | D60 => P119 | D61 => P119 | D62 => P118 | D63 => P118 end
    | D54 => match d0 with D0 => P22 | D1 => P22 | D2 => P21 | D3 => P21 | D4 => P20 | D5 => P20 | D6 => P19 | D7 => P19 | D8 => P18 | D9 => P18 | D10 => P17 | D11 => P17 | D12 => P16 | D13 => P16 | D14 => P15 | D15 => P15 | D16 => P14 | D17 => P14 | D18 => P13 | D19 => P13 | D20 => P12 | D21 => P12 | D22 => P11 | D23 => P11 | D24 => P10 | D25 => P10 | D26 => P9 | D27 => P9 | D28 => P8 | D29 => P8 | D30 => P7 | D31 => P7 | D32 => P6 | D33 => P6 | D34 => P5 | D35 => P5 | D36 => P4 | D37 => P4 | D38 => P3 | D39 => P3 | D40 => P2 | D41 => P2 | D42 => P1 | D43 => P1 | D44 => P0 | D45 => P0 | D46 => P127 | D47 => P127 | D48 => P126 | D49 => P126 | D50 => P125 | D51 => P125 | D52 => P124 | D53 => P124 | D54 => P123 | D55 => P123 | D56 => P122 | D57 => P122 | D58 => P121 | D59 => P121 | D60 => P120 | D61 => P120 | D62 => P119 | D63 => P119 end
    | D55 => match d0 with D0 => P23 | D1 => P23 | D2 => P22 | D3 => P22 | D4 => P21 | D5 => P21 | D6 => P20 | D7 => P20 | D8 => P19 | D9 => P19 | D10 => P18 | D11 => P18 | D12 => P17 | D13 => P17 | D14 => P16 | D15 => P16 | D16 => P15 | D17 => P15 | D18 => P14 | D19 => P14 | D20 => P13 | D21 => P13 | D22 => P12 | D23 => P12 | D24 => P11 | D25 => P11 | D26 => P10 | D27 => P10 | D28 => P9 | D29 => P9 | D30 => P8 | D31 => P8 | D32 => P7 | D33 => P7 | D34 => P6 | D35 => P6 | D36 => P5 | D37 => P5 | D38 => P4 | D39 => P4 | D40 => P3 | D41 => P3 | D42 => P2 | D43 => P2 | D44 => P1 | D45 => P1 | D46 => P0 | D47 => P0 | D48 => P127 | D49 => P127 | D50 => P126 | D51 => P126 | D52 => P125 | D53 => P125 | D54 => P124 | D55 => P124 | D56 => P123 | D57 => P123 | D58 => P122 | D59 => P122 | D60 => P121 | D61 => P121 | D62 => P120 | D63 => P120 end
    | D56 => match d0 with D0 => P24 | D1 => P24 | D2 => P23 | D3 => P23 | D4 => P22 | D5 => P22 | D6 => P21 | D7 => P21 | D8 => P20 | D9 => P20 | D10 => P19 | D11 => P19 | D12 => P18 | D13 => P18 | D14 => P17 | D15 => P17 | D16 => P16 | D17 => P16 | D18 => P15 | D19 => P15 | D20 => P14 | D21 => P14 | D22 => P13 | D23 => P13 | D24 => P12 | D25 => P12 | D26 => P11 | D27 => P11 | D28 => P10 | D29 => P10 | D30 => P9 | D31 => P9 | D32 => P8 | D33 => P8 | D34 => P7 | D35 => P7 | D36 => P6 | D37 => P6 | D38 => P5 | D39 => P5 | D40 => P4 | D41 => P4 | D42 => P3 | D43 => P3 | D44 => P2 | D45 => P2 | D46 => P1 | D47 => P1 | D48 => P0 | D49 => P0 | D50 => P127 | D51 => P127 | D52 => P126 | D53 => P126 | D54 => P125 | D55 => P125 | D56 => P124 | D57 => P124 | D58 => P123 | D59 => P123 | D60 => P122 | D61 => P122 | D62 => P121 | D63 => P121 end
    | D57 => match d0 with D0 => P25 | D1 => P25 | D2 => P24 | D3 => P24 | D4 => P23 | D5 => P23 | D6 => P22 | D7 => P22 | D8 => P21 | D9 => P21 | D10 => P20 | D11 => P20 | D12 => P19 | D13 => P19 | D14 => P18 | D15 => P18 | D16 => P17 | D17 => P17 | D18 => P16 | D19 => P16 | D20 => P15 | D21 => P15 | D22 => P14 | D23 => P14 | D24 => P13 | D25 => P13 | D26 => P12 | D27 => P12 | D28 => P11 | D29 => P11 | D30 => P10 | D31 => P10 | D32 => P9 | D33 => P9 | D34 => P8 | D35 => P8 | D36 => P7 | D37 => P7 | D38 => P6 | D39 => P6 | D40 => P5 | D41 => P5 | D42 => P4 | D43 => P4 | D44 => P3 | D45 => P3 | D46 => P2 | D47 => P2 | D48 => P1 | D49 => P1 | D50 => P0 | D51 => P0 | D52 => P127 | D53 => P127 | D54 => P126 | D55 => P126 | D56 => P125 | D57 => P125 | D58 => P124 | D59 => P124 | D60 => P123 | D61 => P123 | D62 => P122 | D63 => P122 end
    | D58 => match d0 with D0 => P26 | D1 => P26 | D2 => P25 | D3 => P25 | D4 => P24 | D5 => P24 | D6 => P23 | D7 => P23 | D8 => P22 | D9 => P22 | D10 => P21 | D11 => P21 | D12 => P20 | D13 => P20 | D14 => P19 | D15 => P19 | D16 => P18 | D17 => P18 | D18 => P17 | D19 => P17 | D20 => P16 | D21 => P16 | D22 => P15 | D23 => P15 | D24 => P14 | D25 => P14 | D26 => P13 | D27 => P13 | D28 => P12 | D29 => P12 | D30 => P11 | D31 => P11 | D32 => P10 | D33 => P10 | D34 => P9 | D35 => P9 | D36 => P8 | D37 => P8 | D38 => P7 | D39 => P7 | D40 => P6 | D41 => P6 | D42 => P5 | D43 => P5 | D44 => P4 | D45 => P4 | D46 => P3 | D47 => P3 | D48 => P2 | D49 => P2 | D50 => P1 | D51 => P1 | D52 => P0 | D53 => P0 | D54 => P127 | D55 => P127 | D56 => P126 | D57 => P126 | D58 => P125 | D59 => P125 | D60 => P124 | D61 => P124 | D62 => P123 | D63 => P123 end
    | D59 => match d0 with D0 => P27 | D1 => P27 | D2 => P26 | D3 => P26 | D4 => P25 | D5 => P25 | D6 => P24 | D7 => P24 | D8 => P23 | D9 => P23 | D10 => P22 | D11 => P22 | D12 => P21 | D13 => P21 | D14 => P20 | D15 => P20 | D16 => P19 | D17 => P19 | D18 => P18 | D19 => P18 | D20 => P17 | D21 => P17 | D22 => P16 | D23 => P16 | D24 => P15 | D25 => P15 | D26 => P14 | D27 => P14 | D28 => P13 | D29 => P13 | D30 => P12 | D31 => P12 | D32 => P11 | D33 => P11 | D34 => P10 | D35 => P10 | D36 => P9 | D37 => P9 | D38 => P8 | D39 => P8 | D40 => P7 | D41 => P7 | D42 => P6 | D43 => P6 | D44 => P5 | D45 => P5 | D46 => P4 | D47 => P4 | D48 => P3 | D49 => P3 | D50 => P2 | D51 => P2 | D52 => P1 | D53 => P1 | D54 => P0 | D55 => P0 | D56 => P127 | D57 => P127 | D58 => P126 | D59 => P126 | D60 => P125 | D61 => P125 | D62 => P124 | D63 => P124 end
    | D60 => match d0 with D0 => P28 | D1 => P28 | D2 => P27 | D3 => P27 | D4 => P26 | D5 => P26 | D6 => P25 | D7 => P25 | D8 => P24 | D9 => P24 | D10 => P23 | D11 => P23 | D12 => P22 | D13 => P22 | D14 => P21 | D15 => P21 | D16 => P20 | D17 => P20 | D18 => P19 | D19 => P19 | D20 => P18 | D21 => P18 | D22 => P17 | D23 => P17 | D24 => P16 | D25 => P16 | D26 => P15 | D27 => P15 | D28 => P14 | D29 => P14 | D30 => P13 | D31 => P13 | D32 => P12 | D33 => P12 | D34 => P11 | D35 => P11 | D36 => P10 | D37 => P10 | D38 => P9 | D39 => P9 | D40 => P8 | D41 => P8 | D42 => P7 | D43 => P7 | D44 => P6 | D45 => P6 | D46 => P5 | D47 => P5 | D48 => P4 | D49 => P4 | D50 => P3 | D51 => P3 | D52 => P2 | D53 => P2 | D54 => P1 | D55 => P1 | D56 => P0 | D57 => P0 | D58 => P127 | D59 => P127 | D60 => P126 | D61 => P126 | D62 => P125 | D63 => P125 end
    | D61 => match d0 with D0 => P29 | D1 => P29 | D2 => P28 | D3 => P28 | D4 => P27 | D5 => P27 | D6 => P26 | D7 => P26 | D8 => P25 | D9 => P25 | D10 => P24 | D11 => P24 | D12 => P23 | D13 => P23 | D14 => P22 | D15 => P22 | D16 => P21 | D17 => P21 | D18 => P20 | D19 => P20 | D20 => P19 | D21 => P19 | D22 => P18 | D23 => P18 | D24 => P17 | D25 => P17 | D26 => P16 | D27 => P16 | D28 => P15 | D29 => P15 | D30 => P14 | D31 => P14 | D32 => P13 | D33 => P13 | D34 => P12 | D35 => P12 | D36 => P11 | D37 => P11 | D38 => P10 | D39 => P10 | D40 => P9 | D41 => P9 | D42 => P8 | D43 => P8 | D44 => P7 | D45 => P7 | D46 => P6 | D47 => P6 | D48 => P5 | D49 => P5 | D50 => P4 | D51 => P4 | D52 => P3 | D53 => P3 | D54 => P2 | D55 => P2 | D56 => P1 | D57 => P1 | D58 => P0 | D59 => P0 | D60 => P127 | D61 => P127 | D62 => P126 | D63 => P126 end
    | D62 => match d0 with D0 => P30 | D1 => P30 | D2 => P29 | D3 => P29 | D4 => P28 | D5 => P28 | D6 => P27 | D7 => P27 | D8 => P26 | D9 => P26 | D10 => P25 | D11 => P25 | D12 => P24 | D13 => P24 | D14 => P23 | D15 => P23 | D16 => P22 | D17 => P22 | D18 => P21 | D19 => P21 | D20 => P20 | D21 => P20 | D22 => P19 | D23 => P19 | D24 => P18 | D25 => P18 | D26 => P17 | D27 => P17 | D28 => P16 | D29 => P16 | D30 => P15 | D31 => P15 | D32 => P14 | D33 => P14 | D34 => P13 | D35 => P13 | D36 => P12 | D37 => P12 | D38 => P11 | D39 => P11 | D40 => P10 | D41 => P10 | D42 => P9 | D43 => P9 | D44 => P8 | D45 => P8 | D46 => P7 | D47 => P7 | D48 => P6 | D49 => P6 | D50 => P5 | D51 => P5 | D52 => P4 | D53 => P4 | D54 => P3 | D55 => P3 | D56 => P2 | D57 => P2 | D58 => P1 | D59 => P1 | D60 => P0 | D61 => P0 | D62 => P127 | D63 => P127 end
    | D63 => match d0 with D0 => P31 | D1 => P31 | D2 => P30 | D3 => P30 | D4 => P29 | D5 => P29 | D6 => P28 | D7 => P28 | D8 => P27 | D9 => P27 | D10 => P26 | D11 => P26 | D12 => P25 | D13 => P25 | D14 => P24 | D15 => P24 | D16 => P23 | D17 => P23 | D18 => P22 | D19 => P22 | D20 => P21 | D21 => P21 | D22 => P20 | D23 => P20 | D24 => P19 | D25 => P19 | D26 => P18 | D27 => P18 | D28 => P17 | D29 => P17 | D30 => P16 | D31 => P16 | D32 => P15 | D33 => P15 | D34 => P14 | D35 => P14 | D36 => P13 | D37 => P13 | D38 => P12 | D39 => P12 | D40 => P11 | D41 => P11 | D42 => P10 | D43 => P10 | D44 => P9 | D45 => P9 | D46 => P8 | D47 => P8 | D48 => P7 | D49 => P7 | D50 => P6 | D51 => P6 | D52 => P5 | D53 => P5 | D54 => P4 | D55 => P4 | D56 => P3 | D57 => P3 | D58 => P2 | D59 => P2 | D60 => P1 | D61 => P1 | D62 => P0 | D63 => P0 end
    end else match a with
    | D0 => match d0 with D0 => P0 | D1 => P0 | D2 => P127 | D3 => P127 | D4 => P126 | D5 => P126 | D6 => P125 | D7 => P125 | D8 => P124 | D9 => P124 | D10 => P123 | D11 => P123 | D12 => P122 | D13 => P122 | D14 => P121 | D15 => P121 | D16 => P120 | D17 => P120 | D18 => P119 | D19 => P119 | D20 => P118 | D21 => P118 | D22 => P117 | D23 => P117 | D24 => P116 | D25 => P116 | D26 => P115 | D27 => P115 | D28 => P114 | D29 => P114 | D30 => P113 | D31 => P113 | D32 => P112 | D33 => P112 | D34 => P111 | D35 => P111 | D36 => P110 | D37 => P110 | D38 => P109 | D39 => P109 | D40 => P108 | D41 => P108 | D42 => P107 | D43 => P107 | D44 => P106 | D45 => P106 | D46 => P105 | D47 => P105 | D48 => P104 | D49 => P104 | D50 => P103 | D51 => P103 | D52 => P102 | D53 => P102 | D54 => P101 | D55 => P101 | D56 => P100 | D57 => P100 | D58 => P99 | D59 => P99 | D60 => P98 | D61 => P98 | D62 => P97 | D63 => P97 end
    | D1 => match d0 with D0 => P1 | D1 => P1 | D2 => P0 | D3 => P0 | D4 => P127 | D5 => P127 | D6 => P126 | D7 => P126 | D8 => P125 | D9 => P125 | D10 => P124 | D11 => P124 | D12 => P123 | D13 => P123 | D14 => P122 | D15 => P122 | D16 => P121 | D17 => P121 | D18 => P120 | D19 => P120 | D20 => P119 | D21 => P119 | D22 => P118 | D23 => P118 | D24 => P117 | D25 => P117 | D26 => P116 | D27 => P116 | D28 => P115 | D29 => P115 | D30 => P114 | D31 => P114 | D32 => P113 | D33 => P113 | D34 => P112 | D35 => P112 | D36 => P111 | D37 => P111 | D38 => P110 | D39 => P110 | D40 => P109 | D41 => P109 | D42 => P108 | D43 => P108 | D44 => P107 | D45 => P107 | D46 => P106 | D47 => P106 | D48 => P105 | D49 => P105 | D50 => P104 | D51 => P104 | D52 => P103 | D53 => P103 | D54 => P102 | D55 => P102 | D56 => P101 | D57 => P101 | D58 => P100 | D59 => P100 | D60 => P99 | D61 => P99 | D62 => P98 | D63 => P98 end
    | D2 => match d0 with D0 => P2 | D1 => P2 | D2 => P1 | D3 => P1 | D4 => P0 | D5 => P0 | D6 => P127 | D7 => P127 | D8 => P126 | D9 => P126 | D10 => P125 | D11 => P125 | D12 => P124 | D13 => P124 | D14 => P123 | D15 => P123 | D16 => P122 | D17 => P122 | D18 => P121 | D19 => P121 | D20 => P120 | D21 => P120 | D22 => P119 | D23 => P119 | D24 => P118 | D25 => P118 | D26 => P117 | D27 => P117 | D28 => P116 | D29 => P116 | D30 => P115 | D31 => P115 | D32 => P114 | D33 => P114 | D34 => P113 | D35 => P113 | D36 => P112 | D37 => P112 | D38 => P111 | D39 => P111 | D40 => P110 | D41 => P110 | D42 => P109 | D43 => P109 | D44 => P108 | D45 => P108 | D46 => P107 | D47 => P107 | D48 => P106 | D49 => P106 | D50 => P105 | D51 => P105 | D52 => P104 | D53 => P104 | D54 => P103 | D55 => P103 | D56 => P102 | D57 => P102 | D58 => P101 | D59 => P101 | D60 => P100 | D61 => P100 | D62 => P99 | D63 => P99 end
    | D3 => match d0 with D0 => P3 | D1 => P3 | D2 => P2 | D3 => P2 | D4 => P1 | D5 => P1 | D6 => P0 | D7 => P0 | D8 => P127 | D9 => P127 | D10 => P126 | D11 => P126 | D12 => P125 | D13 => P125 | D14 => P124 | D15 => P124 | D16 => P123 | D17 => P123 | D18 => P122 | D19 => P122 | D20 => P121 | D21 => P121 | D22 => P120 | D23 => P120 | D24 => P119 | D25 => P119 | D26 => P118 | D27 => P118 | D28 => P117 | D29 => P117 | D30 => P116 | D31 => P116 | D32 => P115 | D33 => P115 | D34 => P114 | D35 => P114 | D36 => P113 | D37 => P113 | D38 => P112 | D39 => P112 | D40 => P111 | D41 => P111 | D42 => P110 | D43 => P110 | D44 => P109 | D45 => P109 | D46 => P108 | D47 => P108 | D48 => P107 | D49 => P107 | D50 => P106 | D51 => P106 | D52 => P105 | D53 => P105 | D54 => P104 | D55 => P104 | D56 => P103 | D57 => P103 | D58 => P102 | D59 => P102 | D60 => P101 | D61 => P101 | D62 => P100 | D63 => P100 end
    | D4 => match d0 with D0 => P4 | D1 => P4 | D2 => P3 | D3 => P3 | D4 => P2 | D5 => P2 | D6 => P1 | D7 => P1 | D8 => P0 | D9 => P0 | D10 => P127 | D11 => P127 | D12 => P126 | D13 => P126 | D14 => P125 | D15 => P125 | D16 => P124 | D17 => P124 | D18 => P123 | D19 => P123 | D20 => P122 | D21 => P122 | D22 => P121 | D23 => P121 | D24 => P120 | D25 => P120 | D26 => P119 | D27 => P119 | D28 => P118 | D29 => P118 | D30 => P117 | D31 => P117 | D32 => P116 | D33 => P116 | D34 => P115 | D35 => P115 | D36 => P114 | D37 => P114 | D38 => P113 | D39 => P113 | D40 => P112 | D41 => P112 | D42 => P111 | D43 => P111 | D44 => P110 | D45 => P110 | D46 => P109 | D47 => P109 | D48 => P108 | D49 => P108 | D50 => P107 | D51 => P107 | D52 => P106 | D53 => P106 | D54 => P105 | D55 => P105 | D56 => P104 | D57 => P104 | D58 => P103 | D59 => P103 | D60 => P102 | D61 => P102 | D62 => P101 | D63 => P101 end
    | D5 => match d0 with D0 => P5 | D1 => P5 | D2 => P4 | D3 => P4 | D4 => P3 | D5 => P3 | D6 => P2 | D7 => P2 | D8 => P1 | D9 => P1 | D10 => P0 | D11 => P0 | D12 => P127 | D13 => P127 | D14 => P126 | D15 => P126 | D16 => P125 | D17 => P125 | D18 => P124 | D19 => P124 | D20 => P123 | D21 => P123 | D22 => P122 | D23 => P122 | D24 => P121 | D25 => P121 | D26 => P120 | D27 => P120 | D28 => P119 | D29 => P119 | D30 => P118 | D31 => P118 | D32 => P117 | D33 => P117 | D34 => P116 | D35 => P116 | D36 => P115 | D37 => P115 | D38 => P114 | D39 => P114 | D40 => P113 | D41 => P113 | D42 => P112 | D43 => P112 | D44 => P111 | D45 => P111 | D46 => P110 | D47 => P110 | D48 => P109 | D49 => P109 | D50 => P108 | D51 => P108 | D52 => P107 | D53 => P107 | D54 => P106 | D55 => P106 | D56 => P105 | D57 => P105 | D58 => P104 | D59 => P104 | D60 => P103 | D61 => P103 | D62 => P102 | D63 => P102 end
    | D6 => match d0 with D0 => P6 | D1 => P6 | D2 => P5 | D3 => P5 | D4 => P4 | D5 => P4 | D6 => P3 | D7 => P3 | D8 => P2 | D9 => P2 | D10 => P1 | D11 => P1 | D12 => P0 | D13 => P0 | D14 => P127 | D15 => P127 | D16 => P126 | D17 => P126 | D18 => P125 | D19 => P125 | D20 => P124 | D21 => P124 | D22 => P123 | D23 => P123 | D24 => P122 | D25 => P122 | D26 => P121 | D27 => P121 | D28 => P120 | D29 => P120 | D30 => P119 | D31 => P119 | D32 => P118 | D33 => P118 | D34 => P117 | D35 => P117 | D36 => P116 | D37 => P116 | D38 => P115 | D39 => P115 | D40 => P114 | D41 => P114 | D42 => P113 | D43 => P113 | D44 => P112 | D45 => P112 | D46 => P111 | D47 => P111 | D48 => P110 | D49 => P110 | D50 => P109 | D51 => P109 | D52 => P108 | D53 => P108 | D54 => P107 | D55 => P107 | D56 => P106 | D57 => P106 | D58 => P105 | D59 => P105 | D60 => P104 | D61 => P104 | D62 => P103 | D63 => P103 end
    | D7 => match d0 with D0 => P7 | D1 => P7 | D2 => P6 | D3 => P6 | D4 => P5 | D5 => P5 | D6 => P4 | D7 => P4 | D8 => P3 | D9 => P3 | D10 => P2 | D11 => P2 | D12 => P1 | D13 => P1 | D14 => P0 | D15 => P0 | D16 => P127 | D17 => P127 | D18 => P126 | D19 => P126 | D20 => P125 | D21 => P125 | D22 => P124 | D23 => P124 | D24 => P123 | D25 => P123 | D26 => P122 | D27 => P122 | D28 => P121 | D29 => P121 | D30 => P120 | D31 => P120 | D32 => P119 | D33 => P119 | D34 => P118 | D35 => P118 | D36 => P117 | D37 => P117 | D38 => P116 | D39 => P116 | D40 => P115 | D41 => P115 | D42 => P114 | D43 => P114 | D44 => P113 | D45 => P113 | D46 => P112 | D47 => P112 | D48 => P111 | D49 => P111 | D50 => P110 | D51 => P110 | D52 => P109 | D53 => P109 | D54 => P108 | D55 => P108 | D56 => P107 | D57 => P107 | D58 => P106 | D59 => P106 | D60 => P105 | D61 => P105 | D62 => P104 | D63 => P104 end
    | D8 => match d0 with D0 => P8 | D1 => P8 | D2 => P7 | D3 => P7 | D4 => P6 | D5 => P6 | D6 => P5 | D7 => P5 | D8 => P4 | D9 => P4 | D10 => P3 | D11 => P3 | D12 => P2 | D13 => P2 | D14 => P1 | D15 => P1 | D16 => P0 | D17 => P0 | D18 => P127 | D19 => P127 | D20 => P126 | D21 => P126 | D22 => P125 | D23 => P125 | D24 => P124 | D25 => P124 | D26 => P123 | D27 => P123 | D28 => P122 | D29 => P122 | D30 => P121 | D31 => P121 | D32 => P120 | D33 => P120 | D34 => P119 | D35 => P119 | D36 => P118 | D37 => P118 | D38 => P117 | D39 => P117 | D40 => P116 | D41 => P116 | D42 => P115 | D43 => P115 | D44 => P114 | D45 => P114 | D46 => P113 | D47 => P113 | D48 => P112 | D49 => P112 | D50 => P111 | D51 => P111 | D52 => P110 | D53 => P110 | D54 => P109 | D55 => P109 | D56 => P108 | D57 => P108 | D58 => P107 | D59 => P107 | D60 => P106 | D61 => P106 | D62 => P105 | D63 => P105 end
    | D9 => match d0 with D0 => P9 | D1 => P9 | D2 => P8 | D3 => P8 | D4 => P7 | D5 => P7 | D6 => P6 | D7 => P6 | D8 => P5 | D9 => P5 | D10 => P4 | D11 => P4 | D12 => P3 | D13 => P3 | D14 => P2 | D15 => P2 | D16 => P1 | D17 => P1 | D18 => P0 | D19 => P0 | D20 => P127 | D21 => P127 | D22 => P126 | D23 => P126 | D24 => P125 | D25 => P125 | D26 => P124 | D27 => P124 | D28 => P123 | D29 => P123 | D30 => P122 | D31 => P122 | D32 => P121 | D33 => P121 | D34 => P120 | D35 => P120 | D36 => P119 | D37 => P119 | D38 => P118 | D39 => P118 | D40 => P117 | D41 => P117 | D42 => P116 | D43 => P116 | D44 => P115 | D45 => P115 | D46 => P114 | D47 => P114 | D48 => P113 | D49 => P113 | D50 => P112 | D51 => P112 | D52 => P111 | D53 => P111 | D54 => P110 | D55 => P110 | D56 => P109 | D57 => P109 | D58 => P108 | D59 => P108 | D60 => P107 | D61 => P107 | D62 => P106 | D63 => P106 end
    | D10 => match d0 with D0 => P10 | D1 => P10 | D2 => P9 | D3 => P9 | D4 => P8 | D5 => P8 | D6 => P7 | D7 => P7 | D8 => P6 | D9 => P6 | D10 => P5 | D11 => P5 | D12 => P4 | D13 => P4 | D14 => P3 | D15 => P3 | D16 => P2 | D17 => P2 | D18 => P1 | D19 => P1 | D20 => P0 | D21 => P0 | D22 => P127 | D23 => P127 | D24 => P126 | D25 => P126 | D26 => P125 | D27 => P125 | D28 => P124 | D29 => P124 | D30 => P123 | D31 => P123 | D32 => P122 | D33 => P122 | D34 => P121 | D35 => P121 | D36 => P120 | D37 => P120 | D38 => P119 | D39 => P119 | D40 => P118 | D41 => P118 | D42 => P117 | D43 => P117 | D44 => P116 | D45 => P116 | D46 => P115 | D47 => P115 | D48 => P114 | D49 => P114 | D50 => P113 | D51 => P113 | D52 => P112 | D53 => P112 | D54 => P111 | D55 => P111 | D56 => P110 | D57 => P110 | D58 => P109 | D59 => P109 | D60 => P108 | D61 => P108 | D62 => P107 | D63 => P107 end
    | D11 => match d0 with D0 => P11 | D1 => P11 | D2 => P10 | D3 => P10 | D4 => P9 | D5 => P9 | D6 => P8 | D7 => P8 | D8 => P7 | D9 => P7 | D10 => P6 | D11 => P6 | D12 => P5 | D13 => P5 | D14 => P4 | D15 => P4 | D16 => P3 | D17 => P3 | D18 => P2 | D19 => P2 | D20 => P1 | D21 => P1 | D22 => P0 | D23 => P0 | D24 => P127 | D25 => P127 | D26 => P126 | D27 => P126 | D28 => P125 | D29 => P125 | D30 => P124 | D31 => P124 | D32 => P123 | D33 => P123 | D34 => P122 | D35 => P122 | D36 => P121 | D37 => P121 | D38 => P120 | D39 => P120 | D40 => P119 | D41 => P119 | D42 => P118 | D43 => P118 | D44 => P117 | D45 => P117 | D46 => P116 | D47 => P116 | D48 => P115 | D49 => P115 | D50 => P114 | D51 => P114 | D52 => P113 | D53 => P113 | D54 => P112 | D55 => P112 | D56 => P111 | D57 => P111 | D58 => P110 | D59 => P110 | D60 => P109 | D61 => P109 | D62 => P108 | D63 => P108 end
    | D12 => match d0 with D0 => P12 | D1 => P12 | D2 => P11 | D3 => P11 | D4 => P10 | D5 => P10 | D6 => P9 | D7 => P9 | D8 => P8 | D9 => P8 | D10 => P7 | D11 => P7 | D12 => P6 | D13 => P6 | D14 => P5 | D15 => P5 | D16 => P4 | D17 => P4 | D18 => P3 | D19 => P3 | D20 => P2 | D21 => P2 | D22 => P1 | D23 => P1 | D24 => P0 | D25 => P0 | D26 => P127 | D27 => P127 | D28 => P126 | D29 => P126 | D30 => P125 | D31 => P125 | D32 => P124 | D33 => P124 | D34 => P123 | D35 => P123 | D36 => P122 | D37 => P122 | D38 => P121 | D39 => P121 | D40 => P120 | D41 => P120 | D42 => P119 | D43 => P119 | D44 => P118 | D45 => P118 | D46 => P117 | D47 => P117 | D48 => P116 | D49 => P116 | D50 => P115 | D51 => P115 | D52 => P114 | D53 => P114 | D54 => P113 | D55 => P113 | D56 => P112 | D57 => P112 | D58 => P111 | D59 => P111 | D60 => P110 | D61 => P110 | D62 => P109 | D63 => P109 end
    | D13 => match d0 with D0 => P13 | D1 => P13 | D2 => P12 | D3 => P12 | D4 => P11 | D5 => P11 | D6 => P10 | D7 => P10 | D8 => P9 | D9 => P9 | D10 => P8 | D11 => P8 | D12 => P7 | D13 => P7 | D14 => P6 | D15 => P6 | D16 => P5 | D17 => P5 | D18 => P4 | D19 => P4 | D20 => P3 | D21 => P3 | D22 => P2 | D23 => P2 | D24 => P1 | D25 => P1 | D26 => P0 | D27 => P0 | D28 => P127 | D29 => P127 | D30 => P126 | D31 => P126 | D32 => P125 | D33 => P125 | D34 => P124 | D35 => P124 | D36 => P123 | D37 => P123 | D38 => P122 | D39 => P122 | D40 => P121 | D41 => P121 | D42 => P120 | D43 => P120 | D44 => P119 | D45 => P119 | D46 => P118 | D47 => P118 | D48 => P117 | D49 => P117 | D50 => P116 | D51 => P116 | D52 => P115 | D53 => P115 | D54 => P114 | D55 => P114 | D56 => P113 | D57 => P113 | D58 => P112 | D59 => P112 | D60 => P111 | D61 => P111 | D62 => P110 | D63 => P110 end
    | D14 => match d0 with D0 => P14 | D1 => P14 | D2 => P13 | D3 => P13 | D4 => P12 | D5 => P12 | D6 => P11 | D7 => P11 | D8 => P10 | D9 => P10 | D10 => P9 | D11 => P9 | D12 => P8 | D13 => P8 | D14 => P7 | D15 => P7 | D16 => P6 | D17 => P6 | D18 => P5 | D19 => P5 | D20 => P4 | D21 => P4 | D22 => P3 | D23 => P3 | D24 => P2 | D25 => P2 | D26 => P1 | D27 => P1 | D28 => P0 | D29 => P0 | D30 => P127 | D31 => P127 | D32 => P126 | D33 => P126 | D34 => P125 | D35 => P125 | D36 => P124 | D37 => P124 | D38 => P123 | D39 => P123 | D40 => P122 | D41 => P122 | D42 => P121 | D43 => P121 | D44 => P120 | D45 => P120 | D46 => P119 | D47 => P119 | D48 => P118 | D49 => P118 | D50 => P117 | D51 => P117 | D52 => P116 | D53 => P116 | D54 => P115 | D55 => P115 | D56 => P114 | D57 => P114 | D58 => P113 | D59 => P113 | D60 => P112 | D61 => P112 | D62 => P111 | D63 => P111 end
    | D15 => match d0 with D0 => P15 | D1 => P15 | D2 => P14 | D3 => P14 | D4 => P13 | D5 => P13 | D6 => P12 | D7 => P12 | D8 => P11 | D9 => P11 | D10 => P10 | D11 => P10 | D12 => P9 | D13 => P9 | D14 => P8 | D15 => P8 | D16 => P7 | D17 => P7 | D18 => P6 | D19 => P6 | D20 => P5 | D21 => P5 | D22 => P4 | D23 => P4 | D24 => P3 | D25 => P3 | D26 => P2 | D27 => P2 | D28 => P1 | D29 => P1 | D30 => P0 | D31 => P0 | D32 => P127 | D33 => P127 | D34 => P126 | D35 => P126 | D36 => P125 | D37 => P125 | D38 => P124 | D39 => P124 | D40 => P123 | D41 => P123 | D42 => P122 | D43 => P122 | D44 => P121 | D45 => P121 | D46 => P120 | D47 => P120 | D48 => P119 | D49 => P119 | D50 => P118 | D51 => P118 | D52 => P117 | D53 => P117 | D54 => P116 | D55 => P116 | D56 => P115 | D57 => P115 | D58 => P114 | D59 => P114 | D60 => P113 | D61 => P113 | D62 => P112 | D63 => P112 end
    | D16 => match d0 with D0 => P16 | D1 => P16 | D2 => P15 | D3 => P15 | D4 => P14 | D5 => P14 | D6 => P13 | D7 => P13 | D8 => P12 | D9 => P12 | D10 => P11 | D11 => P11 | D12 => P10 | D13 => P10 | D14 => P9 | D15 => P9 | D16 => P8 | D17 => P8 | D18 => P7 | D19 => P7 | D20 => P6 | D21 => P6 | D22 => P5 | D23 => P5 | D24 => P4 | D25 => P4 | D26 => P3 | D27 => P3 | D28 => P2 | D29 => P2 | D30 => P1 | D31 => P1 | D32 => P0 | D33 => P0 | D34 => P127 | D35 => P127 | D36 => P126 | D37 => P126 | D38 => P125 | D39 => P125 | D40 => P124 | D41 => P124 | D42 => P123 | D43 => P123 | D44 => P122 | D45 => P122 | D46 => P121 | D47 => P121 | D48 => P120 | D49 => P120 | D50 => P119 | D51 => P119 | D52 => P118 | D53 => P118 | D54 => P117 | D55 => P117 | D56 => P116 | D57 => P116 | D58 => P115 | D59 => P115 | D60 => P114 | D61 => P114 | D62 => P113 | D63 => P113 end
    | D17 => match d0 with D0 => P17 | D1 => P17 | D2 => P16 | D3 => P16 | D4 => P15 | D5 => P15 | D6 => P14 | D7 => P14 | D8 => P13 | D9 => P13 | D10 => P12 | D11 => P12 | D12 => P11 | D13 => P11 | D14 => P10 | D15 => P10 | D16 => P9 | D17 => P9 | D18 => P8 | D19 => P8 | D20 => P7 | D21 => P7 | D22 => P6 | D23 => P6 | D24 => P5 | D25 => P5 | D26 => P4 | D27 => P4 | D28 => P3 | D29 => P3 | D30 => P2 | D31 => P2 | D32 => P1 | D33 => P1 | D34 => P0 | D35 => P0 | D36 => P127 | D37 => P127 | D38 => P126 | D39 => P126 | D40 => P125 | D41 => P125 | D42 => P124 | D43 => P124 | D44 => P123 | D45 => P123 | D46 => P122 | D47 => P122 | D48 => P121 | D49 => P121 | D50 => P120 | D51 => P120 | D52 => P119 | D53 => P119 | D54 => P118 | D55 => P118 | D56 => P117 | D57 => P117 | D58 => P116 | D59 => P116 | D60 => P115 | D61 => P115 | D62 => P114 | D63 => P114 end
    | D18 => match d0 with D0 => P18 | D1 => P18 | D2 => P17 | D3 => P17 | D4 => P16 | D5 => P16 | D6 => P15 | D7 => P15 | D8 => P14 | D9 => P14 | D10 => P13 | D11 => P13 | D12 => P12 | D13 => P12 | D14 => P11 | D15 => P11 | D16 => P10 | D17 => P10 | D18 => P9 | D19 => P9 | D20 => P8 | D21 => P8 | D22 => P7 | D23 => P7 | D24 => P6 | D25 => P6 | D26 => P5 | D27 => P5 | D28 => P4 | D29 => P4 | D30 => P3 | D31 => P3 | D32 => P2 | D33 => P2 | D34 => P1 | D35 => P1 | D36 => P0 | D37 => P0 | D38 => P127 | D39 => P127 | D40 => P126 | D41 => P126 | D42 => P125 | D43 => P125 | D44 => P124 | D45 => P124 | D46 => P123 | D47 => P123 | D48 => P122 | D49 => P122 | D50 => P121 | D51 => P121 | D52 => P120 | D53 => P120 | D54 => P119 | D55 => P119 | D56 => P118 | D57 => P118 | D58 => P117 | D59 => P117 | D60 => P116 | D61 => P116 | D62 => P115 | D63 => P115 end
    | D19 => match d0 with D0 => P19 | D1 => P19 | D2 => P18 | D3 => P18 | D4 => P17 | D5 => P17 | D6 => P16 | D7 => P16 | D8 => P15 | D9 => P15 | D10 => P14 | D11 => P14 | D12 => P13 | D13 => P13 | D14 => P12 | D15 => P12 | D16 => P11 | D17 => P11 | D18 => P10 | D19 => P10 | D20 => P9 | D21 => P9 | D22 => P8 | D23 => P8 | D24 => P7 | D25 => P7 | D26 => P6 | D27 => P6 | D28 => P5 | D29 => P5 | D30 => P4 | D31 => P4 | D32 => P3 | D33 => P3 | D34 => P2 | D35 => P2 | D36 => P1 | D37 => P1 | D38 => P0 | D39 => P0 | D40 => P127 | D41 => P127 | D42 => P126 | D43 => P126 | D44 => P125 | D45 => P125 | D46 => P124 | D47 => P124 | D48 => P123 | D49 => P123 | D50 => P122 | D51 => P122 | D52 => P121 | D53 => P121 | D54 => P120 | D55 => P120 | D56 => P119 | D57 => P119 | D58 => P118 | D59 => P118 | D60 => P117 | D61 => P117 | D62 => P116 | D63 => P116 end
    | D20 => match d0 with D0 => P20 | D1 => P20 | D2 => P19 | D3 => P19 | D4 => P18 | D5 => P18 | D6 => P17 | D7 => P17 | D8 => P16 | D9 => P16 | D10 => P15 | D11 => P15 | D12 => P14 | D13 => P14 | D14 => P13 | D15 => P13 | D16 => P12 | D17 => P12 | D18 => P11 | D19 => P11 | D20 => P10 | D21 => P10 | D22 => P9 | D23 => P9 | D24 => P8 | D25 => P8 | D26 => P7 | D27 => P7 | D28 => P6 | D29 => P6 | D30 => P5 | D31 => P5 | D32 => P4 | D33 => P4 | D34 => P3 | D35 => P3 | D36 => P2 | D37 => P2 | D38 => P1 | D39 => P1 | D40 => P0 | D41 => P0 | D42 => P127 | D43 => P127 | D44 => P126 | D45 => P126 | D46 => P125 | D47 => P125 | D48 => P124 | D49 => P124 | D50 => P123 | D51 => P123 | D52 => P122 | D53 => P122 | D54 => P121 | D55 => P121 | D56 => P120 | D57 => P120 | D58 => P119 | D59 => P119 | D60 => P118 | D61 => P118 | D62 => P117 | D63 => P117 end
    | D21 => match d0 with D0 => P21 | D1 => P21 | D2 => P20 | D3 => P20 | D4 => P19 | D5 => P19 | D6 => P18 | D7 => P18 | D8 => P17 | D9 => P17 | D10 => P16 | D11 => P16 | D12 => P15 | D13 => P15 | D14 => P14 | D15 => P14 | D16 => P13 | D17 => P13 | D18 => P12 | D19 => P12 | D20 => P11 | D21 => P11 | D22 => P10 | D23 => P10 | D24 => P9 | D25 => P9 | D26 => P8 | D27 => P8 | D28 => P7 | D29 => P7 | D30 => P6 | D31 => P6 | D32 => P5 | D33 => P5 | D34 => P4 | D35 => P4 | D36 => P3 | D37 => P3 | D38 => P2 | D39 => P2 | D40 => P1 | D41 => P1 | D42 => P0 | D43 => P0 | D44 => P127 | D45 => P127 | D46 => P126 | D47 => P126 | D48 => P125 | D49 => P125 | D50 => P124 | D51 => P124 | D52 => P123 | D53 => P123 | D54 => P122 | D55 => P122 | D56 => P121 | D57 => P121 | D58 => P120 | D59 => P120 | D60 => P119 | D61 => P119 | D62 => P118 | D63 => P118 end
    | D22 => match d0 with D0 => P22 | D1 => P22 | D2 => P21 | D3 => P21 | D4 => P20 | D5 => P20 | D6 => P19 | D7 => P19 | D8 => P18 | D9 => P18 | D10 => P17 | D11 => P17 | D12 => P16 | D13 => P16 | D14 => P15 | D15 => P15 | D16 => P14 | D17 => P14 | D18 => P13 | D19 => P13 | D20 => P12 | D21 => P12 | D22 => P11 | D23 => P11 | D24 => P10 | D25 => P10 | D26 => P9 | D27 => P9 | D28 => P8 | D29 => P8 | D30 => P7 | D31 => P7 | D32 => P6 | D33 => P6 | D34 => P5 | D35 => P5 | D36 => P4 | D37 => P4 | D38 => P3 | D39 => P3 | D40 => P2 | D41 => P2 | D42 => P1 | D43 => P1 | D44 => P0 | D45 => P0 | D46 => P127 | D47 => P127 | D48 => P126 | D49 => P126 | D50 => P125 | D51 => P125 | D52 => P124 | D53 => P124 | D54 => P123 | D55 => P123 | D56 => P122 | D57 => P122 | D58 => P121 | D59 => P121 | D60 => P120 | D61 => P120 | D62 => P119 | D63 => P119 end
    | D23 => match d0 with D0 => P23 | D1 => P23 | D2 => P22 | D3 => P22 | D4 => P21 | D5 => P21 | D6 => P20 | D7 => P20 | D8 => P19 | D9 => P19 | D10 => P18 | D11 => P18 | D12 => P17 | D13 => P17 | D14 => P16 | D15 => P16 | D16 => P15 | D17 => P15 | D18 => P14 | D19 => P14 | D20 => P13 | D21 => P13 | D22 => P12 | D23 => P12 | D24 => P11 | D25 => P11 | D26 => P10 | D27 => P10 | D28 => P9 | D29 => P9 | D30 => P8 | D31 => P8 | D32 => P7 | D33 => P7 | D34 => P6 | D35 => P6 | D36 => P5 | D37 => P5 | D38 => P4 | D39 => P4 | D40 => P3 | D41 => P3 | D42 => P2 | D43 => P2 | D44 => P1 | D45 => P1 | D46 => P0 | D47 => P0 | D48 => P127 | D49 => P127 | D50 => P126 | D51 => P126 | D52 => P125 | D53 => P125 | D54 => P124 | D55 => P124 | D56 => P123 | D57 => P123 | D58 => P122 | D59 => P122 | D60 => P121 | D61 => P121 | D62 => P120 | D63 => P120 end
    | D24 => match d0 with D0 => P24 | D1 => P24 | D2 => P23 | D3 => P23 | D4 => P22 | D5 => P22 | D6 => P21 | D7 => P21 | D8 => P20 | D9 => P20 | D10 => P19 | D11 => P19 | D12 => P18 | D13 => P18 | D14 => P17 | D15 => P17 | D16 => P16 | D17 => P16 | D18 => P15 | D19 => P15 | D20 => P14 | D21 => P14 | D22 => P13 | D23 => P13 | D24 => P12 | D25 => P12 | D26 => P11 | D27 => P11 | D28 => P10 | D29 => P10 | D30 => P9 | D31 => P9 | D32 => P8 | D33 => P8 | D34 => P7 | D35 => P7 | D36 => P6 | D37 => P6 | D38 => P5 | D39 => P5 | D40 => P4 | D41 => P4 | D42 => P3 | D43 => P3 | D44 => P2 | D45 => P2 | D46 => P1 | D47 => P1 | D48 => P0 | D49 => P0 | D50 => P127 | D51 => P127 | D52 => P126 | D53 => P126 | D54 => P125 | D55 => P125 | D56 => P124 | D57 => P124 | D58 => P123 | D59 => P123 | D60 => P122 | D61 => P122 | D62 => P121 | D63 => P121 end
    | D25 => match d0 with D0 => P25 | D1 => P25 | D2 => P24 | D3 => P24 | D4 => P23 | D5 => P23 | D6 => P22 | D7 => P22 | D8 => P21 | D9 => P21 | D10 => P20 | D11 => P20 | D12 => P19 | D13 => P19 | D14 => P18 | D15 => P18 | D16 => P17 | D17 => P17 | D18 => P16 | D19 => P16 | D20 => P15 | D21 => P15 | D22 => P14 | D23 => P14 | D24 => P13 | D25 => P13 | D26 => P12 | D27 => P12 | D28 => P11 | D29 => P11 | D30 => P10 | D31 => P10 | D32 => P9 | D33 => P9 | D34 => P8 | D35 => P8 | D36 => P7 | D37 => P7 | D38 => P6 | D39 => P6 | D40 => P5 | D41 => P5 | D42 => P4 | D43 => P4 | D44 => P3 | D45 => P3 | D46 => P2 | D47 => P2 | D48 => P1 | D49 => P1 | D50 => P0 | D51 => P0 | D52 => P127 | D53 => P127 | D54 => P126 | D55 => P126 | D56 => P125 | D57 => P125 | D58 => P124 | D59 => P124 | D60 => P123 | D61 => P123 | D62 => P122 | D63 => P122 end
    | D26 => match d0 with D0 => P26 | D1 => P26 | D2 => P25 | D3 => P25 | D4 => P24 | D5 => P24 | D6 => P23 | D7 => P23 | D8 => P22 | D9 => P22 | D10 => P21 | D11 => P21 | D12 => P20 | D13 => P20 | D14 => P19 | D15 => P19 | D16 => P18 | D17 => P18 | D18 => P17 | D19 => P17 | D20 => P16 | D21 => P16 | D22 => P15 | D23 => P15 | D24 => P14 | D25 => P14 | D26 => P13 | D27 => P13 | D28 => P12 | D29 => P12 | D30 => P11 | D31 => P11 | D32 => P10 | D33 => P10 | D34 => P9 | D35 => P9 | D36 => P8 | D37 => P8 | D38 => P7 | D39 => P7 | D40 => P6 | D41 => P6 | D42 => P5 | D43 => P5 | D44 => P4 | D45 => P4 | D46 => P3 | D47 => P3 | D48 => P2 | D49 => P2 | D50 => P1 | D51 => P1 | D52 => P0 | D53 => P0 | D54 => P127 | D55 => P127 | D56 => P126 | D57 => P126 | D58 => P125 | D59 => P125 | D60 => P124 | D61 => P124 | D62 => P123 | D63 => P123 end
    | D27 => match d0 with D0 => P27 | D1 => P27 | D2 => P26 | D3 => P26 | D4 => P25 | D5 => P25 | D6 => P24 | D7 => P24 | D8 => P23 | D9 => P23 | D10 => P22 | D11 => P22 | D12 => P21 | D13 => P21 | D14 => P20 | D15 => P20 | D16 => P19 | D17 => P19 | D18 => P18 | D19 => P18 | D20 => P17 | D21 => P17 | D22 => P16 | D23 => P16 | D24 => P15 | D25 => P15 | D26 => P14 | D27 => P14 | D28 => P13 | D29 => P13 | D30 => P12 | D31 => P12 | D32 => P11 | D33 => P11 | D34 => P10 | D35 => P10 | D36 => P9 | D37 => P9 | D38 => P8 | D39 => P8 | D40 => P7 | D41 => P7 | D42 => P6 | D43 => P6 | D44 => P5 | D45 => P5 | D46 => P4 | D47 => P4 | D48 => P3 | D49 => P3 | D50 => P2 | D51 => P2 | D52 => P1 | D53 => P1 | D54 => P0 | D55 => P0 | D56 => P127 | D57 => P127 | D58 => P126 | D59 => P126 | D60 => P125 | D61 => P125 | D62 => P124 | D63 => P124 end
    | D28 => match d0 with D0 => P28 | D1 => P28 | D2 => P27 | D3 => P27 | D4 => P26 | D5 => P26 | D6 => P25 | D7 => P25 | D8 => P24 | D9 => P24 | D10 => P23 | D11 => P23 | D12 => P22 | D13 => P22 | D14 => P21 | D15 => P21 | D16 => P20 | D17 => P20 | D18 => P19 | D19 => P19 | D20 => P18 | D21 => P18 | D22 => P17 | D23 => P17 | D24 => P16 | D25 => P16 | D26 => P15 | D27 => P15 | D28 => P14 | D29 => P14 | D30 => P13 | D31 => P13 | D32 => P12 | D33 => P12 | D34 => P11 | D35 => P11 | D36 => P10 | D37 => P10 | D38 => P9 | D39 => P9 | D40 => P8 | D41 => P8 | D42 => P7 | D43 => P7 | D44 => P6 | D45 => P6 | D46 => P5 | D47 => P5 | D48 => P4 | D49 => P4 | D50 => P3 | D51 => P3 | D52 => P2 | D53 => P2 | D54 => P1 | D55 => P1 | D56 => P0 | D57 => P0 | D58 => P127 | D59 => P127 | D60 => P126 | D61 => P126 | D62 => P125 | D63 => P125 end
    | D29 => match d0 with D0 => P29 | D1 => P29 | D2 => P28 | D3 => P28 | D4 => P27 | D5 => P27 | D6 => P26 | D7 => P26 | D8 => P25 | D9 => P25 | D10 => P24 | D11 => P24 | D12 => P23 | D13 => P23 | D14 => P22 | D15 => P22 | D16 => P21 | D17 => P21 | D18 => P20 | D19 => P20 | D20 => P19 | D21 => P19 | D22 => P18 | D23 => P18 | D24 => P17 | D25 => P17 | D26 => P16 | D27 => P16 | D28 => P15 | D29 => P15 | D30 => P14 | D31 => P14 | D32 => P13 | D33 => P13 | D34 => P12 | D35 => P12 | D36 => P11 | D37 => P11 | D38 => P10 | D39 => P10 | D40 => P9 | D41 => P9 | D42 => P8 | D43 => P8 | D44 => P7 | D45 => P7 | D46 => P6 | D47 => P6 | D48 => P5 | D49 => P5 | D50 => P4 | D51 => P4 | D52 => P3 | D53 => P3 | D54 => P2 | D55 => P2 | D56 => P1 | D57 => P1 | D58 => P0 | D59 => P0 | D60 => P127 | D61 => P127 | D62 => P126 | D63 => P126 end
    | D30 => match d0 with D0 => P30 | D1 => P30 | D2 => P29 | D3 => P29 | D4 => P28 | D5 => P28 | D6 => P27 | D7 => P27 | D8 => P26 | D9 => P26 | D10 => P25 | D11 => P25 | D12 => P24 | D13 => P24 | D14 => P23 | D15 => P23 | D16 => P22 | D17 => P22 | D18 => P21 | D19 => P21 | D20 => P20 | D21 => P20 | D22 => P19 | D23 => P19 | D24 => P18 | D25 => P18 | D26 => P17 | D27 => P17 | D28 => P16 | D29 => P16 | D30 => P15 | D31 => P15 | D32 => P14 | D33 => P14 | D34 => P13 | D35 => P13 | D36 => P12 | D37 => P12 | D38 => P11 | D39 => P11 | D40 => P10 | D41 => P10 | D42 => P9 | D43 => P9 | D44 => P8 | D45 => P8 | D46 => P7 | D47 => P7 | D48 => P6 | D49 => P6 | D50 => P5 | D51 => P5 | D52 => P4 | D53 => P4 | D54 => P3 | D55 => P3 | D56 => P2 | D57 => P2 | D58 => P1 | D59 => P1 | D60 => P0 | D61 => P0 | D62 => P127 | D63 => P127 end
    | D31 => match d0 with D0 => P31 | D1 => P31 | D2 => P30 | D3 => P30 | D4 => P29 | D5 => P29 | D6 => P28 | D7 => P28 | D8 => P27 | D9 => P27 | D10 => P26 | D11 => P26 | D12 => P25 | D13 => P25 | D14 => P24 | D15 => P24 | D16 => P23 | D17 => P23 | D18 => P22 | D19 => P22 | D20 => P21 | D21 => P21 | D22 => P20 | D23 => P20 | D24 => P19 | D25 => P19 | D26 => P18 | D27 => P18 | D28 => P17 | D29 => P17 | D30 => P16 | D31 => P16 | D32 => P15 | D33 => P15 | D34 => P14 | D35 => P14 | D36 => P13 | D37 => P13 | D38 => P12 | D39 => P12 | D40 => P11 | D41 => P11 | D42 => P10 | D43 => P10 | D44 => P9 | D45 => P9 | D46 => P8 | D47 => P8 | D48 => P7 | D49 => P7 | D50 => P6 | D51 => P6 | D52 => P5 | D53 => P5 | D54 => P4 | D55 => P4 | D56 => P3 | D57 => P3 | D58 => P2 | D59 => P2 | D60 => P1 | D61 => P1 | D62 => P0 | D63 => P0 end
    | D32 => match d0 with D0 => P32 | D1 => P32 | D2 => P31 | D3 => P31 | D4 => P30 | D5 => P30 | D6 => P29 | D7 => P29 | D8 => P28 | D9 => P28 | D10 => P27 | D11 => P27 | D12 => P26 | D13 => P26 | D14 => P25 | D15 => P25 | D16 => P24 | D17 => P24 | D18 => P23 | D19 => P23 | D20 => P22 | D21 => P22 | D22 => P21 | D23 => P21 | D24 => P20 | D25 => P20 | D26 => P19 | D27 => P19 | D28 => P18 | D29 => P18 | D30 => P17 | D31 => P17 | D32 => P16 | D33 => P16 | D34 => P15 | D35 => P15 | D36 => P14 | D37 => P14 | D38 => P13 | D39 => P13 | D40 => P12 | D41 => P12 | D42 => P11 | D43 => P11 | D44 => P10 | D45 => P10 | D46 => P9 | D47 => P9 | D48 => P8 | D49 => P8 | D50 => P7 | D51 => P7 | D52 => P6 | D53 => P6 | D54 => P5 | D55 => P5 | D56 => P4 | D57 => P4 | D58 => P3 | D59 => P3 | D60 => P2 | D61 => P2 | D62 => P1 | D63 => P1 end
    | D33 => match d0 with D0 => P33 | D1 => P33 | D2 => P32 | D3 => P32 | D4 => P31 | D5 => P31 | D6 => P30 | D7 => P30 | D8 => P29 | D9 => P29 | D10 => P28 | D11 => P28 | D12 => P27 | D13 => P27 | D14 => P26 | D15 => P26 | D16 => P25 | D17 => P25 | D18 => P24 | D19 => P24 | D20 => P23 | D21 => P23 | D22 => P22 | D23 => P22 | D24 => P21 | D25 => P21 | D26 => P20 | D27 => P20 | D28 => P19 | D29 => P19 | D30 => P18 | D31 => P18 | D32 => P17 | D33 => P17 | D34 => P16 | D35 => P16 | D36 => P15 | D37 => P15 | D38 => P14 | D39 => P14 | D40 => P13 | D41 => P13 | D42 => P12 | D43 => P12 | D44 => P11 | D45 => P11 | D46 => P10 | D47 => P10 | D48 => P9 | D49 => P9 | D50 => P8 | D51 => P8 | D52 => P7 | D53 => P7 | D54 => P6 | D55 => P6 | D56 => P5 | D57 => P5 | D58 => P4 | D59 => P4 | D60 => P3 | D61 => P3 | D62 => P2 | D63 => P2 end
    | D34 => match d0 with D0 => P34 | D1 => P34 | D2 => P33 | D3 => P33 | D4 => P32 | D5 => P32 | D6 => P31 | D7 => P31 | D8 => P30 | D9 => P30 | D10 => P29 | D11 => P29 | D12 => P28 | D13 => P28 | D14 => P27 | D15 => P27 | D16 => P26 | D17 => P26 | D18 => P25 | D19 => P25 | D20 => P24 | D21 => P24 | D22 => P23 | D23 => P23 | D24 => P22 | D25 => P22 | D26 => P21 | D27 => P21 | D28 => P20 | D29 => P20 | D30 => P19 | D31 => P19 | D32 => P18 | D33 => P18 | D34 => P17 | D35 => P17 | D36 => P16 | D37 => P16 | D38 => P15 | D39 => P15 | D40 => P14 | D41 => P14 | D42 => P13 | D43 => P13 | D44 => P12 | D45 => P12 | D46 => P11 | D47 => P11 | D48 => P10 | D49 => P10 | D50 => P9 | D51 => P9 | D52 => P8 | D53 => P8 | D54 => P7 | D55 => P7 | D56 => P6 | D57 => P6 | D58 => P5 | D59 => P5 | D60 => P4 | D61 => P4 | D62 => P3 | D63 => P3 end
    | D35 => match d0 with D0 => P35 | D1 => P35 | D2 => P34 | D3 => P34 | D4 => P33 | D5 => P33 | D6 => P32 | D7 => P32 | D8 => P31 | D9 => P31 | D10 => P30 | D11 => P30 | D12 => P29 | D13 => P29 | D14 => P28 | D15 => P28 | D16 => P27 | D17 => P27 | D18 => P26 | D19 => P26 | D20 => P25 | D21 => P25 | D22 => P24 | D23 => P24 | D24 => P23 | D25 => P23 | D26 => P22 | D27 => P22 | D28 => P21 | D29 => P21 | D30 => P20 | D31 => P20 | D32 => P19 | D33 => P19 | D34 => P18 | D35 => P18 | D36 => P17 | D37 => P17 | D38 => P16 | D39 => P16 | D40 => P15 | D41 => P15 | D42 => P14 | D43 => P14 | D44 => P13 | D45 => P13 | D46 => P12 | D47 => P12 | D48 => P11 | D49 => P11 | D50 => P10 | D51 => P10 | D52 => P9 | D53 => P9 | D54 => P8 | D55 => P8 | D56 => P7 | D57 => P7 | D58 => P6 | D59 => P6 | D60 => P5 | D61 => P5 | D62 => P4 | D63 => P4 end
    | D36 => match d0 with D0 => P36 | D1 => P36 | D2 => P35 | D3 => P35 | D4 => P34 | D5 => P34 | D6 => P33 | D7 => P33 | D8 => P32 | D9 => P32 | D10 => P31 | D11 => P31 | D12 => P30 | D13 => P30 | D14 => P29 | D15 => P29 | D16 => P28 | D17 => P28 | D18 => P27 | D19 => P27 | D20 => P26 | D21 => P26 | D22 => P25 | D23 => P25 | D24 => P24 | D25 => P24 | D26 => P23 | D27 => P23 | D28 => P22 | D29 => P22 | D30 => P21 | D31 => P21 | D32 => P20 | D33 => P20 | D34 => P19 | D35 => P19 | D36 => P18 | D37 => P18 | D38 => P17 | D39 => P17 | D40 => P16 | D41 => P16 | D42 => P15 | D43 => P15 | D44 => P14 | D45 => P14 | D46 => P13 | D47 => P13 | D48 => P12 | D49 => P12 | D50 => P11 | D51 => P11 | D52 => P10 | D53 => P10 | D54 => P9 | D55 => P9 | D56 => P8 | D57 => P8 | D58 => P7 | D59 => P7 | D60 => P6 | D61 => P6 | D62 => P5 | D63 => P5 end
    | D37 => match d0 with D0 => P37 | D1 => P37 | D2 => P36 | D3 => P36 | D4 => P35 | D5 => P35 | D6 => P34 | D7 => P34 | D8 => P33 | D9 => P33 | D10 => P32 | D11 => P32 | D12 => P31 | D13 => P31 | D14 => P30 | D15 => P30 | D16 => P29 | D17 => P29 | D18 => P28 | D19 => P28 | D20 => P27 | D21 => P27 | D22 => P26 | D23 => P26 | D24 => P25 | D25 => P25 | D26 => P24 | D27 => P24 | D28 => P23 | D29 => P23 | D30 => P22 | D31 => P22 | D32 => P21 | D33 => P21 | D34 => P20 | D35 => P20 | D36 => P19 | D37 => P19 | D38 => P18 | D39 => P18 | D40 => P17 | D41 => P17 | D42 => P16 | D43 => P16 | D44 => P15 | D45 => P15 | D46 => P14 | D47 => P14 | D48 => P13 | D49 => P13 | D50 => P12 | D51 => P12 | D52 => P11 | D53 => P11 | D54 => P10 | D55 => P10 | D56 => P9 | D57 => P9 | D58 => P8 | D59 => P8 | D60 => P7 | D61 => P7 | D62 => P6 | D63 => P6 end
    | D38 => match d0 with D0 => P38 | D1 => P38 | D2 => P37 | D3 => P37 | D4 => P36 | D5 => P36 | D6 => P35 | D7 => P35 | D8 => P34 | D9 => P34 | D10 => P33 | D11 => P33 | D12 => P32 | D13 => P32 | D14 => P31 | D15 => P31 | D16 => P30 | D17 => P30 | D18 => P29 | D19 => P29 | D20 => P28 | D21 => P28 | D22 => P27 | D23 => P27 | D24 => P26 | D25 => P26 | D26 => P25 | D27 => P25 | D28 => P24 | D29 => P24 | D30 => P23 | D31 => P23 | D32 => P22 | D33 => P22 | D34 => P21 | D35 => P21 | D36 => P20 | D37 => P20 | D38 => P19 | D39 => P19 | D40 => P18 | D41 => P18 | D42 => P17 | D43 => P17 | D44 => P16 | D45 => P16 | D46 => P15 | D47 => P15 | D48 => P14 | D49 => P14 | D50 => P13 | D51 => P13 | D52 => P12 | D53 => P12 | D54 => P11 | D55 => P11 | D56 => P10 | D57 => P10 | D58 => P9 | D59 => P9 | D60 => P8 | D61 => P8 | D62 => P7 | D63 => P7 end
    | D39 => match d0 with D0 => P39 | D1 => P39 | D2 => P38 | D3 => P38 | D4 => P37 | D5 => P37 | D6 => P36 | D7 => P36 | D8 => P35 | D9 => P35 | D10 => P34 | D11 => P34 | D12 => P33 | D13 => P33 | D14 => P32 | D15 => P32 | D16 => P31 | D17 => P31 | D18 => P30 | D19 => P30 | D20 => P29 | D21 => P29 | D22 => P28 | D23 => P28 | D24 => P27 | D25 => P27 | D26 => P26 | D27 => P26 | D28 => P25 | D29 => P25 | D30 => P24 | D31 => P24 | D32 => P23 | D33 => P23 | D34 => P22 | D35 => P22 | D36 => P21 | D37 => P21 | D38 => P20 | D39 => P20 | D40 => P19 | D41 => P19 | D42 => P18 | D43 => P18 | D44 => P17 | D45 => P17 | D46 => P16 | D47 => P16 | D48 => P15 | D49 => P15 | D50 => P14 | D51 => P14 | D52 => P13 | D53 => P13 | D54 => P12 | D55 => P12 | D56 => P11 | D57 => P11 | D58 => P10 | D59 => P10 | D60 => P9 | D61 => P9 | D62 => P8 | D63 => P8 end
    | D40 => match d0 with D0 => P40 | D1 => P40 | D2 => P39 | D3 => P39 | D4 => P38 | D5 => P38 | D6 => P37 | D7 => P37 | D8 => P36 | D9 => P36 | D10 => P35 | D11 => P35 | D12 => P34 | D13 => P34 | D14 => P33 | D15 => P33 | D16 => P32 | D17 => P32 | D18 => P31 | D19 => P31 | D20 => P30 | D21 => P30 | D22 => P29 | D23 => P29 | D24 => P28 | D25 => P28 | D26 => P27 | D27 => P27 | D28 => P26 | D29 => P26 | D30 => P25 | D31 => P25 | D32 => P24 | D33 => P24 | D34 => P23 | D35 => P23 | D36 => P22 | D37 => P22 | D38 => P21 | D39 => P21 | D40 => P20 | D41 => P20 | D42 => P19 | D43 => P19 | D44 => P18 | D45 => P18 | D46 => P17 | D47 => P17 | D48 => P16 | D49 => P16 | D50 => P15 | D51 => P15 | D52 => P14 | D53 => P14 | D54 => P13 | D55 => P13 | D56 => P12 | D57 => P12 | D58 => P11 | D59 => P11 | D60 => P10 | D61 => P10 | D62 => P9 | D63 => P9 end
    | D41 => match d0 with D0 => P41 | D1 => P41 | D2 => P40 | D3 => P40 | D4 => P39 | D5 => P39 | D6 => P38 | D7 => P38 | D8 => P37 | D9 => P37 | D10 => P36 | D11 => P36 | D12 => P35 | D13 => P35 | D14 => P34 | D15 => P34 | D16 => P33 | D17 => P33 | D18 => P32 | D19 => P32 | D20 => P31 | D21 => P31 | D22 => P30 | D23 => P30 | D24 => P29 | D25 => P29 | D26 => P28 | D27 => P28 | D28 => P27 | D29 => P27 | D30 => P26 | D31 => P26 | D32 => P25 | D33 => P25 | D34 => P24 | D35 => P24 | D36 => P23 | D37 => P23 | D38 => P22 | D39 => P22 | D40 => P21 | D41 => P21 | D42 => P20 | D43 => P20 | D44 => P19 | D45 => P19 | D46 => P18 | D47 => P18 | D48 => P17 | D49 => P17 | D50 => P16 | D51 => P16 | D52 => P15 | D53 => P15 | D54 => P14 | D55 => P14 | D56 => P13 | D57 => P13 | D58 => P12 | D59 => P12 | D60 => P11 | D61 => P11 | D62 => P10 | D63 => P10 end
    | D42 => match d0 with D0 => P42 | D1 => P42 | D2 => P41 | D3 => P41 | D4 => P40 | D5 => P40 | D6 => P39 | D7 => P39 | D8 => P38 | D9 => P38 | D10 => P37 | D11 => P37 | D12 => P36 | D13 => P36 | D14 => P35 | D15 => P35 | D16 => P34 | D17 => P34 | D18 => P33 | D19 => P33 | D20 => P32 | D21 => P32 | D22 => P31 | D23 => P31 | D24 => P30 | D25 => P30 | D26 => P29 | D27 => P29 | D28 => P28 | D29 => P28 | D30 => P27 | D31 => P27 | D32 => P26 | D33 => P26 | D34 => P25 | D35 => P25 | D36 => P24 | D37 => P24 | D38 => P23 | D39 => P23 | D40 => P22 | D41 => P22 | D42 => P21 | D43 => P21 | D44 => P20 | D45 => P20 | D46 => P19 | D47 => P19 | D48 => P18 | D49 => P18 | D50 => P17 | D51 => P17 | D52 => P16 | D53 => P16 | D54 => P15 | D55 => P15 | D56 => P14 | D57 => P14 | D58 => P13 | D59 => P13 | D60 => P12 | D61 => P12 | D62 => P11 | D63 => P11 end
    | D43 => match d0 with D0 => P43 | D1 => P43 | D2 => P42 | D3 => P42 | D4 => P41 | D5 => P41 | D6 => P40 | D7 => P40 | D8 => P39 | D9 => P39 | D10 => P38 | D11 => P38 | D12 => P37 | D13 => P37 | D14 => P36 | D15 => P36 | D16 => P35 | D17 => P35 | D18 => P34 | D19 => P34 | D20 => P33 | D21 => P33 | D22 => P32 | D23 => P32 | D24 => P31 | D25 => P31 | D26 => P30 | D27 => P30 | D28 => P29 | D29 => P29 | D30 => P28 | D31 => P28 | D32 => P27 | D33 => P27 | D34 => P26 | D35 => P26 | D36 => P25 | D37 => P25 | D38 => P24 | D39 => P24 | D40 => P23 | D41 => P23 | D42 => P22 | D43 => P22 | D44 => P21 | D45 => P21 | D46 => P20 | D47 => P20 | D48 => P19 | D49 => P19 | D50 => P18 | D51 => P18 | D52 => P17 | D53 => P17 | D54 => P16 | D55 => P16 | D56 => P15 | D57 => P15 | D58 => P14 | D59 => P14 | D60 => P13 | D61 => P13 | D62 => P12 | D63 => P12 end
    | D44 => match d0 with D0 => P44 | D1 => P44 | D2 => P43 | D3 => P43 | D4 => P42 | D5 => P42 | D6 => P41 | D7 => P41 | D8 => P40 | D9 => P40 | D10 => P39 | D11 => P39 | D12 => P38 | D13 => P38 | D14 => P37 | D15 => P37 | D16 => P36 | D17 => P36 | D18 => P35 | D19 => P35 | D20 => P34 | D21 => P34 | D22 => P33 | D23 => P33 | D24 => P32 | D25 => P32 | D26 => P31 | D27 => P31 | D28 => P30 | D29 => P30 | D30 => P29 | D31 => P29 | D32 => P28 | D33 => P28 | D34 => P27 | D35 => P27 | D36 => P26 | D37 => P26 | D38 => P25 | D39 => P25 | D40 => P24 | D41 => P24 | D42 => P23 | D43 => P23 | D44 => P22 | D45 => P22 | D46 => P21 | D47 => P21 | D48 => P20 | D49 => P20 | D50 => P19 | D51 => P19 | D52 => P18 | D53 => P18 | D54 => P17 | D55 => P17 | D56 => P16 | D57 => P16 | D58 => P15 | D59 => P15 | D60 => P14 | D61 => P14 | D62 => P13 | D63 => P13 end
    | D45 => match d0 with D0 => P45 | D1 => P45 | D2 => P44 | D3 => P44 | D4 => P43 | D5 => P43 | D6 => P42 | D7 => P42 | D8 => P41 | D9 => P41 | D10 => P40 | D11 => P40 | D12 => P39 | D13 => P39 | D14 => P38 | D15 => P38 | D16 => P37 | D17 => P37 | D18 => P36 | D19 => P36 | D20 => P35 | D21 => P35 | D22 => P34 | D23 => P34 | D24 => P33 | D25 => P33 | D26 => P32 | D27 => P32 | D28 => P31 | D29 => P31 | D30 => P30 | D31 => P30 | D32 => P29 | D33 => P29 | D34 => P28 | D35 => P28 | D36 => P27 | D37 => P27 | D38 => P26 | D39 => P26 | D40 => P25 | D41 => P25 | D42 => P24 | D43 => P24 | D44 => P23 | D45 => P23 | D46 => P22 | D47 => P22 | D48 => P21 | D49 => P21 | D50 => P20 | D51 => P20 | D52 => P19 | D53 => P19 | D54 => P18 | D55 => P18 | D56 => P17 | D57 => P17 | D58 => P16 | D59 => P16 | D60 => P15 | D61 => P15 | D62 => P14 | D63 => P14 end
    | D46 => match d0 with D0 => P46 | D1 => P46 | D2 => P45 | D3 => P45 | D4 => P44 | D5 => P44 | D6 => P43 | D7 => P43 | D8 => P42 | D9 => P42 | D10 => P41 | D11 => P41 | D12 => P40 | D13 => P40 | D14 => P39 | D15 => P39 | D16 => P38 | D17 => P38 | D18 => P37 | D19 => P37 | D20 => P36 | D21 => P36 | D22 => P35 | D23 => P35 | D24 => P34 | D25 => P34 | D26 => P33 | D27 => P33 | D28 => P32 | D29 => P32 | D30 => P31 | D31 => P31 | D32 => P30 | D33 => P30 | D34 => P29 | D35 => P29 | D36 => P28 | D37 => P28 | D38 => P27 | D39 => P27 | D40 => P26 | D41 => P26 | D42 => P25 | D43 => P25 | D44 => P24 | D45 => P24 | D46 => P23 | D47 => P23 | D48 => P22 | D49 => P22 | D50 => P21 | D51 => P21 | D52 => P20 | D53 => P20 | D54 => P19 | D55 => P19 | D56 => P18 | D57 => P18 | D58 => P17 | D59 => P17 | D60 => P16 | D61 => P16 | D62 => P15 | D63 => P15 end
    | D47 => match d0 with D0 => P47 | D1 => P47 | D2 => P46 | D3 => P46 | D4 => P45 | D5 => P45 | D6 => P44 | D7 => P44 | D8 => P43 | D9 => P43 | D10 => P42 | D11 => P42 | D12 => P41 | D13 => P41 | D14 => P40 | D15 => P40 | D16 => P39 | D17 => P39 | D18 => P38 | D19 => P38 | D20 => P37 | D21 => P37 | D22 => P36 | D23 => P36 | D24 => P35 | D25 => P35 | D26 => P34 | D27 => P34 | D28 => P33 | D29 => P33 | D30 => P32 | D31 => P32 | D32 => P31 | D33 => P31 | D34 => P30 | D35 => P30 | D36 => P29 | D37 => P29 | D38 => P28 | D39 => P28 | D40 => P27 | D41 => P27 | D42 => P26 | D43 => P26 | D44 => P25 | D45 => P25 | D46 => P24 | D47 => P24 | D48 => P23 | D49 => P23 | D50 => P22 | D51 => P22 | D52 => P21 | D53 => P21 | D54 => P20 | D55 => P20 | D56 => P19 | D57 => P19 | D58 => P18 | D59 => P18 | D60 => P17 | D61 => P17 | D62 => P16 | D63 => P16 end
    | D48 => match d0 with D0 => P48 | D1 => P48 | D2 => P47 | D3 => P47 | D4 => P46 | D5 => P46 | D6 => P45 | D7 => P45 | D8 => P44 | D9 => P44 | D10 => P43 | D11 => P43 | D12 => P42 | D13 => P42 | D14 => P41 | D15 => P41 | D16 => P40 | D17 => P40 | D18 => P39 | D19 => P39 | D20 => P38 | D21 => P38 | D22 => P37 | D23 => P37 | D24 => P36 | D25 => P36 | D26 => P35 | D27 => P35 | D28 => P34 | D29 => P34 | D30 => P33 | D31 => P33 | D32 => P32 | D33 => P32 | D34 => P31 | D35 => P31 | D36 => P30 | D37 => P30 | D38 => P29 | D39 => P29 | D40 => P28 | D41 => P28 | D42 => P27 | D43 => P27 | D44 => P26 | D45 => P26 | D46 => P25 | D47 => P25 | D48 => P24 | D49 => P24 | D50 => P23 | D51 => P23 | D52 => P22 | D53 => P22 | D54 => P21 | D55 => P21 | D56 => P20 | D57 => P20 | D58 => P19 | D59 => P19 | D60 => P18 | D61 => P18 | D62 => P17 | D63 => P17 end
    | D49 => match d0 with D0 => P49 | D1 => P49 | D2 => P48 | D3 => P48 | D4 => P47 | D5 => P47 | D6 => P46 | D7 => P46 | D8 => P45 | D9 => P45 | D10 => P44 | D11 => P44 | D12 => P43 | D13 => P43 | D14 => P42 | D15 => P42 | D16 => P41 | D17 => P41 | D18 => P40 | D19 => P40 | D20 => P39 | D21 => P39 | D22 => P38 | D23 => P38 | D24 => P37 | D25 => P37 | D26 => P36 | D27 => P36 | D28 => P35 | D29 => P35 | D30 => P34 | D31 => P34 | D32 => P33 | D33 => P33 | D34 => P32 | D35 => P32 | D36 => P31 | D37 => P31 | D38 => P30 | D39 => P30 | D40 => P29 | D41 => P29 | D42 => P28 | D43 => P28 | D44 => P27 | D45 => P27 | D46 => P26 | D47 => P26 | D48 => P25 | D49 => P25 | D50 => P24 | D51 => P24 | D52 => P23 | D53 => P23 | D54 => P22 | D55 => P22 | D56 => P21 | D57 => P21 | D58 => P20 | D59 => P20 | D60 => P19 | D61 => P19 | D62 => P18 | D63 => P18 end
    | D50 => match d0 with D0 => P50 | D1 => P50 | D2 => P49 | D3 => P49 | D4 => P48 | D5 => P48 | D6 => P47 | D7 => P47 | D8 => P46 | D9 => P46 | D10 => P45 | D11 => P45 | D12 => P44 | D13 => P44 | D14 => P43 | D15 => P43 | D16 => P42 | D17 => P42 | D18 => P41 | D19 => P41 | D20 => P40 | D21 => P40 | D22 => P39 | D23 => P39 | D24 => P38 | D25 => P38 | D26 => P37 | D27 => P37 | D28 => P36 | D29 => P36 | D30 => P35 | D31 => P35 | D32 => P34 | D33 => P34 | D34 => P33 | D35 => P33 | D36 => P32 | D37 => P32 | D38 => P31 | D39 => P31 | D40 => P30 | D41 => P30 | D42 => P29 | D43 => P29 | D44 => P28 | D45 => P28 | D46 => P27 | D47 => P27 | D48 => P26 | D49 => P26 | D50 => P25 | D51 => P25 | D52 => P24 | D53 => P24 | D54 => P23 | D55 => P23 | D56 => P22 | D57 => P22 | D58 => P21 | D59 => P21 | D60 => P20 | D61 => P20 | D62 => P19 | D63 => P19 end
    | D51 => match d0 with D0 => P51 | D1 => P51 | D2 => P50 | D3 => P50 | D4 => P49 | D5 => P49 | D6 => P48 | D7 => P48 | D8 => P47 | D9 => P47 | D10 => P46 | D11 => P46 | D12 => P45 | D13 => P45 | D14 => P44 | D15 => P44 | D16 => P43 | D17 => P43 | D18 => P42 | D19 => P42 | D20 => P41 | D21 => P41 | D22 => P40 | D23 => P40 | D24 => P39 | D25 => P39 | D26 => P38 | D27 => P38 | D28 => P37 | D29 => P37 | D30 => P36 | D31 => P36 | D32 => P35 | D33 => P35 | D34 => P34 | D35 => P34 | D36 => P33 | D37 => P33 | D38 => P32 | D39 => P32 | D40 => P31 | D41 => P31 | D42 => P30 | D43 => P30 | D44 => P29 | D45 => P29 | D46 => P28 | D47 => P28 | D48 => P27 | D49 => P27 | D50 => P26 | D51 => P26 | D52 => P25 | D53 => P25 | D54 => P24 | D55 => P24 | D56 => P23 | D57 => P23 | D58 => P22 | D59 => P22 | D60 => P21 | D61 => P21 | D62 => P20 | D63 => P20 end
    | D52 => match d0 with D0 => P52 | D1 => P52 | D2 => P51 | D3 => P51 | D4 => P50 | D5 => P50 | D6 => P49 | D7 => P49 | D8 => P48 | D9 => P48 | D10 => P47 | D11 => P47 | D12 => P46 | D13 => P46 | D14 => P45 | D15 => P45 | D16 => P44 | D17 => P44 | D18 => P43 | D19 => P43 | D20 => P42 | D21 => P42 | D22 => P41 | D23 => P41 | D24 => P40 | D25 => P40 | D26 => P39 | D27 => P39 | D28 => P38 | D29 => P38 | D30 => P37 | D31 => P37 | D32 => P36 | D33 => P36 | D34 => P35 | D35 => P35 | D36 => P34 | D37 => P34 | D38 => P33 | D39 => P33 | D40 => P32 | D41 => P32 | D42 => P31 | D43 => P31 | D44 => P30 | D45 => P30 | D46 => P29 | D47 => P29 | D48 => P28 | D49 => P28 | D50 => P27 | D51 => P27 | D52 => P26 | D53 => P26 | D54 => P25 | D55 => P25 | D56 => P24 | D57 => P24 | D58 => P23 | D59 => P23 | D60 => P22 | D61 => P22 | D62 => P21 | D63 => P21 end
    | D53 => match d0 with D0 => P53 | D1 => P53 | D2 => P52 | D3 => P52 | D4 => P51 | D5 => P51 | D6 => P50 | D7 => P50 | D8 => P49 | D9 => P49 | D10 => P48 | D11 => P48 | D12 => P47 | D13 => P47 | D14 => P46 | D15 => P46 | D16 => P45 | D17 => P45 | D18 => P44 | D19 => P44 | D20 => P43 | D21 => P43 | D22 => P42 | D23 => P42 | D24 => P41 | D25 => P41 | D26 => P40 | D27 => P40 | D28 => P39 | D29 => P39 | D30 => P38 | D31 => P38 | D32 => P37 | D33 => P37 | D34 => P36 | D35 => P36 | D36 => P35 | D37 => P35 | D38 => P34 | D39 => P34 | D40 => P33 | D41 => P33 | D42 => P32 | D43 => P32 | D44 => P31 | D45 => P31 | D46 => P30 | D47 => P30 | D48 => P29 | D49 => P29 | D50 => P28 | D51 => P28 | D52 => P27 | D53 => P27 | D54 => P26 | D55 => P26 | D56 => P25 | D57 => P25 | D58 => P24 | D59 => P24 | D60 => P23 | D61 => P23 | D62 => P22 | D63 => P22 end
    | D54 => match d0 with D0 => P54 | D1 => P54 | D2 => P53 | D3 => P53 | D4 => P52 | D5 => P52 | D6 => P51 | D7 => P51 | D8 => P50 | D9 => P50 | D10 => P49 | D11 => P49 | D12 => P48 | D13 => P48 | D14 => P47 | D15 => P47 | D16 => P46 | D17 => P46 | D18 => P45 | D19 => P45 | D20 => P44 | D21 => P44 | D22 => P43 | D23 => P43 | D24 => P42 | D25 => P42 | D26 => P41 | D27 => P41 | D28 => P40 | D29 => P40 | D30 => P39 | D31 => P39 | D32 => P38 | D33 => P38 | D34 => P37 | D35 => P37 | D36 => P36 | D37 => P36 | D38 => P35 | D39 => P35 | D40 => P34 | D41 => P34 | D42 => P33 | D43 => P33 | D44 => P32 | D45 => P32 | D46 => P31 | D47 => P31 | D48 => P30 | D49 => P30 | D50 => P29 | D51 => P29 | D52 => P28 | D53 => P28 | D54 => P27 | D55 => P27 | D56 => P26 | D57 => P26 | D58 => P25 | D59 => P25 | D60 => P24 | D61 => P24 | D62 => P23 | D63 => P23 end
    | D55 => match d0 with D0 => P55 | D1 => P55 | D2 => P54 | D3 => P54 | D4 => P53 | D5 => P53 | D6 => P52 | D7 => P52 | D8 => P51 | D9 => P51 | D10 => P50 | D11 => P50 | D12 => P49 | D13 => P49 | D14 => P48 | D15 => P48 | D16 => P47 | D17 => P47 | D18 => P46 | D19 => P46 | D20 => P45 | D21 => P45 | D22 => P44 | D23 => P44 | D24 => P43 | D25 => P43 | D26 => P42 | D27 => P42 | D28 => P41 | D29 => P41 | D30 => P40 | D31 => P40 | D32 => P39 | D33 => P39 | D34 => P38 | D35 => P38 | D36 => P37 | D37 => P37 | D38 => P36 | D39 => P36 | D40 => P35 | D41 => P35 | D42 => P34 | D43 => P34 | D44 => P33 | D45 => P33 | D46 => P32 | D47 => P32 | D48 => P31 | D49 => P31 | D50 => P30 | D51 => P30 | D52 => P29 | D53 => P29 | D54 => P28 | D55 => P28 | D56 => P27 | D57 => P27 | D58 => P26 | D59 => P26 | D60 => P25 | D61 => P25 | D62 => P24 | D63 => P24 end
    | D56 => match d0 with D0 => P56 | D1 => P56 | D2 => P55 | D3 => P55 | D4 => P54 | D5 => P54 | D6 => P53 | D7 => P53 | D8 => P52 | D9 => P52 | D10 => P51 | D11 => P51 | D12 => P50 | D13 => P50 | D14 => P49 | D15 => P49 | D16 => P48 | D17 => P48 | D18 => P47 | D19 => P47 | D20 => P46 | D21 => P46 | D22 => P45 | D23 => P45 | D24 => P44 | D25 => P44 | D26 => P43 | D27 => P43 | D28 => P42 | D29 => P42 | D30 => P41 | D31 => P41 | D32 => P40 | D33 => P40 | D34 => P39 | D35 => P39 | D36 => P38 | D37 => P38 | D38 => P37 | D39 => P37 | D40 => P36 | D41 => P36 | D42 => P35 | D43 => P35 | D44 => P34 | D45 => P34 | D46 => P33 | D47 => P33 | D48 => P32 | D49 => P32 | D50 => P31 | D51 => P31 | D52 => P30 | D53 => P30 | D54 => P29 | D55 => P29 | D56 => P28 | D57 => P28 | D58 => P27 | D59 => P27 | D60 => P26 | D61 => P26 | D62 => P25 | D63 => P25 end
    | D57 => match d0 with D0 => P57 | D1 => P57 | D2 => P56 | D3 => P56 | D4 => P55 | D5 => P55 | D6 => P54 | D7 => P54 | D8 => P53 | D9 => P53 | D10 => P52 | D11 => P52 | D12 => P51 | D13 => P51 | D14 => P50 | D15 => P50 | D16 => P49 | D17 => P49 | D18 => P48 | D19 => P48 | D20 => P47 | D21 => P47 | D22 => P46 | D23 => P46 | D24 => P45 | D25 => P45 | D26 => P44 | D27 => P44 | D28 => P43 | D29 => P43 | D30 => P42 | D31 => P42 | D32 => P41 | D33 => P41 | D34 => P40 | D35 => P40 | D36 => P39 | D37 => P39 | D38 => P38 | D39 => P38 | D40 => P37 | D41 => P37 | D42 => P36 | D43 => P36 | D44 => P35 | D45 => P35 | D46 => P34 | D47 => P34 | D48 => P33 | D49 => P33 | D50 => P32 | D51 => P32 | D52 => P31 | D53 => P31 | D54 => P30 | D55 => P30 | D56 => P29 | D57 => P29 | D58 => P28 | D59 => P28 | D60 => P27 | D61 => P27 | D62 => P26 | D63 => P26 end
    | D58 => match d0 with D0 => P58 | D1 => P58 | D2 => P57 | D3 => P57 | D4 => P56 | D5 => P56 | D6 => P55 | D7 => P55 | D8 => P54 | D9 => P54 | D10 => P53 | D11 => P53 | D12 => P52 | D13 => P52 | D14 => P51 | D15 => P51 | D16 => P50 | D17 => P50 | D18 => P49 | D19 => P49 | D20 => P48 | D21 => P48 | D22 => P47 | D23 => P47 | D24 => P46 | D25 => P46 | D26 => P45 | D27 => P45 | D28 => P44 | D29 => P44 | D30 => P43 | D31 => P43 | D32 => P42 | D33 => P42 | D34 => P41 | D35 => P41 | D36 => P40 | D37 => P40 | D38 => P39 | D39 => P39 | D40 => P38 | D41 => P38 | D42 => P37 | D43 => P37 | D44 => P36 | D45 => P36 | D46 => P35 | D47 => P35 | D48 => P34 | D49 => P34 | D50 => P33 | D51 => P33 | D52 => P32 | D53 => P32 | D54 => P31 | D55 => P31 | D56 => P30 | D57 => P30 | D58 => P29 | D59 => P29 | D60 => P28 | D61 => P28 | D62 => P27 | D63 => P27 end
    | D59 => match d0 with D0 => P59 | D1 => P59 | D2 => P58 | D3 => P58 | D4 => P57 | D5 => P57 | D6 => P56 | D7 => P56 | D8 => P55 | D9 => P55 | D10 => P54 | D11 => P54 | D12 => P53 | D13 => P53 | D14 => P52 | D15 => P52 | D16 => P51 | D17 => P51 | D18 => P50 | D19 => P50 | D20 => P49 | D21 => P49 | D22 => P48 | D23 => P48 | D24 => P47 | D25 => P47 | D26 => P46 | D27 => P46 | D28 => P45 | D29 => P45 | D30 => P44 | D31 => P44 | D32 => P43 | D33 => P43 | D34 => P42 | D35 => P42 | D36 => P41 | D37 => P41 | D38 => P40 | D39 => P40 | D40 => P39 | D41 => P39 | D42 => P38 | D43 => P38 | D44 => P37 | D45 => P37 | D46 => P36 | D47 => P36 | D48 => P35 | D49 => P35 | D50 => P34 | D51 => P34 | D52 => P33 | D53 => P33 | D54 => P32 | D55 => P32 | D56 => P31 | D57 => P31 | D58 => P30 | D59 => P30 | D60 => P29 | D61 => P29 | D62 => P28 | D63 => P28 end
    | D60 => match d0 with D0 => P60 | D1 => P60 | D2 => P59 | D3 => P59 | D4 => P58 | D5 => P58 | D6 => P57 | D7 => P57 | D8 => P56 | D9 => P56 | D10 => P55 | D11 => P55 | D12 => P54 | D13 => P54 | D14 => P53 | D15 => P53 | D16 => P52 | D17 => P52 | D18 => P51 | D19 => P51 | D20 => P50 | D21 => P50 | D22 => P49 | D23 => P49 | D24 => P48 | D25 => P48 | D26 => P47 | D27 => P47 | D28 => P46 | D29 => P46 | D30 => P45 | D31 => P45 | D32 => P44 | D33 => P44 | D34 => P43 | D35 => P43 | D36 => P42 | D37 => P42 | D38 => P41 | D39 => P41 | D40 => P40 | D41 => P40 | D42 => P39 | D43 => P39 | D44 => P38 | D45 => P38 | D46 => P37 | D47 => P37 | D48 => P36 | D49 => P36 | D50 => P35 | D51 => P35 | D52 => P34 | D53 => P34 | D54 => P33 | D55 => P33 | D56 => P32 | D57 => P32 | D58 => P31 | D59 => P31 | D60 => P30 | D61 => P30 | D62 => P29 | D63 => P29 end
    | D61 => match d0 with D0 => P61 | D1 => P61 | D2 => P60 | D3 => P60 | D4 => P59 | D5 => P59 | D6 => P58 | D7 => P58 | D8 => P57 | D9 => P57 | D10 => P56 | D11 => P56 | D12 => P55 | D13 => P55 | D14 => P54 | D15 => P54 | D16 => P53 | D17 => P53 | D18 => P52 | D19 => P52 | D20 => P51 | D21 => P51 | D22 => P50 | D23 => P50 | D24 => P49 | D25 => P49 | D26 => P48 | D27 => P48 | D28 => P47 | D29 => P47 | D30 => P46 | D31 => P46 | D32 => P45 | D33 => P45 | D34 => P44 | D35 => P44 | D36 => P43 | D37 => P43 | D38 => P42 | D39 => P42 | D40 => P41 | D41 => P41 | D42 => P40 | D43 => P40 | D44 => P39 | D45 => P39 | D46 => P38 | D47 => P38 | D48 => P37 | D49 => P37 | D50 => P36 | D51 => P36 | D52 => P35 | D53 => P35 | D54 => P34 | D55 => P34 | D56 => P33 | D57 => P33 | D58 => P32 | D59 => P32 | D60 => P31 | D61 => P31 | D62 => P30 | D63 => P30 end
    | D62 => match d0 with D0 => P62 | D1 => P62 | D2 => P61 | D3 => P61 | D4 => P60 | D5 => P60 | D6 => P59 | D7 => P59 | D8 => P58 | D9 => P58 | D10 => P57 | D11 => P57 | D12 => P56 | D13 => P56 | D14 => P55 | D15 => P55 | D16 => P54 | D17 => P54 | D18 => P53 | D19 => P53 | D20 => P52 | D21 => P52 | D22 => P51 | D23 => P51 | D24 => P50 | D25 => P50 | D26 => P49 | D27 => P49 | D28 => P48 | D29 => P48 | D30 => P47 | D31 => P47 | D32 => P46 | D33 => P46 | D34 => P45 | D35 => P45 | D36 => P44 | D37 => P44 | D38 => P43 | D39 => P43 | D40 => P42 | D41 => P42 | D42 => P41 | D43 => P41 | D44 => P40 | D45 => P40 | D46 => P39 | D47 => P39 | D48 => P38 | D49 => P38 | D50 => P37 | D51 => P37 | D52 => P36 | D53 => P36 | D54 => P35 | D55 => P35 | D56 => P34 | D57 => P34 | D58 => P33 | D59 => P33 | D60 => P32 | D61 => P32 | D62 => P31 | D63 => P31 end
    | D63 => match d0 with D0 => P63 | D1 => P63 | D2 => P62 | D3 => P62 | D4 => P61 | D5 => P61 | D6 => P60 | D7 => P60 | D8 => P59 | D9 => P59 | D10 => P58 | D11 => P58 | D12 => P57 | D13 => P57 | D14 => P56 | D15 => P56 | D16 => P55 | D17 => P55 | D18 => P54 | D19 => P54 | D20 => P53 | D21 => P53 | D22 => P52 | D23 => P52 | D24 => P51 | D25 => P51 | D26 => P50 | D27 => P50 | D28 => P49 | D29 => P49 | D30 => P48 | D31 => P48 | D32 => P47 | D33 => P47 | D34 => P46 | D35 => P46 | D36 => P45 | D37 => P45 | D38 => P44 | D39 => P44 | D40 => P43 | D41 => P43 | D42 => P42 | D43 => P42 | D44 => P41 | D45 => P41 | D46 => P40 | D47 => P40 | D48 => P39 | D49 => P39 | D50 => P38 | D51 => P38 | D52 => P37 | D53 => P37 | D54 => P36 | D55 => P36 | D56 => P35 | D57 => P35 | D58 => P34 | D59 => P34 | D60 => P33 | D61 => P33 | D62 => P32 | D63 => P32 end
    end.

Definition mul3_64 (c : C6) (a : D64) : R256 :=
  match c with
  | C0 => match a with D0 => W0 | D1 => W3 | D2 => W6 | D3 => W9 | D4 => W12 | D5 => W15 | D6 => W18 | D7 => W21 | D8 => W24 | D9 => W27 | D10 => W30 | D11 => W33 | D12 => W36 | D13 => W39 | D14 => W42 | D15 => W45 | D16 => W48 | D17 => W51 | D18 => W54 | D19 => W57 | D20 => W60 | D21 => W63 | D22 => W66 | D23 => W69 | D24 => W72 | D25 => W75 | D26 => W78 | D27 => W81 | D28 => W84 | D29 => W87 | D30 => W90 | D31 => W93 | D32 => W96 | D33 => W99 | D34 => W102 | D35 => W105 | D36 => W108 | D37 => W111 | D38 => W114 | D39 => W117 | D40 => W120 | D41 => W123 | D42 => W126 | D43 => W129 | D44 => W132 | D45 => W135 | D46 => W138 | D47 => W141 | D48 => W144 | D49 => W147 | D50 => W150 | D51 => W153 | D52 => W156 | D53 => W159 | D54 => W162 | D55 => W165 | D56 => W168 | D57 => W171 | D58 => W174 | D59 => W177 | D60 => W180 | D61 => W183 | D62 => W186 | D63 => W189 end
  | C1 => match a with D0 => W1 | D1 => W4 | D2 => W7 | D3 => W10 | D4 => W13 | D5 => W16 | D6 => W19 | D7 => W22 | D8 => W25 | D9 => W28 | D10 => W31 | D11 => W34 | D12 => W37 | D13 => W40 | D14 => W43 | D15 => W46 | D16 => W49 | D17 => W52 | D18 => W55 | D19 => W58 | D20 => W61 | D21 => W64 | D22 => W67 | D23 => W70 | D24 => W73 | D25 => W76 | D26 => W79 | D27 => W82 | D28 => W85 | D29 => W88 | D30 => W91 | D31 => W94 | D32 => W97 | D33 => W100 | D34 => W103 | D35 => W106 | D36 => W109 | D37 => W112 | D38 => W115 | D39 => W118 | D40 => W121 | D41 => W124 | D42 => W127 | D43 => W130 | D44 => W133 | D45 => W136 | D46 => W139 | D47 => W142 | D48 => W145 | D49 => W148 | D50 => W151 | D51 => W154 | D52 => W157 | D53 => W160 | D54 => W163 | D55 => W166 | D56 => W169 | D57 => W172 | D58 => W175 | D59 => W178 | D60 => W181 | D61 => W184 | D62 => W187 | D63 => W190 end
  | C2 => match a with D0 => W2 | D1 => W5 | D2 => W8 | D3 => W11 | D4 => W14 | D5 => W17 | D6 => W20 | D7 => W23 | D8 => W26 | D9 => W29 | D10 => W32 | D11 => W35 | D12 => W38 | D13 => W41 | D14 => W44 | D15 => W47 | D16 => W50 | D17 => W53 | D18 => W56 | D19 => W59 | D20 => W62 | D21 => W65 | D22 => W68 | D23 => W71 | D24 => W74 | D25 => W77 | D26 => W80 | D27 => W83 | D28 => W86 | D29 => W89 | D30 => W92 | D31 => W95 | D32 => W98 | D33 => W101 | D34 => W104 | D35 => W107 | D36 => W110 | D37 => W113 | D38 => W116 | D39 => W119 | D40 => W122 | D41 => W125 | D42 => W128 | D43 => W131 | D44 => W134 | D45 => W137 | D46 => W140 | D47 => W143 | D48 => W146 | D49 => W149 | D50 => W152 | D51 => W155 | D52 => W158 | D53 => W161 | D54 => W164 | D55 => W167 | D56 => W170 | D57 => W173 | D58 => W176 | D59 => W179 | D60 => W182 | D61 => W185 | D62 => W188 | D63 => W191 end
  | C3 => match a with D0 => W3 | D1 => W6 | D2 => W9 | D3 => W12 | D4 => W15 | D5 => W18 | D6 => W21 | D7 => W24 | D8 => W27 | D9 => W30 | D10 => W33 | D11 => W36 | D12 => W39 | D13 => W42 | D14 => W45 | D15 => W48 | D16 => W51 | D17 => W54 | D18 => W57 | D19 => W60 | D20 => W63 | D21 => W66 | D22 => W69 | D23 => W72 | D24 => W75 | D25 => W78 | D26 => W81 | D27 => W84 | D28 => W87 | D29 => W90 | D30 => W93 | D31 => W96 | D32 => W99 | D33 => W102 | D34 => W105 | D35 => W108 | D36 => W111 | D37 => W114 | D38 => W117 | D39 => W120 | D40 => W123 | D41 => W126 | D42 => W129 | D43 => W132 | D44 => W135 | D45 => W138 | D46 => W141 | D47 => W144 | D48 => W147 | D49 => W150 | D50 => W153 | D51 => W156 | D52 => W159 | D53 => W162 | D54 => W165 | D55 => W168 | D56 => W171 | D57 => W174 | D58 => W177 | D59 => W180 | D60 => W183 | D61 => W186 | D62 => W189 | D63 => W192 end
  | C4 => match a with D0 => W4 | D1 => W7 | D2 => W10 | D3 => W13 | D4 => W16 | D5 => W19 | D6 => W22 | D7 => W25 | D8 => W28 | D9 => W31 | D10 => W34 | D11 => W37 | D12 => W40 | D13 => W43 | D14 => W46 | D15 => W49 | D16 => W52 | D17 => W55 | D18 => W58 | D19 => W61 | D20 => W64 | D21 => W67 | D22 => W70 | D23 => W73 | D24 => W76 | D25 => W79 | D26 => W82 | D27 => W85 | D28 => W88 | D29 => W91 | D30 => W94 | D31 => W97 | D32 => W100 | D33 => W103 | D34 => W106 | D35 => W109 | D36 => W112 | D37 => W115 | D38 => W118 | D39 => W121 | D40 => W124 | D41 => W127 | D42 => W130 | D43 => W133 | D44 => W136 | D45 => W139 | D46 => W142 | D47 => W145 | D48 => W148 | D49 => W151 | D50 => W154 | D51 => W157 | D52 => W160 | D53 => W163 | D54 => W166 | D55 => W169 | D56 => W172 | D57 => W175 | D58 => W178 | D59 => W181 | D60 => W184 | D61 => W187 | D62 => W190 | D63 => W193 end
  | C5 => match a with D0 => W5 | D1 => W8 | D2 => W11 | D3 => W14 | D4 => W17 | D5 => W20 | D6 => W23 | D7 => W26 | D8 => W29 | D9 => W32 | D10 => W35 | D11 => W38 | D12 => W41 | D13 => W44 | D14 => W47 | D15 => W50 | D16 => W53 | D17 => W56 | D18 => W59 | D19 => W62 | D20 => W65 | D21 => W68 | D22 => W71 | D23 => W74 | D24 => W77 | D25 => W80 | D26 => W83 | D27 => W86 | D28 => W89 | D29 => W92 | D30 => W95 | D31 => W98 | D32 => W101 | D33 => W104 | D34 => W107 | D35 => W110 | D36 => W113 | D37 => W116 | D38 => W119 | D39 => W122 | D40 => W125 | D41 => W128 | D42 => W131 | D43 => W134 | D44 => W137 | D45 => W140 | D46 => W143 | D47 => W146 | D48 => W149 | D49 => W152 | D50 => W155 | D51 => W158 | D52 => W161 | D53 => W164 | D54 => W167 | D55 => W170 | D56 => W173 | D57 => W176 | D58 => W179 | D59 => W182 | D60 => W185 | D61 => W188 | D62 => W191 | D63 => W194 end
  end.

Definition mul3half_64 (q_hi : bool) (c : C6) (d0 : D64) : R256 :=
  if q_hi then match c with
  | C0 => match d0 with D0 => W96 | D1 => W96 | D2 => W99 | D3 => W99 | D4 => W102 | D5 => W102 | D6 => W105 | D7 => W105 | D8 => W108 | D9 => W108 | D10 => W111 | D11 => W111 | D12 => W114 | D13 => W114 | D14 => W117 | D15 => W117 | D16 => W120 | D17 => W120 | D18 => W123 | D19 => W123 | D20 => W126 | D21 => W126 | D22 => W129 | D23 => W129 | D24 => W132 | D25 => W132 | D26 => W135 | D27 => W135 | D28 => W138 | D29 => W138 | D30 => W141 | D31 => W141 | D32 => W144 | D33 => W144 | D34 => W147 | D35 => W147 | D36 => W150 | D37 => W150 | D38 => W153 | D39 => W153 | D40 => W156 | D41 => W156 | D42 => W159 | D43 => W159 | D44 => W162 | D45 => W162 | D46 => W165 | D47 => W165 | D48 => W168 | D49 => W168 | D50 => W171 | D51 => W171 | D52 => W174 | D53 => W174 | D54 => W177 | D55 => W177 | D56 => W180 | D57 => W180 | D58 => W183 | D59 => W183 | D60 => W186 | D61 => W186 | D62 => W189 | D63 => W189 end
  | C1 => match d0 with D0 => W97 | D1 => W97 | D2 => W100 | D3 => W100 | D4 => W103 | D5 => W103 | D6 => W106 | D7 => W106 | D8 => W109 | D9 => W109 | D10 => W112 | D11 => W112 | D12 => W115 | D13 => W115 | D14 => W118 | D15 => W118 | D16 => W121 | D17 => W121 | D18 => W124 | D19 => W124 | D20 => W127 | D21 => W127 | D22 => W130 | D23 => W130 | D24 => W133 | D25 => W133 | D26 => W136 | D27 => W136 | D28 => W139 | D29 => W139 | D30 => W142 | D31 => W142 | D32 => W145 | D33 => W145 | D34 => W148 | D35 => W148 | D36 => W151 | D37 => W151 | D38 => W154 | D39 => W154 | D40 => W157 | D41 => W157 | D42 => W160 | D43 => W160 | D44 => W163 | D45 => W163 | D46 => W166 | D47 => W166 | D48 => W169 | D49 => W169 | D50 => W172 | D51 => W172 | D52 => W175 | D53 => W175 | D54 => W178 | D55 => W178 | D56 => W181 | D57 => W181 | D58 => W184 | D59 => W184 | D60 => W187 | D61 => W187 | D62 => W190 | D63 => W190 end
  | C2 => match d0 with D0 => W98 | D1 => W98 | D2 => W101 | D3 => W101 | D4 => W104 | D5 => W104 | D6 => W107 | D7 => W107 | D8 => W110 | D9 => W110 | D10 => W113 | D11 => W113 | D12 => W116 | D13 => W116 | D14 => W119 | D15 => W119 | D16 => W122 | D17 => W122 | D18 => W125 | D19 => W125 | D20 => W128 | D21 => W128 | D22 => W131 | D23 => W131 | D24 => W134 | D25 => W134 | D26 => W137 | D27 => W137 | D28 => W140 | D29 => W140 | D30 => W143 | D31 => W143 | D32 => W146 | D33 => W146 | D34 => W149 | D35 => W149 | D36 => W152 | D37 => W152 | D38 => W155 | D39 => W155 | D40 => W158 | D41 => W158 | D42 => W161 | D43 => W161 | D44 => W164 | D45 => W164 | D46 => W167 | D47 => W167 | D48 => W170 | D49 => W170 | D50 => W173 | D51 => W173 | D52 => W176 | D53 => W176 | D54 => W179 | D55 => W179 | D56 => W182 | D57 => W182 | D58 => W185 | D59 => W185 | D60 => W188 | D61 => W188 | D62 => W191 | D63 => W191 end
  | C3 => match d0 with D0 => W99 | D1 => W99 | D2 => W102 | D3 => W102 | D4 => W105 | D5 => W105 | D6 => W108 | D7 => W108 | D8 => W111 | D9 => W111 | D10 => W114 | D11 => W114 | D12 => W117 | D13 => W117 | D14 => W120 | D15 => W120 | D16 => W123 | D17 => W123 | D18 => W126 | D19 => W126 | D20 => W129 | D21 => W129 | D22 => W132 | D23 => W132 | D24 => W135 | D25 => W135 | D26 => W138 | D27 => W138 | D28 => W141 | D29 => W141 | D30 => W144 | D31 => W144 | D32 => W147 | D33 => W147 | D34 => W150 | D35 => W150 | D36 => W153 | D37 => W153 | D38 => W156 | D39 => W156 | D40 => W159 | D41 => W159 | D42 => W162 | D43 => W162 | D44 => W165 | D45 => W165 | D46 => W168 | D47 => W168 | D48 => W171 | D49 => W171 | D50 => W174 | D51 => W174 | D52 => W177 | D53 => W177 | D54 => W180 | D55 => W180 | D56 => W183 | D57 => W183 | D58 => W186 | D59 => W186 | D60 => W189 | D61 => W189 | D62 => W192 | D63 => W192 end
  | C4 => match d0 with D0 => W100 | D1 => W100 | D2 => W103 | D3 => W103 | D4 => W106 | D5 => W106 | D6 => W109 | D7 => W109 | D8 => W112 | D9 => W112 | D10 => W115 | D11 => W115 | D12 => W118 | D13 => W118 | D14 => W121 | D15 => W121 | D16 => W124 | D17 => W124 | D18 => W127 | D19 => W127 | D20 => W130 | D21 => W130 | D22 => W133 | D23 => W133 | D24 => W136 | D25 => W136 | D26 => W139 | D27 => W139 | D28 => W142 | D29 => W142 | D30 => W145 | D31 => W145 | D32 => W148 | D33 => W148 | D34 => W151 | D35 => W151 | D36 => W154 | D37 => W154 | D38 => W157 | D39 => W157 | D40 => W160 | D41 => W160 | D42 => W163 | D43 => W163 | D44 => W166 | D45 => W166 | D46 => W169 | D47 => W169 | D48 => W172 | D49 => W172 | D50 => W175 | D51 => W175 | D52 => W178 | D53 => W178 | D54 => W181 | D55 => W181 | D56 => W184 | D57 => W184 | D58 => W187 | D59 => W187 | D60 => W190 | D61 => W190 | D62 => W193 | D63 => W193 end
  | C5 => match d0 with D0 => W101 | D1 => W101 | D2 => W104 | D3 => W104 | D4 => W107 | D5 => W107 | D6 => W110 | D7 => W110 | D8 => W113 | D9 => W113 | D10 => W116 | D11 => W116 | D12 => W119 | D13 => W119 | D14 => W122 | D15 => W122 | D16 => W125 | D17 => W125 | D18 => W128 | D19 => W128 | D20 => W131 | D21 => W131 | D22 => W134 | D23 => W134 | D24 => W137 | D25 => W137 | D26 => W140 | D27 => W140 | D28 => W143 | D29 => W143 | D30 => W146 | D31 => W146 | D32 => W149 | D33 => W149 | D34 => W152 | D35 => W152 | D36 => W155 | D37 => W155 | D38 => W158 | D39 => W158 | D40 => W161 | D41 => W161 | D42 => W164 | D43 => W164 | D44 => W167 | D45 => W167 | D46 => W170 | D47 => W170 | D48 => W173 | D49 => W173 | D50 => W176 | D51 => W176 | D52 => W179 | D53 => W179 | D54 => W182 | D55 => W182 | D56 => W185 | D57 => W185 | D58 => W188 | D59 => W188 | D60 => W191 | D61 => W191 | D62 => W194 | D63 => W194 end
  end else match c with
  | C0 => match d0 with D0 => W0 | D1 => W0 | D2 => W3 | D3 => W3 | D4 => W6 | D5 => W6 | D6 => W9 | D7 => W9 | D8 => W12 | D9 => W12 | D10 => W15 | D11 => W15 | D12 => W18 | D13 => W18 | D14 => W21 | D15 => W21 | D16 => W24 | D17 => W24 | D18 => W27 | D19 => W27 | D20 => W30 | D21 => W30 | D22 => W33 | D23 => W33 | D24 => W36 | D25 => W36 | D26 => W39 | D27 => W39 | D28 => W42 | D29 => W42 | D30 => W45 | D31 => W45 | D32 => W48 | D33 => W48 | D34 => W51 | D35 => W51 | D36 => W54 | D37 => W54 | D38 => W57 | D39 => W57 | D40 => W60 | D41 => W60 | D42 => W63 | D43 => W63 | D44 => W66 | D45 => W66 | D46 => W69 | D47 => W69 | D48 => W72 | D49 => W72 | D50 => W75 | D51 => W75 | D52 => W78 | D53 => W78 | D54 => W81 | D55 => W81 | D56 => W84 | D57 => W84 | D58 => W87 | D59 => W87 | D60 => W90 | D61 => W90 | D62 => W93 | D63 => W93 end
  | C1 => match d0 with D0 => W1 | D1 => W1 | D2 => W4 | D3 => W4 | D4 => W7 | D5 => W7 | D6 => W10 | D7 => W10 | D8 => W13 | D9 => W13 | D10 => W16 | D11 => W16 | D12 => W19 | D13 => W19 | D14 => W22 | D15 => W22 | D16 => W25 | D17 => W25 | D18 => W28 | D19 => W28 | D20 => W31 | D21 => W31 | D22 => W34 | D23 => W34 | D24 => W37 | D25 => W37 | D26 => W40 | D27 => W40 | D28 => W43 | D29 => W43 | D30 => W46 | D31 => W46 | D32 => W49 | D33 => W49 | D34 => W52 | D35 => W52 | D36 => W55 | D37 => W55 | D38 => W58 | D39 => W58 | D40 => W61 | D41 => W61 | D42 => W64 | D43 => W64 | D44 => W67 | D45 => W67 | D46 => W70 | D47 => W70 | D48 => W73 | D49 => W73 | D50 => W76 | D51 => W76 | D52 => W79 | D53 => W79 | D54 => W82 | D55 => W82 | D56 => W85 | D57 => W85 | D58 => W88 | D59 => W88 | D60 => W91 | D61 => W91 | D62 => W94 | D63 => W94 end
  | C2 => match d0 with D0 => W2 | D1 => W2 | D2 => W5 | D3 => W5 | D4 => W8 | D5 => W8 | D6 => W11 | D7 => W11 | D8 => W14 | D9 => W14 | D10 => W17 | D11 => W17 | D12 => W20 | D13 => W20 | D14 => W23 | D15 => W23 | D16 => W26 | D17 => W26 | D18 => W29 | D19 => W29 | D20 => W32 | D21 => W32 | D22 => W35 | D23 => W35 | D24 => W38 | D25 => W38 | D26 => W41 | D27 => W41 | D28 => W44 | D29 => W44 | D30 => W47 | D31 => W47 | D32 => W50 | D33 => W50 | D34 => W53 | D35 => W53 | D36 => W56 | D37 => W56 | D38 => W59 | D39 => W59 | D40 => W62 | D41 => W62 | D42 => W65 | D43 => W65 | D44 => W68 | D45 => W68 | D46 => W71 | D47 => W71 | D48 => W74 | D49 => W74 | D50 => W77 | D51 => W77 | D52 => W80 | D53 => W80 | D54 => W83 | D55 => W83 | D56 => W86 | D57 => W86 | D58 => W89 | D59 => W89 | D60 => W92 | D61 => W92 | D62 => W95 | D63 => W95 end
  | C3 => match d0 with D0 => W3 | D1 => W3 | D2 => W6 | D3 => W6 | D4 => W9 | D5 => W9 | D6 => W12 | D7 => W12 | D8 => W15 | D9 => W15 | D10 => W18 | D11 => W18 | D12 => W21 | D13 => W21 | D14 => W24 | D15 => W24 | D16 => W27 | D17 => W27 | D18 => W30 | D19 => W30 | D20 => W33 | D21 => W33 | D22 => W36 | D23 => W36 | D24 => W39 | D25 => W39 | D26 => W42 | D27 => W42 | D28 => W45 | D29 => W45 | D30 => W48 | D31 => W48 | D32 => W51 | D33 => W51 | D34 => W54 | D35 => W54 | D36 => W57 | D37 => W57 | D38 => W60 | D39 => W60 | D40 => W63 | D41 => W63 | D42 => W66 | D43 => W66 | D44 => W69 | D45 => W69 | D46 => W72 | D47 => W72 | D48 => W75 | D49 => W75 | D50 => W78 | D51 => W78 | D52 => W81 | D53 => W81 | D54 => W84 | D55 => W84 | D56 => W87 | D57 => W87 | D58 => W90 | D59 => W90 | D60 => W93 | D61 => W93 | D62 => W96 | D63 => W96 end
  | C4 => match d0 with D0 => W4 | D1 => W4 | D2 => W7 | D3 => W7 | D4 => W10 | D5 => W10 | D6 => W13 | D7 => W13 | D8 => W16 | D9 => W16 | D10 => W19 | D11 => W19 | D12 => W22 | D13 => W22 | D14 => W25 | D15 => W25 | D16 => W28 | D17 => W28 | D18 => W31 | D19 => W31 | D20 => W34 | D21 => W34 | D22 => W37 | D23 => W37 | D24 => W40 | D25 => W40 | D26 => W43 | D27 => W43 | D28 => W46 | D29 => W46 | D30 => W49 | D31 => W49 | D32 => W52 | D33 => W52 | D34 => W55 | D35 => W55 | D36 => W58 | D37 => W58 | D38 => W61 | D39 => W61 | D40 => W64 | D41 => W64 | D42 => W67 | D43 => W67 | D44 => W70 | D45 => W70 | D46 => W73 | D47 => W73 | D48 => W76 | D49 => W76 | D50 => W79 | D51 => W79 | D52 => W82 | D53 => W82 | D54 => W85 | D55 => W85 | D56 => W88 | D57 => W88 | D58 => W91 | D59 => W91 | D60 => W94 | D61 => W94 | D62 => W97 | D63 => W97 end
  | C5 => match d0 with D0 => W5 | D1 => W5 | D2 => W8 | D3 => W8 | D4 => W11 | D5 => W11 | D6 => W14 | D7 => W14 | D8 => W17 | D9 => W17 | D10 => W20 | D11 => W20 | D12 => W23 | D13 => W23 | D14 => W26 | D15 => W26 | D16 => W29 | D17 => W29 | D18 => W32 | D19 => W32 | D20 => W35 | D21 => W35 | D22 => W38 | D23 => W38 | D24 => W41 | D25 => W41 | D26 => W44 | D27 => W44 | D28 => W47 | D29 => W47 | D30 => W50 | D31 => W50 | D32 => W53 | D33 => W53 | D34 => W56 | D35 => W56 | D36 => W59 | D37 => W59 | D38 => W62 | D39 => W62 | D40 => W65 | D41 => W65 | D42 => W68 | D43 => W68 | D44 => W71 | D45 => W71 | D46 => W74 | D47 => W74 | D48 => W77 | D49 => W77 | D50 => W80 | D51 => W80 | D52 => W83 | D53 => W83 | D54 => W86 | D55 => W86 | D56 => W89 | D57 => W89 | D58 => W92 | D59 => W92 | D60 => W95 | D61 => W95 | D62 => W98 | D63 => W98 end
  end.

Definition div2_64 (q_hi : bool) (a : D64) : D64 :=
  if q_hi then match a with D0 => D32 | D1 => D32 | D2 => D33 | D3 => D33 | D4 => D34 | D5 => D34 | D6 => D35 | D7 => D35 | D8 => D36 | D9 => D36 | D10 => D37 | D11 => D37 | D12 => D38 | D13 => D38 | D14 => D39 | D15 => D39 | D16 => D40 | D17 => D40 | D18 => D41 | D19 => D41 | D20 => D42 | D21 => D42 | D22 => D43 | D23 => D43 | D24 => D44 | D25 => D44 | D26 => D45 | D27 => D45 | D28 => D46 | D29 => D46 | D30 => D47 | D31 => D47 | D32 => D48 | D33 => D48 | D34 => D49 | D35 => D49 | D36 => D50 | D37 => D50 | D38 => D51 | D39 => D51 | D40 => D52 | D41 => D52 | D42 => D53 | D43 => D53 | D44 => D54 | D45 => D54 | D46 => D55 | D47 => D55 | D48 => D56 | D49 => D56 | D50 => D57 | D51 => D57 | D52 => D58 | D53 => D58 | D54 => D59 | D55 => D59 | D56 => D60 | D57 => D60 | D58 => D61 | D59 => D61 | D60 => D62 | D61 => D62 | D62 => D63 | D63 => D63 end
  else match a with D0 => D0 | D1 => D0 | D2 => D1 | D3 => D1 | D4 => D2 | D5 => D2 | D6 => D3 | D7 => D3 | D8 => D4 | D9 => D4 | D10 => D5 | D11 => D5 | D12 => D6 | D13 => D6 | D14 => D7 | D15 => D7 | D16 => D8 | D17 => D8 | D18 => D9 | D19 => D9 | D20 => D10 | D21 => D10 | D22 => D11 | D23 => D11 | D24 => D12 | D25 => D12 | D26 => D13 | D27 => D13 | D28 => D14 | D29 => D14 | D30 => D15 | D31 => D15 | D32 => D16 | D33 => D16 | D34 => D17 | D35 => D17 | D36 => D18 | D37 => D18 | D38 => D19 | D39 => D19 | D40 => D20 | D41 => D20 | D42 => D21 | D43 => D21 | D44 => D22 | D45 => D22 | D46 => D23 | D47 => D23 | D48 => D24 | D49 => D24 | D50 => D25 | D51 => D25 | D52 => D26 | D53 => D26 | D54 => D27 | D55 => D27 | D56 => D28 | D57 => D28 | D58 => D29 | D59 => D29 | D60 => D30 | D61 => D30 | D62 => D31 | D63 => D31 end.

Fixpoint addcB (c : bool) (x y : Big) {struct x} : Big :=
  match x, y with
  | BCons a xt, BCons b yt =>
    let r := add64c c a b in
    mkBCons (lo128 r) (addcB (hi128 r) xt yt)
  | BCons _ _, _ => if c then incB x else x
  | _, BCons _ _ => if c then incB y else y
  | _, _ => if c then B1 else BNil
  end.
Definition addB (x y : Big) : Big := addcB false x y.

Fixpoint subTryB (br : bool) (x y : Big) {struct x} : Big :=
  match x, y with
  | BCons a xt, BCons b yt =>
    let r := sub64b br a b in
    combineTry (lo128 r) (subTryB (hi128 r) xt yt)
  | BCons a xt, _ =>
    if br then match a, xt with D0, BNil => BUnder | _, _ => dec1B x end else x
  | _, BCons _ _ => BUnder
  | _, _ => if br then BUnder else BNil
  end.

Definition subB (x y : Big) : Big := match subTryB false x y with BUnder => BNil | z => z end.
Definition lebB (x y : Big) : bool := match subTryB false y x with BUnder => false | _ => true end.

Fixpoint sub2xTryB (br : C6) (x y : Big) {struct x} : Big :=
  match x, y with
  | BCons a xt, BCons b yt =>
    match br with
    | C0 | C1 | C2 =>
      let r := sub2x64 br a b in
      combineTry (lo256 r) (sub2xTryB (hi256 r) xt yt)
    | _ => BUnder
    end
  | BCons a xt, _ =>
    match br with
    | C0 => x
    | C1 => match a, xt with D0, BNil => BUnder | _, _ => dec1B x end
    | C2 => match a, xt with D0, BNil => BUnder | D1, BNil => BUnder | _, _ => dec2B x end
    | _ => BUnder
    end
  | _, BCons _ _ => BUnder
  | _, _ => match br with C0 => BNil | _ => BUnder end
  end.

Fixpoint subHalfTryB (br : bool) (x b : Big) {struct x} : Big :=
  match x, b with
  | BCons a xt, BCons d0 bt =>
    let r := subHalf64 br (oddB bt) a d0 in
    combineTry (lo128 r) (subHalfTryB (hi128 r) xt bt)
  | BCons a xt, _ => if br then match a, xt with D0, BNil => BUnder | _, _ => dec1B x end else x
  | _, BCons d0 bt =>
    match bt with
    | BNil => match d0 with D0 | D1 => if br then BUnder else BNil | _ => BUnder end
    | _ => BUnder
    end
  | _, _ => if br then BUnder else BNil
  end.

Fixpoint mul3addcB (c : C6) (x : Big) : Big :=
  match x with
  | BCons a xt =>
    let r := mul3_64 c a in
    mkBCons (lo256 r) (mul3addcB (hi256 r) xt)
  | _ => match c with C0 => BNil | C1 => B1 | C2 => B2 | C3 => B3 | C4 => BCons D4 BNil | C5 => BCons D5 BNil end
  end.

Fixpoint mul3halfB (c : C6) (b : Big) : Big :=
  match b with
  | BCons d0 bt =>
    let r := mul3half_64 (oddB bt) c d0 in
    mkBCons (lo256 r) (mul3halfB (hi256 r) bt)
  | _ => match c with C0 => BNil | C1 => B1 | C2 => B2 | C3 => B3 | C4 => BCons D4 BNil | C5 => BCons D5 BNil end
  end.

Fixpoint div2B (x : Big) : Big :=
  match x with
  | BCons a xt => mkBCons (div2_64 (oddB xt) a) (div2B xt)
  | _ => BNil
  end.

Fixpoint eqbB (x y : Big) : bool :=
  match x, y with
  | BNil, BNil => true
  | BCons a xt, BCons b yt => match sub64b false a b with P0 => eqbB xt yt | _ => false end
  | _, _ => false
  end.

Inductive Tok : Type :=
  | TokZ (n : Big)
  | TokO (n : Big)
  | TokW (n : Big).

Inductive LStack : Type :=
  | LNil
  | LC (b : Big) (tl : LStack)
  | LTok (t : Tok) (tl : LStack).

Inductive RStack : Type :=
  | RNil
  | RC (is1 : bool) (c : Big) (tl : RStack)
  | RTok (t : Tok) (tl : RStack).

Inductive HybState : Type :=
  | HClean (sL : LStack) (sR : RStack)
  | HGen (q : Q_st) (h : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack).

Fixpoint runCleanLoop (steps : nat) (b0 : Big) (lt : LStack) (isC1 : bool) (c0 : Big) (rt : RStack) : HybState :=
  match steps with
  | O => HClean (LC b0 lt) (RC isC1 c0 rt)
  | S steps' =>
    let diff := sub2xTryB C0 b0 c0 in
    if isZeroB diff then
      match lt with
      | LC b1 lt2 =>
        let nb1 := subSmall3B b1 in
        if isZeroB nb1 then HGen QF true [TokW B3] (LC b0 lt) [] (RC isC1 c0 rt)
        else
          if evenB b0 then
            let nc0 := subHalfTryB false c0 b0 in
            if isZeroB nc0 then HGen QF true [TokW B3] (LC b0 lt) [] (RC isC1 c0 rt)
            else runCleanLoop steps' nb1 lt2 true (mul3halfB C3 b0) (RC isC1 nc0 rt)
          else
            let nc0 := subHalfTryB true c0 b0 in
            if isZeroB nc0 then HGen QF true [TokW B3] (LC b0 lt) [] (RC isC1 c0 rt)
            else runCleanLoop steps' nb1 lt2 false (mul3halfB C5 b0) (RC isC1 nc0 rt)
      | _ => HGen QF true [TokW B3] (LC b0 lt) [] (RC isC1 c0 rt)
      end
    else
      if isC1 then
        let nb0 := subSmall2B diff in
        if isZeroB nb0 then HGen QF true [TokW B3] (LC b0 lt) [] (RC true c0 rt)
        else
          match rt with
          | RC t1 c1 rt2 =>
            let nc1 := subSmall2B c1 in
            if isZeroB nc1 then HGen QF true [TokW B3] (LC b0 lt) [] (RC true c0 rt)
            else runCleanLoop steps' (mul3addcB C4 c0) (LC nb0 lt) t1 nc1 rt2
          | _ => HGen QF true [TokW B3] (LC b0 lt) [] (RC true c0 rt)
          end
      else
        if isZeroB c0 then HGen QF true [TokW B3] (LC b0 lt) [] (RC false c0 rt)
        else
          match rt with
          | RC t1 c1 rt2 =>
            let nc1 := subSmall1B c1 in
            if isZeroB nc1 then HGen QF true [TokW B3] (LC b0 lt) [] (RC false c0 rt)
            else runCleanLoop steps' (mul3addcB C1 c0) (LC diff lt) t1 nc1 rt2
          | _ => HGen QF true [TokW B3] (LC b0 lt) [] (RC false c0 rt)
          end
  end.

Definition runCleanChunk (kc4 : nat) (sL : LStack) (sR : RStack) : HybState :=
  match sL, sR with
  | LC b0 lt, RC isC1 c0 rt => runCleanLoop kc4 b0 lt isC1 c0 rt
  | _, _ => HGen QF true [TokW B3] sL [] sR
  end.

Definition sub2xB (x y : Big) : Big := match sub2xTryB C0 x y with BUnder => BNil | z => z end.

Definition pushTok (t : Tok) (ts : list Tok) : list Tok :=
  match t with
  | TokZ BNil => ts
  | TokO BNil => ts
  | TokW BNil => ts
  | TokZ a => match ts with TokZ b :: rest => TokZ (addB a b) :: rest | _ => t :: ts end
  | TokO a => match ts with TokO b :: rest => TokO (addB a b) :: rest | _ => t :: ts end
  | TokW a => match ts with TokW b :: rest => TokW (addB a b) :: rest | _ => t :: ts end
  end.

Fixpoint pushTokBack (ts : list Tok) (t : Tok) : list Tok :=
  match ts with
  | [] => pushTok t []
  | [t0] => pushTok t0 (pushTok t [])
  | t0 :: rest => t0 :: pushTokBack rest t
  end.

Fixpoint stripEndZ (ts : list Tok) : list Tok :=
  match ts with
  | [] => []
  | t :: rest =>
    match stripEndZ rest with
    | [] => match t with TokZ _ => [] | _ => [t] end
    | rest' => t :: rest'
    end
  end.

Definition needPull (ts : list Tok) : bool :=
  match ts with
  | _ :: _ :: _ :: _ :: _ => false
  | _ => true
  end.

Definition pullOneL (bL : list Tok) (rL : LStack) : list Tok * LStack :=
  match rL with
  | LNil => (stripEndZ bL, LNil)
  | LC b tl => (pushTokBack (pushTokBack bL (TokZ B1)) (TokW b), tl)
  | LTok t tl => (pushTokBack bL t, tl)
  end.

Definition pullOneR (bR : list Tok) (rR : RStack) : list Tok * RStack :=
  match rR with
  | RNil => (stripEndZ bR, RNil)
  | RC false c tl => (pushTokBack (pushTokBack bR (TokW c)) (TokZ B1), tl)
  | RC true c tl => (pushTokBack (pushTokBack bR (TokW c)) (TokO B1), tl)
  | RTok t tl => (pushTokBack bR t, tl)
  end.

Definition pullStepL (p : list Tok * LStack) : list Tok * LStack :=
  if needPull (fst p) then pullOneL (fst p) (snd p) else p.

Definition pullStepR (p : list Tok * RStack) : list Tok * RStack :=
  if needPull (fst p) then pullOneR (fst p) (snd p) else p.

Definition ensureL (bL : list Tok) (rL : LStack) : list Tok * LStack :=
  pullStepL (pullStepL (pullStepL (pullStepL (bL, rL)))).

Definition ensureR (bR : list Tok) (rR : RStack) : list Tok * RStack :=
  pullStepR (pullStepR (pullStepR (pullStepR (bR, rR)))).

Fixpoint foldPackL (revTs : list Tok) (rL : LStack) : LStack :=
  match revTs with
  | [] => rL
  | t :: revRest =>
    match t with
    | TokW b =>
      if negb (isZeroB b) then
        match revRest with
        | TokZ z :: revRest2 =>
          if isOneB z then foldPackL revRest2 (LC b rL)
          else foldPackL revRest (LTok t rL)
        | _ => foldPackL revRest (LTok t rL)
        end
      else foldPackL revRest (LTok t rL)
    | TokZ z =>
      if isOneB z then
        match rL with
        | LTok (TokW b) tl =>
          if negb (isZeroB b) then foldPackL revRest (LC b tl)
          else foldPackL revRest (LTok t rL)
        | _ => foldPackL revRest (LTok t rL)
        end
      else foldPackL revRest (LTok t rL)
    | _ => foldPackL revRest (LTok t rL)
    end
  end.

Fixpoint foldPackR (revTs : list Tok) (rR : RStack) : RStack :=
  match revTs with
  | [] => rR
  | t :: revRest =>
    match t with
    | TokZ z =>
      if isOneB z then
        match revRest with
        | TokW c :: revRest2 =>
          if negb (isZeroB c) then foldPackR revRest2 (RC false c rR)
          else foldPackR revRest (RC false B0 rR)
        | _ => foldPackR revRest (RC false B0 rR)
        end
      else foldPackR revRest (RTok t rR)
    | TokO o =>
      if isOneB o then
        match revRest with
        | TokW c :: revRest2 =>
          if negb (isZeroB c) then foldPackR revRest2 (RC true c rR)
          else foldPackR revRest (RC true B0 rR)
        | _ => foldPackR revRest (RC true B0 rR)
        end
      else foldPackR revRest (RTok t rR)
    | TokW c =>
      if negb (isZeroB c) then
        match rR with
        | RTok (TokZ z) tl =>
          if isOneB z then foldPackR revRest (RC false c tl)
          else foldPackR revRest (RTok t rR)
        | RTok (TokO o) tl =>
          if isOneB o then foldPackR revRest (RC true c tl)
          else foldPackR revRest (RTok t rR)
        | RC b c' tl => foldPackR revRest (RC b (addB c c') tl)
        | _ => foldPackR revRest (RTok t rR)
        end
      else
        match rR with
        | RC b c' tl => foldPackR revRest (RC b c' tl)
        | _ => foldPackR revRest (RTok t rR)
        end
    end
  end.

Definition pushRawOverflowL (bL : list Tok) (rL : LStack) : list Tok * LStack :=
  match bL with
  | t0 :: t1 :: t2 :: t3 :: t4 :: t5 :: rest =>
    ([t0; t1; t2; t3], foldPackL (List.rev (t4 :: t5 :: rest)) rL)
  | _ => (bL, rL)
  end.

Definition pushRawOverflowR (bR : list Tok) (rR : RStack) : list Tok * RStack :=
  match bR with
  | t0 :: t1 :: t2 :: t3 :: t4 :: t5 :: rest =>
    ([t0; t1; t2; t3], foldPackR (List.rev (t4 :: t5 :: rest)) rR)
  | _ => (bR, rR)
  end.

Definition canClean (sL : LStack) (sR : RStack) : bool :=
  match sL, sR with
  | LC b0 lt, RC isC1 c0 rt =>
    let diff := sub2xTryB C0 b0 c0 in
    if isZeroB diff then
      match lt with
      | LC b1 _ =>
        if isZeroB (subSmall3B b1) then false
        else negb (isZeroB (subHalfTryB (oddB b0) c0 b0))
      | _ => false
      end
    else
      if isC1 then
        if isZeroB (subSmall2B diff) then false
        else match rt with RC _ c1 _ => negb (isZeroB (subSmall2B c1)) | _ => false end
      else
        if isZeroB c0 then false
        else match rt with RC _ c1 _ => negb (isZeroB (subSmall1B c1)) | _ => false end
  | _, _ => false
  end.

Definition finishGen (q : Q_st) (h : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) : HybState :=
  match q, h, bL with
  | QF, true, TokW w0 :: restL =>
    if isThreeB w0 then
      let rL' := foldPackL (List.rev restL) rL in
      let rR' := foldPackR (List.rev bR) rR in
      if canClean rL' rR' then HClean rL' rR'
      else
        let oL := pushRawOverflowL bL rL in
        let oR := pushRawOverflowR bR rR in
        HGen QF true (fst oL) (snd oL) (fst oR) (snd oR)
    else
      let oL := pushRawOverflowL bL rL in
      let oR := pushRawOverflowR bR rR in
      HGen q h (fst oL) (snd oL) (fst oR) (snd oR)
  | _, _, _ =>
    let oL := pushRawOverflowL bL rL in
    let oR := pushRawOverflowR bR rR in
    HGen q h (fst oL) (snd oL) (fst oR) (snd oR)
  end.

Definition pushBit (b : bool) (ts : list Tok) (emptyTail : bool) : list Tok :=
  if b then
    match ts with
    | [TokO o0] =>
      if isOneB o0 then (if emptyTail then [TokW B1] else [TokO B2])
      else TokO (addSmall1B o0) :: []
    | TokO o0 :: TokZ z0 :: rest =>
      if isOneB o0 then
        if isOneB z0 then pushTok (TokW B1) rest
        else if lebB B2 z0 then TokW B1 :: TokZ (subSmall1B z0) :: rest
        else TokO B2 :: TokZ z0 :: rest
      else TokO (addSmall1B o0) :: TokZ z0 :: rest
    | TokO n :: rest => TokO (addSmall1B n) :: rest
    | _ => TokO B1 :: ts
    end
  else
    match ts with
    | [] => if emptyTail then [] else [TokZ B1]
    | TokZ n :: rest => TokZ (addSmall1B n) :: rest
    | _ => TokZ B1 :: ts
    end.

Fixpoint popBit (ts : list Tok) : option (bool * list Tok) :=
  match ts with
  | [] => None
  | TokZ n :: rest =>
    if isZeroB n then popBit rest
    else if isOneB n then Some (false, rest)
    else Some (false, TokZ (subSmall1B n) :: rest)
  | TokO n :: rest =>
    if isZeroB n then popBit rest
    else if isOneB n then Some (true, rest)
    else Some (true, TokO (subSmall1B n) :: rest)
  | TokW n :: rest =>
    if isZeroB n then popBit rest
    else if isOneB n then Some (true, TokO B1 :: pushTok (TokZ B1) rest)
    else Some (true, TokO B1 :: TokZ B1 :: TokW (subSmall1B n) :: rest)
  end.

Definition isEmptyL (rL : LStack) : bool := match rL with LNil => true | _ => false end.
Definition isEmptyR (rR : RStack) : bool := match rR with RNil => true | _ => false end.

Definition popBitL (bL : list Tok) (rL : LStack) : option (bool * list Tok * LStack) :=
  match popBit bL with
  | Some (b, bL') => Some (b, bL', rL)
  | None => match rL with LNil => Some (false, [], LNil) | _ => None end
  end.

Definition popBitR (bR : list Tok) (rR : RStack) : option (bool * list Tok * RStack) :=
  match popBit bR with
  | Some (b, bR') => Some (b, bR', rR)
  | None => match rR with RNil => Some (false, [], RNil) | _ => None end
  end.

Definition stepRaw (q : Q_st) (h : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) : HybState :=
  match q, h with
  | QA, false =>
    match popBitR bR rR with
    | Some (h', bR', rR') => finishGen QB h' (pushBit true bL (isEmptyL rL)) rL bR' rR'
    | None => HGen q h bL rL bR rR
    end
  | QA, true =>
    match popBitR bR rR with
    | Some (h', bR', rR') => finishGen QE h' (pushBit false bL (isEmptyL rL)) rL bR' rR'
    | None => HGen q h bL rL bR rR
    end
  | QB, false =>
    match popBitL bL rL with
    | Some (h', bL', rL') => finishGen QC h' bL' rL' (pushBit true bR (isEmptyR rR)) rR
    | None => HGen q h bL rL bR rR
    end
  | QB, true =>
    match popBitL bL rL with
    | Some (h', bL', rL') => finishGen QF h' bL' rL' (pushBit true bR (isEmptyR rR)) rR
    | None => HGen q h bL rL bR rR
    end
  | QC, false =>
    match popBitR bR rR with
    | Some (h', bR', rR') => finishGen QA h' (pushBit true bL (isEmptyL rL)) rL bR' rR'
    | None => HGen q h bL rL bR rR
    end
  | QC, true =>
    match popBitL bL rL with
    | Some (h', bL', rL') => finishGen QD h' bL' rL' (pushBit false bR (isEmptyR rR)) rR
    | None => HGen q h bL rL bR rR
    end
  | QD, false =>
    match popBitL bL rL with
    | Some (h', bL', rL') => finishGen QB h' bL' rL' (pushBit true bR (isEmptyR rR)) rR
    | None => HGen q h bL rL bR rR
    end
  | QD, true =>
    match popBitL bL rL with
    | Some (h', bL', rL') => finishGen QA h' bL' rL' (pushBit true bR (isEmptyR rR)) rR
    | None => HGen q h bL rL bR rR
    end
  | QE, false =>
    match popBitR bR rR with
    | Some (h', bR', rR') => finishGen QB h' (pushBit true bL (isEmptyL rL)) rL bR' rR'
    | None => HGen q h bL rL bR rR
    end
  | QE, true =>
    match popBitR bR rR with
    | Some (h', bR', rR') => finishGen QC h' (pushBit true bL (isEmptyL rL)) rL bR' rR'
    | None => HGen q h bL rL bR rR
    end
  | QF, false => HGen q h bL rL bR rR
  | QF, true =>
    match popBitL bL rL with
    | Some (h', bL', rL') => finishGen QA h' bL' rL' (pushBit false bR (isEmptyR rR)) rR
    | None => HGen q h bL rL bR rR
    end
  end.

Definition startsWith1 (ts : list Tok) : bool :=
  match ts with
  | TokO n :: _ => negb (isZeroB n)
  | TokW n :: _ => negb (isZeroB n)
  | _ => false
  end.

Definition subWHead (c d : Big) (rest : list Tok) : list Tok :=
  let rem := subB c d in
  if isZeroB rem then rest else TokW rem :: rest.

Definition stepGenF1PP (a : Big) (lTail : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack)
    (bL_orig : list Tok) : HybState :=
  match bR with
  | TokO o0 :: TokZ z :: rTail =>
    if andb (isOneB o0) (negb (isZeroB z)) then
      let z1 := subSmall1B z in
      let rRest := if isZeroB z1 then rTail else TokZ z1 :: rTail in
      let bR' := TokO B1 :: TokZ B1 :: pushTok (TokW a) rRest in
      finishGen QF true lTail rL bR' rR
    else stepRaw QF true bL_orig rL bR rR
  | [TokO o0] =>
    if isOneB o0 then
      match rR with
      | RNil => finishGen QF true lTail rL [TokO B1; TokZ B1; TokW a] RNil
      | _ => stepRaw QF true bL_orig rL bR rR
      end
    else stepRaw QF true bL_orig rL bR rR
  | _ => stepRaw QF true bL_orig rL bR rR
  end.

Definition stepGenP1 (a b1 : Big) (lTail : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack)
    (bL_orig : list Tok) : HybState :=
  match bR with
  | TokO o0 :: TokZ z :: rTail =>
    if andb (isOneB o0) (negb (isZeroB z)) then
      let z1 := subSmall1B z in
      let rAfter := if isZeroB z1 then rTail else TokZ z1 :: rTail in
      match popBitR rAfter rR with
      | Some (h', bR', rR') =>
        let a' := addSmall2B a in
        let bL' := if isZeroB b1 then TokW a' :: pushTok (TokZ B1) lTail else TokW a' :: TokZ B1 :: TokW b1 :: lTail in
        finishGen QA h' bL' rL bR' rR'
      | None => stepRaw QF true bL_orig rL bR rR
      end
    else stepRaw QF true bL_orig rL bR rR
  | [TokO o0] =>
    if isOneB o0 then
      match rR with
      | RNil =>
        let a' := addSmall2B a in
        let bL' := if isZeroB b1 then TokW a' :: pushTok (TokZ B1) lTail else TokW a' :: TokZ B1 :: TokW b1 :: lTail in
        finishGen QA false bL' rL [] RNil
      | _ => stepRaw QF true bL_orig rL bR rR
      end
    else stepRaw QF true bL_orig rL bR rR
  | _ => stepRaw QF true bL_orig rL bR rR
  end.

Definition stepGenCore (q : Q_st) (h : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) : HybState :=
  match q, h with
  | QF, true =>
    match bL with
    | TokW a :: TokZ z0 :: TokW b :: lTail =>
      if isOneB z0 then
        if andb (negb (isZeroB a)) (negb (isZeroB b)) then
          let b1 := subSmall1B b in
          match bR with
          | TokW c :: rTail =>
            if isZeroB c then stepRaw QF true bL rL bR rR
            else
              let b2 := div2B b in
              let k0 := if lebB b2 c then b2 else c in
              let k := if eqbB k0 c then (if startsWith1 rTail then k0 else subSmall1B k0) else k0 in
              if negb (isZeroB k) then
                let a' := addB a (mul3addcB C0 k) in
                let b' := sub2xB b k in
                let bL' := if isZeroB b' then TokW a' :: pushTok (TokZ B1) lTail else TokW a' :: TokZ B1 :: TokW b' :: lTail in
                finishGen QF true bL' rL (subWHead c k rTail) rR
              else
                let a' := addSmall1B a in
                let bL' := if isZeroB b1 then TokW a' :: pushTok (TokZ B1) lTail else TokW a' :: TokZ B1 :: TokW b1 :: lTail in
                let bR' := TokO B1 :: pushTok (TokZ B2) (subWHead c B1 rTail) in
                finishGen QF true bL' rL bR' rR
          | TokO o0 :: TokZ z1 :: rTail =>
            if isOneB o0 then
              if isTwoB z1 then
                if startsWith1 rTail then
                  let a' := addSmall2B a in
                  let bL' := if isZeroB b1 then TokW a' :: pushTok (TokZ B1) lTail else TokW a' :: TokZ B1 :: TokW b1 :: lTail in
                  finishGen QF true bL' rL rTail rR
                else stepRaw QF true bL rL bR rR
              else if isThreeB z1 then
                match rTail with
                | TokW c :: rTail2 =>
                  if negb (isZeroB c) then
                    let ok := if isOneB c then startsWith1 rTail2 else true in
                    if ok then
                      let bL' := if isZeroB b1 then TokW B3 :: TokZ B1 :: TokW a :: pushTok (TokZ B1) lTail
                                 else TokW B3 :: TokZ B1 :: TokW a :: TokZ B1 :: TokW b1 :: lTail in
                      finishGen QF true bL' rL (subWHead c B1 rTail2) rR
                    else stepRaw QF true bL rL bR rR
                  else stepGenP1 a b1 lTail rL bR rR bL
                | _ => stepGenP1 a b1 lTail rL bR rR bL
                end
              else stepGenP1 a b1 lTail rL bR rR bL
            else stepRaw QF true bL rL bR rR
          | TokO o0 :: TokW c :: rTail =>
            if andb (isOneB o0) (lebB B2 c) then
              if lebB B2 b then
                let ok := if isTwoB c then startsWith1 rTail else true in
                if ok then
                  let a' := addSmall1B a in
                  let b2 := subSmall2B b in
                  let bL' := if isZeroB b2 then TokW B3 :: TokZ B1 :: TokW a' :: pushTok (TokZ B1) lTail
                             else TokW B3 :: TokZ B1 :: TokW a' :: TokZ B1 :: TokW b2 :: lTail in
                  finishGen QF true bL' rL (subWHead c B2 rTail) rR
                else stepRaw QF true bL rL bR rR
              else stepRaw QF true bL rL bR rR
            else stepRaw QF true bL rL bR rR
          | _ => stepGenP1 a b1 lTail rL bR rR bL
          end
        else if negb (isZeroB a) then stepGenF1PP a (TokZ z0 :: TokW b :: lTail) rL bR rR bL
        else stepRaw QF true bL rL bR rR
      else if isTwoB z0 then
        if andb (negb (isZeroB a)) (lebB B3 b) then
          if startsWith1 bR then
            let b3 := subSmall3B b in
            let bL' := if isZeroB b3 then TokW B3 :: pushTok (TokZ B1) lTail else TokW B3 :: TokZ B1 :: TokW b3 :: lTail in
            let bR' := pushTok (TokW a) (pushBit true bR (isEmptyR rR)) in
            finishGen QF true bL' rL bR' rR
          else stepGenF1PP a (TokZ z0 :: TokW b :: lTail) rL bR rR bL
        else if negb (isZeroB a) then stepGenF1PP a (TokZ z0 :: TokW b :: lTail) rL bR rR bL
        else stepRaw QF true bL rL bR rR
      else if negb (isZeroB a) then stepGenF1PP a (TokZ z0 :: TokW b :: lTail) rL bR rR bL
      else stepRaw QF true bL rL bR rR
    | [TokW a; TokO o0] =>
      if andb (negb (isZeroB a)) (isOneB o0) then
        match rL, bR with
        | LNil, TokW c :: rTail =>
          if isZeroB c then stepRaw QF true bL rL bR rR
          else
            let k := if startsWith1 rTail then c else subSmall1B c in
            if negb (isZeroB k) then
              let a' := addB a (mul3addcB C0 k) in
              finishGen QF true [TokW a'; TokO B1] LNil (subWHead c k rTail) rR
            else stepRaw QF true bL rL bR rR
        | _, _ => stepGenF1PP a [TokO o0] rL bR rR bL
        end
      else if negb (isZeroB a) then stepGenF1PP a [TokO o0] rL bR rR bL
      else stepRaw QF true bL rL bR rR
    | TokZ z0 :: TokW b :: lTail =>
      if isOneB z0 then
        if isZeroB b then stepRaw QF true bL rL bR rR
        else
          let b1 := subSmall1B b in
          let bL' := if isZeroB b1 then TokW B1 :: pushTok (TokZ B1) lTail else TokW B1 :: TokZ B1 :: TokW b1 :: lTail in
          finishGen QA true bL' rL bR rR
      else if isTwoB z0 then
        if isZeroB b then stepRaw QF true bL rL bR rR
        else
          let b1 := subSmall1B b in
          let bL' := if isZeroB b1 then pushTok (TokZ B1) lTail else TokZ B1 :: TokW b1 :: lTail in
          let bR' := pushTok (TokW B1) (pushBit true bR (isEmptyR rR)) in
          finishGen QF true bL' rL bR' rR
      else stepRaw QF true bL rL bR rR
    | TokW a :: lTail =>
      if isZeroB a then stepRaw QF true bL rL bR rR
      else stepGenF1PP a lTail rL bR rR bL
    | _ => stepRaw QF true bL rL bR rR
    end
  | QC, false =>
    match bR with
    | TokW c :: rTail =>
      if isZeroB c then stepRaw QC false bL rL bR rR
      else
        match popBitR rTail rR with
        | Some (h', bR', rR') =>
          let bL' := pushTok (TokW c) (pushBit true bL (isEmptyL rL)) in
          finishGen QA h' bL' rL bR' rR'
        | None => stepRaw QC false bL rL bR rR
        end
    | _ => stepRaw QC false bL rL bR rR
    end
  | QA, true =>
    match bR with
    | TokW c :: rTail =>
      if isZeroB c then stepRaw QA true bL rL bR rR
      else finishGen QF true bL rL (TokO B1 :: TokZ B2 :: subWHead c B1 rTail) rR
    | TokO n :: rTail =>
      if lebB B2 n then
        let n2 := subSmall2B n in
        let rRest := if isZeroB n2 then rTail else TokO n2 :: rTail in
        finishGen QF true bL rL (TokO B1 :: pushTok (TokZ B1) rRest) rR
      else if isOneB n then
        match rTail with
        | TokZ z :: rTail2 =>
          if isZeroB z then stepRaw QA true bL rL bR rR
          else
            let z1 := subSmall1B z in
            let rAfter := if isZeroB z1 then rTail2 else TokZ z1 :: rTail2 in
            match rAfter with
            | TokW c :: rTail3 =>
              if isZeroB c then
                match popBitR rAfter rR with
                | Some (h', bR', rR') => finishGen QA h' (pushTok (TokW B1) bL) rL bR' rR'
                | None => stepRaw QA true bL rL bR rR
                end
              else
                match popBitR rTail3 rR with
                | Some (h', bR', rR') => finishGen QA h' (pushTok (TokW (addSmall1B c)) bL) rL bR' rR'
                | None => stepRaw QA true bL rL bR rR
                end
            | _ =>
              match popBitR rAfter rR with
              | Some (h', bR', rR') => finishGen QA h' (pushTok (TokW B1) bL) rL bR' rR'
              | None => stepRaw QA true bL rL bR rR
              end
            end
        | [] =>
          match rR with
          | RNil => finishGen QA false (pushTok (TokW B1) bL) rL [] RNil
          | _ => stepRaw QA true bL rL bR rR
          end
        | TokW c :: rTail2 =>
          if isZeroB c then stepRaw QA true bL rL bR rR
          else finishGen QF true bL rL (TokO B1 :: TokZ B1 :: TokO B1 :: TokZ B1 :: subWHead c B1 rTail2) rR
        | _ => stepRaw QA true bL rL bR rR
        end
      else stepRaw QA true bL rL bR rR
    | _ => stepRaw QA true bL rL bR rR
    end
  | _, _ => stepRaw q h bL rL bR rR
  end.

Definition stepGen (q : Q_st) (h : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) : HybState :=
  let pL := ensureL bL rL in
  let pR := ensureR bR rR in
  stepGenCore q h (fst pL) (snd pL) (fst pR) (snd pR).

Fixpoint runGenChunk (kg : nat) (s : HybState) : HybState :=
  match kg with
  | O => s
  | S kg' =>
    match s with
    | HClean sL sR => HClean sL sR
    | HGen q h bL rL bR rR => runGenChunk kg' (stepGen q h bL rL bR rR)
    end
  end.


Definition stepOuter (s : HybState) : HybState :=
  match s with
  | HClean sL sR => runCleanChunk kc1000 sL sR
  | HGen q h bL rL bR rR => runGenChunk kg128 (HGen q h bL rL bR rR)
  end.

Definition r1Start : HybState := HGen QA false [] LNil [] RNil.

Definition check_cycler_entry (s : HybState) : bool :=
  match s with
  | HGen QA true (TokW n :: _) _ [] RNil => lebB B18 n
  | _ => false
  end.

Definition d64ToNat (d : D64) : nat := match d with D0 => 0 | D1 => 1 | D2 => 2 | D3 => 3 | D4 => 4 | D5 => 5 | D6 => 6 | D7 => 7 | D8 => 8 | D9 => 9 | D10 => 10 | D11 => 11 | D12 => 12 | D13 => 13 | D14 => 14 | D15 => 15 | D16 => 16 | D17 => 17 | D18 => 18 | D19 => 19 | D20 => 20 | D21 => 21 | D22 => 22 | D23 => 23 | D24 => 24 | D25 => 25 | D26 => 26 | D27 => 27 | D28 => 28 | D29 => 29 | D30 => 30 | D31 => 31 | D32 => 32 | D33 => 33 | D34 => 34 | D35 => 35 | D36 => 36 | D37 => 37 | D38 => 38 | D39 => 39 | D40 => 40 | D41 => 41 | D42 => 42 | D43 => 43 | D44 => 44 | D45 => 45 | D46 => 46 | D47 => 47 | D48 => 48 | D49 => 49 | D50 => 50 | D51 => 51 | D52 => 52 | D53 => 53 | D54 => 54 | D55 => 55 | D56 => 56 | D57 => 57 | D58 => 58 | D59 => 59 | D60 => 60 | D61 => 61 | D62 => 62 | D63 => 63 end.
Definition valC6 (c : C6) : nat := match c with C0 => 0 | C1 => 1 | C2 => 2 | C3 => 3 | C4 => 4 | C5 => 5 end.
Definition all_D64 : list D64 := [D0; D1; D2; D3; D4; D5; D6; D7; D8; D9; D10; D11; D12; D13; D14; D15; D16; D17; D18; D19; D20; D21; D22; D23; D24; D25; D26; D27; D28; D29; D30; D31; D32; D33; D34; D35; D36; D37; D38; D39; D40; D41; D42; D43; D44; D45; D46; D47; D48; D49; D50; D51; D52; D53; D54; D55; D56; D57; D58; D59; D60; D61; D62; D63].
Definition all_C6 : list C6 := [C0; C1; C2; C3; C4; C5].
Definition all_C3 : list C6 := [C0; C1; C2].
Definition all_bool : list bool := [false; true].

Fixpoint wfB (x : Big) : Prop :=
  match x with
  | BNil => True
  | BUnder => False
  | BCons d tl => wfB tl /\ (tl = BNil -> d <> D0)
  end.

Fixpoint toNatB (x : Big) : nat :=
  match x with
  | BNil | BUnder => 0
  | BCons d tl => d64ToNat d + 64 * toNatB tl
  end.

Definition wfTok (t : Tok) : Prop :=
  match t with TokZ n | TokO n | TokW n => wfB n end.

Definition evalTok (t : Tok) : TokN :=
  match t with
  | TokZ n => TokZN (toNatB n)
  | TokO n => TokON (toNatB n)
  | TokW n => TokWN (toNatB n)
  end.

Fixpoint wfToks (ts : list Tok) : Prop :=
  match ts with
  | [] => True
  | t :: rest => wfTok t /\ wfToks rest
  end.

Fixpoint evalToks (ts : list Tok) : list TokN :=
  match ts with
  | [] => []
  | t :: rest => evalTok t :: evalToks rest
  end.

Fixpoint wfL (sL : LStack) : Prop :=
  match sL with
  | LNil => True
  | LC b tl => wfB b /\ wfL tl
  | LTok t tl => wfTok t /\ wfL tl
  end.

Fixpoint evalL (sL : LStack) : LStackN :=
  match sL with
  | LNil => LNilN
  | LC b tl => LCN (toNatB b) (evalL tl)
  | LTok t tl => LTokN (evalTok t) (evalL tl)
  end.

Fixpoint wfR (sR : RStack) : Prop :=
  match sR with
  | RNil => True
  | RC _ c tl => wfB c /\ wfR tl
  | RTok t tl => wfTok t /\ wfR tl
  end.

Fixpoint evalR (sR : RStack) : RStackN :=
  match sR with
  | RNil => RNilN
  | RC b c tl => RCN b (toNatB c) (evalR tl)
  | RTok t tl => RTokN (evalTok t) (evalR tl)
  end.

Definition wfHyb (s : HybState) : Prop :=
  match s with
  | HClean sL sR => wfL sL /\ wfR sR
  | HGen _ _ bL rL bR rR => wfToks bL /\ wfL rL /\ wfToks bR /\ wfR rR
  end.

Definition evalHyb (s : HybState) : HybStateN :=
  match s with
  | HClean sL sR => HCleanN (evalL sL) (evalR sR)
  | HGen q h bL rL bR rR => HGenN q h (evalToks bL) (evalL rL) (evalToks bR) (evalR rR)
  end.

(** ** 7. Canonical [wfB] & Arithmetic Equivalence of [Big] Operations *)

Lemma in_all_D64 (d : D64) : List.In d all_D64.
Proof. destruct d; cbn; auto 70. Qed.

Lemma in_all_C6 (c : C6) : List.In c all_C6.
Proof. destruct c; cbn; auto 10. Qed.

Lemma in_all_C3 (c : C6) : (c = C0 \/ c = C1 \/ c = C2) -> List.In c all_C3.
Proof. intros [-> | [-> | ->]]; cbn; auto. Qed.

Lemma in_all_bool (b : bool) : List.In b all_bool.
Proof. destruct b; cbn; auto. Qed.

Lemma d64_bound (d : D64) : d64ToNat d < 64 /\ (d64ToNat d = 0 <-> d = D0).
Proof.
  destruct d; cbn [d64ToNat];
    (split; [lia | split; intro H; [reflexivity || lia | subst; reflexivity || discriminate]]).
Qed.

Lemma wfB_cons_pos (x : Big) :
  wfB x -> match x with BCons _ _ => 1 <= toNatB x | _ => True end.
Proof.
  induction x as [| | d tl IH]; intro Hwf.
  - exact I.
  - contradiction.
  - destruct Hwf as [Htl Hnz]; specialize (IH Htl); cbn [toNatB].
    destruct tl as [| | d2 tl2].
    + pose proof (Hnz eq_refl) as Hd.
      pose proof (d64_bound d) as [_ Hd0].
      destruct (Nat.eq_dec (d64ToNat d) 0) as [Hz | Hpos]; [exfalso; apply Hd, Hd0, Hz | lia].
    + contradiction.
    + lia.
Qed.

Lemma toNatB_zero_iff (x : Big) : wfB x -> (toNatB x = 0 <-> x = BNil).
Proof.
  destruct x as [| | d tl]; intro Hwf.
  - cbn; tauto.
  - contradiction.
  - pose proof (wfB_cons_pos (BCons d tl) Hwf) as Hpos.
    split; [lia | discriminate].
Qed.

Lemma isZeroB_spec (x : Big) : wfB x -> isZeroB x = isZeroN (toNatB x).
Proof.
  destruct x as [| | d tl]; intro Hwf.
  - reflexivity.
  - contradiction.
  - pose proof (wfB_cons_pos (BCons d tl) Hwf) as Hpos.
    cbn [isZeroB]; unfold isZeroN; symmetry; apply Nat.eqb_neq; lia.
Qed.

Lemma mkBCons_spec (d : D64) (tl : Big) :
  wfB tl -> wfB (mkBCons d tl) /\ toNatB (mkBCons d tl) = d64ToNat d + 64 * toNatB tl.
Proof.
  intro Htl; destruct tl as [| | d2 tl2].
  - destruct d;
      try (split; [split; [exact I | intros _; discriminate] | reflexivity]);
      split; [exact I | reflexivity].
  - contradiction.
  - assert (Hmk : mkBCons d (BCons d2 tl2) = BCons d (BCons d2 tl2)) by (destruct d; reflexivity).
    rewrite Hmk; split; [split; [exact Htl | discriminate] | reflexivity].
Qed.

Lemma combineTry_spec (lo : D64) (z : Big) :
  wfB z -> wfB (combineTry lo z) /\ toNatB (combineTry lo z) = d64ToNat lo + 64 * toNatB z.
Proof.
  intro Hwf; assert (Heq : combineTry lo z = mkBCons lo z) by (destruct lo, z; try contradiction; reflexivity).
  rewrite Heq; exact (mkBCons_spec lo z Hwf).
Qed.

Lemma wfB_B0 : wfB B0. Proof. exact I. Qed.
Lemma wfB_B1 : wfB B1. Proof. split; [exact I | discriminate]. Qed.
Lemma wfB_B2 : wfB B2. Proof. split; [exact I | discriminate]. Qed.
Lemma wfB_B3 : wfB B3. Proof. split; [exact I | discriminate]. Qed.
Lemma wfB_B18 : wfB B18. Proof. split; [exact I | discriminate]. Qed.

Lemma isOneB_spec (x : Big) : wfB x -> isOneB x = isOneN (toNatB x).
Proof.
  destruct x as [| | d [| | d2 tl2]]; intro Hwf;
    [reflexivity | contradiction | destruct d; reflexivity | destruct Hwf as [Htl _]; contradiction | ].
  destruct Hwf as [Htl _]; pose proof (wfB_cons_pos _ Htl) as Hpos.
  replace (isOneB (BCons d (BCons d2 tl2))) with false by (destruct d; reflexivity).
  cbn [toNatB] in *; unfold isOneN; symmetry; apply Nat.eqb_neq; lia.
Qed.

Lemma isTwoB_spec (x : Big) : wfB x -> isTwoB x = isTwoN (toNatB x).
Proof.
  destruct x as [| | d [| | d2 tl2]]; intro Hwf;
    [reflexivity | contradiction | destruct d; reflexivity | destruct Hwf as [Htl _]; contradiction | ].
  destruct Hwf as [Htl _]; pose proof (wfB_cons_pos _ Htl) as Hpos.
  replace (isTwoB (BCons d (BCons d2 tl2))) with false by (destruct d; reflexivity).
  cbn [toNatB] in *; unfold isTwoN; symmetry; apply Nat.eqb_neq; lia.
Qed.

Lemma isThreeB_spec (x : Big) : wfB x -> isThreeB x = isThreeN (toNatB x).
Proof.
  destruct x as [| | d [| | d2 tl2]]; intro Hwf;
    [reflexivity | contradiction | destruct d; reflexivity | destruct Hwf as [Htl _]; contradiction | ].
  destruct Hwf as [Htl _]; pose proof (wfB_cons_pos _ Htl) as Hpos.
  replace (isThreeB (BCons d (BCons d2 tl2))) with false by (destruct d; reflexivity).
  cbn [toNatB] in *; unfold isThreeN; symmetry; apply Nat.eqb_neq; lia.
Qed.

Lemma d64_parity (d : D64) (tl : Big) :
  d64ToNat d = 2 * halfN (d64ToNat d) + (if evenB (BCons d tl) then 0 else 1) /\
  evenB (BCons d tl) = evenN (d64ToNat d) /\
  oddB (BCons d tl) = negb (evenB (BCons d tl)).
Proof.
  destruct d; repeat split; reflexivity.
Qed.

Lemma evenB_spec (x : Big) : evenB x = evenN (toNatB x).
Proof.
  destruct x as [| | d tl]; [reflexivity | reflexivity | ].
  destruct (d64_parity d tl) as [Hd [Hev _]].
  cbn [toNatB].
  symmetry; eapply proj2; apply (halfN_unique _ (halfN (d64ToNat d) + 32 * toNatB tl)).
  destruct (evenB (BCons d tl)); lia.
Qed.

Lemma oddB_spec (x : Big) : oddB x = oddN (toNatB x).
Proof.
  unfold oddN; rewrite <- evenB_spec.
  destruct x as [| | d tl]; [reflexivity | reflexivity | ].
  destruct (d64_parity d tl) as [_ [_ Hodd]]; exact Hodd.
Qed.

Lemma halfN_cons (d0 : D64) (bt : Big) :
  halfN (toNatB (BCons d0 bt)) =
  halfN (d64ToNat d0) + (if oddB bt then 32 else 0) + 64 * halfN (toNatB bt).
Proof.
  destruct (d64_parity d0 bt) as [Hd0 _].
  pose proof (halfN_evenN_spec (toNatB bt)) as Hbt.
  pose proof (oddB_spec bt) as Hodd; unfold oddN in Hodd.
  cbn [toNatB].
  eapply proj1; apply (halfN_unique _ _ (evenB (BCons d0 bt))).
  destruct (evenN (toNatB bt)); cbn [negb] in Hodd; rewrite Hodd;
    destruct (evenB (BCons d0 bt)); lia.
Qed.

Lemma incB_cons_step (d : D64) (xt : Big) :
  (d = D63 /\ incB (BCons d xt) = BCons D0 (incB xt)) \/
  (exists d', d' <> D0 /\ d64ToNat d' = d64ToNat d + 1 /\ incB (BCons d xt) = BCons d' xt).
Proof.
  destruct d;
    try (right; eexists; (split; [| split; [| reflexivity]]); [discriminate | reflexivity]);
    left; split; reflexivity.
Qed.

Lemma incB_spec (x : Big) :
  wfB x -> wfB (incB x) /\ toNatB (incB x) = toNatB x + 1.
Proof.
  induction x as [| | d xt IH]; intro Hwf.
  - split; [exact wfB_B1 | reflexivity].
  - contradiction.
  - destruct Hwf as [Hxt _].
    destruct (incB_cons_step d xt) as [[-> Heq] | [d' [Hd' [Hval Heq]]]]; rewrite Heq.
    + destruct (IH Hxt) as [Hwfi Heqi].
      split.
      * split; [exact Hwfi | intro Hnil; apply (proj2 (toNatB_zero_iff _ Hwfi)) in Hnil; lia].
      * cbn [toNatB d64ToNat]; lia.
    + split; [split; [exact Hxt | intros _; exact Hd'] | cbn [toNatB]; lia].
Qed.

Lemma addSmall1B_spec (x : Big) :
  wfB x -> wfB (addSmall1B x) /\ toNatB (addSmall1B x) = toNatB x + 1.
Proof. exact (incB_spec x). Qed.

Lemma addSmall2B_cons_step (d : D64) (xt : Big) :
  (d = D62 /\ addSmall2B (BCons d xt) = BCons D0 (incB xt)) \/
  (d = D63 /\ addSmall2B (BCons d xt) = BCons D1 (incB xt)) \/
  (exists d', d' <> D0 /\ d64ToNat d' = d64ToNat d + 2 /\ addSmall2B (BCons d xt) = BCons d' xt).
Proof.
  destruct d;
    try (right; right; eexists; (split; [| split; [| reflexivity]]); [discriminate | reflexivity]);
    [left; split; reflexivity | right; left; split; reflexivity].
Qed.

Lemma addSmall2B_spec (x : Big) :
  wfB x -> wfB (addSmall2B x) /\ toNatB (addSmall2B x) = toNatB x + 2.
Proof.
  destruct x as [| | d xt]; intro Hwf.
  - split; [exact wfB_B2 | reflexivity].
  - contradiction.
  - destruct Hwf as [Hxt _]; destruct (incB_spec xt Hxt) as [Hwfi Heqi].
    destruct (addSmall2B_cons_step d xt) as [[-> Heq] | [[-> Heq] | [d' [Hd' [Hval Heq]]]]]; rewrite Heq.
    + split; [split; [exact Hwfi | intro Hnil; apply (proj2 (toNatB_zero_iff _ Hwfi)) in Hnil; lia] | cbn [toNatB d64ToNat]; lia].
    + split; [split; [exact Hwfi | discriminate] | cbn [toNatB d64ToNat]; lia].
    + split; [split; [exact Hxt | intros _; exact Hd'] | cbn [toNatB]; lia].
Qed.

Lemma dec1B_cons_step (d : D64) (xt : Big) :
  (d = D0 /\ dec1B (BCons d xt) = BCons D63 (dec1B xt)) \/
  (d = D1 /\ dec1B (BCons d xt) = mkBCons D0 xt) \/
  (exists d', d' <> D0 /\ d64ToNat d = d64ToNat d' + 1 /\ dec1B (BCons d xt) = BCons d' xt).
Proof.
  destruct d;
    [left; split; reflexivity | right; left; split; reflexivity |
     (right; right; eexists; (split; [| split; [| reflexivity]]); [discriminate | reflexivity])..].
Qed.

Lemma dec1B_spec (x : Big) :
  wfB x -> 1 <= toNatB x -> wfB (dec1B x) /\ toNatB (dec1B x) = toNatB x - 1.
Proof.
  induction x as [| | d xt IH]; intros Hwf Hpos.
  - cbn [toNatB] in Hpos; lia.
  - contradiction.
  - destruct Hwf as [Hxt Hnz].
    destruct (dec1B_cons_step d xt) as [[-> Heq] | [[-> Heq] | [d' [Hd' [Hval Heq]]]]]; rewrite Heq.
    + assert (Hxt_pos : 1 <= toNatB xt).
      { destruct (Nat.eq_dec (toNatB xt) 0) as [Hz | Hnz']; [| lia].
        apply (proj1 (toNatB_zero_iff xt Hxt)) in Hz; exfalso; exact (Hnz Hz eq_refl). }
      destruct (IH Hxt Hxt_pos) as [Hwfd Heqd].
      split; [split; [exact Hwfd | discriminate] | cbn [toNatB d64ToNat]; lia].
    + destruct (mkBCons_spec D0 xt Hxt) as [Hwfm Heqm].
      split; [exact Hwfm | cbn [toNatB d64ToNat] in *; lia].
    + split; [split; [exact Hxt | intros _; exact Hd'] | cbn [toNatB]; lia].
Qed.

Lemma dec2B_cons_step (d : D64) (xt : Big) :
  (d = D0 /\ dec2B (BCons d xt) = BCons D62 (dec1B xt)) \/
  (d = D1 /\ dec2B (BCons d xt) = BCons D63 (dec1B xt)) \/
  (d = D2 /\ dec2B (BCons d xt) = mkBCons D0 xt) \/
  (exists d', d' <> D0 /\ d64ToNat d = d64ToNat d' + 2 /\ dec2B (BCons d xt) = BCons d' xt).
Proof.
  destruct d;
    [left; split; reflexivity | right; left; split; reflexivity | right; right; left; split; reflexivity |
     (right; right; right; eexists; (split; [| split; [| reflexivity]]); [discriminate | reflexivity])..].
Qed.

Lemma dec2B_spec (x : Big) :
  wfB x -> 2 <= toNatB x -> wfB (dec2B x) /\ toNatB (dec2B x) = toNatB x - 2.
Proof.
  destruct x as [| | d xt]; intros Hwf Hpos.
  - cbn [toNatB] in Hpos; lia.
  - contradiction.
  - destruct Hwf as [Hxt Hnz].
    destruct (dec2B_cons_step d xt) as [[-> Heq] | [[-> Heq] | [[-> Heq] | [d' [Hd' [Hval Heq]]]]]]; rewrite Heq.
    + cbn [toNatB d64ToNat] in Hpos.
      destruct (dec1B_spec xt Hxt ltac:(lia)) as [Hwfd Heqd].
      split; [split; [exact Hwfd | discriminate] | cbn [toNatB d64ToNat]; lia].
    + cbn [toNatB d64ToNat] in Hpos.
      destruct (dec1B_spec xt Hxt ltac:(lia)) as [Hwfd Heqd].
      split; [split; [exact Hwfd | discriminate] | cbn [toNatB d64ToNat]; lia].
    + destruct (mkBCons_spec D0 xt Hxt) as [Hwfm Heqm].
      split; [exact Hwfm | cbn [toNatB d64ToNat] in *; lia].
    + split; [split; [exact Hxt | intros _; exact Hd'] | cbn [toNatB]; lia].
Qed.

Lemma subSmall1B_spec (x : Big) :
  wfB x -> wfB (subSmall1B x) /\ toNatB (subSmall1B x) = toNatB x - 1.
Proof.
  destruct x as [| | d xt]; intro Hwf.
  - split; [exact I | reflexivity].
  - contradiction.
  - pose proof (wfB_cons_pos (BCons d xt) Hwf) as Hpos.
    assert (Heq : subSmall1B (BCons d xt) = dec1B (BCons d xt)).
    { destruct Hwf as [Hxt Hnz].
      destruct d; try reflexivity.
      destruct xt; [exfalso; exact (Hnz eq_refl eq_refl) | contradiction | reflexivity]. }
    rewrite Heq; exact (dec1B_spec (BCons d xt) Hwf Hpos).
Qed.

Lemma subSmall2B_spec (x : Big) :
  wfB x -> wfB (subSmall2B x) /\ toNatB (subSmall2B x) = toNatB x - 2.
Proof.
  destruct x as [| | d xt]; intro Hwf.
  - split; [exact I | reflexivity].
  - contradiction.
  - pose proof Hwf as [Hxt Hnz].
    destruct d, xt as [| | d2 xt2];
      try contradiction;
      try (exfalso; exact (Hnz eq_refl eq_refl));
      try (split; [exact I | reflexivity]);
      exact (dec2B_spec _ Hwf ltac:(try (pose proof (wfB_cons_pos _ Hxt)); cbn [toNatB d64ToNat] in *; lia)).
Qed.

Lemma subSmall3B_cons_step (d : D64) (xt : Big) :
  (d = D0 /\ subSmall3B (BCons d xt) = match xt with BCons _ _ => BCons D61 (dec1B xt) | _ => BNil end) \/
  (d = D1 /\ subSmall3B (BCons d xt) = match xt with BCons _ _ => BCons D62 (dec1B xt) | _ => BNil end) \/
  (d = D2 /\ subSmall3B (BCons d xt) = match xt with BCons _ _ => BCons D63 (dec1B xt) | _ => BNil end) \/
  (d = D3 /\ subSmall3B (BCons d xt) = mkBCons D0 xt) \/
  (exists d', d' <> D0 /\ d64ToNat d = d64ToNat d' + 3 /\ subSmall3B (BCons d xt) = BCons d' xt).
Proof.
  destruct d;
    [left; split; reflexivity | right; left; split; reflexivity |
     right; right; left; split; reflexivity | right; right; right; left; split; reflexivity |
     (right; right; right; right; eexists; (split; [| split; [| reflexivity]]); [discriminate | reflexivity])..].
Qed.

Lemma subSmall3B_spec (x : Big) :
  wfB x -> wfB (subSmall3B x) /\ toNatB (subSmall3B x) = toNatB x - 3.
Proof.
  destruct x as [| | d xt]; intro Hwf.
  - split; [exact I | reflexivity].
  - contradiction.
  - destruct Hwf as [Hxt Hnz].
    destruct (subSmall3B_cons_step d xt) as [[-> Heq] | [[-> Heq] | [[-> Heq] | [[-> Heq] | [d' [Hd' [Hval Heq]]]]]]]; rewrite Heq.
    + destruct xt as [| | d2 xt2]; [exfalso; exact (Hnz eq_refl eq_refl) | contradiction | ].
      pose proof (wfB_cons_pos _ Hxt) as Hpos; destruct (dec1B_spec _ Hxt Hpos) as [Hwfd Heqd].
      split; [split; [exact Hwfd | discriminate] | cbn [toNatB d64ToNat] in *; lia].
    + destruct xt as [| | d2 xt2]; [split; [exact I | reflexivity] | contradiction | ].
      pose proof (wfB_cons_pos _ Hxt) as Hpos; destruct (dec1B_spec _ Hxt Hpos) as [Hwfd Heqd].
      split; [split; [exact Hwfd | discriminate] | cbn [toNatB d64ToNat] in *; lia].
    + destruct xt as [| | d2 xt2]; [split; [exact I | reflexivity] | contradiction | ].
      pose proof (wfB_cons_pos _ Hxt) as Hpos; destruct (dec1B_spec _ Hxt Hpos) as [Hwfd Heqd].
      split; [split; [exact Hwfd | discriminate] | cbn [toNatB d64ToNat] in *; lia].
    + destruct (mkBCons_spec D0 xt Hxt) as [Hwfm Heqm].
      split; [exact Hwfm | cbn [toNatB d64ToNat] in *; lia].
    + split; [split; [exact Hxt | intros _; exact Hd'] | cbn [toNatB]; lia].
Qed.

(** *** 1-Limb Table Certificates via [vm_cast_no_check] *)

Lemma add64c_cert :
  List.forallb (fun c =>
    List.forallb (fun a =>
      List.forallb (fun b =>
        let r := add64c c a b in
        Nat.eqb (d64ToNat (lo128 r) + 64 * (if hi128 r then 1 else 0))
                (d64ToNat a + d64ToNat b + (if c then 1 else 0))
      ) all_D64) all_D64) all_bool = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma add64c_spec (c : bool) (a b : D64) :
  d64ToNat (lo128 (add64c c a b)) + 64 * (if hi128 (add64c c a b) then 1 else 0) =
  d64ToNat a + d64ToNat b + (if c then 1 else 0).
Proof.
  pose proof add64c_cert as H.
  rewrite List.forallb_forall in H; specialize (H c (in_all_bool c)).
  rewrite List.forallb_forall in H; specialize (H a (in_all_D64 a)).
  rewrite List.forallb_forall in H; specialize (H b (in_all_D64 b)).
  apply Nat.eqb_eq in H; exact H.
Qed.

Lemma sub64b_cert :
  List.forallb (fun br =>
    List.forallb (fun a =>
      List.forallb (fun b =>
        let r := sub64b br a b in
        Nat.eqb (d64ToNat a + 64 * (if hi128 r then 1 else 0))
                (d64ToNat b + (if br then 1 else 0) + d64ToNat (lo128 r))
      ) all_D64) all_D64) all_bool = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma sub64b_spec (br : bool) (a b : D64) :
  d64ToNat a + 64 * (if hi128 (sub64b br a b) then 1 else 0) =
  d64ToNat b + (if br then 1 else 0) + d64ToNat (lo128 (sub64b br a b)).
Proof.
  pose proof sub64b_cert as H.
  rewrite List.forallb_forall in H; specialize (H br (in_all_bool br)).
  rewrite List.forallb_forall in H; specialize (H a (in_all_D64 a)).
  rewrite List.forallb_forall in H; specialize (H b (in_all_D64 b)).
  apply Nat.eqb_eq in H; exact H.
Qed.

Lemma eqb64_cert :
  List.forallb (fun a =>
    List.forallb (fun b =>
      Bool.eqb (match sub64b false a b with P0 => true | _ => false end)
               (Nat.eqb (d64ToNat a) (d64ToNat b))
    ) all_D64) all_D64 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma eqb64_spec (a b : D64) :
  (match sub64b false a b with P0 => true | _ => false end) = Nat.eqb (d64ToNat a) (d64ToNat b).
Proof.
  pose proof eqb64_cert as H.
  rewrite List.forallb_forall in H; specialize (H a (in_all_D64 a)).
  rewrite List.forallb_forall in H; specialize (H b (in_all_D64 b)).
  apply Bool.eqb_prop in H; exact H.
Qed.

Lemma sub2xTryB_cons (br : C6) (a b : D64) (xt yt : Big) :
  (br = C0 \/ br = C1 \/ br = C2) ->
  sub2xTryB br (BCons a xt) (BCons b yt) =
  combineTry (lo256 (sub2x64 br a b)) (sub2xTryB (hi256 (sub2x64 br a b)) xt yt).
Proof.
  intros [-> | [-> | ->]]; exact eq_refl.
Qed.

Lemma sub2x_limb_cert :
  List.forallb (fun br =>
    List.forallb (fun a =>
      List.forallb (fun b =>
        let r := sub2x64 br a b in
        let hi := hi256 r in
        let lo := lo256 r in
        andb (Nat.eqb (d64ToNat a + 64 * valC6 hi) (2 * d64ToNat b + valC6 br + d64ToNat lo))
             (match hi with C0 | C1 | C2 => true | _ => false end)
      ) all_D64) all_D64) all_C3 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma sub2x_limb_spec (br : C6) (a b : D64) :
  (br = C0 \/ br = C1 \/ br = C2) ->
  d64ToNat a + 64 * valC6 (hi256 (sub2x64 br a b)) =
    2 * d64ToNat b + valC6 br + d64ToNat (lo256 (sub2x64 br a b)) /\
  (hi256 (sub2x64 br a b) = C0 \/ hi256 (sub2x64 br a b) = C1 \/ hi256 (sub2x64 br a b) = C2).
Proof.
  intro Hbr; pose proof sub2x_limb_cert as H.
  rewrite List.forallb_forall in H; specialize (H br (in_all_C3 br Hbr)).
  rewrite List.forallb_forall in H; specialize (H a (in_all_D64 a)).
  rewrite List.forallb_forall in H; specialize (H b (in_all_D64 b)).
  apply Bool.andb_true_iff in H; destruct H as [H1 H2].
  apply Nat.eqb_eq in H1; split; [exact H1 | ].
  destruct (hi256 (sub2x64 br a b)); auto; discriminate.
Qed.

Lemma subHalfTryB_cons (br : bool) (a d0 : D64) (xt bt : Big) :
  subHalfTryB br (BCons a xt) (BCons d0 bt) =
  combineTry (lo128 (subHalf64 br (oddB bt) a d0)) (subHalfTryB (hi128 (subHalf64 br (oddB bt) a d0)) xt bt).
Proof.
  exact eq_refl.
Qed.

Lemma subHalf_limb_cert :
  List.forallb (fun br =>
    List.forallb (fun q_hi =>
      List.forallb (fun a =>
        List.forallb (fun d0 =>
          let r := subHalf64 br q_hi a d0 in
          let hi := hi128 r in
          let lo := lo128 r in
          Nat.eqb (d64ToNat a + 64 * (if hi then 1 else 0))
                  (halfN (d64ToNat d0) + (if q_hi then 32 else 0) + (if br then 1 else 0) + d64ToNat lo)
        ) all_D64) all_D64) all_bool) all_bool = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma subHalf_limb_spec (br q_hi : bool) (a d0 : D64) :
  d64ToNat a + 64 * (if hi128 (subHalf64 br q_hi a d0) then 1 else 0) =
  halfN (d64ToNat d0) + (if q_hi then 32 else 0) + (if br then 1 else 0) + d64ToNat (lo128 (subHalf64 br q_hi a d0)).
Proof.
  pose proof subHalf_limb_cert as H.
  rewrite List.forallb_forall in H; specialize (H br (in_all_bool br)).
  rewrite List.forallb_forall in H; specialize (H q_hi (in_all_bool q_hi)).
  rewrite List.forallb_forall in H; specialize (H a (in_all_D64 a)).
  rewrite List.forallb_forall in H; specialize (H d0 (in_all_D64 d0)).
  apply Nat.eqb_eq in H; exact H.
Qed.

Lemma mul3addcB_cons (c : C6) (a : D64) (xt : Big) :
  mul3addcB c (BCons a xt) = mkBCons (lo256 (mul3_64 c a)) (mul3addcB (hi256 (mul3_64 c a)) xt).
Proof.
  exact eq_refl.
Qed.

Lemma mul3_limb_cert :
  List.forallb (fun c =>
    List.forallb (fun a =>
      let r := mul3_64 c a in
      Nat.eqb (d64ToNat (lo256 r) + 64 * valC6 (hi256 r))
              (3 * d64ToNat a + valC6 c)
    ) all_D64) all_C6 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma mul3_limb_spec (c : C6) (a : D64) :
  d64ToNat (lo256 (mul3_64 c a)) + 64 * valC6 (hi256 (mul3_64 c a)) = 3 * d64ToNat a + valC6 c.
Proof.
  pose proof mul3_limb_cert as H.
  rewrite List.forallb_forall in H; specialize (H c (in_all_C6 c)).
  rewrite List.forallb_forall in H; specialize (H a (in_all_D64 a)).
  apply Nat.eqb_eq in H; exact H.
Qed.

Lemma mul3halfB_cons (c : C6) (d0 : D64) (bt : Big) :
  mul3halfB c (BCons d0 bt) =
  mkBCons (lo256 (mul3half_64 (oddB bt) c d0)) (mul3halfB (hi256 (mul3half_64 (oddB bt) c d0)) bt).
Proof.
  exact eq_refl.
Qed.

Lemma mul3half_limb_cert :
  List.forallb (fun q_hi =>
    List.forallb (fun c =>
      List.forallb (fun d0 =>
        let r := mul3half_64 q_hi c d0 in
        Nat.eqb (d64ToNat (lo256 r) + 64 * valC6 (hi256 r))
                (3 * (halfN (d64ToNat d0) + (if q_hi then 32 else 0)) + valC6 c)
      ) all_D64) all_C6) all_bool = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma mul3half_limb_spec (q_hi : bool) (c : C6) (d0 : D64) :
  d64ToNat (lo256 (mul3half_64 q_hi c d0)) + 64 * valC6 (hi256 (mul3half_64 q_hi c d0)) =
  3 * (halfN (d64ToNat d0) + (if q_hi then 32 else 0)) + valC6 c.
Proof.
  pose proof mul3half_limb_cert as H.
  rewrite List.forallb_forall in H; specialize (H q_hi (in_all_bool q_hi)).
  rewrite List.forallb_forall in H; specialize (H c (in_all_C6 c)).
  rewrite List.forallb_forall in H; specialize (H d0 (in_all_D64 d0)).
  apply Nat.eqb_eq in H; exact H.
Qed.

Lemma div2B_cons (a : D64) (xt : Big) :
  div2B (BCons a xt) = mkBCons (div2_64 (oddB xt) a) (div2B xt).
Proof.
  exact eq_refl.
Qed.

Lemma div2_limb_cert :
  List.forallb (fun q_hi =>
    List.forallb (fun a =>
      Nat.eqb (d64ToNat (div2_64 q_hi a)) (halfN (d64ToNat a) + (if q_hi then 32 else 0))
    ) all_D64) all_bool = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma div2_limb_spec (q_hi : bool) (a : D64) :
  d64ToNat (div2_64 q_hi a) = halfN (d64ToNat a) + (if q_hi then 32 else 0).
Proof.
  pose proof div2_limb_cert as H.
  rewrite List.forallb_forall in H; specialize (H q_hi (in_all_bool q_hi)).
  rewrite List.forallb_forall in H; specialize (H a (in_all_D64 a)).
  apply Nat.eqb_eq in H; exact H.
Qed.

(** *** Inductive Multi-Limb [Big] Specifications *)

Lemma addcB_spec (x : Big) :
  forall (c : bool) (y : Big),
    wfB x -> wfB y ->
    wfB (addcB c x y) /\ toNatB (addcB c x y) = toNatB x + toNatB y + (if c then 1 else 0).
Proof.
  induction x as [| | a xt IH]; intros c y Hx Hy.
  - destruct y as [| | b yt]; [| contradiction | ].
    + destruct c; [split; [exact wfB_B1 | reflexivity] | split; [exact I | reflexivity]].
    + cbn [addcB toNatB]; destruct c.
      * destruct (incB_spec (BCons b yt) Hy) as [Hwfi Heqi]; split; [exact Hwfi | cbn [toNatB] in *; lia].
      * split; [exact Hy | cbn [toNatB]; lia].
  - contradiction.
  - destruct y as [| | b yt]; [| contradiction | ].
    + cbn [addcB toNatB]; destruct c.
      * destruct (incB_spec (BCons a xt) Hx) as [Hwfi Heqi]; split; [exact Hwfi | cbn [toNatB] in *; lia].
      * split; [exact Hx | cbn [toNatB]; lia].
    + cbn [addcB]; destruct Hx as [Hxt _]; destruct Hy as [Hyt _].
      set (r := add64c c a b).
      destruct (IH (hi128 r) yt Hxt Hyt) as [Hwfz Heqz].
      destruct (mkBCons_spec (lo128 r) (addcB (hi128 r) xt yt) Hwfz) as [Hwfm Heqm].
      pose proof (add64c_spec c a b) as Hlimb; fold r in Hlimb.
      split; [exact Hwfm | cbn [toNatB]; lia].
Qed.

Lemma addB_spec (x y : Big) :
  wfB x -> wfB y -> wfB (addB x y) /\ toNatB (addB x y) = toNatB x + toNatB y.
Proof.
  intros Hx Hy; unfold addB.
  destruct (addcB_spec x false y Hx Hy) as [Hwf Heq].
  split; [exact Hwf | lia].
Qed.

Lemma match_d0_nil {A : Type} (a : D64) (xt : Big) (u e : A) :
  wfB (BCons a xt) -> (match a, xt with D0, BNil => u | _, _ => e end) = e.
Proof.
  intros [_ Hnz]; destruct a; try reflexivity.
  destruct xt; [exfalso; exact (Hnz eq_refl eq_refl) | reflexivity | reflexivity].
Qed.

Lemma match_d01_nil (a : D64) (xt : Big) :
  wfB (BCons a xt) ->
  (toNatB (BCons a xt) < 2 ->
     (match a, xt with D0, BNil => BUnder | D1, BNil => BUnder | _, _ => dec2B (BCons a xt) end) = BUnder) /\
  (2 <= toNatB (BCons a xt) ->
     (match a, xt with D0, BNil => BUnder | D1, BNil => BUnder | _, _ => dec2B (BCons a xt) end) = dec2B (BCons a xt)).
Proof.
  intros [Hxt Hnz]; split; intro H.
  - destruct xt as [| | d2 xt2].
    + cbn [toNatB] in H; destruct a; cbn [d64ToNat] in H; try reflexivity; lia.
    + contradiction.
    + pose proof (wfB_cons_pos _ Hxt) as Hpos; cbn [toNatB] in H, Hpos; lia.
  - destruct a; try reflexivity;
      destruct xt as [| | d2 xt2]; try reflexivity; cbn [toNatB d64ToNat] in H; lia.
Qed.

Lemma subTryB_spec (x : Big) :
  forall (br : bool) (y : Big),
    wfB x -> wfB y ->
    let rhs := toNatB y + (if br then 1 else 0) in
    (toNatB x < rhs -> subTryB br x y = BUnder) /\
    (rhs <= toNatB x -> wfB (subTryB br x y) /\ toNatB (subTryB br x y) = toNatB x - rhs).
Proof.
  induction x as [| | a xt IH]; intros br y Hx Hy; cbn [ toNatB ].
  - destruct y as [| | b yt]; [| contradiction | ].
    + cbn [subTryB toNatB]; destruct br;
        (split; intro H; [lia | split; [exact I | reflexivity]]) ||
        (split; intro H; [reflexivity | lia]).
    + pose proof (wfB_cons_pos _ Hy) as Hpos; cbn [subTryB toNatB] in *; split; intro H; [reflexivity | lia].
  - contradiction.
  - pose proof (wfB_cons_pos _ Hx) as Hxpos.
    destruct y as [| | b yt]; [| contradiction | ].
    + cbn [subTryB toNatB]; destruct br.
      * rewrite (match_d0_nil a xt BUnder (dec1B (BCons a xt)) Hx).
        cbn [toNatB] in Hxpos; split; intro H; [lia | ].
        destruct (dec1B_spec (BCons a xt) Hx Hxpos) as [Hwfd Heqd]; cbn [toNatB] in Heqd.
        split; [exact Hwfd | lia].
      * split; intro H; [lia | split; [exact Hx | cbn [toNatB]; lia]].
    + cbn [subTryB toNatB]; destruct Hx as [Hxt _]; destruct Hy as [Hyt _].
      set (r := sub64b br a b).
      pose proof (sub64b_spec br a b) as Hlimb; fold r in Hlimb.
      pose proof (proj1 (d64_bound (lo128 r))) as Hlo.
      destruct (IH (hi128 r) yt Hxt Hyt) as [IHlt IHge]; cbn zeta in IHlt, IHge.
      split; intro H.
      * rewrite (IHlt ltac:(lia)); destruct (lo128 r); reflexivity.
      * destruct (IHge ltac:(lia)) as [Hwfz Heqz].
        destruct (combineTry_spec (lo128 r) _ Hwfz) as [Hwfc Heqc].
        split; [exact Hwfc | lia].
Qed.

Lemma subB_spec (x y : Big) :
  wfB x -> wfB y -> wfB (subB x y) /\ toNatB (subB x y) = toNatB x - toNatB y.
Proof.
  intros Hx Hy; unfold subB.
  destruct (subTryB_spec x false y Hx Hy) as [Hlt Hge]; cbn zeta in Hlt, Hge.
  destruct (Nat.lt_ge_cases (toNatB x) (toNatB y + 0)) as [H | H].
  - rewrite (Hlt H); split; [exact I | cbn [toNatB]; lia].
  - destruct (Hge H) as [Hwf Heq].
    destruct (subTryB false x y); [split; [exact I | cbn [toNatB] in *; lia] | contradiction | split; [exact Hwf | lia]].
Qed.

Lemma lebB_spec (x y : Big) :
  wfB x -> wfB y -> lebB x y = lebN (toNatB x) (toNatB y).
Proof.
  intros Hx Hy; unfold lebB, lebN.
  destruct (subTryB_spec y false x Hy Hx) as [Hlt Hge]; cbn zeta in Hlt, Hge.
  destruct (Nat.leb_spec0 (toNatB x) (toNatB y)) as [Hle | Hgt].
  - destruct (Hge ltac:(lia)) as [Hwf _].
    destruct (subTryB false y x); [reflexivity | contradiction | reflexivity].
  - rewrite (Hlt ltac:(lia)); reflexivity.
Qed.

Lemma combineTry_under (lo : D64) : combineTry lo BUnder = BUnder.
Proof. destruct lo; reflexivity. Qed.

Lemma sub2xTryB_spec (x : Big) :
  forall (br : C6) (y : Big),
    (br = C0 \/ br = C1 \/ br = C2) -> wfB x -> wfB y ->
    let rhs := 2 * toNatB y + valC6 br in
    (toNatB x < rhs -> sub2xTryB br x y = BUnder) /\
    (rhs <= toNatB x -> wfB (sub2xTryB br x y) /\ toNatB (sub2xTryB br x y) = toNatB x - rhs).
Proof.
  induction x as [| | a xt IH]; intros br y Hbr Hx Hy.
  - destruct y as [| | b yt]; [| contradiction | ].
    + cbn [sub2xTryB toNatB]; destruct Hbr as [-> | [-> | ->]]; cbn [valC6];
        ((split; intro H; [lia | split; [exact I | reflexivity]]) ||
         (split; intro H; [reflexivity | lia])).
    + pose proof (wfB_cons_pos _ Hy) as Hpos; cbn [sub2xTryB toNatB] in *; split; intro H; [reflexivity | lia].
  - contradiction.
  - pose proof (wfB_cons_pos _ Hx) as Hxpos.
    destruct y as [| | b yt]; [| contradiction | ].
    + cbn [sub2xTryB]; replace (2 * toNatB BNil) with 0 by reflexivity.
      destruct Hbr as [-> | [-> | ->]]; cbn [valC6].
      * split; intro H; [lia | split; [exact Hx | lia]].
      * rewrite (match_d0_nil a xt BUnder (dec1B (BCons a xt)) Hx).
        split; intro H; [lia | ].
        destruct (dec1B_spec _ Hx Hxpos) as [Hwfd Heqd]; split; [exact Hwfd | lia].
      * destruct (match_d01_nil a xt Hx) as [Hm1 Hm2].
        split; intro H; [exact (Hm1 ltac:(lia)) | ].
        rewrite (Hm2 ltac:(lia)); destruct (dec2B_spec _ Hx ltac:(lia)) as [Hwfd Heqd].
        split; [exact Hwfd | lia].
    + rewrite (sub2xTryB_cons br a b xt yt Hbr).
      destruct Hx as [Hxt _]; destruct Hy as [Hyt _].
      destruct (sub2x_limb_spec br a b Hbr) as [Hlimb Hhi].
      set (r := sub2x64 br a b) in *.
      pose proof (proj1 (d64_bound (lo256 r))) as Hlo.
      destruct (IH (hi256 r) yt Hhi Hxt Hyt) as [IHlt IHge]; cbn zeta in IHlt, IHge.
      cbn [toNatB]; split; intro H.
      * rewrite (IHlt ltac:(lia)), combineTry_under; reflexivity.
      * destruct (IHge ltac:(lia)) as [Hwfz Heqz].
        destruct (combineTry_spec (lo256 r) _ Hwfz) as [Hwfc Heqc].
        split; [exact Hwfc | lia].
Qed.

Lemma sub2xB_spec (x y : Big) :
  wfB x -> wfB y -> wfB (sub2xB x y) /\ toNatB (sub2xB x y) = toNatB x - 2 * toNatB y.
Proof.
  intros Hx Hy; unfold sub2xB.
  destruct (sub2xTryB_spec x C0 y (or_introl eq_refl) Hx Hy) as [Hlt Hge]; cbn [valC6] in Hlt, Hge.
  destruct (Nat.lt_ge_cases (toNatB x) (2 * toNatB y + 0)) as [H | H].
  - rewrite (Hlt H); split; [exact I | cbn [toNatB]; lia].
  - destruct (Hge H) as [Hwf Heq].
    destruct (sub2xTryB C0 x y); [split; [exact I | cbn [toNatB] in *; lia] | contradiction | split; [exact Hwf | lia]].
Qed.

Lemma sub2xTryB_zero_spec (x y : Big) :
  wfB x -> wfB y ->
  isZeroB (sub2xTryB C0 x y) = isZeroN (toNatB x - 2 * toNatB y) /\
  (isZeroB (sub2xTryB C0 x y) = false ->
     wfB (sub2xTryB C0 x y) /\ toNatB (sub2xTryB C0 x y) = toNatB x - 2 * toNatB y).
Proof.
  intros Hx Hy.
  destruct (sub2xTryB_spec x C0 y (or_introl eq_refl) Hx Hy) as [Hlt Hge]; cbn [valC6] in Hlt, Hge.
  destruct (Nat.lt_ge_cases (toNatB x) (2 * toNatB y + 0)) as [H | H].
  - rewrite (Hlt H); replace (toNatB x - 2 * toNatB y) with 0 by lia.
    split; [reflexivity | discriminate].
  - destruct (Hge H) as [Hwf Heq].
    rewrite (isZeroB_spec _ Hwf); replace (2 * toNatB y + 0) with (2 * toNatB y) in Heq by lia.
    rewrite Heq; split; [reflexivity | intro; split; [exact Hwf | reflexivity]].
Qed.

Lemma subHalfTryB_spec (x : Big) :
  forall (br : bool) (b : Big),
    wfB x -> wfB b ->
    let rhs := halfN (toNatB b) + (if br then 1 else 0) in
    (toNatB x < rhs -> subHalfTryB br x b = BUnder) /\
    (rhs <= toNatB x -> wfB (subHalfTryB br x b) /\ toNatB (subHalfTryB br x b) = toNatB x - rhs).
Proof.
  induction x as [| | a xt IH]; intros br b Hx Hb.
  - destruct b as [| | d0 bt]; [| contradiction | ].
    + cbn [subHalfTryB toNatB halfN]; destruct br;
        ((split; intro H; [lia | split; [exact I | reflexivity]]) ||
         (split; intro H; [reflexivity | lia])).
    + cbn zeta; change (toNatB BNil) with 0; cbn [subHalfTryB].
      destruct Hb as [Hbt _].
      destruct bt as [| | d2 bt2]; [| contradiction | ].
      * destruct d0; cbn [toNatB Nat.add Nat.mul d64ToNat halfN];
          (destruct br;
            ((split; intro H; [lia | split; [exact I | reflexivity]]) ||
             (split; intro H; [reflexivity | lia]))).
      * pose proof (wfB_cons_pos (BCons d2 bt2) Hbt) as Hpos; cbn [wfB_cons_pos] in Hpos.
        pose proof (halfN_cons d0 (BCons d2 bt2)) as Hhc.
        pose proof (halfN_evenN_spec (toNatB (BCons d2 bt2))) as Hev.
        pose proof (oddB_spec (BCons d2 bt2)) as Hodd; unfold oddN in Hodd.
        assert (Hge32 : 32 <= halfN (toNatB (BCons d0 (BCons d2 bt2)))).
        { destruct (evenN (toNatB (BCons d2 bt2))); cbn [negb] in Hodd; rewrite Hodd in Hhc; lia. }
        split; intro H; [reflexivity | lia].
  - contradiction.
  - pose proof (wfB_cons_pos _ Hx) as Hxpos.
    destruct b as [| | d0 bt]; [| contradiction | ].
    + cbn [subHalfTryB toNatB halfN]; destruct br.
      * rewrite (match_d0_nil a xt BUnder (dec1B (BCons a xt)) Hx).
        cbn [toNatB] in Hxpos; split; intro H; [lia | ].
        destruct (dec1B_spec _ Hx Hxpos) as [Hwfd Heqd]; cbn [toNatB] in Heqd; split; [exact Hwfd | lia].
      * split; intro H; [lia | split; [exact Hx | cbn [toNatB]; lia]].
    + rewrite subHalfTryB_cons, halfN_cons.
      destruct Hx as [Hxt _]; destruct Hb as [Hbt _].
      pose proof (subHalf_limb_spec br (oddB bt) a d0) as Hlimb.
      set (r := subHalf64 br (oddB bt) a d0) in *.
      pose proof (proj1 (d64_bound (lo128 r))) as Hlo.
      destruct (IH (hi128 r) bt Hxt Hbt) as [IHlt IHge]; cbn zeta in IHlt, IHge.
      cbn [toNatB]; split; intro H.
      * rewrite (IHlt ltac:(lia)), combineTry_under; reflexivity.
      * destruct (IHge ltac:(lia)) as [Hwfz Heqz].
        destruct (combineTry_spec (lo128 r) _ Hwfz) as [Hwfc Heqc].
        split; [exact Hwfc | lia].
Qed.

Lemma subHalfTryB_zero_spec (br : bool) (x b : Big) :
  wfB x -> wfB b ->
  isZeroB (subHalfTryB br x b) = isZeroN (toNatB x - (halfN (toNatB b) + (if br then 1 else 0))) /\
  (isZeroB (subHalfTryB br x b) = false ->
     wfB (subHalfTryB br x b) /\
     toNatB (subHalfTryB br x b) = toNatB x - (halfN (toNatB b) + (if br then 1 else 0))).
Proof.
  intros Hx Hb.
  destruct (subHalfTryB_spec x br b Hx Hb) as [Hlt Hge]; cbn zeta in Hlt, Hge.
  set (rhs := halfN (toNatB b) + (if br then 1 else 0)) in *.
  destruct (Nat.lt_ge_cases (toNatB x) rhs) as [H | H].
  - rewrite (Hlt H); replace (toNatB x - rhs) with 0 by lia.
    split; [reflexivity | discriminate].
  - destruct (Hge H) as [Hwf Heq].
    rewrite (isZeroB_spec _ Hwf), Heq; split; [reflexivity | intro; split; [exact Hwf | reflexivity]].
Qed.

Lemma mul3addcB_spec (x : Big) :
  forall (c : C6),
    wfB x -> wfB (mul3addcB c x) /\ toNatB (mul3addcB c x) = mul3addcN (valC6 c) (toNatB x).
Proof.
  induction x as [| | a xt IH]; intros c Hx; unfold mul3addcN in *.
  - cbn [mul3addcB toNatB]; destruct c; cbn [valC6];
      [split; [exact I | reflexivity] | (split; [split; [exact I | discriminate] | reflexivity])..].
  - contradiction.
  - rewrite mul3addcB_cons; destruct Hx as [Hxt _].
    set (r := mul3_64 c a).
    destruct (IH (hi256 r) Hxt) as [Hwfz Heqz].
    destruct (mkBCons_spec (lo256 r) _ Hwfz) as [Hwfm Heqm].
    pose proof (mul3_limb_spec c a) as Hlimb; fold r in Hlimb.
    split; [exact Hwfm | cbn [toNatB]; lia].
Qed.

Lemma mul3halfB_spec (b : Big) :
  forall (c : C6),
    wfB b -> wfB (mul3halfB c b) /\ toNatB (mul3halfB c b) = mul3addcN (valC6 c) (halfN (toNatB b)).
Proof.
  induction b as [| | d0 bt IH]; intros c Hb; unfold mul3addcN in *.
  - cbn [mul3halfB toNatB halfN]; destruct c; cbn [valC6];
      [split; [exact I | reflexivity] | (split; [split; [exact I | discriminate] | reflexivity])..].
  - contradiction.
  - rewrite mul3halfB_cons, halfN_cons; destruct Hb as [Hbt _].
    set (r := mul3half_64 (oddB bt) c d0).
    destruct (IH (hi256 r) Hbt) as [Hwfz Heqz].
    destruct (mkBCons_spec (lo256 r) _ Hwfz) as [Hwfm Heqm].
    pose proof (mul3half_limb_spec (oddB bt) c d0) as Hlimb; fold r in Hlimb.
    split; [exact Hwfm | lia].
Qed.

Lemma div2B_spec (x : Big) :
  wfB x -> wfB (div2B x) /\ toNatB (div2B x) = halfN (toNatB x).
Proof.
  induction x as [| | a xt IH]; intro Hx.
  - split; [exact I | reflexivity].
  - contradiction.
  - rewrite div2B_cons, halfN_cons; destruct Hx as [Hxt _].
    destruct (IH Hxt) as [Hwfz Heqz].
    destruct (mkBCons_spec (div2_64 (oddB xt) a) _ Hwfz) as [Hwfm Heqm].
    pose proof (div2_limb_spec (oddB xt) a) as Hlimb.
    split; [exact Hwfm | lia].
Qed.

Lemma eqbB_spec (x : Big) :
  forall (y : Big), wfB x -> wfB y -> eqbB x y = eqbN (toNatB x) (toNatB y).
Proof.
  induction x as [| | a xt IH]; intros y Hx Hy; unfold eqbN in *.
  - destruct y as [| | b yt]; [reflexivity | contradiction | ].
    pose proof (wfB_cons_pos _ Hy) as Hpos; cbn [eqbB toNatB] in *.
    symmetry; apply Nat.eqb_neq; lia.
  - contradiction.
  - pose proof (wfB_cons_pos _ Hx) as Hxpos.
    destruct y as [| | b yt]; [| contradiction | ].
    + cbn [eqbB toNatB] in *; symmetry; apply Nat.eqb_neq; lia.
    + cbn [eqbB toNatB].
      replace (match sub64b false a b with P0 => eqbB xt yt | _ => false end)
        with (if Nat.eqb (d64ToNat a) (d64ToNat b) then eqbB xt yt else false)
        by (rewrite <- eqb64_spec; destruct (sub64b false a b); reflexivity).
      destruct Hx as [Hxt _]; destruct Hy as [Hyt _].
      pose proof (proj1 (d64_bound a)) as Ha; pose proof (proj1 (d64_bound b)) as Hb.
      destruct (Nat.eqb_spec (d64ToNat a) (d64ToNat b)) as [Hab | Hab].
      * rewrite (IH yt Hxt Hyt).
        destruct (Nat.eqb_spec (toNatB xt) (toNatB yt)) as [Hxy | Hxy];
          symmetry; [apply Nat.eqb_eq; lia | apply Nat.eqb_neq; lia].
      * symmetry; apply Nat.eqb_neq; lia.
Qed.

(** ** 8. Structural Simulation Between [HybState] ([Big]) and [HybStateN] ([nat]) *)

Lemma wfToks_app (xs ys : list Tok) :
  wfToks xs -> wfToks ys -> wfToks (xs ++ ys).
Proof.
  induction xs as [| x xs IH]; intros Hx Hy; [exact Hy | ].
  destruct Hx as [Hx0 Hxs]; split; [exact Hx0 | exact (IH Hxs Hy)].
Qed.

Lemma evalToks_app (xs ys : list Tok) :
  evalToks (xs ++ ys) = evalToks xs ++ evalToks ys.
Proof.
  induction xs as [| x xs IH]; cbn [List.app evalToks]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma wfToks_rev (xs : list Tok) :
  wfToks xs -> wfToks (List.rev xs).
Proof.
  induction xs as [| x xs IH]; intro Hx; [exact I | ].
  destruct Hx as [Hx0 Hxs]; cbn [List.rev].
  apply wfToks_app; [exact (IH Hxs) | split; [exact Hx0 | exact I]].
Qed.

Lemma evalToks_rev (xs : list Tok) :
  evalToks (List.rev xs) = List.rev (evalToks xs).
Proof.
  induction xs as [| x xs IH]; cbn [List.rev evalToks]; [reflexivity | ].
  rewrite evalToks_app, IH; reflexivity.
Qed.

Lemma runCleanLoop_sim (steps : nat) :
  forall (b0 : Big) (lt : LStack) (isC1 : bool) (c0 : Big) (rt : RStack),
    wfB b0 -> wfL lt -> wfB c0 -> wfR rt ->
    wfHyb (runCleanLoop steps b0 lt isC1 c0 rt) /\
    evalHyb (runCleanLoop steps b0 lt isC1 c0 rt) =
      runCleanLoopN steps (toNatB b0) (evalL lt) isC1 (toNatB c0) (evalR rt).
Proof.
  induction steps as [| steps' IH]; intros b0 lt isC1 c0 rt Hb0 Hlt Hc0 Hrt.
  - split; [split; [split; [exact Hb0 | exact Hlt] | split; [exact Hc0 | exact Hrt]] | reflexivity].
  - assert (Hexit : wfHyb (HGen QF true [TokW B3] (LC b0 lt) [] (RC isC1 c0 rt)) /\
                    evalHyb (HGen QF true [TokW B3] (LC b0 lt) [] (RC isC1 c0 rt)) =
                      HGenN QF true [TokWN 3] (LCN (toNatB b0) (evalL lt)) [] (RCN isC1 (toNatB c0) (evalR rt))).
    { split; [repeat split; auto; try discriminate | reflexivity]. }
    cbn [runCleanLoop runCleanLoopN].
    destruct (sub2xTryB_zero_spec b0 c0 Hb0 Hc0) as [Hz Hdiff].
    rewrite Hz.
    destruct (isZeroN (toNatB b0 - 2 * toNatB c0)).
    + destruct lt as [| b1 lt2 | t1 lt2]; [exact Hexit | | exact Hexit].
      destruct Hlt as [Hb1 Hlt2].
      cbn [evalL].
      destruct (subSmall3B_spec b1 Hb1) as [Hwf_nb1 Heq_nb1].
      rewrite (isZeroB_spec _ Hwf_nb1), Heq_nb1.
      destruct (isZeroN (toNatB b1 - 3)); [exact Hexit | ].
      rewrite (evenB_spec b0).
      destruct (evenN (toNatB b0)).
      * destruct (subHalfTryB_zero_spec false c0 b0 Hc0 Hb0) as [Hzh Hnzh].
        replace (halfN (toNatB b0) + 0) with (halfN (toNatB b0)) in Hzh, Hnzh by lia.
        rewrite Hzh.
        destruct (isZeroN (toNatB c0 - halfN (toNatB b0))); [exact Hexit | ].
        destruct (Hnzh Hzh) as [Hwf_nc0 Heq_nc0].
        destruct (mul3halfB_spec b0 C3 Hb0) as [Hwf_m Heq_m]; cbn [valC6] in Heq_m.
        destruct (IH _ lt2 true _ (RC isC1 _ rt) Hwf_nb1 Hlt2 Hwf_m (conj Hwf_nc0 Hrt)) as [Hwf_r Heq_r].
        rewrite Heq_r, Heq_nb1, Heq_m; cbn [evalR]; rewrite Heq_nc0.
        split; [exact Hwf_r | reflexivity].
      * destruct (subHalfTryB_zero_spec true c0 b0 Hc0 Hb0) as [Hzh Hnzh].
        rewrite Hzh.
        destruct (isZeroN (toNatB c0 - (halfN (toNatB b0) + 1))); [exact Hexit | ].
        destruct (Hnzh Hzh) as [Hwf_nc0 Heq_nc0].
        destruct (mul3halfB_spec b0 C5 Hb0) as [Hwf_m Heq_m]; cbn [valC6] in Heq_m.
        destruct (IH _ lt2 false _ (RC isC1 _ rt) Hwf_nb1 Hlt2 Hwf_m (conj Hwf_nc0 Hrt)) as [Hwf_r Heq_r].
        rewrite Heq_r, Heq_nb1, Heq_m; cbn [evalR]; rewrite Heq_nc0.
        split; [exact Hwf_r | reflexivity].
    + destruct (Hdiff Hz) as [Hwf_diff Heq_diff].
      destruct isC1.
      * destruct (subSmall2B_spec _ Hwf_diff) as [Hwf_nb0 Heq_nb0].
        rewrite (isZeroB_spec _ Hwf_nb0), Heq_nb0, Heq_diff.
        destruct (isZeroN (toNatB b0 - 2 * toNatB c0 - 2)); [exact Hexit | ].
        destruct rt as [| t1 c1 rt2 | tr rt2]; [exact Hexit | | exact Hexit].
        destruct Hrt as [Hc1 Hrt2]; cbn [evalR].
        destruct (subSmall2B_spec c1 Hc1) as [Hwf_nc1 Heq_nc1].
        rewrite (isZeroB_spec _ Hwf_nc1), Heq_nc1.
        destruct (isZeroN (toNatB c1 - 2)); [exact Hexit | ].
        destruct (mul3addcB_spec c0 C4 Hc0) as [Hwf_m Heq_m]; cbn [valC6] in Heq_m.
        destruct (IH _ (LC _ lt) t1 _ rt2 Hwf_m (conj Hwf_nb0 Hlt) Hwf_nc1 Hrt2) as [Hwf_r Heq_r].
        rewrite Heq_r, Heq_m; cbn [evalL]; rewrite Heq_nb0, Heq_diff, Heq_nc1.
        split; [exact Hwf_r | reflexivity].
      * rewrite (isZeroB_spec c0 Hc0).
        destruct (isZeroN (toNatB c0)); [exact Hexit | ].
        destruct rt as [| t1 c1 rt2 | tr rt2]; [exact Hexit | | exact Hexit].
        destruct Hrt as [Hc1 Hrt2]; cbn [evalR].
        destruct (subSmall1B_spec c1 Hc1) as [Hwf_nc1 Heq_nc1].
        rewrite (isZeroB_spec _ Hwf_nc1), Heq_nc1.
        destruct (isZeroN (toNatB c1 - 1)); [exact Hexit | ].
        destruct (mul3addcB_spec c0 C1 Hc0) as [Hwf_m Heq_m]; cbn [valC6] in Heq_m.
        destruct (IH _ (LC _ lt) t1 _ rt2 Hwf_m (conj Hwf_diff Hlt) Hwf_nc1 Hrt2) as [Hwf_r Heq_r].
        rewrite Heq_r, Heq_m; cbn [evalL]; rewrite Heq_diff, Heq_nc1.
        split; [exact Hwf_r | reflexivity].
Qed.

Lemma runCleanChunk_sim (kc4 : nat) (sL : LStack) (sR : RStack) :
  wfL sL -> wfR sR ->
  wfHyb (runCleanChunk kc4 sL sR) /\
  evalHyb (runCleanChunk kc4 sL sR) = runCleanChunkN kc4 (evalL sL) (evalR sR).
Proof.
  intros HsL HsR; pose proof wfB_B3.
  destruct sL as [| b0 lt | tL lt];
    try (cbn [runCleanChunk evalL runCleanChunkN wfHyb wfToks wfTok]; split; [tauto | reflexivity]).
  destruct sR as [| isC1 c0 rt | tR rt];
    try (cbn [runCleanChunk evalL evalR runCleanChunkN wfHyb wfToks wfTok]; split; [tauto | reflexivity]).
  destruct HsL as [Hb0 Hlt]; destruct HsR as [Hc0 Hrt].
  exact (runCleanLoop_sim kc4 b0 lt isC1 c0 rt Hb0 Hlt Hc0 Hrt).
Qed.

Lemma pushTok_sim (t : Tok) (ts : list Tok) :
  wfTok t -> wfToks ts ->
  wfToks (pushTok t ts) /\ evalToks (pushTok t ts) = pushTokN (evalTok t) (evalToks ts).
Proof.
  intros Ht Hts; destruct t as [[| | d a] | [| | d a] | [| | d a]];
    try contradiction;
    try (cbn [pushTok evalTok toNatB pushTokN]; split; [exact Hts | reflexivity]);
    pose proof (wfB_cons_pos (BCons d a) Ht) as Hpos;
    cbn [pushTok evalTok];
    destruct (toNatB (BCons d a)) as [| ma] eqn:Hma; try lia;
    destruct ts as [| [b | b | b] rest];
    try (cbn [wfToks evalToks evalTok pushTokN]; rewrite ?Hma; split; [split; [exact Ht | exact Hts] | reflexivity]);
    destruct Hts as [Hb Hrest];
    destruct (addB_spec (BCons d a) b Ht Hb) as [Hwfa Heqa];
    cbn [wfToks wfTok evalToks evalTok pushTokN];
    rewrite Heqa, Hma; (split; [split; [exact Hwfa | exact Hrest] | reflexivity]).
Qed.

Lemma pushTokBack_sim (ts : list Tok) (t : Tok) :
  wfToks ts -> wfTok t ->
  wfToks (pushTokBack ts t) /\ evalToks (pushTokBack ts t) = pushTokBackN (evalToks ts) (evalTok t).
Proof.
  induction ts as [| t0 [| t1 rest2] IH]; intros Hts Ht.
  - cbn [pushTokBack evalToks pushTokBackN]; exact (pushTok_sim t [] Ht I).
  - destruct Hts as [Ht0 _]; cbn [pushTokBack evalToks pushTokBackN].
    destruct (pushTok_sim t [] Ht I) as [Hwf1 Heq1].
    destruct (pushTok_sim t0 (pushTok t []) Ht0 Hwf1) as [Hwf2 Heq2].
    rewrite Heq2, Heq1; split; [exact Hwf2 | reflexivity].
  - destruct Hts as [Ht0 Hrest].
    destruct (IH Hrest Ht) as [Hwf Heq].
    change (pushTokBack (t0 :: t1 :: rest2) t) with (t0 :: pushTokBack (t1 :: rest2) t).
    change (evalToks (t0 :: t1 :: rest2)) with (evalTok t0 :: evalTok t1 :: evalToks rest2).
    change (pushTokBackN (evalTok t0 :: evalTok t1 :: evalToks rest2) (evalTok t))
      with (evalTok t0 :: pushTokBackN (evalTok t1 :: evalToks rest2) (evalTok t)).
    cbn [wfToks evalToks] in *; rewrite Heq.
    split; [split; [exact Ht0 | exact Hwf] | reflexivity].
Qed.

Lemma stripEndZ_sim (ts : list Tok) :
  wfToks ts ->
  wfToks (stripEndZ ts) /\ evalToks (stripEndZ ts) = stripEndZN (evalToks ts).
Proof.
  induction ts as [| t rest IH]; intro Hts.
  - split; [exact I | reflexivity].
  - destruct Hts as [Ht Hrest]; destruct (IH Hrest) as [Hwfr Heqr].
    cbn [stripEndZ evalToks stripEndZN]; rewrite <- Heqr.
    destruct (stripEndZ rest) as [| u urest].
    + cbn [evalToks]; destruct t as [n | n | n]; cbn [wfToks evalToks evalTok];
        [split; [exact I | reflexivity] | split; [split; [exact Ht | exact I] | reflexivity]..].
    + cbn [wfToks evalToks]; split; [split; [exact Ht | exact Hwfr] | reflexivity].
Qed.

Lemma needPull_sim (ts : list Tok) :
  needPull ts = needPullN (evalToks ts).
Proof.
  destruct ts as [| ? [| ? [| ? [| ? [| ? ?]]]]]; reflexivity.
Qed.

Lemma pullOneL_sim (bL : list Tok) (rL : LStack) :
  wfToks bL -> wfL rL ->
  wfToks (fst (pullOneL bL rL)) /\ wfL (snd (pullOneL bL rL)) /\
  evalToks (fst (pullOneL bL rL)) = fst (pullOneLN (evalToks bL) (evalL rL)) /\
  evalL (snd (pullOneL bL rL)) = snd (pullOneLN (evalToks bL) (evalL rL)).
Proof.
  intros HbL HrL; destruct rL as [| b tl | t tl]; cbn [pullOneL evalL pullOneLN fst snd].
  - destruct (stripEndZ_sim bL HbL) as [Hwf Heq]; repeat split; auto.
  - destruct HrL as [Hb Htl].
    destruct (pushTokBack_sim bL (TokZ B1) HbL wfB_B1) as [Hwf1 Heq1].
    destruct (pushTokBack_sim _ (TokW b) Hwf1 Hb) as [Hwf2 Heq2].
    rewrite Heq2, Heq1; repeat split; auto.
  - destruct HrL as [Ht Htl].
    destruct (pushTokBack_sim bL t HbL Ht) as [Hwf1 Heq1].
    rewrite Heq1; repeat split; auto.
Qed.

Lemma pullOneR_sim (bR : list Tok) (rR : RStack) :
  wfToks bR -> wfR rR ->
  wfToks (fst (pullOneR bR rR)) /\ wfR (snd (pullOneR bR rR)) /\
  evalToks (fst (pullOneR bR rR)) = fst (pullOneRN (evalToks bR) (evalR rR)) /\
  evalR (snd (pullOneR bR rR)) = snd (pullOneRN (evalToks bR) (evalR rR)).
Proof.
  intros HbR HrR; destruct rR as [| [|] c tl | t tl]; cbn [pullOneR evalR pullOneRN fst snd].
  - destruct (stripEndZ_sim bR HbR) as [Hwf Heq]; repeat split; auto.
  - destruct HrR as [Hc Htl].
    destruct (pushTokBack_sim bR (TokW c) HbR Hc) as [Hwf1 Heq1].
    destruct (pushTokBack_sim _ (TokO B1) Hwf1 wfB_B1) as [Hwf2 Heq2].
    rewrite Heq2, Heq1; repeat split; auto.
  - destruct HrR as [Hc Htl].
    destruct (pushTokBack_sim bR (TokW c) HbR Hc) as [Hwf1 Heq1].
    destruct (pushTokBack_sim _ (TokZ B1) Hwf1 wfB_B1) as [Hwf2 Heq2].
    rewrite Heq2, Heq1; repeat split; auto.
  - destruct HrR as [Ht Htl].
    destruct (pushTokBack_sim bR t HbR Ht) as [Hwf1 Heq1].
    rewrite Heq1; repeat split; auto.
Qed.

Lemma pullStepL_sim (p : list Tok * LStack) :
  wfToks (fst p) -> wfL (snd p) ->
  wfToks (fst (pullStepL p)) /\ wfL (snd (pullStepL p)) /\
  evalToks (fst (pullStepL p)) = fst (pullStepLN (evalToks (fst p), evalL (snd p))) /\
  evalL (snd (pullStepL p)) = snd (pullStepLN (evalToks (fst p), evalL (snd p))).
Proof.
  intros HbL HrL; unfold pullStepL, pullStepLN; cbn [fst snd].
  rewrite (needPull_sim (fst p)).
  destruct (needPullN (evalToks (fst p))); [apply pullOneL_sim; assumption | repeat split; auto].
Qed.

Lemma pullStepR_sim (p : list Tok * RStack) :
  wfToks (fst p) -> wfR (snd p) ->
  wfToks (fst (pullStepR p)) /\ wfR (snd (pullStepR p)) /\
  evalToks (fst (pullStepR p)) = fst (pullStepRN (evalToks (fst p), evalR (snd p))) /\
  evalR (snd (pullStepR p)) = snd (pullStepRN (evalToks (fst p), evalR (snd p))).
Proof.
  intros HbR HrR; unfold pullStepR, pullStepRN; cbn [fst snd].
  rewrite (needPull_sim (fst p)).
  destruct (needPullN (evalToks (fst p))); [apply pullOneR_sim; assumption | repeat split; auto].
Qed.

Lemma ensureL_sim (bL : list Tok) (rL : LStack) :
  wfToks bL -> wfL rL ->
  wfToks (fst (ensureL bL rL)) /\ wfL (snd (ensureL bL rL)) /\
  evalToks (fst (ensureL bL rL)) = fst (ensureLN (evalToks bL) (evalL rL)) /\
  evalL (snd (ensureL bL rL)) = snd (ensureLN (evalToks bL) (evalL rL)).
Proof.
  intros HbL HrL; unfold ensureL, ensureLN.
  destruct (pullStepL_sim (bL, rL) HbL HrL) as [H1a [H1b [E1a E1b]]].
  destruct (pullStepL_sim _ H1a H1b) as [H2a [H2b [E2a E2b]]].
  destruct (pullStepL_sim _ H2a H2b) as [H3a [H3b [E3a E3b]]].
  destruct (pullStepL_sim _ H3a H3b) as [H4a [H4b [E4a E4b]]].
  cbn [fst snd] in E1a, E1b.
  rewrite E1a, E1b in E2a, E2b; rewrite <- surjective_pairing in E2a, E2b.
  rewrite E2a, E2b in E3a, E3b; rewrite <- surjective_pairing in E3a, E3b.
  rewrite E3a, E3b in E4a, E4b; rewrite <- surjective_pairing in E4a, E4b.
  repeat split; assumption.
Qed.

Lemma ensureR_sim (bR : list Tok) (rR : RStack) :
  wfToks bR -> wfR rR ->
  wfToks (fst (ensureR bR rR)) /\ wfR (snd (ensureR bR rR)) /\
  evalToks (fst (ensureR bR rR)) = fst (ensureRN (evalToks bR) (evalR rR)) /\
  evalR (snd (ensureR bR rR)) = snd (ensureRN (evalToks bR) (evalR rR)).
Proof.
  intros HbR HrR; unfold ensureR, ensureRN.
  destruct (pullStepR_sim (bR, rR) HbR HrR) as [H1a [H1b [E1a E1b]]].
  destruct (pullStepR_sim _ H1a H1b) as [H2a [H2b [E2a E2b]]].
  destruct (pullStepR_sim _ H2a H2b) as [H3a [H3b [E3a E3b]]].
  destruct (pullStepR_sim _ H3a H3b) as [H4a [H4b [E4a E4b]]].
  cbn [fst snd] in E1a, E1b.
  rewrite E1a, E1b in E2a, E2b; rewrite <- surjective_pairing in E2a, E2b.
  rewrite E2a, E2b in E3a, E3b; rewrite <- surjective_pairing in E3a, E3b.
  rewrite E3a, E3b in E4a, E4b; rewrite <- surjective_pairing in E4a, E4b.
  repeat split; assumption.
Qed.

Lemma foldPackL_sim_aux (n : nat) :
  forall (revTs : list Tok) (rL : LStack),
    List.length revTs <= n -> wfToks revTs -> wfL rL ->
    wfL (foldPackL revTs rL) /\ evalL (foldPackL revTs rL) = foldPackLN (evalToks revTs) (evalL rL).
Proof.
  induction n as [| n IH]; intros [| t revRest] rL Hlen Hts HrL; cbn [List.length] in Hlen.
  - split; [exact HrL | reflexivity].
  - lia.
  - split; [exact HrL | reflexivity].
  - destruct Hts as [Ht Hrest]; cbn [foldPackL evalToks foldPackLN].
    destruct t as [z | o | b]; cbn [evalTok].
    + rewrite (isOneB_spec z Ht).
      destruct (isOneN (toNatB z)).
      * destruct rL as [| b' tl | [z' | o' | b] tl];
          try (apply IH; [lia | exact Hrest | split; [exact Ht | exact HrL]]).
        destruct HrL as [Hb Htl]; cbn [evalL evalTok].
        rewrite (isZeroB_spec b Hb).
        destruct (negb (isZeroN (toNatB b)));
          apply IH; [lia | exact Hrest | split; [exact Hb | exact Htl] |
                     lia | exact Hrest | split; [exact Ht | split; [exact Hb | exact Htl]]].
      * apply IH; [lia | exact Hrest | split; [exact Ht | exact HrL]].
    + apply IH; [lia | exact Hrest | split; [exact Ht | exact HrL]].
    + rewrite (isZeroB_spec b Ht).
      destruct (negb (isZeroN (toNatB b))).
      * destruct revRest as [| [z | o' | b'] revRest2];
          try (apply IH; [cbn [List.length] in Hlen |- *; lia | exact Hrest | split; [exact Ht | exact HrL]]).
        destruct Hrest as [Hz Hrest2]; cbn [evalToks evalTok].
        rewrite (isOneB_spec z Hz).
        destruct (isOneN (toNatB z)).
        { apply IH; [cbn [List.length] in Hlen |- *; lia | exact Hrest2 | split; [exact Ht | exact HrL]]. }
        { apply IH; [cbn [List.length] in Hlen |- *; lia | split; [exact Hz | exact Hrest2] | split; [exact Ht | exact HrL]]. }
      * apply IH; [lia | exact Hrest | split; [exact Ht | exact HrL]].
Qed.

Lemma foldPackL_sim (revTs : list Tok) (rL : LStack) :
  wfToks revTs -> wfL rL ->
  wfL (foldPackL revTs rL) /\ evalL (foldPackL revTs rL) = foldPackLN (evalToks revTs) (evalL rL).
Proof.
  exact (foldPackL_sim_aux (List.length revTs) revTs rL (Nat.le_refl _)).
Qed.

Lemma foldPackR_sim_aux (n : nat) :
  forall (revTs : list Tok) (rR : RStack),
    List.length revTs <= n -> wfToks revTs -> wfR rR ->
    wfR (foldPackR revTs rR) /\ evalR (foldPackR revTs rR) = foldPackRN (evalToks revTs) (evalR rR).
Proof.
  induction n as [| n IH]; intros [| t revRest] rR Hlen Hts HrR; cbn [List.length] in Hlen.
  - split; [exact HrR | reflexivity].
  - lia.
  - split; [exact HrR | reflexivity].
  - destruct Hts as [Ht Hrest]; cbn [foldPackR evalToks foldPackRN].
    destruct t as [z | o | c]; cbn [evalTok].
    + rewrite (isOneB_spec z Ht).
      destruct (isOneN (toNatB z)).
      * destruct revRest as [| [z' | o' | c] revRest2];
          try (apply IH; [cbn [List.length] in Hlen |- *; lia | exact Hrest | split; [exact wfB_B0 | exact HrR]]).
        destruct Hrest as [Hc Hrest2]; cbn [evalToks evalTok].
        rewrite (isZeroB_spec c Hc).
        destruct (negb (isZeroN (toNatB c))).
        { apply IH; [cbn [List.length] in Hlen |- *; lia | exact Hrest2 | split; [exact Hc | exact HrR]]. }
        { apply IH; [cbn [List.length] in Hlen |- *; lia | split; [exact Hc | exact Hrest2] | split; [exact wfB_B0 | exact HrR]]. }
      * apply IH; [lia | exact Hrest | split; [exact Ht | exact HrR]].
    + rewrite (isOneB_spec o Ht).
      destruct (isOneN (toNatB o)).
      * destruct revRest as [| [z' | o' | c] revRest2];
          try (apply IH; [cbn [List.length] in Hlen |- *; lia | exact Hrest | split; [exact wfB_B0 | exact HrR]]).
        destruct Hrest as [Hc Hrest2]; cbn [evalToks evalTok].
        rewrite (isZeroB_spec c Hc).
        destruct (negb (isZeroN (toNatB c))).
        { apply IH; [cbn [List.length] in Hlen |- *; lia | exact Hrest2 | split; [exact Hc | exact HrR]]. }
        { apply IH; [cbn [List.length] in Hlen |- *; lia | split; [exact Hc | exact Hrest2] | split; [exact wfB_B0 | exact HrR]]. }
      * apply IH; [lia | exact Hrest | split; [exact Ht | exact HrR]].
    + rewrite (isZeroB_spec c Ht).
      destruct (negb (isZeroN (toNatB c))).
      * destruct rR as [| b c' tl | [z | o | w] tl];
          try (apply IH; [lia | exact Hrest | split; [exact Ht | exact HrR]]).
        { destruct HrR as [Hc' Htl]; cbn [evalR].
          destruct (addB_spec c c' Ht Hc') as [Hwfa Heqa].
          destruct (IH revRest (RC b (addB c c') tl) ltac:(lia) Hrest (conj Hwfa Htl)) as [Hwf_r Heq_r].
          cbn [evalR] in Heq_r; rewrite Heq_r, Heqa; split; [exact Hwf_r | reflexivity]. }
        { destruct HrR as [Hz Htl]; cbn [evalR evalTok].
          rewrite (isOneB_spec z Hz).
          destruct (isOneN (toNatB z));
            apply IH; [lia | exact Hrest | split; [exact Ht | exact Htl] |
                       lia | exact Hrest | split; [exact Ht | split; [exact Hz | exact Htl]]]. }
        { destruct HrR as [Ho Htl]; cbn [evalR evalTok].
          rewrite (isOneB_spec o Ho).
          destruct (isOneN (toNatB o));
            apply IH; [lia | exact Hrest | split; [exact Ht | exact Htl] |
                       lia | exact Hrest | split; [exact Ht | split; [exact Ho | exact Htl]]]. }
      * destruct rR as [| b c' tl | t' tl];
          try (apply IH; [lia | exact Hrest | split; [exact Ht | exact HrR]]).
        apply IH; [lia | exact Hrest | exact HrR].
Qed.

Lemma foldPackR_sim (revTs : list Tok) (rR : RStack) :
  wfToks revTs -> wfR rR ->
  wfR (foldPackR revTs rR) /\ evalR (foldPackR revTs rR) = foldPackRN (evalToks revTs) (evalR rR).
Proof.
  exact (foldPackR_sim_aux (List.length revTs) revTs rR (Nat.le_refl _)).
Qed.

Lemma pushRawOverflowL_sim (bL : list Tok) (rL : LStack) :
  wfToks bL -> wfL rL ->
  wfToks (fst (pushRawOverflowL bL rL)) /\ wfL (snd (pushRawOverflowL bL rL)) /\
  evalToks (fst (pushRawOverflowL bL rL)) = fst (pushRawOverflowLN (evalToks bL) (evalL rL)) /\
  evalL (snd (pushRawOverflowL bL rL)) = snd (pushRawOverflowLN (evalToks bL) (evalL rL)).
Proof.
  intros HbL HrL.
  destruct bL as [| t0 [| t1 [| t2 [| t3 [| t4 [| t5 rest]]]]]];
    try (cbn [pushRawOverflowL evalToks pushRawOverflowLN fst snd];
         (split; [exact HbL | split; [exact HrL | split; reflexivity]])).
  destruct HbL as [Ht0 [Ht1 [Ht2 [Ht3 Htail]]]].
  cbn [pushRawOverflowL evalToks pushRawOverflowLN fst snd].
  pose proof (wfToks_rev (t4 :: t5 :: rest) Htail) as Hrev.
  destruct (foldPackL_sim (List.rev (t4 :: t5 :: rest)) rL Hrev HrL) as [Hwf Heq].
  rewrite evalToks_rev in Heq; cbn [evalToks] in Heq.
  rewrite Heq; split; [cbn [wfToks]; tauto | split; [exact Hwf | split; reflexivity]].
Qed.

Lemma pushRawOverflowR_sim (bR : list Tok) (rR : RStack) :
  wfToks bR -> wfR rR ->
  wfToks (fst (pushRawOverflowR bR rR)) /\ wfR (snd (pushRawOverflowR bR rR)) /\
  evalToks (fst (pushRawOverflowR bR rR)) = fst (pushRawOverflowRN (evalToks bR) (evalR rR)) /\
  evalR (snd (pushRawOverflowR bR rR)) = snd (pushRawOverflowRN (evalToks bR) (evalR rR)).
Proof.
  intros HbR HrR.
  destruct bR as [| t0 [| t1 [| t2 [| t3 [| t4 [| t5 rest]]]]]];
    try (cbn [pushRawOverflowR evalToks pushRawOverflowRN fst snd];
         (split; [exact HbR | split; [exact HrR | split; reflexivity]])).
  destruct HbR as [Ht0 [Ht1 [Ht2 [Ht3 Htail]]]].
  cbn [pushRawOverflowR evalToks pushRawOverflowRN fst snd].
  pose proof (wfToks_rev (t4 :: t5 :: rest) Htail) as Hrev.
  destruct (foldPackR_sim (List.rev (t4 :: t5 :: rest)) rR Hrev HrR) as [Hwf Heq].
  rewrite evalToks_rev in Heq; cbn [evalToks] in Heq.
  rewrite Heq; split; [cbn [wfToks]; tauto | split; [exact Hwf | split; reflexivity]].
Qed.

Lemma canClean_sim (sL : LStack) (sR : RStack) :
  wfL sL -> wfR sR -> canClean sL sR = canCleanN (evalL sL) (evalR sR).
Proof.
  intros HsL HsR.
  destruct sL as [| b0 lt | ? ?]; [reflexivity | | reflexivity].
  destruct sR as [| isC1 c0 rt | ? ?]; [reflexivity | | reflexivity].
  destruct HsL as [Hb0 Hlt]; destruct HsR as [Hc0 Hrt].
  cbn [canClean evalL evalR canCleanN].
  destruct (sub2xTryB_zero_spec b0 c0 Hb0 Hc0) as [Hz Hdiff].
  rewrite Hz.
  destruct (isZeroN (toNatB b0 - 2 * toNatB c0)).
  - destruct lt as [| b1 ? | ? ?]; [reflexivity | | reflexivity].
    destruct Hlt as [Hb1 _]; cbn [evalL].
    destruct (subSmall3B_spec b1 Hb1) as [Hwf_nb1 Heq_nb1].
    rewrite (isZeroB_spec _ Hwf_nb1), Heq_nb1.
    destruct (isZeroN (toNatB b1 - 3)); [reflexivity | ].
    destruct (subHalfTryB_zero_spec (oddB b0) c0 b0 Hc0 Hb0) as [Hzh _].
    rewrite Hzh, (oddB_spec b0); reflexivity.
  - destruct (Hdiff Hz) as [Hwf_diff Heq_diff].
    destruct isC1.
    + destruct (subSmall2B_spec _ Hwf_diff) as [Hwf_nb0 Heq_nb0].
      rewrite (isZeroB_spec _ Hwf_nb0), Heq_nb0, Heq_diff.
      destruct (isZeroN (toNatB b0 - 2 * toNatB c0 - 2)); [reflexivity | ].
      destruct rt as [| ? c1 ? | ? ?]; [reflexivity | | reflexivity].
      destruct Hrt as [Hc1 _]; cbn [evalR]; destruct (subSmall2B_spec c1 Hc1) as [Hwf_nc1 Heq_nc1].
      rewrite (isZeroB_spec _ Hwf_nc1), Heq_nc1; reflexivity.
    + rewrite (isZeroB_spec c0 Hc0); destruct (isZeroN (toNatB c0)); [reflexivity | ].
      destruct rt as [| ? c1 ? | ? ?]; [reflexivity | | reflexivity].
      destruct Hrt as [Hc1 _]; cbn [evalR]; destruct (subSmall1B_spec c1 Hc1) as [Hwf_nc1 Heq_nc1].
      rewrite (isZeroB_spec _ Hwf_nc1), Heq_nc1; reflexivity.
Qed.

Lemma finishGen_overflow_sim (q : Q_st) (h : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) :
  wfToks bL -> wfL rL -> wfToks bR -> wfR rR ->
  let oL := pushRawOverflowL bL rL in
  let oR := pushRawOverflowR bR rR in
  let oLN := pushRawOverflowLN (evalToks bL) (evalL rL) in
  let oRN := pushRawOverflowRN (evalToks bR) (evalR rR) in
  wfHyb (HGen q h (fst oL) (snd oL) (fst oR) (snd oR)) /\
  evalHyb (HGen q h (fst oL) (snd oL) (fst oR) (snd oR)) = HGenN q h (fst oLN) (snd oLN) (fst oRN) (snd oRN).
Proof.
  intros HbL HrL HbR HrR.
  destruct (pushRawOverflowL_sim bL rL HbL HrL) as [HL1 [HL2 [EL1 EL2]]].
  destruct (pushRawOverflowR_sim bR rR HbR HrR) as [HR1 [HR2 [ER1 ER2]]].
  cbn [wfHyb evalHyb]; rewrite EL1, EL2, ER1, ER2.
  split; [exact (conj HL1 (conj HL2 (conj HR1 HR2))) | reflexivity].
Qed.

Lemma finishGen_sim (q : Q_st) (h : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) :
  wfToks bL -> wfL rL -> wfToks bR -> wfR rR ->
  wfHyb (finishGen q h bL rL bR rR) /\
  evalHyb (finishGen q h bL rL bR rR) = finishGenN q h (evalToks bL) (evalL rL) (evalToks bR) (evalR rR).
Proof.
  intros HbL HrL HbR HrR.
  destruct q, h; try exact (finishGen_overflow_sim _ _ bL rL bR rR HbL HrL HbR HrR).
  destruct bL as [| [z0 | o0 | w0] restL];
    try exact (finishGen_overflow_sim QF true _ rL bR rR HbL HrL HbR HrR).
  pose proof HbL as [Hw0 HrestL].
  cbn [finishGen evalToks evalTok finishGenN].
  rewrite (isThreeB_spec w0 Hw0).
  destruct (isThreeN (toNatB w0)).
  - destruct (foldPackL_sim (List.rev restL) rL (wfToks_rev _ HrestL) HrL) as [HwfpL HeqpL].
    destruct (foldPackR_sim (List.rev bR) rR (wfToks_rev _ HbR) HrR) as [HwfpR HeqpR].
    rewrite evalToks_rev in HeqpL, HeqpR.
    rewrite (canClean_sim _ _ HwfpL HwfpR), HeqpL, HeqpR.
    destruct (canCleanN _ _).
    + cbn [wfHyb evalHyb]; rewrite HeqpL, HeqpR; split; [split; assumption | reflexivity].
    + exact (finishGen_overflow_sim QF true (TokW w0 :: restL) rL bR rR HbL HrL HbR HrR).
  - exact (finishGen_overflow_sim QF true (TokW w0 :: restL) rL bR rR HbL HrL HbR HrR).
Qed.

Lemma pushBit_sim (b : bool) (ts : list Tok) (emptyTail : bool) :
  wfToks ts ->
  wfToks (pushBit b ts emptyTail) /\
  evalToks (pushBit b ts emptyTail) = pushBitN b (evalToks ts) emptyTail.
Proof.
  intro Hts; pose proof wfB_B1; pose proof wfB_B2; destruct b.
  - destruct ts as [| [z0 | o0 | w0] [| [z1 | o1 | w1] rest]];
      try (cbn [pushBit wfToks wfTok evalToks evalTok pushBitN] in *; (split; [tauto | reflexivity])).
    + destruct Hts as [Ho0 _]; cbn [pushBit evalToks evalTok pushBitN].
      rewrite (isOneB_spec o0 Ho0).
      destruct (isOneN (toNatB o0)).
      * destruct emptyTail; cbn [wfToks wfTok evalToks evalTok]; (split; [tauto | reflexivity]).
      * destruct (addSmall1B_spec o0 Ho0) as [Hwfa Heqa].
        cbn [wfToks wfTok evalToks evalTok]; rewrite Heqa; split; [tauto | reflexivity].
    + destruct Hts as [Ho0 [Hz1 Hrest]]; cbn [pushBit evalToks evalTok pushBitN].
      rewrite (isOneB_spec o0 Ho0).
      destruct (isOneN (toNatB o0)).
      * rewrite (isOneB_spec z1 Hz1).
        destruct (isOneN (toNatB z1)).
        { exact (pushTok_sim (TokW B1) rest wfB_B1 Hrest). }
        { rewrite (lebB_spec B2 z1 wfB_B2 Hz1); cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul].
          destruct (lebN 2 (toNatB z1)).
          - destruct (subSmall1B_spec z1 Hz1) as [Hwfs Heqs].
            cbn [wfToks wfTok evalToks evalTok]; rewrite Heqs; split; [tauto | reflexivity].
          - cbn [wfToks wfTok evalToks evalTok]; split; [tauto | reflexivity]. }
      * destruct (addSmall1B_spec o0 Ho0) as [Hwfa Heqa].
        cbn [wfToks wfTok evalToks evalTok]; rewrite Heqa; split; [tauto | reflexivity].
    + destruct Hts as [Ho0 Hrest]; destruct (addSmall1B_spec o0 Ho0) as [Hwfa Heqa].
      cbn [pushBit wfToks wfTok evalToks evalTok pushBitN] in *; rewrite Heqa; split; [tauto | reflexivity].
    + destruct Hts as [Ho0 Hrest]; destruct (addSmall1B_spec o0 Ho0) as [Hwfa Heqa].
      cbn [pushBit wfToks wfTok evalToks evalTok pushBitN] in *; rewrite Heqa; split; [tauto | reflexivity].
  - destruct ts as [| [n | n | n] rest];
      try (cbn [pushBit wfToks wfTok evalToks evalTok pushBitN] in *; (split; [tauto | reflexivity])).
    + destruct emptyTail; cbn [pushBit wfToks wfTok evalToks evalTok pushBitN]; (split; [tauto | reflexivity]).
    + destruct Hts as [Hn Hrest]; destruct (addSmall1B_spec n Hn) as [Hwfa Heqa].
      cbn [pushBit wfToks wfTok evalToks evalTok pushBitN]; rewrite Heqa; split; [tauto | reflexivity].
Qed.

Lemma popBit_sim (ts : list Tok) :
  wfToks ts ->
  (match popBit ts with None => True | Some (_, ts') => wfToks ts' end) /\
  popBitN (evalToks ts) =
    match popBit ts with None => None | Some (b, ts') => Some (b, evalToks ts') end.
Proof.
  induction ts as [| [n | n | n] rest IH]; intro Hts; [split; [exact I | reflexivity] | ..];
    destruct Hts as [Hn Hrest]; cbn [popBit evalToks evalTok popBitN];
    rewrite (isZeroB_spec n Hn);
    (destruct (isZeroN (toNatB n)); [exact (IH Hrest) | ]);
    rewrite (isOneB_spec n Hn);
    destruct (isOneN (toNatB n)).
  - split; [exact Hrest | reflexivity].
  - destruct (subSmall1B_spec n Hn) as [Hwfs Heqs]; cbn [wfToks wfTok evalToks evalTok];
      rewrite Heqs; split; [split; [exact Hwfs | exact Hrest] | reflexivity].
  - split; [exact Hrest | reflexivity].
  - destruct (subSmall1B_spec n Hn) as [Hwfs Heqs]; cbn [wfToks wfTok evalToks evalTok];
      rewrite Heqs; split; [split; [exact Hwfs | exact Hrest] | reflexivity].
  - destruct (pushTok_sim (TokZ B1) rest wfB_B1 Hrest) as [Hwfp Heqp].
    cbn [wfToks wfTok evalToks evalTok] in *; rewrite Heqp.
    split; [split; [exact wfB_B1 | exact Hwfp] | reflexivity].
  - destruct (subSmall1B_spec n Hn) as [Hwfs Heqs]; cbn [wfToks wfTok evalToks evalTok];
      rewrite Heqs; split; [repeat split; auto; try discriminate | reflexivity].
Qed.

Lemma isEmptyL_sim (rL : LStack) : isEmptyL rL = isEmptyLN (evalL rL).
Proof. destruct rL; reflexivity. Qed.

Lemma isEmptyR_sim (rR : RStack) : isEmptyR rR = isEmptyRN (evalR rR).
Proof. destruct rR; reflexivity. Qed.

Lemma popBitL_sim (bL : list Tok) (rL : LStack) :
  wfToks bL -> wfL rL ->
  (match popBitL bL rL with None => True | Some (_, bL', rL') => wfToks bL' /\ wfL rL' end) /\
  popBitLN (evalToks bL) (evalL rL) =
    match popBitL bL rL with None => None | Some (b, bL', rL') => Some (b, evalToks bL', evalL rL') end.
Proof.
  intros HbL HrL; unfold popBitL, popBitLN.
  destruct (popBit_sim bL HbL) as [Hwfp Heqp]; rewrite Heqp.
  destruct (popBit bL) as [[b bL'] | ].
  - split; [split; [exact Hwfp | exact HrL] | reflexivity].
  - destruct rL; [split; [split; exact I | reflexivity] | split; [exact I | reflexivity]..].
Qed.

Lemma popBitR_sim (bR : list Tok) (rR : RStack) :
  wfToks bR -> wfR rR ->
  (match popBitR bR rR with None => True | Some (_, bR', rR') => wfToks bR' /\ wfR rR' end) /\
  popBitRN (evalToks bR) (evalR rR) =
    match popBitR bR rR with None => None | Some (b, bR', rR') => Some (b, evalToks bR', evalR rR') end.
Proof.
  intros HbR HrR; unfold popBitR, popBitRN.
  destruct (popBit_sim bR HbR) as [Hwfp Heqp]; rewrite Heqp.
  destruct (popBit bR) as [[b bR'] | ].
  - split; [split; [exact Hwfp | exact HrR] | reflexivity].
  - destruct rR; [split; [split; exact I | reflexivity] | split; [exact I | reflexivity]..].
Qed.

Lemma stepRawR_sim (q q' : Q_st) (h bit : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) :
  wfToks bL -> wfL rL -> wfToks bR -> wfR rR ->
  let s := match popBitR bR rR with
           | Some (h', bR', rR') => finishGen q' h' (pushBit bit bL (isEmptyL rL)) rL bR' rR'
           | None => HGen q h bL rL bR rR
           end in
  let sN := match popBitRN (evalToks bR) (evalR rR) with
            | Some (h', bR', rR') => finishGenN q' h' (pushBitN bit (evalToks bL) (isEmptyLN (evalL rL))) (evalL rL) bR' rR'
            | None => HGenN q h (evalToks bL) (evalL rL) (evalToks bR) (evalR rR)
            end in
  wfHyb s /\ evalHyb s = sN.
Proof.
  intros HbL HrL HbR HrR; cbn zeta.
  destruct (popBitR_sim bR rR HbR HrR) as [Hwfp Heqp]; rewrite Heqp.
  destruct (popBitR bR rR) as [[[h' bR'] rR'] | ].
  - destruct Hwfp as [HbR' HrR'].
    destruct (pushBit_sim bit bL (isEmptyL rL) HbL) as [Hwfb Heqb].
    destruct (finishGen_sim q' h' _ rL bR' rR' Hwfb HrL HbR' HrR') as [Hwff Heqf].
    split; [exact Hwff | rewrite Heqf, Heqb, isEmptyL_sim; reflexivity].
  - split; [exact (conj HbL (conj HrL (conj HbR HrR))) | reflexivity].
Qed.

Lemma stepRawL_sim (q q' : Q_st) (h bit : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) :
  wfToks bL -> wfL rL -> wfToks bR -> wfR rR ->
  let s := match popBitL bL rL with
           | Some (h', bL', rL') => finishGen q' h' bL' rL' (pushBit bit bR (isEmptyR rR)) rR
           | None => HGen q h bL rL bR rR
           end in
  let sN := match popBitLN (evalToks bL) (evalL rL) with
            | Some (h', bL', rL') => finishGenN q' h' bL' rL' (pushBitN bit (evalToks bR) (isEmptyRN (evalR rR))) (evalR rR)
            | None => HGenN q h (evalToks bL) (evalL rL) (evalToks bR) (evalR rR)
            end in
  wfHyb s /\ evalHyb s = sN.
Proof.
  intros HbL HrL HbR HrR; cbn zeta.
  destruct (popBitL_sim bL rL HbL HrL) as [Hwfp Heqp]; rewrite Heqp.
  destruct (popBitL bL rL) as [[[h' bL'] rL'] | ].
  - destruct Hwfp as [HbL' HrL'].
    destruct (pushBit_sim bit bR (isEmptyR rR) HbR) as [Hwfb Heqb].
    destruct (finishGen_sim q' h' bL' rL' _ rR HbL' HrL' Hwfb HrR) as [Hwff Heqf].
    split; [exact Hwff | rewrite Heqf, Heqb, isEmptyR_sim; reflexivity].
  - split; [exact (conj HbL (conj HrL (conj HbR HrR))) | reflexivity].
Qed.

Lemma stepRaw_sim (q : Q_st) (h : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) :
  wfToks bL -> wfL rL -> wfToks bR -> wfR rR ->
  wfHyb (stepRaw q h bL rL bR rR) /\
  evalHyb (stepRaw q h bL rL bR rR) = stepRawN q h (evalToks bL) (evalL rL) (evalToks bR) (evalR rR).
Proof.
  intros HbL HrL HbR HrR; destruct q, h; cbn [stepRaw stepRawN];
    try exact (stepRawR_sim _ _ _ _ bL rL bR rR HbL HrL HbR HrR);
    try exact (stepRawL_sim _ _ _ _ bL rL bR rR HbL HrL HbR HrR);
    (split; [exact (conj HbL (conj HrL (conj HbR HrR))) | reflexivity]).
Qed.

Lemma startsWith1_sim (ts : list Tok) :
  wfToks ts -> startsWith1 ts = startsWith1N (evalToks ts).
Proof.
  destruct ts as [| [n | n | n] rest]; intro Hts; try reflexivity;
    destruct Hts as [Hn _]; cbn [startsWith1 evalToks evalTok startsWith1N];
    rewrite (isZeroB_spec n Hn); reflexivity.
Qed.

Lemma subWHead_sim (c d : Big) (rest : list Tok) :
  wfB c -> wfB d -> wfToks rest ->
  wfToks (subWHead c d rest) /\
  evalToks (subWHead c d rest) = subWHeadN (toNatB c) (toNatB d) (evalToks rest).
Proof.
  intros Hc Hd Hrest; unfold subWHead, subWHeadN.
  destruct (subB_spec c d Hc Hd) as [Hwfs Heqs].
  rewrite (isZeroB_spec _ Hwfs), Heqs.
  destruct (isZeroN (toNatB c - toNatB d)).
  - split; [exact Hrest | reflexivity].
  - cbn [wfToks wfTok evalToks evalTok]; rewrite Heqs; split; [split; [exact Hwfs | exact Hrest] | reflexivity].
Qed.

Lemma tail_w_sim (a b : Big) (lTail : list Tok) :
  wfB a -> wfB b -> wfToks lTail ->
  let res := if isZeroB b then TokW a :: pushTok (TokZ B1) lTail else TokW a :: TokZ B1 :: TokW b :: lTail in
  let resN := if isZeroN (toNatB b) then TokWN (toNatB a) :: pushTokN (TokZN 1) (evalToks lTail)
              else TokWN (toNatB a) :: TokZN 1 :: TokWN (toNatB b) :: evalToks lTail in
  wfToks res /\ evalToks res = resN.
Proof.
  intros Ha Hb Hl; cbn zeta.
  rewrite (isZeroB_spec b Hb).
  destruct (isZeroN (toNatB b)).
  - destruct (pushTok_sim (TokZ B1) lTail wfB_B1 Hl) as [Hwfp Heqp].
    cbn [wfToks wfTok evalToks evalTok] in *; rewrite Heqp; split; [split; [exact Ha | exact Hwfp] | reflexivity].
  - cbn [wfToks wfTok evalToks evalTok]; split; [repeat split; auto; try discriminate | reflexivity].
Qed.

Lemma tail_w3_sim (a b : Big) (lTail : list Tok) :
  wfB a -> wfB b -> wfToks lTail ->
  let res := if isZeroB b then TokW B3 :: TokZ B1 :: TokW a :: pushTok (TokZ B1) lTail
             else TokW B3 :: TokZ B1 :: TokW a :: TokZ B1 :: TokW b :: lTail in
  let resN := if isZeroN (toNatB b) then TokWN 3 :: TokZN 1 :: TokWN (toNatB a) :: pushTokN (TokZN 1) (evalToks lTail)
              else TokWN 3 :: TokZN 1 :: TokWN (toNatB a) :: TokZN 1 :: TokWN (toNatB b) :: evalToks lTail in
  wfToks res /\ evalToks res = resN.
Proof.
  intros Ha Hb Hl; cbn zeta.
  rewrite (isZeroB_spec b Hb).
  destruct (isZeroN (toNatB b)).
  - destruct (pushTok_sim (TokZ B1) lTail wfB_B1 Hl) as [Hwfp Heqp].
    cbn [wfToks wfTok evalToks evalTok] in *; rewrite Heqp; repeat split; auto; try discriminate.
  - cbn [wfToks wfTok evalToks evalTok]; repeat split; auto; try discriminate.
Qed.

Lemma stepGenF1PP_sim (a : Big) (lTail : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) (bL_orig : list Tok) :
  wfB a -> wfToks lTail -> wfL rL -> wfToks bR -> wfR rR -> wfToks bL_orig ->
  wfHyb (stepGenF1PP a lTail rL bR rR bL_orig) /\
  evalHyb (stepGenF1PP a lTail rL bR rR bL_orig) =
    stepGenF1PPN (toNatB a) (evalToks lTail) (evalL rL) (evalToks bR) (evalR rR) (evalToks bL_orig).
Proof.
  intros Ha Hl HrL HbR HrR HbLo; unfold stepGenF1PP, stepGenF1PPN.
  destruct bR as [| [z0 | o0 | w0] [| [z | o1 | w1] rTail]];
    try exact (stepRaw_sim QF true bL_orig rL _ rR HbLo HrL HbR HrR).
  - pose proof HbR as [Ho0 _]; cbn [evalToks evalTok].
    rewrite (isOneB_spec o0 Ho0).
    destruct (isOneN (toNatB o0)); [| exact (stepRaw_sim QF true bL_orig rL _ rR HbLo HrL HbR HrR)].
    destruct rR; try exact (stepRaw_sim QF true bL_orig rL _ _ HbLo HrL HbR HrR).
    destruct (finishGen_sim QF true lTail rL [TokO B1; TokZ B1; TokW a] RNil
                Hl HrL ltac:(repeat split; auto; try discriminate) I) as [Hwff Heqf].
    cbn [evalToks evalTok evalR] in Heqf; rewrite Heqf; split; [exact Hwff | reflexivity].
  - pose proof HbR as [Ho0 [Hz HrTail]]; cbn [evalToks evalTok].
    rewrite (isOneB_spec o0 Ho0), (isZeroB_spec z Hz).
    destruct (andb (isOneN (toNatB o0)) (negb (isZeroN (toNatB z))));
      [| exact (stepRaw_sim QF true bL_orig rL _ rR HbLo HrL HbR HrR)].
    destruct (subSmall1B_spec z Hz) as [Hwf_z1 Heq_z1].
    rewrite (isZeroB_spec _ Hwf_z1), Heq_z1.
    set (rRest := if isZeroN (toNatB z - 1) then rTail else TokZ (subSmall1B z) :: rTail).
    assert (HrRest : wfToks rRest /\
                     evalToks rRest = (if isZeroN (toNatB z - 1) then evalToks rTail else TokZN (toNatB z - 1) :: evalToks rTail)).
    { subst rRest; destruct (isZeroN (toNatB z - 1));
        [split; [exact HrTail | reflexivity]
        | cbn [wfToks wfTok evalToks evalTok]; rewrite Heq_z1; split; [split; assumption | reflexivity]]. }
    destruct HrRest as [Hwf_rr Heq_rr].
    destruct (pushTok_sim (TokW a) rRest Ha Hwf_rr) as [Hwfp Heqp].
    destruct (finishGen_sim QF true lTail rL (TokO B1 :: TokZ B1 :: pushTok (TokW a) rRest) rR
                Hl HrL ltac:(repeat split; auto; try discriminate) HrR) as [Hwff Heqf].
    cbn [evalToks evalTok] in Heqf, Heqp; rewrite Heqf, Heqp, Heq_rr.
    split; [exact Hwff | reflexivity].
Qed.

Lemma stepGenP1_sim (a b1 : Big) (lTail : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) (bL_orig : list Tok) :
  wfB a -> wfB b1 -> wfToks lTail -> wfL rL -> wfToks bR -> wfR rR -> wfToks bL_orig ->
  wfHyb (stepGenP1 a b1 lTail rL bR rR bL_orig) /\
  evalHyb (stepGenP1 a b1 lTail rL bR rR bL_orig) =
    stepGenP1N (toNatB a) (toNatB b1) (evalToks lTail) (evalL rL) (evalToks bR) (evalR rR) (evalToks bL_orig).
Proof.
  intros Ha Hb1 Hl HrL HbR HrR HbLo; unfold stepGenP1, stepGenP1N.
  destruct (addSmall2B_spec a Ha) as [Hwf_a' Heq_a'].
  destruct (tail_w_sim (addSmall2B a) b1 lTail Hwf_a' Hb1 Hl) as [Hwf_bL' Heq_bL']; cbn zeta in Hwf_bL', Heq_bL'.
  rewrite Heq_a' in Heq_bL'.
  destruct bR as [| [z0 | o0 | w0] [| [z | o1 | w1] rTail]];
    try exact (stepRaw_sim QF true bL_orig rL _ rR HbLo HrL HbR HrR).
  - pose proof HbR as [Ho0 _]; cbn [evalToks evalTok].
    rewrite (isOneB_spec o0 Ho0).
    destruct (isOneN (toNatB o0)); [| exact (stepRaw_sim QF true bL_orig rL _ rR HbLo HrL HbR HrR)].
    destruct rR; try exact (stepRaw_sim QF true bL_orig rL _ _ HbLo HrL HbR HrR).
    destruct (finishGen_sim QA false _ rL [] RNil Hwf_bL' HrL I I) as [Hwff Heqf].
    cbn [evalToks evalR] in Heqf; rewrite Heqf, Heq_bL'; split; [exact Hwff | reflexivity].
  - pose proof HbR as [Ho0 [Hz HrTail]]; cbn [evalToks evalTok].
    rewrite (isOneB_spec o0 Ho0), (isZeroB_spec z Hz).
    destruct (andb (isOneN (toNatB o0)) (negb (isZeroN (toNatB z))));
      [| exact (stepRaw_sim QF true bL_orig rL _ rR HbLo HrL HbR HrR)].
    destruct (subSmall1B_spec z Hz) as [Hwf_z1 Heq_z1].
    rewrite (isZeroB_spec _ Hwf_z1), Heq_z1.
    set (rAfter := if isZeroN (toNatB z - 1) then rTail else TokZ (subSmall1B z) :: rTail).
    assert (HrAfter : wfToks rAfter /\
                      evalToks rAfter = (if isZeroN (toNatB z - 1) then evalToks rTail else TokZN (toNatB z - 1) :: evalToks rTail)).
    { subst rAfter; destruct (isZeroN (toNatB z - 1));
        [split; [exact HrTail | reflexivity]
        | cbn [wfToks wfTok evalToks evalTok]; rewrite Heq_z1; split; [split; assumption | reflexivity]]. }
    destruct HrAfter as [Hwf_ra Heq_ra].
    destruct (popBitR_sim rAfter rR Hwf_ra HrR) as [Hwfp Heqp]; rewrite Heq_ra in Heqp; rewrite Heqp.
    destruct (popBitR rAfter rR) as [[[h' bR'] rR'] | ];
      [| exact (stepRaw_sim QF true bL_orig rL _ rR HbLo HrL HbR HrR)].
    destruct Hwfp as [HbR' HrR'].
    destruct (finishGen_sim QA h' _ rL bR' rR' Hwf_bL' HrL HbR' HrR') as [Hwff Heqf].
    rewrite Heqf, Heq_bL'; split; [exact Hwff | reflexivity].
Qed.

Lemma stepGenCore_sim (q : Q_st) (h : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) :
  wfToks bL -> wfL rL -> wfToks bR -> wfR rR ->
  wfHyb (stepGenCore q h bL rL bR rR) /\
  evalHyb (stepGenCore q h bL rL bR rR) = stepGenCoreN q h (evalToks bL) (evalL rL) (evalToks bR) (evalR rR).
Proof.
  intros HbL HrL HbR HrR; unfold stepGenCore, stepGenCoreN.
  destruct q, h; try exact (stepRaw_sim _ _ bL rL bR rR HbL HrL HbR HrR).
  - (* QA, true *)
    destruct bR as [| [zr0 | n | c] rTail];
      try exact (stepRaw_sim QA true bL rL _ rR HbL HrL HbR HrR).
    + (* TokO n :: rTail *)
      pose proof HbR as [Hn HrTail]; cbn [evalToks evalTok].
      rewrite (lebB_spec B2 n wfB_B2 Hn); cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul].
      destruct (lebN 2 (toNatB n)).
      * destruct (subSmall2B_spec n Hn) as [Hwf_n2 Heq_n2].
        rewrite (isZeroB_spec _ Hwf_n2), Heq_n2.
        set (rRest := if isZeroN (toNatB n - 2) then rTail else TokO (subSmall2B n) :: rTail).
        assert (HrRest : wfToks rRest /\
                         evalToks rRest = (if isZeroN (toNatB n - 2) then evalToks rTail else TokON (toNatB n - 2) :: evalToks rTail)).
        { subst rRest; destruct (isZeroN (toNatB n - 2));
            [split; [exact HrTail | reflexivity]
            | cbn [wfToks wfTok evalToks evalTok]; rewrite Heq_n2; split; [split; assumption | reflexivity]]. }
        destruct HrRest as [Hwf_rr Heq_rr].
        destruct (pushTok_sim (TokZ B1) rRest wfB_B1 Hwf_rr) as [Hwfp Heqp].
        destruct (finishGen_sim QF true bL rL (TokO B1 :: pushTok (TokZ B1) rRest) rR
                    HbL HrL ltac:(repeat split; auto; try discriminate) HrR) as [Hwff Heqf].
        cbn [evalToks evalTok] in Heqf, Heqp; rewrite Heqf, Heqp, Heq_rr; split; [exact Hwff | reflexivity].
      * rewrite (isOneB_spec n Hn); destruct (isOneN (toNatB n));
          [| exact (stepRaw_sim QA true bL rL _ rR HbL HrL HbR HrR)].
        destruct rTail as [| [z | o1 | c] rTail2].
        { cbn [evalToks]; destruct rR; try exact (stepRaw_sim QA true bL rL _ _ HbL HrL HbR HrR).
          destruct (pushTok_sim (TokW B1) bL wfB_B1 HbL) as [Hwfp Heqp].
          destruct (finishGen_sim QA false _ rL [] RNil Hwfp HrL I I) as [Hwff Heqf].
          cbn [evalTok evalToks evalR] in Heqf, Heqp; rewrite Heqf, Heqp; split; [exact Hwff | reflexivity]. }
        { (* TokO n :: TokZ z :: rTail2 *)
          pose proof HrTail as [Hz HrTail2]; cbn [evalToks evalTok].
          rewrite (isZeroB_spec z Hz); destruct (isZeroN (toNatB z));
            [exact (stepRaw_sim QA true bL rL _ rR HbL HrL HbR HrR) | ].
          destruct (subSmall1B_spec z Hz) as [Hwf_z1 Heq_z1].
          rewrite (isZeroB_spec _ Hwf_z1), Heq_z1.
          set (rAfter := if isZeroN (toNatB z - 1) then rTail2 else TokZ (subSmall1B z) :: rTail2).
          assert (HrAfter : wfToks rAfter /\
                            evalToks rAfter = (if isZeroN (toNatB z - 1) then evalToks rTail2 else TokZN (toNatB z - 1) :: evalToks rTail2)).
          { subst rAfter; destruct (isZeroN (toNatB z - 1));
              [split; [exact HrTail2 | reflexivity]
              | cbn [wfToks wfTok evalToks evalTok]; rewrite Heq_z1; split; [split; assumption | reflexivity]]. }
          destruct HrAfter as [Hwf_ra Heq_ra]; rewrite <- Heq_ra.
          destruct rAfter as [| [z2 | o2 | c] rTail3];
            try (destruct (popBitR_sim _ rR Hwf_ra HrR) as [Hwfp Heqp]; rewrite Heqp;
                 destruct (popBitR _ rR) as [[[h' bR'] rR'] | ];
                 [destruct Hwfp as [HbR' HrR'];
                  destruct (pushTok_sim (TokW B1) bL wfB_B1 HbL) as [Hwfpt Heqpt];
                  destruct (finishGen_sim QA h' _ rL bR' rR' Hwfpt HrL HbR' HrR') as [Hwff Heqf];
                  cbn [evalTok] in Heqpt; rewrite Heqf, Heqpt; split; [exact Hwff | reflexivity]
                 | exact (stepRaw_sim QA true bL rL _ rR HbL HrL HbR HrR)]).
          pose proof Hwf_ra as [Hc HrTail3]; cbn [evalToks evalTok].
          rewrite (isZeroB_spec c Hc); destruct (isZeroN (toNatB c)).
          - destruct (popBitR_sim (TokW c :: rTail3) rR Hwf_ra HrR) as [Hwfp Heqp]; cbn [evalToks evalTok] in Heqp; rewrite Heqp.
            destruct (popBitR (TokW c :: rTail3) rR) as [[[h' bR'] rR'] | ];
              [| exact (stepRaw_sim QA true bL rL _ rR HbL HrL HbR HrR)].
            destruct Hwfp as [HbR' HrR'].
            destruct (pushTok_sim (TokW B1) bL wfB_B1 HbL) as [Hwfpt Heqpt].
            destruct (finishGen_sim QA h' _ rL bR' rR' Hwfpt HrL HbR' HrR') as [Hwff Heqf].
            cbn [evalTok] in Heqpt; rewrite Heqf, Heqpt; split; [exact Hwff | reflexivity].
          - destruct (popBitR_sim rTail3 rR HrTail3 HrR) as [Hwfp Heqp]; rewrite Heqp.
            destruct (popBitR rTail3 rR) as [[[h' bR'] rR'] | ];
              [| exact (stepRaw_sim QA true bL rL _ rR HbL HrL HbR HrR)].
            destruct Hwfp as [HbR' HrR'].
            destruct (addSmall1B_spec c Hc) as [Hwf_c1 Heq_c1].
            destruct (pushTok_sim (TokW (addSmall1B c)) bL Hwf_c1 HbL) as [Hwfpt Heqpt].
            destruct (finishGen_sim QA h' _ rL bR' rR' Hwfpt HrL HbR' HrR') as [Hwff Heqf].
            cbn [evalTok] in Heqpt; rewrite Heqf, Heqpt, Heq_c1; split; [exact Hwff | reflexivity]. }
        { exact (stepRaw_sim QA true bL rL _ rR HbL HrL HbR HrR). }
        { (* TokO n :: TokW c :: rTail2 *)
          pose proof HrTail as [Hc HrTail2]; cbn [evalToks evalTok].
          rewrite (isZeroB_spec c Hc); destruct (isZeroN (toNatB c));
            [exact (stepRaw_sim QA true bL rL _ rR HbL HrL HbR HrR) | ].
          destruct (subWHead_sim c B1 rTail2 Hc wfB_B1 HrTail2) as [Hwfs Heqs]; cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul] in Heqs.
          destruct (finishGen_sim QF true bL rL (TokO B1 :: TokZ B1 :: TokO B1 :: TokZ B1 :: subWHead c B1 rTail2) rR
                      HbL HrL ltac:(repeat split; auto; try discriminate) HrR) as [Hwff Heqf].
          cbn [evalToks evalTok] in Heqf; rewrite Heqf, Heqs; split; [exact Hwff | reflexivity]. }
    + (* TokW c :: rTail *)
      pose proof HbR as [Hc HrTail]; cbn [evalToks evalTok].
      rewrite (isZeroB_spec c Hc); destruct (isZeroN (toNatB c));
        [exact (stepRaw_sim QA true bL rL _ rR HbL HrL HbR HrR) | ].
      destruct (subWHead_sim c B1 rTail Hc wfB_B1 HrTail) as [Hwfs Heqs]; cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul] in Heqs.
      destruct (finishGen_sim QF true bL rL (TokO B1 :: TokZ B2 :: subWHead c B1 rTail) rR
                  HbL HrL ltac:(repeat split; auto; try discriminate) HrR) as [Hwff Heqf].
      cbn [evalToks evalTok] in Heqf; rewrite Heqf, Heqs; split; [exact Hwff | reflexivity].
  - (* QC, false *)
    destruct bR as [| [zr0 | or0 | c] rTail];
      try exact (stepRaw_sim QC false bL rL _ rR HbL HrL HbR HrR).
    pose proof HbR as [Hc HrTail]; cbn [evalToks evalTok].
    rewrite (isZeroB_spec c Hc); destruct (isZeroN (toNatB c));
      [exact (stepRaw_sim QC false bL rL _ rR HbL HrL HbR HrR) | ].
    destruct (popBitR_sim rTail rR HrTail HrR) as [Hwfp Heqp]; rewrite Heqp.
    destruct (popBitR rTail rR) as [[[h' bR'] rR'] | ];
      [| exact (stepRaw_sim QC false bL rL _ rR HbL HrL HbR HrR)].
    destruct Hwfp as [HbR' HrR'].
    destruct (pushBit_sim true bL (isEmptyL rL) HbL) as [Hwfb Heqb].
    destruct (pushTok_sim (TokW c) _ Hc Hwfb) as [Hwfpt Heqpt].
    destruct (finishGen_sim QA h' _ rL bR' rR' Hwfpt HrL HbR' HrR') as [Hwff Heqf].
    cbn [evalTok] in Heqpt; split; [exact Hwff | rewrite Heqf, Heqpt, Heqb, isEmptyL_sim; reflexivity].
  - (* QF, true *)
    destruct bL as [| [z0 | o0 | a] lTail];
      try exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR).
    + (* TokZ z0 :: lTail *)
      destruct lTail as [| [z1 | o1 | b] lTail2];
        try exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR).
      pose proof HbL as [Hz0 [Hb HlTail2]]; cbn [evalToks evalTok].
      rewrite (isOneB_spec z0 Hz0); destruct (isOneN (toNatB z0)).
      * rewrite (isZeroB_spec b Hb); destruct (isZeroN (toNatB b));
          [exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | ].
        destruct (subSmall1B_spec b Hb) as [Hwf_b1 Heq_b1].
        destruct (tail_w_sim B1 (subSmall1B b) lTail2 wfB_B1 Hwf_b1 HlTail2) as [Hwf_t Heq_t]; cbn zeta in Hwf_t, Heq_t.
        cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul] in Heq_t; rewrite Heq_b1 in Heq_t.
        destruct (finishGen_sim QA true _ rL bR rR Hwf_t HrL HbR HrR) as [Hwff Heqf].
        rewrite Heqf, Heq_t; split; [exact Hwff | reflexivity].
      * rewrite (isTwoB_spec z0 Hz0); destruct (isTwoN (toNatB z0));
          [| exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR)].
        rewrite (isZeroB_spec b Hb); destruct (isZeroN (toNatB b));
          [exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | ].
        destruct (subSmall1B_spec b Hb) as [Hwf_b1 Heq_b1].
        rewrite (isZeroB_spec _ Hwf_b1), Heq_b1.
        set (bL' := if isZeroN (toNatB b - 1) then pushTok (TokZ B1) lTail2 else TokZ B1 :: TokW (subSmall1B b) :: lTail2).
        assert (HbL' : wfToks bL' /\
                       evalToks bL' = (if isZeroN (toNatB b - 1) then pushTokN (TokZN 1) (evalToks lTail2)
                                       else TokZN 1 :: TokWN (toNatB b - 1) :: evalToks lTail2)).
        { subst bL'; destruct (isZeroN (toNatB b - 1)).
          - exact (pushTok_sim (TokZ B1) lTail2 wfB_B1 HlTail2).
          - cbn [wfToks wfTok evalToks evalTok]; rewrite Heq_b1; repeat split; auto; try discriminate. }
        destruct HbL' as [Hwf_bL' Heq_bL'].
        destruct (pushBit_sim true bR (isEmptyR rR) HbR) as [Hwfb Heqb].
        destruct (pushTok_sim (TokW B1) _ wfB_B1 Hwfb) as [Hwf_bR' Heq_bR'].
        destruct (finishGen_sim QF true bL' rL _ rR Hwf_bL' HrL Hwf_bR' HrR) as [Hwff Heqf].
        cbn [evalTok] in Heq_bR'; split; [exact Hwff | rewrite Heqf, Heq_bL', Heq_bR', Heqb, isEmptyR_sim; reflexivity].
    + (* TokW a :: lTail *)
      pose proof HbL as [Ha HlTail].
      assert (HF1 : wfHyb (stepGenF1PP a lTail rL bR rR (TokW a :: lTail)) /\
                    evalHyb (stepGenF1PP a lTail rL bR rR (TokW a :: lTail)) =
                      stepGenF1PPN (toNatB a) (evalToks lTail) (evalL rL) (evalToks bR) (evalR rR) (evalToks (TokW a :: lTail))).
      { exact (stepGenF1PP_sim a lTail rL bR rR (TokW a :: lTail) Ha HlTail HrL HbR HrR HbL). }
      destruct lTail as [| [z0 | o0 | w0] lTail1].
      * cbn [evalToks evalTok]; rewrite (isZeroB_spec a Ha).
        destruct (isZeroN (toNatB a)); [exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | exact HF1].
      * (* TokW a :: TokZ z0 :: lTail1 *)
        destruct lTail1 as [| [z2 | o2 | b] lTail2];
          try (cbn [evalToks evalTok]; rewrite (isZeroB_spec a Ha);
               destruct (isZeroN (toNatB a)); [exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | exact HF1]).
        (* TokW a :: TokZ z0 :: TokW b :: lTail2 *)
        pose proof HlTail as [Hz0 [Hb HlTail2]]; cbn [evalToks evalTok].
        rewrite (isOneB_spec z0 Hz0); destruct (isOneN (toNatB z0)).
        { rewrite (isZeroB_spec a Ha), (isZeroB_spec b Hb).
          destruct (isZeroN (toNatB a)); [cbn [negb andb]; exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | ].
          destruct (isZeroN (toNatB b)); [cbn [negb andb]; exact HF1 | ].
          cbn [negb andb].
          destruct (subSmall1B_spec b Hb) as [Hwf_b1 Heq_b1].
          assert (HP1 : wfHyb (stepGenP1 a (subSmall1B b) lTail2 rL bR rR (TokW a :: TokZ z0 :: TokW b :: lTail2)) /\
                        evalHyb (stepGenP1 a (subSmall1B b) lTail2 rL bR rR (TokW a :: TokZ z0 :: TokW b :: lTail2)) =
                          stepGenP1N (toNatB a) (toNatB b - 1) (evalToks lTail2) (evalL rL) (evalToks bR) (evalR rR)
                            (TokWN (toNatB a) :: TokZN (toNatB z0) :: TokWN (toNatB b) :: evalToks lTail2)).
          { rewrite <- Heq_b1; exact (stepGenP1_sim a (subSmall1B b) lTail2 rL bR rR _ Ha Hwf_b1 HlTail2 HrL HbR HrR HbL). }
          destruct bR as [| [zr0 | o0 | c] rTail]; try exact HP1.
          - (* TokO o0 :: rTail *)
            destruct rTail as [| [z1 | or1 | c] rTail2]; try exact HP1.
            + (* TokO o0 :: TokZ z1 :: rTail2 *)
              pose proof HbR as [Ho0 [Hz1 HrTail2]]; cbn [evalToks evalTok].
              rewrite (isOneB_spec o0 Ho0); destruct (isOneN (toNatB o0));
                [| exact (stepRaw_sim QF true _ rL _ rR HbL HrL HbR HrR)].
              rewrite (isTwoB_spec z1 Hz1); destruct (isTwoN (toNatB z1)).
              * (* HC2 *)
                rewrite (startsWith1_sim rTail2 HrTail2); destruct (startsWith1N (evalToks rTail2));
                  [| exact (stepRaw_sim QF true _ rL _ rR HbL HrL HbR HrR)].
                destruct (addSmall2B_spec a Ha) as [Hwf_a' Heq_a'].
                destruct (tail_w_sim (addSmall2B a) (subSmall1B b) lTail2 Hwf_a' Hwf_b1 HlTail2) as [Hwf_t Heq_t];
                  cbn zeta in Hwf_t, Heq_t.
                rewrite Heq_a', Heq_b1 in Heq_t.
                destruct (finishGen_sim QF true _ rL rTail2 rR Hwf_t HrL HrTail2 HrR) as [Hwff Heqf].
                rewrite Heqf, Heq_t; split; [exact Hwff | reflexivity].
              * rewrite (isThreeB_spec z1 Hz1); destruct (isThreeN (toNatB z1)); [| exact HP1].
                destruct rTail2 as [| [zr2 | or2 | c] rTail3]; try exact HP1.
                pose proof HrTail2 as [Hc HrTail3]; cbn [evalToks evalTok].
                rewrite (isZeroB_spec c Hc); destruct (negb (isZeroN (toNatB c))); [| exact HP1].
                (* B3 *)
                rewrite (isOneB_spec c Hc), (startsWith1_sim rTail3 HrTail3).
                destruct (if isOneN (toNatB c) then startsWith1N (evalToks rTail3) else true);
                  [| exact (stepRaw_sim QF true _ rL _ rR HbL HrL HbR HrR)].
                destruct (tail_w3_sim a (subSmall1B b) lTail2 Ha Hwf_b1 HlTail2) as [Hwf_t Heq_t]; cbn zeta in Hwf_t, Heq_t.
                rewrite Heq_b1 in Heq_t.
                destruct (subWHead_sim c B1 rTail3 Hc wfB_B1 HrTail3) as [Hwfs Heqs]; cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul] in Heqs.
                destruct (finishGen_sim QF true _ rL _ rR Hwf_t HrL Hwfs HrR) as [Hwff Heqf].
                rewrite Heqf, Heq_t, Heqs; split; [exact Hwff | reflexivity].
            + (* B2: TokO o0 :: TokW c :: rTail2 *)
              pose proof HbR as [Ho0 [Hc HrTail2]]; cbn [evalToks evalTok].
              rewrite (isOneB_spec o0 Ho0), (lebB_spec B2 c wfB_B2 Hc); cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul].
              destruct (andb (isOneN (toNatB o0)) (lebN 2 (toNatB c)));
                [| exact (stepRaw_sim QF true _ rL _ rR HbL HrL HbR HrR)].
              rewrite (lebB_spec B2 b wfB_B2 Hb); cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul].
              destruct (lebN 2 (toNatB b));
                [| exact (stepRaw_sim QF true _ rL _ rR HbL HrL HbR HrR)].
              rewrite (isTwoB_spec c Hc), (startsWith1_sim rTail2 HrTail2).
              destruct (if isTwoN (toNatB c) then startsWith1N (evalToks rTail2) else true);
                [| exact (stepRaw_sim QF true _ rL _ rR HbL HrL HbR HrR)].
              destruct (addSmall1B_spec a Ha) as [Hwf_a' Heq_a'].
              destruct (subSmall2B_spec b Hb) as [Hwf_b2 Heq_b2].
              destruct (tail_w3_sim (addSmall1B a) (subSmall2B b) lTail2 Hwf_a' Hwf_b2 HlTail2) as [Hwf_t Heq_t];
                cbn zeta in Hwf_t, Heq_t.
              rewrite Heq_a', Heq_b2 in Heq_t.
              destruct (subWHead_sim c B2 rTail2 Hc wfB_B2 HrTail2) as [Hwfs Heqs]; cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul] in Heqs.
              destruct (finishGen_sim QF true _ rL _ rR Hwf_t HrL Hwfs HrR) as [Hwff Heqf].
              rewrite Heqf, Heq_t, Heqs; split; [exact Hwff | reflexivity].
          - (* J3A / HC1: TokW c :: rTail *)
            pose proof HbR as [Hc HrTail]; cbn [evalToks evalTok].
            rewrite (isZeroB_spec c Hc); destruct (isZeroN (toNatB c));
              [exact (stepRaw_sim QF true _ rL _ rR HbL HrL HbR HrR) | ].
            destruct (div2B_spec b Hb) as [Hwf_b2 Heq_b2].
            rewrite (lebB_spec (div2B b) c Hwf_b2 Hc), Heq_b2.
            set (k0 := if lebN (halfN (toNatB b)) (toNatB c) then div2B b else c).
            assert (Hk0 : wfB k0 /\ toNatB k0 = (if lebN (halfN (toNatB b)) (toNatB c) then halfN (toNatB b) else toNatB c)).
            { subst k0; destruct (lebN (halfN (toNatB b)) (toNatB c));
                [split; [exact Hwf_b2 | exact Heq_b2] | split; [exact Hc | reflexivity]]. }
            destruct Hk0 as [Hwf_k0 Heq_k0].
            rewrite (eqbB_spec k0 c Hwf_k0 Hc), (startsWith1_sim rTail HrTail).
            destruct (subSmall1B_spec k0 Hwf_k0) as [Hwf_k01 Heq_k01].
            set (k := if eqbN (toNatB k0) (toNatB c) then (if startsWith1N (evalToks rTail) then k0 else subSmall1B k0) else k0).
            assert (Hk : wfB k /\
                         toNatB k = (if eqbN (toNatB k0) (toNatB c)
                                     then (if startsWith1N (evalToks rTail) then toNatB k0 else toNatB k0 - 1)
                                     else toNatB k0)).
            { subst k; destruct (eqbN (toNatB k0) (toNatB c));
                [destruct (startsWith1N (evalToks rTail));
                  [split; [exact Hwf_k0 | reflexivity] | split; [exact Hwf_k01 | exact Heq_k01]]
                | split; [exact Hwf_k0 | reflexivity]]. }
            destruct Hk as [Hwf_k Heq_k].
            rewrite (isZeroB_spec k Hwf_k), Heq_k, Heq_k0.
            destruct (negb (isZeroN _)).
            + (* J3A(k) *)
              destruct (mul3addcB_spec k C0 Hwf_k) as [Hwf_3k Heq_3k]; cbn [valC6] in Heq_3k.
              destruct (addB_spec a (mul3addcB C0 k) Ha Hwf_3k) as [Hwf_a' Heq_a'].
              destruct (sub2xB_spec b k Hb Hwf_k) as [Hwf_b' Heq_b'].
              destruct (tail_w_sim (addB a (mul3addcB C0 k)) (sub2xB b k) lTail2 Hwf_a' Hwf_b' HlTail2) as [Hwf_t Heq_t];
                cbn zeta in Hwf_t, Heq_t.
              rewrite Heq_a', Heq_3k, Heq_b', Heq_k, Heq_k0 in Heq_t.
              destruct (subWHead_sim c k rTail Hc Hwf_k HrTail) as [Hwfs Heqs].
              rewrite Heq_k, Heq_k0 in Heqs.
              destruct (finishGen_sim QF true _ rL _ rR Hwf_t HrL Hwfs HrR) as [Hwff Heqf].
              rewrite Heqf, Heq_t, Heqs; split; [exact Hwff | reflexivity].
            + (* HC1 *)
              destruct (addSmall1B_spec a Ha) as [Hwf_a' Heq_a'].
              destruct (tail_w_sim (addSmall1B a) (subSmall1B b) lTail2 Hwf_a' Hwf_b1 HlTail2) as [Hwf_t Heq_t];
                cbn zeta in Hwf_t, Heq_t.
              rewrite Heq_a', Heq_b1 in Heq_t.
              destruct (subWHead_sim c B1 rTail Hc wfB_B1 HrTail) as [Hwfs Heqs]; cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul] in Heqs.
              destruct (pushTok_sim (TokZ B2) _ wfB_B2 Hwfs) as [Hwfpt Heqpt].
              destruct (finishGen_sim QF true _ rL (TokO B1 :: pushTok (TokZ B2) (subWHead c B1 rTail)) rR
                          Hwf_t HrL ltac:(repeat split; auto; try discriminate) HrR) as [Hwff Heqf].
              cbn [evalToks evalTok] in Heqf, Heqpt; rewrite Heqf, Heq_t, Heqpt, Heqs; split; [exact Hwff | reflexivity]. }
        { (* z0 <> 1 *)
          rewrite (isTwoB_spec z0 Hz0); destruct (isTwoN (toNatB z0)).
          - rewrite (isZeroB_spec a Ha), (lebB_spec B3 b wfB_B3 Hb); cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul].
            destruct (isZeroN (toNatB a)); [cbn [negb andb]; exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | ].
            destruct (lebN 3 (toNatB b)); [| cbn [negb andb]; exact HF1].
            cbn [negb andb].
            rewrite (startsWith1_sim bR HbR); destruct (startsWith1N (evalToks bR)); [| exact HF1].
            destruct (subSmall3B_spec b Hb) as [Hwf_b3 Heq_b3].
            destruct (tail_w_sim B3 (subSmall3B b) lTail2 wfB_B3 Hwf_b3 HlTail2) as [Hwf_t Heq_t];
              cbn zeta in Hwf_t, Heq_t; cbn [B0 B1 B2 B3 B18 toNatB d64ToNat Nat.add Nat.mul] in Heq_t; rewrite Heq_b3 in Heq_t.
            destruct (pushBit_sim true bR (isEmptyR rR) HbR) as [Hwfb Heqb].
            destruct (pushTok_sim (TokW a) _ Ha Hwfb) as [Hwf_bR' Heq_bR'].
            destruct (finishGen_sim QF true _ rL _ rR Hwf_t HrL Hwf_bR' HrR) as [Hwff Heqf].
            cbn [evalTok] in Heq_bR'; split; [exact Hwff | rewrite Heqf, Heq_t, Heq_bR', Heqb, isEmptyR_sim; reflexivity].
          - rewrite (isZeroB_spec a Ha); destruct (isZeroN (toNatB a));
              [cbn [negb]; exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | cbn [negb]; exact HF1]. }
      * (* TokW a :: TokO o0 :: lTail1 *)
        destruct lTail1 as [| t2 lTail2];
          [| cbn [evalToks evalTok]; rewrite (isZeroB_spec a Ha);
             destruct (isZeroN (toNatB a)); [exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | exact HF1]].
        pose proof HlTail as [Ho0 _]; cbn [evalToks evalTok].
        rewrite (isZeroB_spec a Ha), (isOneB_spec o0 Ho0).
        destruct (isZeroN (toNatB a)); [cbn [negb andb]; exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | ].
        destruct (isOneN (toNatB o0)); [| cbn [negb andb]; exact HF1].
        cbn [negb andb].
        destruct rL; try exact HF1.
        destruct bR as [| [zr0 | or0 | c] rTail]; try exact HF1.
        pose proof HbR as [Hc HrTail]; cbn [evalL evalToks evalTok].
        rewrite (isZeroB_spec c Hc); destruct (isZeroN (toNatB c));
          [exact (stepRaw_sim QF true _ LNil _ rR HbL HrL HbR HrR) | ].
        rewrite (startsWith1_sim rTail HrTail).
        destruct (subSmall1B_spec c Hc) as [Hwf_c1 Heq_c1].
        set (k := if startsWith1N (evalToks rTail) then c else subSmall1B c).
        assert (Hk : wfB k /\ toNatB k = (if startsWith1N (evalToks rTail) then toNatB c else toNatB c - 1)).
        { subst k; destruct (startsWith1N (evalToks rTail));
            [split; [exact Hc | reflexivity] | split; [exact Hwf_c1 | exact Heq_c1]]. }
        destruct Hk as [Hwf_k Heq_k].
        rewrite (isZeroB_spec k Hwf_k), Heq_k.
        destruct (negb (isZeroN _));
          [| exact (stepRaw_sim QF true _ LNil _ rR HbL HrL HbR HrR)].
        destruct (mul3addcB_spec k C0 Hwf_k) as [Hwf_3k Heq_3k]; cbn [valC6] in Heq_3k.
        destruct (addB_spec a (mul3addcB C0 k) Ha Hwf_3k) as [Hwf_a' Heq_a'].
        destruct (subWHead_sim c k rTail Hc Hwf_k HrTail) as [Hwfs Heqs].
        rewrite Heq_k in Heqs.
        destruct (finishGen_sim QF true [TokW (addB a (mul3addcB C0 k)); TokO B1] LNil _ rR
                    ltac:(repeat split; auto; try discriminate) I Hwfs HrR) as [Hwff Heqf].
        cbn [evalToks evalTok evalL] in Heqf; rewrite Heqf, Heq_a', Heq_3k, Heq_k, Heqs; split; [exact Hwff | reflexivity].
      * (* TokW a :: TokW w0 :: lTail1 *)
        cbn [evalToks evalTok]; rewrite (isZeroB_spec a Ha); destruct (isZeroN (toNatB a));
          [exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | exact HF1].
Qed.

Lemma stepGen_sim (q : Q_st) (h : bool) (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) :
  wfToks bL -> wfL rL -> wfToks bR -> wfR rR ->
  wfHyb (stepGen q h bL rL bR rR) /\
  evalHyb (stepGen q h bL rL bR rR) = stepGenN q h (evalToks bL) (evalL rL) (evalToks bR) (evalR rR).
Proof.
  intros HbL HrL HbR HrR; unfold stepGen, stepGenN.
  destruct (ensureL_sim bL rL HbL HrL) as [HL1 [HL2 [EL1 EL2]]].
  destruct (ensureR_sim bR rR HbR HrR) as [HR1 [HR2 [ER1 ER2]]].
  destruct (stepGenCore_sim q h _ _ _ _ HL1 HL2 HR1 HR2) as [Hwfc Heqc].
  rewrite Heqc, EL1, EL2, ER1, ER2; split; [exact Hwfc | reflexivity].
Qed.

Lemma runGenChunk_sim (kg : nat) :
  forall (s : HybState),
    wfHyb s ->
    wfHyb (runGenChunk kg s) /\ evalHyb (runGenChunk kg s) = runGenChunkN kg (evalHyb s).
Proof.
  induction kg as [| kg' IH]; intros [sL sR | q h bL rL bR rR] Hs; cbn [runGenChunk evalHyb runGenChunkN].
  - split; [exact Hs | reflexivity].
  - split; [exact Hs | reflexivity].
  - split; [exact Hs | reflexivity].
  - destruct Hs as [HbL [HrL [HbR HrR]]].
    destruct (stepGen_sim q h bL rL bR rR HbL HrL HbR HrR) as [Hwfs Heqs].
    destruct (IH _ Hwfs) as [Hwfr Heqr].
    rewrite Heqr, Heqs; split; [exact Hwfr | reflexivity].
Qed.

Lemma stepOuter_sim (s : HybState) :
  wfHyb s -> wfHyb (stepOuter s) /\ evalHyb (stepOuter s) = stepOuterN (evalHyb s).
Proof.
  intros Hs; destruct s as [sL sR | q h bL rL bR rR]; cbn [stepOuter evalHyb stepOuterN].
  - destruct Hs as [HsL HsR]; exact (runCleanChunk_sim kc1000 sL sR HsL HsR).
  - exact (runGenChunk_sim kg128 (HGen q h bL rL bR rR) Hs).
Qed.

Lemma Pos_iter_sim (p : positive) :
  forall (s : HybState),
    wfHyb s ->
    wfHyb (Pos.iter stepOuter s p) /\ evalHyb (Pos.iter stepOuter s p) = Pos.iter stepOuterN (evalHyb s) p.
Proof.
  induction p as [p IHp | p IHp | ]; intros s Hs; cbn [Pos.iter].
  - destruct (IHp s Hs) as [H1 E1].
    destruct (IHp _ H1) as [H2 E2].
    destruct (stepOuter_sim _ H2) as [H3 E3].
    rewrite E3, E2, E1; split; [exact H3 | reflexivity].
  - destruct (IHp s Hs) as [H1 E1].
    destruct (IHp _ H1) as [H2 E2].
    rewrite E2, E1; split; [exact H2 | reflexivity].
  - exact (stepOuter_sim s Hs).
Qed.

Lemma check_cycler_entry_sim (s : HybState) :
  wfHyb s -> check_cycler_entry s = check_cycler_entryN (evalHyb s).
Proof.
  destruct s as [sL sR | q h bL rL bR rR]; intro Hs; [reflexivity | ].
  destruct q; try reflexivity.
  destruct h; [| reflexivity].
  destruct bL as [| [z | o | n] bL_rest]; try reflexivity.
  destruct bR as [| ? ?]; [| reflexivity].
  destruct rR; try reflexivity.
  destruct Hs as [[Hn _] _].
  cbn [check_cycler_entry evalHyb evalToks evalTok evalR check_cycler_entryN].
  rewrite (lebB_spec B18 n wfB_B18 Hn); reflexivity.
Qed.

(** ** 8b. L2-Cache-Compact Clean-Loop Stepper & Equivalence *)

Definition isOdd64 (d : D64) : bool :=
  match d with D0 => false | D1 => true | D2 => false | D3 => true | D4 => false | D5 => true | D6 => false | D7 => true | D8 => false | D9 => true | D10 => false | D11 => true | D12 => false | D13 => true | D14 => false | D15 => true | D16 => false | D17 => true | D18 => false | D19 => true | D20 => false | D21 => true | D22 => false | D23 => true | D24 => false | D25 => true | D26 => false | D27 => true | D28 => false | D29 => true | D30 => false | D31 => true | D32 => false | D33 => true | D34 => false | D35 => true | D36 => false | D37 => true | D38 => false | D39 => true | D40 => false | D41 => true | D42 => false | D43 => true | D44 => false | D45 => true | D46 => false | D47 => true | D48 => false | D49 => true | D50 => false | D51 => true | D52 => false | D53 => true | D54 => false | D55 => true | D56 => false | D57 => true | D58 => false | D59 => true | D60 => false | D61 => true | D62 => false | D63 => true end.

Definition half64_q (q_hi : bool) (d0 : D64) : D64 :=
  if q_hi then match d0 with D0 => D32 | D1 => D32 | D2 => D33 | D3 => D33 | D4 => D34 | D5 => D34 | D6 => D35 | D7 => D35 | D8 => D36 | D9 => D36 | D10 => D37 | D11 => D37 | D12 => D38 | D13 => D38 | D14 => D39 | D15 => D39 | D16 => D40 | D17 => D40 | D18 => D41 | D19 => D41 | D20 => D42 | D21 => D42 | D22 => D43 | D23 => D43 | D24 => D44 | D25 => D44 | D26 => D45 | D27 => D45 | D28 => D46 | D29 => D46 | D30 => D47 | D31 => D47 | D32 => D48 | D33 => D48 | D34 => D49 | D35 => D49 | D36 => D50 | D37 => D50 | D38 => D51 | D39 => D51 | D40 => D52 | D41 => D52 | D42 => D53 | D43 => D53 | D44 => D54 | D45 => D54 | D46 => D55 | D47 => D55 | D48 => D56 | D49 => D56 | D50 => D57 | D51 => D57 | D52 => D58 | D53 => D58 | D54 => D59 | D55 => D59 | D56 => D60 | D57 => D60 | D58 => D61 | D59 => D61 | D60 => D62 | D61 => D62 | D62 => D63 | D63 => D63 end
  else match d0 with D0 => D0 | D1 => D0 | D2 => D1 | D3 => D1 | D4 => D2 | D5 => D2 | D6 => D3 | D7 => D3 | D8 => D4 | D9 => D4 | D10 => D5 | D11 => D5 | D12 => D6 | D13 => D6 | D14 => D7 | D15 => D7 | D16 => D8 | D17 => D8 | D18 => D9 | D19 => D9 | D20 => D10 | D21 => D10 | D22 => D11 | D23 => D11 | D24 => D12 | D25 => D12 | D26 => D13 | D27 => D13 | D28 => D14 | D29 => D14 | D30 => D15 | D31 => D15 | D32 => D16 | D33 => D16 | D34 => D17 | D35 => D17 | D36 => D18 | D37 => D18 | D38 => D19 | D39 => D19 | D40 => D20 | D41 => D20 | D42 => D21 | D43 => D21 | D44 => D22 | D45 => D22 | D46 => D23 | D47 => D23 | D48 => D24 | D49 => D24 | D50 => D25 | D51 => D25 | D52 => D26 | D53 => D26 | D54 => D27 | D55 => D27 | D56 => D28 | D57 => D28 | D58 => D29 | D59 => D29 | D60 => D30 | D61 => D30 | D62 => D31 | D63 => D31 end.

Fixpoint sub2x_B1 (br : C6) (x y : Big) {struct x} : Big :=
  match x, y with
  | BCons a xt, BCons b yt =>
    match br with
    | C0 | C1 | C2 =>
      match sub2x64 br a b with W0 => match sub2x_B1 C0 xt yt with BUnder => BUnder | BNil => BNil | zt => BCons D0 zt end | W1 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D1 zt end | W2 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D2 zt end | W3 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D3 zt end | W4 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D4 zt end | W5 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D5 zt end | W6 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D6 zt end | W7 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D7 zt end | W8 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D8 zt end | W9 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D9 zt end | W10 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D10 zt end | W11 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D11 zt end | W12 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D12 zt end | W13 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D13 zt end | W14 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D14 zt end | W15 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D15 zt end | W16 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D16 zt end | W17 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D17 zt end | W18 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D18 zt end | W19 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D19 zt end | W20 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D20 zt end | W21 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D21 zt end | W22 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D22 zt end | W23 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D23 zt end | W24 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D24 zt end | W25 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D25 zt end | W26 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D26 zt end | W27 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D27 zt end | W28 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D28 zt end | W29 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D29 zt end | W30 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D30 zt end | W31 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D31 zt end | W32 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D32 zt end | W33 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D33 zt end | W34 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D34 zt end | W35 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D35 zt end | W36 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D36 zt end | W37 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D37 zt end | W38 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D38 zt end | W39 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D39 zt end | W40 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D40 zt end | W41 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D41 zt end | W42 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D42 zt end | W43 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D43 zt end | W44 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D44 zt end | W45 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D45 zt end | W46 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D46 zt end | W47 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D47 zt end | W48 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D48 zt end | W49 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D49 zt end | W50 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D50 zt end | W51 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D51 zt end | W52 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D52 zt end | W53 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D53 zt end | W54 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D54 zt end | W55 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D55 zt end | W56 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D56 zt end | W57 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D57 zt end | W58 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D58 zt end | W59 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D59 zt end | W60 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D60 zt end | W61 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D61 zt end | W62 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D62 zt end | W63 => match sub2x_B1 C0 xt yt with BUnder => BUnder | zt => BCons D63 zt end | W64 => match sub2x_B1 C1 xt yt with BUnder => BUnder | BNil => BNil | zt => BCons D0 zt end | W65 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D1 zt end | W66 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D2 zt end | W67 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D3 zt end | W68 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D4 zt end | W69 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D5 zt end | W70 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D6 zt end | W71 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D7 zt end | W72 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D8 zt end | W73 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D9 zt end | W74 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D10 zt end | W75 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D11 zt end | W76 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D12 zt end | W77 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D13 zt end | W78 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D14 zt end | W79 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D15 zt end | W80 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D16 zt end | W81 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D17 zt end | W82 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D18 zt end | W83 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D19 zt end | W84 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D20 zt end | W85 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D21 zt end | W86 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D22 zt end | W87 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D23 zt end | W88 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D24 zt end | W89 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D25 zt end | W90 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D26 zt end | W91 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D27 zt end | W92 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D28 zt end | W93 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D29 zt end | W94 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D30 zt end | W95 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D31 zt end | W96 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D32 zt end | W97 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D33 zt end | W98 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D34 zt end | W99 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D35 zt end | W100 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D36 zt end | W101 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D37 zt end | W102 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D38 zt end | W103 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D39 zt end | W104 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D40 zt end | W105 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D41 zt end | W106 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D42 zt end | W107 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D43 zt end | W108 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D44 zt end | W109 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D45 zt end | W110 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D46 zt end | W111 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D47 zt end | W112 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D48 zt end | W113 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D49 zt end | W114 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D50 zt end | W115 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D51 zt end | W116 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D52 zt end | W117 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D53 zt end | W118 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D54 zt end | W119 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D55 zt end | W120 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D56 zt end | W121 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D57 zt end | W122 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D58 zt end | W123 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D59 zt end | W124 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D60 zt end | W125 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D61 zt end | W126 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D62 zt end | W127 => match sub2x_B1 C1 xt yt with BUnder => BUnder | zt => BCons D63 zt end | W128 => match sub2x_B1 C2 xt yt with BUnder => BUnder | BNil => BNil | zt => BCons D0 zt end | W129 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D1 zt end | W130 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D2 zt end | W131 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D3 zt end | W132 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D4 zt end | W133 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D5 zt end | W134 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D6 zt end | W135 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D7 zt end | W136 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D8 zt end | W137 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D9 zt end | W138 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D10 zt end | W139 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D11 zt end | W140 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D12 zt end | W141 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D13 zt end | W142 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D14 zt end | W143 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D15 zt end | W144 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D16 zt end | W145 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D17 zt end | W146 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D18 zt end | W147 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D19 zt end | W148 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D20 zt end | W149 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D21 zt end | W150 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D22 zt end | W151 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D23 zt end | W152 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D24 zt end | W153 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D25 zt end | W154 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D26 zt end | W155 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D27 zt end | W156 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D28 zt end | W157 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D29 zt end | W158 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D30 zt end | W159 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D31 zt end | W160 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D32 zt end | W161 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D33 zt end | W162 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D34 zt end | W163 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D35 zt end | W164 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D36 zt end | W165 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D37 zt end | W166 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D38 zt end | W167 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D39 zt end | W168 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D40 zt end | W169 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D41 zt end | W170 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D42 zt end | W171 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D43 zt end | W172 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D44 zt end | W173 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D45 zt end | W174 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D46 zt end | W175 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D47 zt end | W176 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D48 zt end | W177 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D49 zt end | W178 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D50 zt end | W179 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D51 zt end | W180 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D52 zt end | W181 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D53 zt end | W182 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D54 zt end | W183 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D55 zt end | W184 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D56 zt end | W185 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D57 zt end | W186 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D58 zt end | W187 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D59 zt end | W188 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D60 zt end | W189 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D61 zt end | W190 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D62 zt end | W191 => match sub2x_B1 C2 xt yt with BUnder => BUnder | zt => BCons D63 zt end | W192 => match sub2x_B1 C3 xt yt with BUnder => BUnder | BNil => BNil | zt => BCons D0 zt end | W193 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D1 zt end | W194 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D2 zt end | W195 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D3 zt end | W196 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D4 zt end | W197 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D5 zt end | W198 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D6 zt end | W199 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D7 zt end | W200 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D8 zt end | W201 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D9 zt end | W202 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D10 zt end | W203 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D11 zt end | W204 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D12 zt end | W205 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D13 zt end | W206 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D14 zt end | W207 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D15 zt end | W208 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D16 zt end | W209 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D17 zt end | W210 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D18 zt end | W211 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D19 zt end | W212 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D20 zt end | W213 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D21 zt end | W214 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D22 zt end | W215 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D23 zt end | W216 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D24 zt end | W217 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D25 zt end | W218 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D26 zt end | W219 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D27 zt end | W220 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D28 zt end | W221 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D29 zt end | W222 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D30 zt end | W223 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D31 zt end | W224 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D32 zt end | W225 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D33 zt end | W226 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D34 zt end | W227 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D35 zt end | W228 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D36 zt end | W229 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D37 zt end | W230 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D38 zt end | W231 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D39 zt end | W232 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D40 zt end | W233 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D41 zt end | W234 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D42 zt end | W235 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D43 zt end | W236 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D44 zt end | W237 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D45 zt end | W238 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D46 zt end | W239 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D47 zt end | W240 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D48 zt end | W241 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D49 zt end | W242 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D50 zt end | W243 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D51 zt end | W244 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D52 zt end | W245 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D53 zt end | W246 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D54 zt end | W247 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D55 zt end | W248 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D56 zt end | W249 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D57 zt end | W250 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D58 zt end | W251 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D59 zt end | W252 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D60 zt end | W253 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D61 zt end | W254 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D62 zt end | W255 => match sub2x_B1 C3 xt yt with BUnder => BUnder | zt => BCons D63 zt end end
    | _ => BUnder
    end
  | BCons a xt, _ =>
    match br with
    | C0 => x
    | C1 => match a, xt with D0, BNil => BUnder | _, _ => dec1B x end
    | C2 => match a, xt with D0, BNil => BUnder | D1, BNil => BUnder | _, _ => dec2B x end
    | _ => BUnder
    end
  | _, BCons _ _ => BUnder
  | _, _ => match br with C0 => BNil | _ => BUnder end
  end.

Fixpoint subHalfAux_B1 (br : bool) (x : Big) (d0 : D64) (bt : Big) {struct x} : Big :=
  match x with
  | BCons a xt =>
    match bt with
    | BCons d1 bt' =>
      match sub64b br a (half64_q (isOdd64 d1) d0) with P0 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | BNil => BNil | zt => BCons D0 zt end | P1 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D1 zt end | P2 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D2 zt end | P3 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D3 zt end | P4 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D4 zt end | P5 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D5 zt end | P6 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D6 zt end | P7 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D7 zt end | P8 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D8 zt end | P9 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D9 zt end | P10 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D10 zt end | P11 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D11 zt end | P12 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D12 zt end | P13 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D13 zt end | P14 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D14 zt end | P15 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D15 zt end | P16 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D16 zt end | P17 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D17 zt end | P18 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D18 zt end | P19 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D19 zt end | P20 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D20 zt end | P21 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D21 zt end | P22 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D22 zt end | P23 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D23 zt end | P24 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D24 zt end | P25 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D25 zt end | P26 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D26 zt end | P27 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D27 zt end | P28 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D28 zt end | P29 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D29 zt end | P30 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D30 zt end | P31 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D31 zt end | P32 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D32 zt end | P33 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D33 zt end | P34 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D34 zt end | P35 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D35 zt end | P36 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D36 zt end | P37 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D37 zt end | P38 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D38 zt end | P39 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D39 zt end | P40 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D40 zt end | P41 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D41 zt end | P42 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D42 zt end | P43 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D43 zt end | P44 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D44 zt end | P45 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D45 zt end | P46 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D46 zt end | P47 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D47 zt end | P48 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D48 zt end | P49 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D49 zt end | P50 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D50 zt end | P51 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D51 zt end | P52 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D52 zt end | P53 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D53 zt end | P54 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D54 zt end | P55 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D55 zt end | P56 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D56 zt end | P57 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D57 zt end | P58 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D58 zt end | P59 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D59 zt end | P60 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D60 zt end | P61 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D61 zt end | P62 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D62 zt end | P63 => match subHalfAux_B1 false xt d1 bt' with BUnder => BUnder | zt => BCons D63 zt end | P64 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | BNil => BNil | zt => BCons D0 zt end | P65 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D1 zt end | P66 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D2 zt end | P67 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D3 zt end | P68 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D4 zt end | P69 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D5 zt end | P70 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D6 zt end | P71 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D7 zt end | P72 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D8 zt end | P73 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D9 zt end | P74 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D10 zt end | P75 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D11 zt end | P76 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D12 zt end | P77 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D13 zt end | P78 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D14 zt end | P79 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D15 zt end | P80 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D16 zt end | P81 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D17 zt end | P82 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D18 zt end | P83 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D19 zt end | P84 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D20 zt end | P85 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D21 zt end | P86 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D22 zt end | P87 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D23 zt end | P88 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D24 zt end | P89 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D25 zt end | P90 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D26 zt end | P91 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D27 zt end | P92 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D28 zt end | P93 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D29 zt end | P94 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D30 zt end | P95 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D31 zt end | P96 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D32 zt end | P97 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D33 zt end | P98 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D34 zt end | P99 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D35 zt end | P100 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D36 zt end | P101 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D37 zt end | P102 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D38 zt end | P103 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D39 zt end | P104 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D40 zt end | P105 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D41 zt end | P106 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D42 zt end | P107 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D43 zt end | P108 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D44 zt end | P109 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D45 zt end | P110 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D46 zt end | P111 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D47 zt end | P112 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D48 zt end | P113 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D49 zt end | P114 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D50 zt end | P115 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D51 zt end | P116 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D52 zt end | P117 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D53 zt end | P118 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D54 zt end | P119 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D55 zt end | P120 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D56 zt end | P121 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D57 zt end | P122 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D58 zt end | P123 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D59 zt end | P124 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D60 zt end | P125 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D61 zt end | P126 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D62 zt end | P127 => match subHalfAux_B1 true xt d1 bt' with BUnder => BUnder | zt => BCons D63 zt end end
    | _ =>
      match sub64b br a (half64_q false d0) with P0 => match xt with BCons _ _ => BCons D0 xt | _ => BNil end | P1 => match xt with BCons _ _ => BCons D1 xt | _ => BCons D1 BNil end | P2 => match xt with BCons _ _ => BCons D2 xt | _ => BCons D2 BNil end | P3 => match xt with BCons _ _ => BCons D3 xt | _ => BCons D3 BNil end | P4 => match xt with BCons _ _ => BCons D4 xt | _ => BCons D4 BNil end | P5 => match xt with BCons _ _ => BCons D5 xt | _ => BCons D5 BNil end | P6 => match xt with BCons _ _ => BCons D6 xt | _ => BCons D6 BNil end | P7 => match xt with BCons _ _ => BCons D7 xt | _ => BCons D7 BNil end | P8 => match xt with BCons _ _ => BCons D8 xt | _ => BCons D8 BNil end | P9 => match xt with BCons _ _ => BCons D9 xt | _ => BCons D9 BNil end | P10 => match xt with BCons _ _ => BCons D10 xt | _ => BCons D10 BNil end | P11 => match xt with BCons _ _ => BCons D11 xt | _ => BCons D11 BNil end | P12 => match xt with BCons _ _ => BCons D12 xt | _ => BCons D12 BNil end | P13 => match xt with BCons _ _ => BCons D13 xt | _ => BCons D13 BNil end | P14 => match xt with BCons _ _ => BCons D14 xt | _ => BCons D14 BNil end | P15 => match xt with BCons _ _ => BCons D15 xt | _ => BCons D15 BNil end | P16 => match xt with BCons _ _ => BCons D16 xt | _ => BCons D16 BNil end | P17 => match xt with BCons _ _ => BCons D17 xt | _ => BCons D17 BNil end | P18 => match xt with BCons _ _ => BCons D18 xt | _ => BCons D18 BNil end | P19 => match xt with BCons _ _ => BCons D19 xt | _ => BCons D19 BNil end | P20 => match xt with BCons _ _ => BCons D20 xt | _ => BCons D20 BNil end | P21 => match xt with BCons _ _ => BCons D21 xt | _ => BCons D21 BNil end | P22 => match xt with BCons _ _ => BCons D22 xt | _ => BCons D22 BNil end | P23 => match xt with BCons _ _ => BCons D23 xt | _ => BCons D23 BNil end | P24 => match xt with BCons _ _ => BCons D24 xt | _ => BCons D24 BNil end | P25 => match xt with BCons _ _ => BCons D25 xt | _ => BCons D25 BNil end | P26 => match xt with BCons _ _ => BCons D26 xt | _ => BCons D26 BNil end | P27 => match xt with BCons _ _ => BCons D27 xt | _ => BCons D27 BNil end | P28 => match xt with BCons _ _ => BCons D28 xt | _ => BCons D28 BNil end | P29 => match xt with BCons _ _ => BCons D29 xt | _ => BCons D29 BNil end | P30 => match xt with BCons _ _ => BCons D30 xt | _ => BCons D30 BNil end | P31 => match xt with BCons _ _ => BCons D31 xt | _ => BCons D31 BNil end | P32 => match xt with BCons _ _ => BCons D32 xt | _ => BCons D32 BNil end | P33 => match xt with BCons _ _ => BCons D33 xt | _ => BCons D33 BNil end | P34 => match xt with BCons _ _ => BCons D34 xt | _ => BCons D34 BNil end | P35 => match xt with BCons _ _ => BCons D35 xt | _ => BCons D35 BNil end | P36 => match xt with BCons _ _ => BCons D36 xt | _ => BCons D36 BNil end | P37 => match xt with BCons _ _ => BCons D37 xt | _ => BCons D37 BNil end | P38 => match xt with BCons _ _ => BCons D38 xt | _ => BCons D38 BNil end | P39 => match xt with BCons _ _ => BCons D39 xt | _ => BCons D39 BNil end | P40 => match xt with BCons _ _ => BCons D40 xt | _ => BCons D40 BNil end | P41 => match xt with BCons _ _ => BCons D41 xt | _ => BCons D41 BNil end | P42 => match xt with BCons _ _ => BCons D42 xt | _ => BCons D42 BNil end | P43 => match xt with BCons _ _ => BCons D43 xt | _ => BCons D43 BNil end | P44 => match xt with BCons _ _ => BCons D44 xt | _ => BCons D44 BNil end | P45 => match xt with BCons _ _ => BCons D45 xt | _ => BCons D45 BNil end | P46 => match xt with BCons _ _ => BCons D46 xt | _ => BCons D46 BNil end | P47 => match xt with BCons _ _ => BCons D47 xt | _ => BCons D47 BNil end | P48 => match xt with BCons _ _ => BCons D48 xt | _ => BCons D48 BNil end | P49 => match xt with BCons _ _ => BCons D49 xt | _ => BCons D49 BNil end | P50 => match xt with BCons _ _ => BCons D50 xt | _ => BCons D50 BNil end | P51 => match xt with BCons _ _ => BCons D51 xt | _ => BCons D51 BNil end | P52 => match xt with BCons _ _ => BCons D52 xt | _ => BCons D52 BNil end | P53 => match xt with BCons _ _ => BCons D53 xt | _ => BCons D53 BNil end | P54 => match xt with BCons _ _ => BCons D54 xt | _ => BCons D54 BNil end | P55 => match xt with BCons _ _ => BCons D55 xt | _ => BCons D55 BNil end | P56 => match xt with BCons _ _ => BCons D56 xt | _ => BCons D56 BNil end | P57 => match xt with BCons _ _ => BCons D57 xt | _ => BCons D57 BNil end | P58 => match xt with BCons _ _ => BCons D58 xt | _ => BCons D58 BNil end | P59 => match xt with BCons _ _ => BCons D59 xt | _ => BCons D59 BNil end | P60 => match xt with BCons _ _ => BCons D60 xt | _ => BCons D60 BNil end | P61 => match xt with BCons _ _ => BCons D61 xt | _ => BCons D61 BNil end | P62 => match xt with BCons _ _ => BCons D62 xt | _ => BCons D62 BNil end | P63 => match xt with BCons _ _ => BCons D63 xt | _ => BCons D63 BNil end | P64 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | BNil => BNil | zt => BCons D0 zt end | P65 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D1 zt end | P66 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D2 zt end | P67 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D3 zt end | P68 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D4 zt end | P69 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D5 zt end | P70 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D6 zt end | P71 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D7 zt end | P72 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D8 zt end | P73 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D9 zt end | P74 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D10 zt end | P75 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D11 zt end | P76 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D12 zt end | P77 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D13 zt end | P78 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D14 zt end | P79 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D15 zt end | P80 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D16 zt end | P81 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D17 zt end | P82 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D18 zt end | P83 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D19 zt end | P84 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D20 zt end | P85 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D21 zt end | P86 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D22 zt end | P87 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D23 zt end | P88 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D24 zt end | P89 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D25 zt end | P90 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D26 zt end | P91 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D27 zt end | P92 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D28 zt end | P93 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D29 zt end | P94 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D30 zt end | P95 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D31 zt end | P96 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D32 zt end | P97 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D33 zt end | P98 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D34 zt end | P99 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D35 zt end | P100 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D36 zt end | P101 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D37 zt end | P102 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D38 zt end | P103 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D39 zt end | P104 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D40 zt end | P105 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D41 zt end | P106 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D42 zt end | P107 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D43 zt end | P108 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D44 zt end | P109 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D45 zt end | P110 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D46 zt end | P111 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D47 zt end | P112 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D48 zt end | P113 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D49 zt end | P114 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D50 zt end | P115 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D51 zt end | P116 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D52 zt end | P117 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D53 zt end | P118 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D54 zt end | P119 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D55 zt end | P120 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D56 zt end | P121 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D57 zt end | P122 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D58 zt end | P123 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D59 zt end | P124 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D60 zt end | P125 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D61 zt end | P126 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D62 zt end | P127 => match (match xt with BCons D0 BNil => BUnder | BCons _ _ => dec1B xt | _ => BUnder end) with BUnder => BUnder | zt => BCons D63 zt end end
    end
  | _ =>
    match bt with
    | BNil => match d0 with D0 | D1 => if br then BUnder else BNil | _ => BUnder end
    | _ => BUnder
    end
  end.

Definition subHalf_B1 (br : bool) (x b : Big) : Big :=
  match b with
  | BCons d0 bt => subHalfAux_B1 br x d0 bt
  | _ =>
    match x with
    | BCons a xt => if br then match a, xt with D0, BNil => BUnder | _, _ => dec1B x end else x
    | _ => if br then BUnder else BNil
    end
  end.

Fixpoint mul3_B1 (c : C6) (x : Big) : Big :=
  match x with
  | BCons a xt =>
    match c with
    | C0 => match a with D0 => match mul3_B1 C0 xt with BNil => BNil | zt => BCons D0 zt end | D1 => BCons D3 (mul3_B1 C0 xt) | D2 => BCons D6 (mul3_B1 C0 xt) | D3 => BCons D9 (mul3_B1 C0 xt) | D4 => BCons D12 (mul3_B1 C0 xt) | D5 => BCons D15 (mul3_B1 C0 xt) | D6 => BCons D18 (mul3_B1 C0 xt) | D7 => BCons D21 (mul3_B1 C0 xt) | D8 => BCons D24 (mul3_B1 C0 xt) | D9 => BCons D27 (mul3_B1 C0 xt) | D10 => BCons D30 (mul3_B1 C0 xt) | D11 => BCons D33 (mul3_B1 C0 xt) | D12 => BCons D36 (mul3_B1 C0 xt) | D13 => BCons D39 (mul3_B1 C0 xt) | D14 => BCons D42 (mul3_B1 C0 xt) | D15 => BCons D45 (mul3_B1 C0 xt) | D16 => BCons D48 (mul3_B1 C0 xt) | D17 => BCons D51 (mul3_B1 C0 xt) | D18 => BCons D54 (mul3_B1 C0 xt) | D19 => BCons D57 (mul3_B1 C0 xt) | D20 => BCons D60 (mul3_B1 C0 xt) | D21 => BCons D63 (mul3_B1 C0 xt) | D22 => BCons D2 (mul3_B1 C1 xt) | D23 => BCons D5 (mul3_B1 C1 xt) | D24 => BCons D8 (mul3_B1 C1 xt) | D25 => BCons D11 (mul3_B1 C1 xt) | D26 => BCons D14 (mul3_B1 C1 xt) | D27 => BCons D17 (mul3_B1 C1 xt) | D28 => BCons D20 (mul3_B1 C1 xt) | D29 => BCons D23 (mul3_B1 C1 xt) | D30 => BCons D26 (mul3_B1 C1 xt) | D31 => BCons D29 (mul3_B1 C1 xt) | D32 => BCons D32 (mul3_B1 C1 xt) | D33 => BCons D35 (mul3_B1 C1 xt) | D34 => BCons D38 (mul3_B1 C1 xt) | D35 => BCons D41 (mul3_B1 C1 xt) | D36 => BCons D44 (mul3_B1 C1 xt) | D37 => BCons D47 (mul3_B1 C1 xt) | D38 => BCons D50 (mul3_B1 C1 xt) | D39 => BCons D53 (mul3_B1 C1 xt) | D40 => BCons D56 (mul3_B1 C1 xt) | D41 => BCons D59 (mul3_B1 C1 xt) | D42 => BCons D62 (mul3_B1 C1 xt) | D43 => BCons D1 (mul3_B1 C2 xt) | D44 => BCons D4 (mul3_B1 C2 xt) | D45 => BCons D7 (mul3_B1 C2 xt) | D46 => BCons D10 (mul3_B1 C2 xt) | D47 => BCons D13 (mul3_B1 C2 xt) | D48 => BCons D16 (mul3_B1 C2 xt) | D49 => BCons D19 (mul3_B1 C2 xt) | D50 => BCons D22 (mul3_B1 C2 xt) | D51 => BCons D25 (mul3_B1 C2 xt) | D52 => BCons D28 (mul3_B1 C2 xt) | D53 => BCons D31 (mul3_B1 C2 xt) | D54 => BCons D34 (mul3_B1 C2 xt) | D55 => BCons D37 (mul3_B1 C2 xt) | D56 => BCons D40 (mul3_B1 C2 xt) | D57 => BCons D43 (mul3_B1 C2 xt) | D58 => BCons D46 (mul3_B1 C2 xt) | D59 => BCons D49 (mul3_B1 C2 xt) | D60 => BCons D52 (mul3_B1 C2 xt) | D61 => BCons D55 (mul3_B1 C2 xt) | D62 => BCons D58 (mul3_B1 C2 xt) | D63 => BCons D61 (mul3_B1 C2 xt) end
    | C1 => match a with D0 => BCons D1 (mul3_B1 C0 xt) | D1 => BCons D4 (mul3_B1 C0 xt) | D2 => BCons D7 (mul3_B1 C0 xt) | D3 => BCons D10 (mul3_B1 C0 xt) | D4 => BCons D13 (mul3_B1 C0 xt) | D5 => BCons D16 (mul3_B1 C0 xt) | D6 => BCons D19 (mul3_B1 C0 xt) | D7 => BCons D22 (mul3_B1 C0 xt) | D8 => BCons D25 (mul3_B1 C0 xt) | D9 => BCons D28 (mul3_B1 C0 xt) | D10 => BCons D31 (mul3_B1 C0 xt) | D11 => BCons D34 (mul3_B1 C0 xt) | D12 => BCons D37 (mul3_B1 C0 xt) | D13 => BCons D40 (mul3_B1 C0 xt) | D14 => BCons D43 (mul3_B1 C0 xt) | D15 => BCons D46 (mul3_B1 C0 xt) | D16 => BCons D49 (mul3_B1 C0 xt) | D17 => BCons D52 (mul3_B1 C0 xt) | D18 => BCons D55 (mul3_B1 C0 xt) | D19 => BCons D58 (mul3_B1 C0 xt) | D20 => BCons D61 (mul3_B1 C0 xt) | D21 => match mul3_B1 C1 xt with BNil => BNil | zt => BCons D0 zt end | D22 => BCons D3 (mul3_B1 C1 xt) | D23 => BCons D6 (mul3_B1 C1 xt) | D24 => BCons D9 (mul3_B1 C1 xt) | D25 => BCons D12 (mul3_B1 C1 xt) | D26 => BCons D15 (mul3_B1 C1 xt) | D27 => BCons D18 (mul3_B1 C1 xt) | D28 => BCons D21 (mul3_B1 C1 xt) | D29 => BCons D24 (mul3_B1 C1 xt) | D30 => BCons D27 (mul3_B1 C1 xt) | D31 => BCons D30 (mul3_B1 C1 xt) | D32 => BCons D33 (mul3_B1 C1 xt) | D33 => BCons D36 (mul3_B1 C1 xt) | D34 => BCons D39 (mul3_B1 C1 xt) | D35 => BCons D42 (mul3_B1 C1 xt) | D36 => BCons D45 (mul3_B1 C1 xt) | D37 => BCons D48 (mul3_B1 C1 xt) | D38 => BCons D51 (mul3_B1 C1 xt) | D39 => BCons D54 (mul3_B1 C1 xt) | D40 => BCons D57 (mul3_B1 C1 xt) | D41 => BCons D60 (mul3_B1 C1 xt) | D42 => BCons D63 (mul3_B1 C1 xt) | D43 => BCons D2 (mul3_B1 C2 xt) | D44 => BCons D5 (mul3_B1 C2 xt) | D45 => BCons D8 (mul3_B1 C2 xt) | D46 => BCons D11 (mul3_B1 C2 xt) | D47 => BCons D14 (mul3_B1 C2 xt) | D48 => BCons D17 (mul3_B1 C2 xt) | D49 => BCons D20 (mul3_B1 C2 xt) | D50 => BCons D23 (mul3_B1 C2 xt) | D51 => BCons D26 (mul3_B1 C2 xt) | D52 => BCons D29 (mul3_B1 C2 xt) | D53 => BCons D32 (mul3_B1 C2 xt) | D54 => BCons D35 (mul3_B1 C2 xt) | D55 => BCons D38 (mul3_B1 C2 xt) | D56 => BCons D41 (mul3_B1 C2 xt) | D57 => BCons D44 (mul3_B1 C2 xt) | D58 => BCons D47 (mul3_B1 C2 xt) | D59 => BCons D50 (mul3_B1 C2 xt) | D60 => BCons D53 (mul3_B1 C2 xt) | D61 => BCons D56 (mul3_B1 C2 xt) | D62 => BCons D59 (mul3_B1 C2 xt) | D63 => BCons D62 (mul3_B1 C2 xt) end
    | C2 => match a with D0 => BCons D2 (mul3_B1 C0 xt) | D1 => BCons D5 (mul3_B1 C0 xt) | D2 => BCons D8 (mul3_B1 C0 xt) | D3 => BCons D11 (mul3_B1 C0 xt) | D4 => BCons D14 (mul3_B1 C0 xt) | D5 => BCons D17 (mul3_B1 C0 xt) | D6 => BCons D20 (mul3_B1 C0 xt) | D7 => BCons D23 (mul3_B1 C0 xt) | D8 => BCons D26 (mul3_B1 C0 xt) | D9 => BCons D29 (mul3_B1 C0 xt) | D10 => BCons D32 (mul3_B1 C0 xt) | D11 => BCons D35 (mul3_B1 C0 xt) | D12 => BCons D38 (mul3_B1 C0 xt) | D13 => BCons D41 (mul3_B1 C0 xt) | D14 => BCons D44 (mul3_B1 C0 xt) | D15 => BCons D47 (mul3_B1 C0 xt) | D16 => BCons D50 (mul3_B1 C0 xt) | D17 => BCons D53 (mul3_B1 C0 xt) | D18 => BCons D56 (mul3_B1 C0 xt) | D19 => BCons D59 (mul3_B1 C0 xt) | D20 => BCons D62 (mul3_B1 C0 xt) | D21 => BCons D1 (mul3_B1 C1 xt) | D22 => BCons D4 (mul3_B1 C1 xt) | D23 => BCons D7 (mul3_B1 C1 xt) | D24 => BCons D10 (mul3_B1 C1 xt) | D25 => BCons D13 (mul3_B1 C1 xt) | D26 => BCons D16 (mul3_B1 C1 xt) | D27 => BCons D19 (mul3_B1 C1 xt) | D28 => BCons D22 (mul3_B1 C1 xt) | D29 => BCons D25 (mul3_B1 C1 xt) | D30 => BCons D28 (mul3_B1 C1 xt) | D31 => BCons D31 (mul3_B1 C1 xt) | D32 => BCons D34 (mul3_B1 C1 xt) | D33 => BCons D37 (mul3_B1 C1 xt) | D34 => BCons D40 (mul3_B1 C1 xt) | D35 => BCons D43 (mul3_B1 C1 xt) | D36 => BCons D46 (mul3_B1 C1 xt) | D37 => BCons D49 (mul3_B1 C1 xt) | D38 => BCons D52 (mul3_B1 C1 xt) | D39 => BCons D55 (mul3_B1 C1 xt) | D40 => BCons D58 (mul3_B1 C1 xt) | D41 => BCons D61 (mul3_B1 C1 xt) | D42 => match mul3_B1 C2 xt with BNil => BNil | zt => BCons D0 zt end | D43 => BCons D3 (mul3_B1 C2 xt) | D44 => BCons D6 (mul3_B1 C2 xt) | D45 => BCons D9 (mul3_B1 C2 xt) | D46 => BCons D12 (mul3_B1 C2 xt) | D47 => BCons D15 (mul3_B1 C2 xt) | D48 => BCons D18 (mul3_B1 C2 xt) | D49 => BCons D21 (mul3_B1 C2 xt) | D50 => BCons D24 (mul3_B1 C2 xt) | D51 => BCons D27 (mul3_B1 C2 xt) | D52 => BCons D30 (mul3_B1 C2 xt) | D53 => BCons D33 (mul3_B1 C2 xt) | D54 => BCons D36 (mul3_B1 C2 xt) | D55 => BCons D39 (mul3_B1 C2 xt) | D56 => BCons D42 (mul3_B1 C2 xt) | D57 => BCons D45 (mul3_B1 C2 xt) | D58 => BCons D48 (mul3_B1 C2 xt) | D59 => BCons D51 (mul3_B1 C2 xt) | D60 => BCons D54 (mul3_B1 C2 xt) | D61 => BCons D57 (mul3_B1 C2 xt) | D62 => BCons D60 (mul3_B1 C2 xt) | D63 => BCons D63 (mul3_B1 C2 xt) end
    | C3 => match a with D0 => BCons D3 (mul3_B1 C0 xt) | D1 => BCons D6 (mul3_B1 C0 xt) | D2 => BCons D9 (mul3_B1 C0 xt) | D3 => BCons D12 (mul3_B1 C0 xt) | D4 => BCons D15 (mul3_B1 C0 xt) | D5 => BCons D18 (mul3_B1 C0 xt) | D6 => BCons D21 (mul3_B1 C0 xt) | D7 => BCons D24 (mul3_B1 C0 xt) | D8 => BCons D27 (mul3_B1 C0 xt) | D9 => BCons D30 (mul3_B1 C0 xt) | D10 => BCons D33 (mul3_B1 C0 xt) | D11 => BCons D36 (mul3_B1 C0 xt) | D12 => BCons D39 (mul3_B1 C0 xt) | D13 => BCons D42 (mul3_B1 C0 xt) | D14 => BCons D45 (mul3_B1 C0 xt) | D15 => BCons D48 (mul3_B1 C0 xt) | D16 => BCons D51 (mul3_B1 C0 xt) | D17 => BCons D54 (mul3_B1 C0 xt) | D18 => BCons D57 (mul3_B1 C0 xt) | D19 => BCons D60 (mul3_B1 C0 xt) | D20 => BCons D63 (mul3_B1 C0 xt) | D21 => BCons D2 (mul3_B1 C1 xt) | D22 => BCons D5 (mul3_B1 C1 xt) | D23 => BCons D8 (mul3_B1 C1 xt) | D24 => BCons D11 (mul3_B1 C1 xt) | D25 => BCons D14 (mul3_B1 C1 xt) | D26 => BCons D17 (mul3_B1 C1 xt) | D27 => BCons D20 (mul3_B1 C1 xt) | D28 => BCons D23 (mul3_B1 C1 xt) | D29 => BCons D26 (mul3_B1 C1 xt) | D30 => BCons D29 (mul3_B1 C1 xt) | D31 => BCons D32 (mul3_B1 C1 xt) | D32 => BCons D35 (mul3_B1 C1 xt) | D33 => BCons D38 (mul3_B1 C1 xt) | D34 => BCons D41 (mul3_B1 C1 xt) | D35 => BCons D44 (mul3_B1 C1 xt) | D36 => BCons D47 (mul3_B1 C1 xt) | D37 => BCons D50 (mul3_B1 C1 xt) | D38 => BCons D53 (mul3_B1 C1 xt) | D39 => BCons D56 (mul3_B1 C1 xt) | D40 => BCons D59 (mul3_B1 C1 xt) | D41 => BCons D62 (mul3_B1 C1 xt) | D42 => BCons D1 (mul3_B1 C2 xt) | D43 => BCons D4 (mul3_B1 C2 xt) | D44 => BCons D7 (mul3_B1 C2 xt) | D45 => BCons D10 (mul3_B1 C2 xt) | D46 => BCons D13 (mul3_B1 C2 xt) | D47 => BCons D16 (mul3_B1 C2 xt) | D48 => BCons D19 (mul3_B1 C2 xt) | D49 => BCons D22 (mul3_B1 C2 xt) | D50 => BCons D25 (mul3_B1 C2 xt) | D51 => BCons D28 (mul3_B1 C2 xt) | D52 => BCons D31 (mul3_B1 C2 xt) | D53 => BCons D34 (mul3_B1 C2 xt) | D54 => BCons D37 (mul3_B1 C2 xt) | D55 => BCons D40 (mul3_B1 C2 xt) | D56 => BCons D43 (mul3_B1 C2 xt) | D57 => BCons D46 (mul3_B1 C2 xt) | D58 => BCons D49 (mul3_B1 C2 xt) | D59 => BCons D52 (mul3_B1 C2 xt) | D60 => BCons D55 (mul3_B1 C2 xt) | D61 => BCons D58 (mul3_B1 C2 xt) | D62 => BCons D61 (mul3_B1 C2 xt) | D63 => match mul3_B1 C3 xt with BNil => BNil | zt => BCons D0 zt end end
    | C4 => match a with D0 => BCons D4 (mul3_B1 C0 xt) | D1 => BCons D7 (mul3_B1 C0 xt) | D2 => BCons D10 (mul3_B1 C0 xt) | D3 => BCons D13 (mul3_B1 C0 xt) | D4 => BCons D16 (mul3_B1 C0 xt) | D5 => BCons D19 (mul3_B1 C0 xt) | D6 => BCons D22 (mul3_B1 C0 xt) | D7 => BCons D25 (mul3_B1 C0 xt) | D8 => BCons D28 (mul3_B1 C0 xt) | D9 => BCons D31 (mul3_B1 C0 xt) | D10 => BCons D34 (mul3_B1 C0 xt) | D11 => BCons D37 (mul3_B1 C0 xt) | D12 => BCons D40 (mul3_B1 C0 xt) | D13 => BCons D43 (mul3_B1 C0 xt) | D14 => BCons D46 (mul3_B1 C0 xt) | D15 => BCons D49 (mul3_B1 C0 xt) | D16 => BCons D52 (mul3_B1 C0 xt) | D17 => BCons D55 (mul3_B1 C0 xt) | D18 => BCons D58 (mul3_B1 C0 xt) | D19 => BCons D61 (mul3_B1 C0 xt) | D20 => match mul3_B1 C1 xt with BNil => BNil | zt => BCons D0 zt end | D21 => BCons D3 (mul3_B1 C1 xt) | D22 => BCons D6 (mul3_B1 C1 xt) | D23 => BCons D9 (mul3_B1 C1 xt) | D24 => BCons D12 (mul3_B1 C1 xt) | D25 => BCons D15 (mul3_B1 C1 xt) | D26 => BCons D18 (mul3_B1 C1 xt) | D27 => BCons D21 (mul3_B1 C1 xt) | D28 => BCons D24 (mul3_B1 C1 xt) | D29 => BCons D27 (mul3_B1 C1 xt) | D30 => BCons D30 (mul3_B1 C1 xt) | D31 => BCons D33 (mul3_B1 C1 xt) | D32 => BCons D36 (mul3_B1 C1 xt) | D33 => BCons D39 (mul3_B1 C1 xt) | D34 => BCons D42 (mul3_B1 C1 xt) | D35 => BCons D45 (mul3_B1 C1 xt) | D36 => BCons D48 (mul3_B1 C1 xt) | D37 => BCons D51 (mul3_B1 C1 xt) | D38 => BCons D54 (mul3_B1 C1 xt) | D39 => BCons D57 (mul3_B1 C1 xt) | D40 => BCons D60 (mul3_B1 C1 xt) | D41 => BCons D63 (mul3_B1 C1 xt) | D42 => BCons D2 (mul3_B1 C2 xt) | D43 => BCons D5 (mul3_B1 C2 xt) | D44 => BCons D8 (mul3_B1 C2 xt) | D45 => BCons D11 (mul3_B1 C2 xt) | D46 => BCons D14 (mul3_B1 C2 xt) | D47 => BCons D17 (mul3_B1 C2 xt) | D48 => BCons D20 (mul3_B1 C2 xt) | D49 => BCons D23 (mul3_B1 C2 xt) | D50 => BCons D26 (mul3_B1 C2 xt) | D51 => BCons D29 (mul3_B1 C2 xt) | D52 => BCons D32 (mul3_B1 C2 xt) | D53 => BCons D35 (mul3_B1 C2 xt) | D54 => BCons D38 (mul3_B1 C2 xt) | D55 => BCons D41 (mul3_B1 C2 xt) | D56 => BCons D44 (mul3_B1 C2 xt) | D57 => BCons D47 (mul3_B1 C2 xt) | D58 => BCons D50 (mul3_B1 C2 xt) | D59 => BCons D53 (mul3_B1 C2 xt) | D60 => BCons D56 (mul3_B1 C2 xt) | D61 => BCons D59 (mul3_B1 C2 xt) | D62 => BCons D62 (mul3_B1 C2 xt) | D63 => BCons D1 (mul3_B1 C3 xt) end
    | C5 => match a with D0 => BCons D5 (mul3_B1 C0 xt) | D1 => BCons D8 (mul3_B1 C0 xt) | D2 => BCons D11 (mul3_B1 C0 xt) | D3 => BCons D14 (mul3_B1 C0 xt) | D4 => BCons D17 (mul3_B1 C0 xt) | D5 => BCons D20 (mul3_B1 C0 xt) | D6 => BCons D23 (mul3_B1 C0 xt) | D7 => BCons D26 (mul3_B1 C0 xt) | D8 => BCons D29 (mul3_B1 C0 xt) | D9 => BCons D32 (mul3_B1 C0 xt) | D10 => BCons D35 (mul3_B1 C0 xt) | D11 => BCons D38 (mul3_B1 C0 xt) | D12 => BCons D41 (mul3_B1 C0 xt) | D13 => BCons D44 (mul3_B1 C0 xt) | D14 => BCons D47 (mul3_B1 C0 xt) | D15 => BCons D50 (mul3_B1 C0 xt) | D16 => BCons D53 (mul3_B1 C0 xt) | D17 => BCons D56 (mul3_B1 C0 xt) | D18 => BCons D59 (mul3_B1 C0 xt) | D19 => BCons D62 (mul3_B1 C0 xt) | D20 => BCons D1 (mul3_B1 C1 xt) | D21 => BCons D4 (mul3_B1 C1 xt) | D22 => BCons D7 (mul3_B1 C1 xt) | D23 => BCons D10 (mul3_B1 C1 xt) | D24 => BCons D13 (mul3_B1 C1 xt) | D25 => BCons D16 (mul3_B1 C1 xt) | D26 => BCons D19 (mul3_B1 C1 xt) | D27 => BCons D22 (mul3_B1 C1 xt) | D28 => BCons D25 (mul3_B1 C1 xt) | D29 => BCons D28 (mul3_B1 C1 xt) | D30 => BCons D31 (mul3_B1 C1 xt) | D31 => BCons D34 (mul3_B1 C1 xt) | D32 => BCons D37 (mul3_B1 C1 xt) | D33 => BCons D40 (mul3_B1 C1 xt) | D34 => BCons D43 (mul3_B1 C1 xt) | D35 => BCons D46 (mul3_B1 C1 xt) | D36 => BCons D49 (mul3_B1 C1 xt) | D37 => BCons D52 (mul3_B1 C1 xt) | D38 => BCons D55 (mul3_B1 C1 xt) | D39 => BCons D58 (mul3_B1 C1 xt) | D40 => BCons D61 (mul3_B1 C1 xt) | D41 => match mul3_B1 C2 xt with BNil => BNil | zt => BCons D0 zt end | D42 => BCons D3 (mul3_B1 C2 xt) | D43 => BCons D6 (mul3_B1 C2 xt) | D44 => BCons D9 (mul3_B1 C2 xt) | D45 => BCons D12 (mul3_B1 C2 xt) | D46 => BCons D15 (mul3_B1 C2 xt) | D47 => BCons D18 (mul3_B1 C2 xt) | D48 => BCons D21 (mul3_B1 C2 xt) | D49 => BCons D24 (mul3_B1 C2 xt) | D50 => BCons D27 (mul3_B1 C2 xt) | D51 => BCons D30 (mul3_B1 C2 xt) | D52 => BCons D33 (mul3_B1 C2 xt) | D53 => BCons D36 (mul3_B1 C2 xt) | D54 => BCons D39 (mul3_B1 C2 xt) | D55 => BCons D42 (mul3_B1 C2 xt) | D56 => BCons D45 (mul3_B1 C2 xt) | D57 => BCons D48 (mul3_B1 C2 xt) | D58 => BCons D51 (mul3_B1 C2 xt) | D59 => BCons D54 (mul3_B1 C2 xt) | D60 => BCons D57 (mul3_B1 C2 xt) | D61 => BCons D60 (mul3_B1 C2 xt) | D62 => BCons D63 (mul3_B1 C2 xt) | D63 => BCons D2 (mul3_B1 C3 xt) end
    end
  | _ => match c with C0 => BNil | C1 => B1 | C2 => B2 | C3 => B3 | C4 => BCons D4 BNil | C5 => BCons D5 BNil end
  end.

Fixpoint mul3hAux_B1 (c : C6) (d0 : D64) (bt : Big) {struct bt} : Big :=
  match bt with
  | BCons d1 bt' =>
    let q0 := half64_q (isOdd64 d1) d0 in
    match c with
    | C0 => match q0 with D0 => match mul3hAux_B1 C0 d1 bt' with BNil => BNil | zt => BCons D0 zt end | D1 => BCons D3 (mul3hAux_B1 C0 d1 bt') | D2 => BCons D6 (mul3hAux_B1 C0 d1 bt') | D3 => BCons D9 (mul3hAux_B1 C0 d1 bt') | D4 => BCons D12 (mul3hAux_B1 C0 d1 bt') | D5 => BCons D15 (mul3hAux_B1 C0 d1 bt') | D6 => BCons D18 (mul3hAux_B1 C0 d1 bt') | D7 => BCons D21 (mul3hAux_B1 C0 d1 bt') | D8 => BCons D24 (mul3hAux_B1 C0 d1 bt') | D9 => BCons D27 (mul3hAux_B1 C0 d1 bt') | D10 => BCons D30 (mul3hAux_B1 C0 d1 bt') | D11 => BCons D33 (mul3hAux_B1 C0 d1 bt') | D12 => BCons D36 (mul3hAux_B1 C0 d1 bt') | D13 => BCons D39 (mul3hAux_B1 C0 d1 bt') | D14 => BCons D42 (mul3hAux_B1 C0 d1 bt') | D15 => BCons D45 (mul3hAux_B1 C0 d1 bt') | D16 => BCons D48 (mul3hAux_B1 C0 d1 bt') | D17 => BCons D51 (mul3hAux_B1 C0 d1 bt') | D18 => BCons D54 (mul3hAux_B1 C0 d1 bt') | D19 => BCons D57 (mul3hAux_B1 C0 d1 bt') | D20 => BCons D60 (mul3hAux_B1 C0 d1 bt') | D21 => BCons D63 (mul3hAux_B1 C0 d1 bt') | D22 => BCons D2 (mul3hAux_B1 C1 d1 bt') | D23 => BCons D5 (mul3hAux_B1 C1 d1 bt') | D24 => BCons D8 (mul3hAux_B1 C1 d1 bt') | D25 => BCons D11 (mul3hAux_B1 C1 d1 bt') | D26 => BCons D14 (mul3hAux_B1 C1 d1 bt') | D27 => BCons D17 (mul3hAux_B1 C1 d1 bt') | D28 => BCons D20 (mul3hAux_B1 C1 d1 bt') | D29 => BCons D23 (mul3hAux_B1 C1 d1 bt') | D30 => BCons D26 (mul3hAux_B1 C1 d1 bt') | D31 => BCons D29 (mul3hAux_B1 C1 d1 bt') | D32 => BCons D32 (mul3hAux_B1 C1 d1 bt') | D33 => BCons D35 (mul3hAux_B1 C1 d1 bt') | D34 => BCons D38 (mul3hAux_B1 C1 d1 bt') | D35 => BCons D41 (mul3hAux_B1 C1 d1 bt') | D36 => BCons D44 (mul3hAux_B1 C1 d1 bt') | D37 => BCons D47 (mul3hAux_B1 C1 d1 bt') | D38 => BCons D50 (mul3hAux_B1 C1 d1 bt') | D39 => BCons D53 (mul3hAux_B1 C1 d1 bt') | D40 => BCons D56 (mul3hAux_B1 C1 d1 bt') | D41 => BCons D59 (mul3hAux_B1 C1 d1 bt') | D42 => BCons D62 (mul3hAux_B1 C1 d1 bt') | D43 => BCons D1 (mul3hAux_B1 C2 d1 bt') | D44 => BCons D4 (mul3hAux_B1 C2 d1 bt') | D45 => BCons D7 (mul3hAux_B1 C2 d1 bt') | D46 => BCons D10 (mul3hAux_B1 C2 d1 bt') | D47 => BCons D13 (mul3hAux_B1 C2 d1 bt') | D48 => BCons D16 (mul3hAux_B1 C2 d1 bt') | D49 => BCons D19 (mul3hAux_B1 C2 d1 bt') | D50 => BCons D22 (mul3hAux_B1 C2 d1 bt') | D51 => BCons D25 (mul3hAux_B1 C2 d1 bt') | D52 => BCons D28 (mul3hAux_B1 C2 d1 bt') | D53 => BCons D31 (mul3hAux_B1 C2 d1 bt') | D54 => BCons D34 (mul3hAux_B1 C2 d1 bt') | D55 => BCons D37 (mul3hAux_B1 C2 d1 bt') | D56 => BCons D40 (mul3hAux_B1 C2 d1 bt') | D57 => BCons D43 (mul3hAux_B1 C2 d1 bt') | D58 => BCons D46 (mul3hAux_B1 C2 d1 bt') | D59 => BCons D49 (mul3hAux_B1 C2 d1 bt') | D60 => BCons D52 (mul3hAux_B1 C2 d1 bt') | D61 => BCons D55 (mul3hAux_B1 C2 d1 bt') | D62 => BCons D58 (mul3hAux_B1 C2 d1 bt') | D63 => BCons D61 (mul3hAux_B1 C2 d1 bt') end
    | C1 => match q0 with D0 => BCons D1 (mul3hAux_B1 C0 d1 bt') | D1 => BCons D4 (mul3hAux_B1 C0 d1 bt') | D2 => BCons D7 (mul3hAux_B1 C0 d1 bt') | D3 => BCons D10 (mul3hAux_B1 C0 d1 bt') | D4 => BCons D13 (mul3hAux_B1 C0 d1 bt') | D5 => BCons D16 (mul3hAux_B1 C0 d1 bt') | D6 => BCons D19 (mul3hAux_B1 C0 d1 bt') | D7 => BCons D22 (mul3hAux_B1 C0 d1 bt') | D8 => BCons D25 (mul3hAux_B1 C0 d1 bt') | D9 => BCons D28 (mul3hAux_B1 C0 d1 bt') | D10 => BCons D31 (mul3hAux_B1 C0 d1 bt') | D11 => BCons D34 (mul3hAux_B1 C0 d1 bt') | D12 => BCons D37 (mul3hAux_B1 C0 d1 bt') | D13 => BCons D40 (mul3hAux_B1 C0 d1 bt') | D14 => BCons D43 (mul3hAux_B1 C0 d1 bt') | D15 => BCons D46 (mul3hAux_B1 C0 d1 bt') | D16 => BCons D49 (mul3hAux_B1 C0 d1 bt') | D17 => BCons D52 (mul3hAux_B1 C0 d1 bt') | D18 => BCons D55 (mul3hAux_B1 C0 d1 bt') | D19 => BCons D58 (mul3hAux_B1 C0 d1 bt') | D20 => BCons D61 (mul3hAux_B1 C0 d1 bt') | D21 => match mul3hAux_B1 C1 d1 bt' with BNil => BNil | zt => BCons D0 zt end | D22 => BCons D3 (mul3hAux_B1 C1 d1 bt') | D23 => BCons D6 (mul3hAux_B1 C1 d1 bt') | D24 => BCons D9 (mul3hAux_B1 C1 d1 bt') | D25 => BCons D12 (mul3hAux_B1 C1 d1 bt') | D26 => BCons D15 (mul3hAux_B1 C1 d1 bt') | D27 => BCons D18 (mul3hAux_B1 C1 d1 bt') | D28 => BCons D21 (mul3hAux_B1 C1 d1 bt') | D29 => BCons D24 (mul3hAux_B1 C1 d1 bt') | D30 => BCons D27 (mul3hAux_B1 C1 d1 bt') | D31 => BCons D30 (mul3hAux_B1 C1 d1 bt') | D32 => BCons D33 (mul3hAux_B1 C1 d1 bt') | D33 => BCons D36 (mul3hAux_B1 C1 d1 bt') | D34 => BCons D39 (mul3hAux_B1 C1 d1 bt') | D35 => BCons D42 (mul3hAux_B1 C1 d1 bt') | D36 => BCons D45 (mul3hAux_B1 C1 d1 bt') | D37 => BCons D48 (mul3hAux_B1 C1 d1 bt') | D38 => BCons D51 (mul3hAux_B1 C1 d1 bt') | D39 => BCons D54 (mul3hAux_B1 C1 d1 bt') | D40 => BCons D57 (mul3hAux_B1 C1 d1 bt') | D41 => BCons D60 (mul3hAux_B1 C1 d1 bt') | D42 => BCons D63 (mul3hAux_B1 C1 d1 bt') | D43 => BCons D2 (mul3hAux_B1 C2 d1 bt') | D44 => BCons D5 (mul3hAux_B1 C2 d1 bt') | D45 => BCons D8 (mul3hAux_B1 C2 d1 bt') | D46 => BCons D11 (mul3hAux_B1 C2 d1 bt') | D47 => BCons D14 (mul3hAux_B1 C2 d1 bt') | D48 => BCons D17 (mul3hAux_B1 C2 d1 bt') | D49 => BCons D20 (mul3hAux_B1 C2 d1 bt') | D50 => BCons D23 (mul3hAux_B1 C2 d1 bt') | D51 => BCons D26 (mul3hAux_B1 C2 d1 bt') | D52 => BCons D29 (mul3hAux_B1 C2 d1 bt') | D53 => BCons D32 (mul3hAux_B1 C2 d1 bt') | D54 => BCons D35 (mul3hAux_B1 C2 d1 bt') | D55 => BCons D38 (mul3hAux_B1 C2 d1 bt') | D56 => BCons D41 (mul3hAux_B1 C2 d1 bt') | D57 => BCons D44 (mul3hAux_B1 C2 d1 bt') | D58 => BCons D47 (mul3hAux_B1 C2 d1 bt') | D59 => BCons D50 (mul3hAux_B1 C2 d1 bt') | D60 => BCons D53 (mul3hAux_B1 C2 d1 bt') | D61 => BCons D56 (mul3hAux_B1 C2 d1 bt') | D62 => BCons D59 (mul3hAux_B1 C2 d1 bt') | D63 => BCons D62 (mul3hAux_B1 C2 d1 bt') end
    | C2 => match q0 with D0 => BCons D2 (mul3hAux_B1 C0 d1 bt') | D1 => BCons D5 (mul3hAux_B1 C0 d1 bt') | D2 => BCons D8 (mul3hAux_B1 C0 d1 bt') | D3 => BCons D11 (mul3hAux_B1 C0 d1 bt') | D4 => BCons D14 (mul3hAux_B1 C0 d1 bt') | D5 => BCons D17 (mul3hAux_B1 C0 d1 bt') | D6 => BCons D20 (mul3hAux_B1 C0 d1 bt') | D7 => BCons D23 (mul3hAux_B1 C0 d1 bt') | D8 => BCons D26 (mul3hAux_B1 C0 d1 bt') | D9 => BCons D29 (mul3hAux_B1 C0 d1 bt') | D10 => BCons D32 (mul3hAux_B1 C0 d1 bt') | D11 => BCons D35 (mul3hAux_B1 C0 d1 bt') | D12 => BCons D38 (mul3hAux_B1 C0 d1 bt') | D13 => BCons D41 (mul3hAux_B1 C0 d1 bt') | D14 => BCons D44 (mul3hAux_B1 C0 d1 bt') | D15 => BCons D47 (mul3hAux_B1 C0 d1 bt') | D16 => BCons D50 (mul3hAux_B1 C0 d1 bt') | D17 => BCons D53 (mul3hAux_B1 C0 d1 bt') | D18 => BCons D56 (mul3hAux_B1 C0 d1 bt') | D19 => BCons D59 (mul3hAux_B1 C0 d1 bt') | D20 => BCons D62 (mul3hAux_B1 C0 d1 bt') | D21 => BCons D1 (mul3hAux_B1 C1 d1 bt') | D22 => BCons D4 (mul3hAux_B1 C1 d1 bt') | D23 => BCons D7 (mul3hAux_B1 C1 d1 bt') | D24 => BCons D10 (mul3hAux_B1 C1 d1 bt') | D25 => BCons D13 (mul3hAux_B1 C1 d1 bt') | D26 => BCons D16 (mul3hAux_B1 C1 d1 bt') | D27 => BCons D19 (mul3hAux_B1 C1 d1 bt') | D28 => BCons D22 (mul3hAux_B1 C1 d1 bt') | D29 => BCons D25 (mul3hAux_B1 C1 d1 bt') | D30 => BCons D28 (mul3hAux_B1 C1 d1 bt') | D31 => BCons D31 (mul3hAux_B1 C1 d1 bt') | D32 => BCons D34 (mul3hAux_B1 C1 d1 bt') | D33 => BCons D37 (mul3hAux_B1 C1 d1 bt') | D34 => BCons D40 (mul3hAux_B1 C1 d1 bt') | D35 => BCons D43 (mul3hAux_B1 C1 d1 bt') | D36 => BCons D46 (mul3hAux_B1 C1 d1 bt') | D37 => BCons D49 (mul3hAux_B1 C1 d1 bt') | D38 => BCons D52 (mul3hAux_B1 C1 d1 bt') | D39 => BCons D55 (mul3hAux_B1 C1 d1 bt') | D40 => BCons D58 (mul3hAux_B1 C1 d1 bt') | D41 => BCons D61 (mul3hAux_B1 C1 d1 bt') | D42 => match mul3hAux_B1 C2 d1 bt' with BNil => BNil | zt => BCons D0 zt end | D43 => BCons D3 (mul3hAux_B1 C2 d1 bt') | D44 => BCons D6 (mul3hAux_B1 C2 d1 bt') | D45 => BCons D9 (mul3hAux_B1 C2 d1 bt') | D46 => BCons D12 (mul3hAux_B1 C2 d1 bt') | D47 => BCons D15 (mul3hAux_B1 C2 d1 bt') | D48 => BCons D18 (mul3hAux_B1 C2 d1 bt') | D49 => BCons D21 (mul3hAux_B1 C2 d1 bt') | D50 => BCons D24 (mul3hAux_B1 C2 d1 bt') | D51 => BCons D27 (mul3hAux_B1 C2 d1 bt') | D52 => BCons D30 (mul3hAux_B1 C2 d1 bt') | D53 => BCons D33 (mul3hAux_B1 C2 d1 bt') | D54 => BCons D36 (mul3hAux_B1 C2 d1 bt') | D55 => BCons D39 (mul3hAux_B1 C2 d1 bt') | D56 => BCons D42 (mul3hAux_B1 C2 d1 bt') | D57 => BCons D45 (mul3hAux_B1 C2 d1 bt') | D58 => BCons D48 (mul3hAux_B1 C2 d1 bt') | D59 => BCons D51 (mul3hAux_B1 C2 d1 bt') | D60 => BCons D54 (mul3hAux_B1 C2 d1 bt') | D61 => BCons D57 (mul3hAux_B1 C2 d1 bt') | D62 => BCons D60 (mul3hAux_B1 C2 d1 bt') | D63 => BCons D63 (mul3hAux_B1 C2 d1 bt') end
    | C3 => match q0 with D0 => BCons D3 (mul3hAux_B1 C0 d1 bt') | D1 => BCons D6 (mul3hAux_B1 C0 d1 bt') | D2 => BCons D9 (mul3hAux_B1 C0 d1 bt') | D3 => BCons D12 (mul3hAux_B1 C0 d1 bt') | D4 => BCons D15 (mul3hAux_B1 C0 d1 bt') | D5 => BCons D18 (mul3hAux_B1 C0 d1 bt') | D6 => BCons D21 (mul3hAux_B1 C0 d1 bt') | D7 => BCons D24 (mul3hAux_B1 C0 d1 bt') | D8 => BCons D27 (mul3hAux_B1 C0 d1 bt') | D9 => BCons D30 (mul3hAux_B1 C0 d1 bt') | D10 => BCons D33 (mul3hAux_B1 C0 d1 bt') | D11 => BCons D36 (mul3hAux_B1 C0 d1 bt') | D12 => BCons D39 (mul3hAux_B1 C0 d1 bt') | D13 => BCons D42 (mul3hAux_B1 C0 d1 bt') | D14 => BCons D45 (mul3hAux_B1 C0 d1 bt') | D15 => BCons D48 (mul3hAux_B1 C0 d1 bt') | D16 => BCons D51 (mul3hAux_B1 C0 d1 bt') | D17 => BCons D54 (mul3hAux_B1 C0 d1 bt') | D18 => BCons D57 (mul3hAux_B1 C0 d1 bt') | D19 => BCons D60 (mul3hAux_B1 C0 d1 bt') | D20 => BCons D63 (mul3hAux_B1 C0 d1 bt') | D21 => BCons D2 (mul3hAux_B1 C1 d1 bt') | D22 => BCons D5 (mul3hAux_B1 C1 d1 bt') | D23 => BCons D8 (mul3hAux_B1 C1 d1 bt') | D24 => BCons D11 (mul3hAux_B1 C1 d1 bt') | D25 => BCons D14 (mul3hAux_B1 C1 d1 bt') | D26 => BCons D17 (mul3hAux_B1 C1 d1 bt') | D27 => BCons D20 (mul3hAux_B1 C1 d1 bt') | D28 => BCons D23 (mul3hAux_B1 C1 d1 bt') | D29 => BCons D26 (mul3hAux_B1 C1 d1 bt') | D30 => BCons D29 (mul3hAux_B1 C1 d1 bt') | D31 => BCons D32 (mul3hAux_B1 C1 d1 bt') | D32 => BCons D35 (mul3hAux_B1 C1 d1 bt') | D33 => BCons D38 (mul3hAux_B1 C1 d1 bt') | D34 => BCons D41 (mul3hAux_B1 C1 d1 bt') | D35 => BCons D44 (mul3hAux_B1 C1 d1 bt') | D36 => BCons D47 (mul3hAux_B1 C1 d1 bt') | D37 => BCons D50 (mul3hAux_B1 C1 d1 bt') | D38 => BCons D53 (mul3hAux_B1 C1 d1 bt') | D39 => BCons D56 (mul3hAux_B1 C1 d1 bt') | D40 => BCons D59 (mul3hAux_B1 C1 d1 bt') | D41 => BCons D62 (mul3hAux_B1 C1 d1 bt') | D42 => BCons D1 (mul3hAux_B1 C2 d1 bt') | D43 => BCons D4 (mul3hAux_B1 C2 d1 bt') | D44 => BCons D7 (mul3hAux_B1 C2 d1 bt') | D45 => BCons D10 (mul3hAux_B1 C2 d1 bt') | D46 => BCons D13 (mul3hAux_B1 C2 d1 bt') | D47 => BCons D16 (mul3hAux_B1 C2 d1 bt') | D48 => BCons D19 (mul3hAux_B1 C2 d1 bt') | D49 => BCons D22 (mul3hAux_B1 C2 d1 bt') | D50 => BCons D25 (mul3hAux_B1 C2 d1 bt') | D51 => BCons D28 (mul3hAux_B1 C2 d1 bt') | D52 => BCons D31 (mul3hAux_B1 C2 d1 bt') | D53 => BCons D34 (mul3hAux_B1 C2 d1 bt') | D54 => BCons D37 (mul3hAux_B1 C2 d1 bt') | D55 => BCons D40 (mul3hAux_B1 C2 d1 bt') | D56 => BCons D43 (mul3hAux_B1 C2 d1 bt') | D57 => BCons D46 (mul3hAux_B1 C2 d1 bt') | D58 => BCons D49 (mul3hAux_B1 C2 d1 bt') | D59 => BCons D52 (mul3hAux_B1 C2 d1 bt') | D60 => BCons D55 (mul3hAux_B1 C2 d1 bt') | D61 => BCons D58 (mul3hAux_B1 C2 d1 bt') | D62 => BCons D61 (mul3hAux_B1 C2 d1 bt') | D63 => match mul3hAux_B1 C3 d1 bt' with BNil => BNil | zt => BCons D0 zt end end
    | C4 => match q0 with D0 => BCons D4 (mul3hAux_B1 C0 d1 bt') | D1 => BCons D7 (mul3hAux_B1 C0 d1 bt') | D2 => BCons D10 (mul3hAux_B1 C0 d1 bt') | D3 => BCons D13 (mul3hAux_B1 C0 d1 bt') | D4 => BCons D16 (mul3hAux_B1 C0 d1 bt') | D5 => BCons D19 (mul3hAux_B1 C0 d1 bt') | D6 => BCons D22 (mul3hAux_B1 C0 d1 bt') | D7 => BCons D25 (mul3hAux_B1 C0 d1 bt') | D8 => BCons D28 (mul3hAux_B1 C0 d1 bt') | D9 => BCons D31 (mul3hAux_B1 C0 d1 bt') | D10 => BCons D34 (mul3hAux_B1 C0 d1 bt') | D11 => BCons D37 (mul3hAux_B1 C0 d1 bt') | D12 => BCons D40 (mul3hAux_B1 C0 d1 bt') | D13 => BCons D43 (mul3hAux_B1 C0 d1 bt') | D14 => BCons D46 (mul3hAux_B1 C0 d1 bt') | D15 => BCons D49 (mul3hAux_B1 C0 d1 bt') | D16 => BCons D52 (mul3hAux_B1 C0 d1 bt') | D17 => BCons D55 (mul3hAux_B1 C0 d1 bt') | D18 => BCons D58 (mul3hAux_B1 C0 d1 bt') | D19 => BCons D61 (mul3hAux_B1 C0 d1 bt') | D20 => match mul3hAux_B1 C1 d1 bt' with BNil => BNil | zt => BCons D0 zt end | D21 => BCons D3 (mul3hAux_B1 C1 d1 bt') | D22 => BCons D6 (mul3hAux_B1 C1 d1 bt') | D23 => BCons D9 (mul3hAux_B1 C1 d1 bt') | D24 => BCons D12 (mul3hAux_B1 C1 d1 bt') | D25 => BCons D15 (mul3hAux_B1 C1 d1 bt') | D26 => BCons D18 (mul3hAux_B1 C1 d1 bt') | D27 => BCons D21 (mul3hAux_B1 C1 d1 bt') | D28 => BCons D24 (mul3hAux_B1 C1 d1 bt') | D29 => BCons D27 (mul3hAux_B1 C1 d1 bt') | D30 => BCons D30 (mul3hAux_B1 C1 d1 bt') | D31 => BCons D33 (mul3hAux_B1 C1 d1 bt') | D32 => BCons D36 (mul3hAux_B1 C1 d1 bt') | D33 => BCons D39 (mul3hAux_B1 C1 d1 bt') | D34 => BCons D42 (mul3hAux_B1 C1 d1 bt') | D35 => BCons D45 (mul3hAux_B1 C1 d1 bt') | D36 => BCons D48 (mul3hAux_B1 C1 d1 bt') | D37 => BCons D51 (mul3hAux_B1 C1 d1 bt') | D38 => BCons D54 (mul3hAux_B1 C1 d1 bt') | D39 => BCons D57 (mul3hAux_B1 C1 d1 bt') | D40 => BCons D60 (mul3hAux_B1 C1 d1 bt') | D41 => BCons D63 (mul3hAux_B1 C1 d1 bt') | D42 => BCons D2 (mul3hAux_B1 C2 d1 bt') | D43 => BCons D5 (mul3hAux_B1 C2 d1 bt') | D44 => BCons D8 (mul3hAux_B1 C2 d1 bt') | D45 => BCons D11 (mul3hAux_B1 C2 d1 bt') | D46 => BCons D14 (mul3hAux_B1 C2 d1 bt') | D47 => BCons D17 (mul3hAux_B1 C2 d1 bt') | D48 => BCons D20 (mul3hAux_B1 C2 d1 bt') | D49 => BCons D23 (mul3hAux_B1 C2 d1 bt') | D50 => BCons D26 (mul3hAux_B1 C2 d1 bt') | D51 => BCons D29 (mul3hAux_B1 C2 d1 bt') | D52 => BCons D32 (mul3hAux_B1 C2 d1 bt') | D53 => BCons D35 (mul3hAux_B1 C2 d1 bt') | D54 => BCons D38 (mul3hAux_B1 C2 d1 bt') | D55 => BCons D41 (mul3hAux_B1 C2 d1 bt') | D56 => BCons D44 (mul3hAux_B1 C2 d1 bt') | D57 => BCons D47 (mul3hAux_B1 C2 d1 bt') | D58 => BCons D50 (mul3hAux_B1 C2 d1 bt') | D59 => BCons D53 (mul3hAux_B1 C2 d1 bt') | D60 => BCons D56 (mul3hAux_B1 C2 d1 bt') | D61 => BCons D59 (mul3hAux_B1 C2 d1 bt') | D62 => BCons D62 (mul3hAux_B1 C2 d1 bt') | D63 => BCons D1 (mul3hAux_B1 C3 d1 bt') end
    | C5 => match q0 with D0 => BCons D5 (mul3hAux_B1 C0 d1 bt') | D1 => BCons D8 (mul3hAux_B1 C0 d1 bt') | D2 => BCons D11 (mul3hAux_B1 C0 d1 bt') | D3 => BCons D14 (mul3hAux_B1 C0 d1 bt') | D4 => BCons D17 (mul3hAux_B1 C0 d1 bt') | D5 => BCons D20 (mul3hAux_B1 C0 d1 bt') | D6 => BCons D23 (mul3hAux_B1 C0 d1 bt') | D7 => BCons D26 (mul3hAux_B1 C0 d1 bt') | D8 => BCons D29 (mul3hAux_B1 C0 d1 bt') | D9 => BCons D32 (mul3hAux_B1 C0 d1 bt') | D10 => BCons D35 (mul3hAux_B1 C0 d1 bt') | D11 => BCons D38 (mul3hAux_B1 C0 d1 bt') | D12 => BCons D41 (mul3hAux_B1 C0 d1 bt') | D13 => BCons D44 (mul3hAux_B1 C0 d1 bt') | D14 => BCons D47 (mul3hAux_B1 C0 d1 bt') | D15 => BCons D50 (mul3hAux_B1 C0 d1 bt') | D16 => BCons D53 (mul3hAux_B1 C0 d1 bt') | D17 => BCons D56 (mul3hAux_B1 C0 d1 bt') | D18 => BCons D59 (mul3hAux_B1 C0 d1 bt') | D19 => BCons D62 (mul3hAux_B1 C0 d1 bt') | D20 => BCons D1 (mul3hAux_B1 C1 d1 bt') | D21 => BCons D4 (mul3hAux_B1 C1 d1 bt') | D22 => BCons D7 (mul3hAux_B1 C1 d1 bt') | D23 => BCons D10 (mul3hAux_B1 C1 d1 bt') | D24 => BCons D13 (mul3hAux_B1 C1 d1 bt') | D25 => BCons D16 (mul3hAux_B1 C1 d1 bt') | D26 => BCons D19 (mul3hAux_B1 C1 d1 bt') | D27 => BCons D22 (mul3hAux_B1 C1 d1 bt') | D28 => BCons D25 (mul3hAux_B1 C1 d1 bt') | D29 => BCons D28 (mul3hAux_B1 C1 d1 bt') | D30 => BCons D31 (mul3hAux_B1 C1 d1 bt') | D31 => BCons D34 (mul3hAux_B1 C1 d1 bt') | D32 => BCons D37 (mul3hAux_B1 C1 d1 bt') | D33 => BCons D40 (mul3hAux_B1 C1 d1 bt') | D34 => BCons D43 (mul3hAux_B1 C1 d1 bt') | D35 => BCons D46 (mul3hAux_B1 C1 d1 bt') | D36 => BCons D49 (mul3hAux_B1 C1 d1 bt') | D37 => BCons D52 (mul3hAux_B1 C1 d1 bt') | D38 => BCons D55 (mul3hAux_B1 C1 d1 bt') | D39 => BCons D58 (mul3hAux_B1 C1 d1 bt') | D40 => BCons D61 (mul3hAux_B1 C1 d1 bt') | D41 => match mul3hAux_B1 C2 d1 bt' with BNil => BNil | zt => BCons D0 zt end | D42 => BCons D3 (mul3hAux_B1 C2 d1 bt') | D43 => BCons D6 (mul3hAux_B1 C2 d1 bt') | D44 => BCons D9 (mul3hAux_B1 C2 d1 bt') | D45 => BCons D12 (mul3hAux_B1 C2 d1 bt') | D46 => BCons D15 (mul3hAux_B1 C2 d1 bt') | D47 => BCons D18 (mul3hAux_B1 C2 d1 bt') | D48 => BCons D21 (mul3hAux_B1 C2 d1 bt') | D49 => BCons D24 (mul3hAux_B1 C2 d1 bt') | D50 => BCons D27 (mul3hAux_B1 C2 d1 bt') | D51 => BCons D30 (mul3hAux_B1 C2 d1 bt') | D52 => BCons D33 (mul3hAux_B1 C2 d1 bt') | D53 => BCons D36 (mul3hAux_B1 C2 d1 bt') | D54 => BCons D39 (mul3hAux_B1 C2 d1 bt') | D55 => BCons D42 (mul3hAux_B1 C2 d1 bt') | D56 => BCons D45 (mul3hAux_B1 C2 d1 bt') | D57 => BCons D48 (mul3hAux_B1 C2 d1 bt') | D58 => BCons D51 (mul3hAux_B1 C2 d1 bt') | D59 => BCons D54 (mul3hAux_B1 C2 d1 bt') | D60 => BCons D57 (mul3hAux_B1 C2 d1 bt') | D61 => BCons D60 (mul3hAux_B1 C2 d1 bt') | D62 => BCons D63 (mul3hAux_B1 C2 d1 bt') | D63 => BCons D2 (mul3hAux_B1 C3 d1 bt') end
    end
  | _ =>
    let q0 := half64_q false d0 in
    match c with
    | C0 => match q0 with D0 => BNil | D1 => BCons D3 BNil | D2 => BCons D6 BNil | D3 => BCons D9 BNil | D4 => BCons D12 BNil | D5 => BCons D15 BNil | D6 => BCons D18 BNil | D7 => BCons D21 BNil | D8 => BCons D24 BNil | D9 => BCons D27 BNil | D10 => BCons D30 BNil | D11 => BCons D33 BNil | D12 => BCons D36 BNil | D13 => BCons D39 BNil | D14 => BCons D42 BNil | D15 => BCons D45 BNil | D16 => BCons D48 BNil | D17 => BCons D51 BNil | D18 => BCons D54 BNil | D19 => BCons D57 BNil | D20 => BCons D60 BNil | D21 => BCons D63 BNil | D22 => BCons D2 (BCons D1 BNil) | D23 => BCons D5 (BCons D1 BNil) | D24 => BCons D8 (BCons D1 BNil) | D25 => BCons D11 (BCons D1 BNil) | D26 => BCons D14 (BCons D1 BNil) | D27 => BCons D17 (BCons D1 BNil) | D28 => BCons D20 (BCons D1 BNil) | D29 => BCons D23 (BCons D1 BNil) | D30 => BCons D26 (BCons D1 BNil) | D31 => BCons D29 (BCons D1 BNil) | D32 => BCons D32 (BCons D1 BNil) | D33 => BCons D35 (BCons D1 BNil) | D34 => BCons D38 (BCons D1 BNil) | D35 => BCons D41 (BCons D1 BNil) | D36 => BCons D44 (BCons D1 BNil) | D37 => BCons D47 (BCons D1 BNil) | D38 => BCons D50 (BCons D1 BNil) | D39 => BCons D53 (BCons D1 BNil) | D40 => BCons D56 (BCons D1 BNil) | D41 => BCons D59 (BCons D1 BNil) | D42 => BCons D62 (BCons D1 BNil) | D43 => BCons D1 (BCons D2 BNil) | D44 => BCons D4 (BCons D2 BNil) | D45 => BCons D7 (BCons D2 BNil) | D46 => BCons D10 (BCons D2 BNil) | D47 => BCons D13 (BCons D2 BNil) | D48 => BCons D16 (BCons D2 BNil) | D49 => BCons D19 (BCons D2 BNil) | D50 => BCons D22 (BCons D2 BNil) | D51 => BCons D25 (BCons D2 BNil) | D52 => BCons D28 (BCons D2 BNil) | D53 => BCons D31 (BCons D2 BNil) | D54 => BCons D34 (BCons D2 BNil) | D55 => BCons D37 (BCons D2 BNil) | D56 => BCons D40 (BCons D2 BNil) | D57 => BCons D43 (BCons D2 BNil) | D58 => BCons D46 (BCons D2 BNil) | D59 => BCons D49 (BCons D2 BNil) | D60 => BCons D52 (BCons D2 BNil) | D61 => BCons D55 (BCons D2 BNil) | D62 => BCons D58 (BCons D2 BNil) | D63 => BCons D61 (BCons D2 BNil) end
    | C1 => match q0 with D0 => BCons D1 BNil | D1 => BCons D4 BNil | D2 => BCons D7 BNil | D3 => BCons D10 BNil | D4 => BCons D13 BNil | D5 => BCons D16 BNil | D6 => BCons D19 BNil | D7 => BCons D22 BNil | D8 => BCons D25 BNil | D9 => BCons D28 BNil | D10 => BCons D31 BNil | D11 => BCons D34 BNil | D12 => BCons D37 BNil | D13 => BCons D40 BNil | D14 => BCons D43 BNil | D15 => BCons D46 BNil | D16 => BCons D49 BNil | D17 => BCons D52 BNil | D18 => BCons D55 BNil | D19 => BCons D58 BNil | D20 => BCons D61 BNil | D21 => BCons D0 (BCons D1 BNil) | D22 => BCons D3 (BCons D1 BNil) | D23 => BCons D6 (BCons D1 BNil) | D24 => BCons D9 (BCons D1 BNil) | D25 => BCons D12 (BCons D1 BNil) | D26 => BCons D15 (BCons D1 BNil) | D27 => BCons D18 (BCons D1 BNil) | D28 => BCons D21 (BCons D1 BNil) | D29 => BCons D24 (BCons D1 BNil) | D30 => BCons D27 (BCons D1 BNil) | D31 => BCons D30 (BCons D1 BNil) | D32 => BCons D33 (BCons D1 BNil) | D33 => BCons D36 (BCons D1 BNil) | D34 => BCons D39 (BCons D1 BNil) | D35 => BCons D42 (BCons D1 BNil) | D36 => BCons D45 (BCons D1 BNil) | D37 => BCons D48 (BCons D1 BNil) | D38 => BCons D51 (BCons D1 BNil) | D39 => BCons D54 (BCons D1 BNil) | D40 => BCons D57 (BCons D1 BNil) | D41 => BCons D60 (BCons D1 BNil) | D42 => BCons D63 (BCons D1 BNil) | D43 => BCons D2 (BCons D2 BNil) | D44 => BCons D5 (BCons D2 BNil) | D45 => BCons D8 (BCons D2 BNil) | D46 => BCons D11 (BCons D2 BNil) | D47 => BCons D14 (BCons D2 BNil) | D48 => BCons D17 (BCons D2 BNil) | D49 => BCons D20 (BCons D2 BNil) | D50 => BCons D23 (BCons D2 BNil) | D51 => BCons D26 (BCons D2 BNil) | D52 => BCons D29 (BCons D2 BNil) | D53 => BCons D32 (BCons D2 BNil) | D54 => BCons D35 (BCons D2 BNil) | D55 => BCons D38 (BCons D2 BNil) | D56 => BCons D41 (BCons D2 BNil) | D57 => BCons D44 (BCons D2 BNil) | D58 => BCons D47 (BCons D2 BNil) | D59 => BCons D50 (BCons D2 BNil) | D60 => BCons D53 (BCons D2 BNil) | D61 => BCons D56 (BCons D2 BNil) | D62 => BCons D59 (BCons D2 BNil) | D63 => BCons D62 (BCons D2 BNil) end
    | C2 => match q0 with D0 => BCons D2 BNil | D1 => BCons D5 BNil | D2 => BCons D8 BNil | D3 => BCons D11 BNil | D4 => BCons D14 BNil | D5 => BCons D17 BNil | D6 => BCons D20 BNil | D7 => BCons D23 BNil | D8 => BCons D26 BNil | D9 => BCons D29 BNil | D10 => BCons D32 BNil | D11 => BCons D35 BNil | D12 => BCons D38 BNil | D13 => BCons D41 BNil | D14 => BCons D44 BNil | D15 => BCons D47 BNil | D16 => BCons D50 BNil | D17 => BCons D53 BNil | D18 => BCons D56 BNil | D19 => BCons D59 BNil | D20 => BCons D62 BNil | D21 => BCons D1 (BCons D1 BNil) | D22 => BCons D4 (BCons D1 BNil) | D23 => BCons D7 (BCons D1 BNil) | D24 => BCons D10 (BCons D1 BNil) | D25 => BCons D13 (BCons D1 BNil) | D26 => BCons D16 (BCons D1 BNil) | D27 => BCons D19 (BCons D1 BNil) | D28 => BCons D22 (BCons D1 BNil) | D29 => BCons D25 (BCons D1 BNil) | D30 => BCons D28 (BCons D1 BNil) | D31 => BCons D31 (BCons D1 BNil) | D32 => BCons D34 (BCons D1 BNil) | D33 => BCons D37 (BCons D1 BNil) | D34 => BCons D40 (BCons D1 BNil) | D35 => BCons D43 (BCons D1 BNil) | D36 => BCons D46 (BCons D1 BNil) | D37 => BCons D49 (BCons D1 BNil) | D38 => BCons D52 (BCons D1 BNil) | D39 => BCons D55 (BCons D1 BNil) | D40 => BCons D58 (BCons D1 BNil) | D41 => BCons D61 (BCons D1 BNil) | D42 => BCons D0 (BCons D2 BNil) | D43 => BCons D3 (BCons D2 BNil) | D44 => BCons D6 (BCons D2 BNil) | D45 => BCons D9 (BCons D2 BNil) | D46 => BCons D12 (BCons D2 BNil) | D47 => BCons D15 (BCons D2 BNil) | D48 => BCons D18 (BCons D2 BNil) | D49 => BCons D21 (BCons D2 BNil) | D50 => BCons D24 (BCons D2 BNil) | D51 => BCons D27 (BCons D2 BNil) | D52 => BCons D30 (BCons D2 BNil) | D53 => BCons D33 (BCons D2 BNil) | D54 => BCons D36 (BCons D2 BNil) | D55 => BCons D39 (BCons D2 BNil) | D56 => BCons D42 (BCons D2 BNil) | D57 => BCons D45 (BCons D2 BNil) | D58 => BCons D48 (BCons D2 BNil) | D59 => BCons D51 (BCons D2 BNil) | D60 => BCons D54 (BCons D2 BNil) | D61 => BCons D57 (BCons D2 BNil) | D62 => BCons D60 (BCons D2 BNil) | D63 => BCons D63 (BCons D2 BNil) end
    | C3 => match q0 with D0 => BCons D3 BNil | D1 => BCons D6 BNil | D2 => BCons D9 BNil | D3 => BCons D12 BNil | D4 => BCons D15 BNil | D5 => BCons D18 BNil | D6 => BCons D21 BNil | D7 => BCons D24 BNil | D8 => BCons D27 BNil | D9 => BCons D30 BNil | D10 => BCons D33 BNil | D11 => BCons D36 BNil | D12 => BCons D39 BNil | D13 => BCons D42 BNil | D14 => BCons D45 BNil | D15 => BCons D48 BNil | D16 => BCons D51 BNil | D17 => BCons D54 BNil | D18 => BCons D57 BNil | D19 => BCons D60 BNil | D20 => BCons D63 BNil | D21 => BCons D2 (BCons D1 BNil) | D22 => BCons D5 (BCons D1 BNil) | D23 => BCons D8 (BCons D1 BNil) | D24 => BCons D11 (BCons D1 BNil) | D25 => BCons D14 (BCons D1 BNil) | D26 => BCons D17 (BCons D1 BNil) | D27 => BCons D20 (BCons D1 BNil) | D28 => BCons D23 (BCons D1 BNil) | D29 => BCons D26 (BCons D1 BNil) | D30 => BCons D29 (BCons D1 BNil) | D31 => BCons D32 (BCons D1 BNil) | D32 => BCons D35 (BCons D1 BNil) | D33 => BCons D38 (BCons D1 BNil) | D34 => BCons D41 (BCons D1 BNil) | D35 => BCons D44 (BCons D1 BNil) | D36 => BCons D47 (BCons D1 BNil) | D37 => BCons D50 (BCons D1 BNil) | D38 => BCons D53 (BCons D1 BNil) | D39 => BCons D56 (BCons D1 BNil) | D40 => BCons D59 (BCons D1 BNil) | D41 => BCons D62 (BCons D1 BNil) | D42 => BCons D1 (BCons D2 BNil) | D43 => BCons D4 (BCons D2 BNil) | D44 => BCons D7 (BCons D2 BNil) | D45 => BCons D10 (BCons D2 BNil) | D46 => BCons D13 (BCons D2 BNil) | D47 => BCons D16 (BCons D2 BNil) | D48 => BCons D19 (BCons D2 BNil) | D49 => BCons D22 (BCons D2 BNil) | D50 => BCons D25 (BCons D2 BNil) | D51 => BCons D28 (BCons D2 BNil) | D52 => BCons D31 (BCons D2 BNil) | D53 => BCons D34 (BCons D2 BNil) | D54 => BCons D37 (BCons D2 BNil) | D55 => BCons D40 (BCons D2 BNil) | D56 => BCons D43 (BCons D2 BNil) | D57 => BCons D46 (BCons D2 BNil) | D58 => BCons D49 (BCons D2 BNil) | D59 => BCons D52 (BCons D2 BNil) | D60 => BCons D55 (BCons D2 BNil) | D61 => BCons D58 (BCons D2 BNil) | D62 => BCons D61 (BCons D2 BNil) | D63 => BCons D0 (BCons D3 BNil) end
    | C4 => match q0 with D0 => BCons D4 BNil | D1 => BCons D7 BNil | D2 => BCons D10 BNil | D3 => BCons D13 BNil | D4 => BCons D16 BNil | D5 => BCons D19 BNil | D6 => BCons D22 BNil | D7 => BCons D25 BNil | D8 => BCons D28 BNil | D9 => BCons D31 BNil | D10 => BCons D34 BNil | D11 => BCons D37 BNil | D12 => BCons D40 BNil | D13 => BCons D43 BNil | D14 => BCons D46 BNil | D15 => BCons D49 BNil | D16 => BCons D52 BNil | D17 => BCons D55 BNil | D18 => BCons D58 BNil | D19 => BCons D61 BNil | D20 => BCons D0 (BCons D1 BNil) | D21 => BCons D3 (BCons D1 BNil) | D22 => BCons D6 (BCons D1 BNil) | D23 => BCons D9 (BCons D1 BNil) | D24 => BCons D12 (BCons D1 BNil) | D25 => BCons D15 (BCons D1 BNil) | D26 => BCons D18 (BCons D1 BNil) | D27 => BCons D21 (BCons D1 BNil) | D28 => BCons D24 (BCons D1 BNil) | D29 => BCons D27 (BCons D1 BNil) | D30 => BCons D30 (BCons D1 BNil) | D31 => BCons D33 (BCons D1 BNil) | D32 => BCons D36 (BCons D1 BNil) | D33 => BCons D39 (BCons D1 BNil) | D34 => BCons D42 (BCons D1 BNil) | D35 => BCons D45 (BCons D1 BNil) | D36 => BCons D48 (BCons D1 BNil) | D37 => BCons D51 (BCons D1 BNil) | D38 => BCons D54 (BCons D1 BNil) | D39 => BCons D57 (BCons D1 BNil) | D40 => BCons D60 (BCons D1 BNil) | D41 => BCons D63 (BCons D1 BNil) | D42 => BCons D2 (BCons D2 BNil) | D43 => BCons D5 (BCons D2 BNil) | D44 => BCons D8 (BCons D2 BNil) | D45 => BCons D11 (BCons D2 BNil) | D46 => BCons D14 (BCons D2 BNil) | D47 => BCons D17 (BCons D2 BNil) | D48 => BCons D20 (BCons D2 BNil) | D49 => BCons D23 (BCons D2 BNil) | D50 => BCons D26 (BCons D2 BNil) | D51 => BCons D29 (BCons D2 BNil) | D52 => BCons D32 (BCons D2 BNil) | D53 => BCons D35 (BCons D2 BNil) | D54 => BCons D38 (BCons D2 BNil) | D55 => BCons D41 (BCons D2 BNil) | D56 => BCons D44 (BCons D2 BNil) | D57 => BCons D47 (BCons D2 BNil) | D58 => BCons D50 (BCons D2 BNil) | D59 => BCons D53 (BCons D2 BNil) | D60 => BCons D56 (BCons D2 BNil) | D61 => BCons D59 (BCons D2 BNil) | D62 => BCons D62 (BCons D2 BNil) | D63 => BCons D1 (BCons D3 BNil) end
    | C5 => match q0 with D0 => BCons D5 BNil | D1 => BCons D8 BNil | D2 => BCons D11 BNil | D3 => BCons D14 BNil | D4 => BCons D17 BNil | D5 => BCons D20 BNil | D6 => BCons D23 BNil | D7 => BCons D26 BNil | D8 => BCons D29 BNil | D9 => BCons D32 BNil | D10 => BCons D35 BNil | D11 => BCons D38 BNil | D12 => BCons D41 BNil | D13 => BCons D44 BNil | D14 => BCons D47 BNil | D15 => BCons D50 BNil | D16 => BCons D53 BNil | D17 => BCons D56 BNil | D18 => BCons D59 BNil | D19 => BCons D62 BNil | D20 => BCons D1 (BCons D1 BNil) | D21 => BCons D4 (BCons D1 BNil) | D22 => BCons D7 (BCons D1 BNil) | D23 => BCons D10 (BCons D1 BNil) | D24 => BCons D13 (BCons D1 BNil) | D25 => BCons D16 (BCons D1 BNil) | D26 => BCons D19 (BCons D1 BNil) | D27 => BCons D22 (BCons D1 BNil) | D28 => BCons D25 (BCons D1 BNil) | D29 => BCons D28 (BCons D1 BNil) | D30 => BCons D31 (BCons D1 BNil) | D31 => BCons D34 (BCons D1 BNil) | D32 => BCons D37 (BCons D1 BNil) | D33 => BCons D40 (BCons D1 BNil) | D34 => BCons D43 (BCons D1 BNil) | D35 => BCons D46 (BCons D1 BNil) | D36 => BCons D49 (BCons D1 BNil) | D37 => BCons D52 (BCons D1 BNil) | D38 => BCons D55 (BCons D1 BNil) | D39 => BCons D58 (BCons D1 BNil) | D40 => BCons D61 (BCons D1 BNil) | D41 => BCons D0 (BCons D2 BNil) | D42 => BCons D3 (BCons D2 BNil) | D43 => BCons D6 (BCons D2 BNil) | D44 => BCons D9 (BCons D2 BNil) | D45 => BCons D12 (BCons D2 BNil) | D46 => BCons D15 (BCons D2 BNil) | D47 => BCons D18 (BCons D2 BNil) | D48 => BCons D21 (BCons D2 BNil) | D49 => BCons D24 (BCons D2 BNil) | D50 => BCons D27 (BCons D2 BNil) | D51 => BCons D30 (BCons D2 BNil) | D52 => BCons D33 (BCons D2 BNil) | D53 => BCons D36 (BCons D2 BNil) | D54 => BCons D39 (BCons D2 BNil) | D55 => BCons D42 (BCons D2 BNil) | D56 => BCons D45 (BCons D2 BNil) | D57 => BCons D48 (BCons D2 BNil) | D58 => BCons D51 (BCons D2 BNil) | D59 => BCons D54 (BCons D2 BNil) | D60 => BCons D57 (BCons D2 BNil) | D61 => BCons D60 (BCons D2 BNil) | D62 => BCons D63 (BCons D2 BNil) | D63 => BCons D2 (BCons D3 BNil) end
    end
  end.

Definition mul3h_B1 (c : C6) (b : Big) : Big :=
  match b with
  | BCons d0 bt => mul3hAux_B1 c d0 bt
  | _ => match c with C0 => BNil | C1 => B1 | C2 => B2 | C3 => B3 | C4 => BCons D4 BNil | C5 => BCons D5 BNil end
  end.

Fixpoint runCleanLoop_B1 (steps : nat) (b0 : Big) (lt : LStack) (isC1 : bool) (c0 : Big) (rt : RStack) : HybState :=
  match steps with
  | O => HClean (LC b0 lt) (RC isC1 c0 rt)
  | S steps' =>
    let diff := sub2x_B1 C0 b0 c0 in
    if isZeroB diff then
      match lt with
      | LC b1 lt2 =>
        let nb1 := subSmall3B b1 in
        if isZeroB nb1 then HGen QF true [TokW B3] (LC b0 lt) [] (RC isC1 c0 rt)
        else
          if evenB b0 then
            let nc0 := subHalf_B1 false c0 b0 in
            if isZeroB nc0 then HGen QF true [TokW B3] (LC b0 lt) [] (RC isC1 c0 rt)
            else runCleanLoop_B1 steps' nb1 lt2 true (mul3h_B1 C3 b0) (RC isC1 nc0 rt)
          else
            let nc0 := subHalf_B1 true c0 b0 in
            if isZeroB nc0 then HGen QF true [TokW B3] (LC b0 lt) [] (RC isC1 c0 rt)
            else runCleanLoop_B1 steps' nb1 lt2 false (mul3h_B1 C5 b0) (RC isC1 nc0 rt)
      | _ => HGen QF true [TokW B3] (LC b0 lt) [] (RC isC1 c0 rt)
      end
    else
      if isC1 then
        let nb0 := subSmall2B diff in
        if isZeroB nb0 then HGen QF true [TokW B3] (LC b0 lt) [] (RC true c0 rt)
        else
          match rt with
          | RC t1 c1 rt2 =>
            let nc1 := subSmall2B c1 in
            if isZeroB nc1 then HGen QF true [TokW B3] (LC b0 lt) [] (RC true c0 rt)
            else runCleanLoop_B1 steps' (mul3_B1 C4 c0) (LC nb0 lt) t1 nc1 rt2
          | _ => HGen QF true [TokW B3] (LC b0 lt) [] (RC true c0 rt)
          end
      else
        if isZeroB c0 then HGen QF true [TokW B3] (LC b0 lt) [] (RC false c0 rt)
        else
          match rt with
          | RC t1 c1 rt2 =>
            let nc1 := subSmall1B c1 in
            if isZeroB nc1 then HGen QF true [TokW B3] (LC b0 lt) [] (RC false c0 rt)
            else runCleanLoop_B1 steps' (mul3_B1 C1 c0) (LC diff lt) t1 nc1 rt2
          | _ => HGen QF true [TokW B3] (LC b0 lt) [] (RC false c0 rt)
          end
  end.

Definition stepOuter_B1 (s : HybState) : HybState :=
  match s with
  | HClean (LC b0 lt) (RC isC1 c0 rt) => runCleanLoop_B1 kc1000 b0 lt isC1 c0 rt
  | HClean sL sR => HGen QF true [TokW B3] sL [] sR
  | HGen q h bL rL bR rR => runGenChunk kg128 (HGen q h bL rL bR rR)
  end.

Definition ofLoHi128 (hi : bool) (lo : D64) : R128 :=
  if hi then match lo with D0 => P64 | D1 => P65 | D2 => P66 | D3 => P67 | D4 => P68 | D5 => P69 | D6 => P70 | D7 => P71 | D8 => P72 | D9 => P73 | D10 => P74 | D11 => P75 | D12 => P76 | D13 => P77 | D14 => P78 | D15 => P79 | D16 => P80 | D17 => P81 | D18 => P82 | D19 => P83 | D20 => P84 | D21 => P85 | D22 => P86 | D23 => P87 | D24 => P88 | D25 => P89 | D26 => P90 | D27 => P91 | D28 => P92 | D29 => P93 | D30 => P94 | D31 => P95 | D32 => P96 | D33 => P97 | D34 => P98 | D35 => P99 | D36 => P100 | D37 => P101 | D38 => P102 | D39 => P103 | D40 => P104 | D41 => P105 | D42 => P106 | D43 => P107 | D44 => P108 | D45 => P109 | D46 => P110 | D47 => P111 | D48 => P112 | D49 => P113 | D50 => P114 | D51 => P115 | D52 => P116 | D53 => P117 | D54 => P118 | D55 => P119 | D56 => P120 | D57 => P121 | D58 => P122 | D59 => P123 | D60 => P124 | D61 => P125 | D62 => P126 | D63 => P127 end
  else match lo with D0 => P0 | D1 => P1 | D2 => P2 | D3 => P3 | D4 => P4 | D5 => P5 | D6 => P6 | D7 => P7 | D8 => P8 | D9 => P9 | D10 => P10 | D11 => P11 | D12 => P12 | D13 => P13 | D14 => P14 | D15 => P15 | D16 => P16 | D17 => P17 | D18 => P18 | D19 => P19 | D20 => P20 | D21 => P21 | D22 => P22 | D23 => P23 | D24 => P24 | D25 => P25 | D26 => P26 | D27 => P27 | D28 => P28 | D29 => P29 | D30 => P30 | D31 => P31 | D32 => P32 | D33 => P33 | D34 => P34 | D35 => P35 | D36 => P36 | D37 => P37 | D38 => P38 | D39 => P39 | D40 => P40 | D41 => P41 | D42 => P42 | D43 => P43 | D44 => P44 | D45 => P45 | D46 => P46 | D47 => P47 | D48 => P48 | D49 => P49 | D50 => P50 | D51 => P51 | D52 => P52 | D53 => P53 | D54 => P54 | D55 => P55 | D56 => P56 | D57 => P57 | D58 => P58 | D59 => P59 | D60 => P60 | D61 => P61 | D62 => P62 | D63 => P63 end.

Definition ofNat64 (n : nat) : D64 :=
  match n with O => D0 | S n => match n with O => D1 | S n => match n with O => D2 | S n => match n with O => D3 | S n => match n with O => D4 | S n => match n with O => D5 | S n => match n with O => D6 | S n => match n with O => D7 | S n => match n with O => D8 | S n => match n with O => D9 | S n => match n with O => D10 | S n => match n with O => D11 | S n => match n with O => D12 | S n => match n with O => D13 | S n => match n with O => D14 | S n => match n with O => D15 | S n => match n with O => D16 | S n => match n with O => D17 | S n => match n with O => D18 | S n => match n with O => D19 | S n => match n with O => D20 | S n => match n with O => D21 | S n => match n with O => D22 | S n => match n with O => D23 | S n => match n with O => D24 | S n => match n with O => D25 | S n => match n with O => D26 | S n => match n with O => D27 | S n => match n with O => D28 | S n => match n with O => D29 | S n => match n with O => D30 | S n => match n with O => D31 | S n => match n with O => D32 | S n => match n with O => D33 | S n => match n with O => D34 | S n => match n with O => D35 | S n => match n with O => D36 | S n => match n with O => D37 | S n => match n with O => D38 | S n => match n with O => D39 | S n => match n with O => D40 | S n => match n with O => D41 | S n => match n with O => D42 | S n => match n with O => D43 | S n => match n with O => D44 | S n => match n with O => D45 | S n => match n with O => D46 | S n => match n with O => D47 | S n => match n with O => D48 | S n => match n with O => D49 | S n => match n with O => D50 | S n => match n with O => D51 | S n => match n with O => D52 | S n => match n with O => D53 | S n => match n with O => D54 | S n => match n with O => D55 | S n => match n with O => D56 | S n => match n with O => D57 | S n => match n with O => D58 | S n => match n with O => D59 | S n => match n with O => D60 | S n => match n with O => D61 | S n => match n with O => D62 | S n => match n with O => D63 | _ => D0 end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end.

Lemma oddB_cons_isOdd64 (d : D64) (tl : Big) : oddB (BCons d tl) = isOdd64 d.
Proof. destruct d; reflexivity. Qed.

Lemma ofLoHi128_id (r : R128) : ofLoHi128 (hi128 r) (lo128 r) = r.
Proof. destruct r; reflexivity. Qed.

Lemma ofNat64_id (d : D64) : ofNat64 (d64ToNat d) = d.
Proof. destruct d; reflexivity. Qed.

Definition eqbR128 (x y : R128) : bool :=
  andb (Bool.eqb (hi128 x) (hi128 y)) (Nat.eqb (d64ToNat (lo128 x)) (d64ToNat (lo128 y))).

Lemma eqbR128_eq (x y : R128) : eqbR128 x y = true -> x = y.
Proof.
  unfold eqbR128; intro H; apply Bool.andb_true_iff in H; destruct H as [Hhi Hlo].
  apply Bool.eqb_prop in Hhi; apply Nat.eqb_eq in Hlo.
  rewrite <- (ofLoHi128_id x), <- (ofLoHi128_id y), Hhi.
  rewrite <- (ofNat64_id (lo128 x)), <- (ofNat64_id (lo128 y)), Hlo; reflexivity.
Qed.

Lemma sub64b_half_cert :
  List.forallb (fun br =>
    List.forallb (fun q_hi =>
      List.forallb (fun a =>
        List.forallb (fun d0 =>
          eqbR128 (sub64b br a (half64_q q_hi d0)) (subHalf64 br q_hi a d0)
        ) all_D64) all_D64) all_bool) all_bool = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma sub64b_half_eq (br q_hi : bool) (a d0 : D64) :
  sub64b br a (half64_q q_hi d0) = subHalf64 br q_hi a d0.
Proof.
  pose proof sub64b_half_cert as H.
  rewrite List.forallb_forall in H; specialize (H br (in_all_bool br)).
  rewrite List.forallb_forall in H; specialize (H q_hi (in_all_bool q_hi)).
  rewrite List.forallb_forall in H; specialize (H a (in_all_D64 a)).
  rewrite List.forallb_forall in H; specialize (H d0 (in_all_D64 d0)).
  exact (eqbR128_eq _ _ H).
Qed.

Lemma sub2x_B1_eq (x : Big) :
  forall (br : C6) (y : Big), sub2x_B1 br x y = sub2xTryB br x y.
Proof.
  induction x as [| | a xt IH]; intros br y.
  - destruct y, br; reflexivity.
  - destruct y, br; reflexivity.
  - destruct y as [| | b yt].
    + destruct br; reflexivity.
    + destruct br; reflexivity.
    + cbn [sub2x_B1 sub2xTryB].
      destruct br; try reflexivity;
        set (r := sub2x64 _ a b);
        destruct r; rewrite IH; destruct (sub2xTryB _ xt yt); reflexivity.
Qed.

Lemma subHalfAux_B1_eq (x : Big) :
  forall (br : bool) (d0 : D64) (bt : Big),
    subHalfAux_B1 br x d0 bt = subHalfTryB br x (BCons d0 bt).
Proof.
  induction x as [| | a xt IH]; intros br d0 bt.
  - destruct bt; reflexivity.
  - destruct bt; reflexivity.
  - destruct bt as [| | d1 bt'].
    + cbn [subHalfAux_B1 subHalfTryB oddB].
      rewrite sub64b_half_eq; set (r := subHalf64 br false a d0).
      destruct r; cbn [lo128 hi128 subHalfTryB];
        destruct xt as [| | a2 xt2]; try reflexivity;
        destruct a2, xt2; reflexivity.
    + cbn [subHalfAux_B1 subHalfTryB oddB].
      rewrite sub64b_half_eq; set (r := subHalf64 br false a d0).
      destruct r; cbn [lo128 hi128 subHalfTryB];
        destruct xt as [| | a2 xt2]; try reflexivity;
        destruct a2, xt2; reflexivity.
    + cbn [subHalfAux_B1]; rewrite subHalfTryB_cons, oddB_cons_isOdd64, sub64b_half_eq.
      set (r := subHalf64 br (isOdd64 d1) a d0).
      destruct r; rewrite IH; destruct (subHalfTryB _ xt (BCons d1 bt')); reflexivity.
Qed.

Lemma subHalf_B1_eq (br : bool) (x b : Big) :
  subHalf_B1 br x b = subHalfTryB br x b.
Proof.
  destruct b as [| | d0 bt].
  - destruct x, br; reflexivity.
  - destruct x, br; reflexivity.
  - exact (subHalfAux_B1_eq x br d0 bt).
Qed.

Lemma mul3_B1_eq (x : Big) :
  forall (c : C6), mul3_B1 c x = mul3addcB c x.
Proof.
  induction x as [| | a xt IH]; intro c.
  - destruct c; reflexivity.
  - destruct c; reflexivity.
  - cbn [mul3_B1 mul3addcB]; destruct c, a; rewrite IH; destruct (mul3addcB _ xt); reflexivity.
Qed.

Lemma mul3hAux_B1_eq (bt : Big) :
  forall (c : C6) (d0 : D64), mul3hAux_B1 c d0 bt = mul3halfB c (BCons d0 bt).
Proof.
  induction bt as [| | d1 bt' IH]; intros c d0.
  - cbn [mul3hAux_B1 mul3halfB oddB]; destruct c, d0; reflexivity.
  - cbn [mul3hAux_B1 mul3halfB oddB]; destruct c, d0; reflexivity.
  - cbn [mul3hAux_B1]; rewrite mul3halfB_cons, oddB_cons_isOdd64.
    set (ob := isOdd64 d1).
    destruct ob, c, d0; cbn [half64_q mul3half_64 lo256 hi256];
      rewrite IH; destruct (mul3halfB _ (BCons d1 bt')); reflexivity.
Qed.

Lemma mul3h_B1_eq (c : C6) (b : Big) :
  mul3h_B1 c b = mul3halfB c b.
Proof.
  destruct b as [| | d0 bt].
  - destruct c; reflexivity.
  - destruct c; reflexivity.
  - exact (mul3hAux_B1_eq bt c d0).
Qed.

Lemma runCleanLoop_B1_eq (steps : nat) :
  forall b0 lt isC1 c0 rt,
    runCleanLoop_B1 steps b0 lt isC1 c0 rt = runCleanLoop steps b0 lt isC1 c0 rt.
Proof.
  induction steps as [| steps' IH]; intros b0 lt isC1 c0 rt; [reflexivity | ].
  cbn [runCleanLoop_B1 runCleanLoop].
  rewrite sub2x_B1_eq, !subHalf_B1_eq, !mul3h_B1_eq, !mul3_B1_eq.
  destruct (isZeroB (sub2xTryB C0 b0 c0)).
  - destruct lt as [| b1 lt2 | ]; [reflexivity | | reflexivity].
    destruct (isZeroB (subSmall3B b1)); [reflexivity | ].
    destruct (evenB b0).
    + destruct (isZeroB (subHalfTryB false c0 b0)); [reflexivity | exact (IH _ _ _ _ _)].
    + destruct (isZeroB (subHalfTryB true c0 b0)); [reflexivity | exact (IH _ _ _ _ _)].
  - destruct isC1.
    + destruct (isZeroB (subSmall2B (sub2xTryB C0 b0 c0))); [reflexivity | ].
      destruct rt as [| t1 c1 rt2 | ]; [reflexivity | | reflexivity].
      destruct (isZeroB (subSmall2B c1)); [reflexivity | exact (IH _ _ _ _ _)].
    + destruct (isZeroB c0); [reflexivity | ].
      destruct rt as [| t1 c1 rt2 | ]; [reflexivity | | reflexivity].
      destruct (isZeroB (subSmall1B c1)); [reflexivity | exact (IH _ _ _ _ _)].
Qed.

Lemma stepOuter_B1_eq (s : HybState) : stepOuter_B1 s = stepOuter s.
Proof.
  destruct s as [[| b0 lt | ] [| isC1 c0 rt | ] | ]; try reflexivity.
  exact (runCleanLoop_B1_eq kc1000 b0 lt isC1 c0 rt).
Qed.

Lemma Pos_iter_B1_eq (p : positive) (s : HybState) :
  Pos.iter stepOuter_B1 s p = Pos.iter stepOuter s p.
Proof.
  revert s; induction p as [p IHp | p IHp | ]; intro s; cbn [Pos.iter].
  - rewrite !IHp; exact (stepOuter_B1_eq _).
  - rewrite !IHp; reflexivity.
  - exact (stepOuter_B1_eq s).
Qed.

(** ** 9. Parametric-Left-Tail 2,035-Step Translated Cycler & Blank-Tape Entry *)

Fixpoint encBits (bs : list bool) (lb : side) : side :=
  match bs with
  | [] => lb
  | b :: rest => bitToSym b >> encBits rest lb
  end.

Lemma encBits_app (xs ys : list bool) (lb : side) :
  encBits (xs ++ ys) lb = encBits xs (encBits ys lb).
Proof.
  induction xs as [| x xs IH]; cbn [List.app encBits]; [reflexivity | rewrite IH; reflexivity].
Qed.

Definition hdBool (bs : list bool) : bool :=
  match bs with [] => false | b :: _ => b end.

Definition tlBool (bs : list bool) : list bool :=
  match bs with [] => [] | _ :: rest => rest end.

Lemma encBits_R_headTail (R : list bool) :
  encBits R lb0 = bitToSym (hdBool R) >> encBits (tlBool R) lb0.
Proof.
  destruct R as [| b rs]; [symmetry; exact lb_zero_cons | reflexivity].
Qed.

Definition rawStepParam (q : Q_st) (h : bool) (bL bR : list bool)
    : option (Q_st * bool * list bool * list bool) :=
  match q, h with
  | QA, false => Some (QB, hdBool bR, true :: bL, tlBool bR)
  | QA, true  => Some (QE, hdBool bR, false :: bL, tlBool bR)
  | QB, false => match bL with [] => None | b :: ls => Some (QC, b, ls, true :: bR) end
  | QB, true  => match bL with [] => None | b :: ls => Some (QF, b, ls, true :: bR) end
  | QC, false => Some (QA, hdBool bR, true :: bL, tlBool bR)
  | QC, true  => match bL with [] => None | b :: ls => Some (QD, b, ls, false :: bR) end
  | QD, false => match bL with [] => None | b :: ls => Some (QB, b, ls, true :: bR) end
  | QD, true  => match bL with [] => None | b :: ls => Some (QA, b, ls, true :: bR) end
  | QE, false => Some (QB, hdBool bR, true :: bL, tlBool bR)
  | QE, true  => Some (QC, hdBool bR, true :: bL, tlBool bR)
  | QF, false => None
  | QF, true  => match bL with [] => None | b :: ls => Some (QA, b, ls, false :: bR) end
  end.

Lemma rawStepParam_sound (q q' : Q_st) (h h' : bool) (bL bL' bR bR' : list bool)
    (Hs : rawStepParam q h bL bR = Some (q', h', bL', bR')) (restL : side) :
  (encBits bL restL) {{qToQ q}}> (bitToSym h >> encBits bR lb0) -[ tm ]->
  (encBits bL' restL) {{qToQ q'}}> (bitToSym h' >> encBits bR' lb0).
Proof.
  destruct q, h; cbn [rawStepParam] in Hs;
    try discriminate;
    try (injection Hs as <- <- <- <-;
         rewrite (encBits_R_headTail bR);
         apply @step_right; reflexivity);
    (destruct bL as [| b ls]; [discriminate | ];
     injection Hs as <- <- <- <-;
     lazymatch goal with
     | |- ?c1 -[ tm ]-> _ =>
       eapply (@eq_ind (Q * tape) _ (fun x => c1 -[ tm ]-> x));
         [apply @step_left; reflexivity | reflexivity]
     end).
Qed.

Fixpoint runRawParam (n : nat) (st : option (Q_st * bool * list bool * list bool))
    : option (Q_st * bool * list bool * list bool) :=
  match n with
  | O => st
  | S n' =>
    match st with
    | None => None
    | Some (q, h, bL, bR) => runRawParam n' (rawStepParam q h bL bR)
    end
  end.

Lemma runRawParam_none (n : nat) : runRawParam n None = None.
Proof. destruct n; reflexivity. Qed.

Lemma runRawParam_sound (n : nat) :
  forall (q q' : Q_st) (h h' : bool) (bL bL' bR bR' : list bool) (restL : side),
    runRawParam n (Some (q, h, bL, bR)) = Some (q', h', bL', bR') ->
    (encBits bL restL) {{qToQ q}}> (bitToSym h >> encBits bR lb0) -[ tm ]->> n /
    (encBits bL' restL) {{qToQ q'}}> (bitToSym h' >> encBits bR' lb0).
Proof.
  induction n as [| n' IH]; intros q q' h h' bL bL' bR bR' restL Hs; cbn [runRawParam] in Hs.
  - injection Hs as <- <- <- <-; apply multistep_0.
  - destruct (rawStepParam q h bL bR) as [[[[q1 h1] bL1] bR1] | ] eqn:Hstep.
    + eapply multistep_S;
        [exact (rawStepParam_sound _ _ _ _ _ _ _ _ Hstep restL) | exact (IH _ _ _ _ _ _ _ _ restL Hs)].
    + rewrite runRawParam_none in Hs; discriminate.
Qed.

Definition beqQ (q1 q2 : Q_st) : bool :=
  match q1, q2 with
  | QA, QA | QB, QB | QC, QC | QD, QD | QE, QE | QF, QF => true
  | _, _ => false
  end.

Lemma beqQ_eq (q1 q2 : Q_st) : beqQ q1 q2 = true -> q1 = q2.
Proof. destruct q1, q2; intro H; try reflexivity; discriminate. Qed.

Fixpoint beqBits (xs ys : list bool) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => andb (Bool.eqb x y) (beqBits xs' ys')
  | _, _ => false
  end.

Lemma beqBits_eq (xs : list bool) : forall ys, beqBits xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] H; try reflexivity; try discriminate.
  cbn [beqBits] in H; apply Bool.andb_true_iff in H; destruct H as [Hxy Hrest].
  apply Bool.eqb_prop in Hxy; f_equal; [exact Hxy | exact (IH ys' Hrest)].
Qed.

Definition beqRawOpt (a b : option (Q_st * bool * list bool * list bool)) : bool :=
  match a, b with
  | None, None => true
  | Some (q1, h1, l1, r1), Some (q2, h2, l2, r2) =>
    andb (beqQ q1 q2) (andb (Bool.eqb h1 h2) (andb (beqBits l1 l2) (beqBits r1 r2)))
  | _, _ => false
  end.

Lemma beqRawOpt_eq (a b : option (Q_st * bool * list bool * list bool)) :
  beqRawOpt a b = true -> a = b.
Proof.
  destruct a as [[[[q1 h1] l1] r1] | ], b as [[[[q2 h2] l2] r2] | ]; intro H;
    try reflexivity; try discriminate.
  cbn [beqRawOpt] in H.
  apply Bool.andb_true_iff in H; destruct H as [Hq H].
  apply Bool.andb_true_iff in H; destruct H as [Hh H].
  apply Bool.andb_true_iff in H; destruct H as [Hl Hr].
  rewrite (beqQ_eq _ _ Hq), (Bool.eqb_prop _ _ Hh), (beqBits_eq _ _ Hl), (beqBits_eq _ _ Hr).
  reflexivity.
Qed.

Fixpoint repWBits (n : nat) : list bool :=
  match n with
  | O => []
  | S n' => true :: true :: false :: repWBits n'
  end.

Lemma encBits_repWBits (n : nat) (lb : side) :
  encBits (repWBits n) lb = encW n lb.
Proof.
  induction n as [| n' IH]; cbn [repWBits encBits bitToSym encW]; [reflexivity | rewrite IH; reflexivity].
Qed.

Definition cycL : list bool := repWBits 18.
Definition cycDelta : list bool := [true; true; false; true; true; false; false].
Definition cycStepsPred : nat := Pos.to_nat 2034%positive.

Lemma cyc_ok :
  beqRawOpt (runRawParam (S cycStepsPred) (Some (QA, true, cycL, [])))
            (Some (QA, true, cycL ++ cycDelta, [])) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma cyc_reaches (restL : side) :
  (encW 18 restL) {{A}}> (S1 >> lb0) -[ tm ]->+
  (encW 18 (encBits cycDelta restL)) {{A}}> (S1 >> lb0).
Proof.
  pose proof (runRawParam_sound (S cycStepsPred) _ _ _ _ _ _ _ _ restL (beqRawOpt_eq _ _ cyc_ok)) as H.
  unfold cycL in H; rewrite encBits_app, !encBits_repWBits in H; cbn [qToQ bitToSym encBits] in H.
  exact (multistep_progress tm cycStepsPred _ _ H).
Qed.

Lemma wf_r1Start : wfHyb r1Start.
Proof. repeat split; exact I. Qed.

Lemma c0_eq_r1StartN : c0 = encHybN (evalHyb r1Start).
Proof. reflexivity. Qed.

Definition outerSteps : positive := 166268%positive.

Lemma cert_entry :
  check_cycler_entry (Pos.iter stepOuter_B1 r1Start outerSteps) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma entry_reaches :
  exists restL : side, c0 -[ tm ]->* (encW 18 restL) {{A}}> (S1 >> lb0).
Proof.
  destruct (Pos_iter_sim outerSteps r1Start wf_r1Start) as [Hwf Heval].
  pose proof cert_entry as Hcert.
  rewrite Pos_iter_B1_eq, (check_cycler_entry_sim _ Hwf), Heval in Hcert.
  destruct (check_cycler_entryN_sound _ Hcert) as [restL Henc].
  exists restL.
  rewrite c0_eq_r1StartN, <- Henc.
  exact (Pos_iter_sound outerSteps (evalHyb r1Start)).
Qed.

End M300_Internal.

Theorem nonhalt : ~ halts tm c0.
Proof.
  destruct M300_Internal.entry_reaches as [restL0 Hreach].
  eapply multistep_nonhalt; [exact Hreach | ].
  apply (progress_nonhalt_simple tm side
           (fun restL : side => (M300_Internal.encW 18%nat restL) {{A}}> (S1 >> const S0))
           restL0).
  intro restL.
  exists (M300_Internal.encBits M300_Internal.cycDelta restL).
  exact (M300_Internal.cyc_reaches restL).
Qed.
