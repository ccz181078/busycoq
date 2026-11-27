(** * BB(6) Holdout 608:#300 / 797:#395: 1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA *)

From BusyCoq Require Import Individual62.
From Coq Require Import String Bool Lists.List Arith Lia PArith.
Import ListNotations.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA").

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

(* Literal fallback gets its next action from the machine itself. *)
Definition qFromQ (q : Q) : Q_st :=
  match q with
  | A => QA | B => QB | C => QC | D => QD | E => QE | F => QF
  end.

Definition dispatchRaw {T : Type} (q : Q_st) (h : bool)
    (left right : Q_st -> bool -> T) (halt : T) : T :=
  match tm (qToQ q, bitToSym h) with
  | Some (s, L, q') => left (qFromQ q') (match s with S0 => false | S1 => true end)
  | Some (s, R, q') => right (qFromQ q') (match s with S0 => false | S1 => true end)
  | None => halt
  end.

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

(* The clean-mode schedule is independent of the counter representation.
   Its stack views expose only the structured block at the top. *)
Section CleanSchedule.
  Context {Count Left Right State : Type}.
  Variable viewL : Left -> option (Count * Left).
  Variable viewR : Right -> option (bool * Count * Right).
  Variable pushL : Count -> Left -> Left.
  Variable pushR : bool -> Count -> Right -> Right.
  Variable stayClean exitClean : Left -> Right -> State.
  Variable zero even : Count -> bool.
  Variable subDouble : Count -> Count -> Count.
  Variable sub1 sub2 sub3 : Count -> Count.
  Variable subHalf : bool -> Count -> Count -> Count.
  Variable move1 move3half move4 move5half : Count -> Count.

  Fixpoint runCleanShared (fuel : nat) (b : Count) (lt : Left)
      (tag : bool) (c : Count) (rt : Right) : State :=
    match fuel with
    | O => stayClean (pushL b lt) (pushR tag c rt)
    | S k =>
        let exit := exitClean (pushL b lt) (pushR tag c rt) in
        let diff := subDouble b c in
        if zero diff then
          match viewL lt with
          | Some (b1, lt') =>
              let nb := sub3 b1 in
              if zero nb then exit
              else if even b then
                let nc := subHalf false c b in
                if zero nc then exit
                else runCleanShared k nb lt' true (move3half b) (pushR tag nc rt)
              else
                let nc := subHalf true c b in
                if zero nc then exit
                else runCleanShared k nb lt' false (move5half b) (pushR tag nc rt)
          | None => exit
          end
        else if tag then
          let nb := sub2 diff in
          if zero nb then exit
          else match viewR rt with
               | Some (tag', c1, rt') =>
                   let nc := sub2 c1 in
                   if zero nc then exit
                   else runCleanShared k (move4 c) (pushL nb lt) tag' nc rt'
               | None => exit
               end
        else
          if zero c then exit
          else match viewR rt with
               | Some (tag', c1, rt') =>
                   let nc := sub1 c1 in
                   if zero nc then exit
                   else runCleanShared k (move1 c) (pushL diff lt) tag' nc rt'
               | None => exit
               end
    end.
End CleanSchedule.

Definition asCleanLN (s : LStackN) :=
  match s with LCN b tl => Some (b, tl) | _ => None end.
Definition asCleanRN (s : RStackN) :=
  match s with RCN tag c tl => Some (tag, c, tl) | _ => None end.

Definition runCleanLoopN :=
  runCleanShared asCleanLN asCleanRN LCN RCN HCleanN
    (fun l r => HGenN QF true [TokWN 3] l [] r)
    isZeroN evenN (fun b c => b - 2 * c)
    (fun x => x - 1) (fun x => x - 2) (fun x => x - 3)
    (fun ceil c b => c - (if ceil then halfN b + 1 else halfN b))
    (mul3addcN 1) (fun b => mul3addcN 3 (halfN b))
    (mul3addcN 4) (fun b => mul3addcN 5 (halfN b)).

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

Definition stepRawN (q : Q_st) (h : bool)
    (bL : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN) : HybStateN :=
  let stay := HGenN q h bL rL bR rR in
  dispatchRaw q h
    (fun q' bit =>
      match popBitLN bL rL with
      | Some (h', bL', rL') => finishGenN q' h' bL' rL' (pushBitN bit bR (isEmptyRN rR)) rR
      | None => stay
      end)
    (fun q' bit =>
      match popBitRN bR rR with
      | Some (h', bR', rR') => finishGenN q' h' (pushBitN bit bL (isEmptyLN rL)) rL bR' rR'
      | None => stay
      end)
    stay.

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
  induction steps as [| steps' IH]; intros b0 lt isC1 c0 rt; cbn [runCleanLoopN runCleanShared asCleanLN asCleanRN].
  - apply evstep_refl.
  - destruct (isZeroN (b0 - 2 * c0)) eqn:Hdiff.
    + destruct lt as [| b1 lt2 | t lt2]; [apply evstep_refl | cbn [asCleanLN asCleanRN] | apply evstep_refl].
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
        destruct rt as [| t1 c1 rt2 | t rt2]; [apply evstep_refl | cbn [asCleanLN asCleanRN] | apply evstep_refl].
        destruct (isZeroN (c1 - 2)) eqn:Hc1; [apply evstep_refl | ].
        apply isZeroN_false in Hc1.
        pose proof (clean_B23_c1 b0 c0 c1 (encLN lt) (bitToSym t1 >> encRN rt2)
                      ltac:(lia) ltac:(lia)) as Hstep.
        replace (4 + 3 * c0) with (mul3addcN 4 c0) in Hstep by (unfold mul3addcN; lia).
        replace (b0 - (2 * c0 + 2)) with (b0 - 2 * c0 - 2) in Hstep by lia.
        exact (stepStar_trans Hstep (IH (mul3addcN 4 c0) (LCN (b0 - 2 * c0 - 2) lt) t1 (c1 - 2) rt2)).
      * destruct (isZeroN c0) eqn:Hc0; [apply evstep_refl | ].
        apply isZeroN_false in Hc0.
        destruct rt as [| t1 c1 rt2 | t rt2]; [apply evstep_refl | cbn [asCleanLN asCleanRN] | apply evstep_refl].
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

Lemma qToQ_from_q q : qToQ (qFromQ q) = q.
Proof. destruct q; reflexivity. Qed.

Lemma bitToSym_from_sym s :
  bitToSym (match s with S0 => false | S1 => true end) = s.
Proof. destruct s; reflexivity. Qed.

Lemma stepRawN_sound (q : Q_st) (h : bool) (bL : list TokN) (rL : LStackN) (bR : list TokN) (rR : RStackN) :
  encHybN (HGenN q h bL rL bR rR) -[ tm ]->* encHybN (stepRawN q h bL rL bR rR).
Proof.
  unfold stepRawN, dispatchRaw.
  destruct (tm (qToQ q, bitToSym h)) as [[[s d] q']|] eqn:Htm; [destruct d | apply evstep_refl].
  - destruct (popBitLN bL rL) as [[[h' bL'] rL'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN].
    rewrite (encPopBitLN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyRN_spec rR)).
    rewrite qToQ_from_q, bitToSym_from_sym.
    eapply evstep_step; [apply @step_left; exact Htm | apply evstep_refl].
  - destruct (popBitRN bR rR) as [[[h' bR'] rR'] | ] eqn:Hp; [| apply evstep_refl].
    rewrite encFinishGenN; cbn [encHybN].
    rewrite (encPopBitRN _ _ _ _ _ Hp), (encPushBitN _ _ _ _ (isEmptyLN_spec rL)).
    rewrite qToQ_from_q, bitToSym_from_sym.
    eapply evstep_step; [apply @step_right; exact Htm | apply evstep_refl].
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

(** Arithmetic is delegated to BusyCoq's verified 54-bit digit routines.
    The macro control and stacks are identical to those of the nat model. *)
From BusyCoq Require BigUint.
From Coq Require Import ZArith.
Import PrimInt63.
Local Open Scope nat_scope.

Definition Big := BigUint.BigUint.
Definition B0 := BigUint.BigUintNil.
Definition B1 := BigUint.BigUintCons 1%uint63 B0.
Definition B2 := BigUint.BigUintCons 2%uint63 B0.
Definition B3 := BigUint.BigUintCons 3%uint63 B0.
Definition B18 := BigUint.BigUintCons 18%uint63 B0.
Definition toNatB := BigUint.to_nat.
Definition wfB (_ : Big) : Prop := True.
Definition isZeroB := BigUint.is0.
Definition eqbB (x y : Big) := andb (BigUint.leb x y) (BigUint.leb y x).
Definition isOneB (x : Big) := eqbB x B1.
Definition isTwoB (x : Big) := eqbB x B2.
Definition isThreeB (x : Big) := eqbB x B3.
Definition lebB := BigUint.leb.
Definition addB := BigUint.add.
Definition subB := BigUint.sub.
Definition addSmall1B := BigUint.succ.
Definition addSmall2B x := BigUint.inc x 2%uint63.
Definition subSmall1B x := subB x B1.
Definition subSmall2B x := subB x B2.
Definition subSmall3B x := subB x B3.

Inductive C6 := C0 | C1 | C2 | C3 | C4 | C5.
Definition valC6 c : nat := match c with C0 => 0 | C1 => 1 | C2 => 2 | C3 => 3 | C4 => 4 | C5 => 5 end.
Definition carry_word c : PrimInt63.int :=
  match c with C0 => 0 | C1 => 1 | C2 => 2 | C3 => 3 | C4 => 4 | C5 => 5 end%uint63.
Definition doubleB x := BigUint.mulc x 2%uint63.
Definition div2B x := fst (BigUint.divmodc x 2%uint63).
Definition evenB x := PrimInt63.eqb (snd (BigUint.divmodc x 2%uint63)) 0%uint63.
Definition oddB x := negb (evenB x).
Definition sub2xB x y := subB x (doubleB y).
Definition subHalfTryB (br : bool) x y := subB x (if br then addSmall1B (div2B y) else div2B y).
Definition mul3addcB c x := BigUint.muladdc x 3%uint63 (carry_word c).
Definition mul3halfB c x := mul3addcB c (div2B x).

Lemma lebB_spec x y : wfB x -> wfB y -> lebB x y = lebN (toNatB x) (toNatB y).
Proof.
  intros _ _. unfold lebB, lebN, toNatB, BigUint.to_nat.
  pose proof (BigUint.toZ_ge0 x); pose proof (BigUint.toZ_ge0 y).
  destruct (BigUint.leb_spec x y), (Nat.leb_spec0 (Z.to_nat (BigUint.toZ x)) (Z.to_nat (BigUint.toZ y))); auto; lia.
Qed.

Lemma eqbB_spec x y : wfB x -> wfB y -> eqbB x y = eqbN (toNatB x) (toNatB y).
Proof.
  intros Hx Hy. unfold eqbB, eqbN.
  change (andb (lebB x y) (lebB y x) = Nat.eqb (toNatB x) (toNatB y)).
  rewrite (lebB_spec x y Hx Hy), (lebB_spec y x Hy Hx); unfold lebN.
  destruct (Nat.leb_spec0 (toNatB x) (toNatB y)),
           (Nat.leb_spec0 (toNatB y) (toNatB x));
     cbn; symmetry; first [apply Nat.eqb_eq; lia | apply Nat.eqb_neq; lia].
Qed.

Lemma wfB_B0 : wfB B0. Proof. exact I. Qed.
Lemma wfB_B1 : wfB B1. Proof. exact I. Qed.
Lemma wfB_B2 : wfB B2. Proof. exact I. Qed.
Lemma wfB_B3 : wfB B3. Proof. exact I. Qed.
Lemma wfB_B18 : wfB B18. Proof. exact I. Qed.

Lemma isZeroB_spec x : wfB x -> isZeroB x = isZeroN (toNatB x).
Proof.
  intros _. unfold isZeroB, isZeroN, toNatB.
  destruct (BigUint.inj_is0 x); [symmetry; apply Nat.eqb_eq | symmetry; apply Nat.eqb_neq]; assumption.
Qed.
Lemma isOneB_spec x : wfB x -> isOneB x = isOneN (toNatB x).
Proof. intro H; exact (eqbB_spec x B1 H I). Qed.
Lemma isTwoB_spec x : wfB x -> isTwoB x = isTwoN (toNatB x).
Proof. intro H; exact (eqbB_spec x B2 H I). Qed.
Lemma isThreeB_spec x : wfB x -> isThreeB x = isThreeN (toNatB x).
Proof. intro H; exact (eqbB_spec x B3 H I). Qed.

Lemma addB_spec x y : wfB x -> wfB y -> wfB (addB x y) /\ toNatB (addB x y) = toNatB x + toNatB y.
Proof. intros _ _; split; [exact I | apply BigUint.inj_add]. Qed.
Lemma subB_spec x y : wfB x -> wfB y -> wfB (subB x y) /\ toNatB (subB x y) = toNatB x - toNatB y.
Proof. intros _ _; split; [exact I | apply BigUint.inj_sub]. Qed.
Lemma addSmall1B_spec x : wfB x -> wfB (addSmall1B x) /\ toNatB (addSmall1B x) = toNatB x + 1.
Proof. intros _; split; [exact I | pose proof (BigUint.inj_succ x); unfold addSmall1B, toNatB; lia]. Qed.
Lemma addSmall2B_spec x : wfB x -> wfB (addSmall2B x) /\ toNatB (addSmall2B x) = toNatB x + 2.
Proof.
  intros _; split; [exact I |].
  unfold addSmall2B, toNatB, BigUint.to_nat.
  rewrite BigUint.inc_spec by reflexivity.
  pose proof (BigUint.toZ_ge0 x); change (Uint63.to_Z 2%uint63) with 2%Z; lia.
Qed.
Lemma subSmall1B_spec x : wfB x -> wfB (subSmall1B x) /\ toNatB (subSmall1B x) = toNatB x - 1.
Proof. intro H; exact (subB_spec x B1 H I). Qed.
Lemma subSmall2B_spec x : wfB x -> wfB (subSmall2B x) /\ toNatB (subSmall2B x) = toNatB x - 2.
Proof. intro H; exact (subB_spec x B2 H I). Qed.
Lemma subSmall3B_spec x : wfB x -> wfB (subSmall3B x) /\ toNatB (subSmall3B x) = toNatB x - 3.
Proof. intro H; exact (subB_spec x B3 H I). Qed.

Lemma toNat_doubleB x : toNatB (doubleB x) = 2 * toNatB x.
Proof.
  unfold doubleB, toNatB, BigUint.to_nat.
  rewrite BigUint.mulc_spec by reflexivity.
  pose proof (BigUint.toZ_ge0 x); change (Uint63.to_Z 2%uint63) with 2%Z; lia.
Qed.
Lemma toNat_sub2xB x y : toNatB (sub2xB x y) = toNatB x - 2 * toNatB y.
Proof.
  unfold sub2xB, subB; unfold toNatB at 1.
  rewrite BigUint.inj_sub, <- (toNat_doubleB y); reflexivity.
Qed.
Lemma sub2xB_spec x y : wfB x -> wfB y -> wfB (sub2xB x y) /\ toNatB (sub2xB x y) = toNatB x - 2 * toNatB y.
Proof. auto using I, toNat_sub2xB. Qed.
Lemma sub2xTryB_zero_spec x y : wfB x -> wfB y ->
  isZeroB (sub2xB x y) = isZeroN (toNatB x - 2 * toNatB y) /\
  (isZeroB (sub2xB x y) = false -> wfB (sub2xB x y) /\ toNatB (sub2xB x y) = toNatB x - 2 * toNatB y).
Proof.
  intros _ _; split.
  - now rewrite (isZeroB_spec _ I), toNat_sub2xB.
  - intros _; split; [exact I | apply toNat_sub2xB].
Qed.

Lemma divmod2B_spec x : let (q, r) := BigUint.divmodc x 2%uint63 in
  toNatB x = 2 * toNatB q + Z.to_nat (Uint63.to_Z r) /\ (Uint63.to_Z r < 2)%Z.
Proof.
  pose proof (BigUint.divmodc_spec x 2%uint63 eq_refl eq_refl) as H.
  destruct (BigUint.divmodc x 2%uint63) as [q r].
  destruct H as [Hq Hr].
  change (Uint63.to_Z 2%uint63) with 2%Z in Hq, Hr.
  pose proof (Z.div_mod (BigUint.toZ x) 2 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (BigUint.toZ x) 2 ltac:(lia)) as Hm.
  pose proof (BigUint.toZ_ge0 x); pose proof (BigUint.toZ_ge0 q).
  unfold toNatB, BigUint.to_nat; lia.
Qed.
Lemma div2_evenB_spec x :
  halfN (toNatB x) = toNatB (div2B x) /\ evenN (toNatB x) = evenB x.
Proof.
  unfold div2B, evenB.
  pose proof (divmod2B_spec x) as H.
  destruct (BigUint.divmodc x 2%uint63) as [q r]; cbn [fst snd]; destruct H as [H Hr].
  pose proof (Uint63.to_Z_bounded r).
  apply halfN_unique.
  destruct (PrimInt63.eqb r 0%uint63) eqn:Er.
  - apply Uint63.eqb_spec in Er. subst r; change (Z.to_nat (Uint63.to_Z 0%uint63)) with 0 in H; exact H.
  - apply Uint63.eqb_false_spec in Er.
    assert (Uint63.to_Z r <> 0)%Z by (intro Hz; apply Er, Uint63.to_Z_inj; exact Hz).
    lia.
Qed.
Lemma div2B_spec x : wfB x -> wfB (div2B x) /\ toNatB (div2B x) = halfN (toNatB x).
Proof. intros _; split; [exact I | symmetry; exact (proj1 (div2_evenB_spec x))]. Qed.
Lemma evenB_spec x : evenB x = evenN (toNatB x).
Proof. symmetry; exact (proj2 (div2_evenB_spec x)). Qed.
Lemma oddB_spec x : oddB x = oddN (toNatB x).
Proof. unfold oddB, oddN; now rewrite evenB_spec. Qed.

Lemma toNat_subHalfTryB br x y :
  toNatB (subHalfTryB br x y) = toNatB x - (halfN (toNatB y) + (if br then 1 else 0)).
Proof.
  unfold subHalfTryB, subB, toNatB at 1; rewrite BigUint.inj_sub.
  fold (toNatB x). fold (toNatB (if br then addSmall1B (div2B y) else div2B y)).
  destruct (div2B_spec y I) as [_ Hd]; destruct (addSmall1B_spec (div2B y) I) as [_ Hs].
  destruct br; rewrite ?Hs, Hd; lia.
Qed.
Lemma subHalfTryB_zero_spec br x y : wfB x -> wfB y ->
  isZeroB (subHalfTryB br x y) = isZeroN (toNatB x - (halfN (toNatB y) + (if br then 1 else 0))) /\
  (isZeroB (subHalfTryB br x y) = false -> wfB (subHalfTryB br x y) /\ toNatB (subHalfTryB br x y) = toNatB x - (halfN (toNatB y) + (if br then 1 else 0))).
Proof.
  intros _ _; split.
  - now rewrite (isZeroB_spec _ I), toNat_subHalfTryB.
  - intros _; split; [exact I | apply toNat_subHalfTryB].
Qed.

Lemma mul3addcB_spec x c : wfB x ->
  wfB (mul3addcB c x) /\ toNatB (mul3addcB c x) = mul3addcN (valC6 c) (toNatB x).
Proof.
  intros _; split; [exact I |].
  unfold mul3addcB, toNatB, BigUint.to_nat, mul3addcN.
  rewrite BigUint.muladdc_spec by (destruct c; reflexivity).
  pose proof (BigUint.toZ_ge0 x).
  change (Uint63.to_Z 3%uint63) with 3%Z.
  assert (Uint63.to_Z (carry_word c) = Z.of_nat (valC6 c))
    as Hcarry by (destruct c; reflexivity).
  rewrite Hcarry; lia.
Qed.
Lemma mul3halfB_spec x c : wfB x ->
  wfB (mul3halfB c x) /\ toNatB (mul3halfB c x) = mul3addcN (valC6 c) (halfN (toNatB x)).
Proof.
  intros H; unfold mul3halfB.
  destruct (div2B_spec x H) as [Hwf <-].
  now apply mul3addcB_spec.
Qed.

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

Definition asCleanL (s : LStack) :=
  match s with LC b tl => Some (b, tl) | _ => None end.
Definition asCleanR (s : RStack) :=
  match s with RC tag c tl => Some (tag, c, tl) | _ => None end.

Definition runCleanLoop :=
  runCleanShared asCleanL asCleanR LC RC HClean
    (fun l r => HGen QF true [TokW B3] l [] r)
    isZeroB evenB sub2xB subSmall1B subSmall2B subSmall3B subHalfTryB
    (mul3addcB C1) (mul3halfB C3) (mul3addcB C4) (mul3halfB C5).

Definition runCleanChunk (kc4 : nat) (sL : LStack) (sR : RStack) : HybState :=
  match sL, sR with
  | LC b0 lt, RC isC1 c0 rt => runCleanLoop kc4 b0 lt isC1 c0 rt
  | _, _ => HGen QF true [TokW B3] sL [] sR
  end.

Definition pushTok (t : Tok) (ts : list Tok) : list Tok :=
  match t with
  | TokZ a => if isZeroB a then ts else
      match ts with TokZ b :: rest => TokZ (addB a b) :: rest | _ => t :: ts end
  | TokO a => if isZeroB a then ts else
      match ts with TokO b :: rest => TokO (addB a b) :: rest | _ => t :: ts end
  | TokW a => if isZeroB a then ts else
      match ts with TokW b :: rest => TokW (addB a b) :: rest | _ => t :: ts end
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
    let diff := sub2xB b0 c0 in
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

Definition stepRaw (q : Q_st) (h : bool)
    (bL : list Tok) (rL : LStack) (bR : list Tok) (rR : RStack) : HybState :=
  let stay := HGen q h bL rL bR rR in
  dispatchRaw q h
    (fun q' bit =>
      match popBitL bL rL with
      | Some (h', bL', rL') => finishGen q' h' bL' rL' (pushBit bit bR (isEmptyR rR)) rR
      | None => stay
      end)
    (fun q' bit =>
      match popBitR bR rR with
      | Some (h', bR', rR') => finishGen q' h' (pushBit bit bL (isEmptyL rL)) rL bR' rR'
      | None => stay
      end)
    stay.

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

Lemma toNat_B0 : toNatB B0 = 0. Proof. reflexivity. Qed.
Lemma toNat_B1 : toNatB B1 = 1. Proof. reflexivity. Qed.
Lemma toNat_B2 : toNatB B2 = 2. Proof. reflexivity. Qed.
Lemma toNat_B3 : toNatB B3 = 3. Proof. reflexivity. Qed.
Lemma toNat_B18 : toNatB B18 = 18. Proof. reflexivity. Qed.

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
    cbn [runCleanLoop runCleanLoopN runCleanShared asCleanL asCleanR asCleanLN asCleanRN].
    destruct (sub2xTryB_zero_spec b0 c0 Hb0 Hc0) as [Hz Hdiff].
    rewrite Hz.
    destruct (isZeroN (toNatB b0 - 2 * toNatB c0)).
    + destruct lt as [| b1 lt2 | t1 lt2]; [exact Hexit | | exact Hexit].
      destruct Hlt as [Hb1 Hlt2].
      cbn [evalL asCleanL asCleanLN].
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
        destruct Hrt as [Hc1 Hrt2]; cbn [evalR asCleanR asCleanRN].
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
        destruct Hrt as [Hc1 Hrt2]; cbn [evalR asCleanR asCleanRN].
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
  intros Ht Hts; destruct t as [a | a | a];
    cbn [wfTok pushTok evalTok] in Ht |- *;
    rewrite (isZeroB_spec a Ht); unfold isZeroN;
    destruct (toNatB a) as [| ma] eqn:Hma; cbn [Nat.eqb].
  all: try (split; [exact Hts | reflexivity]).
  all: destruct ts as [| [b | b | b] rest];
    try (cbn [wfToks evalToks evalTok pushTokN]; rewrite ?Hma;
         split; [split; [exact Ht | exact Hts] | reflexivity]).
  all: destruct Hts as [Hb Hrest];
    destruct (addB_spec a b Ht Hb) as [Hwfa Heqa];
    cbn [wfToks wfTok evalToks evalTok pushTokN];
    rewrite Heqa, Hma; split; [split; [exact Hwfa | exact Hrest] | reflexivity].
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
        { rewrite (lebB_spec B2 z1 wfB_B2 Hz1); rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18; cbn [Nat.add Nat.mul].
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
  intros HbL HrL HbR HrR; unfold stepRaw, stepRawN, dispatchRaw.
  destruct (tm (qToQ q, bitToSym h)) as [[[s d] q']|]; [destruct d |]; cbn zeta;
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
      rewrite (lebB_spec B2 n wfB_B2 Hn); rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18; cbn [Nat.add Nat.mul].
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
          destruct (subWHead_sim c B1 rTail2 Hc wfB_B1 HrTail2) as [Hwfs Heqs]; rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18 in Heqs; cbn [Nat.add Nat.mul] in Heqs.
          destruct (finishGen_sim QF true bL rL (TokO B1 :: TokZ B1 :: TokO B1 :: TokZ B1 :: subWHead c B1 rTail2) rR
                      HbL HrL ltac:(repeat split; auto; try discriminate) HrR) as [Hwff Heqf].
          cbn [evalToks evalTok] in Heqf; rewrite Heqf, Heqs; split; [exact Hwff | reflexivity]. }
    + (* TokW c :: rTail *)
      pose proof HbR as [Hc HrTail]; cbn [evalToks evalTok].
      rewrite (isZeroB_spec c Hc); destruct (isZeroN (toNatB c));
        [exact (stepRaw_sim QA true bL rL _ rR HbL HrL HbR HrR) | ].
      destruct (subWHead_sim c B1 rTail Hc wfB_B1 HrTail) as [Hwfs Heqs]; rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18 in Heqs; cbn [Nat.add Nat.mul] in Heqs.
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
        rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18 in Heq_t; cbn [Nat.add Nat.mul] in Heq_t; rewrite Heq_b1 in Heq_t.
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
                destruct (subWHead_sim c B1 rTail3 Hc wfB_B1 HrTail3) as [Hwfs Heqs]; rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18 in Heqs; cbn [Nat.add Nat.mul] in Heqs.
                destruct (finishGen_sim QF true _ rL _ rR Hwf_t HrL Hwfs HrR) as [Hwff Heqf].
                rewrite Heqf, Heq_t, Heqs; split; [exact Hwff | reflexivity].
            + (* B2: TokO o0 :: TokW c :: rTail2 *)
              pose proof HbR as [Ho0 [Hc HrTail2]]; cbn [evalToks evalTok].
              rewrite (isOneB_spec o0 Ho0), (lebB_spec B2 c wfB_B2 Hc); rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18; cbn [Nat.add Nat.mul].
              destruct (andb (isOneN (toNatB o0)) (lebN 2 (toNatB c)));
                [| exact (stepRaw_sim QF true _ rL _ rR HbL HrL HbR HrR)].
              rewrite (lebB_spec B2 b wfB_B2 Hb); rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18; cbn [Nat.add Nat.mul].
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
              destruct (subWHead_sim c B2 rTail2 Hc wfB_B2 HrTail2) as [Hwfs Heqs]; rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18 in Heqs; cbn [Nat.add Nat.mul] in Heqs.
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
              destruct (subWHead_sim c B1 rTail Hc wfB_B1 HrTail) as [Hwfs Heqs]; rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18 in Heqs; cbn [Nat.add Nat.mul] in Heqs.
              destruct (pushTok_sim (TokZ B2) _ wfB_B2 Hwfs) as [Hwfpt Heqpt].
              destruct (finishGen_sim QF true _ rL (TokO B1 :: pushTok (TokZ B2) (subWHead c B1 rTail)) rR
                          Hwf_t HrL ltac:(repeat split; auto; try discriminate) HrR) as [Hwff Heqf].
              cbn [evalToks evalTok] in Heqf, Heqpt; rewrite Heqf, Heq_t, Heqpt, Heqs; split; [exact Hwff | reflexivity]. }
        { (* z0 <> 1 *)
          rewrite (isTwoB_spec z0 Hz0); destruct (isTwoN (toNatB z0)).
          - rewrite (isZeroB_spec a Ha), (lebB_spec B3 b wfB_B3 Hb); rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18; cbn [Nat.add Nat.mul].
            destruct (isZeroN (toNatB a)); [cbn [negb andb]; exact (stepRaw_sim QF true _ rL bR rR HbL HrL HbR HrR) | ].
            destruct (lebN 3 (toNatB b)); [| cbn [negb andb]; exact HF1].
            cbn [negb andb].
            rewrite (startsWith1_sim bR HbR); destruct (startsWith1N (evalToks bR)); [| exact HF1].
            destruct (subSmall3B_spec b Hb) as [Hwf_b3 Heq_b3].
            destruct (tail_w_sim B3 (subSmall3B b) lTail2 wfB_B3 Hwf_b3 HlTail2) as [Hwf_t Heq_t];
              cbn zeta in Hwf_t, Heq_t; rewrite ?toNat_B0, ?toNat_B1, ?toNat_B2, ?toNat_B3, ?toNat_B18 in Heq_t; cbn [Nat.add Nat.mul] in Heq_t; rewrite Heq_b3 in Heq_t.
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

(** ** 9. Parametric-Left-Tail 2,035-Step Translated Cycler & Blank-Tape Entry *)

(* The closed guard is checked with BusyCoq's bounded stepper.  In
   particular this run may never read the arbitrary left tail. *)
Fixpoint runGuard (n : nat) (c : BoundedConfig.T) : option BoundedConfig.T :=
  match n with
  | O => Some c
  | S k =>
      match BoundedConfig.step_r0inf tm c with
      | Some d => runGuard k d
      | None => None
      end
  end.

Definition denoteGuard (c : BoundedConfig.T) (tail : side) :=
  BoundedConfig.to_config c tail lb0.

Lemma runGuard_sound n c d tail :
  runGuard n c = Some d -> denoteGuard c tail -[tm]->> n / denoteGuard d tail.
Proof.
  revert c; induction n as [|n IH]; intros c H; cbn [runGuard] in H.
  - injection H as ->; constructor.
  - pose proof (BoundedConfig.step_r0inf_spec tm c) as Hstep.
    destruct (BoundedConfig.step_r0inf tm c) as [z|]; [|discriminate].
    eapply multistep_S; [apply Hstep | now apply IH].
Qed.

Definition stripe : list Sym := [S1; S1; S0].
Definition guard := concat (repeat stripe 18).
Definition cycDelta := stripe ++ stripe ++ [S0].
Definition entryGuard := BoundedConfig.Build_T guard [S1] A R.
Definition exitGuard := BoundedConfig.Build_T (guard ++ cycDelta) [S1] A R.
Definition cycStepsPred := Pos.to_nat 2034%positive.

Lemma cyc_ok : runGuard (S cycStepsPred) entryGuard = Some exitGuard.
Proof. vm_compute. reflexivity. Qed.

Lemma cyc_reaches (restL : side) :
  (encW 18 restL) {{A}}> (S1 >> lb0) -[tm]->+
  (encW 18 (restL <* cycDelta)) {{A}}> (S1 >> lb0).
Proof.
  exact (multistep_progress tm cycStepsPred _ _
    (runGuard_sound _ _ _ restL cyc_ok)).
Qed.

Lemma wf_r1Start : wfHyb r1Start.
Proof. repeat split; exact I. Qed.

Lemma c0_eq_r1StartN : c0 = encHybN (evalHyb r1Start).
Proof. reflexivity. Qed.

Definition outerSteps : positive := 166268%positive.


End M300_Internal.

Import M300_Internal.

Theorem nonhalt_from_checked_entry :
  check_cycler_entry (Pos.iter stepOuter r1Start outerSteps) = true ->
  ~ halts tm c0.
Proof.
  intro Hcert.
  destruct (Pos_iter_sim outerSteps r1Start wf_r1Start) as [Hwf Heval].
  rewrite (check_cycler_entry_sim _ Hwf), Heval in Hcert.
  destruct (check_cycler_entryN_sound _ Hcert) as [restL Henc].
  assert (Hreach : c0 -[tm]->* (encW 18 restL) {{A}}> (S1 >> const S0)).
  { rewrite c0_eq_r1StartN, <- Henc.
    exact (Pos_iter_sound outerSteps (evalHyb r1Start)). }
  eapply multistep_nonhalt; [exact Hreach |].
  apply (progress_nonhalt_simple tm side
    (fun restL : side => (encW 18 restL) {{A}}> (S1 >> const S0)) restL).
  intro tail; exists (tail <* cycDelta); exact (cyc_reaches tail).
Qed.

Print Assumptions nonhalt_from_checked_entry.

Lemma cert_entry :
  check_cycler_entry (Pos.iter stepOuter r1Start outerSteps) = true.
Proof. native_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~ halts tm c0.
Proof. exact (nonhalt_from_checked_entry cert_entry). Qed.

End TM1.

Print Assumptions TM1.nonhalt.
