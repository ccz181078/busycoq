(* 1RB0RB_1RC1LC_0LD1RA_1LF1LE_0LA1LC_1LB--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import String Bool Lists.List Lia PeanoNat.
Import ListNotations.

Open Scope list.
Open Scope sym.
Open Scope nat_scope.

Definition tm := Eval compute in
  (TM_from_str "1RB0RB_1RC1LC_0LD1RA_1LF1LE_0LA1LC_1LB---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma pe_trans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->* c3 -> c1 -->+ c3.
Proof. apply progress_evstep_trans. Qed.

Lemma ep_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma etrans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Lemma pev {c1 c2 : Q * tape} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Fixpoint encRight (R : list bool) : side :=
  match R with
  | [] => 0inf%sym
  | false :: R' => 1%sym >> 0%sym >> encRight R'
  | true :: R' => 1%sym >> 1%sym >> 0%sym >> encRight R'
  end.

Definition cfg_B (tl : side) (R : list bool) : Q * tape :=
  B;; (0%sym >> tl) {{0%sym}} (encRight R).

Definition cfg_C (tl : side) (R : list bool) : Q * tape :=
  C;; tl {{0%sym}} (encRight R).

Definition T2 (tl : side) : side := 1%sym >> 1%sym >> 0%sym >> tl.
Definition T3 (tl : side) : side := 1%sym >> 1%sym >> 1%sym >> 0%sym >> tl.
Definition T4 (tl : side) : side := 1%sym >> 1%sym >> 1%sym >> 1%sym >> 0%sym >> tl.
Definition T6 (tl : side) : side :=
  1%sym >> 1%sym >> 1%sym >> 1%sym >> 1%sym >> 1%sym >> 0%sym >> tl.
Definition T12 (tl : side) : side := 1%sym >> 0%sym >> 1%sym >> 1%sym >> 0%sym >> tl.
Definition T322 (tl : side) : side :=
  1%sym >> 1%sym >> 1%sym >> 0%sym >> 0%sym >> 1%sym >> 1%sym >> 0%sym >> tl.

Lemma rule_B_nil (tl : side) :
  cfg_B tl [] -->+ cfg_C (1%sym >> 0%sym >> tl) [].
Proof. unfold cfg_B, cfg_C; simpl; start_progress. Qed.

Lemma rule_B_true (tl : side) (R : list bool) :
  cfg_B tl (true :: R) -->+ cfg_B (T2 tl) R.
Proof. unfold cfg_B, T2; simpl; start_progress. Qed.

Lemma rule_B_false_nil (tl : side) :
  cfg_B tl [false] -->+ cfg_C (T4 tl) [].
Proof. unfold cfg_B, cfg_C, T4; simpl; start_progress. Qed.

Lemma rule_B_false_false (tl : side) (R : list bool) :
  cfg_B tl (false :: false :: R) -->+ cfg_B (T3 tl) R.
Proof. unfold cfg_B, T3; simpl; start_progress. Qed.

Lemma rule_B_false_true (tl : side) (R : list bool) :
  cfg_B tl (false :: true :: R) -->+ cfg_C (T3 tl) (false :: R).
Proof. unfold cfg_B, cfg_C, T3; simpl; start_progress. Qed.

Lemma rule_C_110 (tl : side) (R : list bool) :
  cfg_C (T2 tl) R -->+ cfg_C tl (true :: R).
Proof. unfold cfg_C, T2; simpl; start_progress. Qed.

Lemma rule_C_111 (tl : side) (R : list bool) :
  cfg_C (1%sym >> 1%sym >> 1%sym >> tl) R -->+ cfg_C (1%sym >> tl) (false :: R).
Proof. unfold cfg_C; simpl; start_progress. Qed.

Lemma rule_C_101 (tl : side) (R : list bool) :
  cfg_C (1%sym >> 0%sym >> 1%sym >> tl) R -->+ cfg_B tl (false :: R).
Proof. unfold cfg_C, cfg_B; simpl; start_progress. Qed.

Lemma rule_C_100_false (tl : side) (R : list bool) :
  cfg_C (1%sym >> 0%sym >> 0%sym >> tl) (false :: R) -->+
    cfg_B (1%sym >> 1%sym >> 1%sym >> 1%sym >> tl) R.
Proof. unfold cfg_C, cfg_B; simpl; start_progress. Qed.

Lemma rule_C_41 (tl : side) (R : list bool) :
  cfg_C (T4 tl) R -->+ cfg_C (T2 tl) (false :: R).
Proof. exact (rule_C_111 (1%sym >> 0%sym >> tl) R). Qed.

Lemma rule_C_61 (tl : side) (R : list bool) :
  cfg_C (T6 tl) R -->+ cfg_C (T4 tl) (false :: R).
Proof. exact (rule_C_111 (1%sym >> 1%sym >> 1%sym >> 0%sym >> tl) R). Qed.

Lemma rule_C_32 (tl : side) (R : list bool) :
  cfg_C (1%sym >> 1%sym >> 1%sym >> 0%sym >> 0%sym >> tl) R -->+
    cfg_B (1%sym >> 1%sym >> 1%sym >> 1%sym >> tl) R.
Proof.
  exact (ptrans (rule_C_111 (0%sym >> 0%sym >> tl) R) (rule_C_100_false tl R)).
Qed.

Lemma rule_C_31_1 (tl : side) (R : list bool) :
  cfg_C (T3 (1%sym >> tl)) R -->+ cfg_B (T3 tl) R.
Proof.
  exact (ptrans (rule_C_111 (0%sym >> 1%sym >> tl) R)
    (ptrans (rule_C_101 tl (false :: R)) (rule_B_false_false tl R))).
Qed.

Lemma rule_B_nil_1 (tl : side) :
  cfg_B (1%sym >> tl) [] -->+ cfg_C (T4 tl) [].
Proof.
  exact (ptrans (rule_B_nil (1%sym >> tl))
    (ptrans (rule_C_101 tl []) (rule_B_false_nil tl))).
Qed.

Lemma rule_B_carry_true (tl : side) (R : list bool) :
  cfg_B (1%sym >> tl) (false :: true :: R) -->+ cfg_B (T3 tl) (false :: R).
Proof.
  exact (ptrans (rule_B_false_true (1%sym >> tl) R) (rule_C_31_1 tl (false :: R))).
Qed.

Lemma rule_C_3_22 (tl : side) (R : list bool) :
  cfg_C (T3 (T2 (T2 tl))) R -->+ cfg_B (T3 (T12 tl)) R.
Proof. exact (rule_C_31_1 (1%sym >> 0%sym >> T2 tl) R). Qed.

Lemma rule_C_3_12 (tl : side) (R : list bool) :
  cfg_C (T3 (T12 tl)) R -->+ cfg_B (T322 tl) R.
Proof. exact (rule_C_31_1 (0%sym >> 1%sym >> 1%sym >> 0%sym >> tl) R). Qed.

Lemma rule_C_322 (tl : side) (R : list bool) :
  cfg_C (T322 tl) R -->+ cfg_B (T6 tl) R.
Proof. exact (rule_C_32 (1%sym >> 1%sym >> 0%sym >> tl) R). Qed.

Lemma rule_C_6 (tl : side) (R : list bool) :
  cfg_C (T6 tl) R -->+ cfg_C tl (true :: false :: false :: R).
Proof.
  exact (ptrans (rule_C_61 tl R)
    (ptrans (rule_C_41 tl (false :: R)) (rule_C_110 tl (false :: false :: R)))).
Qed.

Lemma rule_C_default (R : list bool) :
  cfg_C 0inf%sym R -->+ cfg_B 0inf%sym (true :: R).
Proof.
  unfold cfg_C, cfg_B; simpl; rewrite <- const_unfold; start_progress.
Qed.

Lemma rule_B_norm_exit (tl : side) :
  cfg_B (T2 (T2 tl)) [false] -->+ cfg_C tl [true; true; true; false].
Proof.
  exact (ptrans (rule_B_false_nil (T2 (T2 tl)))
    (ptrans (rule_C_41 (T2 (T2 tl)) [])
      (ptrans (rule_C_110 (T2 (T2 tl)) [false])
        (ptrans (rule_C_110 (T2 tl) [true; false])
          (rule_C_110 tl [true; true; false]))))).
Qed.

Lemma rule_B_carry_exit (tl : side) :
  cfg_B (T3 (T2 (T2 tl))) [false; false] -->+
    cfg_C (T3 (T12 tl)) [true; true; true; false].
Proof.
  exact (ptrans (rule_B_false_false (T3 (T2 (T2 tl))) [])
    (ptrans (rule_B_nil_1 (T2 (T3 (T2 (T2 tl)))))
      (ptrans (rule_C_41 (T2 (T3 (T2 (T2 tl)))) [])
        (ptrans (rule_C_110 (T2 (T3 (T2 (T2 tl)))) [false])
          (ptrans (rule_C_110 (T3 (T2 (T2 tl))) [true; false])
            (ptrans (rule_C_3_22 tl [true; true; false])
              (ptrans (rule_B_true (T3 (T12 tl)) [true; false])
                (ptrans (rule_B_true (T2 (T3 (T12 tl))) [false])
                  (ptrans (rule_B_false_nil (T2 (T2 (T3 (T12 tl)))))
                    (ptrans (rule_C_41 (T2 (T2 (T3 (T12 tl)))) [])
                      (ptrans (rule_C_110 (T2 (T2 (T3 (T12 tl)))) [false])
                        (ptrans (rule_C_110 (T2 (T3 (T12 tl))) [true; false])
                          (rule_C_110 (T3 (T12 tl)) [true; true; false]))))))))))))).
Qed.

Lemma rule_C_3_0 (R : list bool) :
  cfg_C (T3 0inf%sym) R -->+ cfg_B (T4 0inf%sym) R.
Proof.
  unfold T3, T4.
  pose proof (rule_C_32 0inf%sym R) as H.
  repeat rewrite <- const_unfold in *.
  exact H.
Qed.

Lemma rule_C_6_3 (R : list bool) :
  cfg_C (T6 (T2 (T2 (T2 (T3 0inf%sym))))) R -->+
    cfg_B (T3 (T2 (T2 (T2 (T2 (T4 0inf%sym)))))) R.
Proof.
  exact (ptrans (rule_C_6 (T2 (T2 (T2 (T3 0inf%sym)))) R)
    (ptrans (rule_C_110 (T2 (T2 (T3 0inf%sym))) (true :: false :: false :: R))
      (ptrans (rule_C_110 (T2 (T3 0inf%sym)) (true :: true :: false :: false :: R))
        (ptrans (rule_C_110 (T3 0inf%sym) (true :: true :: true :: false :: false :: R))
          (ptrans (rule_C_3_0 (true :: true :: true :: true :: false :: false :: R))
            (ptrans (rule_B_true (T4 0inf%sym) (true :: true :: true :: false :: false :: R))
              (ptrans (rule_B_true (T2 (T4 0inf%sym)) (true :: true :: false :: false :: R))
                (ptrans (rule_B_true (T2 (T2 (T4 0inf%sym))) (true :: false :: false :: R))
                  (ptrans (rule_B_true (T2 (T2 (T2 (T4 0inf%sym)))) (false :: false :: R))
                    (rule_B_false_false (T2 (T2 (T2 (T2 (T4 0inf%sym))))) R)))))))))).
Qed.

Lemma rule_B_carry_3_true (x : side) (R : list bool) :
  cfg_B (T3 x) (false :: true :: R) -->+ cfg_B (T3 (T2 x)) (false :: R).
Proof. exact (rule_B_carry_true (T2 x) R). Qed.

Lemma rule_C_6_4 (R : list bool) :
  cfg_C (T6 (T2 (T2 (T4 0inf%sym)))) R -->+
    cfg_B (T3 (T3 (T2 (T2 (T12 0inf%sym))))) (false :: R).
Proof.
  exact (ptrans (rule_C_6 (T2 (T2 (T4 0inf%sym))) R)
    (ptrans (rule_C_110 (T2 (T4 0inf%sym)) (true :: false :: false :: R))
      (ptrans (rule_C_110 (T4 0inf%sym) (true :: true :: false :: false :: R))
        (ptrans (rule_C_41 0inf%sym (true :: true :: true :: false :: false :: R))
          (ptrans (rule_C_110 0inf%sym (false :: true :: true :: true :: false :: false :: R))
            (ptrans (rule_C_default (true :: false :: true :: true :: true :: false :: false :: R))
              (ptrans (rule_B_true 0inf%sym (true :: false :: true :: true :: true :: false :: false :: R))
                (ptrans (rule_B_true (T2 0inf%sym) (false :: true :: true :: true :: false :: false :: R))
                  (ptrans (rule_B_false_true (T2 (T2 0inf%sym)) (true :: true :: false :: false :: R))
                    (ptrans (rule_C_3_22 0inf%sym (false :: true :: true :: false :: false :: R))
                      (ptrans (rule_B_carry_3_true (T12 0inf%sym) (true :: false :: false :: R))
                        (ptrans (rule_B_carry_3_true (T2 (T12 0inf%sym)) (false :: false :: R))
                          (rule_B_false_false (T3 (T2 (T2 (T12 0inf%sym)))) (false :: R)))))))))))))).
Qed.

Lemma rule_C_12_0 (R : list bool) :
  cfg_C (T12 0inf%sym) R -->+ cfg_B (1%sym >> 0inf%sym) (false :: R).
Proof.
  unfold T12.
  pose proof (rule_C_101 (1%sym >> 0%sym >> 0inf%sym) R) as H.
  repeat rewrite <- const_unfold in *.
  exact H.
Qed.

Lemma rule_B_carry_1_0 (R : list bool) :
  cfg_B (1%sym >> 0inf%sym) (false :: true :: R) -->+ cfg_B (T3 0inf%sym) (false :: R).
Proof. exact (rule_B_carry_true 0inf%sym R). Qed.

Lemma rule_C_6_12 (R : list bool) :
  cfg_C (T6 (T12 0inf%sym)) R -->+
    cfg_B (T3 (T3 0inf%sym)) (false :: R).
Proof.
  exact (ptrans (rule_C_6 (T12 0inf%sym) R)
    (ptrans (rule_C_12_0 (true :: false :: false :: R))
      (ptrans (rule_B_carry_1_0 (false :: false :: R))
        (rule_B_false_false (T3 0inf%sym) (false :: R))))).
Qed.

Fixpoint powT2 (n : nat) (x : side) : side :=
  match n with
  | O => x
  | S n' => T2 (powT2 n' x)
  end.

Fixpoint powTrue (n : nat) (R : list bool) : list bool :=
  match n with
  | O => R
  | S n' => true :: powTrue n' R
  end.

Lemma powT2_comm (n : nat) (x : side) : powT2 n (T2 x) = T2 (powT2 n x).
Proof.
  induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma powTrue_comm (n : nat) (R : list bool) : powTrue n (true :: R) = true :: powTrue n R.
Proof.
  induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma c_pop_T2 (n : nat) (x : side) (R : list bool) :
  cfg_C (powT2 n x) R -->* cfg_C x (powTrue n R).
Proof.
  revert R.
  induction n as [|n IH]; intros R; simpl.
  - apply evstep_refl.
  - rewrite <- powTrue_comm.
    exact (pev (pe_trans (rule_C_110 (powT2 n x) R) (IH (true :: R)))).
Qed.

Lemma b_push_T2 (n : nat) (x : side) (R : list bool) :
  cfg_B x (powTrue n R) -->* cfg_B (powT2 n x) R.
Proof.
  revert x.
  induction n as [|n IH]; intros x; simpl.
  - apply evstep_refl.
  - rewrite <- powT2_comm.
    exact (pev (pe_trans (rule_B_true x (powTrue n R)) (IH (T2 x)))).
Qed.

Lemma b_carry_push_T2 (n : nat) (x : side) (R : list bool) :
  cfg_B (T3 x) (false :: powTrue n R) -->* cfg_B (T3 (powT2 n x)) (false :: R).
Proof.
  revert x.
  induction n as [|n IH]; intros x; simpl.
  - apply evstep_refl.
  - rewrite <- powT2_comm.
    exact (pev (pe_trans (rule_B_carry_3_true x (powTrue n R)) (IH (T2 x)))).
Qed.

Lemma c_pop_T6 (b : nat) (tl : side) (R : list bool) :
  cfg_C (T6 (powT2 b tl)) R -->+ cfg_C tl (powTrue (b + 1) (false :: false :: R)).
Proof.
  replace (b + 1) with (S b) by lia; simpl.
  eapply pe_trans; [apply (rule_C_6 (powT2 b tl) R) |].
  pose proof (c_pop_T2 b tl (true :: false :: false :: R)) as H.
  rewrite powTrue_comm in H.
  exact H.
Qed.

Lemma b_norm_block (m : nat) (x : side) (R : list bool) :
  cfg_B x (powTrue m (false :: false :: R)) -->+ cfg_B (T3 (powT2 m x)) R.
Proof.
  exact (ep_trans (b_push_T2 m x (false :: false :: R)) (rule_B_false_false (powT2 m x) R)).
Qed.

Lemma b_carry_block (m : nat) (x : side) (R : list bool) :
  cfg_B (T3 x) (false :: powTrue m (false :: false :: R)) -->+
    cfg_B (T3 (T3 (powT2 m x))) (false :: R).
Proof.
  exact (ep_trans (b_carry_push_T2 m x (false :: false :: R))
    (rule_B_false_false (T3 (powT2 m x)) (false :: R))).
Qed.

Lemma b_norm_end (a : nat) (x : side) :
  cfg_B x (powTrue a [true; true; true; false]) -->+
    cfg_C (powT2 (a + 1) x) [true; true; true; false].
Proof.
  replace (a + 1) with (S a) by lia; simpl.
  exact (ep_trans (b_push_T2 a x [true; true; true; false])
    (ptrans (rule_B_true (powT2 a x) [true; true; false])
      (ptrans (rule_B_true (T2 (powT2 a x)) [true; false])
        (ptrans (rule_B_true (T2 (T2 (powT2 a x))) [false])
          (rule_B_norm_exit (T2 (powT2 a x))))))).
Qed.

Lemma b_carry_end (a : nat) (x : side) :
  cfg_B (T3 x) (false :: powTrue a [true; true; true; false]) -->+
    cfg_C (T3 (T12 (powT2 (a + 1) x))) [true; true; true; false].
Proof.
  replace (a + 1) with (S a) by lia; simpl.
  exact (ep_trans (b_carry_push_T2 a x [true; true; true; false])
    (ptrans (rule_B_carry_3_true (powT2 a x) [true; true; false])
      (ptrans (rule_B_carry_3_true (T2 (powT2 a x)) [true; false])
        (ptrans (rule_B_carry_3_true (T2 (T2 (powT2 a x))) [false])
          (rule_B_carry_exit (T2 (powT2 a x))))))).
Qed.

Definition StepNorm (s1 s2 : side) : Prop :=
  forall R : list bool, cfg_C s1 R -->+ cfg_B s2 R.

Definition StepCarry (s1 s2 : side) : Prop :=
  forall R : list bool, cfg_C s1 R -->+ cfg_B (T3 s2) (false :: R).

Inductive NormSteps : nat -> side -> side -> Prop :=
| NormSteps_zero (s : side) : NormSteps 0 s s
| NormSteps_succ {n : nat} {s1 s2 s3 : side} :
    StepNorm s1 s2 -> NormSteps n s2 s3 -> NormSteps (S n) s1 s3.

Definition CarryRun (n : nat) (s1 s2 : side) : Prop :=
  exists mid : side, NormSteps n s1 mid /\ StepCarry mid s2.

Lemma NormSteps_trans {m n : nat} {s1 s2 s3 : side}
    (H1 : NormSteps m s1 s2) (H2 : NormSteps n s2 s3) : NormSteps (m + n) s1 s3.
Proof.
  induction H1; simpl; [exact H2 | eapply NormSteps_succ; eauto].
Qed.

Lemma CarryRun_prepend {m n : nat} {s1 s2 s3 : side}
    (H1 : NormSteps m s1 s2) (H2 : CarryRun n s2 s3) : CarryRun (m + n) s1 s3.
Proof.
  destruct H2 as [mid [Hm Hc]].
  exists mid; split; [exact (NormSteps_trans H1 Hm) | exact Hc].
Qed.

Lemma stepNorm_3_22 (b : nat) (s : side) :
  StepNorm (T3 (powT2 (b + 2) s)) (T3 (T12 (powT2 b s))).
Proof.
  replace (b + 2) with (S (S b)) by lia; simpl.
  intro R; exact (rule_C_3_22 (powT2 b s) R).
Qed.

Lemma stepNorm_3_12 (s : side) : StepNorm (T3 (T12 s)) (T322 s).
Proof. intro R; exact (rule_C_3_12 s R). Qed.

Lemma stepNorm_322 (s : side) : StepNorm (T322 s) (T6 s).
Proof. intro R; exact (rule_C_322 s R). Qed.

Lemma stepNorm_T6 {s1 s2 : side} (b : nat) (H : StepNorm s1 s2) :
  StepNorm (T6 (powT2 b s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  intro R.
  exact (ptrans (c_pop_T6 b s1 R)
    (ptrans (H (powTrue (b + 1) (false :: false :: R))) (b_norm_block (b + 1) s2 R))).
Qed.

Lemma stepCarry_T6 {s1 s2 : side} (b : nat) (H : StepCarry s1 s2) :
  StepCarry (T6 (powT2 b s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  intro R.
  exact (ptrans (c_pop_T6 b s1 R)
    (ptrans (H (powTrue (b + 1) (false :: false :: R))) (b_carry_block (b + 1) s2 R))).
Qed.

Lemma normSteps_cycle_T3_12 {s1 s2 : side} (b : nat) (H : StepNorm s1 s2) :
  NormSteps 3 (T3 (T12 (powT2 b s1))) (T3 (powT2 (b + 1) s2)).
Proof.
  exact (NormSteps_succ (stepNorm_3_12 _)
    (NormSteps_succ (stepNorm_322 _)
      (NormSteps_succ (stepNorm_T6 b H) (NormSteps_zero _)))).
Qed.

Lemma normSteps_cycle_T3 {s1 s2 : side} (b : nat) (H : StepNorm s1 s2) :
  NormSteps 4 (T3 (powT2 (b + 2) s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  exact (NormSteps_succ (stepNorm_3_22 b s1) (normSteps_cycle_T3_12 b H)).
Qed.

Lemma carryRun_cycle_T3_12 {s1 s2 : side} (b : nat) (H : StepCarry s1 s2) :
  CarryRun 2 (T3 (T12 (powT2 b s1))) (T3 (powT2 (b + 1) s2)).
Proof.
  exists (T6 (powT2 b s1)).
  split.
  - exact (NormSteps_succ (stepNorm_3_12 _) (NormSteps_succ (stepNorm_322 _) (NormSteps_zero _))).
  - exact (stepCarry_T6 b H).
Qed.

Lemma carryRun_cycle_T3 {s1 s2 : side} (b : nat) (H : StepCarry s1 s2) :
  CarryRun 3 (T3 (powT2 (b + 2) s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  destruct (carryRun_cycle_T3_12 b H) as [mid [Hm Hc]].
  exists mid; split; [exact (NormSteps_succ (stepNorm_3_22 b s1) Hm) | exact Hc].
Qed.

Lemma lift_NormSteps {n : nat} {s1 s2 : side} (H : NormSteps n s1 s2) :
  forall b : nat,
    NormSteps (4 * n) (T3 (powT2 (b + n + 1) s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  induction H as [s | m s1 s2 s3 Hstep Hrest IH]; intro b.
  - replace (4 * 0) with 0 by lia.
    replace (b + 0 + 1) with (b + 1) by lia.
    apply NormSteps_zero.
  - assert (H1 : NormSteps 4 (T3 (powT2 (b + S m + 1) s1)) (T3 (powT2 (b + m + 1) s2))).
    { replace (b + S m + 1) with ((b + m) + 2) by lia.
      replace (b + m + 1) with ((b + m) + 1) by lia.
      exact (normSteps_cycle_T3 (b + m) Hstep). }
    pose proof (NormSteps_trans H1 (IH b)) as H2.
    replace (4 + 4 * m) with (4 * S m) in H2 by lia.
    exact H2.
Qed.

Lemma lift_NormSteps_T3_12 {n : nat} {s1 s2 s3 : side}
    (H1 : StepNorm s1 s2) (H2 : NormSteps n s2 s3) (b : nat) :
  NormSteps (4 * n + 3) (T3 (T12 (powT2 (b + n) s1))) (T3 (powT2 (b + 1) s3)).
Proof.
  pose proof (normSteps_cycle_T3_12 (b + n) H1) as Ha.
  replace ((b + n) + 1) with (b + n + 1) in Ha by lia.
  pose proof (lift_NormSteps H2 b) as Hb.
  pose proof (NormSteps_trans Ha Hb) as Hc.
  replace (3 + 4 * n) with (4 * n + 3) in Hc by lia.
  exact Hc.
Qed.

Lemma lift_CarryRun {n : nat} {s1 s2 : side} (H : CarryRun n s1 s2) (b : nat) :
  CarryRun (4 * n + 3) (T3 (powT2 (b + n + 2) s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  destruct H as [mid [Hm Hc]].
  assert (H1 : NormSteps (4 * n) (T3 (powT2 (b + n + 2) s1)) (T3 (powT2 (b + 2) mid))).
  { replace (b + n + 2) with ((b + 1) + n + 1) by lia.
    replace (b + 2) with ((b + 1) + 1) by lia.
    exact (lift_NormSteps Hm (b + 1)). }
  exact (CarryRun_prepend H1 (carryRun_cycle_T3 b Hc)).
Qed.

Lemma lift_CarryRun_T3_12 {n : nat} {s1 s2 : side} (H : CarryRun n s1 s2) (b : nat) :
  CarryRun (4 * n + 2) (T3 (T12 (powT2 (b + n) s1))) (T3 (powT2 (b + 1) s2)).
Proof.
  destruct H as [mid [Hm Hc]].
  inversion Hm as [s Heq1 Heq2 Heq3 | m s_a s_next s_b Hstep Hrest Heq1 Heq2 Heq3]; subst.
  - replace (4 * 0 + 2) with 2 by lia.
    replace (b + 0) with b by lia.
    exact (carryRun_cycle_T3_12 b Hc).
  - assert (H1 : NormSteps 3 (T3 (T12 (powT2 (b + S m) s1))) (T3 (powT2 (b + m + 2) s_next))).
    { replace (b + S m) with ((b + m) + 1) by lia.
      replace (b + m + 2) with (((b + m) + 1) + 1) by lia.
      exact (normSteps_cycle_T3_12 ((b + m) + 1) Hstep). }
    assert (Hcr : CarryRun m s_next s2) by (exists mid; split; assumption).
    pose proof (lift_CarryRun Hcr b) as H2.
    pose proof (CarryRun_prepend H1 H2) as H3.
    replace (3 + (4 * m + 3)) with (4 * S m + 2) in H3 by lia.
    exact H3.
Qed.

Lemma run_StepNorm {s1 s2 : side} (H : StepNorm s1 s2) (a : nat) :
  cfg_C (powT2 a s1) [true; true; true; false] -->+
    cfg_C (powT2 (a + 1) s2) [true; true; true; false].
Proof.
  exact (ep_trans (c_pop_T2 a s1 [true; true; true; false])
    (ptrans (H (powTrue a [true; true; true; false])) (b_norm_end a s2))).
Qed.

Lemma run_NormSteps {n : nat} {s1 s2 : side} (H : NormSteps n s1 s2) :
  forall a : nat,
    cfg_C (powT2 a s1) [true; true; true; false] -->*
      cfg_C (powT2 (a + n) s2) [true; true; true; false].
Proof.
  induction H as [s | m s1 s2 s3 Hstep Hrest IH]; intro a.
  - replace (a + 0) with a by lia.
    apply evstep_refl.
  - pose proof (pev (run_StepNorm Hstep a)) as H1.
    pose proof (IH (a + 1)) as H2.
    replace (a + 1 + m) with (a + S m) in H2 by lia.
    exact (etrans H1 H2).
Qed.

Lemma run_StepCarry {s1 s2 : side} (H : StepCarry s1 s2) (a : nat) :
  cfg_C (powT2 a s1) [true; true; true; false] -->+
    cfg_C (T3 (T12 (powT2 (a + 1) s2))) [true; true; true; false].
Proof.
  exact (ep_trans (c_pop_T2 a s1 [true; true; true; false])
    (ptrans (H (powTrue a [true; true; true; false])) (b_carry_end a s2))).
Qed.

Lemma run_CarryRun {n : nat} {s1 s2 : side} (H : CarryRun n s1 s2) (a : nat) :
  cfg_C (powT2 a s1) [true; true; true; false] -->+
    cfg_C (T3 (T12 (powT2 (a + n + 1) s2))) [true; true; true; false].
Proof.
  destruct H as [mid [Hm Hc]].
  exact (ep_trans (run_NormSteps Hm a) (run_StepCarry Hc (a + n))).
Qed.

Fixpoint N (k : nat) : nat :=
  match k with
  | O => 0
  | S k' => 4 * N k' + 3
  end.

Fixpoint ChainA (k : nat) : side :=
  match k with
  | O => T3 (powT2 2 (T12 0inf%sym))
  | S k' => T3 (powT2 (2 * N (S k') + 3) (ChainA k'))
  end.

Fixpoint ChainB (k : nat) : side :=
  match k with
  | O => T3 0inf%sym
  | S k' => T3 (powT2 (N (S k') + 2) (ChainB k'))
  end.

Fixpoint ChainC (k : nat) : side :=
  match k with
  | O => T3 (powT2 4 (T4 0inf%sym))
  | S k' => T3 (powT2 (3 * N (S k') + 4) (ChainC k'))
  end.

Definition TopA (k : nat) : side := T3 (T12 (powT2 (2 * N (S k) + 1) (ChainA k))).
Definition TopB (k : nat) : side := T3 (T12 (powT2 (N (S (S k))) (ChainB (S k)))).
Definition State (k : nat) : Q * tape :=
  cfg_C (powT2 (N (S k)) (ChainC k)) [true; true; true; false].

Lemma carryRun_base12 : CarryRun 2 (T3 (T12 (T12 0inf%sym))) (T3 0inf%sym).
Proof.
  exists (T6 (T12 0inf%sym)).
  split.
  - exact (NormSteps_succ (stepNorm_3_12 _) (NormSteps_succ (stepNorm_322 _) (NormSteps_zero _))).
  - exact (fun R => rule_C_6_12 R).
Qed.

Lemma normSteps_base3 : NormSteps 3 (T3 (T12 (powT2 3 (T3 0inf%sym)))) (ChainC 0).
Proof.
  exact (NormSteps_succ (stepNorm_3_12 _)
    (NormSteps_succ (stepNorm_322 _)
      (NormSteps_succ (fun R => rule_C_6_3 R) (NormSteps_zero _)))).
Qed.

Lemma carryRun_base4 : CarryRun 3 (ChainC 0) (ChainA 0).
Proof.
  exists (T6 (powT2 2 (T4 0inf%sym))).
  split.
  - exact (NormSteps_succ (stepNorm_3_22 2 (T4 0inf%sym))
      (NormSteps_succ (stepNorm_3_12 _)
        (NormSteps_succ (stepNorm_322 _) (NormSteps_zero _)))).
  - exact (fun R => rule_C_6_4 R).
Qed.

Lemma phase1_chain (k : nat) : CarryRun (N (S k)) (ChainA k) (ChainB k).
Proof.
  induction k as [|k IH].
  - destruct carryRun_base12 as [mid [Hm Hc]].
    exists mid; split; [| exact Hc].
    exact (NormSteps_succ (stepNorm_3_22 0 (T12 0inf%sym)) Hm).
  - pose proof (lift_CarryRun IH (N (S k) + 1)) as H.
    change (4 * N (S k) + 3) with (N (S (S k))) in H.
    replace ((N (S k) + 1) + N (S k) + 2) with (2 * N (S k) + 3) in H by lia.
    replace ((N (S k) + 1) + 1) with (N (S k) + 2) in H by lia.
    exact H.
Qed.

Lemma phase1_top (k : nat) : CarryRun (4 * N (S k) + 2) (TopA k) (ChainB (S k)).
Proof.
  unfold TopA.
  pose proof (lift_CarryRun_T3_12 (phase1_chain k) (N (S k) + 1)) as H.
  replace ((N (S k) + 1) + N (S k)) with (2 * N (S k) + 1) in H by lia.
  replace ((N (S k) + 1) + 1) with (N (S k) + 2) in H by lia.
  exact H.
Qed.

Lemma phase2_chain (k : nat) : NormSteps (N (S k) + 1) (ChainB (S k)) (ChainC k).
Proof.
  induction k as [|k IH].
  - change (N 1 + 1) with 4.
    change (ChainB 1) with (T3 (powT2 5 (T3 0inf%sym))).
    exact (NormSteps_succ (stepNorm_3_22 3 (T3 0inf%sym)) normSteps_base3).
  - pose proof (lift_NormSteps IH (3 * N (S k) + 3)) as H.
    assert (Heq1 : 4 * (N (S k) + 1) = N (S (S k)) + 1) by (simpl; lia).
    assert (Heq2 : (3 * N (S k) + 3) + (N (S k) + 1) + 1 = N (S (S k)) + 2) by (simpl; lia).
    assert (Heq3 : (3 * N (S k) + 3) + 1 = 3 * N (S k) + 4) by lia.
    rewrite Heq1, Heq2, Heq3 in H.
    exact H.
Qed.

Lemma phase2_top (k : nat) : NormSteps (N (S (S k))) (TopB k) (ChainC (S k)).
Proof.
  unfold TopB.
  pose proof (phase2_chain k) as Hchain.
  remember (N (S k)) as n_sk eqn:En.
  replace (n_sk + 1) with (S n_sk) in Hchain by lia.
  inversion Hchain as [| m s1 s_mid s3 Hstep Hrest Heq1 Heq2 Heq3]; subst.
  pose proof (lift_NormSteps_T3_12 Hstep Hrest (3 * N (S k) + 3)) as H.
  replace (4 * N (S k) + 3) with (N (S (S k))) in H by (simpl; lia).
  replace ((3 * N (S k) + 3) + N (S k)) with (N (S (S k))) in H by (simpl; lia).
  replace ((3 * N (S k) + 3) + 1) with (3 * N (S k) + 4) in H by lia.
  exact H.
Qed.

Lemma phase3_chain (k : nat) : CarryRun (N (S k)) (ChainC k) (ChainA k).
Proof.
  induction k as [|k IH].
  - exact carryRun_base4.
  - pose proof (lift_CarryRun IH (2 * N (S k) + 2)) as H.
    change (4 * N (S k) + 3) with (N (S (S k))) in H.
    replace ((2 * N (S k) + 2) + N (S k) + 2) with (3 * N (S k) + 4) in H by lia.
    replace ((2 * N (S k) + 2) + 1) with (2 * N (S k) + 3) in H by lia.
    exact H.
Qed.

Lemma state_step (k : nat) : State k -->+ State (S k).
Proof.
  unfold State.
  pose proof (run_CarryRun (phase3_chain k) (N (S k))) as H3.
  replace (N (S k) + N (S k) + 1) with (2 * N (S k) + 1) in H3 by lia.
  fold (TopA k) in H3.
  pose proof (run_CarryRun (phase1_top k) 0) as H1.
  assert (Heq1 : 0 + (4 * N (S k) + 2) + 1 = N (S (S k))) by (simpl; lia).
  rewrite Heq1 in H1.
  fold (TopB k) in H1.
  pose proof (run_NormSteps (phase2_top k) 0) as H2.
  replace (0 + N (S (S k))) with (N (S (S k))) in H2 by lia.
  exact (ptrans H3 (pe_trans H1 H2)).
Qed.

Lemma init_step5 : c0 -->+ cfg_C 0inf%sym [true].
Proof. unfold c0, tape0, cfg_C; simpl; start_progress. Qed.

Lemma start_to_step127 :
  cfg_C 0inf%sym [true] -->+ cfg_C (T4 0inf%sym) [true; true; true; false].
Proof.
  exact (ptrans (rule_C_default [true])
    (ptrans (rule_B_true 0inf%sym [true])
      (ptrans (rule_B_true (T2 0inf%sym) [])
        (ptrans (rule_B_nil_1 (1%sym >> 0%sym >> T2 0inf%sym))
          (ptrans (rule_C_41 (T12 0inf%sym) [])
            (ptrans (rule_C_110 (T12 0inf%sym) [false])
              (ptrans (rule_C_12_0 [true; false])
                (ptrans (rule_B_carry_1_0 [false])
                  (ptrans (rule_B_false_false (T3 0inf%sym) [])
                    (ptrans (rule_B_nil_1 (1%sym >> 1%sym >> 0%sym >> T3 0inf%sym))
                      (ptrans (rule_C_41 (T2 (T3 0inf%sym)) [])
                        (ptrans (rule_C_110 (T2 (T3 0inf%sym)) [false])
                          (ptrans (rule_C_110 (T3 0inf%sym) [true; false])
                            (ptrans (rule_C_3_0 [true; true; false])
                              (ptrans (rule_B_true (T4 0inf%sym) [true; false])
                                (ptrans (rule_B_true (T2 (T4 0inf%sym)) [false])
                                  (rule_B_norm_exit (T4 0inf%sym)))))))))))))))))).
Qed.

Lemma step127_to_start :
  cfg_C (T4 0inf%sym) [true; true; true; false] -->+
    cfg_C (T3 (T12 (T12 0inf%sym))) [true; true; true; false].
Proof.
  exact (ptrans (rule_C_41 0inf%sym [true; true; true; false])
    (ptrans (rule_C_110 0inf%sym [false; true; true; true; false])
      (ptrans (rule_C_default [true; false; true; true; true; false])
        (ptrans (rule_B_true 0inf%sym [true; false; true; true; true; false])
          (ptrans (rule_B_true (T2 0inf%sym) [false; true; true; true; false])
            (ptrans (rule_B_false_true (T2 (T2 0inf%sym)) [true; true; false])
              (ptrans (rule_C_3_22 0inf%sym [false; true; true; false])
                (ptrans (rule_B_carry_3_true (T12 0inf%sym) [true; false])
                  (ptrans (rule_B_carry_3_true (T2 (T12 0inf%sym)) [false])
                    (rule_B_carry_exit (T12 0inf%sym))))))))))).
Qed.

Lemma init_to_start :
  c0 -->+ cfg_C (T3 (T12 (T12 0inf%sym))) [true; true; true; false].
Proof.
  exact (ptrans init_step5 (ptrans start_to_step127 step127_to_start)).
Qed.

Lemma init_to_state0 : c0 -->+ State 0.
Proof.
  pose proof init_to_start as H0.
  pose proof (run_CarryRun carryRun_base12 0) as H1.
  pose proof (run_NormSteps normSteps_base3 0) as H2.
  exact (ptrans H0 (pe_trans H1 H2)).
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt with (c' := State 0).
  - exact (pev init_to_state0).
  - eapply progress_nonhalt_simple with (C := State) (i0 := 0).
    intro k; exists (S k); exact (state_step k).
Qed.

Print Assumptions nonhalt.
