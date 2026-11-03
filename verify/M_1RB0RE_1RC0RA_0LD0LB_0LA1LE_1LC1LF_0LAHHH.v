(* 1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA--- halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat ZifyN NArith PeanoNat Bool String Lists.Streams List.
Import ListNotations.

Open Scope list.
Open Scope sym.

Definition tm : TM := Eval compute in
  (TM_from_str "1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope N_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ========================================================================== *)
(* Section 0: Generic Helpers (N, replicate, repBlock, step compositions)     *)
(* ========================================================================== *)

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

Lemma N_peano_ind (P : N -> Prop)
  (H0 : P 0) (HS : forall n : N, P n -> P (n + 1)) :
  forall n : N, P n.
Proof.
  intro n. induction n using N.peano_ind.
  - exact H0.
  - rewrite <- N.add_1_r. exact (HS n IHn).
Qed.

Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | 0%nat => []
  | S n' => x :: replicate n' x
  end.

Lemma replicate_add {A : Type} (m n : nat) (x : A) :
  replicate (m + n)%nat x = replicate m x ++ replicate n x.
Proof.
  induction m as [| m' ih]; simpl; [reflexivity | rewrite ih; reflexivity].
Qed.

Lemma replicate_succ_r {A : Type} (n : nat) (x : A) :
  replicate (S n) x = replicate n x ++ [x].
Proof.
  induction n as [| n' ih]; [reflexivity |].
  change (replicate (S (S n')) x) with (x :: replicate (S n') x).
  rewrite ih at 1; reflexivity.
Qed.

Definition nreplicate {A : Type} (n : N) (x : A) : list A :=
  replicate (N.to_nat n) x.

Lemma nreplicate_0 {A : Type} (x : A) : nreplicate 0 x = [].
Proof. reflexivity. Qed.

Lemma nreplicate_succ {A : Type} (n : N) (x : A) :
  nreplicate (n + 1) x = x :: nreplicate n x.
Proof.
  unfold nreplicate.
  replace (N.to_nat (n + 1)) with (S (N.to_nat n)) by lia.
  reflexivity.
Qed.

Lemma nreplicate_succ_r {A : Type} (n : N) (x : A) :
  nreplicate (n + 1) x = nreplicate n x ++ [x].
Proof.
  unfold nreplicate.
  replace (N.to_nat (n + 1)) with (S (N.to_nat n)) by lia.
  apply replicate_succ_r.
Qed.

Lemma nreplicate_add {A : Type} (m n : N) (x : A) :
  nreplicate (m + n) x = nreplicate m x ++ nreplicate n x.
Proof.
  unfold nreplicate.
  rewrite N2Nat.inj_add.
  apply replicate_add.
Qed.

Fixpoint repBlockNat {A : Type} (blk : list A) (k : nat) : list A :=
  match k with
  | 0%nat => []
  | S k' => blk ++ repBlockNat blk k'
  end.

Lemma repBlockNat_add {A : Type} (blk : list A) (k1 k2 : nat) :
  repBlockNat blk (k1 + k2)%nat = repBlockNat blk k1 ++ repBlockNat blk k2.
Proof.
  induction k1 as [| k1 ih]; simpl; [reflexivity |].
  rewrite ih, app_assoc. reflexivity.
Qed.

Lemma repBlockNat_succ_r {A : Type} (blk : list A) (k : nat) :
  repBlockNat blk (S k) = repBlockNat blk k ++ blk.
Proof.
  replace (S k) with (k + 1)%nat by lia.
  rewrite repBlockNat_add; simpl.
  rewrite app_nil_r; reflexivity.
Qed.

Definition repBlock {A : Type} (blk : list A) (k : N) : list A :=
  repBlockNat blk (N.to_nat k).

Lemma repBlock_0 {A : Type} (blk : list A) : repBlock blk 0 = [].
Proof. reflexivity. Qed.

Lemma repBlock_1 {A : Type} (blk : list A) : repBlock blk 1 = blk.
Proof. unfold repBlock; simpl; apply app_nil_r. Qed.

Lemma repBlock_succ_l {A : Type} (blk : list A) (k : N) :
  repBlock blk (k + 1) = blk ++ repBlock blk k.
Proof.
  unfold repBlock.
  replace (N.to_nat (k + 1)) with (S (N.to_nat k)) by lia.
  reflexivity.
Qed.

Lemma repBlock_add {A : Type} (blk : list A) (k1 k2 : N) :
  repBlock blk (k1 + k2) = repBlock blk k1 ++ repBlock blk k2.
Proof.
  unfold repBlock.
  rewrite N2Nat.inj_add.
  apply repBlockNat_add.
Qed.

Lemma repBlock_succ_r {A : Type} (blk : list A) (k : N) :
  repBlock blk (k + 1) = repBlock blk k ++ blk.
Proof.
  unfold repBlock.
  replace (N.to_nat (k + 1)) with (S (N.to_nat k)) by lia.
  apply repBlockNat_succ_r.
Qed.

Definition rep0 (n : N) : list N := nreplicate n 0.

Lemma rep0_0 : rep0 0 = [].
Proof. reflexivity. Qed.

Lemma rep0_1 : rep0 1 = [0].
Proof. reflexivity. Qed.

Lemma rep0_2 : rep0 2 = [0; 0].
Proof. reflexivity. Qed.

Lemma rep0_3 : rep0 3 = [0; 0; 0].
Proof. reflexivity. Qed.

Lemma rep0_succ (n : N) : rep0 (n + 1) = 0 :: rep0 n.
Proof. apply nreplicate_succ. Qed.

Lemma rep0_succ_r (n : N) : rep0 (n + 1) = rep0 n ++ [0].
Proof. apply nreplicate_succ_r. Qed.

Lemma rep0_add (m n : N) : rep0 (m + n) = rep0 m ++ rep0 n.
Proof. apply nreplicate_add. Qed.

Lemma rep0_append_zero_cons (k : N) (L : list N) :
  rep0 k ++ (0 :: L) = 0 :: (rep0 k ++ L).
Proof.
  induction k as [| k ih] using N_peano_ind; [reflexivity |].
  rewrite !rep0_succ; simpl; rewrite ih; reflexivity.
Qed.

(* ========================================================================== *)
(* Section 1: 2nd-Order Digit-Stack Encodings & 19 Local Separator Rules      *)
(* ========================================================================== *)

Fixpoint encLeft1 (L : list N) : side :=
  match L with
  | [] => 0inf%sym
  | a :: L' => [1]%sym ^^ (S (N.to_nat a)) *> (0%sym >> encLeft1 L')
  end.

Definition encRight1 : list N -> side := encLeft1.

Definition encTailL (a : N) (L : list N) : side :=
  [1]%sym ^^ (N.to_nat a) *> (0%sym >> encLeft1 L).

Definition encTailR (d : N) (R : list N) : side :=
  [1]%sym ^^ (N.to_nat d) *> (0%sym >> encRight1 R).

Definition bumpHead (L : list N) : list N :=
  match L with
  | [] => [0]
  | b :: L' => (b + 1) :: L'
  end.

Lemma encLeft_cons_one (L : list N) :
  1%sym >> encLeft1 L = encLeft1 (bumpHead L).
Proof.
  destruct L as [| b L']; simpl.
  - rewrite <- const_unfold; reflexivity.
  - replace (N.to_nat (b + 1)) with (S (N.to_nat b)) by lia.
    reflexivity.
Qed.

Lemma encRight_cons_one (R : list N) :
  1%sym >> encRight1 R = encRight1 (bumpHead R).
Proof.
  destruct R as [| d R']; simpl.
  - rewrite <- const_unfold; reflexivity.
  - replace (N.to_nat (d + 1)) with (S (N.to_nat d)) by lia.
    reflexivity.
Qed.

Lemma encLeft_zero (L : list N) :
  encLeft1 (0 :: L) = 1%sym >> 0%sym >> encLeft1 L.
Proof. reflexivity. Qed.

Lemma encLeft_one (L : list N) :
  encLeft1 (1 :: L) = 1%sym >> 1%sym >> 0%sym >> encLeft1 L.
Proof. reflexivity. Qed.

Lemma encRight_zero (R : list N) :
  encRight1 (0 :: R) = 1%sym >> 0%sym >> encRight1 R.
Proof. reflexivity. Qed.

Lemma encRight_one (R : list N) :
  encRight1 (1 :: R) = 1%sym >> 1%sym >> 0%sym >> encRight1 R.
Proof. reflexivity. Qed.

Lemma encRight_two (R : list N) :
  encRight1 (2 :: R) = 1%sym >> 1%sym >> 1%sym >> 0%sym >> encRight1 R.
Proof. reflexivity. Qed.

Lemma encLeft_cons_tail (a : N) (L : list N) :
  encLeft1 (a :: L) = 1%sym >> encTailL a L.
Proof. reflexivity. Qed.

Lemma encRight_cons_tail (d : N) (R : list N) :
  encRight1 (d :: R) = 1%sym >> encTailR d R.
Proof. reflexivity. Qed.

Lemma encLeft_add_one (a : N) (L : list N) :
  encLeft1 ((a + 1) :: L) = 1%sym >> encLeft1 (a :: L).
Proof.
  unfold encLeft1; fold encLeft1.
  replace (N.to_nat (a + 1)) with (S (N.to_nat a)) by lia.
  reflexivity.
Qed.

Lemma encLeft_add_two (a : N) (L : list N) :
  encLeft1 ((a + 2) :: L) = 1%sym >> 1%sym >> encLeft1 (a :: L).
Proof.
  unfold encLeft1; fold encLeft1.
  replace (N.to_nat (a + 2)) with (S (S (N.to_nat a))) by lia.
  reflexivity.
Qed.

Lemma encRight_add_one (d : N) (R : list N) :
  encRight1 ((d + 1) :: R) = 1%sym >> encRight1 (d :: R).
Proof.
  unfold encRight1, encLeft1; fold encLeft1.
  replace (N.to_nat (d + 1)) with (S (N.to_nat d)) by lia.
  reflexivity.
Qed.

Lemma encRight_add_two (d : N) (R : list N) :
  encRight1 ((d + 2) :: R) = 1%sym >> 1%sym >> encRight1 (d :: R).
Proof.
  unfold encRight1, encLeft1; fold encLeft1.
  replace (N.to_nat (d + 2)) with (S (S (N.to_nat d))) by lia.
  reflexivity.
Qed.

Definition cfg_BR (L R : list N) : Q * tape :=
  encLeft1 L {{B}}> encRight1 R.

Definition cfg_C (L R : list N) : Q * tape :=
  C;; encLeft1 L {{0%sym}} encRight1 R.

Definition cfg_B (L R : list N) : Q * tape :=
  B;; encLeft1 L {{0%sym}} encRight1 R.

Definition cfg_DR0 (L R : list N) : Q * tape :=
  D;; encLeft1 L {{0%sym}} (0%sym >> encRight1 R).

Definition cfg_Halt (l r : side) : Q * tape :=
  F;; l {{1%sym}} r.

Inductive StackMode : Type :=
  | SM_BR
  | SM_C
  | SM_B
  | SM_DR0.

Definition evalStackCfg1 (mode : StackMode) (L R : list N) : Q * tape :=
  match mode with
  | SM_BR => cfg_BR L R
  | SM_C => cfg_C L R
  | SM_B => cfg_B L R
  | SM_DR0 => cfg_DR0 L R
  end.

Lemma init_reaches_stack : c0 -->+ cfg_B [0] [].
Proof.
  unfold c0, cfg_B; rewrite encLeft_zero; simpl; start_progress.
Qed.

Lemma rule_B_nil (L : list N) :
  cfg_B L [] -->+ cfg_C (bumpHead L) [].
Proof.
  unfold cfg_B, cfg_C; rewrite <- encLeft_cons_one; simpl; start_progress.
Qed.

Lemma rule_B_zero (L R : list N) :
  cfg_B L (0 :: R) -->+ cfg_B (0 :: L) R.
Proof.
  unfold cfg_B; rewrite encRight_zero, encLeft_zero; simpl; start_progress.
Qed.

Lemma rule_B_succ (d : N) (L R : list N) :
  cfg_B L ((d + 1) :: R) -->+ cfg_BR L (0 :: d :: R).
Proof.
  unfold cfg_B, cfg_BR.
  rewrite encRight_add_one, (encRight_zero (d :: R)), (encRight_cons_tail d R).
  simpl; start_progress.
Qed.

Lemma rule_BR_nil (L : list N) :
  cfg_BR L [] -->+ cfg_C (bumpHead L) [].
Proof.
  exact (rule_B_nil L).
Qed.

Lemma rule_BR_zero (L R : list N) :
  cfg_BR L (0 :: R) -->+ cfg_BR (0 :: L) R.
Proof.
  unfold cfg_BR; rewrite encRight_zero, encLeft_zero; simpl; start_progress.
Qed.

Lemma rule_BR_one (L R : list N) :
  cfg_BR L (1 :: R) -->+ cfg_DR0 L (bumpHead R).
Proof.
  unfold cfg_BR, cfg_DR0; rewrite encRight_one, <- encRight_cons_one; simpl; start_progress.
Qed.

Lemma rule_BR_add_two (d : N) (L R : list N) :
  cfg_BR L ((d + 2) :: R) -->+ cfg_B (bumpHead L) (d :: R).
Proof.
  unfold cfg_BR, cfg_B.
  rewrite encRight_add_two, (encRight_cons_tail d R), <- encLeft_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_DR0_nil (R : list N) :
  cfg_DR0 [] R -->+ cfg_C [1] R.
Proof.
  unfold cfg_DR0, cfg_C; simpl; start_progress.
Qed.

Lemma rule_DR0_zero (L R : list N) :
  cfg_DR0 (0 :: L) R -->+ cfg_DR0 L (0 :: R).
Proof.
  unfold cfg_DR0; rewrite encLeft_zero, encRight_zero; simpl; start_progress.
Qed.

Lemma rule_DR0_succ (a : N) (L R : list N) :
  cfg_DR0 ((a + 1) :: L) R -->+ cfg_C (a :: L) (0 :: R).
Proof.
  unfold cfg_DR0, cfg_C; rewrite encLeft_add_one, encRight_zero; simpl; start_progress.
Qed.

Lemma rule_C_nil (R : list N) :
  cfg_C [] R -->+ cfg_DR0 [] R.
Proof.
  unfold cfg_C, cfg_DR0; simpl; start_progress.
Qed.

Lemma rule_C_zero_nil (R : list N) :
  cfg_C [0] R -->+ cfg_C [] (1 :: R).
Proof.
  unfold cfg_C; rewrite encLeft_zero, encRight_one; simpl; start_progress.
Qed.

Lemma rule_C_zero_zero (L R : list N) :
  cfg_C (0 :: 0 :: L) R -->+ cfg_C (bumpHead L) (1 :: R).
Proof.
  unfold cfg_C.
  rewrite (encLeft_zero (0 :: L)), (encLeft_zero L), encRight_one, <- encLeft_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_C_zero_one (L R : list N) :
  cfg_C (0 :: 1 :: L) R -->+ cfg_C (bumpHead (bumpHead L)) (0 :: bumpHead R).
Proof.
  unfold cfg_C.
  rewrite (encLeft_zero (1 :: L)), (encLeft_one L), (encRight_zero (bumpHead R)).
  rewrite <- !encLeft_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_C_zero_add_two (a : N) (L R : list N) :
  cfg_C (0 :: (a + 2) :: L) R -->+ cfg_BR (a :: L) (0 :: 1 :: R).
Proof.
  unfold cfg_C, cfg_BR.
  rewrite (encLeft_zero ((a + 2) :: L)), encLeft_add_two.
  rewrite (encRight_zero (1 :: R)), encRight_one.
  simpl; start_progress.
Qed.

Lemma rule_C_one_nil (R : list N) :
  cfg_C [1] R -->+ cfg_B [0] (1 :: R).
Proof.
  unfold cfg_C, cfg_B; rewrite (encLeft_one []), (encLeft_zero []), encRight_one.
  simpl; start_progress.
Qed.

Lemma rule_C_one_zero (L R : list N) :
  cfg_C (1 :: 0 :: L) R -->+ cfg_DR0 L (2 :: R).
Proof.
  unfold cfg_C, cfg_DR0; rewrite (encLeft_one (0 :: L)), (encLeft_zero L), encRight_two.
  simpl; start_progress.
Qed.

Lemma rule_C_one_succ (a : N) (L R : list N) :
  cfg_C (1 :: (a + 1) :: L) R -->+ cfg_C (a :: L) (2 :: R).
Proof.
  unfold cfg_C; rewrite (encLeft_one ((a + 1) :: L)), encLeft_add_one, encRight_two.
  simpl; start_progress.
Qed.

Lemma rule_C_add_two_step (a : N) (L R : list N) :
  cfg_C ((a + 2) :: L) R -->+ cfg_Halt (encTailL a L) (1%sym >> 1%sym >> 0%sym >> encRight1 R).
Proof.
  unfold cfg_C, cfg_Halt; rewrite encLeft_add_two, (encLeft_cons_tail a L).
  simpl; start_progress.
Qed.

Lemma rule_C_add_two_halt (a : N) (L R : list N) :
  halts tm (cfg_C ((a + 2) :: L) R).
Proof.
  eapply halts_evstep; [| apply pev, rule_C_add_two_step].
  apply halted_halts. reflexivity.
Qed.

(* ========================================================================== *)
(* Section 2: Semantic Multi-Step Contractions on `list N`                    *)
(* ========================================================================== *)

Definition blkL (r : N) : list N := rep0 (r + 2) ++ [1].
Definition blkR (r : N) : list N := rep0 r ++ [2; 1].

Lemma rule_BR_zeros_all (L R : list N) (k : N) :
  cfg_BR L (rep0 k ++ R) -->* cfg_BR (rep0 k ++ L) R.
Proof.
  revert L.
  induction k as [| k ih] using N_peano_ind; intro L.
  - apply evstep_refl.
  - rewrite rep0_succ; simpl.
    eapply etrans; [exact (pev (rule_BR_zero L (rep0 k ++ R))) |].
    rewrite <- rep0_append_zero_cons.
    exact (ih (0 :: L)).
Qed.

Lemma rule_B_zeros_all (L R : list N) (k : N) :
  cfg_B L (rep0 k ++ R) -->* cfg_B (rep0 k ++ L) R.
Proof.
  revert L.
  induction k as [| k ih] using N_peano_ind; intro L.
  - apply evstep_refl.
  - rewrite rep0_succ; simpl.
    eapply etrans; [exact (pev (rule_B_zero L (rep0 k ++ R))) |].
    rewrite <- rep0_append_zero_cons.
    exact (ih (0 :: L)).
Qed.

Lemma rule_DR0_zeros_all (L R : list N) (k : N) :
  cfg_DR0 (rep0 k ++ L) R -->* cfg_DR0 L (rep0 k ++ R).
Proof.
  revert R.
  induction k as [| k ih] using N_peano_ind; intro R.
  - apply evstep_refl.
  - rewrite rep0_succ; simpl.
    eapply etrans; [exact (pev (rule_DR0_zero (rep0 k ++ L) R)) |].
    rewrite <- rep0_append_zero_cons.
    exact (ih (0 :: R)).
Qed.

Lemma rule_B_succ_step (d : N) (L R : list N) :
  cfg_B L ((d + 1) :: R) -->+ cfg_BR (0 :: L) (d :: R).
Proof.
  exact (ptrans (rule_B_succ d L R) (rule_BR_zero L (d :: R))).
Qed.

Lemma rule_C_one_prefix (z0 : N) (L R : list N) :
  cfg_C (1 :: (rep0 z0 ++ 1 :: L)) R -->* cfg_C (0 :: L) (rep0 z0 ++ 2 :: R).
Proof.
  destruct (N.eq_dec z0 0) as [-> | hne].
  - simpl. exact (pev (rule_C_one_succ 0 L R)).
  - replace z0 with ((z0 - 1) + 1) by lia.
    rewrite rep0_succ; simpl.
    eapply etrans; [exact (pev (rule_C_one_zero (rep0 (z0 - 1) ++ 1 :: L) R)) |].
    eapply etrans; [exact (rule_DR0_zeros_all (1 :: L) (2 :: R) (z0 - 1)) |].
    exact (pev (rule_DR0_succ 0 L (rep0 (z0 - 1) ++ 2 :: R))).
Qed.

Lemma rule_C_r_add_three (r : N) (L R : list N) :
  cfg_C (rep0 (r + 3) ++ 1 :: L) R -->* cfg_C (0 :: L) (blkR r ++ R).
Proof.
  replace (r + 3) with (3 + r) by lia.
  rewrite rep0_add; simpl.
  eapply etrans; [exact (pev (rule_C_zero_zero (0 :: (rep0 r ++ 1 :: L)) R)) |].
  cbn [bumpHead].
  unfold blkR; rewrite <- app_assoc; simpl.
  exact (rule_C_one_prefix r L (1 :: R)).
Qed.

Lemma rule_C_blkL_pow (c r : N) (L R : list N) :
  cfg_C (0 :: (repBlock (blkL r) c ++ L)) R -->*
  cfg_C (0 :: L) (repBlock (blkR r) c ++ R).
Proof.
  revert L R.
  induction c as [| c ih] using N_peano_ind; intros L R.
  - apply evstep_refl.
  - rewrite repBlock_succ_l, <- app_assoc.
    assert (heq : 0 :: (blkL r ++ (repBlock (blkL r) c ++ L)) =
                  rep0 (r + 3) ++ 1 :: (repBlock (blkL r) c ++ L)).
    { unfold blkL at 1.
      replace (r + 3) with ((r + 2) + 1) by lia.
      rewrite rep0_succ, <- app_assoc; reflexivity. }
    rewrite heq.
    eapply etrans; [exact (rule_C_r_add_three r (repBlock (blkL r) c ++ L) R) |].
    pose proof (ih L (blkR r ++ R)) as h2.
    rewrite app_assoc, <- repBlock_succ_r in h2.
    exact h2.
Qed.

Lemma rule_C_bot_four (r : N) (R : list N) :
  cfg_C (rep0 (r + 4)) R -->* cfg_DR0 [] (blkR r ++ R).
Proof.
  replace (r + 4) with (4 + r) by lia.
  rewrite rep0_add; simpl.
  eapply etrans; [exact (pev (rule_C_zero_zero (0 :: 0 :: rep0 r) R)) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_C_one_zero (rep0 r) (1 :: R))) |].
  pose proof (rule_DR0_zeros_all [] (2 :: 1 :: R) r) as h3.
  rewrite app_nil_r in h3.
  unfold blkR; rewrite <- app_assoc; simpl.
  exact h3.
Qed.

Lemma rule_DR0_bot (k : N) (R : list N) :
  cfg_DR0 (rep0 k) R -->* cfg_BR (rep0 (k + 3)) R.
Proof.
  rewrite <- (app_nil_r (rep0 k)).
  eapply etrans; [exact (rule_DR0_zeros_all [] R k) |].
  eapply etrans; [exact (pev (rule_DR0_nil (rep0 k ++ R))) |].
  eapply etrans; [exact (pev (rule_C_one_nil (rep0 k ++ R))) |].
  eapply etrans; [exact (pev (rule_B_succ_step 0 [0] (rep0 k ++ R))) |].
  assert (heqR : 0 :: (rep0 k ++ R) = rep0 (k + 1) ++ R).
  { rewrite rep0_succ; reflexivity. }
  rewrite heqR.
  pose proof (rule_BR_zeros_all [0; 0] R (k + 1)) as h5.
  assert (heqL : rep0 (k + 1) ++ [0; 0] = rep0 (k + 3)).
  { replace (k + 3) with ((k + 1) + 2) by lia.
    rewrite (rep0_add (k + 1) 2); reflexivity. }
  rewrite heqL in h5.
  exact h5.
Qed.

Lemma rule_DR0_bot_zeros (q : N) : forall (k : N) (R : list N),
  cfg_DR0 (rep0 k) (1 :: (rep0 q ++ R)) -->*
  cfg_DR0 (rep0 (k + 3 * q)) (1 :: R).
Proof.
  induction q as [| q ih] using N_peano_ind; intros k R.
  - rewrite N.mul_0_r, N.add_0_r; simpl; apply evstep_refl.
  - rewrite rep0_succ; simpl.
    eapply etrans; [exact (rule_DR0_bot k (1 :: 0 :: (rep0 q ++ R))) |].
    eapply etrans; [exact (pev (rule_BR_one (rep0 (k + 3)) (0 :: (rep0 q ++ R)))) |].
    cbn [bumpHead].
    pose proof (ih (k + 3) R) as h3.
    replace (k + 3 + 3 * q) with (k + 3 * (q + 1)) in h3 by lia.
    exact h3.
Qed.

Lemma rule_BR_blkR_one (r : N) (L R : list N) :
  cfg_BR (0 :: L) (blkR r ++ R) -->* cfg_BR (rep0 3 ++ 1 :: (rep0 r ++ L)) R.
Proof.
  unfold blkR; rewrite <- app_assoc; simpl.
  eapply etrans; [exact (rule_BR_zeros_all (0 :: L) (2 :: 1 :: R) r) |].
  rewrite rep0_append_zero_cons.
  eapply etrans; [exact (pev (rule_BR_add_two 0 (0 :: (rep0 r ++ L)) (1 :: R))) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_B_zero (1 :: (rep0 r ++ L)) (1 :: R))) |].
  eapply etrans; [exact (pev (rule_B_succ_step 0 (0 :: 1 :: (rep0 r ++ L)) R)) |].
  exact (pev (rule_BR_zero (0 :: 0 :: 1 :: (rep0 r ++ L)) R)).
Qed.

Lemma rule_BR_blkR_succ (k : N) : forall (r : N) (L R : list N),
  cfg_BR (0 :: L) (repBlock (blkR r) (k + 1) ++ R) -->*
  cfg_BR (rep0 3 ++ 1 :: (repBlock (blkL r) k ++ (rep0 r ++ L))) R.
Proof.
  induction k as [| k ih] using N_peano_ind; intros r L R.
  - rewrite repBlock_1, repBlock_0; simpl.
    exact (rule_BR_blkR_one r L R).
  - replace (k + 1 + 1) with (1 + (k + 1)) by lia.
    rewrite repBlock_add, repBlock_1, <- app_assoc.
    eapply etrans; [exact (rule_BR_blkR_one r L (repBlock (blkR r) (k + 1) ++ R)) |].
    change (rep0 3 ++ 1 :: (rep0 r ++ L)) with (0 :: (0 :: 0 :: 1 :: (rep0 r ++ L))).
    pose proof (ih r (0 :: 0 :: 1 :: (rep0 r ++ L)) R) as h2.
    assert (heqL : repBlock (blkL r) k ++ (rep0 r ++ (0 :: 0 :: 1 :: (rep0 r ++ L))) =
                   repBlock (blkL r) (k + 1) ++ (rep0 r ++ L)).
    { assert (hb : rep0 r ++ (0 :: 0 :: 1 :: (rep0 r ++ L)) = blkL r ++ (rep0 r ++ L)).
      { unfold blkL; rewrite (rep0_add r 2), <- !app_assoc; reflexivity. }
      rewrite hb, app_assoc, <- repBlock_succ_r; reflexivity. }
    rewrite heqL in h2.
    exact h2.
Qed.

Lemma rule_BR_blkR_clean (c r : N) (L R : list N) :
  cfg_BR (rep0 3 ++ 1 :: L) (repBlock (blkR r) c ++ R) -->*
  cfg_BR (rep0 3 ++ 1 :: (repBlock (blkL r) c ++ L)) R.
Proof.
  destruct (N.eq_dec c 0) as [-> | hne].
  - simpl; apply evstep_refl.
  - replace c with ((c - 1) + 1) by lia.
    change (rep0 3 ++ 1 :: L) with (0 :: (0 :: 0 :: 1 :: L)) at 1.
    pose proof (rule_BR_blkR_succ (c - 1) r (0 :: 0 :: 1 :: L) R) as h.
    assert (heq : repBlock (blkL r) (c - 1) ++ (rep0 r ++ (0 :: 0 :: 1 :: L)) =
                  repBlock (blkL r) ((c - 1) + 1) ++ L).
    { assert (hb : rep0 r ++ (0 :: 0 :: 1 :: L) = blkL r ++ L).
      { unfold blkL; rewrite (rep0_add r 2), <- !app_assoc; reflexivity. }
      rewrite hb, app_assoc, <- repBlock_succ_r; reflexivity. }
    rewrite heq in h.
    exact h.
Qed.

(* ========================================================================== *)
(* Section 3: Clean-Mode Invariant Structure & O(1) Contraction Theorems      *)
(* ========================================================================== *)

Fixpoint decSegs (segs : list (N * N)) : list N :=
  match segs with
  | [] => []
  | (r, c) :: ss => repBlock (blkL r) c ++ decSegs ss
  end.

Inductive Item : Type :=
  | IT_z (c : N)
  | IT_d (v : N)
  | IT_k (r c : N).

Inductive LState : Type :=
  | LS_raw (items : list Item)
  | LS_clean (z0 : N) (segs : list (N * N)) (bot : N).

Fixpoint decL (items : list Item) : list N :=
  match items with
  | [] => []
  | IT_z c :: xs => rep0 c ++ decL xs
  | IT_d v :: xs => v :: decL xs
  | IT_k r c :: xs => repBlock (blkL r) c ++ decL xs
  end.

Fixpoint decR (items : list Item) : list N :=
  match items with
  | [] => []
  | IT_z c :: xs => rep0 c ++ decR xs
  | IT_d v :: xs => v :: decR xs
  | IT_k r c :: xs => repBlock (blkR r) c ++ decR xs
  end.

Definition decLState (ls : LState) : list N :=
  match ls with
  | LS_raw items => decL items
  | LS_clean z0 segs bot => rep0 z0 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))
  end.

Definition pushSeg (r c : N) (segs : list (N * N)) : list (N * N) :=
  if c =? 0 then segs
  else match segs with
    | (r2, c2) :: ss => if r =? r2 then (r, c + c2) :: ss else (r, c) :: segs
    | [] => [(r, c)]
    end.

Lemma decSegs_pushSeg (r c : N) (segs : list (N * N)) :
  decSegs (pushSeg r c segs) = repBlock (blkL r) c ++ decSegs segs.
Proof.
  unfold pushSeg.
  destruct (c =? 0) eqn:hc.
  - apply N.eqb_eq in hc; subst c; reflexivity.
  - destruct segs as [| [r2 c2] ss]; [reflexivity |].
    destruct (r =? r2) eqn:hr.
    + apply N.eqb_eq in hr; subst r2.
      simpl; rewrite repBlock_add, app_assoc; reflexivity.
    + reflexivity.
Qed.

Lemma clean_sweep_core (segs : list (N * N)) : forall (bot : N) (R : list N),
  cfg_C (0 :: (decSegs segs ++ rep0 (bot + 3))) R -->*
  cfg_BR (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) R.
Proof.
  induction segs as [| [r c] ss ih]; intros bot R; simpl.
  - assert (heq : 0 :: rep0 (bot + 3) = rep0 (bot + 4)).
    { replace (bot + 4) with ((bot + 3) + 1) by lia.
      rewrite rep0_succ; reflexivity. }
    rewrite heq.
    eapply etrans; [exact (rule_C_bot_four bot R) |].
    eapply etrans; [exact (rule_DR0_bot 0 (blkR bot ++ R)) |].
    change (rep0 (0 + 3)) with (0 :: [0; 0]).
    pose proof (rule_BR_blkR_one bot [0; 0] R) as h3.
    assert (heq2 : rep0 bot ++ [0; 0] = rep0 (bot + 2)).
    { rewrite (rep0_add bot 2); reflexivity. }
    rewrite heq2 in h3.
    exact h3.
  - rewrite <- !app_assoc.
    eapply etrans; [exact (rule_C_blkL_pow c r (decSegs ss ++ rep0 (bot + 3)) R) |].
    eapply etrans; [exact (ih bot (repBlock (blkR r) c ++ R)) |].
    exact (rule_BR_blkR_clean c r (decSegs ss ++ rep0 (bot + 2)) R).
Qed.

Lemma clean_DR0_one (z0 : N) (segs : list (N * N)) (bot : N) (R : list N) :
  cfg_DR0 (decLState (LS_clean z0 segs (bot + 1))) R -->*
  cfg_BR (decLState (LS_clean (z0 + 4) segs bot)) R.
Proof.
  cbn [decLState].
  replace (bot + 1 + 2) with (bot + 3) by lia.
  eapply etrans; [exact (rule_DR0_zeros_all (1 :: (decSegs segs ++ rep0 (bot + 3))) R z0) |].
  eapply etrans; [exact (pev (rule_DR0_succ 0 (decSegs segs ++ rep0 (bot + 3)) (rep0 z0 ++ R))) |].
  eapply etrans; [exact (clean_sweep_core segs bot (0 :: (rep0 z0 ++ R))) |].
  change (0 :: (rep0 z0 ++ R)) with (rep0 1 ++ (rep0 z0 ++ R)).
  rewrite app_assoc, <- (rep0_add 1 z0).
  replace (1 + z0) with (z0 + 1) by lia.
  pose proof (rule_BR_zeros_all (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) R (z0 + 1)) as h4.
  rewrite app_assoc, <- (rep0_add (z0 + 1) 3) in h4.
  replace (z0 + 1 + 3) with (z0 + 4) in h4 by lia.
  exact h4.
Qed.

Lemma clean_DR0_zeros (q : N) : forall (z0 : N) (segs : list (N * N)) (bot : N) (R : list N),
  cfg_DR0 (decLState (LS_clean z0 segs (bot + q))) (1 :: (rep0 q ++ R)) -->*
  cfg_DR0 (decLState (LS_clean (z0 + 4 * q) segs bot)) (1 :: R).
Proof.
  induction q as [| q ih] using N_peano_ind; intros z0 segs bot R.
  - rewrite N.mul_0_r, !N.add_0_r; simpl; apply evstep_refl.
  - replace (bot + (q + 1)) with ((bot + q) + 1) by lia.
    rewrite rep0_succ; simpl.
    eapply etrans; [exact (clean_DR0_one z0 segs (bot + q) (1 :: 0 :: (rep0 q ++ R))) |].
    eapply etrans; [exact (pev (rule_BR_one (decLState (LS_clean (z0 + 4) segs (bot + q))) (0 :: (rep0 q ++ R)))) |].
    cbn [bumpHead].
    pose proof (ih (z0 + 4) segs bot R) as h3.
    replace (z0 + 4 + 4 * q) with (z0 + 4 * (q + 1)) in h3 by lia.
    exact h3.
Qed.

Lemma clean_RNIL_one (m : StackMode) (hm : m = SM_B \/ m = SM_BR)
  (z0 : N) (segs : list (N * N)) (bot : N) :
  evalStackCfg1 m (decLState (LS_clean (z0 + 1) segs (bot + 1))) [] -->*
  cfg_B (decLState (LS_clean 1 (pushSeg z0 1 segs) bot)) [].
Proof.
  assert (h0 : evalStackCfg1 m (decLState (LS_clean (z0 + 1) segs (bot + 1))) [] -->*
               cfg_C (1 :: (rep0 z0 ++ 1 :: (decSegs segs ++ rep0 (bot + 3)))) []).
  { assert (heqL : bumpHead (decLState (LS_clean (z0 + 1) segs (bot + 1))) =
                   1 :: (rep0 z0 ++ 1 :: (decSegs segs ++ rep0 (bot + 3)))).
    { cbn [decLState].
      rewrite rep0_succ; simpl.
      replace (bot + 1 + 2) with (bot + 3) by lia.
      reflexivity. }
    destruct hm as [-> | ->]; simpl; rewrite <- heqL.
    - exact (pev (rule_B_nil _)).
    - exact (pev (rule_BR_nil _)). }
  eapply etrans; [exact h0 |].
  eapply etrans; [exact (rule_C_one_prefix z0 (decSegs segs ++ rep0 (bot + 3)) []) |].
  eapply etrans; [exact (clean_sweep_core segs bot (rep0 z0 ++ [2])) |].
  eapply etrans; [exact (rule_BR_zeros_all (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) [2] z0) |].
  assert (heq3 : rep0 z0 ++ (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
                 0 :: (rep0 (z0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)))).
  { rewrite app_assoc, <- (rep0_add z0 3).
    replace (z0 + 3) with ((z0 + 2) + 1) by lia.
    rewrite (rep0_succ (z0 + 2)); reflexivity. }
  rewrite heq3.
  eapply etrans; [exact (pev (rule_BR_add_two 0 (0 :: (rep0 (z0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)))) [])) |].
  cbn [bumpHead].
  pose proof (pev (rule_B_zero (1 :: (rep0 (z0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)))) [])) as h5.
  assert (heq5 : 0 :: 1 :: (rep0 (z0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
                 decLState (LS_clean 1 (pushSeg z0 1 segs) bot)).
  { cbn [decLState]; rewrite decSegs_pushSeg, repBlock_1; unfold blkL.
    rewrite <- !app_assoc; reflexivity. }
  rewrite heq5 in h5.
  exact h5.
Qed.

Lemma decSegs_pushSeg_succ (r q : N) (segs : list (N * N)) :
  decSegs (pushSeg r q (pushSeg r 1 segs)) = decSegs (pushSeg r (q + 1) segs).
Proof.
  rewrite !decSegs_pushSeg, app_assoc, <- repBlock_add; reflexivity.
Qed.

Lemma clean_RNIL_zero_pow (q : N) : forall (segs : list (N * N)) (bot : N),
  cfg_B (decLState (LS_clean 1 segs (bot + q))) [] -->*
  cfg_B (decLState (LS_clean 1 (pushSeg 0 q segs) bot)) [].
Proof.
  induction q as [| q ih] using N_peano_ind; intros segs bot.
  - rewrite N.add_0_r; simpl; apply evstep_refl.
  - replace (bot + (q + 1)) with ((bot + q) + 1) by lia.
    eapply etrans; [exact (clean_RNIL_one SM_B (or_introl eq_refl) 0 segs (bot + q)) |].
    pose proof (ih (pushSeg 0 1 segs) bot) as h2.
    cbn [decLState] in h2 |- *; rewrite decSegs_pushSeg_succ in h2.
    exact h2.
Qed.

Lemma clean_P1_one (r : N) (segs : list (N * N)) (bot : N) (R : list N) :
  cfg_B (decLState (LS_clean 0 segs (bot + 1))) (0 :: (blkR r ++ R)) -->*
  cfg_B (decLState (LS_clean 0 (pushSeg (r + 3) 1 segs) bot)) (0 :: R).
Proof.
  assert (heqR : 0 :: (blkR r ++ R) = rep0 (r + 1) ++ (2 :: 1 :: R)).
  { unfold blkR; rewrite rep0_succ, <- app_assoc; reflexivity. }
  rewrite heqR.
  eapply etrans; [exact (rule_B_zeros_all (decLState (LS_clean 0 segs (bot + 1))) (2 :: 1 :: R) (r + 1)) |].
  eapply etrans; [exact (pev (rule_B_succ_step 1 (rep0 (r + 1) ++ decLState (LS_clean 0 segs (bot + 1))) (1 :: R))) |].
  assert (heq2 : 0 :: (rep0 (r + 1) ++ decLState (LS_clean 0 segs (bot + 1))) =
                 decLState (LS_clean (r + 2) segs (bot + 1))).
  { cbn [decLState].
    replace (r + 2) with ((r + 1) + 1) by lia.
    rewrite (rep0_succ (r + 1)); reflexivity. }
  rewrite heq2.
  eapply etrans; [exact (pev (rule_BR_one (decLState (LS_clean (r + 2) segs (bot + 1))) (1 :: R))) |].
  cbn [bumpHead].
  eapply etrans; [exact (clean_DR0_one (r + 2) segs bot (2 :: R)) |].
  replace (r + 2 + 4) with (r + 6) by lia.
  pose proof (pev (rule_BR_add_two 0 (decLState (LS_clean (r + 6) segs bot)) R)) as h5.
  assert (heq5 : bumpHead (decLState (LS_clean (r + 6) segs bot)) =
                 decLState (LS_clean 0 (pushSeg (r + 3) 1 segs) bot)).
  { cbn [decLState]; rewrite decSegs_pushSeg, repBlock_1; unfold blkL.
    replace (r + 6) with ((r + 3 + 2) + 1) by lia.
    rewrite (rep0_succ (r + 3 + 2)), <- !app_assoc; reflexivity. }
  rewrite heq5 in h5.
  exact h5.
Qed.

Lemma clean_P1_pow (q : N) : forall (r : N) (segs : list (N * N)) (bot : N) (R : list N),
  cfg_B (decLState (LS_clean 0 segs (bot + q))) (0 :: (repBlock (blkR r) q ++ R)) -->*
  cfg_B (decLState (LS_clean 0 (pushSeg (r + 3) q segs) bot)) (0 :: R).
Proof.
  induction q as [| q ih] using N_peano_ind; intros r segs bot R.
  - rewrite N.add_0_r; simpl; apply evstep_refl.
  - replace (bot + (q + 1)) with ((bot + q) + 1) by lia.
    rewrite repBlock_succ_l, <- app_assoc.
    eapply etrans; [exact (clean_P1_one r segs (bot + q) (repBlock (blkR r) q ++ R)) |].
    pose proof (ih r (pushSeg (r + 3) 1 segs) bot R) as h2.
    cbn [decLState] in h2 |- *; rewrite decSegs_pushSeg_succ in h2.
    exact h2.
Qed.

Lemma clean_P2_one (r : N) (segs : list (N * N)) (bot : N) (R : list N) :
  cfg_B (decLState (LS_clean 0 segs (bot + (r + 1)))) (1 :: 1 :: (blkR r ++ R)) -->*
  cfg_B (decLState (LS_clean 0 (pushSeg (4 * r + 3) 1 segs) bot)) (1 :: 1 :: R).
Proof.
  destruct (N.eq_dec r 0) as [-> | hne].
  - simpl.
    eapply etrans; [exact (pev (rule_B_succ_step 0 (decLState (LS_clean 0 segs (bot + 1))) (1 :: 2 :: 1 :: R))) |].
    eapply etrans; [exact (pev (rule_BR_zero (0 :: decLState (LS_clean 0 segs (bot + 1))) (1 :: 2 :: 1 :: R))) |].
    change (0 :: 0 :: decLState (LS_clean 0 segs (bot + 1)))
      with (decLState (LS_clean 2 segs (bot + 1))).
    eapply etrans; [exact (pev (rule_BR_one (decLState (LS_clean 2 segs (bot + 1))) (2 :: 1 :: R))) |].
    cbn [bumpHead].
    eapply etrans; [exact (clean_DR0_one 2 segs bot (3 :: 1 :: R)) |].
    change (2 + 4) with 6.
    pose proof (pev (rule_BR_add_two 1 (decLState (LS_clean 6 segs bot)) (1 :: R))) as h5.
    assert (heq5 : bumpHead (decLState (LS_clean 6 segs bot)) =
                   decLState (LS_clean 0 (pushSeg 3 1 segs) bot)).
    { cbn [decLState]; rewrite decSegs_pushSeg, repBlock_1; unfold blkL; reflexivity. }
    rewrite heq5 in h5.
    exact h5.
  - set (r' := r - 1).
    replace r with (r' + 1) by lia.
    replace (bot + (r' + 1 + 1)) with ((bot + 2) + r') by lia.
    eapply etrans; [exact (pev (rule_B_succ_step 0 (decLState (LS_clean 0 segs ((bot + 2) + r'))) (1 :: (blkR (r' + 1) ++ R)))) |].
    eapply etrans; [exact (pev (rule_BR_zero (0 :: decLState (LS_clean 0 segs ((bot + 2) + r'))) (1 :: (blkR (r' + 1) ++ R)))) |].
    change (0 :: 0 :: decLState (LS_clean 0 segs ((bot + 2) + r')))
      with (decLState (LS_clean 2 segs ((bot + 2) + r'))).
    eapply etrans; [exact (pev (rule_BR_one (decLState (LS_clean 2 segs ((bot + 2) + r'))) (blkR (r' + 1) ++ R))) |].
    assert (hb : bumpHead (blkR (r' + 1) ++ R) = 1 :: (rep0 r' ++ (2 :: 1 :: R))).
    { unfold blkR; rewrite rep0_succ, <- app_assoc; reflexivity. }
    rewrite hb.
    eapply etrans; [exact (clean_DR0_zeros r' 2 segs (bot + 2) (2 :: 1 :: R)) |].
    replace (bot + 2) with ((bot + 1) + 1) by lia.
    eapply etrans; [exact (clean_DR0_one (2 + 4 * r') segs (bot + 1) (1 :: 2 :: 1 :: R)) |].
    eapply etrans; [exact (pev (rule_BR_one (decLState (LS_clean (2 + 4 * r' + 4) segs (bot + 1))) (2 :: 1 :: R))) |].
    cbn [bumpHead].
    eapply etrans; [exact (clean_DR0_one (2 + 4 * r' + 4) segs bot (3 :: 1 :: R)) |].
    pose proof (pev (rule_BR_add_two 1 (decLState (LS_clean ((2 + 4 * r' + 4) + 4) segs bot)) (1 :: R))) as h8.
    assert (heq8 : bumpHead (decLState (LS_clean ((2 + 4 * r' + 4) + 4) segs bot)) =
                   decLState (LS_clean 0 (pushSeg (4 * (r' + 1) + 3) 1 segs) bot)).
    { cbn [decLState]; rewrite decSegs_pushSeg, repBlock_1; unfold blkL.
      replace ((2 + 4 * r' + 4) + 4) with ((4 * (r' + 1) + 3 + 2) + 1) by lia.
      rewrite (rep0_succ (4 * (r' + 1) + 3 + 2)), <- !app_assoc; reflexivity. }
    rewrite heq8 in h8.
    exact h8.
Qed.

Lemma clean_P2_pow (q : N) : forall (r : N) (segs : list (N * N)) (bot : N) (R : list N),
  cfg_B (decLState (LS_clean 0 segs (bot + q * (r + 1)))) (1 :: 1 :: (repBlock (blkR r) q ++ R)) -->*
  cfg_B (decLState (LS_clean 0 (pushSeg (4 * r + 3) q segs) bot)) (1 :: 1 :: R).
Proof.
  induction q as [| q ih] using N_peano_ind; intros r segs bot R.
  - rewrite N.mul_0_l, N.add_0_r; simpl; apply evstep_refl.
  - replace (bot + (q + 1) * (r + 1)) with ((bot + q * (r + 1)) + (r + 1)) by lia.
    rewrite repBlock_succ_l, <- app_assoc.
    eapply etrans; [exact (clean_P2_one r segs (bot + q * (r + 1)) (repBlock (blkR r) q ++ R)) |].
    pose proof (ih r (pushSeg (4 * r + 3) 1 segs) bot R) as h2.
    cbn [decLState] in h2 |- *; rewrite decSegs_pushSeg_succ in h2.
    exact h2.
Qed.

(* ========================================================================== *)
(* Section 4: Executable RLE Stack Engine & Denotational Soundness            *)
(* ========================================================================== *)

Definition pushL0 (c : N) (L : list Item) : list Item :=
  if c =? 0 then L
  else match L with
    | IT_z c2 :: xs => IT_z (c + c2) :: xs
    | _ => IT_z c :: L
    end.

Definition pushLk2 (r c : N) (L : list Item) : list Item :=
  if c =? 0 then L
  else match L with
    | IT_k r2 c2 :: xs => if r =? r2 then IT_k r (c + c2) :: xs else IT_k r c :: L
    | _ => IT_k r c :: L
    end.

Definition pushLd (v : N) (L : list Item) : list Item :=
  if v =? 0 then pushL0 1 L
  else if v =? 1 then
    match L with
    | IT_z c :: IT_d v2 :: xs =>
      if (v2 =? 1) && (2 <=? c) then IT_d 1 :: pushLk2 (c - 2) 1 xs
      else IT_d 1 :: L
    | _ => IT_d 1 :: L
    end
  else IT_d v :: L.

Definition popKTail (r c : N) (xs : list Item) : list Item :=
  if c =? 1 then xs else IT_k r (c - 1) :: xs.

Fixpoint popL1 (L : list Item) : option (N * list Item) :=
  match L with
  | [] => None
  | IT_z c :: xs =>
    if c =? 0 then popL1 xs
    else if c =? 1 then Some (0, xs)
    else Some (0, IT_z (c - 1) :: xs)
  | IT_k r c :: xs =>
    if c =? 0 then popL1 xs
    else Some (0, pushL0 (r + 1) (pushLd 1 (popKTail r c xs)))
  | IT_d v :: xs => Some (v, xs)
  end.

Definition bumpL (L : list Item) : list Item :=
  match popL1 L with
  | None => [IT_z 1]
  | Some (a, L1) => pushLd (a + 1) L1
  end.

Definition pushR0 (c : N) (R : list Item) : list Item :=
  if c =? 0 then R
  else match R with
    | IT_z c2 :: xs => IT_z (c + c2) :: xs
    | _ => IT_z c :: R
    end.

Definition mergeRk2Pre (r c : N) (R : list Item) : N * list Item :=
  if 1 <=? r then
    match R with
    | IT_z rz :: IT_d v2 :: IT_d v1 :: xs =>
      if (rz =? r) && (v2 =? 2) && (v1 =? 1) then (c + 1, xs) else (c, R)
    | _ => (c, R)
    end
  else (c, R).

Definition pushRk2 (r c : N) (R : list Item) : list Item :=
  if c =? 0 then R
  else
    let p := mergeRk2Pre r c R in
    match snd p with
    | IT_k r2 c2 :: xs => if r =? r2 then IT_k r (fst p + c2) :: xs else IT_k r (fst p) :: snd p
    | _ => IT_k r (fst p) :: snd p
    end.

Definition pushRd (v : N) (R : list Item) : list Item :=
  if v =? 0 then pushR0 1 R
  else if v =? 2 then
    match R with
    | IT_d v1 :: xs => if v1 =? 1 then pushRk2 0 1 xs else IT_d 2 :: R
    | _ => IT_d 2 :: R
    end
  else IT_d v :: R.

Fixpoint popR1 (R : list Item) : option (N * list Item) :=
  match R with
  | [] => None
  | IT_z c :: xs =>
    if c =? 0 then popR1 xs
    else if c =? 1 then Some (0, xs)
    else Some (0, IT_z (c - 1) :: xs)
  | IT_k r c :: xs =>
    if c =? 0 then popR1 xs
    else if r =? 0 then Some (2, IT_d 1 :: popKTail r c xs)
    else Some (0, pushR0 (r - 1) (IT_d 2 :: IT_d 1 :: popKTail r c xs))
  | IT_d v :: xs => Some (v, xs)
  end.

Definition bumpR (R : list Item) : list Item :=
  match popR1 R with
  | None => [IT_z 1]
  | Some (d, R1) => pushRd (d + 1) R1
  end.

Fixpoint segsToItems (segs : list (N * N)) (acc : list Item) : list Item :=
  match segs with
  | [] => acc
  | (r, c) :: ss =>
    if c =? 0 then segsToItems ss acc
    else IT_k r c :: segsToItems ss acc
  end.

Definition unpackClean (z0 : N) (segs : list (N * N)) (bot : N) : list Item :=
  let tail := segsToItems segs [IT_z (bot + 2)] in
  if z0 =? 0 then IT_d 1 :: tail else IT_z z0 :: IT_d 1 :: tail.

Fixpoint packTail (cur0 : N) (items : list Item) : option (list (N * N) * N) :=
  match items with
  | [] => if 2 <=? cur0 then Some ([], cur0 - 2) else None
  | IT_z c :: rest => packTail (cur0 + c) rest
  | IT_d v :: rest =>
    if (v =? 1) && (2 <=? cur0) then
      match packTail 0 rest with
      | Some (segs, bot) => Some (pushSeg (cur0 - 2) 1 segs, bot)
      | None => None
      end
    else None
  | IT_k r c :: rest =>
    if c =? 0 then packTail cur0 rest
    else
      match packTail 0 rest with
      | Some (segs, bot) =>
        Some (pushSeg (cur0 + r) 1 (pushSeg r (c - 1) segs), bot)
      | None => None
      end
  end.

Fixpoint packHead (cur0 : N) (items : list Item) : option LState :=
  match items with
  | [] => None
  | IT_z c :: rest => packHead (cur0 + c) rest
  | IT_d v :: rest =>
    if v =? 1 then
      match packTail 0 rest with
      | Some (segs, bot) => Some (LS_clean cur0 segs bot)
      | None => None
      end
    else None
  | IT_k r c :: rest =>
    if c =? 0 then packHead cur0 rest
    else
      match packTail 0 rest with
      | Some (segs, bot) =>
        Some (LS_clean (cur0 + r + 2) (pushSeg r (c - 1) segs) bot)
      | None => None
      end
  end.

Lemma decL_pushL0 (c : N) (L : list Item) :
  decL (pushL0 c L) = rep0 c ++ decL L.
Proof.
  unfold pushL0.
  destruct (c =? 0) eqn:hc.
  - apply N.eqb_eq in hc; subst c; reflexivity.
  - destruct L as [| [c2 | v | r k] xs]; try reflexivity.
    simpl; rewrite (rep0_add c c2), <- app_assoc; reflexivity.
Qed.

Lemma decL_pushLk2 (r c : N) (L : list Item) :
  decL (pushLk2 r c L) = repBlock (blkL r) c ++ decL L.
Proof.
  unfold pushLk2.
  destruct (c =? 0) eqn:hc.
  - apply N.eqb_eq in hc; subst c; reflexivity.
  - destruct L as [| [c2 | v | r2 c2] xs]; try reflexivity.
    destruct (r =? r2) eqn:hr; [| reflexivity].
    apply N.eqb_eq in hr; subst r2.
    simpl; rewrite repBlock_add, <- app_assoc; reflexivity.
Qed.

Lemma decL_pushLd (v : N) (L : list Item) :
  decL (pushLd v L) = v :: decL L.
Proof.
  unfold pushLd.
  destruct (v =? 0) eqn:hv0.
  - apply N.eqb_eq in hv0; subst v; exact (decL_pushL0 1 L).
  - destruct (v =? 1) eqn:hv1; [| reflexivity].
    apply N.eqb_eq in hv1; subst v.
    destruct L as [| [c | ? | ? ?] [| [? | v2 | ? ?] xs]]; try reflexivity.
    destruct ((v2 =? 1) && (2 <=? c)) eqn:hb; [| reflexivity].
    apply andb_true_iff in hb; destruct hb as [hv2 hc2].
    apply N.eqb_eq in hv2; apply N.leb_le in hc2; subst v2.
    cbn [decL]; rewrite decL_pushLk2, repBlock_1; unfold blkL.
    replace (c - 2 + 2) with c by lia.
    rewrite <- !app_assoc; reflexivity.
Qed.

Lemma decL_popKTail (r c : N) (xs : list Item) :
  decL (popKTail r c xs) = repBlock (blkL r) (c - 1) ++ decL xs.
Proof.
  unfold popKTail.
  destruct (c =? 1) eqn:hc; [apply N.eqb_eq in hc; subst c; reflexivity | reflexivity].
Qed.

Lemma decR_popKTail (r c : N) (xs : list Item) :
  decR (popKTail r c xs) = repBlock (blkR r) (c - 1) ++ decR xs.
Proof.
  unfold popKTail.
  destruct (c =? 1) eqn:hc; [apply N.eqb_eq in hc; subst c; reflexivity | reflexivity].
Qed.

Lemma decL_popL1_none (L : list Item) :
  popL1 L = None -> decL L = [].
Proof.
  induction L as [| [c | v | r c] xs ih]; intros h; simpl in h |- *.
  - reflexivity.
  - destruct (c =? 0) eqn:hc0.
    + apply N.eqb_eq in hc0; subst c; exact (ih h).
    + destruct (c =? 1); discriminate.
  - discriminate.
  - destruct (c =? 0) eqn:hc0.
    + apply N.eqb_eq in hc0; subst c; exact (ih h).
    + discriminate.
Qed.

Lemma decL_popL1_some (L : list Item) : forall (a : N) (L' : list Item),
  popL1 L = Some (a, L') -> decL L = a :: decL L'.
Proof.
  induction L as [| [c | v | r c] xs ih]; intros a L' h; simpl in h.
  - discriminate.
  - destruct (c =? 0) eqn:hc0.
    + apply N.eqb_eq in hc0; subst c; simpl; exact (ih a L' h).
    + apply N.eqb_neq in hc0.
      destruct (c =? 1) eqn:hc1.
      * apply N.eqb_eq in hc1; subst c; injection h as <- <-; reflexivity.
      * apply N.eqb_neq in hc1; injection h as <- <-; cbn [decL].
        replace c with ((c - 1) + 1) at 1 by lia.
        rewrite (rep0_succ (c - 1)); reflexivity.
  - injection h as <- <-; reflexivity.
  - destruct (c =? 0) eqn:hc0.
    + apply N.eqb_eq in hc0; subst c; simpl; exact (ih a L' h).
    + apply N.eqb_neq in hc0; injection h as <- <-.
      rewrite decL_pushL0, decL_pushLd, decL_popKTail; cbn [decL].
      replace c with (1 + (c - 1)) at 1 by lia.
      rewrite repBlock_add, repBlock_1; unfold blkL at 1.
      replace (r + 2) with ((r + 1) + 1) by lia.
      rewrite (rep0_succ (r + 1)), <- !app_assoc; reflexivity.
Qed.

Lemma decL_bumpL (L : list Item) : decL (bumpL L) = bumpHead (decL L).
Proof.
  unfold bumpL.
  destruct (popL1 L) as [[a L1] |] eqn:hp.
  - rewrite (decL_popL1_some L a L1 hp), decL_pushLd; reflexivity.
  - rewrite (decL_popL1_none L hp); reflexivity.
Qed.

Lemma decR_pushR0 (c : N) (R : list Item) :
  decR (pushR0 c R) = rep0 c ++ decR R.
Proof.
  unfold pushR0.
  destruct (c =? 0) eqn:hc.
  - apply N.eqb_eq in hc; subst c; reflexivity.
  - destruct R as [| [c2 | v | r k] xs]; try reflexivity.
    simpl; rewrite (rep0_add c c2), <- app_assoc; reflexivity.
Qed.

Lemma mergeRk2Pre_spec (r c : N) (R : list Item) :
  repBlock (blkR r) (fst (mergeRk2Pre r c R)) ++ decR (snd (mergeRk2Pre r c R)) =
  repBlock (blkR r) c ++ decR R.
Proof.
  unfold mergeRk2Pre.
  destruct (1 <=? r) eqn:hr; [| reflexivity].
  destruct R as [| [rz | ? | ? ?] [| [? | v2 | ? ?] [| [? | v1 | ? ?] xs]]]; try reflexivity.
  destruct ((rz =? r) && (v2 =? 2) && (v1 =? 1)) eqn:hb; [| reflexivity].
  apply andb_true_iff in hb; destruct hb as [hb hv1].
  apply andb_true_iff in hb; destruct hb as [hrz hv2].
  apply N.eqb_eq in hrz; apply N.eqb_eq in hv2; apply N.eqb_eq in hv1.
  subst rz v2 v1; simpl.
  rewrite repBlock_succ_r; unfold blkR at 2; rewrite <- !app_assoc; reflexivity.
Qed.

Lemma decR_pushRk2 (r c : N) (R : list Item) :
  decR (pushRk2 r c R) = repBlock (blkR r) c ++ decR R.
Proof.
  unfold pushRk2.
  destruct (c =? 0) eqn:hc.
  - apply N.eqb_eq in hc; subst c; reflexivity.
  - pose proof (mergeRk2Pre_spec r c R) as key.
    destruct (mergeRk2Pre r c R) as [c' R']; simpl in key |- *.
    destruct R' as [| [? | ? | r2 c2] xs]; try exact key.
    destruct (r =? r2) eqn:hr; [| exact key].
    apply N.eqb_eq in hr; subst r2.
    simpl in key |- *; rewrite repBlock_add, <- app_assoc; exact key.
Qed.

Lemma decR_pushRd (v : N) (R : list Item) :
  decR (pushRd v R) = v :: decR R.
Proof.
  unfold pushRd.
  destruct (v =? 0) eqn:hv0.
  - apply N.eqb_eq in hv0; subst v; exact (decR_pushR0 1 R).
  - destruct (v =? 2) eqn:hv2; [| reflexivity].
    apply N.eqb_eq in hv2; subst v.
    destruct R as [| [? | v1 | ? ?] xs]; try reflexivity.
    destruct (v1 =? 1) eqn:hv1; [| reflexivity].
    apply N.eqb_eq in hv1; subst v1.
    rewrite decR_pushRk2, repBlock_1; reflexivity.
Qed.

Lemma decR_popR1_none (R : list Item) :
  popR1 R = None -> decR R = [].
Proof.
  induction R as [| [c | v | r c] xs ih]; intros h; simpl in h |- *.
  - reflexivity.
  - destruct (c =? 0) eqn:hc0.
    + apply N.eqb_eq in hc0; subst c; exact (ih h).
    + destruct (c =? 1); discriminate.
  - discriminate.
  - destruct (c =? 0) eqn:hc0.
    + apply N.eqb_eq in hc0; subst c; exact (ih h).
    + destruct (r =? 0); discriminate.
Qed.

Lemma decR_popR1_some (R : list Item) : forall (d : N) (R' : list Item),
  popR1 R = Some (d, R') -> decR R = d :: decR R'.
Proof.
  induction R as [| [c | v | r c] xs ih]; intros d R' h; simpl in h.
  - discriminate.
  - destruct (c =? 0) eqn:hc0.
    + apply N.eqb_eq in hc0; subst c; simpl; exact (ih d R' h).
    + apply N.eqb_neq in hc0.
      destruct (c =? 1) eqn:hc1.
      * apply N.eqb_eq in hc1; subst c; injection h as <- <-; reflexivity.
      * apply N.eqb_neq in hc1; injection h as <- <-; cbn [decR].
        replace c with ((c - 1) + 1) at 1 by lia.
        rewrite (rep0_succ (c - 1)); reflexivity.
  - injection h as <- <-; reflexivity.
  - destruct (c =? 0) eqn:hc0.
    + apply N.eqb_eq in hc0; subst c; simpl; exact (ih d R' h).
    + apply N.eqb_neq in hc0.
      destruct (r =? 0) eqn:hr0.
      * apply N.eqb_eq in hr0; subst r; injection h as <- <-.
        cbn [decR]; rewrite decR_popKTail.
        replace c with (1 + (c - 1)) at 1 by lia.
        rewrite repBlock_add, repBlock_1; reflexivity.
      * apply N.eqb_neq in hr0; injection h as <- <-.
        rewrite decR_pushR0; cbn [decR]; rewrite decR_popKTail.
        replace c with (1 + (c - 1)) at 1 by lia.
        rewrite repBlock_add, repBlock_1; unfold blkR at 1.
        replace r with ((r - 1) + 1) at 1 by lia.
        rewrite (rep0_succ (r - 1)), <- !app_assoc; reflexivity.
Qed.

Lemma decR_bumpR (R : list Item) : decR (bumpR R) = bumpHead (decR R).
Proof.
  unfold bumpR.
  destruct (popR1 R) as [[d R1] |] eqn:hp.
  - rewrite (decR_popR1_some R d R1 hp), decR_pushRd; reflexivity.
  - rewrite (decR_popR1_none R hp); reflexivity.
Qed.

Lemma decL_segsToItems (segs : list (N * N)) (acc : list Item) :
  decL (segsToItems segs acc) = decSegs segs ++ decL acc.
Proof.
  induction segs as [| [r c] ss ih]; simpl; [reflexivity |].
  destruct (c =? 0) eqn:hc.
  - apply N.eqb_eq in hc; subst c; simpl; exact ih.
  - simpl; rewrite ih, <- app_assoc; reflexivity.
Qed.

Lemma decL_unpackClean (z0 : N) (segs : list (N * N)) (bot : N) :
  decL (unpackClean z0 segs bot) = decLState (LS_clean z0 segs bot).
Proof.
  unfold unpackClean.
  destruct (z0 =? 0) eqn:hz.
  - apply N.eqb_eq in hz; subst z0.
    cbn [decL decLState]; rewrite decL_segsToItems; simpl; rewrite app_nil_r; reflexivity.
  - cbn [decL decLState]; rewrite decL_segsToItems; simpl; rewrite app_nil_r; reflexivity.
Qed.

Lemma packTail_spec (items : list Item) : forall (cur0 : N) (segs : list (N * N)) (bot : N),
  packTail cur0 items = Some (segs, bot) ->
  rep0 cur0 ++ decL items = decSegs segs ++ rep0 (bot + 2).
Proof.
  induction items as [| [c | v | r c] rest ih]; intros cur0 segs bot h; simpl in h.
  - destruct (2 <=? cur0) eqn:hb; [| discriminate].
    apply N.leb_le in hb; injection h as <- <-; simpl.
    rewrite app_nil_r; replace (cur0 - 2 + 2) with cur0 by lia; reflexivity.
  - pose proof (ih (cur0 + c) segs bot h) as hrec.
    cbn [decL]; rewrite app_assoc, <- (rep0_add cur0 c); exact hrec.
  - destruct ((v =? 1) && (2 <=? cur0)) eqn:hb; [| discriminate].
    apply andb_true_iff in hb; destruct hb as [hv hge].
    apply N.eqb_eq in hv; apply N.leb_le in hge; subst v.
    destruct (packTail 0 rest) as [[ss b] |] eqn:hp; [| discriminate].
    injection h as <- <-.
    pose proof (ih 0 ss b hp) as hrec; simpl in hrec.
    cbn [decL]; rewrite hrec, decSegs_pushSeg, repBlock_1; unfold blkL.
    replace (cur0 - 2 + 2) with cur0 by lia.
    rewrite <- !app_assoc; reflexivity.
  - destruct (c =? 0) eqn:hc0.
    + apply N.eqb_eq in hc0; subst c; cbn [decL]; rewrite repBlock_0; simpl.
      exact (ih cur0 segs bot h).
    + apply N.eqb_neq in hc0.
      destruct (packTail 0 rest) as [[ss b] |] eqn:hp; [| discriminate].
      injection h as <- <-.
      pose proof (ih 0 ss b hp) as hrec; simpl in hrec.
      cbn [decL]; rewrite hrec, !decSegs_pushSeg, repBlock_1; unfold blkL at 1.
      replace c with (1 + (c - 1)) at 1 by lia.
      rewrite repBlock_add, repBlock_1; unfold blkL at 1.
      rewrite !app_assoc, <- (rep0_add cur0 (r + 2)).
      replace (cur0 + (r + 2)) with (cur0 + r + 2) by lia.
      rewrite <- !app_assoc; reflexivity.
Qed.

Lemma packHead_spec (items : list Item) : forall (cur0 : N) (ls : LState),
  packHead cur0 items = Some ls ->
  rep0 cur0 ++ decL items = decLState ls.
Proof.
  induction items as [| [c | v | r c] rest ih]; intros cur0 ls h; simpl in h.
  - discriminate.
  - pose proof (ih (cur0 + c) ls h) as hrec.
    cbn [decL]; rewrite app_assoc, <- (rep0_add cur0 c); exact hrec.
  - destruct (v =? 1) eqn:hv; [| discriminate].
    apply N.eqb_eq in hv; subst v.
    destruct (packTail 0 rest) as [[ss b] |] eqn:hp; [| discriminate].
    injection h as <-.
    pose proof (packTail_spec rest 0 ss b hp) as hrec; simpl in hrec.
    cbn [decL decLState]; rewrite hrec; reflexivity.
  - destruct (c =? 0) eqn:hc0.
    + apply N.eqb_eq in hc0; subst c; cbn [decL]; rewrite repBlock_0; simpl.
      exact (ih cur0 ls h).
    + apply N.eqb_neq in hc0.
      destruct (packTail 0 rest) as [[ss b] |] eqn:hp; [| discriminate].
      injection h as <-.
      pose proof (packTail_spec rest 0 ss b hp) as hrec; simpl in hrec.
      cbn [decL decLState]; rewrite hrec, decSegs_pushSeg.
      replace c with (1 + (c - 1)) at 1 by lia.
      rewrite repBlock_add, repBlock_1; unfold blkL at 1.
      rewrite !app_assoc, <- (rep0_add cur0 (r + 2)).
      replace (cur0 + (r + 2)) with (cur0 + r + 2) by lia.
      rewrite <- !app_assoc; reflexivity.
Qed.

(* ========================================================================== *)
(* Section 5: Modular Transition Engine `rleStep` & Per-Mode Soundness        *)
(* ========================================================================== *)

Record RleFullState : Type := mkRleState {
  rle_mode : StackMode;
  rle_ls : LState;
  rle_R : list Item;
  rle_halted : bool
}.

Definition evalRle (s : RleFullState) : Q * tape :=
  evalStackCfg1 (rle_mode s) (decLState (rle_ls s)) (decR (rle_R s)).

Definition StateHalts (s : RleFullState) : Prop :=
  rle_halted s = true \/ halts tm (evalRle s).

Lemma stateHalts_of_stepStar {c : Q * tape} {s' : RleFullState}
  (hh : StateHalts s')
  (hf : rle_halted s' = false)
  (hstep : c -->* evalRle s') : halts tm c.
Proof.
  destruct hh as [hh | hh].
  - rewrite hf in hh; discriminate.
  - eapply halts_evstep; [exact hh | exact hstep].
Qed.

Definition isTopD1 (items : list Item) : bool :=
  match items with
  | IT_d v :: _ => v =? 1
  | _ => false
  end.

Definition isEmpty {A : Type} (xs : list A) : bool :=
  match xs with
  | [] => true
  | _ :: _ => false
  end.

Definition modeCanPack (m : StackMode) (items R : list Item) : bool :=
  match m with
  | SM_B => isEmpty R || isTopD1 items
  | SM_BR => isEmpty R
  | SM_DR0 => true
  | SM_C => false
  end.

Definition minN (a b : N) : N := if a <=? b then a else b.

Lemma minN_le_l (a b : N) : minN a b <= a.
Proof.
  unfold minN; destruct (a <=? b) eqn:hab; [lia |].
  apply N.leb_gt in hab; lia.
Qed.

Lemma minN_le_r (a b : N) : minN a b <= b.
Proof.
  unfold minN; destruct (a <=? b) eqn:hab; [apply N.leb_le in hab; lia | lia].
Qed.

(* 5.1 Raw B *)
Definition stepRawB (items R : list Item) : RleFullState :=
  match R with
  | [] => mkRleState SM_C (LS_raw (bumpL items)) [] false
  | IT_z c :: R1 => mkRleState SM_B (LS_raw (pushL0 c items)) R1 false
  | _ =>
    match popR1 R with
    | None => mkRleState SM_C (LS_raw (bumpL items)) [] false
    | Some (d, R1) =>
      if d =? 0 then mkRleState SM_B (LS_raw (pushL0 1 items)) R1 false
      else mkRleState SM_BR (LS_raw items) (pushR0 1 (pushRd (d - 1) R1)) false
    end
  end.

Lemma stepRawB_halts (items R : list Item) (hh : StateHalts (stepRawB items R)) :
  halts tm (cfg_B (decL items) (decR R)).
Proof.
  unfold stepRawB in hh.
  destruct R as [| [c | v | r c] R1].
  - apply (stateHalts_of_stepStar hh eq_refl).
    unfold evalRle; simpl; rewrite decL_bumpL.
    exact (pev (rule_B_nil (decL items))).
  - apply (stateHalts_of_stepStar hh eq_refl).
    unfold evalRle; simpl; rewrite decL_pushL0.
    exact (rule_B_zeros_all (decL items) (decR R1) c).
  - destruct (popR1 (IT_d v :: R1)) as [[d R2] |] eqn:hp; [| discriminate].
    pose proof (decR_popR1_some _ d R2 hp) as hR.
    destruct (d =? 0) eqn:hd0.
    + apply N.eqb_eq in hd0; subst d.
      apply (stateHalts_of_stepStar hh eq_refl).
      rewrite hR; unfold evalRle; simpl; rewrite decL_pushL0; simpl.
      exact (pev (rule_B_zero (decL items) (decR R2))).
    + apply N.eqb_neq in hd0.
      apply (stateHalts_of_stepStar hh eq_refl).
      rewrite hR; replace d with ((d - 1) + 1) at 1 by lia.
      unfold evalRle; simpl; rewrite decR_pushR0, decR_pushRd; simpl.
      exact (pev (rule_B_succ (d - 1) (decL items) (decR R2))).
  - destruct (popR1 (IT_k r c :: R1)) as [[d R2] |] eqn:hp.
    + pose proof (decR_popR1_some _ d R2 hp) as hR.
      destruct (d =? 0) eqn:hd0.
      * apply N.eqb_eq in hd0; subst d.
        apply (stateHalts_of_stepStar hh eq_refl).
        rewrite hR; unfold evalRle; simpl; rewrite decL_pushL0; simpl.
        exact (pev (rule_B_zero (decL items) (decR R2))).
      * apply N.eqb_neq in hd0.
        apply (stateHalts_of_stepStar hh eq_refl).
        rewrite hR; replace d with ((d - 1) + 1) at 1 by lia.
        unfold evalRle; simpl; rewrite decR_pushR0, decR_pushRd; simpl.
        exact (pev (rule_B_succ (d - 1) (decL items) (decR R2))).
    + apply (stateHalts_of_stepStar hh eq_refl).
      rewrite (decR_popR1_none _ hp); unfold evalRle; simpl; rewrite decL_bumpL.
      exact (pev (rule_B_nil (decL items))).
Qed.

(* 5.2 Raw BR *)
Definition stepRawBRPop (items R : list Item) : RleFullState :=
  match popR1 R with
  | None => mkRleState SM_C (LS_raw (bumpL items)) [] false
  | Some (d, R1) =>
    if d =? 0 then mkRleState SM_BR (LS_raw (pushL0 1 items)) R1 false
    else if d =? 1 then mkRleState SM_DR0 (LS_raw items) (bumpR R1) false
    else mkRleState SM_B (LS_raw (bumpL items)) (pushRd (d - 2) R1) false
  end.

Lemma stepRawBRPop_halts (items R : list Item) (hh : StateHalts (stepRawBRPop items R)) :
  halts tm (cfg_BR (decL items) (decR R)).
Proof.
  unfold stepRawBRPop in hh.
  destruct (popR1 R) as [[d R1] |] eqn:hp.
  - pose proof (decR_popR1_some R d R1 hp) as hR.
    destruct (d =? 0) eqn:hd0.
    + apply N.eqb_eq in hd0; subst d.
      apply (stateHalts_of_stepStar hh eq_refl).
      rewrite hR; unfold evalRle; simpl; rewrite decL_pushL0; simpl.
      exact (pev (rule_BR_zero (decL items) (decR R1))).
    + apply N.eqb_neq in hd0.
      destruct (d =? 1) eqn:hd1.
      * apply N.eqb_eq in hd1; subst d.
        apply (stateHalts_of_stepStar hh eq_refl).
        rewrite hR; unfold evalRle; simpl; rewrite decR_bumpR.
        exact (pev (rule_BR_one (decL items) (decR R1))).
      * apply N.eqb_neq in hd1.
        apply (stateHalts_of_stepStar hh eq_refl).
        rewrite hR; replace d with ((d - 2) + 2) at 1 by lia.
        unfold evalRle; simpl; rewrite decL_bumpL, decR_pushRd.
        exact (pev (rule_BR_add_two (d - 2) (decL items) (decR R1))).
  - apply (stateHalts_of_stepStar hh eq_refl).
    rewrite (decR_popR1_none R hp); unfold evalRle; simpl; rewrite decL_bumpL.
    exact (pev (rule_BR_nil (decL items))).
Qed.

Definition stepRawBR (items R : list Item) : RleFullState :=
  match R with
  | [] => mkRleState SM_C (LS_raw (bumpL items)) [] false
  | IT_z c :: R1 => mkRleState SM_BR (LS_raw (pushL0 c items)) R1 false
  | IT_k r m :: R1 =>
    if 1 <=? m then
      match popL1 items with
      | Some (a, L1) =>
        if a =? 0 then
          mkRleState SM_BR (LS_raw (pushL0 3 (pushLd 1 (pushLk2 r (m - 1) (pushL0 r L1))))) R1 false
        else stepRawBRPop items (IT_k r m :: R1)
      | None => stepRawBRPop items (IT_k r m :: R1)
      end
    else mkRleState SM_BR (LS_raw items) R1 false
  | IT_d v :: R1 => stepRawBRPop items (IT_d v :: R1)
  end.

Lemma stepRawBR_halts (items R : list Item) (hh : StateHalts (stepRawBR items R)) :
  halts tm (cfg_BR (decL items) (decR R)).
Proof.
  unfold stepRawBR in hh.
  destruct R as [| [c | v | r m] R1].
  - apply (stateHalts_of_stepStar hh eq_refl).
    unfold evalRle; simpl; rewrite decL_bumpL.
    exact (pev (rule_BR_nil (decL items))).
  - apply (stateHalts_of_stepStar hh eq_refl).
    unfold evalRle; simpl; rewrite decL_pushL0.
    exact (rule_BR_zeros_all (decL items) (decR R1) c).
  - exact (stepRawBRPop_halts items (IT_d v :: R1) hh).
  - destruct (1 <=? m) eqn:hm1.
    + apply N.leb_le in hm1.
      destruct (popL1 items) as [[a L1] |] eqn:hpL.
      * destruct (a =? 0) eqn:ha0.
        -- apply N.eqb_eq in ha0; subst a.
           apply (stateHalts_of_stepStar hh eq_refl).
           rewrite (decL_popL1_some items 0 L1 hpL); cbn [decR].
           replace m with ((m - 1) + 1) at 1 by lia.
           unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
           rewrite decL_pushL0, decL_pushLd, decL_pushLk2, decL_pushL0.
           exact (rule_BR_blkR_succ (m - 1) r (decL L1) (decR R1)).
        -- exact (stepRawBRPop_halts items (IT_k r m :: R1) hh).
      * exact (stepRawBRPop_halts items (IT_k r m :: R1) hh).
    + apply N.leb_gt in hm1; assert (m = 0) by lia; subst m.
      apply (stateHalts_of_stepStar hh eq_refl).
      apply evstep_refl.
Qed.

(* 5.3 Raw DR0 *)
Definition stepRawDR0Atomic (items R : list Item) : RleFullState :=
  match popL1 items with
  | None => mkRleState SM_C (LS_raw [IT_d 1]) R false
  | Some (a, L1) =>
    if a =? 0 then
      match items with
      | IT_z c :: Lrest => mkRleState SM_DR0 (LS_raw Lrest) (pushR0 c R) false
      | _ => mkRleState SM_DR0 (LS_raw L1) (pushR0 1 R) false
      end
    else mkRleState SM_C (LS_raw (pushLd (a - 1) L1)) (pushR0 1 R) false
  end.

Lemma stepRawDR0Atomic_halts (items R : list Item) (hh : StateHalts (stepRawDR0Atomic items R)) :
  halts tm (cfg_DR0 (decL items) (decR R)).
Proof.
  unfold stepRawDR0Atomic in hh.
  destruct (popL1 items) as [[a L1] |] eqn:hpL.
  - pose proof (decL_popL1_some items a L1 hpL) as hL.
    destruct (a =? 0) eqn:ha0.
    + apply N.eqb_eq in ha0; subst a.
      destruct items as [| [c | v | r c] Lrest]; [discriminate | | |].
      * apply (stateHalts_of_stepStar hh eq_refl).
        unfold evalRle; simpl; rewrite decR_pushR0.
        exact (rule_DR0_zeros_all (decL Lrest) (decR R) c).
      * apply (stateHalts_of_stepStar hh eq_refl).
        rewrite hL; unfold evalRle; simpl; rewrite decR_pushR0; simpl.
        exact (pev (rule_DR0_zero (decL L1) (decR R))).
      * apply (stateHalts_of_stepStar hh eq_refl).
        rewrite hL; unfold evalRle; simpl; rewrite decR_pushR0; simpl.
        exact (pev (rule_DR0_zero (decL L1) (decR R))).
    + apply N.eqb_neq in ha0.
      apply (stateHalts_of_stepStar hh eq_refl).
      rewrite hL; replace a with ((a - 1) + 1) at 1 by lia.
      unfold evalRle; simpl; rewrite decL_pushLd, decR_pushR0; simpl.
      exact (pev (rule_DR0_succ (a - 1) (decL L1) (decR R))).
  - apply (stateHalts_of_stepStar hh eq_refl).
    rewrite (decL_popL1_none items hpL); unfold evalRle; simpl.
    exact (pev (rule_DR0_nil (decR R))).
Qed.

Definition stepRawDR0 (items R : list Item) : RleFullState :=
  match items with
  | [IT_z c] =>
    match R with
    | IT_d v1 :: IT_z q :: R2 =>
      if v1 =? 1 then mkRleState SM_DR0 (LS_raw [IT_z (c + 3 * q)]) (IT_d 1 :: R2) false
      else mkRleState SM_BR (LS_raw [IT_z (c + 3)]) R false
    | _ => mkRleState SM_BR (LS_raw [IT_z (c + 3)]) R false
    end
  | _ => stepRawDR0Atomic items R
  end.

Lemma stepRawDR0_halts (items R : list Item) (hh : StateHalts (stepRawDR0 items R)) :
  halts tm (cfg_DR0 (decL items) (decR R)).
Proof.
  unfold stepRawDR0 in hh.
  destruct items as [| [c | v | r c] [| hd2 xs]];
    try exact (stepRawDR0Atomic_halts _ R hh).
  assert (hbot : StateHalts (mkRleState SM_BR (LS_raw [IT_z (c + 3)]) R false) ->
                 halts tm (cfg_DR0 (decL [IT_z c]) (decR R))).
  { intros hhb.
    apply (stateHalts_of_stepStar hhb eq_refl).
    unfold evalRle; simpl; rewrite !app_nil_r.
    exact (rule_DR0_bot c (decR R)). }
  destruct R as [| [? | v1 | ? ?] [| [q | ? | ? ?] R2]]; try exact (hbot hh).
  destruct (v1 =? 1) eqn:hv1; [| exact (hbot hh)].
  apply N.eqb_eq in hv1; subst v1.
  apply (stateHalts_of_stepStar hh eq_refl).
  unfold evalRle; simpl; rewrite !app_nil_r.
  exact (rule_DR0_bot_zeros q c (decR R2)).
Qed.

(* 5.4 Raw C *)
Definition stepRawCAtomic (items R : list Item) : RleFullState :=
  match popL1 items with
  | None => mkRleState SM_DR0 (LS_raw []) R false
  | Some (a, L1) =>
    if a =? 0 then
      match popL1 L1 with
      | None => mkRleState SM_C (LS_raw []) (pushRd 1 R) false
      | Some (a1, L3) =>
        if a1 =? 0 then mkRleState SM_C (LS_raw (bumpL L3)) (pushRd 1 R) false
        else if a1 =? 1 then mkRleState SM_C (LS_raw (bumpL (bumpL L3))) (pushR0 1 (bumpR R)) false
        else mkRleState SM_BR (LS_raw (pushLd (a1 - 2) L3)) (pushR0 1 (pushRd 1 R)) false
      end
    else if a =? 1 then
      match popL1 L1 with
      | None => mkRleState SM_B (LS_raw [IT_z 1]) (pushRd 1 R) false
      | Some (a1, L3) =>
        if a1 =? 0 then mkRleState SM_DR0 (LS_raw L3) (pushRd 2 R) false
        else mkRleState SM_C (LS_raw (pushLd (a1 - 1) L3)) (pushRd 2 R) false
      end
    else mkRleState SM_C (LS_raw (pushLd a L1)) R true
  end.

Lemma stepRawCAtomic_halts (items R : list Item) (hh : StateHalts (stepRawCAtomic items R)) :
  halts tm (cfg_C (decL items) (decR R)).
Proof.
  unfold stepRawCAtomic in hh.
  destruct (popL1 items) as [[a L1] |] eqn:hp1.
  - pose proof (decL_popL1_some items a L1 hp1) as hL1.
    destruct (a =? 0) eqn:ha0.
    + apply N.eqb_eq in ha0; subst a.
      destruct (popL1 L1) as [[a1 L3] |] eqn:hp2.
      * pose proof (decL_popL1_some L1 a1 L3 hp2) as hL2.
        destruct (a1 =? 0) eqn:ha10.
        -- apply N.eqb_eq in ha10; subst a1.
           apply (stateHalts_of_stepStar hh eq_refl).
           rewrite hL1, hL2; unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
           rewrite decL_bumpL, decR_pushRd.
           exact (pev (rule_C_zero_zero (decL L3) (decR R))).
        -- apply N.eqb_neq in ha10.
           destruct (a1 =? 1) eqn:ha11.
           ++ apply N.eqb_eq in ha11; subst a1.
              apply (stateHalts_of_stepStar hh eq_refl).
              rewrite hL1, hL2; unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
              rewrite !decL_bumpL, decR_pushR0, decR_bumpR; simpl.
              exact (pev (rule_C_zero_one (decL L3) (decR R))).
           ++ apply N.eqb_neq in ha11.
              apply (stateHalts_of_stepStar hh eq_refl).
              rewrite hL1, hL2; replace a1 with ((a1 - 2) + 2) at 1 by lia.
              unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
              rewrite decL_pushLd, decR_pushR0, decR_pushRd; simpl.
              exact (pev (rule_C_zero_add_two (a1 - 2) (decL L3) (decR R))).
      * apply (stateHalts_of_stepStar hh eq_refl).
        rewrite hL1, (decL_popL1_none L1 hp2).
        unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState decL]; rewrite decR_pushRd.
        exact (pev (rule_C_zero_nil (decR R))).
    + apply N.eqb_neq in ha0.
      destruct (a =? 1) eqn:ha1.
      * apply N.eqb_eq in ha1; subst a.
        destruct (popL1 L1) as [[a1 L3] |] eqn:hp2.
        -- pose proof (decL_popL1_some L1 a1 L3 hp2) as hL2.
           destruct (a1 =? 0) eqn:ha10.
           ++ apply N.eqb_eq in ha10; subst a1.
              apply (stateHalts_of_stepStar hh eq_refl).
              rewrite hL1, hL2; unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
              rewrite decR_pushRd.
              exact (pev (rule_C_one_zero (decL L3) (decR R))).
           ++ apply N.eqb_neq in ha10.
              apply (stateHalts_of_stepStar hh eq_refl).
              rewrite hL1, hL2; replace a1 with ((a1 - 1) + 1) at 1 by lia.
              unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
              rewrite decL_pushLd, decR_pushRd.
              exact (pev (rule_C_one_succ (a1 - 1) (decL L3) (decR R))).
        -- apply (stateHalts_of_stepStar hh eq_refl).
           rewrite hL1, (decL_popL1_none L1 hp2).
           unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState decL]; rewrite decR_pushRd.
           exact (pev (rule_C_one_nil (decR R))).
      * apply N.eqb_neq in ha1.
        rewrite hL1; replace a with ((a - 2) + 2) by lia.
        exact (rule_C_add_two_halt (a - 2) (decL L1) (decR R)).
  - apply (stateHalts_of_stepStar hh eq_refl).
    rewrite (decL_popL1_none items hp1); unfold evalRle; simpl.
    exact (pev (rule_C_nil (decR R))).
Qed.

Definition stepRawC (items R : list Item) : RleFullState :=
  match items with
  | IT_z cz :: IT_k r m :: L2 =>
    if cz =? 1 then mkRleState SM_C (LS_raw (pushL0 1 L2)) (pushRk2 r m R) false
    else stepRawCAtomic items R
  | IT_z cz :: IT_d v1 :: L2 =>
    if (4 <=? cz) && (v1 =? 1) then
      mkRleState SM_C (LS_raw (pushL0 1 L2)) (pushRk2 (cz - 3) 1 R) false
    else stepRawCAtomic items R
  | [IT_z cz] =>
    if 4 <=? cz then mkRleState SM_DR0 (LS_raw []) (pushRk2 (cz - 4) 1 R) false
    else stepRawCAtomic items R
  | _ => stepRawCAtomic items R
  end.

Lemma stepRawC_halts (items R : list Item) (hh : StateHalts (stepRawC items R)) :
  halts tm (cfg_C (decL items) (decR R)).
Proof.
  unfold stepRawC in hh.
  destruct items as [| [cz | v | r m] rest1];
    try exact (stepRawCAtomic_halts _ R hh).
  destruct rest1 as [| [c2 | v1 | r m] L2].
  - destruct (4 <=? cz) eqn:h4; [| exact (stepRawCAtomic_halts _ R hh)].
    apply N.leb_le in h4.
    apply (stateHalts_of_stepStar hh eq_refl).
    cbn [decL]; rewrite app_nil_r; replace cz with ((cz - 4) + 4) at 1 by lia.
    unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState decL].
    rewrite decR_pushRk2, repBlock_1.
    exact (rule_C_bot_four (cz - 4) (decR R)).
  - exact (stepRawCAtomic_halts _ R hh).
  - destruct ((4 <=? cz) && (v1 =? 1)) eqn:hb; [| exact (stepRawCAtomic_halts _ R hh)].
    apply andb_true_iff in hb; destruct hb as [h4 hv1].
    apply N.leb_le in h4; apply N.eqb_eq in hv1; subst v1.
    apply (stateHalts_of_stepStar hh eq_refl).
    cbn [decL]; replace cz with ((cz - 3) + 3) at 1 by lia.
    unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
    rewrite decL_pushL0, decR_pushRk2, repBlock_1; simpl.
    exact (rule_C_r_add_three (cz - 3) (decL L2) (decR R)).
  - destruct (cz =? 1) eqn:hcz; [| exact (stepRawCAtomic_halts _ R hh)].
    apply N.eqb_eq in hcz; subst cz.
    apply (stateHalts_of_stepStar hh eq_refl).
    unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState decL].
    rewrite decL_pushL0, decR_pushRk2; simpl.
    exact (rule_C_blkL_pow m r (decL L2) (decR R)).
Qed.

(* 5.5 Clean B *)
Definition stepCleanBPop (z0 : N) (segs : list (N * N)) (bot : N) (R : list Item) : RleFullState :=
  match popR1 R with
  | None => mkRleState SM_B (LS_raw (unpackClean z0 segs bot)) R false
  | Some (d, R1) =>
    if d =? 0 then mkRleState SM_B (LS_clean (z0 + 1) segs bot) R1 false
    else mkRleState SM_BR (LS_clean z0 segs bot) (pushR0 1 (pushRd (d - 1) R1)) false
  end.

Lemma stepCleanBPop_halts (z0 : N) (segs : list (N * N)) (bot : N) (R : list Item)
  (hh : StateHalts (stepCleanBPop z0 segs bot R)) :
  halts tm (cfg_B (decLState (LS_clean z0 segs bot)) (decR R)).
Proof.
  unfold stepCleanBPop in hh.
  destruct (popR1 R) as [[d R1] |] eqn:hp.
  - pose proof (decR_popR1_some R d R1 hp) as hR.
    destruct (d =? 0) eqn:hd0.
    + apply N.eqb_eq in hd0; subst d.
      apply (stateHalts_of_stepStar hh eq_refl).
      rewrite hR; unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1].
      assert (heq : 0 :: decLState (LS_clean z0 segs bot) =
                    decLState (LS_clean (z0 + 1) segs bot)).
      { cbn [decLState]; rewrite (rep0_succ z0); reflexivity. }
      rewrite <- heq.
      exact (pev (rule_B_zero (decLState (LS_clean z0 segs bot)) (decR R1))).
    + apply N.eqb_neq in hd0.
      apply (stateHalts_of_stepStar hh eq_refl).
      rewrite hR; replace d with ((d - 1) + 1) at 1 by lia.
      unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1].
      rewrite decR_pushR0, decR_pushRd; simpl.
      exact (pev (rule_B_succ (d - 1) (decLState (LS_clean z0 segs bot)) (decR R1))).
  - apply (stateHalts_of_stepStar hh eq_refl).
    unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
    rewrite decL_unpackClean; apply evstep_refl.
Qed.

Definition stepCleanB (z0 : N) (segs : list (N * N)) (bot : N) (R : list Item) : RleFullState :=
  match R with
  | [] =>
    if (1 <=? z0) && (1 <=? bot) then
      mkRleState SM_B (LS_clean 1 (pushSeg 0 (bot - 1) (pushSeg (z0 - 1) 1 segs)) 0) [] false
    else mkRleState SM_B (LS_raw (unpackClean z0 segs bot)) [] false
  | IT_z cz :: IT_k r cnt :: Rrem =>
    if (z0 =? 0) && (1 <=? bot) && (cz =? 1) then
      let q := minN cnt bot in
      if 1 <=? q then
        let Rnew := if cnt =? q then IT_z 1 :: Rrem else IT_z 1 :: IT_k r (cnt - q) :: Rrem in
        mkRleState SM_B (LS_clean 0 (pushSeg (r + 3) q segs) (bot - q)) Rnew false
      else mkRleState SM_B (LS_clean (z0 + cz) segs bot) (IT_k r cnt :: Rrem) false
    else mkRleState SM_B (LS_clean (z0 + cz) segs bot) (IT_k r cnt :: Rrem) false
  | IT_z cz :: R1 =>
    mkRleState SM_B (LS_clean (z0 + cz) segs bot) R1 false
  | IT_d v1 :: IT_d v2 :: IT_k r cnt :: Rrem =>
    if (z0 =? 0) && (v1 =? 1) && (v2 =? 1) then
      let q := minN cnt (bot / (r + 1)) in
      if 1 <=? q then
        let Rnew := if cnt =? q then IT_d 1 :: IT_d 1 :: Rrem else IT_d 1 :: IT_d 1 :: IT_k r (cnt - q) :: Rrem in
        mkRleState SM_B (LS_clean 0 (pushSeg (4 * r + 3) q segs) (bot - q * (r + 1))) Rnew false
      else mkRleState SM_BR (LS_clean z0 segs bot) (pushR0 1 (pushRd 0 (IT_d v2 :: IT_k r cnt :: Rrem))) false
    else stepCleanBPop z0 segs bot (IT_d v1 :: IT_d v2 :: IT_k r cnt :: Rrem)
  | _ => stepCleanBPop z0 segs bot R
  end.

Lemma stepCleanB_halts (z0 : N) (segs : list (N * N)) (bot : N) (R : list Item)
  (hh : StateHalts (stepCleanB z0 segs bot R)) :
  halts tm (cfg_B (decLState (LS_clean z0 segs bot)) (decR R)).
Proof.
  unfold stepCleanB in hh.
  destruct R as [| [cz | v1 | r1 c1] R1].
  - destruct ((1 <=? z0) && (1 <=? bot)) eqn:hb.
    + apply andb_true_iff in hb; destruct hb as [hz0 hbot].
      apply N.leb_le in hz0; apply N.leb_le in hbot.
      apply (stateHalts_of_stepStar hh eq_refl).
      pose proof (clean_RNIL_one SM_B (or_introl eq_refl) (z0 - 1) segs (bot - 1)) as h1.
      pose proof (clean_RNIL_zero_pow (bot - 1) (pushSeg (z0 - 1) 1 segs) 0) as h2.
      replace (z0 - 1 + 1) with z0 in h1 by lia.
      replace (bot - 1 + 1) with bot in h1 by lia.
      rewrite N.add_0_l in h2.
      exact (etrans h1 h2).
    + apply (stateHalts_of_stepStar hh eq_refl).
      unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState decR].
      rewrite decL_unpackClean; apply evstep_refl.
  - assert (h_zonly : forall (Rtail : list Item),
      StateHalts (mkRleState SM_B (LS_clean (z0 + cz) segs bot) Rtail false) ->
      halts tm (cfg_B (decLState (LS_clean z0 segs bot)) (decR (IT_z cz :: Rtail)))).
    { intros Rtail hhz.
      apply (stateHalts_of_stepStar hhz eq_refl).
      pose proof (rule_B_zeros_all (decLState (LS_clean z0 segs bot)) (decR Rtail) cz) as hstep.
      assert (heq : rep0 cz ++ decLState (LS_clean z0 segs bot) =
                    decLState (LS_clean (z0 + cz) segs bot)).
      { cbn [decLState]; rewrite app_assoc, <- (rep0_add cz z0).
        replace (cz + z0) with (z0 + cz) by lia; reflexivity. }
      rewrite heq in hstep; exact hstep. }
    destruct R1 as [| [? | ? | r cnt] Rrem]; try exact (h_zonly _ hh).
    destruct ((z0 =? 0) && (1 <=? bot) && (cz =? 1)) eqn:hb; [| exact (h_zonly _ hh)].
    apply andb_true_iff in hb; destruct hb as [hb hcz].
    apply andb_true_iff in hb; destruct hb as [hz0 hbot].
    apply N.eqb_eq in hz0; apply N.leb_le in hbot; apply N.eqb_eq in hcz; subst z0 cz.
    destruct (1 <=? minN cnt bot) eqn:hq1; [| exact (h_zonly _ hh)].
    set (q := minN cnt bot) in *.
    assert (hqcnt : q <= cnt) by apply minN_le_l.
    assert (hqbot : q <= bot) by apply minN_le_r.
    apply (stateHalts_of_stepStar hh eq_refl).
    pose proof (clean_P1_pow q r segs (bot - q) (repBlock (blkR r) (cnt - q) ++ decR Rrem)) as hstep.
    replace (bot - q + q) with bot in hstep by lia.
    assert (heqR1 : 0 :: (repBlock (blkR r) q ++ (repBlock (blkR r) (cnt - q) ++ decR Rrem)) =
                    decR (IT_z 1 :: IT_k r cnt :: Rrem)).
    { rewrite app_assoc, <- repBlock_add; replace (q + (cnt - q)) with cnt by lia; reflexivity. }
    assert (heqR2 : 0 :: (repBlock (blkR r) (cnt - q) ++ decR Rrem) =
                    decR (if cnt =? q then IT_z 1 :: Rrem else IT_z 1 :: IT_k r (cnt - q) :: Rrem)).
    { destruct (cnt =? q) eqn:heq.
      - apply N.eqb_eq in heq; rewrite heq, N.sub_diag; reflexivity.
      - reflexivity. }
    rewrite heqR1, heqR2 in hstep; exact hstep.
  - destruct R1 as [| [? | v2 | ? ?] [| [? | ? | r cnt] Rrem]];
      try exact (stepCleanBPop_halts z0 segs bot _ hh).
    destruct ((z0 =? 0) && (v1 =? 1) && (v2 =? 1)) eqn:hb;
      [| exact (stepCleanBPop_halts z0 segs bot _ hh)].
    apply andb_true_iff in hb; destruct hb as [hb hv2].
    apply andb_true_iff in hb; destruct hb as [hz0 hv1].
    apply N.eqb_eq in hz0; apply N.eqb_eq in hv1; apply N.eqb_eq in hv2; subst z0 v1 v2.
    destruct (1 <=? minN cnt (bot / (r + 1))) eqn:hq1.
    + set (q := minN cnt (bot / (r + 1))) in *.
      assert (hqcnt : q <= cnt) by apply minN_le_l.
      assert (hqdiv : q <= bot / (r + 1)) by apply minN_le_r.
      assert (hqmul : q * (r + 1) <= bot).
      { apply N.le_trans with (m := (bot / (r + 1)) * (r + 1)).
        - apply N.mul_le_mono_nonneg_r; [lia | exact hqdiv].
        - rewrite N.mul_comm; apply N.Div0.mul_div_le. }
      apply (stateHalts_of_stepStar hh eq_refl).
      pose proof (clean_P2_pow q r segs (bot - q * (r + 1)) (repBlock (blkR r) (cnt - q) ++ decR Rrem)) as hstep.
      replace (bot - q * (r + 1) + q * (r + 1)) with bot in hstep by lia.
      assert (heqR1 : 1 :: 1 :: (repBlock (blkR r) q ++ (repBlock (blkR r) (cnt - q) ++ decR Rrem)) =
                      decR (IT_d 1 :: IT_d 1 :: IT_k r cnt :: Rrem)).
      { rewrite app_assoc, <- repBlock_add; replace (q + (cnt - q)) with cnt by lia; reflexivity. }
      assert (heqR2 : 1 :: 1 :: (repBlock (blkR r) (cnt - q) ++ decR Rrem) =
                      decR (if cnt =? q then IT_d 1 :: IT_d 1 :: Rrem else IT_d 1 :: IT_d 1 :: IT_k r (cnt - q) :: Rrem)).
      { destruct (cnt =? q) eqn:heq.
        - apply N.eqb_eq in heq; rewrite heq, N.sub_diag; reflexivity.
        - reflexivity. }
      rewrite heqR1, heqR2 in hstep; exact hstep.
    + apply (stateHalts_of_stepStar hh eq_refl).
      unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1].
      rewrite decR_pushR0, decR_pushRd; simpl.
      exact (pev (rule_B_succ 0 (decLState (LS_clean 0 segs bot)) (1 :: repBlock (blkR r) cnt ++ decR Rrem))).
  - exact (stepCleanBPop_halts z0 segs bot _ hh).
Qed.

(* 5.6 Clean BR *)
Definition stepCleanBR (z0 : N) (segs : list (N * N)) (bot : N) (R : list Item) : RleFullState :=
  match R with
  | [] =>
    if (1 <=? z0) && (1 <=? bot) then
      mkRleState SM_B (LS_clean 1 (pushSeg 0 (bot - 1) (pushSeg (z0 - 1) 1 segs)) 0) [] false
    else mkRleState SM_BR (LS_raw (unpackClean z0 segs bot)) [] false
  | IT_z cz :: R1 =>
    mkRleState SM_BR (LS_clean (z0 + cz) segs bot) R1 false
  | IT_k r m :: R1 =>
    if (1 <=? m) && (1 <=? z0) && (3 <=? r + z0) then
      mkRleState SM_BR (LS_clean 3 (pushSeg r (m - 1) (pushSeg (r + z0 - 3) 1 segs)) bot) R1 false
    else mkRleState SM_BR (LS_raw (unpackClean z0 segs bot)) (IT_k r m :: R1) false
  | IT_d v :: R1 =>
    match popR1 (IT_d v :: R1) with
    | None => mkRleState SM_BR (LS_raw (unpackClean z0 segs bot)) (IT_d v :: R1) false
    | Some (d, R2) =>
      if d =? 0 then mkRleState SM_BR (LS_clean (z0 + 1) segs bot) R2 false
      else if d =? 1 then mkRleState SM_DR0 (LS_clean z0 segs bot) (bumpR R2) false
      else if 3 <=? z0 then
        mkRleState SM_B (LS_clean 0 (pushSeg (z0 - 3) 1 segs) bot) (pushRd (d - 2) R2) false
      else mkRleState SM_BR (LS_raw (unpackClean z0 segs bot)) (IT_d v :: R1) false
    end
  end.

Lemma stepCleanBR_halts (z0 : N) (segs : list (N * N)) (bot : N) (R : list Item)
  (hh : StateHalts (stepCleanBR z0 segs bot R)) :
  halts tm (cfg_BR (decLState (LS_clean z0 segs bot)) (decR R)).
Proof.
  unfold stepCleanBR in hh.
  destruct R as [| [cz | v | r m] R1].
  - destruct ((1 <=? z0) && (1 <=? bot)) eqn:hb.
    + apply andb_true_iff in hb; destruct hb as [hz0 hbot].
      apply N.leb_le in hz0; apply N.leb_le in hbot.
      apply (stateHalts_of_stepStar hh eq_refl).
      pose proof (clean_RNIL_one SM_BR (or_intror eq_refl) (z0 - 1) segs (bot - 1)) as h1.
      pose proof (clean_RNIL_zero_pow (bot - 1) (pushSeg (z0 - 1) 1 segs) 0) as h2.
      replace (z0 - 1 + 1) with z0 in h1 by lia.
      replace (bot - 1 + 1) with bot in h1 by lia.
      rewrite N.add_0_l in h2.
      exact (etrans h1 h2).
    + apply (stateHalts_of_stepStar hh eq_refl).
      unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState decR].
      rewrite decL_unpackClean; apply evstep_refl.
  - apply (stateHalts_of_stepStar hh eq_refl).
    pose proof (rule_BR_zeros_all (decLState (LS_clean z0 segs bot)) (decR R1) cz) as hstep.
    assert (heq : rep0 cz ++ decLState (LS_clean z0 segs bot) =
                  decLState (LS_clean (z0 + cz) segs bot)).
    { cbn [decLState]; rewrite app_assoc, <- (rep0_add cz z0).
      replace (cz + z0) with (z0 + cz) by lia; reflexivity. }
    rewrite heq in hstep; exact hstep.
  - destruct (popR1 (IT_d v :: R1)) as [[d R2] |] eqn:hp; [| discriminate].
    pose proof (decR_popR1_some _ d R2 hp) as hR.
    destruct (d =? 0) eqn:hd0.
    + apply N.eqb_eq in hd0; subst d.
      apply (stateHalts_of_stepStar hh eq_refl).
      rewrite hR; unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1].
      assert (heq : 0 :: decLState (LS_clean z0 segs bot) =
                    decLState (LS_clean (z0 + 1) segs bot)).
      { cbn [decLState]; rewrite (rep0_succ z0); reflexivity. }
      rewrite <- heq.
      exact (pev (rule_BR_zero (decLState (LS_clean z0 segs bot)) (decR R2))).
    + apply N.eqb_neq in hd0.
      destruct (d =? 1) eqn:hd1.
      * apply N.eqb_eq in hd1; subst d.
        apply (stateHalts_of_stepStar hh eq_refl).
        rewrite hR; unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1].
        rewrite decR_bumpR.
        exact (pev (rule_BR_one (decLState (LS_clean z0 segs bot)) (decR R2))).
      * apply N.eqb_neq in hd1.
        destruct (3 <=? z0) eqn:hz3.
        -- apply N.leb_le in hz3.
           apply (stateHalts_of_stepStar hh eq_refl).
           rewrite hR; replace d with ((d - 2) + 2) at 1 by lia.
           pose proof (pev (rule_BR_add_two (d - 2) (decLState (LS_clean z0 segs bot)) (decR R2))) as hstep.
           assert (heq : bumpHead (decLState (LS_clean z0 segs bot)) =
                         decLState (LS_clean 0 (pushSeg (z0 - 3) 1 segs) bot)).
           { cbn [decLState]; rewrite decSegs_pushSeg, repBlock_1; unfold blkL.
             replace z0 with ((z0 - 3 + 2) + 1) at 1 by lia.
             rewrite (rep0_succ (z0 - 3 + 2)), <- !app_assoc; reflexivity. }
           rewrite heq in hstep.
           unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1]; rewrite decR_pushRd.
           exact hstep.
        -- apply (stateHalts_of_stepStar hh eq_refl).
           unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
           rewrite decL_unpackClean; apply evstep_refl.
  - destruct ((1 <=? m) && (1 <=? z0) && (3 <=? r + z0)) eqn:hb.
    + apply andb_true_iff in hb; destruct hb as [hb hrz].
      apply andb_true_iff in hb; destruct hb as [hm hz0].
      apply N.leb_le in hm; apply N.leb_le in hz0; apply N.leb_le in hrz.
      apply (stateHalts_of_stepStar hh eq_refl).
      assert (heqL0 : decLState (LS_clean z0 segs bot) =
                      0 :: (rep0 (z0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)))).
      { cbn [decLState]; replace z0 with ((z0 - 1) + 1) at 1 by lia.
        rewrite (rep0_succ (z0 - 1)); reflexivity. }
      pose proof (rule_BR_blkR_succ (m - 1) r (rep0 (z0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) (decR R1)) as hstep.
      assert (heqR : decR (IT_k r m :: R1) = repBlock (blkR r) ((m - 1) + 1) ++ decR R1).
      { cbn [decR]; replace ((m - 1) + 1) with m by lia; reflexivity. }
      assert (heqL1 : rep0 3 ++ 1 :: (repBlock (blkL r) (m - 1) ++ (rep0 r ++ (rep0 (z0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))))) =
                      decLState (LS_clean 3 (pushSeg r (m - 1) (pushSeg (r + z0 - 3) 1 segs)) bot)).
      { assert (hmerge : rep0 r ++ (rep0 (z0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
                         rep0 (r + z0 - 3 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))).
        { rewrite app_assoc, <- (rep0_add r (z0 - 1)).
          replace (r + (z0 - 1)) with (r + z0 - 3 + 2) by lia; reflexivity. }
        rewrite hmerge; cbn [decLState]; rewrite !decSegs_pushSeg, repBlock_1; unfold blkL.
        rewrite <- !app_assoc; reflexivity. }
      unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1].
      rewrite heqL0, heqR, <- heqL1; exact hstep.
    + apply (stateHalts_of_stepStar hh eq_refl).
      unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
      rewrite decL_unpackClean; apply evstep_refl.
Qed.

(* 5.7 Clean DR0 *)
Definition stepCleanDR0 (z0 : N) (segs : list (N * N)) (bot : N) (R : list Item) : RleFullState :=
  if 1 <=? bot then
    match R with
    | IT_d v1 :: IT_z rz :: R2 =>
      if v1 =? 1 then
        let q := minN rz bot in
        if 1 <=? q then
          let Rnew := if rz =? q then IT_d 1 :: R2 else IT_d 1 :: IT_z (rz - q) :: R2 in
          mkRleState SM_DR0 (LS_clean (z0 + 4 * q) segs (bot - q)) Rnew false
        else mkRleState SM_BR (LS_clean (z0 + 4) segs (bot - 1)) R false
      else mkRleState SM_BR (LS_clean (z0 + 4) segs (bot - 1)) R false
    | _ => mkRleState SM_BR (LS_clean (z0 + 4) segs (bot - 1)) R false
    end
  else mkRleState SM_DR0 (LS_raw (unpackClean z0 segs bot)) R false.

Lemma stepCleanDR0_halts (z0 : N) (segs : list (N * N)) (bot : N) (R : list Item)
  (hh : StateHalts (stepCleanDR0 z0 segs bot R)) :
  halts tm (cfg_DR0 (decLState (LS_clean z0 segs bot)) (decR R)).
Proof.
  unfold stepCleanDR0 in hh.
  destruct (1 <=? bot) eqn:hbot.
  - apply N.leb_le in hbot.
    assert (h_one : StateHalts (mkRleState SM_BR (LS_clean (z0 + 4) segs (bot - 1)) R false) ->
                    halts tm (cfg_DR0 (decLState (LS_clean z0 segs bot)) (decR R))).
    { intros hh1.
      apply (stateHalts_of_stepStar hh1 eq_refl).
      pose proof (clean_DR0_one z0 segs (bot - 1) (decR R)) as hstep.
      replace (bot - 1 + 1) with bot in hstep by lia.
      exact hstep. }
    destruct R as [| [? | v1 | ? ?] [| [rz | ? | ? ?] R2]]; try exact (h_one hh).
    destruct (v1 =? 1) eqn:hv1; [| exact (h_one hh)].
    apply N.eqb_eq in hv1; subst v1.
    destruct (1 <=? minN rz bot) eqn:hq1; [| exact (h_one hh)].
    set (q := minN rz bot) in *.
    assert (hqrz : q <= rz) by apply minN_le_l.
    assert (hqbot : q <= bot) by apply minN_le_r.
    apply (stateHalts_of_stepStar hh eq_refl).
    pose proof (clean_DR0_zeros q z0 segs (bot - q) (rep0 (rz - q) ++ decR R2)) as hstep.
    replace (bot - q + q) with bot in hstep by lia.
    assert (heqR1 : 1 :: (rep0 q ++ (rep0 (rz - q) ++ decR R2)) =
                    decR (IT_d 1 :: IT_z rz :: R2)).
    { rewrite app_assoc, <- (rep0_add q (rz - q)); replace (q + (rz - q)) with rz by lia; reflexivity. }
    assert (heqR2 : 1 :: (rep0 (rz - q) ++ decR R2) =
                    decR (if rz =? q then IT_d 1 :: R2 else IT_d 1 :: IT_z (rz - q) :: R2)).
    { destruct (rz =? q) eqn:heq.
      - apply N.eqb_eq in heq; rewrite heq, N.sub_diag; reflexivity.
      - reflexivity. }
    rewrite heqR1, heqR2 in hstep; exact hstep.
  - apply (stateHalts_of_stepStar hh eq_refl).
    unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
    rewrite decL_unpackClean; apply evstep_refl.
Qed.

(* 5.8 Top-Level Dispatch `rleStep` *)
Definition tryPack (m : StackMode) (items R : list Item) : option LState :=
  if modeCanPack m items R then
    match packHead 0 items with
    | Some (LS_clean z0 segs bot) =>
      if 1 <=? bot then Some (LS_clean z0 segs bot) else None
    | _ => None
    end
  else None.

Lemma tryPack_spec (m : StackMode) (items R : list Item) (ls' : LState)
  (h : tryPack m items R = Some ls') : decL items = decLState ls'.
Proof.
  unfold tryPack in h.
  destruct (modeCanPack m items R); [| discriminate].
  destruct (packHead 0 items) as [[? | z0 segs bot] |] eqn:hph; try discriminate.
  destruct (1 <=? bot); [| discriminate].
  injection h as <-.
  pose proof (packHead_spec items 0 (LS_clean z0 segs bot) hph) as hspec.
  exact hspec.
Qed.

Definition rleStep (s : RleFullState) : RleFullState :=
  match rle_ls s with
  | LS_raw items =>
    match tryPack (rle_mode s) items (rle_R s) with
    | Some ls' => mkRleState (rle_mode s) ls' (rle_R s) false
    | None =>
      match rle_mode s with
      | SM_B => stepRawB items (rle_R s)
      | SM_BR => stepRawBR items (rle_R s)
      | SM_DR0 => stepRawDR0 items (rle_R s)
      | SM_C => stepRawC items (rle_R s)
      end
    end
  | LS_clean z0 segs bot =>
    match rle_mode s with
    | SM_B => stepCleanB z0 segs bot (rle_R s)
    | SM_BR => stepCleanBR z0 segs bot (rle_R s)
    | SM_DR0 => stepCleanDR0 z0 segs bot (rle_R s)
    | SM_C => mkRleState SM_C (LS_raw (unpackClean z0 segs bot)) (rle_R s) false
    end
  end.

Lemma rleStep_halts (s : RleFullState) (hh : StateHalts (rleStep s)) :
  halts tm (evalRle s).
Proof.
  destruct s as [mode [items | z0 segs bot] R halted];
    cbn [rleStep rle_ls rle_mode rle_R] in hh.
  - destruct (tryPack mode items R) as [ls' |] eqn:hpk.
    + apply (stateHalts_of_stepStar hh eq_refl).
      unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
      rewrite (tryPack_spec mode items R ls' hpk).
      apply evstep_refl.
    + destruct mode; unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1 decLState].
      * exact (stepRawBR_halts items R hh).
      * exact (stepRawC_halts items R hh).
      * exact (stepRawB_halts items R hh).
      * exact (stepRawDR0_halts items R hh).
  - destruct mode; unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1].
    + exact (stepCleanBR_halts z0 segs bot R hh).
    + apply (stateHalts_of_stepStar hh eq_refl).
      unfold evalRle; cbn [rle_mode rle_ls rle_R evalStackCfg1].
      change (decLState (LS_raw (unpackClean z0 segs bot)))
        with (decL (unpackClean z0 segs bot)).
      rewrite decL_unpackClean; apply evstep_refl.
    + exact (stepCleanB_halts z0 segs bot R hh).
    + exact (stepCleanDR0_halts z0 segs bot R hh).
Qed.

(* ========================================================================== *)
(* Section 6: VM Trajectory Evaluation (`19 * 500 = 9,500 > 9,101`) & `halt`  *)
(* ========================================================================== *)

Fixpoint runChunkOpt (fuel : nat) (s : RleFullState) : option RleFullState :=
  if rle_halted s then None
  else match fuel with
  | 0%nat => Some s
  | S fuel' => runChunkOpt fuel' (rleStep s)
  end.

Lemma runChunkOpt_none_halts (fuel : nat) : forall (s : RleFullState),
  runChunkOpt fuel s = None -> StateHalts s.
Proof.
  induction fuel as [| fuel' ih]; intros s h; cbn [runChunkOpt] in h.
  - destruct (rle_halted s) eqn:hh; [left; exact hh | discriminate].
  - destruct (rle_halted s) eqn:hh.
    + left; exact hh.
    + right; exact (rleStep_halts s (ih (rleStep s) h)).
Qed.

Lemma runChunkOpt_some_halts (fuel : nat) : forall (s s' : RleFullState),
  runChunkOpt fuel s = Some s' -> StateHalts s' -> StateHalts s.
Proof.
  induction fuel as [| fuel' ih]; intros s s' h hs'; cbn [runChunkOpt] in h.
  - destruct (rle_halted s); [discriminate | injection h as <-; exact hs'].
  - destruct (rle_halted s) eqn:hh; [discriminate |].
    right; exact (rleStep_halts s (ih (rleStep s) s' h hs')).
Qed.

Fixpoint runChunks (chunks fuel : nat) (s : RleFullState) : bool :=
  match chunks with
  | 0%nat => rle_halted s
  | S chunks' =>
    match runChunkOpt fuel s with
    | None => true
    | Some s' => runChunks chunks' fuel s'
    end
  end.

Lemma runChunks_halts (chunks fuel : nat) : forall (s : RleFullState),
  runChunks chunks fuel s = true -> StateHalts s.
Proof.
  induction chunks as [| chunks' ih]; intros s h; cbn [runChunks] in h.
  - left; exact h.
  - destruct (runChunkOpt fuel s) as [s' |] eqn:hc.
    + exact (runChunkOpt_some_halts fuel s s' hc (ih s' h)).
    + exact (runChunkOpt_none_halts fuel s hc).
Qed.

Definition ckpt0 : RleFullState := mkRleState SM_B (LS_raw [IT_z 1]) [] false.

Lemma run_ckpt0 : runChunks 19%nat 500%nat ckpt0 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma reach_0 : StateHalts ckpt0.
Proof.
  exact (runChunks_halts 19%nat 500%nat ckpt0 run_ckpt0).
Qed.

Lemma halt : halts tm c0.
Proof.
  destruct reach_0 as [hfalse | hcan]; [discriminate |].
  eapply halts_evstep; [exact hcan | exact (pev init_reaches_stack)].
Qed.
