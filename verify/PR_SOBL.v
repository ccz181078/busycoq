(* Classification: SOBL. Source: BusyCoq PR #35,
   commit 0913bd4fc552cc8213e7ecd9d39a224663a1481d.
   Original proof bodies preserved; local packaging only. *)

(* 1RB0RC_1RC0LD_1LD1RA_1LF0LE_---0RD_1LB0LA halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat ZifyN NArith PeanoNat Bool String Lists.Streams List.
Import ListNotations.

Open Scope list.
Open Scope sym.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC0LD_1LD1RA_1LF0LE_---0RD_1LB0LA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope N_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ========================================================================== *)
(* Section 0: Generic Helpers (N, replicate, iter, step compositions)         *)
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

Fixpoint iter {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | 0%nat => x
  | S n' => iter f n' (f x)
  end.

Lemma iter_succ_r {A : Type} (f : A -> A) (n : nat) (x : A) :
  iter f (S n) x = f (iter f n x).
Proof.
  revert x.
  induction n as [| n' ih]; intros x; simpl; [reflexivity | rewrite <- ih; reflexivity].
Qed.

Lemma iter_add {A : Type} (f : A -> A) (m n : nat) (x : A) :
  iter f (m + n)%nat x = iter f m (iter f n x).
Proof.
  revert x.
  induction m as [| m' ih]; intros x; simpl; [reflexivity |].
  rewrite ih, <- iter_succ_r; reflexivity.
Qed.

Definition niter {A : Type} (f : A -> A) (n : N) (x : A) : A :=
  iter f (N.to_nat n) x.

Lemma niter_0 {A : Type} (f : A -> A) (x : A) : niter f 0 x = x.
Proof. reflexivity. Qed.

Lemma niter_succ_l {A : Type} (f : A -> A) (n : N) (x : A) :
  niter f (n + 1) x = niter f n (f x).
Proof.
  unfold niter.
  replace (N.to_nat (n + 1)) with (S (N.to_nat n)) by lia.
  reflexivity.
Qed.

Lemma niter_succ_r {A : Type} (f : A -> A) (n : N) (x : A) :
  niter f (n + 1) x = f (niter f n x).
Proof.
  unfold niter.
  replace (N.to_nat (n + 1)) with (S (N.to_nat n)) by lia.
  apply iter_succ_r.
Qed.

Lemma niter_add {A : Type} (f : A -> A) (m n : N) (x : A) :
  niter f (m + n) x = niter f m (niter f n x).
Proof.
  unfold niter.
  rewrite N2Nat.inj_add.
  apply iter_add.
Qed.

(* ========================================================================== *)
(* Section 1: 2nd-Order Digit-Stack Encodings & 16 Local Separator Rules      *)
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

Lemma encLeft_two (L : list N) :
  encLeft1 (2 :: L) = 1%sym >> 1%sym >> 1%sym >> 0%sym >> encLeft1 L.
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

Lemma encLeft_add_two (b : N) (L : list N) :
  encLeft1 ((b + 2) :: L) = 1%sym >> 1%sym >> encLeft1 (b :: L).
Proof.
  unfold encLeft1; fold encLeft1.
  replace (N.to_nat (b + 2)) with (S (S (N.to_nat b))) by lia.
  reflexivity.
Qed.

Lemma encLeft_add_three (a : N) (L : list N) :
  encLeft1 ((a + 3) :: L) = 1%sym >> 1%sym >> 1%sym >> encLeft1 (a :: L).
Proof.
  unfold encLeft1; fold encLeft1.
  replace (N.to_nat (a + 3)) with (S (S (S (N.to_nat a)))) by lia.
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

Definition cfg_F (L R : list N) : Q * tape :=
  F;; encLeft1 L {{0%sym}} encRight1 R.

Definition cfg_AR (L R : list N) : Q * tape :=
  encLeft1 L {{A}}> encRight1 R.

Inductive StackMode : Type :=
  | SM_F
  | SM_AR.

Definition evalStackCfg (mode : StackMode) (L R : list N) : Q * tape :=
  match mode with
  | SM_F => cfg_F L R
  | SM_AR => cfg_AR L R
  end.

(* Mode F Rules (8 Rules) *)

Lemma rule_F_nil (R : list N) :
  cfg_F [] R -->+ cfg_AR [1] R.
Proof.
  unfold cfg_F, cfg_AR; simpl; start_progress.
Qed.

Lemma rule_F_zero_nil (R : list N) :
  cfg_F [0] R -->+ cfg_F [] (0 :: bumpHead R).
Proof.
  unfold cfg_F; rewrite encLeft_zero, encRight_zero, <- encRight_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_F_zero_zero (L R : list N) :
  cfg_F (0 :: 0 :: L) R -->+ cfg_F (bumpHead (bumpHead L)) (0 :: R).
Proof.
  unfold cfg_F.
  rewrite (encLeft_zero (0 :: L)), (encLeft_zero L), encRight_zero.
  rewrite <- !encLeft_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_F_zero_one (L R : list N) :
  cfg_F (0 :: 1 :: L) R -->+ cfg_F L (2 :: bumpHead R).
Proof.
  unfold cfg_F.
  rewrite (encLeft_zero (1 :: L)), (encLeft_one L), encRight_two, <- encRight_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_F_zero_add_two (L R : list N) (b : N) :
  cfg_F (0 :: (b + 2) :: L) R -->+ cfg_AR (b :: L) (0 :: 0 :: bumpHead R).
Proof.
  unfold cfg_F, cfg_AR.
  rewrite (encLeft_zero ((b + 2) :: L)), encLeft_add_two, encLeft_cons_tail.
  rewrite (encRight_zero (0 :: bumpHead R)), (encRight_zero (bumpHead R)), <- encRight_cons_one.
  simpl; start_progress.
Qed.

Definition cfg_Halt_F (L R : list N) : Q * tape :=
  E;; encLeft1 L {{0%sym}} (0%sym >> 0%sym >> encRight1 (bumpHead R)).

Lemma rule_F_one (L R : list N) :
  cfg_F (1 :: L) R -->+ cfg_Halt_F L R.
Proof.
  unfold cfg_F, cfg_Halt_F.
  rewrite encLeft_one, <- encRight_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_F_one_halt (L R : list N) :
  halts tm (cfg_F (1 :: L) R).
Proof.
  eapply halts_evstep; [| apply pev, rule_F_one].
  apply halted_halts. reflexivity.
Qed.

Lemma rule_F_two (L R : list N) :
  cfg_F (2 :: L) R -->+ cfg_AR (bumpHead (bumpHead L)) (0 :: bumpHead R).
Proof.
  unfold cfg_F, cfg_AR.
  rewrite encLeft_two, encRight_zero, <- !encLeft_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_F_add_three (L R : list N) (a : N) :
  cfg_F ((a + 3) :: L) R -->+ cfg_F (a :: L) (0 :: bumpHead R).
Proof.
  unfold cfg_F.
  rewrite encLeft_add_three, encLeft_cons_tail, encRight_zero, <- encRight_cons_one.
  simpl; start_progress.
Qed.

(* Mode AR Rules (8 Rules) *)

Lemma rule_AR_nil (L : list N) :
  cfg_AR L [] -->+ cfg_F L [1].
Proof.
  unfold cfg_AR, cfg_F; simpl; start_progress.
Qed.

Lemma rule_AR_nil_zero (R : list N) :
  cfg_AR [] (0 :: R) -->+ cfg_F [] (bumpHead (bumpHead R)).
Proof.
  unfold cfg_AR, cfg_F.
  rewrite encRight_zero, <- !encRight_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_AR_zero_zero (L R : list N) :
  cfg_AR (0 :: L) (0 :: R) -->+
  cfg_AR (bumpHead (bumpHead (bumpHead L))) (bumpHead R).
Proof.
  unfold cfg_AR.
  rewrite encLeft_zero, encRight_zero, <- !encLeft_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_AR_one_zero (L R : list N) :
  cfg_AR (1 :: L) (0 :: R) -->+
  cfg_F L (bumpHead (bumpHead (bumpHead (bumpHead R)))).
Proof.
  unfold cfg_AR, cfg_F.
  rewrite encLeft_one, encRight_zero, <- !encRight_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_AR_add_two_zero (L R : list N) (a : N) :
  cfg_AR ((a + 2) :: L) (0 :: R) -->+
  cfg_AR (a :: L) (0 :: bumpHead (bumpHead R)).
Proof.
  unfold cfg_AR.
  rewrite encLeft_add_two, encLeft_cons_tail, (encRight_zero R),
          (encRight_zero (bumpHead (bumpHead R))), <- !encRight_cons_one.
  simpl; start_progress.
Qed.

Lemma rule_AR_one_nil (L : list N) :
  cfg_AR L [1] -->+ cfg_AR (0 :: L) [].
Proof.
  unfold cfg_AR; simpl; start_progress.
Qed.

Lemma rule_AR_one_cons (L R : list N) (e : N) :
  cfg_AR L (1 :: e :: R) -->+ cfg_AR L (0 :: (e + 1) :: R).
Proof.
  unfold cfg_AR.
  rewrite (encRight_one (e :: R)), (encRight_zero ((e + 1) :: R)),
          encRight_add_one, encRight_cons_tail.
  simpl; start_progress.
Qed.

Lemma rule_AR_add_two (L R : list N) (d : N) :
  cfg_AR L ((d + 2) :: R) -->+ cfg_AR (0 :: L) (d :: R).
Proof.
  unfold cfg_AR.
  rewrite encLeft_zero, encRight_add_two, encRight_cons_tail.
  simpl; start_progress.
Qed.

(* ========================================================================== *)
(* Section 2: Multi-Step Bulk Contractions on `list N`                        *)
(* ========================================================================== *)

Lemma bumpHead_iterate_cons (k v : N) (L : list N) :
  niter bumpHead k (v :: L) = (v + k) :: L.
Proof.
  revert v.
  induction k using N_peano_ind; intros v.
  - rewrite niter_0, N.add_0_r; reflexivity.
  - rewrite niter_succ_l; simpl bumpHead.
    rewrite IHk.
    replace (v + 1 + k) with (v + (k + 1)) by lia; reflexivity.
Qed.

Lemma bumpHead_iterate_nil (k : N) :
  niter bumpHead (k + 1) [] = [k].
Proof.
  rewrite niter_succ_l; simpl bumpHead.
  rewrite bumpHead_iterate_cons, N.add_0_l; reflexivity.
Qed.

Lemma bumpHead2_iterate_eq (k : N) (R : list N) :
  niter (fun R0 => bumpHead (bumpHead R0)) k R = niter bumpHead (2 * k) R.
Proof.
  revert R.
  induction k using N_peano_ind; intros R.
  - reflexivity.
  - replace (2 * (k + 1)) with (2 + 2 * k) by lia.
    rewrite niter_succ_r, IHk, niter_add; reflexivity.
Qed.

Definition stepF3Right (k : N) (R : list N) : list N :=
  niter (fun R0 => 0 :: bumpHead R0) k R.

Lemma stepF3Right_0 (R : list N) : stepF3Right 0 R = R.
Proof. reflexivity. Qed.

Lemma stepF3Right_step (k : N) (R : list N) :
  stepF3Right (k + 1) R = stepF3Right k (0 :: bumpHead R).
Proof. exact (niter_succ_l (fun R0 => 0 :: bumpHead R0) k R). Qed.

Lemma stepF3Right_succ (k : N) (R : list N) :
  stepF3Right (k + 1) R = 0 :: (nreplicate k 1 ++ bumpHead R).
Proof.
  revert R.
  induction k using N_peano_ind; intros R.
  - reflexivity.
  - rewrite stepF3Right_step, IHk; simpl bumpHead.
    rewrite nreplicate_succ_r, <- app_assoc; reflexivity.
Qed.

Lemma rule_F_step3_all (L R : list N) (a k : N) :
  cfg_F ((3 * k + a) :: L) R -->* cfg_F (a :: L) (stepF3Right k R).
Proof.
  revert R.
  induction k using N_peano_ind; intros R.
  - replace (3 * 0 + a) with a by lia; apply evstep_refl.
  - replace (3 * (k + 1) + a) with ((3 * k + a) + 3) by lia.
    rewrite stepF3Right_step.
    eapply etrans; [apply pev, rule_F_add_three | apply IHk].
Qed.

Lemma rule_AR_step2_all (L R : list N) (d k : N) :
  cfg_AR L ((2 * k + d) :: R) -->* cfg_AR (nreplicate k 0 ++ L) (d :: R).
Proof.
  revert L.
  induction k using N_peano_ind; intros L.
  - replace (2 * 0 + d) with d by lia; apply evstep_refl.
  - replace (2 * (k + 1) + d) with ((2 * k + d) + 2) by lia.
    rewrite nreplicate_succ_r, <- app_assoc; simpl app.
    eapply etrans; [apply pev, rule_AR_add_two | apply IHk].
Qed.

Lemma rule_AR_add_two_zero_all (L R : list N) (a k : N) :
  cfg_AR ((2 * k + a) :: L) (0 :: R) -->*
  cfg_AR (a :: L) (0 :: niter (fun R0 => bumpHead (bumpHead R0)) k R).
Proof.
  revert R.
  induction k using N_peano_ind; intros R.
  - replace (2 * 0 + a) with a by lia; apply evstep_refl.
  - replace (2 * (k + 1) + a) with ((2 * k + a) + 2) by lia.
    rewrite (niter_succ_l (fun R0 => bumpHead (bumpHead R0)) k R).
    eapply etrans; [apply pev, rule_AR_add_two_zero | apply IHk].
Qed.

Lemma rule_F_zero4_one (L : list N) (d : N) (R : list N) :
  cfg_F (0 :: 0 :: 0 :: 0 :: 0 :: L) (0 :: d :: R) -->*
  cfg_F (0 :: L) (0 :: (d + 8) :: R).
Proof.
  eapply etrans; [apply pev, (rule_F_zero_zero (0 :: 0 :: 0 :: L) (0 :: d :: R)) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_F_two (0 :: 0 :: L) (0 :: 0 :: d :: R)) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: L) (1 :: 0 :: d :: R) 0) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_zero_zero (0 :: L) (3 :: 0 :: d :: R)) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two (3 :: L) (0 :: d :: R) 2) |].
  eapply etrans; [apply pev, (rule_AR_add_two (0 :: 3 :: L) (0 :: d :: R) 0) |].
  eapply etrans; [apply pev, (rule_AR_zero_zero (0 :: 3 :: L) (0 :: d :: R)) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_one_cons (3 :: 3 :: L) R d) |].
  eapply etrans; [apply pev, (rule_AR_add_two_zero (3 :: L) ((d + 1) :: R) 1) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_one_zero (3 :: L) ((d + 1 + 1 + 1) :: R)) |].
  simpl bumpHead.
  replace (d + 1 + 1 + 1 + 1 + 1 + 1 + 1) with (d + 7) by lia.
  eapply etrans; [apply pev, (rule_F_add_three L ((d + 7) :: R) 0) |].
  simpl bumpHead.
  replace (d + 7 + 1) with (d + 8) by lia.
  apply evstep_refl.
Qed.

Lemma rule_F_zero4_all (k r : N) (L : list N) (d : N) (R : list N) :
  cfg_F (nreplicate (4 * k + r + 1) 0 ++ L) (0 :: d :: R) -->*
  cfg_F (nreplicate (r + 1) 0 ++ L) (0 :: (d + 8 * k) :: R).
Proof.
  revert d.
  induction k using N_peano_ind; intros d.
  - replace (4 * 0 + r + 1) with (r + 1) by lia.
    replace (d + 8 * 0) with d by lia.
    apply evstep_refl.
  - replace (4 * (k + 1) + r + 1) with (5 + (4 * k + r)) by lia.
    rewrite nreplicate_add, <- app_assoc.
    change (nreplicate 5 0) with [0; 0; 0; 0; 0]; cbn [app].
    eapply etrans; [apply rule_F_zero4_one |].
    replace (0 :: (nreplicate (4 * k + r) 0 ++ L)) with
      (nreplicate (4 * k + r + 1) 0 ++ L)
      by (replace (4 * k + r + 1) with ((4 * k + r) + 1) by lia;
          rewrite nreplicate_succ; reflexivity).
    replace (d + 8 * (k + 1)) with ((d + 8) + 8 * k) by lia.
    apply IHk.
Qed.

Lemma rule_AR_zero_ones_all (m b : N) (L R : list N) :
  cfg_AR (0 :: b :: L) (0 :: (nreplicate m 1 ++ R)) -->*
  cfg_AR (0 :: (b + 3 * m) :: L) (0 :: R).
Proof.
  revert b.
  induction m using N_peano_ind; intros b.
  - replace (b + 3 * 0) with b by lia; apply evstep_refl.
  - rewrite nreplicate_succ; simpl app.
    eapply etrans; [apply pev, (rule_AR_zero_zero (b :: L) (1 :: (nreplicate m 1 ++ R))) |].
    simpl bumpHead.
    replace (b + 1 + 1 + 1) with (b + 3) by lia.
    eapply etrans; [apply pev, (rule_AR_add_two ((b + 3) :: L) (nreplicate m 1 ++ R) 0) |].
    replace (b + 3 * (m + 1)) with ((b + 3) + 3 * m) by lia.
    apply IHm.
Qed.

Lemma rule_AR_ones_all (m b : N) (L R : list N) :
  cfg_AR (0 :: b :: L) (nreplicate (m + 1) 1 ++ R) -->*
  cfg_AR (0 :: (b + 3 * m) :: L) (1 :: R).
Proof.
  revert b.
  induction m using N_peano_ind; intros b.
  - replace (b + 3 * 0) with b by lia; apply evstep_refl.
  - replace (m + 1 + 1) with (2 + m) by lia.
    rewrite nreplicate_add, <- app_assoc.
    change (nreplicate 2 1) with [1; 1]; cbn [app].
    eapply etrans; [apply pev, (rule_AR_one_cons (0 :: b :: L) (nreplicate m 1 ++ R) 1) |].
    eapply etrans; [apply pev, (rule_AR_zero_zero (b :: L) (2 :: (nreplicate m 1 ++ R))) |].
    simpl bumpHead.
    replace (b + 1 + 1 + 1) with (b + 3) by lia.
    eapply etrans; [apply pev, (rule_AR_add_two ((b + 3) :: L) (nreplicate m 1 ++ R) 1) |].
    replace (1 :: (nreplicate m 1 ++ R)) with (nreplicate (m + 1) 1 ++ R)
      by (rewrite nreplicate_succ; reflexivity).
    replace (b + 3 * (m + 1)) with ((b + 3) + 3 * m) by lia.
    apply IHm.
Qed.

(* ========================================================================== *)
(* Section 3: 6-Rule Inductive Tower Algebra                                  *)
(* ========================================================================== *)

Definition A3 (k : N) (tail : list N) : list N :=
  6 :: 0 :: 0 :: 0 :: (3 * k + 3) :: 3 :: 0 :: tail.

Definition A0 (k : N) (tail : list N) : list N :=
  6 :: 0 :: 0 :: 0 :: (3 * k + 3) :: 0 :: 0 :: 0 :: tail.

Definition B3 (k : N) (tail : list N) : list N :=
  0 :: 3 :: 3 :: 0 :: 0 :: (3 * k + 3) :: 3 :: 0 :: tail.

Definition B0 (k : N) (tail : list N) : list N :=
  0 :: 3 :: 3 :: 0 :: 0 :: (3 * k + 3) :: 0 :: 0 :: 0 :: tail.

Definition SubStep (St St' : list N) : Prop :=
  forall R_bot : list N,
    cfg_F (0 :: St) (9 :: R_bot) -->*
    cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: St') (0 :: R_bot).

Definition TopStep (St St' : list N) : Prop :=
  cfg_F (0 :: St) [5] -->* cfg_F (0 :: St') [5].

Definition SubHalt (St : list N) : Prop :=
  forall R_bot : list N,
    halts tm (cfg_F (0 :: St) (9 :: R_bot)).

Lemma topStep_refl (St : list N) : TopStep St St.
Proof. apply evstep_refl. Qed.

Lemma topStep_trans {St1 St2 St3 : list N} (h1 : TopStep St1 St2) (h2 : TopStep St2 St3) :
  TopStep St1 St3.
Proof. exact (etrans h1 h2). Qed.

Lemma exit_sub (W R_bot : list N) :
  cfg_AR W (10 :: R_bot) -->* cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: W) (0 :: R_bot).
Proof.
  exact (rule_AR_step2_all W R_bot 0 5).
Qed.

Lemma exit_top (W : list N) :
  cfg_AR W [6] -->* cfg_F (0 :: W) [5].
Proof.
  eapply etrans; [apply (rule_AR_step2_all W [] 0 3) |].
  change (nreplicate 3 0 ++ W) with (0 :: 0 :: 0 :: W).
  eapply etrans; [apply pev, (rule_AR_zero_zero (0 :: 0 :: W) []) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: W) [] 1) |].
  simpl bumpHead.
  apply pev, (rule_AR_one_zero (0 :: W) [1]).
Qed.

Lemma subStep_A_any (U : list N) :
  SubStep (6 :: 0 :: 0 :: 0 :: U) (0 :: 3 :: 3 :: 0 :: 0 :: U).
Proof.
  intros R_bot.
  eapply etrans; [apply pev, (rule_F_zero_add_two (0 :: 0 :: 0 :: U) (9 :: R_bot) 4) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: 0 :: 0 :: U) (0 :: 10 :: R_bot) 2) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: 0 :: 0 :: U) (2 :: 10 :: R_bot) 0) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_zero_zero (0 :: 0 :: 0 :: U) (4 :: 10 :: R_bot)) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two (3 :: 0 :: 0 :: U) (10 :: R_bot) 3) |].
  eapply etrans; [apply pev, (rule_AR_add_two (0 :: 3 :: 0 :: 0 :: U) (10 :: R_bot) 1) |].
  eapply etrans; [apply pev, (rule_AR_one_cons (0 :: 0 :: 3 :: 0 :: 0 :: U) R_bot 10) |].
  eapply etrans; [apply pev, (rule_AR_zero_zero (0 :: 3 :: 0 :: 0 :: U) (11 :: R_bot)) |].
  simpl bumpHead.
  exact (rule_AR_step2_all (3 :: 3 :: 0 :: 0 :: U) R_bot 0 6).
Qed.

Lemma subStep_A3 (k : N) (tail : list N) : SubStep (A3 k tail) (B3 k tail).
Proof. exact (subStep_A_any ((3 * k + 3) :: 3 :: 0 :: tail)). Qed.

Lemma subStep_A0 (k : N) (tail : list N) : SubStep (A0 k tail) (B0 k tail).
Proof. exact (subStep_A_any ((3 * k + 3) :: 0 :: 0 :: 0 :: tail)). Qed.

Lemma top_A_to_B (U : list N) :
  cfg_F (0 :: 6 :: 0 :: 0 :: 0 :: U) [5] -->*
  cfg_F (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [5].
Proof.
  eapply etrans; [apply pev, (rule_F_zero_add_two (0 :: 0 :: 0 :: U) [5] 4) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: 0 :: 0 :: U) [0; 6] 2) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: 0 :: 0 :: U) [2; 6] 0) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_zero_zero (0 :: 0 :: 0 :: U) [4; 6]) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two (3 :: 0 :: 0 :: U) [6] 3) |].
  eapply etrans; [apply pev, (rule_AR_add_two (0 :: 3 :: 0 :: 0 :: U) [6] 1) |].
  eapply etrans; [apply pev, (rule_AR_one_cons (0 :: 0 :: 3 :: 0 :: 0 :: U) [] 6) |].
  eapply etrans; [apply pev, (rule_AR_zero_zero (0 :: 3 :: 0 :: 0 :: U) [7]) |].
  simpl bumpHead.
  eapply etrans; [apply (rule_AR_step2_all (3 :: 3 :: 0 :: 0 :: U) [] 0 4) |].
  change (nreplicate 4 0 ++ (3 :: 3 :: 0 :: 0 :: U)) with
    (0 :: 0 :: 0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U).
  eapply etrans; [apply pev, (rule_AR_zero_zero (0 :: 0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) []) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [] 1) |].
  simpl bumpHead.
  apply pev, (rule_AR_one_zero (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [1]).
Qed.

Lemma step_B_prefix (V : list N) (d0 : N) (R_rest : list N) :
  cfg_F (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: V) (d0 :: R_rest) -->*
  cfg_F (0 :: 0 :: V) (9 :: 1 :: d0 :: R_rest).
Proof.
  eapply etrans; [apply pev, (rule_F_zero_zero (3 :: 3 :: 0 :: 0 :: V) (d0 :: R_rest)) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_F_add_three (3 :: 0 :: 0 :: V) (0 :: d0 :: R_rest) 2) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_F_two (3 :: 0 :: 0 :: V) (0 :: 1 :: d0 :: R_rest)) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: 0 :: V) (1 :: 1 :: d0 :: R_rest) 3) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: 0 :: V) (3 :: 1 :: d0 :: R_rest) 1) |].
  simpl bumpHead.
  apply pev, (rule_AR_one_zero (0 :: 0 :: V) (5 :: 1 :: d0 :: R_rest)).
Qed.

Lemma step_B0_core (k : N) (tail : list N) (d0 : N) (R_rest : list N) :
  cfg_F (0 :: B0 k tail) (d0 :: R_rest) -->*
  cfg_AR (A3 (k + 1) tail) ((d0 + 1) :: R_rest).
Proof.
  unfold B0.
  eapply etrans; [apply (step_B_prefix ((3 * k + 3) :: 0 :: 0 :: 0 :: tail) d0 R_rest) |].
  eapply etrans; [apply pev, (rule_F_zero_zero ((3 * k + 3) :: 0 :: 0 :: 0 :: tail) (9 :: 1 :: d0 :: R_rest)) |].
  cbn [bumpHead].
  replace (3 * k + 3 + 1 + 1) with (3 * (k + 1) + 2) by lia.
  eapply etrans; [apply (rule_F_step3_all (0 :: 0 :: 0 :: tail) (0 :: 9 :: 1 :: d0 :: R_rest) 2 (k + 1)) |].
  rewrite (stepF3Right_succ k (0 :: 9 :: 1 :: d0 :: R_rest)).
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_F_two (0 :: 0 :: 0 :: tail)
    (0 :: (nreplicate k 1 ++ (1 :: 9 :: 1 :: d0 :: R_rest)))) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: 0 :: tail)
    (1 :: (nreplicate k 1 ++ (1 :: 9 :: 1 :: d0 :: R_rest))) 0) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_zero_zero (0 :: 0 :: tail)
    (3 :: (nreplicate k 1 ++ (1 :: 9 :: 1 :: d0 :: R_rest)))) |].
  simpl bumpHead.
  replace (nreplicate k 1 ++ (1 :: 9 :: 1 :: d0 :: R_rest)) with
    (nreplicate (k + 1) 1 ++ (9 :: 1 :: d0 :: R_rest))
    by (rewrite nreplicate_succ_r, <- app_assoc; reflexivity).
  eapply etrans; [apply (rule_AR_step2_all (3 :: 0 :: tail)
    (nreplicate (k + 1) 1 ++ (9 :: 1 :: d0 :: R_rest)) 0 2) |].
  change (nreplicate 2 0 ++ (3 :: 0 :: tail)) with (0 :: 0 :: 3 :: 0 :: tail).
  eapply etrans; [apply (rule_AR_zero_ones_all (k + 1) 0 (3 :: 0 :: tail) (9 :: 1 :: d0 :: R_rest)) |].
  rewrite N.add_0_l.
  eapply etrans; [apply pev, (rule_AR_zero_zero ((3 * (k + 1)) :: 3 :: 0 :: tail) (9 :: 1 :: d0 :: R_rest)) |].
  cbn [bumpHead].
  replace (3 * (k + 1) + 1 + 1 + 1) with (3 * (k + 1) + 3) by lia.
  eapply etrans; [apply (rule_AR_step2_all ((3 * (k + 1) + 3) :: 3 :: 0 :: tail) (1 :: d0 :: R_rest) 0 5) |].
  change (nreplicate 5 0 ++ ((3 * (k + 1) + 3) :: 3 :: 0 :: tail)) with
    (0 :: 0 :: 0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 3 :: 0 :: tail).
  eapply etrans; [apply (rule_AR_zero_ones_all 1 0
    (0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 3 :: 0 :: tail) (d0 :: R_rest)) |].
  change (0 + 3 * 1) with 3.
  eapply etrans; [apply pev, (rule_AR_zero_zero
    (3 :: 0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 3 :: 0 :: tail) (d0 :: R_rest)) |].
  unfold A3; cbn [bumpHead]; replace (3 + 1 + 1 + 1) with 6 by lia.
  apply evstep_refl.
Qed.

Lemma step_B3_pre (k : N) (tail : list N) (d0 : N) (R_rest : list N) :
  cfg_F (0 :: B3 k tail) (d0 :: R_rest) -->*
  cfg_F (0 :: tail) (9 :: (nreplicate (k + 1) 1 ++ (9 :: 1 :: d0 :: R_rest))).
Proof.
  unfold B3.
  eapply etrans; [apply (step_B_prefix ((3 * k + 3) :: 3 :: 0 :: tail) d0 R_rest) |].
  eapply etrans; [apply pev, (rule_F_zero_zero ((3 * k + 3) :: 3 :: 0 :: tail) (9 :: 1 :: d0 :: R_rest)) |].
  cbn [bumpHead].
  replace (3 * k + 3 + 1 + 1) with (3 * (k + 1) + 2) by lia.
  eapply etrans; [apply (rule_F_step3_all (3 :: 0 :: tail) (0 :: 9 :: 1 :: d0 :: R_rest) 2 (k + 1)) |].
  rewrite (stepF3Right_succ k (0 :: 9 :: 1 :: d0 :: R_rest)).
  simpl bumpHead.
  replace (nreplicate k 1 ++ (1 :: 9 :: 1 :: d0 :: R_rest)) with
    (nreplicate (k + 1) 1 ++ (9 :: 1 :: d0 :: R_rest))
    by (rewrite nreplicate_succ_r, <- app_assoc; reflexivity).
  eapply etrans; [apply pev, (rule_F_two (3 :: 0 :: tail)
    (0 :: (nreplicate (k + 1) 1 ++ (9 :: 1 :: d0 :: R_rest)))) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: tail)
    (1 :: (nreplicate (k + 1) 1 ++ (9 :: 1 :: d0 :: R_rest))) 3) |].
  simpl bumpHead.
  eapply etrans; [apply pev, (rule_AR_add_two_zero (0 :: tail)
    (3 :: (nreplicate (k + 1) 1 ++ (9 :: 1 :: d0 :: R_rest))) 1) |].
  simpl bumpHead.
  apply pev, (rule_AR_one_zero (0 :: tail)
    (5 :: (nreplicate (k + 1) 1 ++ (9 :: 1 :: d0 :: R_rest)))).
Qed.

Lemma step_B3_post (k : N) (tail' : list N) (d0 : N) (R_rest : list N) :
  cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: tail') (0 :: (nreplicate (k + 1) 1 ++ (9 :: 1 :: d0 :: R_rest))) -->*
  cfg_AR (A0 (k + 1) tail') ((d0 + 1) :: R_rest).
Proof.
  eapply etrans; [apply (rule_AR_zero_ones_all (k + 1) 0 (0 :: 0 :: 0 :: tail') (9 :: 1 :: d0 :: R_rest)) |].
  rewrite N.add_0_l.
  eapply etrans; [apply pev, (rule_AR_zero_zero ((3 * (k + 1)) :: 0 :: 0 :: 0 :: tail') (9 :: 1 :: d0 :: R_rest)) |].
  cbn [bumpHead].
  replace (3 * (k + 1) + 1 + 1 + 1) with (3 * (k + 1) + 3) by lia.
  eapply etrans; [apply (rule_AR_step2_all ((3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail') (1 :: d0 :: R_rest) 0 5) |].
  change (nreplicate 5 0 ++ ((3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail')) with
    (0 :: 0 :: 0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail').
  eapply etrans; [apply (rule_AR_zero_ones_all 1 0
    (0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail') (d0 :: R_rest)) |].
  change (0 + 3 * 1) with 3.
  eapply etrans; [apply pev, (rule_AR_zero_zero
    (3 :: 0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail') (d0 :: R_rest)) |].
  unfold A0; cbn [bumpHead]; replace (3 + 1 + 1 + 1) with 6 by lia.
  apply evstep_refl.
Qed.

Lemma subStep_B0 (k : N) (tail : list N) : SubStep (B0 k tail) (A3 (k + 1) tail).
Proof.
  intros R_bot.
  eapply etrans; [apply (step_B0_core k tail 9 R_bot) | apply exit_sub].
Qed.

Lemma topStep_A0 (k : N) (tail : list N) : TopStep (A0 k tail) (A3 (k + 1) tail).
Proof.
  eapply etrans; [apply (top_A_to_B ((3 * k + 3) :: 0 :: 0 :: 0 :: tail)) |].
  eapply etrans; [apply (step_B0_core k tail 5 []) | apply exit_top].
Qed.

Lemma subStep_B3 (k : N) {tail tail' : list N} (h : SubStep tail tail') :
  SubStep (B3 k tail) (A0 (k + 1) tail').
Proof.
  intros R_bot.
  eapply etrans; [apply (step_B3_pre k tail 9 R_bot) |].
  eapply etrans; [apply (h (nreplicate (k + 1) 1 ++ (9 :: 1 :: 9 :: R_bot))) |].
  eapply etrans; [apply (step_B3_post k tail' 9 R_bot) | apply exit_sub].
Qed.

Lemma topStep_A3 (k : N) {tail tail' : list N} (h : SubStep tail tail') :
  TopStep (A3 k tail) (A0 (k + 1) tail').
Proof.
  eapply etrans; [apply (top_A_to_B ((3 * k + 3) :: 3 :: 0 :: tail)) |].
  eapply etrans; [apply (step_B3_pre k tail 5 []) |].
  eapply etrans; [apply (h (nreplicate (k + 1) 1 ++ [9; 1; 5])) |].
  eapply etrans; [apply (step_B3_post k tail' 5 []) | apply exit_top].
Qed.

Lemma subHalt_B3 (k : N) {tail : list N} (h : SubHalt tail) :
  SubHalt (B3 k tail).
Proof.
  intros R_bot.
  eapply halts_evstep; [apply (h (nreplicate (k + 1) 1 ++ (9 :: 1 :: 9 :: R_bot))) |].
  apply step_B3_pre.
Qed.

Lemma topHalt_A3 (k : N) {tail : list N} (h : SubHalt tail) :
  halts tm (cfg_F (0 :: A3 k tail) [5]).
Proof.
  eapply halts_evstep; [apply (h (nreplicate (k + 1) 1 ++ [9; 1; 5])) |].
  eapply etrans; [apply top_A_to_B | apply step_B3_pre].
Qed.

Fixpoint TowerA3 (ks : list N) (St : list N) : list N :=
  match ks with
  | [] => St
  | k :: ks' => TowerA3 ks' (A3 k St)
  end.

Fixpoint TowerA0Out (ks : list N) (St : list N) : list N :=
  match ks with
  | [] => St
  | k :: ks' => A0 k (TowerA0Out ks' St)
  end.

Fixpoint stepTowerAt (c : N) (ks : list N) : list N :=
  match ks with
  | [] => []
  | k :: ks' => (k + c) :: stepTowerAt (4 * c) ks'
  end.

Lemma stepTowerAt_ne_nil (c : N) {ks : list N} (hks : ks <> []) :
  stepTowerAt c ks <> [].
Proof.
  destruct ks as [| k ks']; [contradiction | discriminate].
Qed.

Lemma stepTowerAt_length (c : N) (ks : list N) :
  length (stepTowerAt c ks) = length ks.
Proof.
  revert c.
  induction ks as [| k ks' ih]; intros c; cbn [stepTowerAt length]; [reflexivity | rewrite ih; reflexivity].
Qed.

Lemma stepTowerAt_four (ks : list N) (c : N) :
  stepTowerAt c (stepTowerAt c (stepTowerAt c (stepTowerAt c ks))) = stepTowerAt (4 * c) ks.
Proof.
  revert c.
  induction ks as [| k ks' ih]; intros c; cbn [stepTowerAt]; [reflexivity |].
  f_equal; [lia | apply ih].
Qed.

Lemma towerA3_topStep_len : forall (n : nat) (ks : list N),
  length ks = S n ->
  forall {St St' : list N}, SubStep St St' ->
  TopStep (TowerA3 ks St) (TowerA3 (stepTowerAt 2 ks) St').
Proof.
  induction n as [| n ih]; intros ks hlen St St' h.
  - destruct ks as [| k [| ? ?]]; try discriminate.
    cbn [TowerA3 stepTowerAt].
    replace (k + 2) with (k + 1 + 1) by lia.
    exact (topStep_trans (topStep_A3 k h) (topStep_A0 (k + 1) St')).
  - destruct ks as [| k ks_rest]; [discriminate |].
    cbn [TowerA3 stepTowerAt].
    replace (k + 2) with (k + 1 + 1) by lia.
    injection hlen as hlen0.
    assert (hlen1 : length (stepTowerAt 2 ks_rest) = S n)
      by (rewrite stepTowerAt_length; exact hlen0).
    assert (hlen2 : length (stepTowerAt 2 (stepTowerAt 2 ks_rest)) = S n)
      by (rewrite stepTowerAt_length; exact hlen1).
    assert (hlen3 : length (stepTowerAt 2 (stepTowerAt 2 (stepTowerAt 2 ks_rest))) = S n)
      by (rewrite stepTowerAt_length; exact hlen2).
    pose proof (ih ks_rest hlen0 _ _ (subStep_A3 k St)) as h1.
    pose proof (ih _ hlen1 _ _ (subStep_B3 k h)) as h2.
    pose proof (ih _ hlen2 _ _ (subStep_A0 (k + 1) St')) as h3.
    pose proof (ih _ hlen3 _ _ (subStep_B0 (k + 1) St')) as h4.
    pose proof (topStep_trans h1 (topStep_trans h2 (topStep_trans h3 h4))) as hall.
    rewrite stepTowerAt_four in hall.
    exact hall.
Qed.

Lemma towerA3_topStep (ks : list N) (hks : ks <> []) {St St' : list N} (h : SubStep St St') :
  TopStep (TowerA3 ks St) (TowerA3 (stepTowerAt 2 ks) St').
Proof.
  destruct ks as [| k ks']; [contradiction |].
  exact (towerA3_topStep_len (length ks') (k :: ks') eq_refl h).
Qed.

Definition absorbA0 (k : N) (ks : list N) : list N :=
  match ks with
  | [] => [k + 1]
  | _ :: _ => (k + 1) :: stepTowerAt 2 (stepTowerAt 2 ks)
  end.

Lemma absorbA0_ne_nil (k : N) (ks : list N) : absorbA0 k ks <> [].
Proof.
  destruct ks; discriminate.
Qed.

Lemma towerA3_absorb_A0 (k : N) (ks : list N) (U : list N) :
  TopStep (TowerA3 ks (A0 k U)) (TowerA3 (absorbA0 k ks) U).
Proof.
  destruct ks as [| k0 ks0].
  - simpl; exact (topStep_A0 k U).
  - assert (hne : k0 :: ks0 <> []) by discriminate.
    pose proof (towerA3_topStep (k0 :: ks0) hne (subStep_A0 k U)) as h1.
    pose proof (towerA3_topStep (stepTowerAt 2 (k0 :: ks0))
      (stepTowerAt_ne_nil 2 hne) (subStep_B0 k U)) as h2.
    exact (topStep_trans h1 h2).
Qed.

Fixpoint absorbTowerA0Out (ks_bot ks_top : list N) : list N :=
  match ks_bot with
  | [] => ks_top
  | k :: ks_bot' => absorbTowerA0Out ks_bot' (absorbA0 k ks_top)
  end.

Lemma absorbTowerA0Out_ne_nil : forall (ks_bot ks_top : list N),
  (ks_bot <> [] \/ ks_top <> []) -> absorbTowerA0Out ks_bot ks_top <> [].
Proof.
  induction ks_bot as [| k ks_bot' ih]; intros ks_top h.
  - destruct h as [h | h]; [contradiction | exact h].
  - simpl. apply ih. right. apply absorbA0_ne_nil.
Qed.

Lemma towerA3_absorb_towerA0Out : forall (ks_bot ks_top : list N) (St : list N),
  TopStep (TowerA3 ks_top (TowerA0Out ks_bot St))
          (TowerA3 (absorbTowerA0Out ks_bot ks_top) St).
Proof.
  induction ks_bot as [| k ks_bot' ih]; intros ks_top St.
  - apply topStep_refl.
  - simpl TowerA0Out; simpl absorbTowerA0Out.
    exact (topStep_trans (towerA3_absorb_A0 k ks_top (TowerA0Out ks_bot' St))
                         (ih (absorbA0 k ks_top) St)).
Qed.

Lemma towerA3_halt_len : forall (n : nat) (ks : list N),
  length ks = S n ->
  forall {St : list N}, SubHalt St ->
  halts tm (cfg_F (0 :: TowerA3 ks St) [5]).
Proof.
  induction n as [| n ih]; intros ks hlen St h.
  - destruct ks as [| k [| ? ?]]; try discriminate.
    simpl TowerA3; exact (topHalt_A3 k h).
  - destruct ks as [| k ks_rest]; [discriminate |].
    simpl TowerA3.
    injection hlen as hlen_rest.
    assert (hne_rest : ks_rest <> [])
      by (destruct ks_rest; [discriminate | discriminate]).
    pose proof (towerA3_topStep ks_rest hne_rest (subStep_A3 k St)) as h_top.
    assert (hlen_step : length (stepTowerAt 2 ks_rest) = S n)
      by (rewrite stepTowerAt_length; exact hlen_rest).
    pose proof (ih (stepTowerAt 2 ks_rest) hlen_step _ (subHalt_B3 k h)) as h_halt.
    eapply halts_evstep; [exact h_halt | exact h_top].
Qed.

Lemma towerA3_halt (ks : list N) (hks : ks <> []) {St : list N} (h : SubHalt St) :
  halts tm (cfg_F (0 :: TowerA3 ks St) [5]).
Proof.
  destruct ks as [| k ks']; [contradiction |].
  exact (towerA3_halt_len (length ks') (k :: ks') eq_refl h).
Qed.

Lemma TowerA3_append : forall (ks1 ks2 : list N) (St : list N),
  TowerA3 (ks1 ++ ks2) St = TowerA3 ks2 (TowerA3 ks1 St).
Proof.
  induction ks1 as [| k ks1' ih]; intros ks2 St; simpl; [reflexivity | apply ih].
Qed.

(* ========================================================================== *)
(* Section 4: Computable RLE Stack Simulator (`stepGenRLE` & `runSubSim`)     *)
(* ========================================================================== *)

Definition RLEStack : Type := list (N * N).

Fixpoint evalRLE (s : RLEStack) : list N :=
  match s with
  | [] => []
  | (v, c) :: s' => nreplicate c v ++ evalRLE s'
  end.

Definition tailFor (isOpen : bool) (bot : list N) : list N :=
  if isOpen then bot else [].

Definition evalRLEWith (isOpen : bool) (s : RLEStack) (bot : list N) : list N :=
  evalRLE s ++ tailFor isOpen bot.

Lemma evalRLEWith_false (s : RLEStack) (bot : list N) :
  evalRLEWith false s bot = evalRLE s.
Proof.
  unfold evalRLEWith, tailFor; apply app_nil_r.
Qed.

Lemma evalRLEWith_true (s : RLEStack) (bot : list N) :
  evalRLEWith true s bot = evalRLE s ++ bot.
Proof. reflexivity. Qed.

Lemma evalRLE_append : forall (xs ys : RLEStack),
  evalRLE (xs ++ ys) = evalRLE xs ++ evalRLE ys.
Proof.
  intros xs ys; induction xs as [| [v c] xs' ih]; simpl; [reflexivity |].
  rewrite ih, app_assoc; reflexivity.
Qed.

Definition pushRun (v c : N) (s : RLEStack) : RLEStack :=
  if N.eqb c 0 then s
  else match s with
    | [] => [(v, c)]
    | (v', c') :: rest =>
      if N.eqb v v' then (v', c + c') :: rest
      else (v, c) :: (v', c') :: rest
    end.

Lemma evalRLE_pushRun (v c : N) (s : RLEStack) :
  evalRLE (pushRun v c s) = nreplicate c v ++ evalRLE s.
Proof.
  unfold pushRun.
  destruct (N.eqb c 0) eqn:hc.
  - apply N.eqb_eq in hc; subst c; reflexivity.
  - destruct s as [| [v' c'] rest]; [reflexivity |].
    destruct (N.eqb v v') eqn:hv.
    + apply N.eqb_eq in hv; subst v'.
      cbn [evalRLE].
      rewrite nreplicate_add, app_assoc; reflexivity.
    + reflexivity.
Qed.

Lemma evalRLEWith_pushRun (isOpen : bool) (v c : N) (s : RLEStack) (bot : list N) :
  evalRLEWith isOpen (pushRun v c s) bot = nreplicate c v ++ evalRLEWith isOpen s bot.
Proof.
  unfold evalRLEWith; rewrite evalRLE_pushRun, app_assoc; reflexivity.
Qed.

Lemma evalRLEWith_pushOne (isOpen : bool) (v : N) (s : RLEStack) (bot : list N) :
  evalRLEWith isOpen (pushRun v 1 s) bot = v :: evalRLEWith isOpen s bot.
Proof.
  exact (evalRLEWith_pushRun isOpen v 1 s bot).
Qed.

Fixpoint popOne (s : RLEStack) : option (N * RLEStack) :=
  match s with
  | [] => None
  | (v, c) :: s' =>
    if N.eqb c 0 then popOne s'
    else Some (v, if N.eqb c 1 then s' else (v, c - 1) :: s')
  end.

Lemma evalRLE_popOne_some : forall {s s' : RLEStack} {v : N},
  popOne s = Some (v, s') -> evalRLE s = v :: evalRLE s'.
Proof.
  induction s as [| [w c] s0 ih]; intros s' v h; [discriminate |].
  simpl in h.
  destruct (N.eqb c 0) eqn:hc0.
  - apply N.eqb_eq in hc0; subst c.
    cbn [evalRLE nreplicate replicate app].
    exact (ih s' v h).
  - apply N.eqb_neq in hc0.
    injection h as hv hs'; subst w s'.
    cbn [evalRLE].
    replace c with ((c - 1) + 1) at 1 by lia.
    rewrite nreplicate_succ; cbn [app].
    destruct (N.eqb c 1) eqn:hc1.
    + apply N.eqb_eq in hc1; subst c; reflexivity.
    + reflexivity.
Qed.

Lemma evalRLE_popOne_none : forall {s : RLEStack},
  popOne s = None -> evalRLE s = [].
Proof.
  induction s as [| [w c] s0 ih]; intros h; [reflexivity |].
  simpl in h.
  destruct (N.eqb c 0) eqn:hc0; [| discriminate].
  apply N.eqb_eq in hc0; subst c.
  cbn [evalRLE nreplicate replicate app].
  exact (ih h).
Qed.

Lemma evalRLEWith_popOne_some (isOpen : bool) {s s' : RLEStack} {v : N} (bot : list N)
  (h : popOne s = Some (v, s')) :
  evalRLEWith isOpen s bot = v :: evalRLEWith isOpen s' bot.
Proof.
  unfold evalRLEWith; rewrite (evalRLE_popOne_some h); reflexivity.
Qed.

Lemma evalRLEWith_popOne_none_closed {s : RLEStack} (bot : list N)
  (h : popOne s = None) :
  evalRLEWith false s bot = [].
Proof.
  unfold evalRLEWith, tailFor; rewrite (evalRLE_popOne_none h); reflexivity.
Qed.

Definition bumpTopOpt (isOpen : bool) (k : N) (s : RLEStack) : option RLEStack :=
  if N.eqb k 0 then Some s
  else match popOne s with
    | Some (v, s') => Some (pushRun (v + k) 1 s')
    | None => if isOpen then None else Some (pushRun (k - 1) 1 [])
    end.

Lemma evalRLEWith_bumpTopOpt {isOpen : bool} {k : N} {s s' : RLEStack} (bot : list N)
  (h : bumpTopOpt isOpen k s = Some s') :
  evalRLEWith isOpen s' bot = niter bumpHead k (evalRLEWith isOpen s bot).
Proof.
  unfold bumpTopOpt in h.
  destruct (N.eqb k 0) eqn:hk0.
  - apply N.eqb_eq in hk0; subst k.
    injection h as hs'; subst s'; reflexivity.
  - apply N.eqb_neq in hk0.
    destruct (popOne s) as [[v s1] |] eqn:hpop.
    + injection h as hs'; subst s'.
      rewrite evalRLEWith_pushOne, (evalRLEWith_popOne_some isOpen bot hpop),
              bumpHead_iterate_cons.
      reflexivity.
    + destruct isOpen; [discriminate |].
      injection h as hs'; subst s'.
      rewrite evalRLEWith_pushOne, (evalRLEWith_popOne_none_closed bot hpop).
      unfold evalRLEWith, tailFor, evalRLE; cbn [app].
      replace k with ((k - 1) + 1) at 2 by lia.
      rewrite bumpHead_iterate_nil; reflexivity.
Qed.

Inductive GenStepResult : Type :=
  | GSR_stepped (mode : StackMode) (L R : RLEStack)
  | GSR_halted
  | GSR_abort.

Definition tryFastF (L R : RLEStack) : option (RLEStack * RLEStack) :=
  match L with
  | [] => None
  | (v, c) :: L_rest =>
    if N.eqb v 0 && (5 <=? c) then
      match popOne R with
      | None => None
      | Some (r0, R1) =>
        if N.eqb r0 0 then
          match popOne R1 with
          | None => None
          | Some (d, R2) =>
            let k := (c - 1) / 4 in
            let rem := (c - 1) mod 4 in
            Some ((0, rem + 1) :: L_rest, pushRun 0 1 (pushRun (d + 8 * k) 1 R2))
          end
        else None
      end
    else None
  end.

Lemma tryFastF_sound {openL openR : bool} {L R L' R' : RLEStack} (L_bot R_bot : list N)
  (h : tryFastF L R = Some (L', R')) :
  cfg_F (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot) -->*
  cfg_F (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot).
Proof.
  unfold tryFastF in h.
  destruct L as [| [v c] L_rest]; [discriminate |].
  destruct (N.eqb v 0) eqn:hv; [| discriminate].
  destruct (5 <=? c) eqn:hc; [| discriminate].
  cbn [andb] in h.
  apply N.eqb_eq in hv; subst v.
  apply N.leb_le in hc.
  destruct (popOne R) as [[r0 R1] |] eqn:hR1; [| discriminate].
  destruct (N.eqb r0 0) eqn:hr0; [| discriminate].
  apply N.eqb_eq in hr0; subst r0.
  destruct (popOne R1) as [[d R2] |] eqn:hR2; [| discriminate].
  injection h as hL' hR'; subst L' R'.
  assert (hL : evalRLEWith openL ((0, c) :: L_rest) L_bot =
               nreplicate (4 * ((c - 1) / 4) + ((c - 1) mod 4) + 1) 0 ++
               evalRLEWith openL L_rest L_bot).
  { unfold evalRLEWith, evalRLE; fold evalRLE.
    rewrite <- app_assoc.
    replace c with (4 * ((c - 1) / 4) + ((c - 1) mod 4) + 1) at 1 by lia.
    reflexivity. }
  assert (hL2 : evalRLEWith openL ((0, (c - 1) mod 4 + 1) :: L_rest) L_bot =
                nreplicate ((c - 1) mod 4 + 1) 0 ++ evalRLEWith openL L_rest L_bot).
  { unfold evalRLEWith, evalRLE; fold evalRLE; rewrite <- app_assoc; reflexivity. }
  assert (hR : evalRLEWith openR R R_bot = 0 :: d :: evalRLEWith openR R2 R_bot).
  { rewrite (evalRLEWith_popOne_some openR R_bot hR1), (evalRLEWith_popOne_some openR R_bot hR2); reflexivity. }
  rewrite hL, hL2, hR, !evalRLEWith_pushOne.
  exact (rule_F_zero4_all ((c - 1) / 4) ((c - 1) mod 4)
           (evalRLEWith openL L_rest L_bot) d (evalRLEWith openR R2 R_bot)).
Qed.

Definition tryFastAR_ones (fast1 : bool) (L R : RLEStack) : option (RLEStack * RLEStack) :=
  if negb fast1 then None
  else match R with
    | [] => None
    | (v, c) :: R_rest =>
      if N.eqb v 1 && (2 <=? c) then
        match popOne L with
        | None => None
        | Some (l0, L1) =>
          if N.eqb l0 0 then
            match popOne L1 with
            | None => None
            | Some (b, L2) =>
              let m := c - 1 in
              Some (pushRun 0 1 (pushRun (b + 3 * m) 1 L2), (1, 1) :: R_rest)
            end
          else None
        end
      else None
    end.

Lemma tryFastAR_ones_sound {openL openR fast1 : bool} {L R L' R' : RLEStack}
  (L_bot R_bot : list N) (h : tryFastAR_ones fast1 L R = Some (L', R')) :
  cfg_AR (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot) -->*
  cfg_AR (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot).
Proof.
  unfold tryFastAR_ones in h.
  destruct fast1; [cbn [negb] in h | discriminate].
  destruct R as [| [v c] R_rest]; [discriminate |].
  destruct (N.eqb v 1) eqn:hv; [| discriminate].
  destruct (2 <=? c) eqn:hc; [| discriminate].
  cbn [andb] in h.
  apply N.eqb_eq in hv; subst v.
  apply N.leb_le in hc.
  destruct (popOne L) as [[l0 L1] |] eqn:hL1; [| discriminate].
  destruct (N.eqb l0 0) eqn:hl0; [| discriminate].
  apply N.eqb_eq in hl0; subst l0.
  destruct (popOne L1) as [[b L2] |] eqn:hL2; [| discriminate].
  injection h as hL' hR'; subst L' R'.
  assert (hL : evalRLEWith openL L L_bot = 0 :: b :: evalRLEWith openL L2 L_bot).
  { rewrite (evalRLEWith_popOne_some openL L_bot hL1), (evalRLEWith_popOne_some openL L_bot hL2); reflexivity. }
  assert (hR : evalRLEWith openR ((1, c) :: R_rest) R_bot =
               nreplicate ((c - 1) + 1) 1 ++ evalRLEWith openR R_rest R_bot).
  { unfold evalRLEWith, evalRLE; fold evalRLE.
    rewrite <- app_assoc.
    replace c with ((c - 1) + 1) at 1 by lia.
    reflexivity. }
  assert (hR_out : evalRLEWith openR ((1, 1) :: R_rest) R_bot =
                   1 :: evalRLEWith openR R_rest R_bot) by reflexivity.
  rewrite hL, hR, hR_out, !evalRLEWith_pushOne.
  exact (rule_AR_ones_all (c - 1) b (evalRLEWith openL L2 L_bot)
           (evalRLEWith openR R_rest R_bot)).
Qed.

Definition tryFastAR_zeroOnes (L R : RLEStack) : option (RLEStack * RLEStack) :=
  match R with
  | (v1, c1) :: (v2, m) :: R_rest =>
    if N.eqb v1 0 && N.eqb c1 1 && N.eqb v2 1 && (1 <=? m) then
      match popOne L with
      | None => None
      | Some (l0, L1) =>
        if N.eqb l0 0 then
          match popOne L1 with
          | None => None
          | Some (b, L2) =>
            Some (pushRun 0 1 (pushRun (b + 3 * m) 1 L2), pushRun 0 1 R_rest)
          end
        else None
      end
    else None
  | _ => None
  end.

Lemma tryFastAR_zeroOnes_sound {openL openR : bool} {L R L' R' : RLEStack}
  (L_bot R_bot : list N) (h : tryFastAR_zeroOnes L R = Some (L', R')) :
  cfg_AR (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot) -->*
  cfg_AR (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot).
Proof.
  unfold tryFastAR_zeroOnes in h.
  destruct R as [| [v1 c1] [| [v2 m] R_rest]]; try discriminate.
  destruct (N.eqb v1 0) eqn:hv1; [| discriminate].
  destruct (N.eqb c1 1) eqn:hc1; [| discriminate].
  destruct (N.eqb v2 1) eqn:hv2; [| discriminate].
  destruct (1 <=? m) eqn:hm; [| discriminate].
  cbn [andb] in h.
  apply N.eqb_eq in hv1; subst v1.
  apply N.eqb_eq in hc1; subst c1.
  apply N.eqb_eq in hv2; subst v2.
  destruct (popOne L) as [[l0 L1] |] eqn:hL1; [| discriminate].
  destruct (N.eqb l0 0) eqn:hl0; [| discriminate].
  apply N.eqb_eq in hl0; subst l0.
  destruct (popOne L1) as [[b L2] |] eqn:hL2; [| discriminate].
  injection h as hL' hR'; subst L' R'.
  assert (hL : evalRLEWith openL L L_bot = 0 :: b :: evalRLEWith openL L2 L_bot).
  { rewrite (evalRLEWith_popOne_some openL L_bot hL1), (evalRLEWith_popOne_some openL L_bot hL2); reflexivity. }
  assert (hR : evalRLEWith openR ((0, 1) :: (1, m) :: R_rest) R_bot =
               0 :: (nreplicate m 1 ++ evalRLEWith openR R_rest R_bot)).
  { unfold evalRLEWith, evalRLE; fold evalRLE.
    change (nreplicate 1 0) with [0]; cbn [app]; rewrite <- app_assoc; reflexivity. }
  rewrite hL, hR, !evalRLEWith_pushOne.
  exact (rule_AR_zero_ones_all m b (evalRLEWith openL L2 L_bot)
           (evalRLEWith openR R_rest R_bot)).
Qed.

Definition stepGenF_slow (openL openR : bool) (L R : RLEStack) : GenStepResult :=
  match popOne L with
  | None =>
    if openL then GSR_abort
    else GSR_stepped SM_AR (pushRun 1 1 []) R
  | Some (a, L1) =>
    if N.eqb a 0 then
      match popOne L1 with
      | None =>
        if openL then GSR_abort
        else match bumpTopOpt openR 1 R with
          | None => GSR_abort
          | Some R1 => GSR_stepped SM_F [] (pushRun 0 1 R1)
          end
      | Some (b, L2) =>
        if N.eqb b 0 then
          match bumpTopOpt openL 2 L2 with
          | None => GSR_abort
          | Some L3 => GSR_stepped SM_F L3 (pushRun 0 1 R)
          end
        else if N.eqb b 1 then
          match bumpTopOpt openR 1 R with
          | None => GSR_abort
          | Some R1 => GSR_stepped SM_F L2 (pushRun 2 1 R1)
          end
        else
          let b' := b - 2 in
          match bumpTopOpt openR 1 R with
          | None => GSR_abort
          | Some R1 => GSR_stepped SM_AR (pushRun b' 1 L2) (pushRun 0 2 R1)
          end
      end
    else if N.eqb a 1 then GSR_halted
    else if N.eqb a 2 then
      match bumpTopOpt openL 2 L1 with
      | None => GSR_abort
      | Some L2 =>
        match bumpTopOpt openR 1 R with
        | None => GSR_abort
        | Some R1 => GSR_stepped SM_AR L2 (pushRun 0 1 R1)
        end
      end
    else
      let a' := a - 3 in
      match bumpTopOpt openR 1 R with
      | None => GSR_abort
      | Some R1 =>
        GSR_stepped SM_F (pushRun (a' mod 3) 1 L1)
          (pushRun 0 1 (pushRun 1 (a' / 3) R1))
      end
  end.

Lemma stepGenF_slow_sound_step {openL openR : bool} {L R L' R' : RLEStack} {mode' : StackMode}
  (L_bot R_bot : list N) (h : stepGenF_slow openL openR L R = GSR_stepped mode' L' R') :
  cfg_F (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot) -->*
  evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot).
Proof.
  unfold stepGenF_slow in h.
  destruct (popOne L) as [[a L1] |] eqn:hpopL.
  - pose proof (evalRLEWith_popOne_some openL L_bot hpopL) as hL.
    destruct (N.eqb a 0) eqn:ha0.
    + apply N.eqb_eq in ha0; subst a.
      destruct (popOne L1) as [[b L2] |] eqn:hpopL1.
      * pose proof (evalRLEWith_popOne_some openL L_bot hpopL1) as hL1.
        destruct (N.eqb b 0) eqn:hb0.
        -- apply N.eqb_eq in hb0; subst b.
           destruct (bumpTopOpt openL 2 L2) as [L3 |] eqn:hL3; [| discriminate].
           injection h as hm hL' hR'; subst mode' L' R'.
           cbn [evalStackCfg].
           rewrite hL, hL1, (evalRLEWith_bumpTopOpt L_bot hL3), evalRLEWith_pushOne.
           exact (pev (rule_F_zero_zero (evalRLEWith openL L2 L_bot)
                        (evalRLEWith openR R R_bot))).
        -- destruct (N.eqb b 1) eqn:hb1.
           ++ apply N.eqb_eq in hb1; subst b.
              destruct (bumpTopOpt openR 1 R) as [R1 |] eqn:hR1; [| discriminate].
              injection h as hm hL' hR'; subst mode' L' R'.
              cbn [evalStackCfg].
              rewrite hL, hL1, evalRLEWith_pushOne, (evalRLEWith_bumpTopOpt R_bot hR1).
              exact (pev (rule_F_zero_one (evalRLEWith openL L2 L_bot)
                           (evalRLEWith openR R R_bot))).
           ++ apply N.eqb_neq in hb0; apply N.eqb_neq in hb1.
              destruct (bumpTopOpt openR 1 R) as [R1 |] eqn:hR1; [| discriminate].
              injection h as hm hL' hR'; subst mode' L' R'.
              cbn [evalStackCfg].
              rewrite hL, hL1, evalRLEWith_pushOne, evalRLEWith_pushRun,
                      (evalRLEWith_bumpTopOpt R_bot hR1).
              replace b with ((b - 2) + 2) at 1 by lia.
              exact (pev (rule_F_zero_add_two (evalRLEWith openL L2 L_bot)
                           (evalRLEWith openR R R_bot) (b - 2))).
      * destruct openL; [discriminate |].
        destruct (bumpTopOpt openR 1 R) as [R1 |] eqn:hR1; [| discriminate].
        injection h as hm hL' hR'; subst mode' L' R'.
        cbn [evalStackCfg].
        rewrite hL, (evalRLEWith_popOne_none_closed L_bot hpopL1),
                evalRLEWith_pushOne, (evalRLEWith_bumpTopOpt R_bot hR1),
                evalRLEWith_false.
        exact (pev (rule_F_zero_nil (evalRLEWith openR R R_bot))).
    + destruct (N.eqb a 1) eqn:ha1; [discriminate |].
      destruct (N.eqb a 2) eqn:ha2.
      * apply N.eqb_eq in ha2; subst a.
        destruct (bumpTopOpt openL 2 L1) as [L2 |] eqn:hL2; [| discriminate].
        destruct (bumpTopOpt openR 1 R) as [R1 |] eqn:hR1; [| discriminate].
        injection h as hm hL' hR'; subst mode' L' R'.
        cbn [evalStackCfg].
        rewrite hL, (evalRLEWith_bumpTopOpt L_bot hL2), evalRLEWith_pushOne,
                (evalRLEWith_bumpTopOpt R_bot hR1).
        exact (pev (rule_F_two (evalRLEWith openL L1 L_bot)
                     (evalRLEWith openR R R_bot))).
      * apply N.eqb_neq in ha0; apply N.eqb_neq in ha1; apply N.eqb_neq in ha2.
        destruct (bumpTopOpt openR 1 R) as [R1 |] eqn:hR1; [| discriminate].
        injection h as hm hL' hR'; subst mode' L' R'.
        cbn [evalStackCfg].
        rewrite hL, evalRLEWith_pushOne, evalRLEWith_pushOne,
                evalRLEWith_pushRun, (evalRLEWith_bumpTopOpt R_bot hR1).
        replace a with (3 * ((a - 3) / 3 + 1) + ((a - 3) mod 3)) at 1 by lia.
        pose proof (rule_F_step3_all (evalRLEWith openL L1 L_bot)
          (evalRLEWith openR R R_bot) ((a - 3) mod 3) ((a - 3) / 3 + 1)) as hstep.
        rewrite stepF3Right_succ in hstep.
        exact hstep.
  - destruct openL; [discriminate |].
    injection h as hm hL' hR'; subst mode' L' R'.
    cbn [evalStackCfg].
    rewrite (evalRLEWith_popOne_none_closed L_bot hpopL),
            evalRLEWith_pushOne, evalRLEWith_false.
    exact (pev (rule_F_nil (evalRLEWith openR R R_bot))).
Qed.

Lemma stepGenF_slow_sound_halt {openL openR : bool} {L R : RLEStack}
  (L_bot R_bot : list N) (h : stepGenF_slow openL openR L R = GSR_halted) :
  halts tm (cfg_F (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)).
Proof.
  unfold stepGenF_slow in h.
  destruct (popOne L) as [[a L1] |] eqn:hpopL; [| destruct openL; discriminate].
  destruct (N.eqb a 0) eqn:ha0.
  - destruct (popOne L1) as [[b L2] |].
    + destruct (N.eqb b 0); [destruct (bumpTopOpt openL 2 L2); discriminate |].
      destruct (N.eqb b 1); [destruct (bumpTopOpt openR 1 R); discriminate |].
      destruct (bumpTopOpt openR 1 R); discriminate.
    + destruct openL; [discriminate |].
      destruct (bumpTopOpt openR 1 R); discriminate.
  - destruct (N.eqb a 1) eqn:ha1.
    + apply N.eqb_eq in ha1; subst a.
      rewrite (evalRLEWith_popOne_some openL L_bot hpopL).
      apply rule_F_one_halt.
    + destruct (N.eqb a 2).
      * destruct (bumpTopOpt openL 2 L1); [| discriminate].
        destruct (bumpTopOpt openR 1 R); discriminate.
      * destruct (bumpTopOpt openR 1 R); discriminate.
Qed.

Definition stepGenAR_slow (openL openR : bool) (L R : RLEStack) : GenStepResult :=
  match popOne R with
  | None =>
    if openR then GSR_abort
    else GSR_stepped SM_F L (pushRun 1 1 [])
  | Some (d, R1) =>
    if N.eqb d 0 then
      match popOne L with
      | None =>
        if openL then GSR_abort
        else match bumpTopOpt openR 2 R1 with
          | None => GSR_abort
          | Some R2 => GSR_stepped SM_F [] R2
          end
      | Some (a, L1) =>
        if N.eqb a 0 then
          match bumpTopOpt openL 3 L1 with
          | None => GSR_abort
          | Some L2 =>
            match bumpTopOpt openR 1 R1 with
            | None => GSR_abort
            | Some R2 => GSR_stepped SM_AR L2 R2
            end
          end
        else if N.eqb a 1 then
          match bumpTopOpt openR 4 R1 with
          | None => GSR_abort
          | Some R2 => GSR_stepped SM_F L1 R2
          end
        else
          let k := a / 2 in
          match bumpTopOpt openR (2 * k) R1 with
          | None => GSR_abort
          | Some R2 => GSR_stepped SM_AR (pushRun (a mod 2) 1 L1) (pushRun 0 1 R2)
          end
      end
    else if N.eqb d 1 then
      match popOne R1 with
      | None =>
        if openR then GSR_abort
        else GSR_stepped SM_AR (pushRun 0 1 L) []
      | Some (e, R2) =>
        GSR_stepped SM_AR L (pushRun 0 1 (pushRun (e + 1) 1 R2))
      end
    else
      let k := d / 2 in
      GSR_stepped SM_AR (pushRun 0 k L) (pushRun (d mod 2) 1 R1)
  end.

Lemma stepGenAR_slow_sound_step {openL openR : bool} {L R L' R' : RLEStack} {mode' : StackMode}
  (L_bot R_bot : list N) (h : stepGenAR_slow openL openR L R = GSR_stepped mode' L' R') :
  cfg_AR (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot) -->*
  evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot).
Proof.
  unfold stepGenAR_slow in h.
  destruct (popOne R) as [[d R1] |] eqn:hpopR.
  - pose proof (evalRLEWith_popOne_some openR R_bot hpopR) as hR.
    destruct (N.eqb d 0) eqn:hd0.
    + apply N.eqb_eq in hd0; subst d.
      destruct (popOne L) as [[a L1] |] eqn:hpopL.
      * pose proof (evalRLEWith_popOne_some openL L_bot hpopL) as hL.
        destruct (N.eqb a 0) eqn:ha0.
        -- apply N.eqb_eq in ha0; subst a.
           destruct (bumpTopOpt openL 3 L1) as [L2 |] eqn:hL2; [| discriminate].
           destruct (bumpTopOpt openR 1 R1) as [R2 |] eqn:hR2; [| discriminate].
           injection h as hm hL' hR'; subst mode' L' R'.
           cbn [evalStackCfg].
           rewrite hL, hR, (evalRLEWith_bumpTopOpt L_bot hL2),
                   (evalRLEWith_bumpTopOpt R_bot hR2).
           exact (pev (rule_AR_zero_zero (evalRLEWith openL L1 L_bot)
                        (evalRLEWith openR R1 R_bot))).
        -- destruct (N.eqb a 1) eqn:ha1.
           ++ apply N.eqb_eq in ha1; subst a.
              destruct (bumpTopOpt openR 4 R1) as [R2 |] eqn:hR2; [| discriminate].
              injection h as hm hL' hR'; subst mode' L' R'.
              cbn [evalStackCfg].
              rewrite hL, hR, (evalRLEWith_bumpTopOpt R_bot hR2).
              exact (pev (rule_AR_one_zero (evalRLEWith openL L1 L_bot)
                           (evalRLEWith openR R1 R_bot))).
           ++ apply N.eqb_neq in ha0; apply N.eqb_neq in ha1.
              destruct (bumpTopOpt openR (2 * (a / 2)) R1) as [R2 |] eqn:hR2; [| discriminate].
              injection h as hm hL' hR'; subst mode' L' R'.
              cbn [evalStackCfg].
              rewrite hL, hR, !evalRLEWith_pushOne,
                      (evalRLEWith_bumpTopOpt R_bot hR2), <- bumpHead2_iterate_eq.
              replace a with (2 * (a / 2) + (a mod 2)) at 1 by lia.
              exact (rule_AR_add_two_zero_all (evalRLEWith openL L1 L_bot)
                       (evalRLEWith openR R1 R_bot) (a mod 2) (a / 2)).
      * destruct openL; [discriminate |].
        destruct (bumpTopOpt openR 2 R1) as [R2 |] eqn:hR2; [| discriminate].
        injection h as hm hL' hR'; subst mode' L' R'.
        cbn [evalStackCfg].
        rewrite (evalRLEWith_popOne_none_closed L_bot hpopL),
                hR, (evalRLEWith_bumpTopOpt R_bot hR2), evalRLEWith_false.
        exact (pev (rule_AR_nil_zero (evalRLEWith openR R1 R_bot))).
    + destruct (N.eqb d 1) eqn:hd1.
      * apply N.eqb_eq in hd1; subst d.
        destruct (popOne R1) as [[e R2] |] eqn:hpopR1.
        -- injection h as hm hL' hR'; subst mode' L' R'.
           cbn [evalStackCfg].
           rewrite hR, (evalRLEWith_popOne_some openR R_bot hpopR1), !evalRLEWith_pushOne.
           exact (pev (rule_AR_one_cons (evalRLEWith openL L L_bot)
                        (evalRLEWith openR R2 R_bot) e)).
        -- destruct openR; [discriminate |].
           injection h as hm hL' hR'; subst mode' L' R'.
           cbn [evalStackCfg].
           rewrite hR, (evalRLEWith_popOne_none_closed R_bot hpopR1),
                   evalRLEWith_pushOne, evalRLEWith_false.
           exact (pev (rule_AR_one_nil (evalRLEWith openL L L_bot))).
      * apply N.eqb_neq in hd0; apply N.eqb_neq in hd1.
        injection h as hm hL' hR'; subst mode' L' R'.
        cbn [evalStackCfg].
        rewrite hR, evalRLEWith_pushRun, evalRLEWith_pushOne.
        replace d with (2 * (d / 2) + (d mod 2)) at 1 by lia.
        exact (rule_AR_step2_all (evalRLEWith openL L L_bot)
                 (evalRLEWith openR R1 R_bot) (d mod 2) (d / 2)).
  - destruct openR; [discriminate |].
    injection h as hm hL' hR'; subst mode' L' R'.
    cbn [evalStackCfg].
    rewrite (evalRLEWith_popOne_none_closed R_bot hpopR),
            evalRLEWith_pushOne, evalRLEWith_false.
    exact (pev (rule_AR_nil (evalRLEWith openL L L_bot))).
Qed.

Lemma stepGenAR_slow_not_halt (openL openR : bool) (L R : RLEStack) :
  stepGenAR_slow openL openR L R <> GSR_halted.
Proof.
  unfold stepGenAR_slow.
  destruct (popOne R) as [[d R1] |].
  - destruct (N.eqb d 0).
    + destruct (popOne L) as [[a L1] |].
      * destruct (N.eqb a 0).
        -- destruct (bumpTopOpt openL 3 L1); [| discriminate].
           destruct (bumpTopOpt openR 1 R1); discriminate.
        -- destruct (N.eqb a 1).
           ++ destruct (bumpTopOpt openR 4 R1); discriminate.
           ++ destruct (bumpTopOpt openR (2 * (a / 2)) R1); discriminate.
      * destruct openL; [discriminate |].
        destruct (bumpTopOpt openR 2 R1); discriminate.
    + destruct (N.eqb d 1).
      * destruct (popOne R1) as [[e R2] |]; [discriminate |].
        destruct openR; discriminate.
      * discriminate.
  - destruct openR; discriminate.
Qed.

Definition stepGenRLE (openL openR fast1 : bool) (mode : StackMode) (L R : RLEStack) : GenStepResult :=
  match mode with
  | SM_F =>
    match tryFastF L R with
    | Some (L', R') => GSR_stepped SM_F L' R'
    | None => stepGenF_slow openL openR L R
    end
  | SM_AR =>
    match tryFastAR_ones fast1 L R with
    | Some (L', R') => GSR_stepped SM_AR L' R'
    | None =>
      match tryFastAR_zeroOnes L R with
      | Some (L', R') => GSR_stepped SM_AR L' R'
      | None => stepGenAR_slow openL openR L R
      end
    end
  end.

Lemma stepGenRLE_sound_step {openL openR fast1 : bool} {mode mode' : StackMode}
  {L R L' R' : RLEStack} (L_bot R_bot : list N)
  (h : stepGenRLE openL openR fast1 mode L R = GSR_stepped mode' L' R') :
  evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot) -->*
  evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot).
Proof.
  unfold stepGenRLE in h.
  destruct mode.
  - destruct (tryFastF L R) as [[Lf Rf] |] eqn:hfast.
    + injection h as hm hL' hR'; subst mode' L' R'.
      exact (tryFastF_sound L_bot R_bot hfast).
    + exact (stepGenF_slow_sound_step L_bot R_bot h).
  - destruct (tryFastAR_ones fast1 L R) as [[Lf Rf] |] eqn:hfast1.
    + injection h as hm hL' hR'; subst mode' L' R'.
      exact (tryFastAR_ones_sound L_bot R_bot hfast1).
    + destruct (tryFastAR_zeroOnes L R) as [[Lf Rf] |] eqn:hfast2.
      * injection h as hm hL' hR'; subst mode' L' R'.
        exact (tryFastAR_zeroOnes_sound L_bot R_bot hfast2).
      * exact (stepGenAR_slow_sound_step L_bot R_bot h).
Qed.

Lemma stepGenRLE_sound_halt {openL openR fast1 : bool} {mode : StackMode} {L R : RLEStack}
  (L_bot R_bot : list N) (h : stepGenRLE openL openR fast1 mode L R = GSR_halted) :
  halts tm (evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)).
Proof.
  unfold stepGenRLE in h.
  destruct mode.
  - destruct (tryFastF L R) as [[? ?] |]; [discriminate |].
    exact (stepGenF_slow_sound_halt L_bot R_bot h).
  - destruct (tryFastAR_ones fast1 L R) as [[? ?] |]; [discriminate |].
    destruct (tryFastAR_zeroOnes L R) as [[? ?] |]; [discriminate |].
    exfalso; exact (stepGenAR_slow_not_halt openL openR L R h).
Qed.

Fixpoint runStepsRLE (n : nat) (openL openR fast1 : bool) (mode : StackMode)
  (L R : RLEStack) : GenStepResult :=
  match n with
  | 0%nat => GSR_stepped mode L R
  | S n' =>
    match stepGenRLE openL openR fast1 mode L R with
    | GSR_stepped mode1 L1 R1 => runStepsRLE n' openL openR fast1 mode1 L1 R1
    | GSR_halted => GSR_halted
    | GSR_abort => GSR_abort
    end
  end.

Lemma runStepsRLE_sound_step : forall {n : nat} {openL openR fast1 : bool}
  {mode mode' : StackMode} {L R L' R' : RLEStack} (L_bot R_bot : list N),
  runStepsRLE n openL openR fast1 mode L R = GSR_stepped mode' L' R' ->
  evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot) -->*
  evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot).
Proof.
  induction n as [| n ih]; intros openL openR fast1 mode mode' L R L' R' L_bot R_bot h.
  - injection h as hm hL hR; subst mode' L' R'; apply evstep_refl.
  - cbn [runStepsRLE] in h.
    destruct (stepGenRLE openL openR fast1 mode L R) as [mode1 L1 R1 | |] eqn:hstep;
      try discriminate.
    exact (etrans (stepGenRLE_sound_step L_bot R_bot hstep) (ih _ _ _ _ _ _ _ _ _ L_bot R_bot h)).
Qed.

Fixpoint peelZeros (n : nat) (s : RLEStack) : option RLEStack :=
  match n with
  | 0%nat => Some s
  | S n' =>
    match popOne s with
    | None => None
    | Some (v, s') =>
      if N.eqb v 0 then peelZeros n' s' else None
    end
  end.

Lemma evalRLE_peelZeros : forall {n : nat} {s s' : RLEStack},
  peelZeros n s = Some s' -> evalRLE s = replicate n 0 ++ evalRLE s'.
Proof.
  induction n as [| n ih]; intros s s' h.
  - injection h as hs'; subst s'; reflexivity.
  - cbn [peelZeros] in h.
    destruct (popOne s) as [[v s1] |] eqn:hpop; [| discriminate].
    destruct (N.eqb v 0) eqn:hv; [| discriminate].
    apply N.eqb_eq in hv; subst v.
    rewrite (evalRLE_popOne_some hpop), (ih s1 s' h); reflexivity.
Qed.

Lemma evalRLEWith_peelZeros {isOpen : bool} {n : nat} {s s' : RLEStack} (bot : list N)
  (h : peelZeros n s = Some s') :
  evalRLEWith isOpen s bot = replicate n 0 ++ evalRLEWith isOpen s' bot.
Proof.
  unfold evalRLEWith; rewrite (evalRLE_peelZeros h), app_assoc; reflexivity.
Qed.

Definition isSingleVal (v : N) (s : RLEStack) : bool :=
  match popOne s with
  | Some (w, s') => N.eqb w v && match popOne s' with None => true | Some _ => false end
  | None => false
  end.

Lemma evalRLEWith_isSingleVal {v : N} {s : RLEStack} (bot : list N)
  (h : isSingleVal v s = true) :
  evalRLEWith true s bot = v :: bot.
Proof.
  unfold isSingleVal in h.
  destruct (popOne s) as [[w s'] |] eqn:hp1; [| discriminate].
  destruct (N.eqb w v) eqn:hw; [| discriminate].
  apply N.eqb_eq in hw; subst w.
  destruct (popOne s') eqn:hp2; [discriminate |].
  unfold evalRLEWith, tailFor.
  rewrite (evalRLE_popOne_some hp1), (evalRLE_popOne_none hp2); reflexivity.
Qed.

Lemma evalRLE_isSingleVal {v : N} {s : RLEStack} (h : isSingleVal v s = true) :
  evalRLE s = [v].
Proof.
  pose proof (evalRLEWith_isSingleVal [] h) as h1.
  unfold evalRLEWith, tailFor in h1.
  rewrite app_nil_r in h1; exact h1.
Qed.

Inductive SubSimResult : Type :=
  | SSR_stepped (S' : RLEStack)
  | SSR_halted
  | SSR_abort.

Definition mode_eqb (m1 m2 : StackMode) : bool :=
  match m1, m2 with
  | SM_F, SM_F => true
  | SM_AR, SM_AR => true
  | _, _ => false
  end.

Fixpoint runSubLoop (fuel : nat) (openL fast1 : bool) (mode : StackMode)
  (L R : RLEStack) : SubSimResult :=
  match fuel with
  | 0%nat => SSR_abort
  | S fuel' =>
    if mode_eqb mode SM_AR && isSingleVal 0 R then
      match peelZeros 5 L with
      | Some S' => SSR_stepped S'
      | None => SSR_abort
      end
    else
      match stepGenRLE openL true fast1 mode L R with
      | GSR_stepped mode' L' R' => runSubLoop fuel' openL fast1 mode' L' R'
      | GSR_halted => SSR_halted
      | GSR_abort => SSR_abort
      end
  end.

Definition runSubSim (fuel : nat) (openL fast1 : bool) (St : RLEStack) : SubSimResult :=
  runSubLoop fuel openL fast1 SM_F (pushRun 0 1 St) [(9, 1)].

Lemma runSubLoop_sound_step : forall {fuel : nat} {openL fast1 : bool} {mode : StackMode}
  {L R St' : RLEStack} (L_bot R_bot : list N),
  runSubLoop fuel openL fast1 mode L R = SSR_stepped St' ->
  evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith true R R_bot) -->*
  cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: evalRLEWith openL St' L_bot) (0 :: R_bot).
Proof.
  induction fuel as [| fuel ih]; intros openL fast1 mode L R St' L_bot R_bot h; [discriminate |].
  cbn [runSubLoop] in h.
  destruct (mode_eqb mode SM_AR && isSingleVal 0 R) eqn:hexit.
  - apply Bool.andb_true_iff in hexit.
    destruct hexit as [hmode hR0].
    destruct mode; [discriminate |].
    destruct (peelZeros 5 L) as [S_out |] eqn:hpeel; [| discriminate].
    injection h as hSt'; subst S_out.
    cbn [evalStackCfg].
    rewrite (evalRLEWith_isSingleVal R_bot hR0), (evalRLEWith_peelZeros L_bot hpeel).
    apply evstep_refl.
  - destruct (stepGenRLE openL true fast1 mode L R) as [mode' L' R' | |] eqn:hstep;
      try discriminate.
    exact (etrans (stepGenRLE_sound_step L_bot R_bot hstep) (ih _ _ _ _ _ _ L_bot R_bot h)).
Qed.

Lemma runSubLoop_sound_halt : forall {fuel : nat} {openL fast1 : bool} {mode : StackMode}
  {L R : RLEStack} (L_bot R_bot : list N),
  runSubLoop fuel openL fast1 mode L R = SSR_halted ->
  halts tm (evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith true R R_bot)).
Proof.
  induction fuel as [| fuel ih]; intros openL fast1 mode L R L_bot R_bot h; [discriminate |].
  cbn [runSubLoop] in h.
  destruct (mode_eqb mode SM_AR && isSingleVal 0 R) eqn:hexit.
  - destruct (peelZeros 5 L); discriminate.
  - destruct (stepGenRLE openL true fast1 mode L R) as [mode' L' R' | |] eqn:hstep;
      try discriminate.
    + eapply halts_evstep; [exact (ih _ _ _ _ _ L_bot R_bot h) |].
      exact (stepGenRLE_sound_step L_bot R_bot hstep).
    + exact (stepGenRLE_sound_halt L_bot R_bot hstep).
Qed.

Lemma runSubSim_sound_closed {fuel : nat} {fast1 : bool} {St St' : RLEStack}
  (h : runSubSim fuel false fast1 St = SSR_stepped St') :
  SubStep (evalRLE St) (evalRLE St').
Proof.
  intros R_bot.
  pose proof (runSubLoop_sound_step [] R_bot h) as h1.
  cbn [evalStackCfg] in h1.
  rewrite evalRLEWith_pushOne, !evalRLEWith_false in h1.
  exact h1.
Qed.

Lemma runSubSim_sound_open {fuel : nat} {fast1 : bool} {St St' : RLEStack} (U : list N)
  (h : runSubSim fuel true fast1 St = SSR_stepped St') :
  SubStep (evalRLE St ++ U) (evalRLE St' ++ U).
Proof.
  intros R_bot.
  pose proof (runSubLoop_sound_step U R_bot h) as h1.
  cbn [evalStackCfg] in h1.
  rewrite evalRLEWith_pushOne, !evalRLEWith_true in h1.
  exact h1.
Qed.

Lemma runSubSim_sound_halt {fuel : nat} {fast1 : bool} {St : RLEStack}
  (h : runSubSim fuel false fast1 St = SSR_halted) :
  SubHalt (evalRLE St).
Proof.
  intros R_bot.
  pose proof (runSubLoop_sound_halt [] R_bot h) as h1.
  cbn [evalStackCfg] in h1.
  rewrite evalRLEWith_pushOne, evalRLEWith_false in h1.
  exact h1.
Qed.

Definition peelOneA3 (s : RLEStack) : option (N * RLEStack) :=
  match popOne s with
  | None => None
  | Some (v6, s1) =>
    if N.eqb v6 6 then
      match peelZeros 3 s1 with
      | None => None
      | Some s2 =>
        match popOne s2 with
        | None => None
        | Some (x, s3) =>
          if (3 <=? x) && N.eqb (x mod 3) 0 then
            match popOne s3 with
            | None => None
            | Some (v3, s4) =>
              if N.eqb v3 3 then
                match popOne s4 with
                | None => None
                | Some (v0, s5) =>
                  if N.eqb v0 0 then Some (x / 3 - 1, s5)
                  else None
                end
              else None
            end
          else None
        end
      end
    else None
  end.

Lemma evalRLE_peelOneA3 {s s' : RLEStack} {k : N} (h : peelOneA3 s = Some (k, s')) :
  evalRLE s = A3 k (evalRLE s').
Proof.
  unfold peelOneA3 in h.
  destruct (popOne s) as [[v6 s1] |] eqn:hp1; [| discriminate].
  destruct (N.eqb v6 6) eqn:hv6; [| discriminate].
  apply N.eqb_eq in hv6; subst v6.
  destruct (peelZeros 3 s1) as [s2 |] eqn:hpz; [| discriminate].
  destruct (popOne s2) as [[x s3] |] eqn:hp2; [| discriminate].
  destruct (3 <=? x) eqn:hx1; [| discriminate].
  destruct (N.eqb (x mod 3) 0) eqn:hx2; [| discriminate].
  cbn [andb] in h.
  apply N.leb_le in hx1; apply N.eqb_eq in hx2.
  destruct (popOne s3) as [[v3 s4] |] eqn:hp3; [| discriminate].
  destruct (N.eqb v3 3) eqn:hv3; [| discriminate].
  apply N.eqb_eq in hv3; subst v3.
  destruct (popOne s4) as [[v0 s5] |] eqn:hp4; [| discriminate].
  destruct (N.eqb v0 0) eqn:hv0; [| discriminate].
  apply N.eqb_eq in hv0; subst v0.
  injection h as hk hs'; subst k s'.
  rewrite (evalRLE_popOne_some hp1), (evalRLE_peelZeros hpz),
          (evalRLE_popOne_some hp2), (evalRLE_popOne_some hp3),
          (evalRLE_popOne_some hp4).
  unfold A3; cbn [replicate app].
  replace (3 * (x / 3 - 1) + 3) with x by lia.
  reflexivity.
Qed.

Fixpoint peelA3Loop (fuel : nat) (acc : list N) (s : RLEStack) : list N * RLEStack :=
  match fuel with
  | 0%nat => (acc, s)
  | S fuel' =>
    match peelOneA3 s with
    | Some (k, s') => peelA3Loop fuel' (k :: acc) s'
    | None => (acc, s)
    end
  end.

Lemma evalRLE_peelA3Loop : forall (fuel : nat) (acc : list N) (s : RLEStack),
  TowerA3 (fst (peelA3Loop fuel acc s)) (evalRLE (snd (peelA3Loop fuel acc s))) =
  TowerA3 acc (evalRLE s).
Proof.
  induction fuel as [| fuel ih]; intros acc s; [reflexivity |].
  cbn [peelA3Loop].
  destruct (peelOneA3 s) as [[k s'] |] eqn:hp; [| reflexivity].
  rewrite ih; cbn [TowerA3]; rewrite (evalRLE_peelOneA3 hp); reflexivity.
Qed.

Definition wrapOneA3RLE (k : N) (s : RLEStack) : RLEStack :=
  pushRun 6 1 (pushRun 0 3 (pushRun (3 * k + 3) 1 (pushRun 3 1 (pushRun 0 1 s)))).

Fixpoint wrapTowerA3RLE (ks : list N) (s : RLEStack) : RLEStack :=
  match ks with
  | [] => s
  | k :: ks' => wrapTowerA3RLE ks' (wrapOneA3RLE k s)
  end.

Lemma evalRLE_wrapOneA3RLE (k : N) (s : RLEStack) :
  evalRLE (wrapOneA3RLE k s) = A3 k (evalRLE s).
Proof.
  unfold wrapOneA3RLE, A3.
  rewrite !evalRLE_pushRun; reflexivity.
Qed.

Lemma evalRLE_wrapTowerA3RLE : forall (ks : list N) (s : RLEStack),
  evalRLE (wrapTowerA3RLE ks s) = TowerA3 ks (evalRLE s).
Proof.
  induction ks as [| k ks' ih]; intros s; [reflexivity |].
  cbn [wrapTowerA3RLE TowerA3].
  rewrite ih, evalRLE_wrapOneA3RLE; reflexivity.
Qed.

Definition wrapOneA0RLE (k : N) (s : RLEStack) : RLEStack :=
  pushRun 6 1 (pushRun 0 3 (pushRun (3 * k + 3) 1 (pushRun 0 3 s))).

Fixpoint wrapTowerA0OutRLE (ks : list N) (s : RLEStack) : RLEStack :=
  match ks with
  | [] => s
  | k :: ks' => wrapOneA0RLE k (wrapTowerA0OutRLE ks' s)
  end.

Lemma evalRLE_wrapOneA0RLE (k : N) (s : RLEStack) :
  evalRLE (wrapOneA0RLE k s) = A0 k (evalRLE s).
Proof.
  unfold wrapOneA0RLE, A0.
  rewrite !evalRLE_pushRun; reflexivity.
Qed.

Lemma evalRLE_wrapTowerA0OutRLE : forall (ks : list N) (s : RLEStack),
  evalRLE (wrapTowerA0OutRLE ks s) = TowerA0Out ks (evalRLE s).
Proof.
  induction ks as [| k ks' ih]; intros s; [reflexivity |].
  cbn [wrapTowerA0OutRLE TowerA0Out].
  rewrite evalRLE_wrapOneA0RLE, ih; reflexivity.
Qed.

(* ========================================================================== *)
(* Section 5: Three-Phase Halting Trajectory (`c0 -> HALT`)                   *)
(* ========================================================================== *)

Lemma evalRLE_pushOne (v : N) (s : RLEStack) :
  evalRLE (pushRun v 1 s) = v :: evalRLE s.
Proof.
  exact (evalRLE_pushRun v 1 s).
Qed.

Definition midPrefixRLE : RLEStack :=
  [ (0, 2819); (12, 1); (0, 2); (3, 1); (0, 4); (1398, 1); (0, 3); (6, 1);
    (0, 3); (345, 1); (0, 3); (6, 1); (0, 3); (81, 1); (0, 3); (6, 1);
    (0, 3); (15, 1); (0, 3); (3, 1); (0, 59107); (6, 1); (0, 883); (6, 1);
    (0, 47); (12, 1); (0, 2); (3, 1); (0, 4); (12, 1); (0, 3); (3, 1);
    (0, 203); (6, 1); (0, 54); (3, 1); (0, 3); (3, 2); (0, 7) ].

Definition midPrefix : list N := evalRLE midPrefixRLE.

Definition bodyStack (Z b1 : N) : list N :=
  0 :: 3 :: (nreplicate Z 0 ++ (6 :: (midPrefix ++ [b1; 2]))).

Definition bodyStackRLE (Z b1 : N) : RLEStack :=
  pushRun 0 1 (pushRun 3 1 (pushRun 0 Z (pushRun 6 1
    (midPrefixRLE ++ [(b1, 1); (2, 1)])))).

Lemma evalRLE_bodyStackRLE (Z b1 : N) :
  evalRLE (bodyStackRLE Z b1) = bodyStack Z b1.
Proof.
  unfold bodyStackRLE, bodyStack.
  rewrite evalRLE_pushOne, evalRLE_pushOne, evalRLE_pushRun, evalRLE_pushOne, evalRLE_append.
  change (evalRLE midPrefixRLE) with midPrefix.
  reflexivity.
Qed.

Definition ksInitOut : list N :=
  [30758225; 7689554; 1922386; 480594; 120146; 30034; 7506; 1874; 466; 114; 26; 4].

Definition expectedPhase1L : RLEStack :=
  pushRun 0 1 (wrapTowerA0OutRLE ksInitOut (bodyStackRLE 56233 3)).

Lemma evalRLE_expectedPhase1L :
  evalRLE expectedPhase1L = 0 :: TowerA0Out ksInitOut (bodyStack 56233 3).
Proof.
  unfold expectedPhase1L.
  rewrite evalRLE_pushOne, evalRLE_wrapTowerA0OutRLE, evalRLE_bodyStackRLE.
  reflexivity.
Qed.

(* Phase 1: 11,728 steps (with 1,062 TowerA3 jumps) from `cfg_F [] [1]` to `SNAP 1 + R=[5]` *)

Definition tryJumpPhase1 (mode : StackMode) (L R : RLEStack) : option RLEStack :=
  if mode_eqb mode SM_F && isSingleVal 5 R then
    match popOne L with
    | None => None
    | Some (v0, S_rle) =>
      if N.eqb v0 0 then
        let p := peelA3Loop 35 [] S_rle in
        match fst p with
        | [] => None
        | k0 :: ks0 =>
          match runSubSim 100 false false (snd p) with
          | SSR_stepped S'_inner =>
            Some (pushRun 0 1 (wrapTowerA3RLE (stepTowerAt 2 (k0 :: ks0)) S'_inner))
          | SSR_halted => None
          | SSR_abort => None
          end
        end
      else None
    end
  else None.

Lemma tryJumpPhase1_sound {mode : StackMode} {L R L' : RLEStack}
  (h : tryJumpPhase1 mode L R = Some L') :
  evalStackCfg mode (evalRLE L) (evalRLE R) -->* cfg_F (evalRLE L') [5].
Proof.
  unfold tryJumpPhase1 in h.
  destruct (mode_eqb mode SM_F && isSingleVal 5 R) eqn:hmr; [| discriminate].
  apply Bool.andb_true_iff in hmr; destruct hmr as [hm hR5].
  destruct mode; [| discriminate].
  destruct (popOne L) as [[v0 S_rle] |] eqn:hpop; [| discriminate].
  destruct (N.eqb v0 0) eqn:hv0; [| discriminate].
  apply N.eqb_eq in hv0; subst v0.
  pose proof (evalRLE_peelA3Loop 35 [] S_rle) as hpeel.
  cbn [TowerA3] in hpeel.
  destruct (fst (peelA3Loop 35 [] S_rle)) as [| k0 ks0] eqn:hks; [discriminate |].
  destruct (runSubSim 100 false false (snd (peelA3Loop 35 [] S_rle))) as [S'_inner | |] eqn:hsim;
    try discriminate.
  injection h as hL'; subst L'.
  cbn [evalStackCfg].
  rewrite (evalRLE_popOne_some hpop), (evalRLE_isSingleVal hR5), <- hpeel,
          evalRLE_pushOne, evalRLE_wrapTowerA3RLE, evalRLE_wrapOneA3RLE.
  assert (hne : k0 :: ks0 <> []) by discriminate.
  exact (towerA3_topStep (k0 :: ks0) hne (runSubSim_sound_closed hsim)).
Qed.

Definition stepPhase1 (mode : StackMode) (L R : RLEStack)
  : option (StackMode * RLEStack * RLEStack) :=
  match tryJumpPhase1 mode L R with
  | Some L' => Some (SM_F, L', [(5, 1)])
  | None =>
    match stepGenRLE false false true mode L R with
    | GSR_stepped mode' L' R' => Some (mode', L', R')
    | GSR_halted => None
    | GSR_abort => None
    end
  end.

Lemma stepPhase1_sound {mode mode' : StackMode} {L R L' R' : RLEStack}
  (h : stepPhase1 mode L R = Some (mode', L', R')) :
  evalStackCfg mode (evalRLE L) (evalRLE R) -->*
  evalStackCfg mode' (evalRLE L') (evalRLE R').
Proof.
  unfold stepPhase1 in h.
  destruct (tryJumpPhase1 mode L R) as [Lj |] eqn:hj.
  - injection h as hm hL hR; subst mode' L' R'.
    exact (tryJumpPhase1_sound hj).
  - destruct (stepGenRLE false false true mode L R) as [m1 L1 R1 | |] eqn:hstep;
      try discriminate.
    injection h as hm hL hR; subst mode' L' R'.
    pose proof (stepGenRLE_sound_step [] [] hstep) as hs.
    rewrite !evalRLEWith_false in hs.
    exact hs.
Qed.

Fixpoint runPhase1Steps (n : nat) (mode : StackMode) (L R : RLEStack)
  : option (StackMode * RLEStack * RLEStack) :=
  match n with
  | 0%nat => Some (mode, L, R)
  | S n' =>
    match stepPhase1 mode L R with
    | Some (mode1, L1, R1) => runPhase1Steps n' mode1 L1 R1
    | None => None
    end
  end.

Lemma runPhase1Steps_sound : forall {n : nat} {mode mode' : StackMode} {L R L' R' : RLEStack},
  runPhase1Steps n mode L R = Some (mode', L', R') ->
  evalStackCfg mode (evalRLE L) (evalRLE R) -->*
  evalStackCfg mode' (evalRLE L') (evalRLE R').
Proof.
  induction n as [| n ih]; intros mode mode' L R L' R' h.
  - injection h as hm hL hR; subst mode' L' R'; apply evstep_refl.
  - cbn [runPhase1Steps] in h.
    destruct (stepPhase1 mode L R) as [[[m1 L1] R1] |] eqn:hstep; [| discriminate].
    exact (etrans (stepPhase1_sound hstep) (ih _ _ _ _ _ _ h)).
Qed.

Fixpoint runPhase1Sched (sched : list nat) (mode : StackMode) (L R : RLEStack)
  : option (StackMode * RLEStack * RLEStack) :=
  match sched with
  | [] => Some (mode, L, R)
  | chunk :: sched' =>
    match runPhase1Steps chunk mode L R with
    | Some (mode1, L1, R1) => runPhase1Sched sched' mode1 L1 R1
    | None => None
    end
  end.

Lemma runPhase1Sched_sound : forall {sched : list nat} {mode mode' : StackMode}
  {L R L' R' : RLEStack},
  runPhase1Sched sched mode L R = Some (mode', L', R') ->
  evalStackCfg mode (evalRLE L) (evalRLE R) -->*
  evalStackCfg mode' (evalRLE L') (evalRLE R').
Proof.
  induction sched as [| chunk sched' ih]; intros mode mode' L R L' R' h.
  - injection h as hm hL hR; subst mode' L' R'; apply evstep_refl.
  - cbn [runPhase1Sched] in h.
    destruct (runPhase1Steps chunk mode L R) as [[[m1 L1] R1] |] eqn:hstep; [| discriminate].
    exact (etrans (runPhase1Steps_sound hstep) (ih _ _ _ _ _ _ h)).
Qed.

Definition phase1_sched : list nat :=
  [1000; 1000; 1000; 1000; 1000; 1000; 1000; 1000; 1000; 1000; 1000; 728]%nat.

Lemma runPhase1All_eq :
  runPhase1Sched phase1_sched SM_F [] [(1, 1)] = Some (SM_F, expectedPhase1L, [(5, 1)]).
Proof.
  vm_compute; reflexivity.
Qed.

Strategy 1000 [midPrefix midPrefixRLE bodyStack bodyStackRLE expectedPhase1L].

Lemma phase1_reach :
  exists ks0 : list N, ks0 <> [] /\
    c0 -->* cfg_F (0 :: TowerA3 ks0 (bodyStack 56233 3)) [5].
Proof.
  assert (h_entry : c0 -->* cfg_F [] [1]).
  { change c0 with (cfg_AR [] []).
    exact (pev (rule_AR_nil [])). }
  assert (h_p1 : cfg_F [] [1] -->*
                 cfg_F (0 :: TowerA0Out ksInitOut (bodyStack 56233 3)) [5]).
  { pose proof (runPhase1Sched_sound runPhase1All_eq) as h_all.
    cbn [evalStackCfg] in h_all.
    rewrite evalRLE_expectedPhase1L in h_all.
    exact h_all. }
  pose proof (towerA3_absorb_towerA0Out ksInitOut [] (bodyStack 56233 3)) as h_abs.
  assert (h_ne : absorbTowerA0Out ksInitOut [] <> []).
  { apply absorbTowerA0Out_ne_nil. left; discriminate. }
  exists (absorbTowerA0Out ksInitOut []).
  split; [exact h_ne |].
  exact (etrans h_entry (etrans h_p1 h_abs)).
Qed.

(* Phase 2: 7,029 parametric body cycles from `Z = 56,233` down to `Z = 1` *)

Fixpoint runOpenSubCalls (n fuel : nat) (s : RLEStack) : option RLEStack :=
  match n with
  | 0%nat => Some s
  | S n' =>
    match runSubSim fuel true true s with
    | SSR_stepped s' => runOpenSubCalls n' fuel s'
    | SSR_halted => None
    | SSR_abort => None
    end
  end.

Lemma runOpenSubCalls_sound : forall {n fuel : nat} {s s' : RLEStack} {ks : list N},
  ks <> [] -> runOpenSubCalls n fuel s = Some s' ->
  forall (U : list N),
  exists ks' : list N, ks' <> [] /\
    TopStep (TowerA3 ks (evalRLE s ++ U)) (TowerA3 ks' (evalRLE s' ++ U)).
Proof.
  induction n as [| n ih]; intros fuel s s' ks hks h U.
  - injection h as hs'; subst s'.
    exists ks; split; [exact hks | apply topStep_refl].
  - cbn [runOpenSubCalls] in h.
    destruct (runSubSim fuel true true s) as [s1 | |] eqn:hsim; try discriminate.
    pose proof (runSubSim_sound_open U hsim) as h_sub.
    pose proof (towerA3_topStep ks hks h_sub) as h_top.
    pose proof (stepTowerAt_ne_nil 2 hks) as hne1.
    destruct (ih fuel s1 s' (stepTowerAt 2 ks) hne1 h U) as [ks' [hne' h_rest]].
    exists ks'; split; [exact hne' | exact (topStep_trans h_top h_rest)].
Qed.

Definition headForA (m : N) (U : list N) : list N :=
  if N.eqb m 0 then 3 :: 9 :: U
  else 3 :: 3 :: (nreplicate (8 * (m - 1) + 7) 0 ++ (6 :: U)).

Lemma calls1to10_m0_rle :
  runOpenSubCalls 10 50 [(0, 1); (3, 1); (0, 9); (6, 1)] =
  Some [(0, 1); (3, 2); (0, 2); (12, 1); (3, 1); (0, 1); (3, 1); (9, 1)].
Proof.
  vm_compute; reflexivity.
Qed.

Lemma calls1to10_mpos_rle :
  runOpenSubCalls 10 50 [(0, 1); (3, 1); (0, 10)] =
  Some [(0, 1); (3, 2); (0, 2); (12, 1); (3, 1); (0, 1); (3, 2)].
Proof.
  vm_compute; reflexivity.
Qed.

Lemma calls1to10_topStep (m : N) (U : list N) {ks : list N} (hks : ks <> []) :
  exists ks1 : list N, ks1 <> [] /\
    TopStep (TowerA3 ks (0 :: 3 :: (nreplicate (8 * m + 9) 0 ++ (6 :: U))))
            (TowerA3 ks1 (B3 3 (headForA m U))).
Proof.
  destruct (N.eqb m 0) eqn:hm0.
  - apply N.eqb_eq in hm0; subst m.
    destruct (runOpenSubCalls_sound hks calls1to10_m0_rle U) as [ks1 [hne1 htop]].
    exists ks1; split; [exact hne1 |].
    exact htop.
  - pose proof (proj1 (N.eqb_neq m 0) hm0) as hm_neq.
    set (V := nreplicate (8 * (m - 1) + 7) 0 ++ (6 :: U)).
    destruct (runOpenSubCalls_sound hks calls1to10_mpos_rle V) as [ks1 [hne1 htop]].
    exists ks1; split; [exact hne1 |].
    assert (h_rep : nreplicate (8 * m + 9) 0 ++ (6 :: U) =
                    nreplicate 10 0 ++ V).
    { unfold V.
      replace (8 * m + 9) with (10 + (8 * (m - 1) + 7)) by lia.
      rewrite nreplicate_add, app_assoc; reflexivity. }
    rewrite h_rep.
    unfold headForA; rewrite hm0.
    exact htop.
Qed.

Lemma partA_m0 (U R_bot : list N) :
  cfg_F (0 :: 3 :: 9 :: U) (9 :: R_bot) -->*
  cfg_F (0 :: U) (0 :: 1 :: 1 :: 5 :: 10 :: R_bot).
Proof.
  eapply etrans; [exact (pev (rule_F_zero_add_two (9 :: U) (9 :: R_bot) 1)) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_one_zero (9 :: U) (0 :: 10 :: R_bot))) |].
  cbn [bumpHead].
  pose proof (rule_F_step3_all U (4 :: 10 :: R_bot) 0 3) as h3.
  exact h3.
Qed.

Lemma partA_mpos (m' : N) (U R_bot : list N) :
  cfg_F (0 :: 3 :: 3 :: (nreplicate (8 * m' + 7) 0 ++ (6 :: U))) (9 :: R_bot) -->*
  cfg_F (0 :: U) (0 :: 1 :: 1 :: (16 * (m' + 1) + 5) :: 10 :: R_bot).
Proof.
  set (V := nreplicate (8 * m' + 7) 0 ++ (6 :: U)).
  eapply etrans; [exact (pev (rule_F_zero_add_two (3 :: V) (9 :: R_bot) 1)) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_one_zero (3 :: V) (0 :: 10 :: R_bot))) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_F_add_three V (4 :: 10 :: R_bot) 0)) |].
  cbn [bumpHead].
  assert (hV : 0 :: V = nreplicate (4 * (2 * m' + 1) + 3 + 1) 0 ++ (6 :: U)).
  { replace (4 * (2 * m' + 1) + 3 + 1) with (1 + (8 * m' + 7)) by lia.
    rewrite nreplicate_add. unfold V; reflexivity. }
  rewrite hV.
  eapply etrans; [exact (rule_F_zero4_all (2 * m' + 1) 3 (6 :: U) 5 (10 :: R_bot)) |].
  set (d1 := 5 + 8 * (2 * m' + 1)).
  change (cfg_F (0 :: 0 :: 0 :: 0 :: 6 :: U) (0 :: d1 :: 10 :: R_bot) -->*
          cfg_F (0 :: U) (0 :: 1 :: 1 :: (16 * (m' + 1) + 5) :: 10 :: R_bot)).
  eapply etrans; [exact (pev (rule_F_zero_zero (0 :: 0 :: 6 :: U) (0 :: d1 :: 10 :: R_bot))) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_F_two (0 :: 6 :: U) (0 :: 0 :: d1 :: 10 :: R_bot))) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_add_two_zero (6 :: U) (1 :: 0 :: d1 :: 10 :: R_bot) 0)) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_zero_zero (6 :: U) (3 :: 0 :: d1 :: 10 :: R_bot))) |].
  cbn [bumpHead].
  eapply etrans; [exact (rule_AR_step2_all (9 :: U) (0 :: d1 :: 10 :: R_bot) 0 2) |].
  change (nreplicate 2 0 ++ (9 :: U)) with (0 :: 0 :: 9 :: U).
  eapply etrans; [exact (pev (rule_AR_zero_zero (0 :: 9 :: U) (0 :: d1 :: 10 :: R_bot))) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_one_cons (3 :: 9 :: U) (10 :: R_bot) d1)) |].
  eapply etrans; [exact (pev (rule_AR_add_two_zero (9 :: U) ((d1 + 1) :: 10 :: R_bot) 1)) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_one_zero (9 :: U) ((d1 + 1 + 1 + 1) :: 10 :: R_bot))) |].
  cbn [bumpHead].
  assert (hd : d1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 16 * (m' + 1) + 4) by (unfold d1; lia).
  rewrite hd.
  pose proof (rule_F_step3_all U ((16 * (m' + 1) + 4) :: 10 :: R_bot) 0 3) as h14.
  change (stepF3Right 3 ((16 * (m' + 1) + 4) :: 10 :: R_bot))
    with (0 :: 1 :: 1 :: (16 * (m' + 1) + 4 + 1) :: 10 :: R_bot) in h14.
  replace (16 * (m' + 1) + 4 + 1) with (16 * (m' + 1) + 5) in h14 by lia.
  exact h14.
Qed.

Lemma partA_all (m : N) (U R_bot : list N) :
  cfg_F (0 :: headForA m U) (9 :: R_bot) -->*
  cfg_F (0 :: U) (0 :: 1 :: 1 :: (16 * m + 5) :: 10 :: R_bot).
Proof.
  destruct (N.eqb m 0) eqn:hm0.
  - apply N.eqb_eq in hm0; subst m.
    exact (partA_m0 U R_bot).
  - pose proof (proj1 (N.eqb_neq m 0) hm0) as hm_neq.
    unfold headForA; rewrite hm0.
    replace (16 * m + 5) with (16 * ((m - 1) + 1) + 5) by lia.
    exact (partA_mpos (m - 1) U R_bot).
Qed.

Definition midRightTailRLE : RLEStack :=
  [ (9, 1); (0, 1); (105, 1); (1, 1); (409, 1); (9, 1); (1, 3); (10, 1);
    (8, 1); (1, 3); (97, 1); (1, 1); (1769, 1); (1, 1); (118217, 1); (9, 1);
    (1, 4); (9, 1); (1, 1); (9, 1); (1, 26); (9, 1); (1, 1); (9, 1);
    (1, 114); (9, 1); (1, 1); (9, 1); (1, 465); (10, 1); (8, 1); (1, 3);
    (5641, 1); (1, 1) ].

Strategy 1000 [midRightTailRLE].

Lemma partB_rle :
  runStepsRLE 189 true true true SM_F (pushRun 0 1 midPrefixRLE) [(0, 1); (1, 2)] =
  GSR_stepped SM_AR [(0, 1)]
    (pushRun 0 1 (pushRun 3 1 (pushRun 0 1 (pushRun 18 1 midRightTailRLE)))).
Proof.
  vm_compute; reflexivity.
Qed.

Lemma partB_step (L_bot R_bot' : list N) :
  cfg_F (0 :: (midPrefix ++ L_bot)) (0 :: 1 :: 1 :: R_bot') -->*
  cfg_AR (0 :: L_bot) (0 :: 3 :: 0 :: 18 :: (evalRLE midRightTailRLE ++ R_bot')).
Proof.
  pose proof (runStepsRLE_sound_step L_bot R_bot' partB_rle) as h.
  cbn [evalStackCfg] in h.
  rewrite evalRLEWith_pushOne, evalRLEWith_pushOne, evalRLEWith_pushOne,
          evalRLEWith_pushOne, evalRLEWith_pushOne, !evalRLEWith_true in h.
  change (evalRLE midPrefixRLE) with midPrefix in h.
  exact h.
Qed.

Lemma partC_step (k : N) (R_tail : list N) :
  cfg_AR [0; 3 * (k + 1); 2] (0 :: 3 :: 0 :: 18 :: R_tail) -->*
  cfg_AR [3 * (k + 2); 2] (28 :: R_tail).
Proof.
  eapply etrans; [exact (pev (rule_AR_zero_zero [3 * (k + 1); 2] (3 :: 0 :: 18 :: R_tail))) |].
  cbn [bumpHead].
  assert (hk1 : 3 * (k + 1) + 1 + 1 + 1 = 3 * (k + 2)) by lia.
  rewrite hk1.
  eapply etrans; [exact (rule_AR_step2_all [3 * (k + 2); 2] (0 :: 18 :: R_tail) 0 2) |].
  change (nreplicate 2 0 ++ [3 * (k + 2); 2]) with [0; 0; 3 * (k + 2); 2].
  eapply etrans; [exact (pev (rule_AR_zero_zero [0; 3 * (k + 2); 2] (0 :: 18 :: R_tail))) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_one_cons [3; 3 * (k + 2); 2] R_tail 18)) |].
  eapply etrans; [exact (pev (rule_AR_add_two_zero [3 * (k + 2); 2] (19 :: R_tail) 1)) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_one_zero [3 * (k + 2); 2] (21 :: R_tail))) |].
  cbn [bumpHead].
  replace (3 * (k + 2)) with (3 * (k + 2) + 0) at 1 by lia.
  eapply etrans; [exact (rule_F_step3_all [2] (25 :: R_tail) 0 (k + 2)) |].
  replace (k + 2) with ((k + 1) + 1) at 1 by lia.
  rewrite stepF3Right_succ.
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_F_zero_add_two []
    (0 :: (nreplicate (k + 1) 1 ++ (26 :: R_tail))) 0)) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_zero_zero []
    (0 :: 1 :: (nreplicate (k + 1) 1 ++ (26 :: R_tail))))) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_one_cons [2]
    (nreplicate (k + 1) 1 ++ (26 :: R_tail)) 1)) |].
  eapply etrans; [exact (pev (rule_AR_add_two_zero []
    (2 :: (nreplicate (k + 1) 1 ++ (26 :: R_tail))) 0)) |].
  cbn [bumpHead].
  eapply etrans; [exact (pev (rule_AR_zero_zero []
    (4 :: (nreplicate (k + 1) 1 ++ (26 :: R_tail))))) |].
  cbn [bumpHead].
  eapply etrans; [exact (rule_AR_step2_all [2]
    (nreplicate (k + 1) 1 ++ (26 :: R_tail)) 1 2) |].
  change (nreplicate 2 0 ++ [2]) with [0; 0; 2].
  assert (h_rep : 1 :: (nreplicate (k + 1) 1 ++ (26 :: R_tail)) =
                  nreplicate ((k + 1) + 1) 1 ++ (26 :: R_tail)).
  { symmetry.
    replace ((k + 1) + 1) with (1 + (k + 1)) at 1 by lia.
    rewrite nreplicate_add; reflexivity. }
  rewrite h_rep.
  eapply etrans; [exact (rule_AR_ones_all (k + 1) 0 [2] (26 :: R_tail)) |].
  rewrite N.add_0_l.
  eapply etrans; [exact (pev (rule_AR_one_cons [0; 3 * (k + 1); 2] R_tail 26)) |].
  eapply etrans; [exact (pev (rule_AR_zero_zero [3 * (k + 1); 2] (27 :: R_tail))) |].
  cbn [bumpHead].
  rewrite hk1.
  apply evstep_refl.
Qed.

Lemma partD_rle :
  runStepsRLE 83 true true true SM_AR [] (pushRun 28 1 midRightTailRLE) =
  GSR_stepped SM_AR (pushRun 0 1 (pushRun 3 1 midPrefixRLE)) [(1, 1)].
Proof.
  vm_compute; reflexivity.
Qed.

Lemma partD_step (L_bot R_bot' : list N) :
  cfg_AR L_bot (28 :: (evalRLE midRightTailRLE ++ R_bot')) -->*
  cfg_AR (0 :: 3 :: (midPrefix ++ L_bot)) (1 :: R_bot').
Proof.
  pose proof (runStepsRLE_sound_step L_bot R_bot' partD_rle) as h.
  cbn [evalStackCfg] in h.
  rewrite evalRLEWith_pushOne, evalRLEWith_pushOne, evalRLEWith_pushOne,
          !evalRLEWith_true in h.
  change (evalRLE midPrefixRLE) with midPrefix in h.
  exact h.
Qed.

Lemma partE_step (m : N) (W R_bot : list N) :
  cfg_AR (0 :: 3 :: W) (1 :: (16 * m + 5) :: 10 :: R_bot) -->*
  cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 3 :: (nreplicate (8 * m + 1) 0 ++ (6 :: W)))
    (0 :: R_bot).
Proof.
  eapply etrans; [exact (pev (rule_AR_one_cons (0 :: 3 :: W) (10 :: R_bot) (16 * m + 5))) |].
  eapply etrans; [exact (pev (rule_AR_zero_zero (3 :: W) ((16 * m + 5 + 1) :: 10 :: R_bot))) |].
  cbn [bumpHead].
  replace (16 * m + 5 + 1 + 1) with (2 * (8 * m + 3) + 1) by lia.
  eapply etrans; [exact (rule_AR_step2_all (6 :: W) (10 :: R_bot) 1 (8 * m + 3)) |].
  assert (hrep1 : nreplicate (8 * m + 3) 0 ++ (6 :: W) =
                  0 :: 0 :: (nreplicate (8 * m + 1) 0 ++ (6 :: W))).
  { replace (8 * m + 3) with (2 + (8 * m + 1)) by lia.
    rewrite nreplicate_add; reflexivity. }
  rewrite hrep1.
  set (V := nreplicate (8 * m + 1) 0 ++ (6 :: W)).
  eapply etrans; [exact (pev (rule_AR_one_cons (0 :: 0 :: V) R_bot 10)) |].
  eapply etrans; [exact (pev (rule_AR_zero_zero (0 :: V) (11 :: R_bot))) |].
  cbn [bumpHead].
  pose proof (rule_AR_step2_all (3 :: V) R_bot 0 6) as h6.
  exact h6.
Qed.

Lemma call11_core_subStep (m k : N) :
  SubStep (headForA m (midPrefix ++ [3 * (k + 1); 2]))
          (bodyStack (8 * m + 1) (3 * (k + 2))).
Proof.
  intros R_bot.
  set (U := midPrefix ++ [3 * (k + 1); 2]).
  set (R_bot' := (16 * m + 5) :: 10 :: R_bot).
  eapply etrans; [exact (partA_all m U R_bot) |].
  eapply etrans; [exact (partB_step [3 * (k + 1); 2] R_bot') |].
  eapply etrans; [exact (partC_step k (evalRLE midRightTailRLE ++ R_bot')) |].
  eapply etrans; [exact (partD_step [3 * (k + 2); 2] R_bot') |].
  exact (partE_step m (midPrefix ++ [3 * (k + 2); 2]) R_bot).
Qed.

Lemma call11_subStep (m k : N) :
  SubStep (B3 3 (headForA m (midPrefix ++ [3 * (k + 1); 2])))
          (A0 4 (bodyStack (8 * m + 1) (3 * (k + 2)))).
Proof.
  exact (subStep_B3 3 (call11_core_subStep m k)).
Qed.

Lemma body_cycle_step (m k : N) {ks : list N} (hks : ks <> []) :
  exists ks' : list N, ks' <> [] /\
    TopStep (TowerA3 ks (bodyStack (8 * m + 9) (3 * (k + 1))))
            (TowerA3 ks' (bodyStack (8 * m + 1) (3 * (k + 2)))).
Proof.
  destruct (calls1to10_topStep m (midPrefix ++ [3 * (k + 1); 2]) hks)
    as [ks1 [hne1 h10]].
  pose proof (towerA3_topStep ks1 hne1 (call11_subStep m k)) as h11.
  pose proof (towerA3_absorb_A0 4 (stepTowerAt 2 ks1)
                (bodyStack (8 * m + 1) (3 * (k + 2)))) as h12.
  exists (absorbA0 4 (stepTowerAt 2 ks1)).
  split.
  - apply absorbA0_ne_nil.
  - exact (topStep_trans h10 (topStep_trans h11 h12)).
Qed.

Lemma body_cycles_all (n : N) : forall (m0 k0 : N) {ks : list N}, ks <> [] ->
  exists ks' : list N, ks' <> [] /\
    TopStep (TowerA3 ks (bodyStack (8 * (m0 + n) + 1) (3 * (k0 + 1))))
            (TowerA3 ks' (bodyStack (8 * m0 + 1) (3 * (k0 + n + 1)))).
Proof.
  induction n using N_peano_ind; intros m0 k0 ks hks.
  - rewrite !N.add_0_r.
    exists ks; split; [exact hks | apply topStep_refl].
  - replace (8 * (m0 + (n + 1)) + 1) with (8 * (m0 + n) + 9) by lia.
    destruct (body_cycle_step (m0 + n) k0 hks) as [ks1 [hne1 hstep]].
    replace (3 * (k0 + 2)) with (3 * ((k0 + 1) + 1)) in hstep by lia.
    destruct (IHn m0 (k0 + 1) ks1 hne1) as [ks' [hne' hrest]].
    replace (k0 + 1 + n + 1) with (k0 + (n + 1) + 1) in hrest by lia.
    exists ks'; split; [exact hne' | exact (topStep_trans hstep hrest)].
Qed.

(* Phase 3: 186 SubStep calls from `bodyStack 1 21090` to `SubHalt` *)

Fixpoint runPhase3 (fuel : nat) (s : RLEStack) : bool :=
  match fuel with
  | 0%nat => false
  | S fuel' =>
    let p := peelA3Loop 35 [] s in
    match runSubSim 400 false true (snd p) with
    | SSR_stepped s' => runPhase3 fuel' s'
    | SSR_halted => true
    | SSR_abort => false
    end
  end.

Lemma runPhase3_eq : runPhase3 186 (bodyStackRLE 1 21090) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Lemma runPhase3_sound : forall (fuel : nat) (s : RLEStack),
  runPhase3 fuel s = true ->
  forall (ks : list N), ks <> [] ->
  halts tm (cfg_F (0 :: TowerA3 ks (evalRLE s)) [5]).
Proof.
  induction fuel as [| fuel ih]; intros s h ks hks; [discriminate |].
  cbn [runPhase3] in h.
  pose proof (evalRLE_peelA3Loop 35 [] s) as hpeel.
  cbn [TowerA3] in hpeel.
  set (ks_p := fst (peelA3Loop 35 [] s)) in *.
  set (s_in := snd (peelA3Loop 35 [] s)) in *.
  assert (h_tower : TowerA3 ks (evalRLE s) = TowerA3 (ks_p ++ ks) (evalRLE s_in)).
  { rewrite <- hpeel, <- TowerA3_append; reflexivity. }
  assert (hne_all : ks_p ++ ks <> []).
  { intros hnil; apply app_eq_nil in hnil; destruct hnil as [_ hk]; exact (hks hk). }
  rewrite h_tower.
  destruct (runSubSim 400 false true s_in) as [s' | |] eqn:hsim; try discriminate.
  - pose proof (towerA3_topStep (ks_p ++ ks) hne_all (runSubSim_sound_closed hsim)) as h_top.
    pose proof (ih s' h (stepTowerAt 2 (ks_p ++ ks)) (stepTowerAt_ne_nil 2 hne_all)) as h_rest.
    eapply halts_evstep; [exact h_rest | exact h_top].
  - exact (towerA3_halt (ks_p ++ ks) hne_all (runSubSim_sound_halt hsim)).
Qed.

Theorem halt: halts tm c0.
Proof.
  destruct phase1_reach as [ks0 [hks0 h_p1]].
  destruct (body_cycles_all 7029 0 0 hks0) as [ks1 [hks1 h_p2]].
  change (8 * (0 + 7029) + 1) with 56233 in h_p2.
  change (3 * (0 + 1)) with 3 in h_p2.
  change (8 * 0 + 1) with 1 in h_p2.
  change (3 * (0 + 7029 + 1)) with 21090 in h_p2.
  rewrite <- (evalRLE_bodyStackRLE 1 21090) in h_p2.
  pose proof (runPhase3_sound 186 (bodyStackRLE 1 21090) runPhase3_eq ks1 hks1) as h_p3.
  eapply halts_evstep; [exact h_p3 | exact (etrans h_p1 h_p2)].
Qed.

End TM1.
