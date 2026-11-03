(* 1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat ZifyN NArith PeanoNat Bool String Lists.Streams List.
Import ListNotations.

Open Scope list.
Open Scope sym.

Definition tm : TM := Eval compute in
  (TM_from_str "1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope N_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ========================================================================== *)
(* Section 0: Generic Helpers                                                 *)
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

Lemma iter_sound {A : Type} (f : A -> A) (ev : A -> Q * tape)
  (hf : forall s, ev s -->* ev (f s)) (n : nat) (s : A) :
  ev s -->* ev (iter f n s).
Proof.
  revert s.
  induction n as [| n ih]; intro s; simpl; [apply evstep_refl |].
  exact (etrans (hf s) (ih (f s))).
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

Lemma list_ind2 {A : Type} (P : list A -> Prop)
  (Hnil : P [])
  (H1 : forall x, P [x])
  (H2 : forall x y xs, P (y :: xs) -> P xs -> P (x :: y :: xs)) :
  forall xs, P xs.
Proof.
  assert (Hboth : forall xs, P xs /\ forall x, P (x :: xs)).
  { induction xs as [| y xs [ih1 ih2]]; split.
    - exact Hnil.
    - exact H1.
    - exact (ih2 y).
    - intro x. exact (H2 x y xs (ih2 y) ih1). }
  intro xs; apply Hboth.
Qed.

(* ========================================================================== *)
(* Section 1: Unary-Run Stack Encoding & Elementary TM Rules                  *)
(* ========================================================================== *)

Inductive MItem : Type :=
  | MZero
  | MRun (d : N).

Definition mitem_eqb (x y : MItem) : bool :=
  match x, y with
  | MZero, MZero => true
  | MRun d1, MRun d2 => N.eqb d1 d2
  | _, _ => false
  end.

Lemma mitem_eqb_eq (x y : MItem) : mitem_eqb x y = true <-> x = y.
Proof.
  destruct x as [| d1], y as [| d2]; simpl; split; intro h;
    try discriminate; try reflexivity.
  - apply N.eqb_eq in h; subst; reflexivity.
  - injection h as h; subst; apply N.eqb_refl.
Qed.

Fixpoint encM (M : list MItem) : side :=
  match M with
  | [] => 0inf%sym
  | MZero :: M' => 0%sym >> encM M'
  | MRun d :: M' => [1%sym] ^^ (S (N.to_nat d)) *> (0%sym >> encM M')
  end.

Definition bumpM (M : list MItem) : list MItem :=
  match M with
  | [] => [MRun 0]
  | MZero :: M' => MRun 0 :: M'
  | MRun d :: M' => MRun (d + 1) :: M'
  end.

Lemma encM_run_add1 (d : N) (M : list MItem) :
  encM (MRun (d + 1) :: M) = 1%sym >> encM (MRun d :: M).
Proof.
  unfold encM; fold encM.
  replace (N.to_nat (d + 1)) with (S (N.to_nat d)) by lia.
  reflexivity.
Qed.

Lemma encM_run_add3 (d : N) (M : list MItem) :
  encM (MRun (d + 3) :: M) = 1%sym >> 1%sym >> 1%sym >> encM (MRun d :: M).
Proof.
  unfold encM; fold encM.
  replace (N.to_nat (d + 3)) with (S (S (S (N.to_nat d)))) by lia.
  reflexivity.
Qed.

Lemma encM_run_add4 (d : N) (M : list MItem) :
  encM (MRun (d + 4) :: M) = 1%sym >> 1%sym >> 1%sym >> 1%sym >> encM (MRun d :: M).
Proof.
  unfold encM; fold encM.
  replace (N.to_nat (d + 4)) with (S (S (S (S (N.to_nat d))))) by lia.
  reflexivity.
Qed.

Lemma encM_bumpM (M : list MItem) :
  1%sym >> encM M = encM (bumpM M).
Proof.
  destruct M as [| [| d] M'].
  - simpl. rewrite <- const_unfold. reflexivity.
  - reflexivity.
  - symmetry. apply encM_run_add1.
Qed.

Definition cfgBB (L R : list MItem) : Q * tape :=
  B;; encM L {{0%sym}} encM R.

Definition cfgCB (L R : list MItem) : Q * tape :=
  C;; encM L {{0%sym}} encM R.

Definition cfgDL (L R : list MItem) : Q * tape :=
  encM L <{{D}} encM R.

Lemma step_BB_nil (R : list MItem) :
  cfgBB [] R -->+ cfgCB [] (bumpM R).
Proof.
  unfold cfgBB, cfgCB. rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_BB_zero (L1 R : list MItem) :
  cfgBB (MZero :: L1) R -->+ cfgCB L1 (bumpM R).
Proof.
  unfold cfgBB, cfgCB. rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_BB_run0 (L1 R : list MItem) :
  cfgBB (MRun 0 :: L1) R -->+ cfgBB L1 (MRun 0 :: R).
Proof.
  unfold cfgBB. simpl. start_progress.
Qed.

Lemma step_BB_run1 (L1 R : list MItem) :
  cfgBB (MRun 1 :: L1) R -->+ cfgBB L1 (MRun 0 :: bumpM R).
Proof.
  unfold cfgBB.
  change (encM (MRun 0 :: bumpM R)) with (1%sym >> 0%sym >> encM (bumpM R)).
  rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_BB_run2 (L1 R : list MItem) :
  cfgBB (MRun 2 :: L1) R -->+ cfgDL L1 (MRun 0 :: MRun 0 :: bumpM R).
Proof.
  unfold cfgBB, cfgDL.
  change (encM (MRun 0 :: MRun 0 :: bumpM R)) with (1%sym >> 0%sym >> 1%sym >> 0%sym >> encM (bumpM R)).
  rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_BB_run3 (L1 R : list MItem) :
  cfgBB (MRun 3 :: L1) R -->+ cfgBB (MRun 0 :: MZero :: MZero :: L1) (bumpM R).
Proof.
  unfold cfgBB. rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_BB_run_ge4 (d : N) (L1 R : list MItem) :
  cfgBB (MRun (d + 4) :: L1) R -->+ cfgBB (MRun 0 :: MZero :: MRun d :: L1) (bumpM R).
Proof.
  unfold cfgBB. rewrite encM_run_add4, <- encM_bumpM. simpl. start_progress.
Qed.

Lemma cyc_R_A (k : nat) (V s : side) :
  A;; (0%sym >> V) {{0%sym}} ([1%sym]^^k *> s) -->*
  A;; (0%sym >> ([0%sym]^^k *> V)) {{0%sym}} s.
Proof.
  revert V.
  induction k as [| k ih]; intro V.
  - finish.
  - assert (h1 :
      A;; (0%sym >> V) {{0%sym}} ([1%sym]^^(S k) *> s) -->+
      A;; (0%sym >> 0%sym >> V) {{0%sym}} ([1%sym]^^k *> s)).
    { simpl. start_progress. }
    pose proof (ih (0%sym >> V)) as h2.
    change (0%sym >> V) with ([0%sym] *> V) in h2; rewrite lpow_shift' in h2.
    exact (pev (pe_trans h1 h2)).
Qed.

Lemma exit_R_A (W R1 : list MItem) :
  A;; (0%sym >> 0%sym >> 0%sym >> encM W) {{0%sym}} (0%sym >> encM R1) -->+
  cfgCB (MRun 0 :: MRun 0 :: W) R1.
Proof.
  unfold cfgCB. simpl. start_progress.
Qed.

Lemma encM_replicate_zero (k : nat) (L : list MItem) :
  [0%sym]^^k *> encM L = encM (replicate k MZero ++ L).
Proof.
  induction k as [| k ih]; simpl; [reflexivity | rewrite ih; reflexivity].
Qed.

Lemma encM_nreplicate_zero (n : N) (L : list MItem) :
  [0%sym]^^(N.to_nat n) *> encM L = encM (nreplicate n MZero ++ L).
Proof.
  apply encM_replicate_zero.
Qed.

Lemma step_DL_run0 (L1 R : list MItem) :
  cfgDL (MRun 0 :: L1) R -->+ cfgBB L1 (bumpM R).
Proof.
  unfold cfgDL, cfgBB. rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_DL_run1 (L1 R : list MItem) :
  cfgDL (MRun 1 :: L1) R -->+ cfgDL L1 (MRun 0 :: bumpM R).
Proof.
  unfold cfgDL.
  change (encM (MRun 0 :: bumpM R)) with (1%sym >> 0%sym >> encM (bumpM R)).
  rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_DL_run2 (d0 : N) (L1 R1 : list MItem) :
  cfgDL (MRun 2 :: L1) (MRun d0 :: R1) -->+
  cfgCB (MRun 0 :: MRun 0 :: nreplicate (d0 + 1) MZero ++ L1) R1.
Proof.
  unfold cfgDL.
  assert (h1 :
    encM (MRun 2 :: L1) <{{D}} encM (MRun d0 :: R1) -->+
    A;; (0%sym >> 0%sym >> 0%sym >> encM L1) {{0%sym}}
      ([1%sym]^^(S (N.to_nat d0)) *> (0%sym >> encM R1))).
  { simpl. start_progress. }
  pose proof (cyc_R_A (S (N.to_nat d0)) (0%sym >> 0%sym >> encM L1) (0%sym >> encM R1)) as h2.
  pose proof (pe_trans h1 h2) as h12.
  change (0%sym >> 0%sym >> encM L1) with ([0%sym] *> (0%sym >> encM L1)) in h12;
    rewrite lpow_shift' in h12.
  change (0%sym >> encM L1) with ([0%sym] *> encM L1) in h12;
    rewrite lpow_shift' in h12.
  replace (S (N.to_nat d0)) with (N.to_nat (d0 + 1)) in h12 by lia.
  rewrite encM_nreplicate_zero in h12.
  exact (ptrans h12 (exit_R_A (nreplicate (d0 + 1) MZero ++ L1) R1)).
Qed.

Lemma step_CB_nil (L : list MItem) :
  cfgCB L [] -->+ cfgDL (bumpM L) [MRun 0].
Proof.
  unfold cfgCB, cfgDL. rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_CB_zero (L R1 : list MItem) :
  cfgCB L (MZero :: R1) -->+ cfgDL (bumpM L) (bumpM R1).
Proof.
  unfold cfgCB, cfgDL. rewrite <- (encM_bumpM L), <- (encM_bumpM R1). simpl. start_progress.
Qed.

Lemma step_CB_run0_nil (L : list MItem) :
  cfgCB L [MRun 0] -->+ cfgBB (MRun 0 :: bumpM L) [].
Proof.
  unfold cfgCB, cfgBB.
  change (encM (MRun 0 :: bumpM L)) with (1%sym >> 0%sym >> encM (bumpM L)).
  rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_CB_run0_zero (L R2 : list MItem) :
  cfgCB L (MRun 0 :: MZero :: R2) -->+ cfgBB (MRun 0 :: bumpM L) R2.
Proof.
  unfold cfgCB, cfgBB.
  change (encM (MRun 0 :: bumpM L)) with (1%sym >> 0%sym >> encM (bumpM L)).
  rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_CB_run0_run0 (L R2 : list MItem) :
  cfgCB L (MRun 0 :: MRun 0 :: R2) -->+ cfgBB (MRun 0 :: MZero :: bumpM L) R2.
Proof.
  unfold cfgCB, cfgBB.
  change (encM (MRun 0 :: MZero :: bumpM L)) with (1%sym >> 0%sym >> 0%sym >> encM (bumpM L)).
  rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_CB_run0_run_pos (d2 : N) (L R2 : list MItem) :
  cfgCB L (MRun 0 :: MRun (d2 + 1) :: R2) -->+
  cfgCB (MRun 0 :: MRun 0 :: nreplicate d2 MZero ++ bumpM L) R2.
Proof.
  unfold cfgCB.
  assert (h1 :
    (C;; encM L {{0%sym}} encM (MRun 0 :: MRun (d2 + 1) :: R2)) -->+
    (A;; (0%sym >> 0%sym >> encM (bumpM L)) {{0%sym}}
      ([1%sym]^^(S (N.to_nat d2)) *> (0%sym >> encM R2)))).
  { rewrite <- (encM_bumpM L).
    unfold encM at 2; fold encM.
    replace (N.to_nat (d2 + 1)) with (S (N.to_nat d2)) by lia.
    simpl. start_progress. }
  pose proof (cyc_R_A (S (N.to_nat d2)) (0%sym >> encM (bumpM L)) (0%sym >> encM R2)) as h2.
  pose proof (pe_trans h1 h2) as h12.
  change (0%sym >> encM (bumpM L)) with ([0%sym] *> encM (bumpM L)) in h12;
    rewrite lpow_shift' in h12.
  change ([0%sym]^^(S (N.to_nat d2)) *> encM (bumpM L))
    with (0%sym >> ([0%sym]^^(N.to_nat d2) *> encM (bumpM L))) in h12.
  rewrite encM_nreplicate_zero in h12.
  exact (ptrans h12 (exit_R_A (nreplicate d2 MZero ++ bumpM L) R2)).
Qed.

Lemma step_CB_run1 (L R1 : list MItem) :
  cfgCB L (MRun 1 :: R1) -->+ cfgCB (MRun 0 :: bumpM L) R1.
Proof.
  unfold cfgCB.
  change (encM (MRun 0 :: bumpM L)) with (1%sym >> 0%sym >> encM (bumpM L)).
  rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_CB_run2 (L R1 : list MItem) :
  cfgCB L (MRun 2 :: R1) -->+ cfgBB (bumpM L) (MRun 0 :: MZero :: R1).
Proof.
  unfold cfgCB, cfgBB. rewrite <- encM_bumpM. simpl. start_progress.
Qed.

Lemma step_CB_run_ge3 (d : N) (L R1 : list MItem) :
  cfgCB L (MRun (d + 3) :: R1) -->+ cfgBB (bumpM L) (MRun 0 :: MRun d :: R1).
Proof.
  unfold cfgCB, cfgBB. rewrite encM_run_add3, <- encM_bumpM. simpl. start_progress.
Qed.

Lemma init_to_BB : c0 -->+ cfgBB [MRun 0] [].
Proof.
  unfold c0, tape0, cfgBB. simpl. start_progress.
Qed.

Lemma step_DL_zero_halt (L1 R1 : list MItem) :
  cfgDL (MZero :: L1) (MRun 0 :: R1) -->+
  E;; (0%sym >> encM L1) {{1%sym}} (0%sym >> encM R1).
Proof.
  unfold cfgDL. simpl. start_progress.
Qed.

Lemma step_BB_r0_r1 (L R : list MItem) :
  cfgBB (MRun 0 :: MRun 1 :: L) R -->+ cfgBB L (MRun 0 :: MRun 1 :: R).
Proof.
  exact (ptrans (step_BB_run0 (MRun 1 :: L) R) (step_BB_run1 L (MRun 0 :: R))).
Qed.

Lemma step_BB_r1_r0_r1_comm (L R : list MItem) :
  cfgBB (MRun 1 :: MRun 0 :: MRun 1 :: L) (MRun 0 :: MRun 1 :: R) -->+
  cfgBB L (MRun 0 :: MRun 1 :: MRun 0 :: MRun 1 :: MRun 1 :: R).
Proof.
  exact (ptrans (step_BB_run1 (MRun 0 :: MRun 1 :: L) (MRun 0 :: MRun 1 :: R))
    (ptrans (step_BB_run0 (MRun 1 :: L) (MRun 0 :: MRun 1 :: MRun 1 :: R))
      (step_BB_run1 L (MRun 0 :: MRun 0 :: MRun 1 :: MRun 1 :: R)))).
Qed.

(* ========================================================================== *)
(* Section 2: Elementary Simulator (`SymMode`, `stepElemM`, `runElemFast`)    *)
(* ========================================================================== *)

Inductive SymMode : Type :=
  | BB
  | DL
  | CB
  | HALT.

Definition evalM (s : SymMode * list MItem * list MItem) : Q * tape :=
  let '(m, ls, rs) := s in
  match m with
  | BB => cfgBB ls rs
  | DL => cfgDL ls rs
  | CB => cfgCB ls rs
  | HALT => cfgDL ls rs
  end.

Definition stepElemM (s : SymMode * list MItem * list MItem) : SymMode * list MItem * list MItem :=
  let '(m, ls, rs) := s in
  match m with
  | BB =>
    match ls with
    | [] => (CB, [], bumpM rs)
    | MZero :: L1 => (CB, L1, bumpM rs)
    | MRun d :: L1 =>
      if d =? 0 then (BB, L1, MRun 0 :: rs)
      else if d =? 1 then (BB, L1, MRun 0 :: bumpM rs)
      else if d =? 2 then (DL, L1, MRun 0 :: MRun 0 :: bumpM rs)
      else if d =? 3 then (BB, MRun 0 :: MZero :: MZero :: L1, bumpM rs)
      else (BB, MRun 0 :: MZero :: MRun (d - 4) :: L1, bumpM rs)
    end
  | DL =>
    match ls with
    | [] => s
    | MZero :: L1 => (HALT, MZero :: L1, rs)
    | MRun d :: L1 =>
      if d =? 0 then (BB, L1, bumpM rs)
      else if d =? 1 then (DL, L1, MRun 0 :: bumpM rs)
      else if d =? 2 then
        match rs with
        | MRun d0 :: R1 => (CB, MRun 0 :: MRun 0 :: (nreplicate (d0 + 1) MZero ++ L1), R1)
        | _ => s
        end
      else s
    end
  | CB =>
    match rs with
    | [] => (DL, bumpM ls, [MRun 0])
    | MZero :: R1 => (DL, bumpM ls, bumpM R1)
    | MRun d :: R1 =>
      if d =? 0 then
        match R1 with
        | [] => (BB, MRun 0 :: bumpM ls, [])
        | MZero :: R2 => (BB, MRun 0 :: bumpM ls, R2)
        | MRun d2 :: R2 =>
          if d2 =? 0 then (BB, MRun 0 :: MZero :: bumpM ls, R2)
          else (CB, MRun 0 :: MRun 0 :: (nreplicate (d2 - 1) MZero ++ bumpM ls), R2)
        end
      else if d =? 1 then (CB, MRun 0 :: bumpM ls, R1)
      else if d =? 2 then (BB, bumpM ls, MRun 0 :: MZero :: R1)
      else (BB, bumpM ls, MRun 0 :: MRun (d - 3) :: R1)
    end
  | HALT => s
  end.

Lemma stepElemM_sound (s : SymMode * list MItem * list MItem) :
  evalM s -->* evalM (stepElemM s).
Proof.
  destruct s as [[m ls] rs].
  destruct m; simpl.
  - (* BB *)
    destruct ls as [| [| d] L1].
    + exact (pev (step_BB_nil rs)).
    + exact (pev (step_BB_zero L1 rs)).
    + destruct (N.eqb_spec d 0) as [-> | h0]; [exact (pev (step_BB_run0 L1 rs)) |].
      destruct (N.eqb_spec d 1) as [-> | h1]; [exact (pev (step_BB_run1 L1 rs)) |].
      destruct (N.eqb_spec d 2) as [-> | h2]; [exact (pev (step_BB_run2 L1 rs)) |].
      destruct (N.eqb_spec d 3) as [-> | h3]; [exact (pev (step_BB_run3 L1 rs)) |].
      replace d with ((d - 4) + 4) at 1 by lia.
      exact (pev (step_BB_run_ge4 (d - 4) L1 rs)).
  - (* DL *)
    destruct ls as [| [| d] L1]; [apply evstep_refl | apply evstep_refl |].
    destruct (N.eqb_spec d 0) as [-> | h0]; [exact (pev (step_DL_run0 L1 rs)) |].
    destruct (N.eqb_spec d 1) as [-> | h1]; [exact (pev (step_DL_run1 L1 rs)) |].
    destruct (N.eqb_spec d 2) as [-> | h2].
    + destruct rs as [| [| d0] R1]; [apply evstep_refl | apply evstep_refl |].
      exact (pev (step_DL_run2 d0 L1 R1)).
    + apply evstep_refl.
  - (* CB *)
    destruct rs as [| [| d] R1].
    + exact (pev (step_CB_nil ls)).
    + exact (pev (step_CB_zero ls R1)).
    + destruct (N.eqb_spec d 0) as [-> | h0].
      * destruct R1 as [| [| d2] R2].
        -- exact (pev (step_CB_run0_nil ls)).
        -- exact (pev (step_CB_run0_zero ls R2)).
        -- destruct (N.eqb_spec d2 0) as [-> | hd2].
           ++ exact (pev (step_CB_run0_run0 ls R2)).
           ++ replace d2 with ((d2 - 1) + 1) at 1 by lia.
              exact (pev (step_CB_run0_run_pos (d2 - 1) ls R2)).
      * destruct (N.eqb_spec d 1) as [-> | h1]; [exact (pev (step_CB_run1 ls R1)) |].
        destruct (N.eqb_spec d 2) as [-> | h2]; [exact (pev (step_CB_run2 ls R1)) |].
        replace d with ((d - 3) + 3) at 1 by lia.
        exact (pev (step_CB_run_ge3 (d - 3) ls R1)).
  - (* HALT *)
    apply evstep_refl.
Qed.

Definition stepElem16 := iter stepElemM 16%nat.
Definition stepElem256 := iter stepElem16 16%nat.
Definition stepElem4096 := iter stepElem256 16%nat.

Definition runElemFast (s : SymMode * list MItem * list MItem) : SymMode * list MItem * list MItem :=
  iter stepElemM 7%nat (iter stepElem16 3%nat (iter stepElem256 11%nat (iter stepElem4096 4%nat s))).

Lemma stepElem16_sound (s : SymMode * list MItem * list MItem) :
  evalM s -->* evalM (stepElem16 s).
Proof. apply (iter_sound stepElemM evalM stepElemM_sound 16%nat). Qed.

Lemma stepElem256_sound (s : SymMode * list MItem * list MItem) :
  evalM s -->* evalM (stepElem256 s).
Proof. apply (iter_sound stepElem16 evalM stepElem16_sound 16%nat). Qed.

Lemma stepElem4096_sound (s : SymMode * list MItem * list MItem) :
  evalM s -->* evalM (stepElem4096 s).
Proof. apply (iter_sound stepElem256 evalM stepElem256_sound 16%nat). Qed.

Lemma runElemFast_sound (s : SymMode * list MItem * list MItem) :
  evalM s -->* evalM (runElemFast s).
Proof.
  unfold runElemFast.
  eapply etrans; [exact (iter_sound stepElem4096 evalM stepElem4096_sound 4%nat s) |].
  eapply etrans; [exact (iter_sound stepElem256 evalM stepElem256_sound 11%nat _) |].
  eapply etrans; [exact (iter_sound stepElem16 evalM stepElem16_sound 3%nat _) |].
  exact (iter_sound stepElemM evalM stepElemM_sound 7%nat _).
Qed.

(* ========================================================================== *)
(* Section 3: Symbolic Tokens (`SymTok`) & Block Sweeps                       *)
(* ========================================================================== *)

Inductive SymTok : Type :=
  | STItem (x : MItem)
  | STRepB1 (k : N)
  | STRep2 (p : N)
  | STRep12 (m : N).

Definition symtok_eqb (t1 t2 : SymTok) : bool :=
  match t1, t2 with
  | STItem x1, STItem x2 => mitem_eqb x1 x2
  | STRepB1 k1, STRepB1 k2 => N.eqb k1 k2
  | STRep2 p1, STRep2 p2 => N.eqb p1 p2
  | STRep12 m1, STRep12 m2 => N.eqb m1 m2
  | _, _ => false
  end.

Lemma symtok_eqb_eq (t1 t2 : SymTok) : symtok_eqb t1 t2 = true <-> t1 = t2.
Proof.
  destruct t1, t2; simpl; split; intro h; try discriminate; try reflexivity.
  - apply mitem_eqb_eq in h; subst; reflexivity.
  - injection h as h; subst; apply mitem_eqb_eq; reflexivity.
  - apply N.eqb_eq in h; subst; reflexivity.
  - injection h as h; subst; apply N.eqb_refl.
  - apply N.eqb_eq in h; subst; reflexivity.
  - injection h as h; subst; apply N.eqb_refl.
  - apply N.eqb_eq in h; subst; reflexivity.
  - injection h as h; subst; apply N.eqb_refl.
Qed.

Fixpoint stripPrefixSym (pre xs : list SymTok) : option (list SymTok) :=
  match pre, xs with
  | [], _ => Some xs
  | p :: ps, x :: xs' =>
    if symtok_eqb p x then stripPrefixSym ps xs' else None
  | _ :: _, [] => None
  end.

Lemma stripPrefixSym_some (pre xs rest : list SymTok) :
  stripPrefixSym pre xs = Some rest -> xs = pre ++ rest.
Proof.
  revert xs.
  induction pre as [| p ps ih]; intros xs h; simpl in *.
  - injection h as <-; reflexivity.
  - destruct xs as [| x xs']; [discriminate |].
    destruct (symtok_eqb p x) eqn:heq; [| discriminate].
    apply symtok_eqb_eq in heq; subst x.
    f_equal; exact (ih xs' h).
Qed.

Fixpoint encSymL (xs : list SymTok) : list MItem :=
  match xs with
  | [] => []
  | STItem x :: xs' => x :: encSymL xs'
  | STRepB1 k :: xs' => repBlock [MRun 0; MRun 1] k ++ encSymL xs'
  | STRep2 p :: xs' => repBlock [MRun 1; MRun 0; MRun 1] p ++ encSymL xs'
  | STRep12 m :: xs' => repBlock [MRun 1; MRun 0; MRun 1; MRun 0; MRun 1] m ++ encSymL xs'
  end.

Fixpoint encSymR (xs : list SymTok) : list MItem :=
  match xs with
  | [] => []
  | STItem x :: xs' => x :: encSymR xs'
  | STRepB1 k :: xs' => repBlock [MRun 0; MRun 1] k ++ encSymR xs'
  | STRep2 p :: xs' => repBlock [MRun 0; MRun 1; MRun 1] p ++ encSymR xs'
  | STRep12 m :: xs' => repBlock [MRun 0; MRun 1; MRun 0; MRun 1; MRun 1] m ++ encSymR xs'
  end.

Definition evalSym (s : SymMode * list SymTok * list SymTok) : Q * tape :=
  let '(m, ls, rs) := s in
  evalM (m, encSymL ls, encSymR rs).

Definition getRepB1 (t : SymTok) : option N :=
  match t with STRepB1 k => Some k | _ => None end.
Definition getRep2 (t : SymTok) : option N :=
  match t with STRep2 p => Some p | _ => None end.
Definition getRep12 (t : SymTok) : option N :=
  match t with STRep12 m => Some m | _ => None end.

Definition eatStep (blk : list SymTok) (getRep : SymTok -> option N)
  (k : N) (xs : list SymTok) : option (N * list SymTok) :=
  match xs with
  | [] => None
  | x :: rest =>
    match getRep x with
    | Some k2 => Some (k + k2, rest)
    | None =>
      match stripPrefixSym blk (x :: rest) with
      | Some rest2 => Some (k + 1, rest2)
      | None => None
      end
    end
  end.

Fixpoint eatFuel (blk : list SymTok) (mkRep : N -> SymTok) (getRep : SymTok -> option N)
  (fuel : nat) (k : N) (xs : list SymTok) : list SymTok :=
  match fuel with
  | 0%nat => mkRep k :: xs
  | S fuel' =>
    match eatStep blk getRep k xs with
    | Some (k', rest) => eatFuel blk mkRep getRep fuel' k' rest
    | None => mkRep k :: xs
    end
  end.

Lemma enc_eatFuel (enc : list SymTok -> list MItem) (mblk : list MItem)
  (blk : list SymTok) (mkRep : N -> SymTok) (getRep : SymTok -> option N)
  (hmk : forall k xs, enc (mkRep k :: xs) = repBlock mblk k ++ enc xs)
  (hget : forall x k2 rest, getRep x = Some k2 -> enc (x :: rest) = repBlock mblk k2 ++ enc rest)
  (hblk : forall rest, enc (blk ++ rest) = mblk ++ enc rest)
  (fuel : nat) (k : N) (xs : list SymTok) :
  enc (eatFuel blk mkRep getRep fuel k xs) = repBlock mblk k ++ enc xs.
Proof.
  revert k xs.
  induction fuel as [| fuel ih]; intros k xs; simpl; [exact (hmk k xs) |].
  destruct (eatStep blk getRep k xs) as [[k' rest] |] eqn:hstep; [| exact (hmk k xs)].
  rewrite (ih k' rest).
  destruct xs as [| x rest0]; [discriminate |].
  simpl in hstep.
  destruct (getRep x) as [k2 |] eqn:hg.
  - injection hstep as <- <-.
    rewrite repBlock_add, <- app_assoc, <- (hget x k2 rest0 hg).
    reflexivity.
  - destruct (stripPrefixSym blk (x :: rest0)) as [rest2 |] eqn:hs; [| discriminate].
    injection hstep as <- <-.
    pose proof (stripPrefixSym_some blk (x :: rest0) rest2 hs) as hxs.
    rewrite repBlock_succ_r, <- app_assoc, <- (hblk rest2), <- hxs.
    reflexivity.
Qed.

Definition eatB1 (k : N) (xs : list SymTok) : list SymTok :=
  eatFuel [STItem (MRun 0); STItem (MRun 1)] STRepB1 getRepB1 4%nat k xs.

Definition eatC2 (p : N) (xs : list SymTok) : list SymTok :=
  eatFuel [STItem (MRun 1); STItem (MRun 0); STItem (MRun 1)] STRep2 getRep2 4%nat p xs.

Definition eatB2 (p : N) (xs : list SymTok) : list SymTok :=
  eatFuel [STItem (MRun 0); STItem (MRun 1); STItem (MRun 1)] STRep2 getRep2 4%nat p xs.

Definition eatC12 (m : N) (xs : list SymTok) : list SymTok :=
  eatFuel [STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1)]
    STRep12 getRep12 4%nat m xs.

Definition eatB12R (m : N) (xs : list SymTok) : list SymTok :=
  eatFuel [STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1)]
    STRep12 getRep12 4%nat m xs.

Lemma encSymL_eatB1 (k : N) (xs : list SymTok) :
  encSymL (eatB1 k xs) = repBlock [MRun 0; MRun 1] k ++ encSymL xs.
Proof.
  apply enc_eatFuel; [reflexivity | | reflexivity].
  intros x k2 rest h; destruct x; try discriminate; injection h as <-; reflexivity.
Qed.

Lemma encSymR_eatB1 (k : N) (xs : list SymTok) :
  encSymR (eatB1 k xs) = repBlock [MRun 0; MRun 1] k ++ encSymR xs.
Proof.
  apply enc_eatFuel; [reflexivity | | reflexivity].
  intros x k2 rest h; destruct x; try discriminate; injection h as <-; reflexivity.
Qed.

Lemma encSymL_eatC2 (p : N) (xs : list SymTok) :
  encSymL (eatC2 p xs) = repBlock [MRun 1; MRun 0; MRun 1] p ++ encSymL xs.
Proof.
  apply enc_eatFuel; [reflexivity | | reflexivity].
  intros x k2 rest h; destruct x; try discriminate; injection h as <-; reflexivity.
Qed.

Lemma encSymR_eatB2 (p : N) (xs : list SymTok) :
  encSymR (eatB2 p xs) = repBlock [MRun 0; MRun 1; MRun 1] p ++ encSymR xs.
Proof.
  apply enc_eatFuel; [reflexivity | | reflexivity].
  intros x k2 rest h; destruct x; try discriminate; injection h as <-; reflexivity.
Qed.

Lemma encSymL_eatC12 (m : N) (xs : list SymTok) :
  encSymL (eatC12 m xs) = repBlock [MRun 1; MRun 0; MRun 1; MRun 0; MRun 1] m ++ encSymL xs.
Proof.
  apply enc_eatFuel; [reflexivity | | reflexivity].
  intros x k2 rest h; destruct x; try discriminate; injection h as <-; reflexivity.
Qed.

Lemma encSymR_eatB12R (m : N) (xs : list SymTok) :
  encSymR (eatB12R m xs) = repBlock [MRun 0; MRun 1; MRun 0; MRun 1; MRun 1] m ++ encSymR xs.
Proof.
  apply enc_eatFuel; [reflexivity | | reflexivity].
  intros x k2 rest h; destruct x; try discriminate; injection h as <-; reflexivity.
Qed.

Definition peelTok (t : SymTok) (xs : list SymTok) : list SymTok :=
  match t with
  | STRepB1 k =>
    if k =? 0 then STRepB1 0 :: xs
    else if k =? 1 then STItem (MRun 0) :: STItem (MRun 1) :: xs
    else STItem (MRun 0) :: STItem (MRun 1) :: STRepB1 (k - 1) :: xs
  | STRep2 p =>
    if p =? 0 then STRep2 0 :: xs
    else if p =? 1 then STItem (MRun 1) :: STItem (MRun 0) :: STItem (MRun 1) :: xs
    else STItem (MRun 1) :: STItem (MRun 0) :: STItem (MRun 1) :: STRep2 (p - 1) :: xs
  | STRep12 m =>
    if m =? 0 then STRep12 0 :: xs
    else if m =? 1 then
      STItem (MRun 1) :: STItem (MRun 0) :: STItem (MRun 1) :: STItem (MRun 0) :: STItem (MRun 1) :: xs
    else
      STItem (MRun 1) :: STItem (MRun 0) :: STItem (MRun 1) :: STItem (MRun 0) :: STItem (MRun 1) :: STRep12 (m - 1) :: xs
  | STItem x => STItem x :: xs
  end.

Definition peelL (xs : list SymTok) : list SymTok :=
  match xs with
  | [] => []
  | t :: xs' => peelTok t xs'
  end.

Lemma encSymL_peelTok (t : SymTok) (xs : list SymTok) :
  encSymL (peelTok t xs) = encSymL (t :: xs).
Proof.
  destruct t as [x | k | p | m]; simpl; [reflexivity | | |].
  - destruct (N.eqb_spec k 0) as [-> | h0]; [reflexivity |].
    destruct (N.eqb_spec k 1) as [-> | h1]; [reflexivity |].
    replace k with ((k - 1) + 1) at 2 by lia.
    rewrite repBlock_succ_l; reflexivity.
  - destruct (N.eqb_spec p 0) as [-> | h0]; [reflexivity |].
    destruct (N.eqb_spec p 1) as [-> | h1]; [reflexivity |].
    replace p with ((p - 1) + 1) at 2 by lia.
    rewrite repBlock_succ_l; reflexivity.
  - destruct (N.eqb_spec m 0) as [-> | h0]; [reflexivity |].
    destruct (N.eqb_spec m 1) as [-> | h1]; [reflexivity |].
    replace m with ((m - 1) + 1) at 2 by lia.
    rewrite repBlock_succ_l; reflexivity.
Qed.

Lemma encSymL_peelL (xs : list SymTok) : encSymL (peelL xs) = encSymL xs.
Proof.
  destruct xs as [| t rest]; [reflexivity | apply encSymL_peelTok].
Qed.

Fixpoint bumpSymL (M : list SymTok) : list SymTok :=
  match M with
  | [] => [STItem (MRun 0)]
  | STItem MZero :: M' => STItem (MRun 0) :: M'
  | STItem (MRun d) :: M' => STItem (MRun (d + 1)) :: M'
  | STRepB1 k :: M' =>
    if k =? 0 then bumpSymL M'
    else if k =? 1 then STItem (MRun 1) :: STItem (MRun 1) :: M'
    else STItem (MRun 1) :: STItem (MRun 1) :: STRepB1 (k - 1) :: M'
  | STRep2 p :: M' =>
    if p =? 0 then bumpSymL M'
    else STItem (MRun 2) :: STItem (MRun 0) :: STItem (MRun 1) :: STRep2 (p - 1) :: M'
  | STRep12 m :: M' =>
    if m =? 0 then bumpSymL M'
    else STItem (MRun 2) :: STItem (MRun 0) :: STItem (MRun 1) :: STItem (MRun 0) :: STItem (MRun 1) :: STRep12 (m - 1) :: M'
  end.

Fixpoint bumpSymR (M : list SymTok) : list SymTok :=
  match M with
  | [] => [STItem (MRun 0)]
  | STItem MZero :: M' => STItem (MRun 0) :: M'
  | STItem (MRun d) :: M' => STItem (MRun (d + 1)) :: M'
  | STRepB1 k :: M' =>
    if k =? 0 then bumpSymR M'
    else if k =? 1 then STItem (MRun 1) :: STItem (MRun 1) :: M'
    else STItem (MRun 1) :: STItem (MRun 1) :: STRepB1 (k - 1) :: M'
  | STRep2 p :: M' =>
    if p =? 0 then bumpSymR M'
    else STItem (MRun 1) :: STItem (MRun 1) :: STItem (MRun 1) :: STRep2 (p - 1) :: M'
  | STRep12 m :: M' =>
    if m =? 0 then bumpSymR M'
    else STItem (MRun 1) :: STItem (MRun 1) :: STItem (MRun 0) :: STItem (MRun 1) :: STItem (MRun 1) :: STRep12 (m - 1) :: M'
  end.

Lemma encSymL_bumpSymL (L : list SymTok) :
  encSymL (bumpSymL L) = bumpM (encSymL L).
Proof.
  induction L as [| t M ih]; [reflexivity |].
  destruct t as [[| d] | k | p | m]; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (N.eqb_spec k 0) as [-> | h0]; [exact ih |].
    destruct (N.eqb_spec k 1) as [-> | h1]; [reflexivity |].
    replace k with ((k - 1) + 1) at 2 by lia.
    rewrite repBlock_succ_l; reflexivity.
  - destruct (N.eqb_spec p 0) as [-> | h0]; [exact ih |].
    replace p with ((p - 1) + 1) at 2 by lia.
    rewrite repBlock_succ_l; reflexivity.
  - destruct (N.eqb_spec m 0) as [-> | h0]; [exact ih |].
    replace m with ((m - 1) + 1) at 2 by lia.
    rewrite repBlock_succ_l; reflexivity.
Qed.

Lemma encSymR_bumpSymR (R : list SymTok) :
  encSymR (bumpSymR R) = bumpM (encSymR R).
Proof.
  induction R as [| t M ih]; [reflexivity |].
  destruct t as [[| d] | k | p | m]; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (N.eqb_spec k 0) as [-> | h0]; [exact ih |].
    destruct (N.eqb_spec k 1) as [-> | h1]; [reflexivity |].
    replace k with ((k - 1) + 1) at 2 by lia.
    rewrite repBlock_succ_l; reflexivity.
  - destruct (N.eqb_spec p 0) as [-> | h0]; [exact ih |].
    replace p with ((p - 1) + 1) at 2 by lia.
    rewrite repBlock_succ_l; reflexivity.
  - destruct (N.eqb_spec m 0) as [-> | h0]; [exact ih |].
    replace m with ((m - 1) + 1) at 2 by lia.
    rewrite repBlock_succ_l; reflexivity.
Qed.

Fixpoint prependZeroSymNat (n : nat) (acc : list SymTok) : list SymTok :=
  match n with
  | 0%nat => acc
  | S n' => prependZeroSymNat n' (STItem MZero :: acc)
  end.

Definition prependZeroSym (n : N) (acc : list SymTok) : list SymTok :=
  prependZeroSymNat (N.to_nat n) acc.

Lemma encSymL_prependZeroSymNat (n : nat) (acc : list SymTok) :
  encSymL (prependZeroSymNat n acc) = replicate n MZero ++ encSymL acc.
Proof.
  revert acc.
  induction n as [| n ih]; intro acc; [reflexivity |].
  cbn [prependZeroSymNat].
  rewrite ih.
  cbn [encSymL].
  change (MZero :: encSymL acc) with ([MZero] ++ encSymL acc).
  rewrite app_assoc, <- replicate_succ_r.
  reflexivity.
Qed.

Lemma encSymL_prependZeroSym (n : N) (acc : list SymTok) :
  encSymL (prependZeroSym n acc) = nreplicate n MZero ++ encSymL acc.
Proof.
  apply encSymL_prependZeroSymNat.
Qed.

Lemma sweep_BB_B1 (k : N) : forall (L R : list MItem),
  cfgBB (repBlock [MRun 0; MRun 1] k ++ L) R -->*
  cfgBB L (repBlock [MRun 0; MRun 1] k ++ R).
Proof.
  induction k using N_peano_ind; intros L R.
  - simpl. apply evstep_refl.
  - rewrite (repBlock_succ_l [MRun 0; MRun 1] k) at 1.
    rewrite <- app_assoc.
    eapply etrans; [exact (pev (step_BB_r0_r1 (repBlock [MRun 0; MRun 1] k ++ L) R)) |].
    rewrite (repBlock_succ_r [MRun 0; MRun 1] k), <- app_assoc.
    exact (IHk L (MRun 0 :: MRun 1 :: R)).
Qed.

Lemma sweep_BB_C2 (p : N) : forall (L R : list MItem),
  cfgBB (repBlock [MRun 1; MRun 0; MRun 1] p ++ L) (MRun 0 :: MRun 1 :: R) -->*
  cfgBB L (MRun 0 :: MRun 1 :: repBlock [MRun 0; MRun 1; MRun 1] p ++ R).
Proof.
  induction p using N_peano_ind; intros L R.
  - simpl. apply evstep_refl.
  - rewrite repBlock_succ_l, <- app_assoc.
    eapply etrans;
      [exact (pev (step_BB_r1_r0_r1_comm (repBlock [MRun 1; MRun 0; MRun 1] p ++ L) R)) |].
    rewrite (repBlock_succ_r [MRun 0; MRun 1; MRun 1] p), <- app_assoc.
    exact (IHp L (MRun 0 :: MRun 1 :: MRun 1 :: R)).
Qed.

Lemma sweep_BB_C12 (m : N) : forall (L R : list MItem),
  cfgBB (repBlock [MRun 1; MRun 0; MRun 1; MRun 0; MRun 1] m ++ L) (MRun 0 :: MRun 1 :: R) -->*
  cfgBB L (MRun 0 :: MRun 1 :: repBlock [MRun 0; MRun 1; MRun 0; MRun 1; MRun 1] m ++ R).
Proof.
  induction m using N_peano_ind; intros L R.
  - simpl. apply evstep_refl.
  - rewrite repBlock_succ_l, <- app_assoc.
    eapply etrans.
    { exact (pev (ptrans
        (step_BB_r1_r0_r1_comm (MRun 0 :: MRun 1 :: (repBlock [MRun 1; MRun 0; MRun 1; MRun 0; MRun 1] m ++ L)) R)
        (step_BB_r0_r1 (repBlock [MRun 1; MRun 0; MRun 1; MRun 0; MRun 1] m ++ L)
          (MRun 0 :: MRun 1 :: MRun 0 :: MRun 1 :: MRun 1 :: R)))). }
    rewrite (repBlock_succ_r [MRun 0; MRun 1; MRun 0; MRun 1; MRun 1] m), <- app_assoc.
    exact (IHm L (MRun 0 :: MRun 1 :: MRun 0 :: MRun 1 :: MRun 1 :: R)).
Qed.

Lemma sweep_CB_B1 (k : N) : forall (L R : list MItem),
  cfgCB (MRun 0 :: L) (repBlock [MRun 0; MRun 1] k ++ R) -->*
  cfgCB (MRun 0 :: repBlock [MRun 0; MRun 1] k ++ L) R.
Proof.
  induction k using N_peano_ind; intros L R.
  - simpl. apply evstep_refl.
  - rewrite (repBlock_succ_l [MRun 0; MRun 1] k) at 1.
    rewrite <- app_assoc.
    pose proof (step_CB_run0_run_pos 0 (MRun 0 :: L) (repBlock [MRun 0; MRun 1] k ++ R)) as h1.
    cbn [nreplicate replicate bumpM app] in h1.
    change (0 + 1) with 1 in h1.
    eapply etrans; [exact (pev h1) |].
    rewrite (repBlock_succ_r [MRun 0; MRun 1] k), <- app_assoc.
    exact (IHk (MRun 0 :: MRun 1 :: L) R).
Qed.

Lemma sweep_CB_B2 (p : N) : forall (L R : list MItem),
  cfgCB (MRun 0 :: L) (repBlock [MRun 0; MRun 1; MRun 1] p ++ R) -->*
  cfgCB (MRun 0 :: repBlock [MRun 1; MRun 0; MRun 1] p ++ L) R.
Proof.
  induction p using N_peano_ind; intros L R.
  - simpl. apply evstep_refl.
  - rewrite repBlock_succ_l, <- app_assoc.
    pose proof (step_CB_run0_run_pos 0 (MRun 0 :: L)
      (MRun 1 :: repBlock [MRun 0; MRun 1; MRun 1] p ++ R)) as h1.
    cbn [nreplicate replicate bumpM app] in h1.
    change (0 + 1) with 1 in h1.
    pose proof (step_CB_run1 (MRun 0 :: MRun 0 :: MRun 1 :: L)
      (repBlock [MRun 0; MRun 1; MRun 1] p ++ R)) as h2.
    cbn [bumpM] in h2.
    eapply etrans; [exact (pev (ptrans h1 h2)) |].
    rewrite (repBlock_succ_r [MRun 1; MRun 0; MRun 1] p), <- app_assoc.
    exact (IHp (MRun 1 :: MRun 0 :: MRun 1 :: L) R).
Qed.

Lemma sweep_CB_B12R (m : N) : forall (L R : list MItem),
  cfgCB (MRun 0 :: L) (repBlock [MRun 0; MRun 1; MRun 0; MRun 1; MRun 1] m ++ R) -->*
  cfgCB (MRun 0 :: repBlock [MRun 1; MRun 0; MRun 1; MRun 0; MRun 1] m ++ L) R.
Proof.
  induction m using N_peano_ind; intros L R.
  - simpl. apply evstep_refl.
  - rewrite repBlock_succ_l, <- app_assoc.
    pose proof (step_CB_run0_run_pos 0 (MRun 0 :: L)
      (MRun 0 :: MRun 1 :: MRun 1 :: repBlock [MRun 0; MRun 1; MRun 0; MRun 1; MRun 1] m ++ R)) as h1.
    cbn [nreplicate replicate bumpM app] in h1.
    change (0 + 1) with 1 in h1.
    pose proof (step_CB_run0_run_pos 0 (MRun 0 :: MRun 0 :: MRun 1 :: L)
      (MRun 1 :: repBlock [MRun 0; MRun 1; MRun 0; MRun 1; MRun 1] m ++ R)) as h2.
    cbn [nreplicate replicate bumpM app] in h2.
    change (0 + 1) with 1 in h2.
    pose proof (step_CB_run1 (MRun 0 :: MRun 0 :: MRun 1 :: MRun 0 :: MRun 1 :: L)
      (repBlock [MRun 0; MRun 1; MRun 0; MRun 1; MRun 1] m ++ R)) as h3.
    cbn [bumpM] in h3.
    eapply etrans; [exact (pev (ptrans h1 (ptrans h2 h3))) |].
    rewrite (repBlock_succ_r [MRun 1; MRun 0; MRun 1; MRun 0; MRun 1] m), <- app_assoc.
    exact (IHm (MRun 1 :: MRun 0 :: MRun 1 :: MRun 0 :: MRun 1 :: L) R).
Qed.

(* ========================================================================== *)
(* Section 4: Symbolic Elementary Step & Sweep Soundness                      *)
(* ========================================================================== *)

Definition stepElemBB (L R : list SymTok) : SymMode * list SymTok * list SymTok :=
  match L with
  | [] => (CB, [], bumpSymR R)
  | STItem MZero :: L1 => (CB, L1, bumpSymR R)
  | STItem (MRun d) :: L1 =>
    if d =? 0 then (BB, L1, STItem (MRun 0) :: R)
    else if d =? 1 then (BB, L1, STItem (MRun 0) :: bumpSymR R)
    else if d =? 2 then (DL, L1, STItem (MRun 0) :: STItem (MRun 0) :: bumpSymR R)
    else if d =? 3 then (BB, STItem (MRun 0) :: STItem MZero :: STItem MZero :: L1, bumpSymR R)
    else (BB, STItem (MRun 0) :: STItem MZero :: STItem (MRun (d - 4)) :: L1, bumpSymR R)
  | _ => (BB, L, R)
  end.

Definition stepElemDL (L R : list SymTok) : SymMode * list SymTok * list SymTok :=
  match L with
  | [] => (DL, [], R)
  | STItem MZero :: L1 => (HALT, STItem MZero :: L1, R)
  | STItem (MRun d) :: L1 =>
    if d =? 0 then (BB, L1, bumpSymR R)
    else if d =? 1 then (DL, L1, STItem (MRun 0) :: bumpSymR R)
    else if d =? 2 then
      match R with
      | STItem (MRun d0) :: R1 =>
        (CB, STItem (MRun 0) :: STItem (MRun 0) :: prependZeroSym (d0 + 1) L1, R1)
      | _ => (DL, L, R)
      end
    else (DL, L, R)
  | _ => (DL, L, R)
  end.

Definition stepElemCB_run0 (L R1 : list SymTok) : SymMode * list SymTok * list SymTok :=
  match R1 with
  | [] => (BB, STItem (MRun 0) :: bumpSymL L, [])
  | STItem MZero :: R2 => (BB, STItem (MRun 0) :: bumpSymL L, R2)
  | STItem (MRun d2) :: R2 =>
    if d2 =? 0 then (BB, STItem (MRun 0) :: STItem MZero :: bumpSymL L, R2)
    else (CB, STItem (MRun 0) :: STItem (MRun 0) :: prependZeroSym (d2 - 1) (bumpSymL L), R2)
  | _ => (CB, L, STItem (MRun 0) :: R1)
  end.

Definition stepElemCB (L R : list SymTok) : SymMode * list SymTok * list SymTok :=
  match R with
  | [] => (DL, bumpSymL L, [STItem (MRun 0)])
  | STItem MZero :: R1 => (DL, bumpSymL L, bumpSymR R1)
  | STItem (MRun d) :: R1 =>
    if d =? 0 then stepElemCB_run0 L R1
    else if d =? 1 then (CB, STItem (MRun 0) :: bumpSymL L, R1)
    else if d =? 2 then (BB, bumpSymL L, STItem (MRun 0) :: STItem MZero :: R1)
    else (BB, bumpSymL L, STItem (MRun 0) :: STItem (MRun (d - 3)) :: R1)
  | _ => (CB, L, R)
  end.

Definition stepElemSym (m : SymMode) (L R : list SymTok) : SymMode * list SymTok * list SymTok :=
  match m with
  | BB => stepElemBB L R
  | DL => stepElemDL L R
  | CB => stepElemCB L R
  | HALT => (HALT, L, R)
  end.

Lemma stepElemBB_sound (L R : list SymTok) :
  evalSym (BB, L, R) -->* evalSym (stepElemBB L R).
Proof.
  destruct L as [| [[| d] | k | p | m] L1]; simpl; try apply evstep_refl.
  - rewrite encSymR_bumpSymR. exact (pev (step_BB_nil _)).
  - rewrite encSymR_bumpSymR. exact (pev (step_BB_zero _ _)).
  - destruct (N.eqb_spec d 0) as [-> | h0]; simpl; [exact (pev (step_BB_run0 _ _)) |].
    destruct (N.eqb_spec d 1) as [-> | h1]; simpl;
      [rewrite encSymR_bumpSymR; exact (pev (step_BB_run1 _ _)) |].
    destruct (N.eqb_spec d 2) as [-> | h2]; simpl;
      [rewrite encSymR_bumpSymR; exact (pev (step_BB_run2 _ _)) |].
    destruct (N.eqb_spec d 3) as [-> | h3]; simpl;
      [rewrite encSymR_bumpSymR; exact (pev (step_BB_run3 _ _)) |].
    rewrite encSymR_bumpSymR.
    replace d with ((d - 4) + 4) at 1 by lia.
    exact (pev (step_BB_run_ge4 (d - 4) _ _)).
Qed.

Lemma stepElemDL_sound (L R : list SymTok) :
  evalSym (DL, L, R) -->* evalSym (stepElemDL L R).
Proof.
  destruct L as [| [[| d] | k | p | m] L1]; simpl; try apply evstep_refl.
  destruct (N.eqb_spec d 0) as [-> | h0]; simpl;
    [rewrite encSymR_bumpSymR; exact (pev (step_DL_run0 _ _)) |].
  destruct (N.eqb_spec d 1) as [-> | h1]; simpl;
    [rewrite encSymR_bumpSymR; exact (pev (step_DL_run1 _ _)) |].
  destruct (N.eqb_spec d 2) as [-> | h2]; simpl; [| apply evstep_refl].
  destruct R as [| [[| d0] | k | p | m] R1]; simpl; try apply evstep_refl.
  rewrite encSymL_prependZeroSym.
  exact (pev (step_DL_run2 d0 _ _)).
Qed.

Lemma stepElemCB_run0_sound (L R1 : list SymTok) :
  evalSym (CB, L, STItem (MRun 0) :: R1) -->* evalSym (stepElemCB_run0 L R1).
Proof.
  destruct R1 as [| [[| d2] | k | p | m] R2]; simpl; try apply evstep_refl.
  - rewrite encSymL_bumpSymL. exact (pev (step_CB_run0_nil _)).
  - rewrite encSymL_bumpSymL. exact (pev (step_CB_run0_zero _ _)).
  - destruct (N.eqb_spec d2 0) as [-> | hd2]; simpl.
    + rewrite encSymL_bumpSymL. exact (pev (step_CB_run0_run0 _ _)).
    + rewrite encSymL_prependZeroSym, encSymL_bumpSymL.
      replace d2 with ((d2 - 1) + 1) at 1 by lia.
      exact (pev (step_CB_run0_run_pos (d2 - 1) _ _)).
Qed.

Lemma stepElemCB_sound (L R : list SymTok) :
  evalSym (CB, L, R) -->* evalSym (stepElemCB L R).
Proof.
  destruct R as [| [[| d] | k | p | m] R1]; simpl; try apply evstep_refl.
  - rewrite encSymL_bumpSymL. exact (pev (step_CB_nil _)).
  - rewrite encSymL_bumpSymL, encSymR_bumpSymR. exact (pev (step_CB_zero _ _)).
  - destruct (N.eqb_spec d 0) as [-> | h0]; [exact (stepElemCB_run0_sound L R1) |].
    destruct (N.eqb_spec d 1) as [-> | h1]; simpl;
      [rewrite encSymL_bumpSymL; exact (pev (step_CB_run1 _ _)) |].
    destruct (N.eqb_spec d 2) as [-> | h2]; simpl;
      [rewrite encSymL_bumpSymL; exact (pev (step_CB_run2 _ _)) |].
    rewrite encSymL_bumpSymL.
    replace d with ((d - 3) + 3) at 1 by lia.
    exact (pev (step_CB_run_ge3 (d - 3) _ _)).
Qed.

Lemma stepElemSym_sound (m : SymMode) (L R : list SymTok) :
  evalSym (m, L, R) -->* evalSym (stepElemSym m L R).
Proof.
  destruct m; [apply stepElemBB_sound | apply stepElemDL_sound | apply stepElemCB_sound | apply evstep_refl].
Qed.

Fixpoint sweepBB (L R : list SymTok) : SymMode * list SymTok * list SymTok :=
  match L with
  | [] => stepElemBB [] R
  | STItem MZero :: L1 => stepElemBB (STItem MZero :: L1) R
  | STItem (MRun d) :: L1 =>
    if d =? 0 then sweepBB L1 (STItem (MRun 0) :: R)
    else if d =? 1 then sweepBB L1 (STItem (MRun 0) :: bumpSymR R)
    else stepElemBB (STItem (MRun d) :: L1) R
  | STRepB1 k :: L1 => sweepBB L1 (eatB1 k R)
  | STRep2 p :: L1 =>
    match stripPrefixSym [STItem (MRun 0); STItem (MRun 1)] R with
    | Some R2 => sweepBB L1 (STItem (MRun 0) :: STItem (MRun 1) :: eatB2 p R2)
    | None => stepElemBB (peelTok (STRep2 p) L1) R
    end
  | STRep12 m :: L1 =>
    match stripPrefixSym [STItem (MRun 0); STItem (MRun 1)] R with
    | Some R2 => sweepBB L1 (STItem (MRun 0) :: STItem (MRun 1) :: eatB12R m R2)
    | None => stepElemBB (peelTok (STRep12 m) L1) R
    end
  end.

Lemma sweepBB_sound (L : list SymTok) : forall (R : list SymTok),
  evalSym (BB, L, R) -->* evalSym (sweepBB L R).
Proof.
  induction L as [| t L1 ih]; intro R; cbn [sweepBB].
  - exact (stepElemBB_sound [] R).
  - destruct t as [[| d] | k | p | m].
    + exact (stepElemBB_sound (STItem MZero :: L1) R).
    + destruct (N.eqb_spec d 0) as [-> | h0].
      * eapply etrans; [| exact (ih (STItem (MRun 0) :: R))].
        exact (pev (step_BB_run0 (encSymL L1) (encSymR R))).
      * destruct (N.eqb_spec d 1) as [-> | h1].
        -- eapply etrans; [| exact (ih (STItem (MRun 0) :: bumpSymR R))].
           unfold evalSym; simpl. rewrite encSymR_bumpSymR. exact (pev (step_BB_run1 _ _)).
        -- exact (stepElemBB_sound (STItem (MRun d) :: L1) R).
    + eapply etrans; [| exact (ih (eatB1 k R))].
      unfold evalSym; simpl. rewrite encSymR_eatB1. exact (sweep_BB_B1 k _ _).
    + destruct (stripPrefixSym [STItem (MRun 0); STItem (MRun 1)] R) as [R2 |] eqn:hs.
      * pose proof (stripPrefixSym_some _ R R2 hs) as hR.
        eapply etrans; [| exact (ih (STItem (MRun 0) :: STItem (MRun 1) :: eatB2 p R2))].
        rewrite hR. unfold evalSym; simpl. rewrite encSymR_eatB2. exact (sweep_BB_C2 p _ _).
      * assert (heq : evalSym (BB, STRep2 p :: L1, R) = evalSym (BB, peelTok (STRep2 p) L1, R)).
        { unfold evalSym; rewrite encSymL_peelTok; reflexivity. }
        rewrite heq. exact (stepElemBB_sound (peelTok (STRep2 p) L1) R).
    + destruct (stripPrefixSym [STItem (MRun 0); STItem (MRun 1)] R) as [R2 |] eqn:hs.
      * pose proof (stripPrefixSym_some _ R R2 hs) as hR.
        eapply etrans; [| exact (ih (STItem (MRun 0) :: STItem (MRun 1) :: eatB12R m R2))].
        rewrite hR. unfold evalSym; simpl. rewrite encSymR_eatB12R. exact (sweep_BB_C12 m _ _).
      * assert (heq : evalSym (BB, STRep12 m :: L1, R) = evalSym (BB, peelTok (STRep12 m) L1, R)).
        { unfold evalSym; rewrite encSymL_peelTok; reflexivity. }
        rewrite heq. exact (stepElemBB_sound (peelTok (STRep12 m) L1) R).
Qed.

Fixpoint sweepCB (L R : list SymTok) : list SymTok * list SymTok :=
  match R with
  | [] => (L, [])
  | STItem MZero :: R1 => (L, STItem MZero :: R1)
  | STItem (MRun d) :: R1 =>
    if d =? 0 then
      match R1 with
      | STItem (MRun d2) :: R2 =>
        if d2 =? 1 then sweepCB (STItem (MRun 0) :: STItem (MRun 0) :: bumpSymL L) R2
        else (L, STItem (MRun 0) :: R1)
      | _ => (L, STItem (MRun 0) :: R1)
      end
    else if d =? 1 then sweepCB (STItem (MRun 0) :: bumpSymL L) R1
    else (L, STItem (MRun d) :: R1)
  | STRepB1 k :: R1 =>
    match stripPrefixSym [STItem (MRun 0)] L with
    | Some L1 => sweepCB (STItem (MRun 0) :: eatB1 k L1) R1
    | None => (L, STRepB1 k :: R1)
    end
  | STRep2 p :: R1 =>
    match stripPrefixSym [STItem (MRun 0)] L with
    | Some L1 => sweepCB (STItem (MRun 0) :: eatC2 p L1) R1
    | None => (L, STRep2 p :: R1)
    end
  | STRep12 m :: R1 =>
    match stripPrefixSym [STItem (MRun 0)] L with
    | Some L1 => sweepCB (STItem (MRun 0) :: eatC12 m L1) R1
    | None => (L, STRep12 m :: R1)
    end
  end.

Lemma sweepCB_sound_step (R : list SymTok) : forall (L : list SymTok),
  evalSym (CB, L, R) -->* evalSym (CB, fst (sweepCB L R), snd (sweepCB L R)).
Proof.
  induction R as [| x | x y R2 ih1 ih2] using list_ind2; intro L.
  - cbn [sweepCB fst snd]. apply evstep_refl.
  - destruct x as [[| d] | k | p | m]; cbn [sweepCB fst snd]; try apply evstep_refl.
    + destruct (N.eqb_spec d 0) as [-> | h0]; cbn [sweepCB fst snd]; [apply evstep_refl |].
      destruct (N.eqb_spec d 1) as [-> | h1]; cbn [sweepCB fst snd]; [| apply evstep_refl].
      unfold evalSym; simpl. rewrite encSymL_bumpSymL. exact (pev (step_CB_run1 _ [])).
    + destruct (stripPrefixSym [STItem (MRun 0)] L) as [L1 |] eqn:hs; cbn [sweepCB fst snd]; [| apply evstep_refl].
      pose proof (stripPrefixSym_some _ L L1 hs) as ->.
      unfold evalSym; simpl. rewrite encSymL_eatB1. exact (sweep_CB_B1 k _ []).
    + destruct (stripPrefixSym [STItem (MRun 0)] L) as [L1 |] eqn:hs; cbn [sweepCB fst snd]; [| apply evstep_refl].
      pose proof (stripPrefixSym_some _ L L1 hs) as ->.
      unfold evalSym; simpl. rewrite encSymL_eatC2. exact (sweep_CB_B2 p _ []).
    + destruct (stripPrefixSym [STItem (MRun 0)] L) as [L1 |] eqn:hs; cbn [sweepCB fst snd]; [| apply evstep_refl].
      pose proof (stripPrefixSym_some _ L L1 hs) as ->.
      unfold evalSym; simpl. rewrite encSymL_eatC12. exact (sweep_CB_B12R m _ []).
  - destruct x as [[| d] | k | p | m]; cbn [sweepCB].
    + cbn [fst snd]. apply evstep_refl.
    + destruct (N.eqb_spec d 0) as [-> | h0].
      * destruct y as [[| d2] | k2 | p2 | m2]; cbn [fst snd]; try apply evstep_refl.
        destruct (N.eqb_spec d2 1) as [-> | hd2]; cbn [fst snd]; [| apply evstep_refl].
        eapply etrans; [| exact (ih2 (STItem (MRun 0) :: STItem (MRun 0) :: bumpSymL L))].
        unfold evalSym; simpl. rewrite encSymL_bumpSymL.
        pose proof (step_CB_run0_run_pos 0 (encSymL L) (encSymR R2)) as hstep.
        cbn [nreplicate replicate app] in hstep. change (0 + 1) with 1 in hstep.
        exact (pev hstep).
      * destruct (N.eqb_spec d 1) as [-> | h1]; cbn [fst snd]; [| apply evstep_refl].
        eapply etrans; [| exact (ih1 (STItem (MRun 0) :: bumpSymL L))].
        unfold evalSym; simpl. rewrite encSymL_bumpSymL. exact (pev (step_CB_run1 _ _)).
    + destruct (stripPrefixSym [STItem (MRun 0)] L) as [L1 |] eqn:hs; cbn [fst snd]; [| apply evstep_refl].
      pose proof (stripPrefixSym_some _ L L1 hs) as hL.
      eapply etrans; [| exact (ih1 (STItem (MRun 0) :: eatB1 k L1))].
      rewrite hL. unfold evalSym; simpl. rewrite encSymL_eatB1. exact (sweep_CB_B1 k _ _).
    + destruct (stripPrefixSym [STItem (MRun 0)] L) as [L1 |] eqn:hs; cbn [fst snd]; [| apply evstep_refl].
      pose proof (stripPrefixSym_some _ L L1 hs) as hL.
      eapply etrans; [| exact (ih1 (STItem (MRun 0) :: eatC2 p L1))].
      rewrite hL. unfold evalSym; simpl. rewrite encSymL_eatC2. exact (sweep_CB_B2 p _ _).
    + destruct (stripPrefixSym [STItem (MRun 0)] L) as [L1 |] eqn:hs; cbn [fst snd]; [| apply evstep_refl].
      pose proof (stripPrefixSym_some _ L L1 hs) as hL.
      eapply etrans; [| exact (ih1 (STItem (MRun 0) :: eatC12 m L1))].
      rewrite hL. unfold evalSym; simpl. rewrite encSymL_eatC12. exact (sweep_CB_B12R m _ _).
Qed.

Lemma sweepCB_sound (L R : list SymTok) :
  evalSym (CB, L, R) -->* evalSym (CB, fst (sweepCB L R), snd (sweepCB L R)).
Proof. apply sweepCB_sound_step. Qed.

Definition finishThenBB (s : SymMode * list SymTok * list SymTok) : SymMode * list SymTok * list SymTok :=
  let '(m, L1, R1) := s in
  match m with
  | BB => sweepBB L1 R1
  | _ => s
  end.

Lemma finishThenBB_sound (s : SymMode * list SymTok * list SymTok) :
  evalSym s -->* evalSym (finishThenBB s).
Proof.
  destruct s as [[m L1] R1]; destruct m; try apply evstep_refl.
  apply sweepBB_sound.
Qed.

Definition stepElemThenBB (m : SymMode) (L R : list SymTok) : SymMode * list SymTok * list SymTok :=
  finishThenBB (stepElemSym m L R).

Lemma stepElemThenBB_sound (m : SymMode) (L R : list SymTok) :
  evalSym (m, L, R) -->* evalSym (stepElemThenBB m L R).
Proof.
  exact (etrans (stepElemSym_sound m L R) (finishThenBB_sound (stepElemSym m L R))).
Qed.

(* ========================================================================== *)
(* Section 5: Pure Unary Simulator (`NatTok`) & Accelerated Rules A, B, C     *)
(* ========================================================================== *)

Inductive NatTok : Type :=
  | NTZero
  | NTRun (d : nat)
  | NTRepB1 (k : nat)
  | NTRep2 (p : nat)
  | NTRep12 (m : nat).

Definition natTokToSym (t : NatTok) : SymTok :=
  match t with
  | NTZero => STItem MZero
  | NTRun d => STItem (MRun (N.of_nat d))
  | NTRepB1 k => STRepB1 (N.of_nat k)
  | NTRep2 p => STRep2 (N.of_nat p)
  | NTRep12 m => STRep12 (N.of_nat m)
  end.

Definition symTokToNat (t : SymTok) : NatTok :=
  match t with
  | STItem MZero => NTZero
  | STItem (MRun d) => NTRun (N.to_nat d)
  | STRepB1 k => NTRepB1 (N.to_nat k)
  | STRep2 p => NTRep2 (N.to_nat p)
  | STRep12 m => NTRep12 (N.to_nat m)
  end.

Lemma natTokToSym_symTokToNat (t : SymTok) :
  natTokToSym (symTokToNat t) = t.
Proof.
  destruct t as [[| d] | k | p | m]; simpl; repeat rewrite N2Nat.id; reflexivity.
Qed.

Lemma map_natTokToSym_symTokToNat (xs : list SymTok) :
  map natTokToSym (map symTokToNat xs) = xs.
Proof.
  induction xs as [| t xs ih]; simpl; [reflexivity |].
  rewrite natTokToSym_symTokToNat, ih; reflexivity.
Qed.

Definition evalNat (s : SymMode * list NatTok * list NatTok) : Q * tape :=
  let '(m, ls, rs) := s in
  evalSym (m, map natTokToSym ls, map natTokToSym rs).

Definition nattok_eqb (t1 t2 : NatTok) : bool :=
  match t1, t2 with
  | NTZero, NTZero => true
  | NTRun d1, NTRun d2 => Nat.eqb d1 d2
  | NTRepB1 k1, NTRepB1 k2 => Nat.eqb k1 k2
  | NTRep2 p1, NTRep2 p2 => Nat.eqb p1 p2
  | NTRep12 m1, NTRep12 m2 => Nat.eqb m1 m2
  | _, _ => false
  end.

Lemma nattok_eqb_eq (t1 t2 : NatTok) : nattok_eqb t1 t2 = true <-> t1 = t2.
Proof.
  destruct t1, t2; simpl; split; intro h; try discriminate; try reflexivity;
    try (apply Nat.eqb_eq in h; subst; reflexivity);
    try (injection h as <-; apply Nat.eqb_refl).
Qed.

Fixpoint stripPrefixNat (pre xs : list NatTok) : option (list NatTok) :=
  match pre, xs with
  | [], _ => Some xs
  | p :: ps, x :: xs' =>
    if nattok_eqb p x then stripPrefixNat ps xs' else None
  | _ :: _, [] => None
  end.

Lemma stripPrefixNat_some (pre xs rest : list NatTok) :
  stripPrefixNat pre xs = Some rest -> xs = pre ++ rest.
Proof.
  revert xs.
  induction pre as [| p ps ih]; intros xs h; simpl in *.
  - injection h as <-; reflexivity.
  - destruct xs as [| x xs']; [discriminate |].
    destruct (nattok_eqb p x) eqn:heq; [| discriminate].
    apply nattok_eqb_eq in heq; subst x.
    f_equal; exact (ih xs' h).
Qed.

Fixpoint bumpNatL (M : list NatTok) : list NatTok :=
  match M with
  | [] => [NTRun 0%nat]
  | NTZero :: M' => NTRun 0%nat :: M'
  | NTRun d :: M' => NTRun (S d) :: M'
  | NTRepB1 0%nat :: M' => bumpNatL M'
  | NTRepB1 1%nat :: M' => NTRun 1%nat :: NTRun 1%nat :: M'
  | NTRepB1 (S (S k)) :: M' => NTRun 1%nat :: NTRun 1%nat :: NTRepB1 (S k) :: M'
  | NTRep2 0%nat :: M' => bumpNatL M'
  | NTRep2 (S p) :: M' => NTRun 2%nat :: NTRun 0%nat :: NTRun 1%nat :: NTRep2 p :: M'
  | NTRep12 0%nat :: M' => bumpNatL M'
  | NTRep12 (S m) :: M' => NTRun 2%nat :: NTRun 0%nat :: NTRun 1%nat :: NTRun 0%nat :: NTRun 1%nat :: NTRep12 m :: M'
  end.

Fixpoint bumpNatR (M : list NatTok) : list NatTok :=
  match M with
  | [] => [NTRun 0%nat]
  | NTZero :: M' => NTRun 0%nat :: M'
  | NTRun d :: M' => NTRun (S d) :: M'
  | NTRepB1 0%nat :: M' => bumpNatR M'
  | NTRepB1 1%nat :: M' => NTRun 1%nat :: NTRun 1%nat :: M'
  | NTRepB1 (S (S k)) :: M' => NTRun 1%nat :: NTRun 1%nat :: NTRepB1 (S k) :: M'
  | NTRep2 0%nat :: M' => bumpNatR M'
  | NTRep2 (S p) :: M' => NTRun 1%nat :: NTRun 1%nat :: NTRun 1%nat :: NTRep2 p :: M'
  | NTRep12 0%nat :: M' => bumpNatR M'
  | NTRep12 (S m) :: M' => NTRun 1%nat :: NTRun 1%nat :: NTRun 0%nat :: NTRun 1%nat :: NTRun 1%nat :: NTRep12 m :: M'
  end.

Lemma map_bumpNatL (M : list NatTok) :
  map natTokToSym (bumpNatL M) = bumpSymL (map natTokToSym M).
Proof.
  induction M as [| t M' ih]; [reflexivity |].
  destruct t as [| d | [| [| k]] | [| p] | [| m]];
    cbn [map bumpNatL bumpSymL natTokToSym].
  - reflexivity.
  - rewrite Nat2N.inj_succ, <- N.add_1_r. reflexivity.
  - exact ih.
  - reflexivity.
  - destruct (N.eqb_spec (N.of_nat (S (S k))) 0) as [h | _]; [lia |].
    destruct (N.eqb_spec (N.of_nat (S (S k))) 1) as [h | _]; [lia |].
    replace (N.of_nat (S (S k)) - 1) with (N.of_nat (S k)) by lia.
    reflexivity.
  - exact ih.
  - destruct (N.eqb_spec (N.of_nat (S p)) 0) as [h | _]; [lia |].
    replace (N.of_nat (S p) - 1) with (N.of_nat p) by lia.
    reflexivity.
  - exact ih.
  - destruct (N.eqb_spec (N.of_nat (S m)) 0) as [h | _]; [lia |].
    replace (N.of_nat (S m) - 1) with (N.of_nat m) by lia.
    reflexivity.
Qed.

Lemma map_bumpNatR (M : list NatTok) :
  map natTokToSym (bumpNatR M) = bumpSymR (map natTokToSym M).
Proof.
  induction M as [| t M' ih]; [reflexivity |].
  destruct t as [| d | [| [| k]] | [| p] | [| m]];
    cbn [map bumpNatR bumpSymR natTokToSym].
  - reflexivity.
  - rewrite Nat2N.inj_succ, <- N.add_1_r. reflexivity.
  - exact ih.
  - reflexivity.
  - destruct (N.eqb_spec (N.of_nat (S (S k))) 0) as [h | _]; [lia |].
    destruct (N.eqb_spec (N.of_nat (S (S k))) 1) as [h | _]; [lia |].
    replace (N.of_nat (S (S k)) - 1) with (N.of_nat (S k)) by lia.
    reflexivity.
  - exact ih.
  - destruct (N.eqb_spec (N.of_nat (S p)) 0) as [h | _]; [lia |].
    replace (N.of_nat (S p) - 1) with (N.of_nat p) by lia.
    reflexivity.
  - exact ih.
  - destruct (N.eqb_spec (N.of_nat (S m)) 0) as [h | _]; [lia |].
    replace (N.of_nat (S m) - 1) with (N.of_nat m) by lia.
    reflexivity.
Qed.

Fixpoint prependZeroNat (n : nat) (acc : list NatTok) : list NatTok :=
  match n with
  | 0%nat => acc
  | S n' => prependZeroNat n' (NTZero :: acc)
  end.

Lemma map_prependZeroNat (n : nat) (acc : list NatTok) :
  map natTokToSym (prependZeroNat n acc) = prependZeroSymNat n (map natTokToSym acc).
Proof.
  revert acc.
  induction n as [| n ih]; intro acc; simpl; [reflexivity |].
  exact (ih (NTZero :: acc)).
Qed.

Definition peelPureTok (t : NatTok) (xs : list NatTok) : list NatTok :=
  match t with
  | NTRepB1 0%nat => NTRepB1 0%nat :: xs
  | NTRepB1 (S k) => NTRun 0%nat :: NTRun 1%nat :: NTRepB1 k :: xs
  | NTRep2 0%nat => NTRep2 0%nat :: xs
  | NTRep2 (S p) => NTRun 1%nat :: NTRun 0%nat :: NTRun 1%nat :: NTRep2 p :: xs
  | NTRep12 0%nat => NTRep12 0%nat :: xs
  | NTRep12 (S m) => NTRun 1%nat :: NTRun 0%nat :: NTRun 1%nat :: NTRun 0%nat :: NTRun 1%nat :: NTRep12 m :: xs
  | x => x :: xs
  end.

Lemma encSymL_peelPureTok (t : NatTok) (xs : list NatTok) :
  encSymL (map natTokToSym (peelPureTok t xs)) = encSymL (map natTokToSym (t :: xs)).
Proof.
  destruct t as [| d | [| k] | [| p] | [| m]];
    cbn [map peelPureTok natTokToSym encSymL]; try reflexivity.
  - replace (N.of_nat (S k)) with (N.of_nat k + 1) by lia.
    rewrite repBlock_succ_l; reflexivity.
  - replace (N.of_nat (S p)) with (N.of_nat p + 1) by lia.
    rewrite repBlock_succ_l; reflexivity.
  - replace (N.of_nat (S m)) with (N.of_nat m + 1) by lia.
    rewrite repBlock_succ_l; reflexivity.
Qed.

Definition stepNatBB (L R : list NatTok) : SymMode * list NatTok * list NatTok :=
  match L with
  | [] => (CB, [], bumpNatR R)
  | NTZero :: L1 => (CB, L1, bumpNatR R)
  | NTRun 0%nat :: L1 => (BB, L1, NTRun 0%nat :: R)
  | NTRun 1%nat :: L1 => (BB, L1, NTRun 0%nat :: bumpNatR R)
  | NTRun 2%nat :: L1 => (DL, L1, NTRun 0%nat :: NTRun 0%nat :: bumpNatR R)
  | NTRun 3%nat :: L1 => (BB, NTRun 0%nat :: NTZero :: NTZero :: L1, bumpNatR R)
  | NTRun (S (S (S (S d)))) :: L1 => (BB, NTRun 0%nat :: NTZero :: NTRun d :: L1, bumpNatR R)
  | _ => (BB, L, R)
  end.

Definition stepNatDL (L R : list NatTok) : SymMode * list NatTok * list NatTok :=
  match L with
  | [] => (DL, [], R)
  | NTZero :: L1 => (HALT, NTZero :: L1, R)
  | NTRun 0%nat :: L1 => (BB, L1, bumpNatR R)
  | NTRun 1%nat :: L1 => (DL, L1, NTRun 0%nat :: bumpNatR R)
  | NTRun 2%nat :: L1 =>
    match R with
    | NTRun d0 :: R1 => (CB, NTRun 0%nat :: NTRun 0%nat :: prependZeroNat (S d0) L1, R1)
    | _ => (DL, L, R)
    end
  | _ => (DL, L, R)
  end.

Definition stepNatCB_run0 (L R1 : list NatTok) : SymMode * list NatTok * list NatTok :=
  match R1 with
  | [] => (BB, NTRun 0%nat :: bumpNatL L, [])
  | NTZero :: R2 => (BB, NTRun 0%nat :: bumpNatL L, R2)
  | NTRun 0%nat :: R2 => (BB, NTRun 0%nat :: NTZero :: bumpNatL L, R2)
  | NTRun (S d2) :: R2 => (CB, NTRun 0%nat :: NTRun 0%nat :: prependZeroNat d2 (bumpNatL L), R2)
  | _ => (CB, L, NTRun 0%nat :: R1)
  end.

Definition stepNatCB (L R : list NatTok) : SymMode * list NatTok * list NatTok :=
  match R with
  | [] => (DL, bumpNatL L, [NTRun 0%nat])
  | NTZero :: R1 => (DL, bumpNatL L, bumpNatR R1)
  | NTRun 0%nat :: R1 => stepNatCB_run0 L R1
  | NTRun 1%nat :: R1 => (CB, NTRun 0%nat :: bumpNatL L, R1)
  | NTRun 2%nat :: R1 => (BB, bumpNatL L, NTRun 0%nat :: NTZero :: R1)
  | NTRun (S (S (S d))) :: R1 => (BB, bumpNatL L, NTRun 0%nat :: NTRun d :: R1)
  | _ => (CB, L, R)
  end.

Definition stepPureBB (L R : list NatTok) : SymMode * list NatTok * list NatTok :=
  match L with
  | [] => stepNatBB [] R
  | NTZero :: L1 => stepNatBB (NTZero :: L1) R
  | NTRun d :: L1 => stepNatBB (NTRun d :: L1) R
  | NTRepB1 k :: L1 => (BB, L1, NTRepB1 k :: R)
  | NTRep2 p :: L1 =>
    match stripPrefixNat [NTRun 0%nat; NTRun 1%nat] R with
    | Some R2 => (BB, L1, NTRun 0%nat :: NTRun 1%nat :: NTRep2 p :: R2)
    | None => stepNatBB (peelPureTok (NTRep2 p) L1) R
    end
  | NTRep12 m :: L1 =>
    match stripPrefixNat [NTRun 0%nat; NTRun 1%nat] R with
    | Some R2 => (BB, L1, NTRun 0%nat :: NTRun 1%nat :: NTRep12 m :: R2)
    | None => stepNatBB (peelPureTok (NTRep12 m) L1) R
    end
  end.

Definition stepPureDL (L R : list NatTok) : SymMode * list NatTok * list NatTok :=
  match L with
  | [] => (DL, [], R)
  | t :: L1 => stepNatDL (peelPureTok t L1) R
  end.

Definition stepPureCB (L R : list NatTok) : SymMode * list NatTok * list NatTok :=
  match R with
  | [] => stepNatCB L []
  | NTZero :: R1 => stepNatCB L (NTZero :: R1)
  | NTRun 0%nat :: R1 => stepNatCB_run0 L R1
  | NTRun 1%nat :: R1 => stepNatCB L (NTRun 1%nat :: R1)
  | NTRun 2%nat :: R1 => stepNatCB L (NTRun 2%nat :: R1)
  | NTRun (S (S (S d))) :: R1 => (BB, bumpNatL L, NTRun 0%nat :: NTRun d :: R1)
  | NTRepB1 k :: R1 =>
    match stripPrefixNat [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat] L with
    | Some L2 => (CB, NTRun 0%nat :: NTRepB1 (S k) :: L2, R1)
    | None =>
      match stripPrefixNat [NTRun 0%nat] L with
      | Some L1 => (CB, NTRun 0%nat :: NTRepB1 k :: L1, R1)
      | None => (CB, L, NTRepB1 k :: R1)
      end
    end
  | NTRep2 p :: R1 =>
    match stripPrefixNat [NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat] L with
    | Some L2 => (CB, NTRun 0%nat :: NTRep2 (S p) :: L2, R1)
    | None =>
      match stripPrefixNat [NTRun 0%nat] L with
      | Some L1 => (CB, NTRun 0%nat :: NTRep2 p :: L1, R1)
      | None => (CB, L, NTRep2 p :: R1)
      end
    end
  | NTRep12 m :: R1 =>
    match stripPrefixNat [NTRun 0%nat] L with
    | Some L1 => (CB, NTRun 0%nat :: NTRep12 m :: L1, R1)
    | None => (CB, L, NTRep12 m :: R1)
    end
  end.

Definition stepPure (s : SymMode * list NatTok * list NatTok) : SymMode * list NatTok * list NatTok :=
  let '(m, ls, rs) := s in
  match m with
  | BB => stepPureBB ls rs
  | DL => stepPureDL ls rs
  | CB => stepPureCB ls rs
  | HALT => (HALT, ls, rs)
  end.

Lemma stepNatBB_sound (L R : list NatTok) :
  evalNat (BB, L, R) -->* evalNat (stepNatBB L R).
Proof.
  destruct L as [| t L1]; [| destruct t as [| [| [| [| [| d]]]] | k | p | m]];
    cbn [stepNatBB]; try apply evstep_refl.
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatR, encSymR_bumpSymR.
    exact (pev (step_BB_nil _)).
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatR, encSymR_bumpSymR.
    exact (pev (step_BB_zero _ _)).
  - unfold evalNat, evalSym; simpl.
    exact (pev (step_BB_run0 _ _)).
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatR, encSymR_bumpSymR.
    exact (pev (step_BB_run1 _ _)).
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatR, encSymR_bumpSymR.
    exact (pev (step_BB_run2 _ _)).
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatR, encSymR_bumpSymR.
    exact (pev (step_BB_run3 _ _)).
  - unfold evalNat, evalSym; cbn [map natTokToSym encSymL encSymR evalM].
    rewrite map_bumpNatR, encSymR_bumpSymR.
    replace (N.of_nat (S (S (S (S d))))) with (N.of_nat d + 4) by lia.
    exact (pev (step_BB_run_ge4 (N.of_nat d) _ _)).
Qed.

Lemma stepNatDL_sound (L R : list NatTok) :
  evalNat (DL, L, R) -->* evalNat (stepNatDL L R).
Proof.
  destruct L as [| t L1]; [apply evstep_refl |].
  destruct t as [| [| [| [| d]]] | k | p | m]; cbn [stepNatDL]; try apply evstep_refl.
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatR, encSymR_bumpSymR.
    exact (pev (step_DL_run0 _ _)).
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatR, encSymR_bumpSymR.
    exact (pev (step_DL_run1 _ _)).
  - destruct R as [| rt R1]; [apply evstep_refl |].
    destruct rt as [| d0 | | |]; [apply evstep_refl | | apply evstep_refl | apply evstep_refl | apply evstep_refl].
    unfold evalNat, evalSym; cbn [map natTokToSym encSymL encSymR evalM].
    rewrite map_prependZeroNat, encSymL_prependZeroSymNat.
    pose proof (step_DL_run2 (N.of_nat d0) (encSymL (map natTokToSym L1)) (encSymR (map natTokToSym R1))) as h.
    unfold nreplicate in h.
    replace (N.to_nat (N.of_nat d0 + 1)) with (S d0) in h by lia.
    exact (pev h).
Qed.

Lemma stepNatCB_run0_sound (L R1 : list NatTok) :
  evalNat (CB, L, NTRun 0%nat :: R1) -->* evalNat (stepNatCB_run0 L R1).
Proof.
  destruct R1 as [| rt R2]; [| destruct rt as [| [| d2] | k | p | m]];
    cbn [stepNatCB_run0]; try apply evstep_refl.
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatL, encSymL_bumpSymL.
    exact (pev (step_CB_run0_nil _)).
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatL, encSymL_bumpSymL.
    exact (pev (step_CB_run0_zero _ _)).
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatL, encSymL_bumpSymL.
    exact (pev (step_CB_run0_run0 _ _)).
  - unfold evalNat, evalSym; cbn [map natTokToSym encSymL encSymR evalM].
    rewrite map_prependZeroNat, encSymL_prependZeroSymNat, map_bumpNatL, encSymL_bumpSymL.
    pose proof (step_CB_run0_run_pos (N.of_nat d2) (encSymL (map natTokToSym L)) (encSymR (map natTokToSym R2))) as h.
    unfold nreplicate in h.
    replace (N.of_nat (S d2)) with (N.of_nat d2 + 1) by lia.
    rewrite Nat2N.id in h.
    exact (pev h).
Qed.

Lemma stepNatCB_sound (L R : list NatTok) :
  evalNat (CB, L, R) -->* evalNat (stepNatCB L R).
Proof.
  destruct R as [| t R1]; [| destruct t as [| [| [| [| d]]] | k | p | m]];
    cbn [stepNatCB]; try apply evstep_refl.
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatL, encSymL_bumpSymL.
    exact (pev (step_CB_nil _)).
  - unfold evalNat, evalSym; simpl.
    rewrite map_bumpNatL, encSymL_bumpSymL, map_bumpNatR, encSymR_bumpSymR.
    exact (pev (step_CB_zero _ _)).
  - exact (stepNatCB_run0_sound L R1).
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatL, encSymL_bumpSymL.
    exact (pev (step_CB_run1 _ _)).
  - unfold evalNat, evalSym; simpl. rewrite map_bumpNatL, encSymL_bumpSymL.
    exact (pev (step_CB_run2 _ _)).
  - unfold evalNat, evalSym; cbn [map natTokToSym encSymL encSymR evalM].
    rewrite map_bumpNatL, encSymL_bumpSymL.
    replace (N.of_nat (S (S (S d)))) with (N.of_nat d + 3) by lia.
    exact (pev (step_CB_run_ge3 (N.of_nat d) _ _)).
Qed.

Lemma stepPureBB_sound (L R : list NatTok) :
  evalNat (BB, L, R) -->* evalNat (stepPureBB L R).
Proof.
  destruct L as [| t L1]; [exact (stepNatBB_sound [] R) |].
  destruct t as [| d | k | p | m]; cbn [stepPureBB].
  - exact (stepNatBB_sound (NTZero :: L1) R).
  - exact (stepNatBB_sound (NTRun d :: L1) R).
  - unfold evalNat, evalSym; simpl.
    exact (sweep_BB_B1 (N.of_nat k) _ _).
  - destruct (stripPrefixNat [NTRun 0%nat; NTRun 1%nat] R) as [R2 |] eqn:hs.
    + pose proof (stripPrefixNat_some _ R R2 hs) as ->.
      unfold evalNat, evalSym; simpl.
      exact (sweep_BB_C2 (N.of_nat p) _ _).
    + assert (heq : evalNat (BB, NTRep2 p :: L1, R) = evalNat (BB, peelPureTok (NTRep2 p) L1, R)).
      { unfold evalNat, evalSym; rewrite encSymL_peelPureTok; reflexivity. }
      rewrite heq; exact (stepNatBB_sound (peelPureTok (NTRep2 p) L1) R).
  - destruct (stripPrefixNat [NTRun 0%nat; NTRun 1%nat] R) as [R2 |] eqn:hs.
    + pose proof (stripPrefixNat_some _ R R2 hs) as ->.
      unfold evalNat, evalSym; simpl.
      exact (sweep_BB_C12 (N.of_nat m) _ _).
    + assert (heq : evalNat (BB, NTRep12 m :: L1, R) = evalNat (BB, peelPureTok (NTRep12 m) L1, R)).
      { unfold evalNat, evalSym; rewrite encSymL_peelPureTok; reflexivity. }
      rewrite heq; exact (stepNatBB_sound (peelPureTok (NTRep12 m) L1) R).
Qed.

Lemma stepPureDL_sound (L R : list NatTok) :
  evalNat (DL, L, R) -->* evalNat (stepPureDL L R).
Proof.
  destruct L as [| t L1]; cbn [stepPureDL]; [apply evstep_refl |].
  assert (heq : evalNat (DL, t :: L1, R) = evalNat (DL, peelPureTok t L1, R)).
  { unfold evalNat, evalSym; rewrite encSymL_peelPureTok; reflexivity. }
  rewrite heq; exact (stepNatDL_sound (peelPureTok t L1) R).
Qed.

Lemma stepPureCB_sound (L R : list NatTok) :
  evalNat (CB, L, R) -->* evalNat (stepPureCB L R).
Proof.
  destruct R as [| t R1]; [exact (stepNatCB_sound L []) |].
  destruct t as [| [| [| [| d]]] | k | p | m]; cbn [stepPureCB].
  - exact (stepNatCB_sound L (NTZero :: R1)).
  - exact (stepNatCB_run0_sound L R1).
  - exact (stepNatCB_sound L (NTRun 1%nat :: R1)).
  - exact (stepNatCB_sound L (NTRun 2%nat :: R1)).
  - unfold evalNat, evalSym; cbn [map natTokToSym encSymL encSymR evalM].
    rewrite map_bumpNatL, encSymL_bumpSymL.
    replace (N.of_nat (S (S (S d)))) with (N.of_nat d + 3) by lia.
    exact (pev (step_CB_run_ge3 (N.of_nat d) _ _)).
  - destruct (stripPrefixNat [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat] L) as [L2 |] eqn:hs2.
    + pose proof (stripPrefixNat_some _ L L2 hs2) as ->.
      unfold evalNat, evalSym; cbn [map natTokToSym encSymL encSymR evalM].
      replace (N.of_nat (S k)) with (N.of_nat k + 1) by lia.
      rewrite repBlock_succ_r, <- app_assoc.
      exact (sweep_CB_B1 (N.of_nat k) (MRun 0 :: MRun 1 :: _) _).
    + destruct (stripPrefixNat [NTRun 0%nat] L) as [L1 |] eqn:hs1; [| apply evstep_refl].
      pose proof (stripPrefixNat_some _ L L1 hs1) as ->.
      unfold evalNat, evalSym; simpl.
      exact (sweep_CB_B1 (N.of_nat k) _ _).
  - destruct (stripPrefixNat [NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat] L) as [L2 |] eqn:hs2.
    + pose proof (stripPrefixNat_some _ L L2 hs2) as ->.
      unfold evalNat, evalSym; cbn [map natTokToSym encSymL encSymR evalM].
      replace (N.of_nat (S p)) with (N.of_nat p + 1) by lia.
      rewrite repBlock_succ_r, <- app_assoc.
      exact (sweep_CB_B2 (N.of_nat p) (MRun 1 :: MRun 0 :: MRun 1 :: _) _).
    + destruct (stripPrefixNat [NTRun 0%nat] L) as [L1 |] eqn:hs1; [| apply evstep_refl].
      pose proof (stripPrefixNat_some _ L L1 hs1) as ->.
      unfold evalNat, evalSym; simpl.
      exact (sweep_CB_B2 (N.of_nat p) _ _).
  - destruct (stripPrefixNat [NTRun 0%nat] L) as [L1 |] eqn:hs1; [| apply evstep_refl].
    pose proof (stripPrefixNat_some _ L L1 hs1) as ->.
    unfold evalNat, evalSym; simpl.
    exact (sweep_CB_B12R (N.of_nat m) _ _).
Qed.

Lemma stepPure_sound (s : SymMode * list NatTok * list NatTok) :
  evalNat s -->* evalNat (stepPure s).
Proof.
  destruct s as [[m ls] rs]; destruct m.
  - exact (stepPureBB_sound ls rs).
  - exact (stepPureDL_sound ls rs).
  - exact (stepPureCB_sound ls rs).
  - apply evstep_refl.
Qed.

Definition sep3A : list SymTok := [STItem (MRun 0); STItem (MRun 1); STItem (MRun 2)].
Definition sep3B : list SymTok := [STItem (MRun 0); STItem MZero; STItem (MRun 1)].

Definition sep3A_nat : list NatTok := [NTRun 0%nat; NTRun 1%nat; NTRun 2%nat].
Definition sep3B_nat : list NatTok := [NTRun 0%nat; NTZero; NTRun 1%nat].

Definition stateA0_nat (k d : nat) (R_tail : list NatTok) : SymMode * list NatTok * list NatTok :=
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat;
    NTRun 1%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat; NTZero;
    NTRun 1%nat; NTRepB1 k; NTRun 0%nat],
   NTRun d :: R_tail).

Definition stateA_nat (m k d : nat) (R_tail : list NatTok) : SymMode * list NatTok * list NatTok :=
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat;
    NTRun 1%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRep12 m; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat;
    NTZero; NTRun 1%nat; NTRepB1 k; NTRun 0%nat],
   NTRun d :: R_tail).

Definition stateC_nat (p k d2 : nat) (R_tail : list NatTok) : SymMode * list NatTok * list NatTok :=
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 p;
    NTRun 0%nat; NTRun 1%nat; NTRun 1%nat; NTRun 1%nat;
    NTRepB1 k; NTRun 0%nat],
   NTZero :: NTRun d2 :: R_tail).

Definition stateB_nat (s_sep m_sep : list NatTok) (p m k d2 : nat) (R_tail : list NatTok) :
    SymMode * list NatTok * list NatTok :=
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 p; NTRun 1%nat] ++
     s_sep ++ [NTRep12 m; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat] ++
     m_sep ++ [NTRepB1 k; NTRun 0%nat],
   NTZero :: NTRun d2 :: R_tail).

Lemma test_ruleA0 (k d : nat) (R_tail : list NatTok) :
  iter stepPure 46%nat (stateA0_nat (S k) (6 + d)%nat R_tail) =
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat;
    NTRun 1%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat;
    NTZero; NTRun 1%nat; NTRepB1 k; NTRun 0%nat],
   NTRun d :: R_tail).
Proof. reflexivity. Qed.

Lemma test_ruleA_step (m k d : nat) (R_tail : list NatTok) :
  iter stepPure 66%nat (stateA_nat m (S k) (6 + d)%nat R_tail) =
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat;
    NTRun 1%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRep12 m; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat;
    NTZero; NTRun 1%nat; NTRepB1 k; NTRun 0%nat],
   NTRun d :: R_tail).
Proof. reflexivity. Qed.

Lemma test_ruleC_step (p k d2 : nat) (R_tail : list NatTok) :
  iter stepPure 46%nat (stateC_nat (3 + p)%nat (S k) d2 R_tail) =
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 (2 + p)%nat;
    NTRun 0%nat; NTRun 1%nat; NTRun 1%nat; NTRun 1%nat;
    NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRepB1 (S k); NTRun 0%nat],
   NTZero :: NTRun (S (S d2)) :: R_tail).
Proof. reflexivity. Qed.

Lemma test_ruleB_AA (p m k d2 : nat) (R_tail : list NatTok) :
  iter stepPure 126%nat (stateB_nat sep3A_nat sep3A_nat (S p) (2 + m)%nat (S k) d2 R_tail) =
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 (3 + p)%nat; NTRun 1%nat;
    NTRun 0%nat; NTRun 1%nat; NTRun 2%nat; NTRep12 m;
    NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRun 0%nat; NTRun 1%nat; NTRun 2%nat; NTRepB1 k; NTRun 0%nat],
   NTZero :: NTRun (4 + d2)%nat :: R_tail).
Proof. reflexivity. Qed.

Lemma test_ruleB_AB (p m k d2 : nat) (R_tail : list NatTok) :
  iter stepPure 118%nat (stateB_nat sep3A_nat sep3B_nat (S p) (2 + m)%nat (S k) d2 R_tail) =
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 (3 + p)%nat; NTRun 1%nat;
    NTRun 0%nat; NTRun 1%nat; NTRun 2%nat; NTRep12 m;
    NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRun 0%nat; NTZero; NTRun 1%nat; NTRepB1 k; NTRun 0%nat],
   NTZero :: NTRun (4 + d2)%nat :: R_tail).
Proof. reflexivity. Qed.

Lemma test_ruleB_BA (p m k d2 : nat) (R_tail : list NatTok) :
  iter stepPure 106%nat (stateB_nat sep3B_nat sep3A_nat (S p) (2 + m)%nat (S k) d2 R_tail) =
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 (3 + p)%nat; NTRun 1%nat;
    NTRun 0%nat; NTZero; NTRun 1%nat; NTRep12 m;
    NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRun 0%nat; NTRun 1%nat; NTRun 2%nat; NTRepB1 k; NTRun 0%nat],
   NTZero :: NTRun (4 + d2)%nat :: R_tail).
Proof. reflexivity. Qed.

Lemma test_ruleB_BB (p m k d2 : nat) (R_tail : list NatTok) :
  iter stepPure 98%nat (stateB_nat sep3B_nat sep3B_nat (S p) (2 + m)%nat (S k) d2 R_tail) =
  (CB,
   [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 (3 + p)%nat; NTRun 1%nat;
    NTRun 0%nat; NTZero; NTRun 1%nat; NTRep12 m;
    NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
    NTRun 0%nat; NTZero; NTRun 1%nat; NTRepB1 k; NTRun 0%nat],
   NTZero :: NTRun (4 + d2)%nat :: R_tail).
Proof. reflexivity. Qed.

Definition stateA0 (k d : N) (R_tail : list SymTok) : SymMode * list SymTok * list SymTok :=
  (CB,
   [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0);
    STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem MZero;
    STItem (MRun 1); STRepB1 k; STItem (MRun 0)],
   STItem (MRun d) :: R_tail).

Definition stateA (m k d : N) (R_tail : list SymTok) : SymMode * list SymTok * list SymTok :=
  (CB,
   [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0);
    STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1);
    STRep12 m; STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0);
    STItem MZero; STItem (MRun 1); STRepB1 k; STItem (MRun 0)],
   STItem (MRun d) :: R_tail).

Definition stateC (p k d2 : N) (R_tail : list SymTok) : SymMode * list SymTok * list SymTok :=
  (CB,
   [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STRep2 p;
    STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1);
    STRepB1 k; STItem (MRun 0)],
   STItem MZero :: STItem (MRun d2) :: R_tail).

Definition stateB (s_sep m_sep : list SymTok) (p m k d2 : N) (R_tail : list SymTok) :
    SymMode * list SymTok * list SymTok :=
  (CB,
   [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STRep2 p; STItem (MRun 1)] ++
     s_sep ++ [STRep12 m; STItem (MRun 1); STItem (MRun 0); STItem (MRun 1)] ++
     m_sep ++ [STRepB1 k; STItem (MRun 0)],
   STItem MZero :: STItem (MRun d2) :: R_tail).

Lemma repBlock12_snoc (m : N) (xs : list MItem) :
  repBlock [MRun 1; MRun 0; MRun 1; MRun 0; MRun 1] m ++
    (MRun 1 :: MRun 0 :: MRun 1 :: MRun 0 :: MRun 1 :: xs) =
  repBlock [MRun 1; MRun 0; MRun 1; MRun 0; MRun 1] (m + 1) ++ xs.
Proof.
  rewrite repBlock_succ_r, <- app_assoc; reflexivity.
Qed.

Lemma ruleA0_sound (k d : N) (R_tail : list SymTok) :
  evalSym (stateA0 (k + 1) (d + 6) R_tail) -->*
  evalSym (stateA 0 k d R_tail).
Proof.
  pose proof (iter_sound stepPure evalNat stepPure_sound 46%nat
    (stateA0_nat (S (N.to_nat k)) (6 + N.to_nat d)%nat (map symTokToNat R_tail))) as h.
  rewrite test_ruleA0 in h.
  assert (heq1 : evalNat (stateA0_nat (S (N.to_nat k)) (6 + N.to_nat d)%nat (map symTokToNat R_tail)) =
                 evalSym (stateA0 (k + 1) (d + 6) R_tail)).
  { unfold evalNat, stateA0_nat, stateA0; cbn [map natTokToSym].
    rewrite map_natTokToSym_symTokToNat.
    replace (N.of_nat (S (N.to_nat k))) with (k + 1) by lia.
    replace (N.of_nat (6 + N.to_nat d)) with (d + 6) by lia.
    reflexivity. }
  assert (heq2 : evalNat (CB,
     [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat;
      NTRun 1%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat;
      NTZero; NTRun 1%nat; NTRepB1 (N.to_nat k); NTRun 0%nat],
     NTRun (N.to_nat d) :: map symTokToNat R_tail) =
     evalSym (stateA 0 k d R_tail)).
  { unfold evalNat, stateA, evalSym; cbn [map natTokToSym encSymL encSymR repBlock repBlockNat app].
    rewrite map_natTokToSym_symTokToNat, !N2Nat.id; reflexivity. }
  rewrite <- heq1, <- heq2; exact h.
Qed.

Lemma ruleA_step_sound (m k d : N) (R_tail : list SymTok) :
  evalSym (stateA m (k + 1) (d + 6) R_tail) -->*
  evalSym (stateA (m + 1) k d R_tail).
Proof.
  pose proof (iter_sound stepPure evalNat stepPure_sound 66%nat
    (stateA_nat (N.to_nat m) (S (N.to_nat k)) (6 + N.to_nat d)%nat (map symTokToNat R_tail))) as h.
  rewrite test_ruleA_step in h.
  assert (heq1 : evalNat (stateA_nat (N.to_nat m) (S (N.to_nat k)) (6 + N.to_nat d)%nat (map symTokToNat R_tail)) =
                 evalSym (stateA m (k + 1) (d + 6) R_tail)).
  { unfold evalNat, stateA_nat, stateA; cbn [map natTokToSym].
    rewrite map_natTokToSym_symTokToNat, N2Nat.id.
    replace (N.of_nat (S (N.to_nat k))) with (k + 1) by lia.
    replace (N.of_nat (6 + N.to_nat d)) with (d + 6) by lia.
    reflexivity. }
  assert (heq2 : evalNat (CB,
     [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat;
      NTRun 1%nat; NTRun 1%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRep12 (N.to_nat m); NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat;
      NTZero; NTRun 1%nat; NTRepB1 (N.to_nat k); NTRun 0%nat],
     NTRun (N.to_nat d) :: map symTokToNat R_tail) =
     evalSym (stateA (m + 1) k d R_tail)).
  { unfold evalNat, stateA, evalSym; cbn [map natTokToSym encSymL encSymR app].
    rewrite map_natTokToSym_symTokToNat, !N2Nat.id.
    rewrite repBlock12_snoc; reflexivity. }
  rewrite <- heq1, <- heq2; exact h.
Qed.

Lemma ruleA_iter (n : N) : forall (m k d : N) (R_tail : list SymTok),
  evalSym (stateA m (k + n) (d + 6 * n) R_tail) -->*
  evalSym (stateA (m + n) k d R_tail).
Proof.
  induction n using N_peano_ind; intros m k d R_tail.
  - replace (k + 0) with k by lia.
    replace (d + 6 * 0) with d by lia.
    replace (m + 0) with m by lia.
    apply evstep_refl.
  - replace (k + (n + 1)) with ((k + n) + 1) by lia.
    replace (d + 6 * (n + 1)) with ((d + 6 * n) + 6) by lia.
    replace (m + (n + 1)) with ((m + 1) + n) by lia.
    exact (etrans (ruleA_step_sound m (k + n) (d + 6 * n) R_tail) (IHn (m + 1) k d R_tail)).
Qed.

Lemma ruleC_step_sound (p k d2 : N) (R_tail : list SymTok) :
  evalSym (stateC (p + 3) (k + 1) d2 R_tail) -->*
  evalSym (stateC (p + 2) (k + 3) (d2 + 2) R_tail).
Proof.
  pose proof (iter_sound stepPure evalNat stepPure_sound 46%nat
    (stateC_nat (3 + N.to_nat p)%nat (S (N.to_nat k)) (N.to_nat d2) (map symTokToNat R_tail))) as h.
  rewrite test_ruleC_step in h.
  assert (heq1 : evalNat (stateC_nat (3 + N.to_nat p)%nat (S (N.to_nat k)) (N.to_nat d2) (map symTokToNat R_tail)) =
                 evalSym (stateC (p + 3) (k + 1) d2 R_tail)).
  { unfold evalNat, stateC_nat, stateC; cbn [map natTokToSym].
    rewrite map_natTokToSym_symTokToNat, N2Nat.id.
    replace (N.of_nat (3 + N.to_nat p)) with (p + 3) by lia.
    replace (N.of_nat (S (N.to_nat k))) with (k + 1) by lia.
    reflexivity. }
  assert (heq2 : evalNat (CB,
     [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 (2 + N.to_nat p)%nat;
      NTRun 0%nat; NTRun 1%nat; NTRun 1%nat; NTRun 1%nat;
      NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRepB1 (S (N.to_nat k)); NTRun 0%nat],
     NTZero :: NTRun (S (S (N.to_nat d2))) :: map symTokToNat R_tail) =
     evalSym (stateC (p + 2) (k + 3) (d2 + 2) R_tail)).
  { unfold evalNat, stateC, evalSym; cbn [map natTokToSym encSymL encSymR app].
    rewrite map_natTokToSym_symTokToNat.
    replace (N.of_nat (2 + N.to_nat p)) with (p + 2) by lia.
    replace (N.of_nat (S (S (N.to_nat d2)))) with (d2 + 2) by lia.
    replace (k + 3) with ((k + 1 + 1) + 1) by lia.
    replace (N.of_nat (S (N.to_nat k))) with (k + 1) by lia.
    rewrite (repBlock_succ_l [MRun 0; MRun 1] (k + 1 + 1)).
    rewrite (repBlock_succ_l [MRun 0; MRun 1] (k + 1)).
    reflexivity. }
  rewrite <- heq1, <- heq2; exact h.
Qed.

Lemma ruleC_iter (n : N) : forall (p k d2 : N) (R_tail : list SymTok),
  1 <= k ->
  evalSym (stateC (p + n + 2) k d2 R_tail) -->*
  evalSym (stateC (p + 2) (k + 2 * n) (d2 + 2 * n) R_tail).
Proof.
  induction n using N_peano_ind; intros p k d2 R_tail hk.
  - replace (p + 0 + 2) with (p + 2) by lia.
    replace (k + 2 * 0) with k by lia.
    replace (d2 + 2 * 0) with d2 by lia.
    apply evstep_refl.
  - replace (p + (n + 1) + 2) with ((p + n) + 3) by lia.
    replace k with ((k - 1) + 1) at 1 by lia.
    replace (k + 2 * (n + 1)) with (((k - 1) + 3) + 2 * n) by lia.
    replace (d2 + 2 * (n + 1)) with ((d2 + 2) + 2 * n) by lia.
    eapply etrans; [exact (ruleC_step_sound (p + n) (k - 1) d2 R_tail) |].
    apply IHn; lia.
Qed.

Lemma ruleB_step_AA (p m k d2 : N) (R_tail : list SymTok) :
  evalSym (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) -->*
  evalSym (stateB sep3A sep3A (p + 3) (m + 1) k (d2 + 4) R_tail).
Proof.
  pose proof (iter_sound stepPure evalNat stepPure_sound 126%nat
    (stateB_nat sep3A_nat sep3A_nat (S (N.to_nat p)) (2 + N.to_nat m)%nat (S (N.to_nat k)) (N.to_nat d2) (map symTokToNat R_tail))) as h.
  rewrite test_ruleB_AA in h.
  assert (heq1 : evalNat (stateB_nat sep3A_nat sep3A_nat (S (N.to_nat p)) (2 + N.to_nat m)%nat (S (N.to_nat k)) (N.to_nat d2) (map symTokToNat R_tail)) =
                 evalSym (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)).
  { unfold evalNat, stateB_nat, stateB, sep3A_nat, sep3A; cbn [map natTokToSym app].
    rewrite map_natTokToSym_symTokToNat, N2Nat.id.
    replace (N.of_nat (S (N.to_nat p))) with (p + 1) by lia.
    replace (N.of_nat (2 + N.to_nat m)) with (m + 2) by lia.
    replace (N.of_nat (S (N.to_nat k))) with (k + 1) by lia.
    reflexivity. }
  assert (heq2 : evalNat (CB,
     [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 (3 + N.to_nat p)%nat; NTRun 1%nat;
      NTRun 0%nat; NTRun 1%nat; NTRun 2%nat; NTRep12 (N.to_nat m);
      NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRun 0%nat; NTRun 1%nat; NTRun 2%nat; NTRepB1 (N.to_nat k); NTRun 0%nat],
     NTZero :: NTRun (4 + N.to_nat d2)%nat :: map symTokToNat R_tail) =
     evalSym (stateB sep3A sep3A (p + 3) (m + 1) k (d2 + 4) R_tail)).
  { unfold evalNat, stateB, sep3A, evalSym; cbn [map natTokToSym encSymL encSymR app].
    rewrite map_natTokToSym_symTokToNat, !N2Nat.id.
    replace (N.of_nat (3 + N.to_nat p)) with (p + 3) by lia.
    replace (N.of_nat (4 + N.to_nat d2)) with (d2 + 4) by lia.
    rewrite repBlock12_snoc; reflexivity. }
  rewrite <- heq1, <- heq2; exact h.
Qed.

Lemma ruleB_step_AB (p m k d2 : N) (R_tail : list SymTok) :
  evalSym (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) -->*
  evalSym (stateB sep3A sep3B (p + 3) (m + 1) k (d2 + 4) R_tail).
Proof.
  pose proof (iter_sound stepPure evalNat stepPure_sound 118%nat
    (stateB_nat sep3A_nat sep3B_nat (S (N.to_nat p)) (2 + N.to_nat m)%nat (S (N.to_nat k)) (N.to_nat d2) (map symTokToNat R_tail))) as h.
  rewrite test_ruleB_AB in h.
  assert (heq1 : evalNat (stateB_nat sep3A_nat sep3B_nat (S (N.to_nat p)) (2 + N.to_nat m)%nat (S (N.to_nat k)) (N.to_nat d2) (map symTokToNat R_tail)) =
                 evalSym (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)).
  { unfold evalNat, stateB_nat, stateB, sep3A_nat, sep3B_nat, sep3A, sep3B; cbn [map natTokToSym app].
    rewrite map_natTokToSym_symTokToNat, N2Nat.id.
    replace (N.of_nat (S (N.to_nat p))) with (p + 1) by lia.
    replace (N.of_nat (2 + N.to_nat m)) with (m + 2) by lia.
    replace (N.of_nat (S (N.to_nat k))) with (k + 1) by lia.
    reflexivity. }
  assert (heq2 : evalNat (CB,
     [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 (3 + N.to_nat p)%nat; NTRun 1%nat;
      NTRun 0%nat; NTRun 1%nat; NTRun 2%nat; NTRep12 (N.to_nat m);
      NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRun 0%nat; NTZero; NTRun 1%nat; NTRepB1 (N.to_nat k); NTRun 0%nat],
     NTZero :: NTRun (4 + N.to_nat d2)%nat :: map symTokToNat R_tail) =
     evalSym (stateB sep3A sep3B (p + 3) (m + 1) k (d2 + 4) R_tail)).
  { unfold evalNat, stateB, sep3A, sep3B, evalSym; cbn [map natTokToSym encSymL encSymR app].
    rewrite map_natTokToSym_symTokToNat, !N2Nat.id.
    replace (N.of_nat (3 + N.to_nat p)) with (p + 3) by lia.
    replace (N.of_nat (4 + N.to_nat d2)) with (d2 + 4) by lia.
    rewrite repBlock12_snoc; reflexivity. }
  rewrite <- heq1, <- heq2; exact h.
Qed.

Lemma ruleB_step_BA (p m k d2 : N) (R_tail : list SymTok) :
  evalSym (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) -->*
  evalSym (stateB sep3B sep3A (p + 3) (m + 1) k (d2 + 4) R_tail).
Proof.
  pose proof (iter_sound stepPure evalNat stepPure_sound 106%nat
    (stateB_nat sep3B_nat sep3A_nat (S (N.to_nat p)) (2 + N.to_nat m)%nat (S (N.to_nat k)) (N.to_nat d2) (map symTokToNat R_tail))) as h.
  rewrite test_ruleB_BA in h.
  assert (heq1 : evalNat (stateB_nat sep3B_nat sep3A_nat (S (N.to_nat p)) (2 + N.to_nat m)%nat (S (N.to_nat k)) (N.to_nat d2) (map symTokToNat R_tail)) =
                 evalSym (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)).
  { unfold evalNat, stateB_nat, stateB, sep3A_nat, sep3B_nat, sep3A, sep3B; cbn [map natTokToSym app].
    rewrite map_natTokToSym_symTokToNat, N2Nat.id.
    replace (N.of_nat (S (N.to_nat p))) with (p + 1) by lia.
    replace (N.of_nat (2 + N.to_nat m)) with (m + 2) by lia.
    replace (N.of_nat (S (N.to_nat k))) with (k + 1) by lia.
    reflexivity. }
  assert (heq2 : evalNat (CB,
     [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 (3 + N.to_nat p)%nat; NTRun 1%nat;
      NTRun 0%nat; NTZero; NTRun 1%nat; NTRep12 (N.to_nat m);
      NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRun 0%nat; NTRun 1%nat; NTRun 2%nat; NTRepB1 (N.to_nat k); NTRun 0%nat],
     NTZero :: NTRun (4 + N.to_nat d2)%nat :: map symTokToNat R_tail) =
     evalSym (stateB sep3B sep3A (p + 3) (m + 1) k (d2 + 4) R_tail)).
  { unfold evalNat, stateB, sep3A, sep3B, evalSym; cbn [map natTokToSym encSymL encSymR app].
    rewrite map_natTokToSym_symTokToNat, !N2Nat.id.
    replace (N.of_nat (3 + N.to_nat p)) with (p + 3) by lia.
    replace (N.of_nat (4 + N.to_nat d2)) with (d2 + 4) by lia.
    rewrite repBlock12_snoc; reflexivity. }
  rewrite <- heq1, <- heq2; exact h.
Qed.

Lemma ruleB_step_BB (p m k d2 : N) (R_tail : list SymTok) :
  evalSym (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) -->*
  evalSym (stateB sep3B sep3B (p + 3) (m + 1) k (d2 + 4) R_tail).
Proof.
  pose proof (iter_sound stepPure evalNat stepPure_sound 98%nat
    (stateB_nat sep3B_nat sep3B_nat (S (N.to_nat p)) (2 + N.to_nat m)%nat (S (N.to_nat k)) (N.to_nat d2) (map symTokToNat R_tail))) as h.
  rewrite test_ruleB_BB in h.
  assert (heq1 : evalNat (stateB_nat sep3B_nat sep3B_nat (S (N.to_nat p)) (2 + N.to_nat m)%nat (S (N.to_nat k)) (N.to_nat d2) (map symTokToNat R_tail)) =
                 evalSym (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)).
  { unfold evalNat, stateB_nat, stateB, sep3B_nat, sep3B; cbn [map natTokToSym app].
    rewrite map_natTokToSym_symTokToNat, N2Nat.id.
    replace (N.of_nat (S (N.to_nat p))) with (p + 1) by lia.
    replace (N.of_nat (2 + N.to_nat m)) with (m + 2) by lia.
    replace (N.of_nat (S (N.to_nat k))) with (k + 1) by lia.
    reflexivity. }
  assert (heq2 : evalNat (CB,
     [NTRun 0%nat; NTRun 0%nat; NTRun 1%nat; NTRep2 (3 + N.to_nat p)%nat; NTRun 1%nat;
      NTRun 0%nat; NTZero; NTRun 1%nat; NTRep12 (N.to_nat m);
      NTRun 1%nat; NTRun 0%nat; NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRun 1%nat; NTRun 0%nat; NTRun 1%nat;
      NTRun 0%nat; NTZero; NTRun 1%nat; NTRepB1 (N.to_nat k); NTRun 0%nat],
     NTZero :: NTRun (4 + N.to_nat d2)%nat :: map symTokToNat R_tail) =
     evalSym (stateB sep3B sep3B (p + 3) (m + 1) k (d2 + 4) R_tail)).
  { unfold evalNat, stateB, sep3B, evalSym; cbn [map natTokToSym encSymL encSymR app].
    rewrite map_natTokToSym_symTokToNat, !N2Nat.id.
    replace (N.of_nat (3 + N.to_nat p)) with (p + 3) by lia.
    replace (N.of_nat (4 + N.to_nat d2)) with (d2 + 4) by lia.
    rewrite repBlock12_snoc; reflexivity. }
  rewrite <- heq1, <- heq2; exact h.
Qed.

Lemma ruleB_step_sound (s_sep m_sep : list SymTok)
  (hs : s_sep = sep3A \/ s_sep = sep3B)
  (hm : m_sep = sep3A \/ m_sep = sep3B)
  (p m k d2 : N) (R_tail : list SymTok) :
  evalSym (stateB s_sep m_sep (p + 1) (m + 2) (k + 1) d2 R_tail) -->*
  evalSym (stateB s_sep m_sep (p + 3) (m + 1) k (d2 + 4) R_tail).
Proof.
  destruct hs as [-> | ->]; destruct hm as [-> | ->].
  - exact (ruleB_step_AA p m k d2 R_tail).
  - exact (ruleB_step_AB p m k d2 R_tail).
  - exact (ruleB_step_BA p m k d2 R_tail).
  - exact (ruleB_step_BB p m k d2 R_tail).
Qed.

Lemma ruleB_iter (s_sep m_sep : list SymTok)
  (hs : s_sep = sep3A \/ s_sep = sep3B)
  (hm : m_sep = sep3A \/ m_sep = sep3B)
  (n : N) : forall (p m k d2 : N) (R_tail : list SymTok),
  evalSym (stateB s_sep m_sep (p + 1) (m + n + 1) (k + n) d2 R_tail) -->*
  evalSym (stateB s_sep m_sep (p + 1 + 2 * n) (m + 1) k (d2 + 4 * n) R_tail).
Proof.
  induction n using N_peano_ind; intros p m k d2 R_tail.
  - replace (m + 0 + 1) with (m + 1) by lia.
    replace (k + 0) with k by lia.
    replace (p + 1 + 2 * 0) with (p + 1) by lia.
    replace (d2 + 4 * 0) with d2 by lia.
    apply evstep_refl.
  - replace (m + (n + 1) + 1) with ((m + n) + 2) by lia.
    replace (k + (n + 1)) with ((k + n) + 1) by lia.
    replace (p + 1 + 2 * (n + 1)) with ((p + 2) + 1 + 2 * n) by lia.
    replace (d2 + 4 * (n + 1)) with ((d2 + 4) + 4 * n) by lia.
    eapply etrans; [exact (ruleB_step_sound s_sep m_sep hs hm p (m + n) (k + n) d2 R_tail) |].
    replace (p + 3) with ((p + 2) + 1) by lia.
    exact (IHn (p + 2) m k (d2 + 4) R_tail).
Qed.

Fixpoint splitB2Aux (fuel : nat) (p : N) (xs : list SymTok) : N * list SymTok :=
  match fuel with
  | 0%nat => (p, xs)
  | S fuel' =>
    match stripPrefixSym [STItem (MRun 0); STItem (MRun 1); STItem (MRun 1)] xs with
    | Some rest => splitB2Aux fuel' (p + 1) rest
    | None => (p, xs)
    end
  end.

Definition splitB2 (p : N) (xs : list SymTok) : N * list SymTok :=
  splitB2Aux 16%nat p xs.

Lemma splitB2Aux_spec (fuel : nat) : forall (p : N) (xs : list SymTok),
  repBlock [MRun 0; MRun 1; MRun 1] p ++ encSymL xs =
  repBlock [MRun 0; MRun 1; MRun 1] (fst (splitB2Aux fuel p xs)) ++
    encSymL (snd (splitB2Aux fuel p xs)).
Proof.
  induction fuel as [| fuel ih]; intros p xs; [reflexivity |].
  cbn [splitB2Aux].
  destruct (stripPrefixSym [STItem (MRun 0); STItem (MRun 1); STItem (MRun 1)] xs) as [rest |] eqn:hs;
    [| reflexivity].
  pose proof (stripPrefixSym_some _ xs rest hs) as ->.
  rewrite <- (ih (p + 1) rest).
  rewrite (repBlock_succ_r [MRun 0; MRun 1; MRun 1] p), <- app_assoc.
  reflexivity.
Qed.

Lemma repBlock_B2_shift (q : N) : forall (tail : list MItem),
  MRun 0 :: (repBlock [MRun 0; MRun 1; MRun 1] (q + 1) ++ tail) =
  [MRun 0; MRun 0; MRun 1] ++ (repBlock [MRun 1; MRun 0; MRun 1] q ++ (MRun 1 :: tail)).
Proof.
  induction q using N_peano_ind; intro tail.
  - reflexivity.
  - rewrite (repBlock_succ_r [MRun 0; MRun 1; MRun 1] (q + 1)), <- app_assoc.
    cbn [app].
    rewrite (IHq (MRun 0 :: MRun 1 :: MRun 1 :: tail)).
    rewrite (repBlock_succ_r [MRun 1; MRun 0; MRun 1] q), <- app_assoc.
    reflexivity.
Qed.

Definition popSep3 (xs : list SymTok) : option (list SymTok * list SymTok) :=
  match stripPrefixSym sep3A xs with
  | Some rest => Some (sep3A, rest)
  | None =>
    match stripPrefixSym sep3B xs with
    | Some rest => Some (sep3B, rest)
    | None => None
    end
  end.

Definition popRep2 (xs : list SymTok) : option (N * list SymTok) :=
  match xs with STRep2 p :: rest => Some (p, rest) | _ => None end.

Definition popRep12 (xs : list SymTok) : option (N * list SymTok) :=
  match xs with STRep12 m :: rest => Some (m, rest) | _ => None end.

Definition popRepB1 (xs : list SymTok) : option (N * list SymTok) :=
  match xs with STRepB1 k :: rest => Some (k, rest) | _ => None end.

Definition matchEndB1 (xs : list SymTok) : option N :=
  match popRepB1 xs with
  | Some (k, rest) =>
    match stripPrefixSym [STItem (MRun 0)] rest with
    | Some [] => Some k
    | _ => None
    end
  | None => None
  end.

Lemma popRepB1_some (xs : list SymTok) (k : N) (rest : list SymTok) :
  popRepB1 xs = Some (k, rest) -> xs = STRepB1 k :: rest.
Proof.
  destruct xs as [| [| | | ] tl]; intro h; try discriminate.
  injection h as <- <-; reflexivity.
Qed.

Lemma matchEndB1_some (xs : list SymTok) (k : N) :
  matchEndB1 xs = Some k -> xs = [STRepB1 k; STItem (MRun 0)].
Proof.
  unfold matchEndB1.
  destruct (popRepB1 xs) as [[k' rest] |] eqn:hp; [| discriminate].
  destruct (stripPrefixSym [STItem (MRun 0)] rest) as [[| t rest2] |] eqn:hs; try discriminate.
  intro h; injection h as <-.
  pose proof (popRepB1_some xs k' rest hp) as ->.
  pose proof (stripPrefixSym_some _ rest [] hs) as ->.
  reflexivity.
Qed.

Lemma popRep2_some (xs : list SymTok) (p : N) (rest : list SymTok) :
  popRep2 xs = Some (p, rest) -> xs = STRep2 p :: rest.
Proof.
  destruct xs as [| [| | | ] tl]; intro h; try discriminate.
  injection h as <- <-; reflexivity.
Qed.

Lemma popRep12_some (xs : list SymTok) (m : N) (rest : list SymTok) :
  popRep12 xs = Some (m, rest) -> xs = STRep12 m :: rest.
Proof.
  destruct xs as [| [| | | ] tl]; intro h; try discriminate.
  injection h as <- <-; reflexivity.
Qed.

Lemma popSep3_some (xs sep rest : list SymTok) :
  popSep3 xs = Some (sep, rest) -> xs = sep ++ rest /\ (sep = sep3A \/ sep = sep3B).
Proof.
  unfold popSep3.
  destruct (stripPrefixSym sep3A xs) as [rA |] eqn:hsA.
  - intro h; injection h as <- <-.
    split; [exact (stripPrefixSym_some _ xs rA hsA) | left; reflexivity].
  - destruct (stripPrefixSym sep3B xs) as [rB |] eqn:hsB; [| discriminate].
    intro h; injection h as <- <-.
    split; [exact (stripPrefixSym_some _ xs rB hsB) | right; reflexivity].
Qed.

Definition tryRuleA (L : list SymTok) (d : N) (R_tail : list SymTok) :
    SymMode * list SymTok * list SymTok :=
  match stripPrefixSym [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0);
     STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem MZero; STItem (MRun 1)] L with
  | Some rest =>
    match matchEndB1 rest with
    | Some k =>
      let n1 := d / 6 in
      if (2 <=? n1) && (n1 <=? k) then
        let m_new := n1 - 1 in
        let k_new := k - n1 in
        let d_new := d - 6 * n1 in
        (CB,
         [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0);
          STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1);
          STRep12 m_new; STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0);
          STItem MZero; STItem (MRun 1); STRepB1 k_new; STItem (MRun 0)],
         STItem (MRun d_new) :: R_tail)
      else stepElemThenBB CB L (STItem (MRun d) :: R_tail)
    | None => stepElemThenBB CB L (STItem (MRun d) :: R_tail)
    end
  | None => stepElemThenBB CB L (STItem (MRun d) :: R_tail)
  end.

Lemma tryRuleA_sound (L : list SymTok) (d : N) (R_tail : list SymTok) :
  evalSym (CB, L, STItem (MRun d) :: R_tail) -->* evalSym (tryRuleA L d R_tail).
Proof.
  unfold tryRuleA.
  destruct (stripPrefixSym _ L) as [rest |] eqn:hs; [| apply stepElemThenBB_sound].
  destruct (matchEndB1 rest) as [k |] eqn:hm; [| apply stepElemThenBB_sound].
  destruct ((2 <=? d / 6) && (d / 6 <=? k)) eqn:hcond; [| apply stepElemThenBB_sound].
  apply andb_prop in hcond; destruct hcond as [hc1 hc2].
  apply N.leb_le in hc1; apply N.leb_le in hc2.
  pose proof (matchEndB1_some rest k hm) as hrest.
  pose proof (stripPrefixSym_some _ L rest hs) as hL.
  rewrite hrest in hL.
  pose proof (N.div_mod d 6 ltac:(lia)) as hdiv.
  set (n1 := d / 6) in *.
  set (m_new := n1 - 1).
  set (k_new := k - n1).
  set (d_new := d - 6 * n1).
  assert (hk_eq : k = (k_new + m_new) + 1) by lia.
  assert (hd_eq : d = (d_new + 6 * m_new) + 6) by lia.
  assert (hlhs : (CB, L, STItem (MRun d) :: R_tail) =
    stateA0 ((k_new + m_new) + 1) ((d_new + 6 * m_new) + 6) R_tail).
  { rewrite hL, hk_eq, hd_eq; reflexivity. }
  rewrite hlhs.
  eapply etrans; [exact (ruleA0_sound (k_new + m_new) (d_new + 6 * m_new) R_tail) |].
  pose proof (ruleA_iter m_new 0 k_new d_new R_tail) as hiter.
  replace (0 + m_new) with m_new in hiter by lia.
  exact hiter.
Qed.

Definition afterSplitB2 (L : list SymTok) (d2 : N) (R_tail : list SymTok)
  (res : N * list SymTok) : SymMode * list SymTok * list SymTok :=
  match popSep3 (snd res) with
  | Some (s_sep, rest0) =>
    match popRep12 rest0 with
    | Some (m12, rest1) =>
      match stripPrefixSym [STItem (MRun 1); STItem (MRun 0); STItem (MRun 1)] rest1 with
      | Some rest2 =>
        match popSep3 rest2 with
        | Some (m_sep, rest3) =>
          match matchEndB1 rest3 with
          | Some k1 =>
            let p := fst res in
            if (2 <=? p) && (2 <=? m12) && (m12 <=? k1) then
              let n3 := m12 - 1 in
              let p_new := p + 2 * n3 - 1 in
              let k_new := k1 - n3 in
              let d_new := d2 + 4 * n3 in
              (CB,
               [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STRep2 p_new; STItem (MRun 1)] ++
                 s_sep ++ [STRep12 1; STItem (MRun 1); STItem (MRun 0); STItem (MRun 1)] ++
                 m_sep ++ [STRepB1 k_new; STItem (MRun 0)],
               STItem MZero :: STItem (MRun d_new) :: R_tail)
            else stepElemThenBB CB L (STItem MZero :: STItem (MRun d2) :: R_tail)
          | None => stepElemThenBB CB L (STItem MZero :: STItem (MRun d2) :: R_tail)
          end
        | None => stepElemThenBB CB L (STItem MZero :: STItem (MRun d2) :: R_tail)
        end
      | None => stepElemThenBB CB L (STItem MZero :: STItem (MRun d2) :: R_tail)
      end
    | None => stepElemThenBB CB L (STItem MZero :: STItem (MRun d2) :: R_tail)
    end
  | None => stepElemThenBB CB L (STItem MZero :: STItem (MRun d2) :: R_tail)
  end.

Definition tryRuleB (L : list SymTok) (d2 : N) (R_tail : list SymTok) :
    SymMode * list SymTok * list SymTok :=
  match stripPrefixSym [STItem (MRun 0)] L with
  | Some restL => afterSplitB2 L d2 R_tail (splitB2 0 restL)
  | None => stepElemThenBB CB L (STItem MZero :: STItem (MRun d2) :: R_tail)
  end.

Lemma encSymL_app (xs ys : list SymTok) :
  encSymL (xs ++ ys) = encSymL xs ++ encSymL ys.
Proof.
  induction xs as [| [x | k | p | m] xs ih]; simpl; [reflexivity | | | |];
    rewrite ih; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma tryRuleB_sound (L : list SymTok) (d2 : N) (R_tail : list SymTok) :
  evalSym (CB, L, STItem MZero :: STItem (MRun d2) :: R_tail) -->*
  evalSym (tryRuleB L d2 R_tail).
Proof.
  unfold tryRuleB.
  destruct (stripPrefixSym [STItem (MRun 0)] L) as [restL |] eqn:hsL;
    [| apply stepElemThenBB_sound].
  unfold afterSplitB2.
  destruct (popSep3 (snd (splitB2 0 restL))) as [[s_sep rest0] |] eqn:hsep1;
    [| apply stepElemThenBB_sound].
  destruct (popRep12 rest0) as [[m12 rest1] |] eqn:h12;
    [| apply stepElemThenBB_sound].
  destruct (stripPrefixSym [STItem (MRun 1); STItem (MRun 0); STItem (MRun 1)] rest1) as [rest2 |] eqn:hs1;
    [| apply stepElemThenBB_sound].
  destruct (popSep3 rest2) as [[m_sep rest3] |] eqn:hsep2;
    [| apply stepElemThenBB_sound].
  destruct (matchEndB1 rest3) as [k1 |] eqn:hend;
    [| apply stepElemThenBB_sound].
  destruct ((2 <=? fst (splitB2 0 restL)) && (2 <=? m12) && (m12 <=? k1)) eqn:hcond;
    [| apply stepElemThenBB_sound].
  apply andb_prop in hcond; destruct hcond as [hcond12 hc3].
  apply andb_prop in hcond12; destruct hcond12 as [hc1 hc2].
  apply N.leb_le in hc1; apply N.leb_le in hc2; apply N.leb_le in hc3.
  pose proof (stripPrefixSym_some _ L restL hsL) as hL.
  pose proof (splitB2Aux_spec 16%nat 0 restL) as hspec.
  rewrite repBlock_0 in hspec; cbn [app] in hspec.
  change (splitB2Aux 16%nat 0 restL) with (splitB2 0 restL) in hspec.
  destruct (popSep3_some _ s_sep rest0 hsep1) as [h_s hs_or].
  pose proof (popRep12_some rest0 m12 rest1 h12) as h_m12.
  pose proof (stripPrefixSym_some _ rest1 rest2 hs1) as h_r1.
  destruct (popSep3_some _ m_sep rest3 hsep2) as [h_m hm_or].
  pose proof (matchEndB1_some rest3 k1 hend) as h_k1.
  set (p := fst (splitB2 0 restL)) in *.
  set (n3 := m12 - 1).
  set (p0 := p - 2).
  set (k_new := k1 - n3).
  assert (hp_eq : p = (p0 + 1) + 1) by lia.
  assert (hm_eq : m12 = 0 + n3 + 1) by lia.
  assert (hk_eq : k1 = k_new + n3) by lia.
  assert (hp_new : p + 2 * n3 - 1 = p0 + 1 + 2 * n3) by lia.
  assert (hlhs : evalSym (CB, L, STItem MZero :: STItem (MRun d2) :: R_tail) =
    evalSym (stateB s_sep m_sep (p0 + 1) (0 + n3 + 1) (k_new + n3) d2 R_tail)).
  { unfold evalSym, stateB.
    rewrite hL; cbn [encSymL app].
    rewrite hspec, h_s, h_m12, h_r1, h_m, h_k1, hp_eq, hm_eq, hk_eq.
    rewrite (repBlock_B2_shift (p0 + 1)).
    repeat rewrite encSymL_app || cbn [encSymL app].
    reflexivity. }
  rewrite hlhs, hp_new.
  exact (ruleB_iter s_sep m_sep hs_or hm_or n3 p0 0 k_new d2 R_tail).
Qed.

Definition tryRuleBC (L : list SymTok) (d2 : N) (R_tail : list SymTok) :
    SymMode * list SymTok * list SymTok :=
  match stripPrefixSym [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1)] L with
  | Some rest1 =>
    match popRep2 rest1 with
    | Some (p, restC) =>
      match stripPrefixSym [STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1)] restC with
      | Some rest2 =>
        match matchEndB1 rest2 with
        | Some k1 =>
          if (3 <=? p) && (1 <=? k1) then
            let n4 := p - 2 in
            let k_new := k1 + 2 * n4 in
            let d_new := d2 + 2 * n4 in
            (CB,
             [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STRep2 2;
              STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1);
              STRepB1 k_new; STItem (MRun 0)],
             STItem MZero :: STItem (MRun d_new) :: R_tail)
          else tryRuleB L d2 R_tail
        | None => tryRuleB L d2 R_tail
        end
      | None => tryRuleB L d2 R_tail
      end
    | None => tryRuleB L d2 R_tail
    end
  | None => tryRuleB L d2 R_tail
  end.

Lemma tryRuleBC_sound (L : list SymTok) (d2 : N) (R_tail : list SymTok) :
  evalSym (CB, L, STItem MZero :: STItem (MRun d2) :: R_tail) -->*
  evalSym (tryRuleBC L d2 R_tail).
Proof.
  unfold tryRuleBC.
  destruct (stripPrefixSym [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1)] L) as [rest1 |] eqn:hs1;
    [| apply tryRuleB_sound].
  destruct (popRep2 rest1) as [[p restC] |] eqn:hp2;
    [| apply tryRuleB_sound].
  destruct (stripPrefixSym [STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1)] restC) as [rest2 |] eqn:hs2;
    [| apply tryRuleB_sound].
  destruct (matchEndB1 rest2) as [k1 |] eqn:hend;
    [| apply tryRuleB_sound].
  destruct ((3 <=? p) && (1 <=? k1)) eqn:hcond;
    [| apply tryRuleB_sound].
  apply andb_prop in hcond; destruct hcond as [hp hk1].
  apply N.leb_le in hp; apply N.leb_le in hk1.
  pose proof (stripPrefixSym_some _ L rest1 hs1) as hL1.
  pose proof (popRep2_some rest1 p restC hp2) as hL2.
  pose proof (stripPrefixSym_some _ restC rest2 hs2) as hL3.
  pose proof (matchEndB1_some rest2 k1 hend) as hL4.
  set (n4 := p - 2).
  assert (hp_eq : p = 0 + n4 + 2) by lia.
  assert (hlhs : (CB, L, STItem MZero :: STItem (MRun d2) :: R_tail) =
    stateC (0 + n4 + 2) k1 d2 R_tail).
  { rewrite hL1, hL2, hL3, hL4, hp_eq; reflexivity. }
  rewrite hlhs.
  exact (ruleC_iter n4 0 k1 d2 R_tail hk1).
Qed.

Definition afterSweepCB (p : list SymTok * list SymTok) : SymMode * list SymTok * list SymTok :=
  let '(ls, rs) := p in
  match rs with
  | STItem MZero :: STItem (MRun d2) :: R_tail => tryRuleBC ls d2 R_tail
  | STItem (MRun d) :: R_tail =>
    if 12 <=? d then tryRuleA ls d R_tail
    else stepElemThenBB CB ls rs
  | _ => stepElemThenBB CB ls rs
  end.

Lemma afterSweepCB_sound (p : list SymTok * list SymTok) :
  evalSym (CB, fst p, snd p) -->* evalSym (afterSweepCB p).
Proof.
  destruct p as [L R]; cbn [fst snd afterSweepCB].
  destruct R as [| t1 R1]; [apply stepElemThenBB_sound |].
  destruct t1 as [[| d] | k | p | m]; try apply stepElemThenBB_sound.
  - destruct R1 as [| t2 R_tail]; [apply stepElemThenBB_sound |].
    destruct t2 as [[| d2] | k2 | p2 | m2]; try apply stepElemThenBB_sound.
    apply tryRuleBC_sound.
  - destruct (12 <=? d); [apply tryRuleA_sound | apply stepElemThenBB_sound].
Qed.

Definition stepSym (s : SymMode * list SymTok * list SymTok) : SymMode * list SymTok * list SymTok :=
  let '(m, ls, rs) := s in
  match m with
  | BB => sweepBB ls rs
  | DL => stepElemThenBB DL (peelL ls) rs
  | HALT => (HALT, ls, rs)
  | CB => afterSweepCB (sweepCB ls rs)
  end.

Lemma stepSym_sound (s : SymMode * list SymTok * list SymTok) :
  evalSym s -->* evalSym (stepSym s).
Proof.
  destruct s as [[m L] R]; destruct m; cbn [stepSym].
  - exact (sweepBB_sound L R).
  - assert (heq : evalSym (DL, L, R) = evalSym (DL, peelL L, R)).
    { unfold evalSym; rewrite encSymL_peelL; reflexivity. }
    rewrite heq; exact (stepElemThenBB_sound DL (peelL L) R).
  - exact (etrans (sweepCB_sound L R) (afterSweepCB_sound (sweepCB L R))).
  - apply evstep_refl.
Qed.

Definition stepSym16 := iter stepSym 16%nat.
Definition stepSym256 := iter stepSym16 16%nat.
Definition stepSym4096 := iter stepSym256 16%nat.

Lemma stepSym16_sound (s : SymMode * list SymTok * list SymTok) :
  evalSym s -->* evalSym (stepSym16 s).
Proof. exact (iter_sound stepSym evalSym stepSym_sound 16%nat s). Qed.

Lemma stepSym256_sound (s : SymMode * list SymTok * list SymTok) :
  evalSym s -->* evalSym (stepSym256 s).
Proof. exact (iter_sound stepSym16 evalSym stepSym16_sound 16%nat s). Qed.

Lemma stepSym4096_sound (s : SymMode * list SymTok * list SymTok) :
  evalSym s -->* evalSym (stepSym4096 s).
Proof. exact (iter_sound stepSym256 evalSym stepSym256_sound 16%nat s). Qed.

(* ========================================================================== *)
(* Section 6: Checkpointed Trajectory & Halting Theorem                       *)
(* ========================================================================== *)

Definition initSymCyc3 : SymMode * list SymTok * list SymTok :=
  (CB,
   [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0);
    STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem MZero;
    STItem (MRun 1); STRepB1 46; STItem (MRun 0)],
   [STItem (MRun 79); STItem (MRun 0); STItem (MRun 1); STItem MZero;
    STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1)]).

Definition symChk4096 : SymMode * list SymTok * list SymTok :=
  (CB, [STItem (MRun 1); STRepB1 349285; STItem (MRun 0)], [STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STRep12 69932; STItem (MRun 0); STItem (MRun 2); STItem (MRun 3); STItem (MRun 5); STItem (MRun 1); STItem (MRun 5); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1)]).

Definition symChk8192 : SymMode * list SymTok * list SymTok :=
  (CB, [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STRep2 2; STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STRepB1 1762386413; STItem (MRun 0)], [STItem MZero; STItem (MRun 1762387139); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 2); STItem (MRun 3); STItem (MRun 0); STItem (MRun 1); STItem MZero; STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1)]).

Definition symChk12288 : SymMode * list SymTok * list SymTok :=
  (CB, [STItem (MRun 1); STRep12 925198033012; STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem MZero; STItem (MRun 1); STRepB1 4625990163979; STItem (MRun 0)], [STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 2); STItem (MRun 0); STItem (MRun 1); STItem (MRun 2); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem MZero; STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 2); STItem (MRun 3); STItem (MRun 1); STItem (MRun 1)]).

Definition symChk16384 : SymMode * list SymTok * list SymTok :=
  (DL, [STRepB1 14570999059234231; STItem (MRun 0)], [STItem (MRun 0); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STRep12 2914199811847131; STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem MZero; STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 2); STItem (MRun 3); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem MZero; STItem (MRun 5)]).

Definition symChk20480 : SymMode * list SymTok * list SymTok :=
  (DL, [STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem MZero; STItem MZero; STItem MZero; STItem MZero; STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 2); STRep12 12238908486313258620; STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem MZero; STItem (MRun 1); STRepB1 61194542431566291295; STItem (MRun 0)], [STItem (MRun 0); STItem (MRun 4); STItem (MRun 1); STItem MZero; STItem (MRun 1); STItem (MRun 1); STItem (MRun 1); STItem (MRun 1)]).

Definition symChk21383 : SymMode * list SymTok * list SymTok :=
  (HALT, [STItem MZero; STItem MZero; STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem MZero; STItem MZero; STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 2); STRep12 68766212839422643803; STItem (MRun 2); STRepB1 343831064197113217107; STItem (MRun 0)], [STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem MZero; STItem (MRun 3); STItem (MRun 1); STItem (MRun 1)]).

Lemma test_elem_rfl :
  runElemFast (BB, [MRun 0], []) =
  (fst (fst initSymCyc3), encSymL (snd (fst initSymCyc3)), encSymR (snd initSymCyc3)).
Proof. vm_compute. reflexivity. Qed.

Lemma sym_chk1 : stepSym4096 initSymCyc3 = symChk4096.
Proof. vm_compute. reflexivity. Qed.

Lemma sym_chk2 : stepSym4096 symChk4096 = symChk8192.
Proof. vm_compute. reflexivity. Qed.

Lemma sym_chk3 : stepSym4096 symChk8192 = symChk12288.
Proof. vm_compute. reflexivity. Qed.

Lemma sym_chk4 : stepSym4096 symChk12288 = symChk16384.
Proof. vm_compute. reflexivity. Qed.

Lemma sym_chk5 : stepSym4096 symChk16384 = symChk20480.
Proof. vm_compute. reflexivity. Qed.

Lemma sym_chk6 :
  iter stepSym 7%nat (iter stepSym16 8%nat (iter stepSym256 3%nat symChk20480)) = symChk21383.
Proof. vm_compute. reflexivity. Qed.

Strategy 1000 [initSymCyc3 symChk4096 symChk8192 symChk12288 symChk16384 symChk20480 symChk21383
  runElemFast stepSym4096 stepSym256 stepSym16 stepSym].

Lemma halts_evstep {c c' : Q * tape} : halts tm c' -> c -->* c' -> halts tm c.
Proof.
  intros Hh Hev. apply with_counter in Hev. destruct Hev as [n Hms].
  eapply halts_multistep; eauto.
Qed.

Lemma halt : halts tm c0.
Proof.
  assert (h0 : c0 -->* evalM (BB, [MRun 0], [])).
  { exact (pev init_to_BB). }
  assert (h1 : evalM (BB, [MRun 0], []) -->* evalSym initSymCyc3).
  { pose proof (runElemFast_sound (BB, [MRun 0], [])) as h.
    rewrite test_elem_rfl in h.
    exact h. }
  assert (hc1 : evalSym initSymCyc3 -->* evalSym symChk4096).
  { rewrite <- sym_chk1. exact (stepSym4096_sound initSymCyc3). }
  assert (hc2 : evalSym symChk4096 -->* evalSym symChk8192).
  { rewrite <- sym_chk2. exact (stepSym4096_sound symChk4096). }
  assert (hc3 : evalSym symChk8192 -->* evalSym symChk12288).
  { rewrite <- sym_chk3. exact (stepSym4096_sound symChk8192). }
  assert (hc4 : evalSym symChk12288 -->* evalSym symChk16384).
  { rewrite <- sym_chk4. exact (stepSym4096_sound symChk12288). }
  assert (hc5 : evalSym symChk16384 -->* evalSym symChk20480).
  { rewrite <- sym_chk5. exact (stepSym4096_sound symChk16384). }
  assert (hc6 : evalSym symChk20480 -->* evalSym symChk21383).
  { rewrite <- sym_chk6.
    eapply etrans; [exact (iter_sound stepSym256 evalSym stepSym256_sound 3%nat symChk20480) |].
    eapply etrans; [exact (iter_sound stepSym16 evalSym stepSym16_sound 8%nat _) |].
    exact (iter_sound stepSym evalSym stepSym_sound 7%nat _). }
  assert (h_to_halt : c0 -->* evalSym symChk21383).
  { exact (etrans h0 (etrans h1 (etrans hc1 (etrans hc2 (etrans hc3 (etrans hc4 (etrans hc5 hc6))))))). }
  pose proof (step_DL_zero_halt
    (encSymL [STItem MZero; STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 0); STItem MZero; STItem MZero; STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 2); STRep12 68766212839422643803; STItem (MRun 2); STRepB1 343831064197113217107; STItem (MRun 0)])
    (encSymR [STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem (MRun 1); STItem (MRun 0); STItem (MRun 1); STItem MZero; STItem (MRun 3); STItem (MRun 1); STItem (MRun 1)])) as h_final.
  eapply halts_evstep; [| exact h_to_halt].
  unfold symChk21383, evalSym, evalM; cbn [encSymL encSymR].
  eapply halts_evstep; [| exact (pev h_final)].
  apply halted_halts; reflexivity.
Qed.
