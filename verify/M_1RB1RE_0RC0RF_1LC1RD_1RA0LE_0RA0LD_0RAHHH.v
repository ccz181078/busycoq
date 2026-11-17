(* 1RB1RE_0RC0RF_1LC1RD_1RA0LE_0RA0LD_0RA--- halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import String Bool Lists.List PeanoNat NArith PArith ZArith ZifyNat ZifyN Lia.
Import ListNotations.
Set Default Goal Selector "!".

Definition tm : TM := TM_from_str "1RB1RE_0RC0RF_1LC1RD_1RA0LE_0RA0LD_0RA---".

Module Internal.

Local Close Scope sym_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(* ========================================================================= *)
(* Section 1: Concrete Macro System                                          *)
(* ========================================================================= *)

Inductive SegMode : Type :=
  | mAR | mAR0 | mAR00 | mCL | mDL | mEL | mDR | mER.

Fixpoint lWord_aux (d : nat) (b : bool) : list Sym :=
  match d with
  | 0 => if b then [S1; S0; S0] else [S1; S0]
  | S d' => S1 :: lWord_aux d' b
  end.

Definition lWord (p : nat * bool) : list Sym := lWord_aux (fst p) (snd p).

Fixpoint lTail_aux (d : nat) (b : bool) : list Sym :=
  match d with
  | 0 => if b then [S0; S0] else [S0]
  | S d' => S1 :: lTail_aux d' b
  end.

Definition lTail (p : nat * bool) : list Sym := lTail_aux (fst p) (snd p).

Lemma lWord_eq_cons (p : nat * bool) : lWord p = S1 :: lTail p.
Proof.
  destruct p as [d b]. unfold lWord, lTail, fst, snd.
  induction d as [|d IH]; simpl.
  - destruct b; reflexivity.
  - rewrite IH; reflexivity.
Qed.

Fixpoint oWord (o : nat) : list Sym :=
  match o with
  | 0 => [S1; S0]
  | S o' => S1 :: oWord o'
  end.

Fixpoint rWord_aux (z o : nat) : list Sym :=
  match z with
  | 0 => oWord o
  | S z' => S0 :: rWord_aux z' o
  end.

Definition rWord (p : nat * nat) : list Sym := rWord_aux (fst p) (snd p).

Fixpoint encLeft (ls : list (nat * bool)) : side :=
  match ls with
  | [] => const S0
  | p :: rest => lWord p *> encLeft rest
  end.

Fixpoint encRight (rs : list (nat * nat)) : side :=
  match rs with
  | [] => const S0
  | p :: rest => rWord p *> encRight rest
  end.

Definition bumpL (ls : list (nat * bool)) : list (nat * bool) :=
  match ls with
  | [] => [(0, false)]
  | (d, b) :: rest => (S d, b) :: rest
  end.

Definition push100L (ls : list (nat * bool)) : list (nat * bool) :=
  match ls with
  | [] => [(0, false)]
  | p :: rest => (0, true) :: p :: rest
  end.

Definition push0R (rs : list (nat * nat)) : list (nat * nat) :=
  match rs with
  | [] => []
  | (z, o) :: rest => (S z, o) :: rest
  end.

Fixpoint push0R_iter (k : nat) (rs : list (nat * nat)) : list (nat * nat) :=
  match k with
  | 0 => rs
  | S k' => push0R_iter k' (push0R rs)
  end.

Lemma push0R_iter_nil (k : nat) : push0R_iter k [] = [].
Proof.
  induction k as [|k IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma push0R_iter_cons (k z o : nat) (rs : list (nat * nat)) :
  push0R_iter k ((z, o) :: rs) = (z + k, o) :: rs.
Proof.
  revert z. induction k as [|k IH]; intros z; simpl.
  - f_equal; f_equal; lia.
  - rewrite IH. f_equal; f_equal; lia.
Qed.

Definition push1R (rs : list (nat * nat)) : list (nat * nat) :=
  match rs with
  | [] => [(0, 0)]
  | (0, o) :: rest => (0, S o) :: rest
  | (S z, o) :: rest => (0, 0) :: (z, o) :: rest
  end.

Definition evalSegCfg (m : SegMode) (ls : list (nat * bool)) (rs : list (nat * nat)) : Q * tape :=
  match m with
  | mAR => encLeft ls {{A}}> encRight rs
  | mAR0 => (S0 >> encLeft ls) {{A}}> encRight rs
  | mAR00 => (S0 >> S0 >> encLeft ls) {{A}}> encRight rs
  | mCL => encLeft ls <{{C}} encRight rs
  | mDL => encLeft ls <{{D}} encRight rs
  | mEL => encLeft ls <{{E}} encRight rs
  | mDR => encLeft ls {{D}}> encRight rs
  | mER => encLeft ls {{E}}> encRight rs
  end.

Definition evalA (ls : list (nat * bool)) (rs : list (nat * nat)) : Q * tape :=
  match ls with
  | [] => (const S0) {{A}}> encRight rs
  | p :: rest => (lTail p *> encLeft rest) {{A}}> encRight rs
  end.

Lemma evalA_zero_false (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalA ((0, false) :: ls) rs = evalSegCfg mAR0 ls rs.
Proof. reflexivity. Qed.

Lemma evalA_zero_true (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalA ((0, true) :: ls) rs = evalSegCfg mAR00 ls rs.
Proof. reflexivity. Qed.

Lemma evalA_succ (d : nat) (b : bool) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalA ((d + 1, b) :: ls) rs = evalSegCfg mAR ((d, b) :: ls) rs.
Proof.
  replace (d + 1) with (S d) by lia.
  unfold evalA, evalSegCfg, encLeft; fold encLeft.
  rewrite lWord_eq_cons. reflexivity.
Qed.

Lemma cons_one_encLeft (ls : list (nat * bool)) :
  (S1 >> encLeft ls) = encLeft (bumpL ls).
Proof.
  destruct ls as [|[d b] rest]; simpl; [rewrite <- const_unfold |]; reflexivity.
Qed.

Lemma cons_100_encLeft (ls : list (nat * bool)) :
  (S1 >> S0 >> S0 >> encLeft ls) = encLeft (push100L ls).
Proof.
  destruct ls as [|p rest]; simpl; [rewrite <- const_unfold |]; reflexivity.
Qed.

Lemma cons_zero_encRight (rs : list (nat * nat)) :
  (S0 >> encRight rs) = encRight (push0R rs).
Proof.
  destruct rs as [|[z o] rest]; simpl; [rewrite <- const_unfold |]; reflexivity.
Qed.

Lemma cons_one_encRight (rs : list (nat * nat)) :
  (S1 >> encRight rs) = encRight (push1R rs).
Proof.
  destruct rs as [|[[|z] o] rest]; simpl; [rewrite <- const_unfold | |]; reflexivity.
Qed.

Definition SegState : Type := SegMode * list (nat * bool) * list (nat * nat).

Definition stepA (ls' : list (nat * bool)) (rs : list (nat * nat)) : option SegState :=
  match rs with
  | [] => Some (mCL, ls', [(0, 1)])
  | (0, 0) :: rest => Some (mER, ls', push0R rest)
  | (0, S o) :: rest => Some (mER, ls', (0, o) :: rest)
  | (1, 0) :: rest => Some (mAR00, ls', rest)
  | (1, S _) :: _ => None
  | (2, 0) :: rest => Some (mDR, (0, false) :: ls', push0R rest)
  | (2, S o) :: rest => Some (mDR, (0, false) :: ls', (0, o) :: rest)
  | (S (S (S z)), o) :: rest => Some (mCL, ls', push1R (push1R ((z, o) :: rest)))
  end.

Definition sweepMode (isE : bool) : SegMode :=
  if isE then mEL else mDL.

Fixpoint sweepDLEL (isE : bool) (d : nat) (b : bool)
    (ls : list (nat * bool)) (rs : list (nat * nat)) : SegState :=
  match d with
  | 0 =>
    match isE, b with
    | false, false => (mAR0, ls, push0R rs)
    | false, true => (mAR00, ls, push0R rs)
    | true, false => (mAR, bumpL ls, push0R rs)
    | true, true => (mAR, (0, false) :: ls, push0R rs)
    end
  | S d' => sweepDLEL (negb isE) d' b ls (push0R rs)
  end.

Lemma sweepDLEL_closed (d : nat) (isE b : bool)
    (ls : list (nat * bool)) (rs : list (nat * nat)) :
  sweepDLEL isE d b ls rs =
    let r1 := push0R_iter (d + 1) rs in
    let finE := if Nat.eqb (d mod 2) 0 then isE else negb isE in
    if finE then
      (mAR, if b then (0, false) :: ls else bumpL ls, r1)
    else
      (if b then mAR00 else mAR0, ls, r1).
Proof.
  revert isE rs.
  induction d as [|d IH]; intros isE rs.
  - replace (0 + 1) with 1 by lia.
    replace (0 mod 2) with 0 by reflexivity.
    destruct isE, b; reflexivity.
  - simpl sweepDLEL. rewrite IH.
    replace (S d + 1) with (S (d + 1)) by lia.
    simpl push0R_iter.
    assert (Hmod : Nat.eqb (S d mod 2) 0 = negb (Nat.eqb (d mod 2) 0)).
    { assert (H1 : d mod 2 = 0 \/ d mod 2 = 1) by lia.
      assert (H2 : S d mod 2 = 1 - d mod 2) by lia.
      destruct H1 as [H1 | H1]; rewrite H2, H1; reflexivity. }
    rewrite Hmod.
    destruct (Nat.eqb (d mod 2) 0), isE, b; reflexivity.
Qed.

Definition stepMacro (m : SegMode) (ls : list (nat * bool)) (rs : list (nat * nat)) : option SegState :=
  match m with
  | mAR => stepA (bumpL ls) rs
  | mAR0 => stepA ((0, false) :: ls) rs
  | mAR00 => stepA (push100L ls) rs
  | mCL =>
    match ls with
    | [] => Some (mCL, [], push1R rs)
    | p :: rest => Some (mDR, p :: rest, rs)
    end
  | mDL =>
    match ls with
    | [] => Some (mAR, [(0, false)], rs)
    | (d, b) :: rest => Some (sweepDLEL false d b rest rs)
    end
  | mEL =>
    match ls with
    | [] => Some (mAR0, [], rs)
    | (d, b) :: rest => Some (sweepDLEL true d b rest rs)
    end
  | mDR =>
    match rs with
    | [] => Some (mAR, bumpL ls, [])
    | (0, 0) :: rest => Some (mEL, ls, push0R (push0R rest))
    | (0, S o) :: rest => Some (mEL, ls, (1, o) :: rest)
    | (S z, o) :: rest => Some (mAR, bumpL ls, (z, o) :: rest)
    end
  | mER =>
    match rs with
    | [] => Some (mAR0, ls, [])
    | (0, 0) :: rest => Some (mDL, ls, push0R (push0R rest))
    | (0, S o) :: rest => Some (mDL, ls, (1, o) :: rest)
    | (S z, o) :: rest => Some (mAR0, ls, (z, o) :: rest)
    end
  end.

Lemma init_reaches_segmented_system :
  c0 -[ tm ]->+ evalSegCfg mCL [(0, false)] [(0, 1)].
Proof.
  unfold c0, tape0, evalSegCfg, encLeft, encRight, lWord, rWord, lWord_aux, rWord_aux, oWord, fst, snd.
  simpl Str_app.
  start_progress.
Qed.

Lemma step_A_common (l : side) (ls' : list (nat * bool)) (hl : (S1 >> l) = encLeft ls')
    (rs : list (nat * nat)) (m' : SegMode) (ls'' : list (nat * bool)) (rs' : list (nat * nat))
    (h : stepA ls' rs = Some (m', ls'', rs')) :
  (l {{A}}> encRight rs) -[ tm ]->+ evalSegCfg m' ls'' rs'.
Proof.
  destruct rs as [|[[|[|[|z]]] o] rest].
  - unfold stepA in h; inversion h; subst.
    unfold evalSegCfg; rewrite <- hl.
    simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app.
    start_progress.
  - destruct o as [|o]; unfold stepA in h; inversion h; subst.
    + unfold evalSegCfg; rewrite <- hl, <- cons_zero_encRight.
      simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app.
      start_progress.
    + unfold evalSegCfg; rewrite <- hl.
      simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app.
      start_progress.
  - destruct o as [|o]; unfold stepA in h; [inversion h; subst | discriminate].
    unfold evalSegCfg; rewrite <- hl.
    simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app.
    start_progress.
  - destruct o as [|o]; unfold stepA in h; inversion h; subst.
    + unfold evalSegCfg; simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app.
      rewrite <- cons_zero_encRight, <- hl.
      simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app.
      start_progress.
    + unfold evalSegCfg; simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app.
      rewrite <- hl.
      simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app.
      start_progress.
  - assert (m' = mCL /\ ls'' = ls' /\ rs' = push1R (push1R ((z, o) :: rest))) as [-> [-> ->]]
      by (unfold stepA in h; inversion h; repeat split).
    unfold evalSegCfg.
    rewrite <- cons_one_encRight, <- cons_one_encRight, <- hl.
    simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app.
    start_progress.
Qed.

Lemma step_evalA (p : nat * bool) (ls : list (nat * bool)) (rs : list (nat * nat))
    (m' : SegMode) (ls'' : list (nat * bool)) (rs' : list (nat * nat))
    (h : stepA (p :: ls) rs = Some (m', ls'', rs')) :
  evalA (p :: ls) rs -[ tm ]->+ evalSegCfg m' ls'' rs'.
Proof.
  unfold evalA.
  apply (step_A_common (lTail p *> encLeft ls) (p :: ls)).
  - unfold encLeft; fold encLeft. rewrite lWord_eq_cons. reflexivity.
  - exact h.
Qed.

Lemma step_A_halts (l : side) (o : nat) (rs : list (nat * nat)) :
  halts tm (l {{A}}> encRight ((1, S o) :: rs)).
Proof.
  destruct o as [|o].
  - eapply halts_evstep with (c' := (S0 >> S1 >> l) {{F}}> (S1 >> S0 >> encRight rs)).
    + apply halted_halts. reflexivity.
    + unfold encRight; fold encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app.
      execute.
  - eapply halts_evstep with (c' := (S0 >> S1 >> l) {{F}}> (S1 >> (oWord o *> encRight rs))).
    + apply halted_halts. reflexivity.
    + unfold encRight; fold encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app.
      execute.
Qed.

Lemma step_DL_0_false (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mDL ((0, false) :: ls) rs -[ tm ]->+ evalSegCfg mAR0 ls (push0R rs).
Proof.
  unfold evalSegCfg; rewrite <- cons_zero_encRight.
  simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app.
  start_progress.
Qed.

Lemma step_DL_0_true (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mDL ((0, true) :: ls) rs -[ tm ]->+ evalSegCfg mAR00 ls (push0R rs).
Proof.
  unfold evalSegCfg; rewrite <- cons_zero_encRight.
  simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app.
  start_progress.
Qed.

Lemma step_DL_succ (d : nat) (b : bool) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mDL ((S d, b) :: ls) rs -[ tm ]->+ evalSegCfg mEL ((d, b) :: ls) (push0R rs).
Proof.
  destruct b; unfold evalSegCfg; rewrite <- cons_zero_encRight;
    simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app;
    start_progress.
Qed.

Lemma step_EL_0_false (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((0, false) :: ls) rs -[ tm ]->+ evalSegCfg mAR (bumpL ls) (push0R rs).
Proof.
  unfold evalSegCfg; rewrite <- cons_one_encLeft, <- cons_zero_encRight.
  simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app.
  start_progress.
Qed.

Lemma step_EL_0_true (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((0, true) :: ls) rs -[ tm ]->+ evalSegCfg mAR ((0, false) :: ls) (push0R rs).
Proof.
  unfold evalSegCfg; rewrite <- cons_zero_encRight.
  simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app.
  start_progress.
Qed.

Lemma step_EL_succ (d : nat) (b : bool) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((S d, b) :: ls) rs -[ tm ]->+ evalSegCfg mDL ((d, b) :: ls) (push0R rs).
Proof.
  destruct b; unfold evalSegCfg; rewrite <- cons_zero_encRight;
    simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app;
    start_progress.
Qed.

Lemma step_sweepDLEL (d : nat) (isE b : bool) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  let '(m', ls', rs') := sweepDLEL isE d b ls rs in
  evalSegCfg (sweepMode isE) ((d, b) :: ls) rs -[ tm ]->+ evalSegCfg m' ls' rs'.
Proof.
  revert isE rs.
  induction d as [|d IH]; intros isE rs; simpl.
  - destruct isE, b.
    + exact (step_EL_0_true ls rs).
    + exact (step_EL_0_false ls rs).
    + exact (step_DL_0_true ls rs).
    + exact (step_DL_0_false ls rs).
  - destruct isE; simpl sweepMode; simpl negb.
    + specialize (IH false (push0R rs)).
      destruct (sweepDLEL false d b ls (push0R rs)) as [[m' ls'] rs'].
      exact (progress_trans tm _ _ _ (step_EL_succ d b ls rs) IH).
    + specialize (IH true (push0R rs)).
      destruct (sweepDLEL true d b ls (push0R rs)) as [[m' ls'] rs'].
      exact (progress_trans tm _ _ _ (step_DL_succ d b ls rs) IH).
Qed.

Lemma segmented_step_sound (m : SegMode) (ls : list (nat * bool)) (rs : list (nat * nat))
    (m' : SegMode) (ls' : list (nat * bool)) (rs' : list (nat * nat))
    (h : stepMacro m ls rs = Some (m', ls', rs')) :
  evalSegCfg m ls rs -[ tm ]->+ evalSegCfg m' ls' rs'.
Proof.
  destruct m.
  - exact (step_A_common (encLeft ls) (bumpL ls) (cons_one_encLeft ls) rs m' ls' rs' h).
  - exact (step_A_common (S0 >> encLeft ls) ((0, false) :: ls) eq_refl rs m' ls' rs' h).
  - exact (step_A_common (S0 >> S0 >> encLeft ls) (push100L ls) (cons_100_encLeft ls) rs m' ls' rs' h).
  - destruct ls as [|[[|d] [|]] rest]; unfold stepMacro in h; inversion h; subst.
    + unfold evalSegCfg; rewrite <- cons_one_encRight; simpl encLeft; start_progress.
    + unfold evalSegCfg; simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app; start_progress.
    + unfold evalSegCfg; simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app; start_progress.
    + unfold evalSegCfg; simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app; start_progress.
    + unfold evalSegCfg; simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app; start_progress.
  - destruct ls as [|[d b] rest]; unfold stepMacro in h.
    + inversion h; subst.
      unfold evalSegCfg; simpl encLeft; unfold lWord, lWord_aux, fst, snd; simpl Str_app.
      rewrite <- const_unfold; start_progress.
    + inversion h; subst.
      pose proof (step_sweepDLEL d false b rest rs) as Hsw.
      rewrite H0 in Hsw. exact Hsw.
  - destruct ls as [|[d b] rest]; unfold stepMacro in h.
    + inversion h; subst.
      unfold evalSegCfg; simpl encLeft; start_progress.
    + inversion h; subst.
      pose proof (step_sweepDLEL d true b rest rs) as Hsw.
      rewrite H0 in Hsw. exact Hsw.
  - destruct rs as [|[[|z] [|o]] rest]; unfold stepMacro in h; injection h as <- <- <-.
    + unfold evalSegCfg; rewrite <- cons_one_encLeft; simpl encRight; start_progress.
    + unfold evalSegCfg; rewrite <- cons_zero_encRight, <- cons_zero_encRight.
      simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app; start_progress.
    + unfold evalSegCfg; simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app; start_progress.
    + unfold evalSegCfg; rewrite <- cons_one_encLeft.
      simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app; start_progress.
    + unfold evalSegCfg; rewrite <- cons_one_encLeft.
      simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app; start_progress.
  - destruct rs as [|[[|z] [|o]] rest]; unfold stepMacro in h; injection h as <- <- <-.
    + unfold evalSegCfg; simpl encRight; start_progress.
    + unfold evalSegCfg; rewrite <- cons_zero_encRight, <- cons_zero_encRight.
      simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app; start_progress.
    + unfold evalSegCfg; simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app; start_progress.
    + unfold evalSegCfg; simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app; start_progress.
    + unfold evalSegCfg; simpl encRight; unfold rWord, rWord_aux, oWord, fst, snd; simpl Str_app; start_progress.
Qed.

Lemma mstep {m m' : SegMode} {ls ls' : list (nat * bool)} {rs rs' : list (nat * nat)}
    (h : stepMacro m ls rs = Some (m', ls', rs')) :
  evalSegCfg m ls rs -[ tm ]->+ evalSegCfg m' ls' rs'.
Proof. exact (segmented_step_sound m ls rs m' ls' rs' h). Qed.

Arguments evalSegCfg : simpl never.
Arguments evalA : simpl never.
Local Ltac step1 := eapply mstep; simpl; reflexivity.

(* ========================================================================= *)
(* Section 3: List Helpers & The 11 RLE Bulk Rules                           *)
(* ========================================================================= *)

Fixpoint repPair {X : Type} (a b : X) (k : nat) : list X :=
  match k with
  | 0 => []
  | S k' => a :: b :: repPair a b k'
  end.

Lemma repeat_add {X : Type} (x : X) (m n : nat) :
  repeat x (m + n) = repeat x m ++ repeat x n.
Proof.
  induction m as [|m IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma repeat_append_cons {X : Type} (n : nat) (x : X) (ls : list X) :
  repeat x n ++ x :: ls = repeat x (n + 1) ++ ls.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH. replace (n + 1) with (S n) by lia. reflexivity.
Qed.

Lemma repPair_add {X : Type} (a b : X) (m n : nat) :
  repPair a b (m + n) = repPair a b m ++ repPair a b n.
Proof.
  induction m as [|m IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma repPair_succ_shift {X : Type} (a b : X) (k : nat) :
  repPair a b (k + 1) = a :: repPair b a k ++ [b].
Proof.
  induction k as [|k IH].
  - reflexivity.
  - replace (S k + 1) with (S (k + 1)) by lia.
    simpl repPair at 1. rewrite IH. reflexivity.
Qed.

Lemma repPair_append_cons {X : Type} (n : nat) (a b : X) (ls : list X) :
  repPair a b n ++ a :: b :: ls = repPair a b (n + 1) ++ ls.
Proof.
  rewrite (repPair_add a b n 1), <- app_assoc. reflexivity.
Qed.

Local Ltac ptrans H1 H2 := exact (progress_trans tm _ _ _ H1 H2).

Lemma rule_A1 (k : nat) (hk : 1 <= k) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mAR0 ls (repeat (0, 0) k ++ rs) -[ tm ]->+
    evalSegCfg mAR0 (repeat (0, false) k ++ ls) rs.
Proof.
  destruct k as [|m]; [lia | clear hk].
  revert ls. induction m as [|m IH]; intros ls.
  - simpl.
    eapply progress_trans; [exact (@mstep mAR0 _ ls _ ((0, 0) :: rs) _ eq_refl) |].
    destruct rs as [|[z o] rest]; step1.
  - change (repeat (0, 0) (S (S m)) ++ rs) with ((0, 0) :: repeat (0, 0) (S m) ++ rs).
    eapply progress_trans; [exact (@mstep mAR0 _ ls _ ((0, 0) :: repeat (0, 0) (S m) ++ rs) _ eq_refl) |].
    eapply progress_trans.
    + step1.
    + pose proof (IH ((0, false) :: ls)) as H3.
      rewrite repeat_append_cons in H3.
      replace (S m + 1) with (S (S m)) in H3 by lia.
      exact H3.
Qed.

Lemma rule_A2a_one (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mAR0 ls ((2, 0) :: (0, 0) :: rs) -[ tm ]->+
    evalSegCfg mAR0 ((2, false) :: (0, false) :: ls) rs.
Proof.
  eapply progress_trans; [exact (@mstep mAR0 _ ls _ ((2, 0) :: (0, 0) :: rs) _ eq_refl) |].
  simpl push0R.
  eapply progress_trans; [step1 |].
  simpl bumpL.
  eapply progress_trans; [step1 |].
  destruct rs as [|[z o] rest]; step1.
Qed.

Lemma rule_A2a (k : nat) (hk : 1 <= k) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mAR0 ls (repPair (2, 0) (0, 0) k ++ rs) -[ tm ]->+
    evalSegCfg mAR0 (repPair (2, false) (0, false) k ++ ls) rs.
Proof.
  destruct k as [|m]; [lia | clear hk].
  revert ls. induction m as [|m IH]; intros ls.
  - exact (rule_A2a_one ls rs).
  - change (repPair (2, 0) (0, 0) (S (S m)) ++ rs) with
      ((2, 0) :: (0, 0) :: repPair (2, 0) (0, 0) (S m) ++ rs).
    eapply progress_trans; [exact (rule_A2a_one ls (repPair (2, 0) (0, 0) (S m) ++ rs)) |].
    pose proof (IH ((2, false) :: (0, false) :: ls)) as H2.
    rewrite repPair_append_cons in H2.
    replace (S m + 1) with (S (S m)) in H2 by lia.
    exact H2.
Qed.

Lemma rule_A2b (k : nat) (hk : 2 <= k) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mAR0 ls (repPair (0, 0) (2, 0) k ++ rs) -[ tm ]->+
    evalSegCfg mAR0 (repPair (2, false) (0, false) (k - 1) ++ (0, false) :: ls) ((2, 0) :: rs).
Proof.
  replace k with ((k - 1) + 1) at 1 by lia.
  rewrite repPair_succ_shift.
  rewrite <- app_comm_cons, <- app_assoc. simpl app.
  eapply progress_trans; [exact (rule_A1 1 ltac:(lia) ls (repPair (2, 0) (0, 0) (k - 1) ++ (2, 0) :: rs)) |].
  simpl. exact (rule_A2a (k - 1) ltac:(lia) ((0, false) :: ls) ((2, 0) :: rs)).
Qed.

Lemma rule_A2c (k : nat) (hk : 1 <= k) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mAR0 ls ((2, 0) :: repPair (0, 0) (2, 0) k ++ rs) -[ tm ]->+
    evalSegCfg mAR0 (repPair (2, false) (0, false) k ++ ls) ((2, 0) :: rs).
Proof.
  assert (HR : (2, 0) :: repPair (0, 0) (2, 0) k ++ rs = repPair (2, 0) (0, 0) k ++ (2, 0) :: rs).
  { clear hk. induction k as [|k IH]; simpl; [reflexivity |].
    f_equal. f_equal. exact IH. }
  rewrite HR. exact (rule_A2a k hk ls ((2, 0) :: rs)).
Qed.

Lemma rule_A3_one (d : nat) (b : bool) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mAR0 ((d, b) :: ls) ((4, 0) :: rs) -[ tm ]->+
    evalSegCfg mAR0 ((2, false) :: (d + 2, b) :: ls) rs.
Proof.
  eapply progress_trans; [exact (@mstep mAR0 _ ((d, b) :: ls) _ ((4, 0) :: rs) _ eq_refl) |].
  simpl push1R.
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  simpl sweepDLEL; unfold bumpL, push0R; simpl.
  eapply progress_trans; [step1 |].
  simpl bumpL; simpl push0R.
  replace (S (S d)) with (d + 2) by lia.
  eapply progress_trans; [step1 |].
  simpl bumpL.
  eapply progress_trans; [step1 |].
  simpl bumpL.
  destruct rs as [|[z o] rest]; step1.
Qed.

Lemma rule_A3 (k : nat) (hk : 1 <= k) (d : nat) (b : bool)
    (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mAR0 ((d, b) :: ls) (repeat (4, 0) k ++ rs) -[ tm ]->+
    evalSegCfg mAR0 ((2, false) :: repeat (4, false) (k - 1) ++ (d + 2, b) :: ls) rs.
Proof.
  destruct k as [|m]; [lia | clear hk].
  replace (S m - 1) with m by lia.
  simpl repeat at 1; rewrite <- app_comm_cons.
  eapply progress_evstep_trans; [exact (rule_A3_one d b ls (repeat (4, 0) m ++ rs)) |].
  assert (Hloop : forall (n : nat) (ls' : list (nat * bool)),
    evalSegCfg mAR0 ((2, false) :: ls') (repeat (4, 0) n ++ rs) -[ tm ]->*
      evalSegCfg mAR0 ((2, false) :: repeat (4, false) n ++ ls') rs).
  { induction n as [|n IH]; intros ls'.
    - apply evstep_refl.
    - simpl repeat at 1; rewrite <- app_comm_cons.
      eapply evstep_trans; [apply progress_evstep, (rule_A3_one 2 false ls' (repeat (4, 0) n ++ rs)) |].
      simpl Nat.add.
      pose proof (IH ((4, false) :: ls')) as H2.
      rewrite repeat_append_cons in H2.
      replace (n + 1) with (S n) in H2 by lia.
      exact H2. }
  exact (Hloop m ((d + 2, b) :: ls)).
Qed.

Lemma rule_A4 (k : nat) (hk : 2 <= k) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mAR0 ls (repeat (2, 0) k ++ rs) -[ tm ]->+
    evalSegCfg mDR ((0, false) :: repeat (2, false) (k - 2) ++ (0, false) :: ls) ((3, 0) :: rs).
Proof.
  assert (Hk : k = S (S (k - 2))) by lia.
  remember (k - 2) as m eqn:Heqm. rewrite Hk; clear Hk hk Heqm k.
  change (repeat (2, 0) (S (S m)) ++ rs) with ((2, 0) :: (2, 0) :: repeat (2, 0) m ++ rs).
  eapply progress_evstep_trans.
  { exact (@mstep mAR0 _ ls _ ((2, 0) :: (2, 0) :: repeat (2, 0) m ++ rs) _ eq_refl). }
  simpl push0R.
  assert (Hloop : forall (n : nat) (ls' : list (nat * bool)),
    evalSegCfg mDR ((0, false) :: ls') ((3, 0) :: repeat (2, 0) n ++ rs) -[ tm ]->*
      evalSegCfg mDR ((0, false) :: repeat (2, false) n ++ ls') ((3, 0) :: rs)).
  { induction n as [|n IH]; intros ls'.
    - apply evstep_refl.
    - simpl repeat at 1; rewrite <- app_comm_cons.
      eapply evstep_trans.
      + apply progress_evstep.
        eapply progress_trans; [exact (@mstep mDR _ ((0, false) :: ls') _ ((3, 0) :: (2, 0) :: repeat (2, 0) n ++ rs) _ eq_refl) |].
        simpl bumpL.
        exact (@mstep mAR _ ((1, false) :: ls') _ ((2, 0) :: (2, 0) :: repeat (2, 0) n ++ rs) _ eq_refl).
      + simpl bumpL; simpl push0R.
        pose proof (IH ((2, false) :: ls')) as H2.
        rewrite repeat_append_cons in H2.
        replace (n + 1) with (S n) in H2 by lia.
        exact H2. }
  exact (Hloop m ((0, false) :: ls)).
Qed.

Lemma sweep_mEL_even (q : nat) (ls : list (nat * bool)) (z o : nat) (rs : list (nat * nat)) :
  evalSegCfg mEL ((2 * q, false) :: ls) ((z, o) :: rs) -[ tm ]->+
    evalSegCfg mAR (bumpL ls) ((z + (2 * q + 1), o) :: rs).
Proof.
  pose proof (step_sweepDLEL (2 * q) true false ls ((z, o) :: rs)) as H.
  rewrite sweepDLEL_closed in H.
  assert (Hmod : Nat.eqb ((2 * q) mod 2) 0 = true).
  { apply Nat.eqb_eq. lia. }
  rewrite Hmod, push0R_iter_cons in H.
  exact H.
Qed.

Lemma rule_B1_one (q : nat) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((2 * q + 2, false) :: (2 * q, false) :: ls) ((1, 0) :: rs) -[ tm ]->+
    evalSegCfg mEL ((2 * q + 2, false) :: ls) ((1, 0) :: (2 * q, 0) :: rs).
Proof.
  pose proof (sweep_mEL_even (q + 1) ((2 * q, false) :: ls) 1 0 rs) as S1_step.
  replace (2 * (q + 1)) with (2 * q + 2) in S1_step by lia.
  replace (1 + (2 * q + 2 + 1)) with (S (S (S (S (2 * q))))) in S1_step by lia.
  remember (2 * q) as dq eqn:Hdq.
  simpl bumpL in S1_step.
  eapply progress_trans; [exact S1_step |].
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  eapply mstep; simpl. replace (S (S dq)) with (dq + 2) by lia. reflexivity.
Qed.

Lemma rule_B1 (q k : nat) (hk : 1 <= k) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((2 * q + 2, false) :: repeat (2 * q, false) k ++ ls) ((1, 0) :: rs) -[ tm ]->+
    evalSegCfg mEL ((2 * q + 2, false) :: ls) ((1, 0) :: repeat (2 * q, 0) k ++ rs).
Proof.
  destruct k as [|m]; [lia | clear hk].
  revert rs. induction m as [|m IH]; intros rs.
  - exact (rule_B1_one q ls rs).
  - change (repeat (2 * q, false) (S (S m)) ++ ls) with
      ((2 * q, false) :: repeat (2 * q, false) (S m) ++ ls).
    eapply progress_trans; [exact (rule_B1_one q (repeat (2 * q, false) (S m) ++ ls) rs) |].
    pose proof (IH ((2 * q, 0) :: rs)) as H2.
    rewrite repeat_append_cons in H2.
    replace (S m + 1) with (S (S m)) in H2 by lia.
    exact H2.
Qed.

Lemma rule_B2_one (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((4, false) :: (0, false) :: (2, false) :: ls) ((1, 0) :: rs) -[ tm ]->+
    evalSegCfg mEL ((4, false) :: ls) ((1, 0) :: (0, 0) :: (2, 0) :: rs).
Proof.
  eapply progress_trans; [exact (@mstep mEL _ ((4, false) :: (0, false) :: (2, false) :: ls) _ ((1, 0) :: rs) _ eq_refl) |].
  simpl.
  eapply progress_trans; [step1 |]. simpl.
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |]. simpl.
  eapply progress_trans; [step1 |]. simpl.
  eapply progress_trans; [step1 |].
  step1.
Qed.

Lemma rule_B2 (k : nat) (hk : 1 <= k) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((4, false) :: repPair (0, false) (2, false) k ++ ls) ((1, 0) :: rs) -[ tm ]->+
    evalSegCfg mEL ((4, false) :: ls) ((1, 0) :: repPair (0, 0) (2, 0) k ++ rs).
Proof.
  destruct k as [|m]; [lia | clear hk].
  revert rs. induction m as [|m IH]; intros rs.
  - exact (rule_B2_one ls rs).
  - change (repPair (0, false) (2, false) (S (S m)) ++ ls) with
      ((0, false) :: (2, false) :: repPair (0, false) (2, false) (S m) ++ ls).
    eapply progress_trans; [exact (rule_B2_one (repPair (0, false) (2, false) (S m) ++ ls) rs) |].
    pose proof (IH ((0, 0) :: (2, 0) :: rs)) as H2.
    rewrite repPair_append_cons in H2.
    replace (S m + 1) with (S (S m)) in H2 by lia.
    exact H2.
Qed.

Lemma rule_B3_one (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((2, false) :: (2, false) :: (0, false) :: ls) ((1, 0) :: rs) -[ tm ]->+
    evalSegCfg mEL ((2, false) :: ls) ((1, 0) :: (2, 0) :: (0, 0) :: rs).
Proof.
  eapply progress_trans; [exact (@mstep mEL _ ((2, false) :: (2, false) :: (0, false) :: ls) _ ((1, 0) :: rs) _ eq_refl) |].
  simpl.
  eapply progress_trans; [step1 |]. simpl.
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |]. simpl.
  eapply progress_trans; [step1 |]. simpl.
  eapply progress_trans; [step1 |].
  step1.
Qed.

Lemma rule_B3 (k : nat) (hk : 1 <= k) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((2, false) :: repPair (2, false) (0, false) k ++ ls) ((1, 0) :: rs) -[ tm ]->+
    evalSegCfg mEL ((2, false) :: ls) ((1, 0) :: repPair (2, 0) (0, 0) k ++ rs).
Proof.
  destruct k as [|m]; [lia | clear hk].
  revert rs. induction m as [|m IH]; intros rs.
  - exact (rule_B3_one ls rs).
  - change (repPair (2, false) (0, false) (S (S m)) ++ ls) with
      ((2, false) :: (0, false) :: repPair (2, false) (0, false) (S m) ++ ls).
    eapply progress_trans; [exact (rule_B3_one (repPair (2, false) (0, false) (S m) ++ ls) rs) |].
    pose proof (IH ((2, 0) :: (0, 0) :: rs)) as H2.
    rewrite repPair_append_cons in H2.
    replace (S m + 1) with (S (S m)) in H2 by lia.
    exact H2.
Qed.

Lemma rule_B4 (k : nat) (hk : 2 <= k) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((2, false) :: repPair (0, false) (2, false) k ++ ls) ((1, 0) :: rs) -[ tm ]->+
    evalSegCfg mEL ((2, false) :: (2, false) :: ls)
      ((1, 0) :: repPair (2, 0) (0, 0) (k - 1) ++ (0, 0) :: rs).
Proof.
  replace k with ((k - 1) + 1) at 1 by lia.
  rewrite repPair_succ_shift.
  rewrite <- app_comm_cons, <- app_assoc. simpl app.
  eapply progress_trans; [exact (rule_B1_one 0 (repPair (2, false) (0, false) (k - 1) ++ (2, false) :: ls) rs) |].
  simpl. exact (rule_B3 (k - 1) ltac:(lia) ((2, false) :: ls) ((0, 0) :: rs)).
Qed.

Lemma rule_B5 (k : nat) (hk : 2 <= k) (ls : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mEL ((4, false) :: repPair (2, false) (0, false) k ++ ls) ((1, 0) :: rs) -[ tm ]->+
    evalSegCfg mEL ((4, false) :: (0, false) :: ls)
      ((1, 0) :: repPair (0, 0) (2, 0) (k - 1) ++ (2, 0) :: rs).
Proof.
  replace k with ((k - 1) + 1) at 1 by lia.
  rewrite repPair_succ_shift.
  rewrite <- app_comm_cons, <- app_assoc. simpl app.
  eapply progress_trans; [exact (rule_B1_one 1 (repPair (0, false) (2, false) (k - 1) ++ (0, false) :: ls) rs) |].
  simpl. exact (rule_B2 (k - 1) ltac:(lia) ((0, false) :: ls) ((2, 0) :: rs)).
Qed.

(* ========================================================================= *)
(* Section 5: Odometer Master Theorem                                        *)
(* ========================================================================= *)

Definition bump2 (ls : list (nat * bool)) : list (nat * bool) :=
  match ls with
  | [] => []
  | (d, b) :: xs => (d + 2, b) :: xs
  end.

Definition bump4 (ls : list (nat * bool)) : list (nat * bool) :=
  match ls with
  | [] => []
  | (d, b) :: xs => (d + 4, b) :: xs
  end.

Fixpoint encW (w : list bool) : list (nat * bool) :=
  match w with
  | [] => []
  | false :: u => (0, false) :: encW u
  | true :: u => (2, false) :: encW u
  end.

Lemma evalA_zero_zero {xs : list (nat * bool)} (hxs : xs <> []) (rs : list (nat * nat)) :
  evalA xs ((0, 0) :: rs) -[ tm ]->+ evalA ((0, false) :: xs) rs.
Proof.
  destruct xs as [|p ys]; [contradiction |].
  rewrite evalA_zero_false.
  eapply progress_trans; [exact (step_evalA p ys ((0, 0) :: rs) mER (p :: ys) (push0R rs) eq_refl) |].
  destruct rs as [|[z o] rest]; step1.
Qed.

Lemma evalA_two_zero {xs : list (nat * bool)} (hxs : xs <> []) (rs : list (nat * nat)) :
  evalA xs ((2, 0) :: rs) -[ tm ]->+ evalA ((2, false) :: xs) rs.
Proof.
  destruct xs as [|p ys]; [contradiction |].
  change (2, false) with (1 + 1, false).
  rewrite evalA_succ.
  eapply progress_trans; [exact (step_evalA p ys ((2, 0) :: rs) mDR ((0, false) :: p :: ys) (push0R rs) eq_refl) |].
  destruct rs as [|[z o] rest]; step1.
Qed.

Lemma evalA_one_zero {xs : list (nat * bool)} (hxs : xs <> []) (rs : list (nat * nat)) :
  evalA xs ((1, 0) :: rs) -[ tm ]->+ evalA ((0, true) :: xs) rs.
Proof.
  destruct xs as [|p ys]; [contradiction |].
  rewrite evalA_zero_true.
  exact (step_evalA p ys ((1, 0) :: rs) mAR00 (p :: ys) rs eq_refl).
Qed.

Lemma evalA_four_zero {xs : list (nat * bool)} (hxs : xs <> []) (rs : list (nat * nat)) :
  evalA xs ((4, 0) :: rs) -[ tm ]->+ evalSegCfg mEL xs ((1, 0) :: (0, 0) :: rs).
Proof.
  destruct xs as [|p ys]; [contradiction |].
  eapply progress_trans; [exact (step_evalA p ys ((4, 0) :: rs) mCL (p :: ys) ((0, 1) :: (0, 0) :: rs) eq_refl) |].
  eapply progress_trans; [step1 | step1].
Qed.

Definition P2 (xs xs' : list (nat * bool)) : Prop :=
  forall rs, evalSegCfg mEL ((2, false) :: xs) ((1, 0) :: rs) -[ tm ]->* evalA ((0, false) :: xs') rs.

Definition P4 (xs xs' : list (nat * bool)) : Prop :=
  forall rs, evalSegCfg mEL ((4, false) :: xs) ((1, 0) :: rs) -[ tm ]->* evalA ((2, false) :: xs') rs.

Definition Step4 (xs xs' : list (nat * bool)) : Prop :=
  xs' <> [] /\ forall rs, evalSegCfg mEL (bump4 xs) ((1, 0) :: rs) -[ tm ]->* evalA xs' rs.

Lemma cons_neq_nil {X : Type} (x : X) (xs : list X) : x :: xs <> [].
Proof. discriminate. Qed.

Lemma p2_cons0 {xs xs' : list (nat * bool)} (h : P2 xs xs') :
  P2 ((0, false) :: xs) ((0, false) :: xs').
Proof.
  intros rs.
  eapply evstep_trans; [apply progress_evstep, (rule_B1_one 0 xs rs) |].
  simpl.
  eapply evstep_trans; [exact (h ((0, 0) :: rs)) |].
  apply progress_evstep, (evalA_zero_zero (cons_neq_nil _ _) rs).
Qed.

Lemma p2_cons2 {xs xs' : list (nat * bool)} (h : P4 xs xs') :
  P2 ((2, false) :: xs) ((2, false) :: xs').
Proof.
  intros rs.
  eapply evstep_trans.
  - apply progress_evstep.
    eapply progress_trans; [exact (@mstep mEL _ ((2, false) :: (2, false) :: xs) _ ((1, 0) :: rs) _ eq_refl) |].
    simpl.
    eapply progress_trans; [step1 |]. simpl.
    eapply progress_trans; [step1 | step1].
  - eapply evstep_trans; [exact (h ((0, 0) :: rs)) |].
    apply progress_evstep, (evalA_zero_zero (cons_neq_nil _ _) rs).
Qed.

Lemma p4_cons0 {xs xs' : list (nat * bool)} (h : P2 xs xs') :
  P4 ((0, false) :: xs) ((0, false) :: xs').
Proof.
  intros rs.
  eapply evstep_trans.
  - apply progress_evstep.
    eapply progress_trans; [exact (@mstep mEL _ ((4, false) :: (0, false) :: xs) _ ((1, 0) :: rs) _ eq_refl) |].
    simpl.
    eapply progress_trans; [step1 |]. simpl.
    eapply progress_trans; [step1 | step1].
  - eapply evstep_trans; [exact (h ((2, 0) :: rs)) |].
    apply progress_evstep, (evalA_two_zero (cons_neq_nil _ _) rs).
Qed.

Lemma p4_cons2 {xs xs' : list (nat * bool)} (h : P4 xs xs') :
  P4 ((2, false) :: xs) ((2, false) :: xs').
Proof.
  intros rs.
  eapply evstep_trans; [apply progress_evstep, (rule_B1_one 1 xs rs) |].
  simpl.
  eapply evstep_trans; [exact (h ((2, 0) :: rs)) |].
  apply progress_evstep, (evalA_two_zero (cons_neq_nil _ _) rs).
Qed.

Lemma p2_bump2 {xs xs' : list (nat * bool)} (hxs : xs <> []) (h : Step4 xs xs') :
  P2 (bump2 xs) xs'.
Proof.
  destruct xs as [|[d b] ys]; [contradiction |].
  destruct h as [hxs' hstep]. intros rs. simpl bump2.
  eapply evstep_trans.
  - apply progress_evstep.
    eapply progress_trans; [exact (@mstep mEL _ ((2, false) :: (d + 2, b) :: ys) _ ((1, 0) :: rs) _ eq_refl) |].
    simpl.
    eapply progress_trans; [step1 |].
    simpl bumpL; simpl push1R.
    replace (S (S (d + 2))) with (d + 4) by lia.
    eapply progress_trans; [step1 | step1].
  - eapply evstep_trans; [exact (hstep ((0, 0) :: rs)) |].
    apply progress_evstep, (evalA_zero_zero hxs' rs).
Qed.

Lemma p4_bump2 {xs xs' : list (nat * bool)} (hxs : xs <> []) (h : Step4 xs xs') :
  P4 (bump2 xs) xs'.
Proof.
  destruct xs as [|[d b] ys]; [contradiction |].
  destruct h as [hxs' hstep]. intros rs. simpl bump2.
  eapply evstep_trans.
  - apply progress_evstep.
    eapply progress_trans; [exact (@mstep mEL _ ((4, false) :: (d + 2, b) :: ys) _ ((1, 0) :: rs) _ eq_refl) |].
    simpl.
    eapply progress_trans; [step1 |].
    simpl bumpL; simpl push1R.
    replace (S (S (d + 2))) with (d + 4) by lia.
    eapply progress_trans; [step1 | step1].
  - eapply evstep_trans; [exact (hstep ((2, 0) :: rs)) |].
    apply progress_evstep, (evalA_two_zero hxs' rs).
Qed.

Lemma step4_0 {xs xs' : list (nat * bool)} (h : P4 xs xs') :
  Step4 ((0, false) :: xs) ((2, false) :: xs').
Proof.
  split; [apply cons_neq_nil | exact h].
Qed.

Lemma step4_20 {xs xs' : list (nat * bool)} (h : P2 xs xs') (hxs' : xs' <> []) :
  Step4 ((2, false) :: (0, false) :: xs) ((0, false) :: (2, false) :: bump2 xs').
Proof.
  split; [apply cons_neq_nil | intros rs].
  destruct xs' as [|[d b] ys]; [contradiction |].
  simpl bump4; simpl bump2.
  eapply evstep_trans.
  - apply progress_evstep.
    eapply progress_trans; [exact (@mstep mEL _ ((6, false) :: (0, false) :: xs) _ ((1, 0) :: rs) _ eq_refl) |].
    simpl.
    eapply progress_trans; [step1 |]. simpl.
    eapply progress_trans; [step1 | step1].
  - eapply evstep_trans; [exact (h ((4, 0) :: rs)) |].
    eapply evstep_trans; [apply progress_evstep, (evalA_four_zero (cons_neq_nil _ _) rs) |].
    rewrite evalA_zero_false.
    apply progress_evstep.
    eapply progress_trans; [exact (@mstep mEL _ ((0, false) :: (d, b) :: ys) _ ((1, 0) :: (0, 0) :: rs) _ eq_refl) |].
    simpl sweepDLEL; unfold bumpL, push0R; simpl.
    eapply progress_trans; [step1 |].
    simpl bumpL; simpl push0R.
    replace (S (S d)) with (d + 2) by lia.
    eapply progress_trans; [step1 |].
    simpl bumpL.
    eapply progress_trans; [step1 |].
    simpl bumpL.
    destruct rs as [|[z o] rest]; step1.
Qed.

Lemma step4_22 {xs x1 x2 : list (nat * bool)} (h1 : P4 xs x1) (h2 : P2 x1 x2) :
  Step4 ((2, false) :: (2, false) :: xs) ((0, false) :: (0, false) :: x2).
Proof.
  split; [apply cons_neq_nil | intros rs].
  simpl bump4.
  eapply evstep_trans.
  - apply progress_evstep.
    eapply progress_trans; [exact (@mstep mEL _ ((6, false) :: (2, false) :: xs) _ ((1, 0) :: rs) _ eq_refl) |].
    simpl.
    eapply progress_trans; [step1 |]. simpl.
    eapply progress_trans; [step1 | step1].
  - eapply evstep_trans; [exact (h1 ((4, 0) :: rs)) |].
    eapply evstep_trans; [apply progress_evstep, (evalA_four_zero (cons_neq_nil _ _) rs) |].
    eapply evstep_trans; [exact (h2 ((0, 0) :: rs)) |].
    apply progress_evstep, (evalA_zero_zero (cons_neq_nil _ _) rs).
Qed.

Definition P24 (xs xs' : list (nat * bool)) : Prop := P2 xs xs' /\ P4 xs xs'.

Definition P24N (n : nat) (fn : nat -> list (nat * bool)) : Prop :=
  forall t, t < n -> P24 (fn t) (fn (t + 1)).

Lemma p24_of_cons0 {xs xs' : list (nat * bool)} (h : P2 xs xs') :
  P24 ((0, false) :: xs) ((0, false) :: xs').
Proof. split; [exact (p2_cons0 h) | exact (p4_cons0 h)]. Qed.

Lemma p24_cons0 {xs xs' : list (nat * bool)} (h : P24 xs xs') :
  P24 ((0, false) :: xs) ((0, false) :: xs').
Proof. destruct h as [h2 _]; split; [exact (p2_cons0 h2) | exact (p4_cons0 h2)]. Qed.

Lemma p24_cons2 {xs xs' : list (nat * bool)} (h : P24 xs xs') :
  P24 ((2, false) :: xs) ((2, false) :: xs').
Proof. destruct h as [_ h4]; split; [exact (p2_cons2 h4) | exact (p4_cons2 h4)]. Qed.

Lemma p24_of_step4 {xs xs' : list (nat * bool)} (hxs : xs <> []) (h : Step4 xs xs') :
  P24 (bump2 xs) xs'.
Proof. split; [exact (p2_bump2 hxs h) | exact (p4_bump2 hxs h)]. Qed.

Lemma p24_append_w (w : list bool) {xs xs' : list (nat * bool)} (h : P24 xs xs') :
  P24 (encW w ++ xs) (encW w ++ xs').
Proof.
  induction w as [|[|] bs IH]; simpl.
  - exact h.
  - exact (p24_cons2 IH).
  - exact (p24_cons0 IH).
Qed.

Lemma p24N_append_w (w : list bool) {n : nat} {fn : nat -> list (nat * bool)} (h : P24N n fn) :
  P24N n (fun t => encW w ++ fn t).
Proof.
  intros t ht. exact (p24_append_w w (h t ht)).
Qed.

Lemma hub_enter_0 {ls : list (nat * bool)} (hls : ls <> []) :
  evalSegCfg mAR0 ls [] -[ tm ]->+ evalSegCfg mEL (bump4 ls) [(1, 0); (0, 0)].
Proof.
  destruct ls as [|[d b] ys]; [contradiction |].
  simpl bump4.
  eapply progress_trans; [exact (@mstep mAR0 _ ((d, b) :: ys) _ [] _ eq_refl) |].
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  simpl sweepDLEL; unfold bumpL, push0R; simpl.
  eapply progress_trans; [step1 |].
  simpl bumpL; simpl push0R.
  eapply progress_trans; [step1 |]. simpl bumpL.
  eapply progress_trans; [step1 |]. simpl bumpL.
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  simpl sweepDLEL; unfold bumpL, push0R; simpl.
  eapply progress_trans; [step1 |].
  simpl bumpL; simpl push1R.
  replace (S (S (S (S d)))) with (d + 4) by lia.
  eapply progress_trans; [step1 | step1].
Qed.

Lemma hub_0plus_first (zs : list (nat * bool)) :
  evalSegCfg mAR0 ((0, true) :: zs) [] -[ tm ]->+
    evalSegCfg mAR0 zs [(3, 0); (2, 0); (0, 0)].
Proof.
  eapply progress_trans; [exact (@mstep mAR0 _ ((0, true) :: zs) _ [] _ eq_refl) |].
  do 16 (eapply progress_trans; [step1 |]; simpl).
  step1.
Qed.

Lemma hub_0plus_next (zs : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mAR0 ((0, true) :: zs) ((3, 0) :: (2, 0) :: rs) -[ tm ]->+
    evalSegCfg mAR0 zs ((3, 0) :: (2, 0) :: (1, 0) :: rs).
Proof.
  eapply progress_trans; [exact (@mstep mAR0 _ ((0, true) :: zs) _ ((3, 0) :: (2, 0) :: rs) _ eq_refl) |].
  do 13 (eapply progress_trans; [step1 |]; simpl).
  step1.
Qed.

Lemma hub_0plus_rep (q : nat) (zs : list (nat * bool)) (rs : list (nat * nat)) :
  evalSegCfg mAR0 (repeat (0, true) q ++ zs) ((3, 0) :: (2, 0) :: rs) -[ tm ]->*
    evalSegCfg mAR0 zs ((3, 0) :: (2, 0) :: repeat (1, 0) q ++ rs).
Proof.
  revert rs. induction q as [|q IH]; intros rs.
  - apply evstep_refl.
  - simpl repeat at 1; rewrite <- app_comm_cons.
    eapply evstep_trans; [apply progress_evstep, (hub_0plus_next (repeat (0, true) q ++ zs) rs) |].
    pose proof (IH ((1, 0) :: rs)) as H2.
    rewrite repeat_append_cons in H2.
    replace (q + 1) with (S q) in H2 by lia.
    exact H2.
Qed.

Lemma hub_0plus_finish {ls : list (nat * bool)} (hls : ls <> []) (rs : list (nat * nat)) :
  evalSegCfg mAR0 ls ((3, 0) :: (2, 0) :: rs) -[ tm ]->+
    evalSegCfg mEL (bump4 ls) ((1, 0) :: (1, 0) :: rs).
Proof.
  destruct ls as [|[d b] ys]; [contradiction |].
  simpl bump4.
  eapply progress_trans; [exact (@mstep mAR0 _ ((d, b) :: ys) _ ((3, 0) :: (2, 0) :: rs) _ eq_refl) |].
  simpl push1R.
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  eapply progress_trans; [step1 |].
  simpl sweepDLEL; unfold bumpL, push0R; simpl.
  eapply progress_trans; [step1 |].
  simpl bumpL.
  eapply progress_trans; [step1 |].
  simpl push0R.
  eapply progress_trans; [step1 |].
  simpl sweepDLEL; unfold bumpL, push0R; simpl.
  eapply progress_trans; [step1 |].
  simpl bumpL; simpl push1R.
  replace (S (S (S (S d)))) with (d + 4) by lia.
  eapply progress_trans; [step1 | step1].
Qed.

Lemma hub_enter_0plus (p : nat) {ls : list (nat * bool)} (hls : ls <> []) :
  evalSegCfg mAR0 (repeat (0, true) p ++ ls) [] -[ tm ]->+
    evalSegCfg mEL (bump4 ls) ((1, 0) :: repeat (1, 0) p ++ [(0, 0)]).
Proof.
  destruct p as [|q].
  - exact (hub_enter_0 hls).
  - simpl repeat at 1; rewrite <- app_comm_cons.
    eapply progress_trans.
    + eapply progress_evstep_trans.
      * exact (hub_0plus_first (repeat (0, true) q ++ ls)).
      * exact (hub_0plus_rep q ls [(0, 0)]).
    + exact (hub_0plus_finish hls (repeat (1, 0) q ++ [(0, 0)])).
Qed.

Lemma hub_exit_0plus (p : nat) {xs : list (nat * bool)} (hxs : xs <> []) :
  evalA xs (repeat (1, 0) p ++ [(0, 0)]) -[ tm ]->+
    evalSegCfg mAR0 (repeat (0, true) p ++ xs) [].
Proof.
  revert xs hxs. induction p as [|p IH]; intros xs hxs.
  - simpl. rewrite <- evalA_zero_false. exact (evalA_zero_zero hxs []).
  - simpl repeat at 1; rewrite <- app_comm_cons.
    eapply progress_trans; [exact (evalA_one_zero hxs (repeat (1, 0) p ++ [(0, 0)])) |].
    pose proof (IH ((0, true) :: xs) (cons_neq_nil _ _)) as H2.
    rewrite repeat_append_cons in H2.
    replace (p + 1) with (S p) in H2 by lia.
    exact H2.
Qed.

Lemma hub_of_step4 (p : nat) {ls ls' : list (nat * bool)} (hls : ls <> []) (h : Step4 ls ls') :
  evalSegCfg mAR0 (repeat (0, true) p ++ ls) [] -[ tm ]->*
    evalSegCfg mAR0 (repeat (0, true) p ++ ls') [].
Proof.
  destruct h as [hls' hstep].
  eapply evstep_trans; [apply progress_evstep, (hub_enter_0plus p hls) |].
  eapply evstep_trans; [exact (hstep (repeat (1, 0) p ++ [(0, 0)])) |].
  apply progress_evstep, (hub_exit_0plus p hls').
Qed.

Fixpoint prePostVal (k : nat) : nat * nat :=
  match k with
  | 0 => (2, 2)
  | S k' =>
    let '(pr, po) := prePostVal k' in
    (2 * pr + po + 2, 2 * pr + 3 * po + 2)
  end.

Definition preVal (k : nat) : nat := fst (prePostVal k).
Definition postVal (k : nat) : nat := snd (prePostVal k).

Lemma preVal_0 : preVal 0 = 2. Proof. reflexivity. Qed.
Lemma postVal_0 : postVal 0 = 2. Proof. reflexivity. Qed.

Lemma preVal_S (k : nat) : preVal (S k) = 2 * preVal k + postVal k + 2.
Proof.
  unfold preVal, postVal; simpl. destruct (prePostVal k); reflexivity.
Qed.

Lemma postVal_S (k : nat) : postVal (S k) = 2 * preVal k + 3 * postVal k + 2.
Proof.
  unfold preVal, postVal; simpl. destruct (prePostVal k); reflexivity.
Qed.

Lemma postVal_ge_two (k : nat) : 2 <= postVal k.
Proof.
  destruct k as [|k]; [rewrite postVal_0; lia | rewrite postVal_S; lia].
Qed.

Lemma odom_master (p k : nat) :
  forall (fn gn : nat -> list (nat * bool)),
    fn (preVal k) <> [] ->
    P24N (preVal k) fn ->
    Step4 (fn (preVal k)) (gn 0) ->
    P24N (postVal k) gn ->
    evalSegCfg mAR0 (repeat (0, true) p ++ repeat (0, false) (2 * (k + 1)) ++ fn 0) [] -[ tm ]->*
    evalSegCfg mAR0 (repeat (0, true) p ++ repeat (0, false) (2 * (k + 1)) ++ gn (postVal k)) [].
Proof.
  induction k as [|k IH]; intros fn gn hFne hF hS4 hG.
  - rewrite preVal_0 in hFne, hF, hS4.
    rewrite postVal_0 in hG |- *.
    replace (2 * (0 + 1)) with 2 by lia.
    simpl (repeat (0, false) 2).
    repeat rewrite <- app_assoc; simpl app.
    eapply evstep_trans.
    + eapply (hub_of_step4 p (cons_neq_nil _ _)).
      eapply step4_0, p4_cons0, (proj1 (hF 0 ltac:(lia))).
    + eapply evstep_trans.
      * eapply (hub_of_step4 p (cons_neq_nil _ _)).
        exact (step4_20 (proj1 (hF 1 ltac:(lia))) hFne).
      * eapply evstep_trans.
        -- eapply (hub_of_step4 p (cons_neq_nil _ _)).
           exact (step4_0 (p4_cons2 (p4_bump2 hFne hS4))).
        -- eapply (hub_of_step4 p (cons_neq_nil _ _)).
           exact (step4_22 (proj2 (hG 0 ltac:(lia))) (proj1 (hG 1 ltac:(lia)))).
  - set (vA := preVal k).
    set (vB := postVal k).
    fold vA vB in IH.
    pose proof (postVal_ge_two k) as hB2; fold vB in hB2.
    assert (hpre : preVal (S k) = 2 * vA + vB + 2) by exact (preVal_S k).
    assert (hpost : postVal (S k) = 2 * vA + 3 * vB + 2) by exact (postVal_S k).
    assert (hrep : forall xs : list (nat * bool),
      repeat (0, true) p ++ repeat (0, false) (2 * (S k + 1)) ++ xs =
      repeat (0, true) p ++ repeat (0, false) (2 * (k + 1)) ++ (0, false) :: (0, false) :: xs).
    { intros xs.
      replace (2 * (S k + 1)) with (2 * (k + 1) + 2) by lia.
      rewrite repeat_add, <- app_assoc. reflexivity. }
    rewrite (hrep (fn 0)), (hrep (gn (postVal (S k)))).
    (* Phase 1 *)
    eapply evstep_trans.
    { apply (IH (fun t => (0, false) :: (0, false) :: fn t)
                (fun t => (2, false) :: (0, false) :: fn (vA + 1 + t))).
      - apply cons_neq_nil.
      - intros t ht. apply p24_cons0, p24_cons0, hF. lia.
      - replace (vA + 1 + 0) with (vA + 1) by lia.
        apply step4_0, p4_cons0. exact (proj1 (hF vA ltac:(lia))).
      - intros t ht. apply p24_cons2, p24_cons0.
        replace (vA + 1 + (t + 1)) with ((vA + 1 + t) + 1) by lia.
        apply hF. lia. }
    (* Phase 2 *)
    set (G2 := fun t : nat =>
      match t with
      | 0 => (0, false) :: (2, false) :: bump2 (fn (preVal (S k)))
      | S t' => (0, false) :: (2, false) :: gn t'
      end).
    eapply evstep_trans.
    { pose proof (IH (fun t => (2, false) :: (0, false) :: fn (vA + 1 + vB + t)) G2) as ph2.
      cbv beta in ph2.
      replace (vA + 1 + vB + 0) with (vA + 1 + vB) in ph2 by lia.
      apply ph2.
      - apply cons_neq_nil.
      - intros t ht. apply p24_cons2, p24_cons0.
        replace (vA + 1 + vB + (t + 1)) with ((vA + 1 + vB + t) + 1) by lia.
        apply hF. lia.
      - pose proof (hF (vA + 1 + vB + vA) ltac:(lia)) as hstep.
        replace ((vA + 1 + vB + vA) + 1) with (preVal (S k)) in hstep by lia.
        exact (step4_20 (proj1 hstep) hFne).
      - intros t ht. destruct t as [|t']; unfold G2.
        + simpl. exact (p24_cons0 (p24_cons2 (p24_of_step4 hFne hS4))).
        + replace (S t' + 1) with (S (t' + 1)) by lia.
          exact (p24_cons0 (p24_cons2 (hG t' ltac:(lia)))). }
    assert (hG2_B : G2 vB = (0, false) :: (2, false) :: gn (vB - 1)).
    { unfold G2. destruct vB as [|b']; [lia |].
      replace (S b' - 1) with b' by lia. reflexivity. }
    rewrite hG2_B.
    (* Phase 3 *)
    eapply evstep_trans.
    { pose proof (IH (fun t => (0, false) :: (2, false) :: gn (vB - 1 + t))
                     (fun t => (2, false) :: (2, false) :: gn (vA + vB + t))) as ph3.
      cbv beta in ph3.
      replace (vB - 1 + 0) with (vB - 1) in ph3 by lia.
      apply ph3.
      - apply cons_neq_nil.
      - intros t ht. apply p24_cons0, p24_cons2.
        replace (vB - 1 + (t + 1)) with ((vB - 1 + t) + 1) by lia.
        apply hG. lia.
      - pose proof (hG (vB - 1 + vA) ltac:(lia)) as hstep.
        replace ((vB - 1 + vA) + 1) with (vA + vB + 0) in hstep by lia.
        exact (step4_0 (p4_cons2 (proj2 hstep))).
      - intros t ht. apply p24_cons2, p24_cons2.
        replace (vA + vB + (t + 1)) with ((vA + vB + t) + 1) by lia.
        apply hG. lia. }
    (* Phase 4 *)
    pose proof (IH (fun t => (2, false) :: (2, false) :: gn (vA + vB + vB + t))
                   (fun t => (0, false) :: (0, false) :: gn (2 * vA + 2 * vB + 2 + t))) as ph4.
    cbv beta in ph4.
    replace (vA + vB + vB + 0) with (vA + vB + vB) in ph4 by lia.
    replace (2 * vA + 2 * vB + 2 + vB) with (postVal (S k)) in ph4 by lia.
    apply ph4.
    + apply cons_neq_nil.
    + intros t ht. apply p24_cons2, p24_cons2.
      replace (vA + vB + vB + (t + 1)) with ((vA + vB + vB + t) + 1) by lia.
      apply hG. lia.
    + pose proof (hG (vA + vB + vB + vA) ltac:(lia)) as hs1.
      pose proof (hG ((vA + vB + vB + vA) + 1) ltac:(lia)) as hs2.
      replace (((vA + vB + vB + vA) + 1) + 1) with (2 * vA + 2 * vB + 2 + 0) in hs2 by lia.
      exact (step4_22 (proj2 hs1) (proj1 hs2)).
    + intros t ht. apply p24_cons0, p24_cons0.
      replace (2 * vA + 2 * vB + 2 + (t + 1)) with ((2 * vA + 2 * vB + 2 + t) + 1) by lia.
      apply hG. lia.
Qed.

Local Close Scope sym_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope N_scope.

Local Open Scope N_scope.

Inductive LRun : Type :=
  | LOne (d : N) (b : bool) (cnt : N)
  | LTwo (d1 : N) (b1 : bool) (d2 : N) (b2 : bool) (cnt : N).

Inductive RRun : Type :=
  | ROne (z : N) (o : N) (cnt : N)
  | RTwo (z1 : N) (o1 : N) (z2 : N) (o2 : N) (cnt : N).

Inductive SymCnt : Type :=
  | SCConst (a : N)
  | SCInc (a : N) (d : N)
  | SCDec (a : N) (d : N).

Inductive SLRun : Type :=
  | SLOne (d : N) (b : bool) (c : SymCnt)
  | SLTwo (d1 : N) (b1 : bool) (d2 : N) (b2 : bool) (c : SymCnt).

Inductive SRRun : Type :=
  | SROne (z : N) (o : N) (c : SymCnt)
  | SRTwo (z1 : N) (o1 : N) (z2 : N) (o2 : N) (c : SymCnt).

Inductive SlopeSpec : Type :=
  | SlZ
  | SlP (d : N)
  | SlN (d : N).

Inductive Op : Type :=
  | OpRun (steps : N)
  | OpJump (p : N) (m : N) (ssteps : N) (w : list bool) (slopes : list SlopeSpec).

Inductive StepRes : Type :=
  | SROk (m : SegMode) (ls : list LRun) (rs : list RRun)
  | SRHalted
  | SRErr.

Inductive SymState : Type :=
  | SSOk (m : SegMode) (ls : list SLRun) (rs : list SRRun)
  | SSErr.

Inductive CarryRes : Type :=
  | CROk (w : list bool) (extra : N)
  | CRErr.

Inductive SymBuildRes : Type :=
  | SBOk (sL : list SLRun) (sTarg : list SLRun) (bFin : list LRun)
  | SBErr.

Inductive PopLRes : Type :=
  | PLOk (d : N) (b : bool) (rest : list LRun)
  | PLErr.

Inductive PopRRes : Type :=
  | PROk (z : N) (o : N) (rest : list RRun)
  | PRErr.

Inductive PopSLRes : Type :=
  | PSLOk (d : N) (b : bool) (rest : list SLRun)
  | PSLErr.

Inductive PopSRRes : Type :=
  | PSROk (z : N) (o : N) (rest : list SRRun)
  | PSRErr.

Definition beqSC (c1 c2 : SymCnt) : bool :=
  match c1, c2 with
  | SCConst a1, SCConst a2 => N.eqb a1 a2
  | SCInc a1 d1, SCInc a2 d2 => N.eqb a1 a2 && N.eqb d1 d2
  | SCDec a1 d1, SCDec a2 d2 => N.eqb a1 a2 && N.eqb d1 d2
  | _, _ => false
  end.

Definition beqSLRun (x y : SLRun) : bool :=
  match x, y with
  | SLOne d1 b1 c1, SLOne d2 b2 c2 =>
    N.eqb d1 d2 && Bool.eqb b1 b2 && beqSC c1 c2
  | SLTwo d1 b1 d2 b2 c1, SLTwo d1' b1' d2' b2' c2 =>
    N.eqb d1 d1' && Bool.eqb b1 b1' && N.eqb d2 d2' && Bool.eqb b2 b2' && beqSC c1 c2
  | _, _ => false
  end.

Fixpoint beqListSLRun (xs ys : list SLRun) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => beqSLRun x y && beqListSLRun xs' ys'
  | _, _ => false
  end.

Definition foldLStep (next : list LRun -> list LRun) (ls : list LRun) : list LRun :=
  match ls with
  | LOne d1 b1 c1 :: LOne d2 b2 c2 :: rest =>
    if N.eqb d1 d2 && Bool.eqb b1 b2 then
      next (LOne d1 b1 (c1 + c2) :: rest)
    else if N.eqb c1 1 && N.eqb c2 1 then
      match rest with
      | LTwo td1 tb1 td2 tb2 tc :: rest2 =>
        if N.eqb td1 d1 && Bool.eqb tb1 b1 && N.eqb td2 d2 && Bool.eqb tb2 b2 then
          next (LTwo td1 tb1 td2 tb2 (tc + 1) :: rest2)
        else ls
      | LOne d3 b3 c3 :: LOne d4 b4 c4 :: rest2 =>
        if N.eqb c3 1 && N.eqb c4 1 &&
           N.eqb d1 d3 && Bool.eqb b1 b3 && N.eqb d2 d4 && Bool.eqb b2 b4 then
          next (LTwo d1 b1 d2 b2 2 :: rest2)
        else ls
      | _ => ls
      end
    else ls
  | LTwo d1 b1 d2 b2 c1 :: LTwo d1' b1' d2' b2' c2 :: rest =>
    if N.eqb d1 d1' && Bool.eqb b1 b1' && N.eqb d2 d2' && Bool.eqb b2 b2' then
      next (LTwo d1 b1 d2 b2 (c1 + c2) :: rest)
    else ls
  | _ => ls
  end.

Definition foldL3 (ls : list LRun) : list LRun :=
  foldLStep (foldLStep (foldLStep (fun x => x))) ls.

Definition foldRStep (next : list RRun -> list RRun) (rs : list RRun) : list RRun :=
  match rs with
  | ROne z1 o1 c1 :: ROne z2 o2 c2 :: rest =>
    if N.eqb z1 z2 && N.eqb o1 o2 then
      next (ROne z1 o1 (c1 + c2) :: rest)
    else if N.eqb c1 1 && N.eqb c2 1 then
      match rest with
      | RTwo tz1 to1 tz2 to2 tc :: rest2 =>
        if N.eqb tz1 z1 && N.eqb to1 o1 && N.eqb tz2 z2 && N.eqb to2 o2 then
          next (RTwo tz1 to1 tz2 to2 (tc + 1) :: rest2)
        else rs
      | ROne z3 o3 c3 :: ROne z4 o4 c4 :: rest2 =>
        if N.eqb c3 1 && N.eqb c4 1 &&
           N.eqb z1 z3 && N.eqb o1 o3 && N.eqb z2 z4 && N.eqb o2 o4 then
          next (RTwo z1 o1 z2 o2 2 :: rest2)
        else rs
      | _ => rs
      end
    else rs
  | RTwo z1 o1 z2 o2 c1 :: RTwo z1' o1' z2' o2' c2 :: rest =>
    if N.eqb z1 z1' && N.eqb o1 o1' && N.eqb z2 z2' && N.eqb o2 o2' then
      next (RTwo z1 o1 z2 o2 (c1 + c2) :: rest)
    else rs
  | _ => rs
  end.

Definition foldR3 (rs : list RRun) : list RRun :=
  foldRStep (foldRStep (foldRStep (fun x => x))) rs.

Definition pushL1C (ls : list LRun) (d : N) (b : bool) (k : N) : list LRun :=
  foldL3 (LOne d b k :: ls).

Definition pushR1C (rs : list RRun) (z o k : N) : list RRun :=
  foldR3 (ROne z o k :: rs).

Definition pushL1 (ls : list LRun) (d : N) (b : bool) (k : N) : list LRun :=
  if N.eqb k 0 then ls else foldL3 (LOne d b k :: ls).

Definition pushL2 (ls : list LRun) (d1 : N) (b1 : bool) (d2 : N) (b2 : bool) (k : N) : list LRun :=
  if N.eqb k 0 then ls else foldL3 (LTwo d1 b1 d2 b2 k :: ls).

Definition pushR1 (rs : list RRun) (z o k : N) : list RRun :=
  if N.eqb k 0 then rs else foldR3 (ROne z o k :: rs).

Definition pushR2 (rs : list RRun) (z1 o1 z2 o2 k : N) : list RRun :=
  if N.eqb k 0 then rs else foldR3 (RTwo z1 o1 z2 o2 k :: rs).

Definition popL (ls : list LRun) : PopLRes :=
  match ls with
  | [] => PLErr
  | LOne d b cnt :: rest =>
    if N.eqb cnt 0 then PLErr
    else if N.eqb cnt 1 then PLOk d b rest
    else PLOk d b (LOne d b (cnt - 1) :: rest)
  | LTwo d1 b1 d2 b2 cnt :: rest =>
    if N.eqb cnt 0 then PLErr
    else if N.eqb cnt 1 then PLOk d1 b1 (LOne d2 b2 1 :: rest)
    else PLOk d1 b1 (LOne d2 b2 1 :: LTwo d1 b1 d2 b2 (cnt - 1) :: rest)
  end.

Definition popR (rs : list RRun) : PopRRes :=
  match rs with
  | [] => PRErr
  | ROne z o cnt :: rest =>
    if N.eqb cnt 0 then PRErr
    else if N.eqb cnt 1 then PROk z o rest
    else PROk z o (ROne z o (cnt - 1) :: rest)
  | RTwo z1 o1 z2 o2 cnt :: rest =>
    if N.eqb cnt 0 then PRErr
    else if N.eqb cnt 1 then PROk z1 o1 (ROne z2 o2 1 :: rest)
    else PROk z1 o1 (ROne z2 o2 1 :: RTwo z1 o1 z2 o2 (cnt - 1) :: rest)
  end.

Definition bumpLK (ls : list LRun) : list LRun :=
  match popL ls with
  | PLErr => pushL1C ls 0 false 1
  | PLOk d b rest => pushL1C rest (d + 1) b 1
  end.

Definition push100LK (ls : list LRun) : list LRun :=
  match ls with
  | [] => [LOne 0 false 1]
  | _ => pushL1C ls 0 true 1
  end.

Definition push0RK (rs : list RRun) (k : N) : list RRun :=
  match popR rs with
  | PRErr => rs
  | PROk z o rest => pushR1C rest (z + k) o 1
  end.

Definition push1RK (rs : list RRun) : list RRun :=
  match popR rs with
  | PRErr => pushR1C rs 0 0 1
  | PROk z o rest =>
    if N.eqb z 0 then pushR1C rest 0 (o + 1) 1
    else pushR1C (pushR1C rest (z - 1) o 1) 0 0 1
  end.

Definition stepAK (ls : list LRun) (rs : list RRun) : StepRes :=
  match rs with
  | [] => SROk mCL ls [ROne 0 1 1]
  | _ =>
    match popR rs with
    | PRErr => SRErr
    | PROk z o r1 =>
      if N.eqb z 0 then
        let r2 := if N.eqb o 0 then push0RK r1 1 else pushR1C r1 0 (o - 1) 1 in
        SROk mER ls r2
      else if N.eqb z 1 then
        if N.eqb o 0 then SROk mAR00 ls r1 else SRHalted
      else if N.eqb z 2 then
        let l1 := pushL1C ls 0 false 1 in
        let r2 := if N.eqb o 0 then push0RK r1 1 else pushR1C r1 0 (o - 1) 1 in
        SROk mDR l1 r2
      else
        let r2 := push1RK (push1RK (pushR1C r1 (z - 3) o 1)) in
        SROk mCL ls r2
    end
  end.

Definition sweepK (isE : bool) (d : N) (b : bool) (ls : list LRun) (rs : list RRun) : StepRes :=
  let r1 := push0RK rs (d + 1) in
  let finE := if N.eqb (N.modulo d 2) 0 then isE else negb isE in
  if finE then
    let l1 := if b then pushL1C ls 0 false 1 else bumpLK ls in
    SROk mAR l1 r1
  else
    SROk (if b then mAR00 else mAR0) ls r1.

Definition stepSingleRLEK (m : SegMode) (ls : list LRun) (rs : list RRun) : StepRes :=
  match m with
  | mAR => stepAK (bumpLK ls) rs
  | mAR0 => stepAK (pushL1C ls 0 false 1) rs
  | mAR00 => stepAK (push100LK ls) rs
  | mCL =>
    match ls with
    | [] => SROk mCL [] (push1RK rs)
    | _ => SROk mDR ls rs
    end
  | mDL =>
    match popL ls with
    | PLErr => SROk mAR (pushL1C ls 0 false 1) rs
    | PLOk d b l1 => sweepK false d b l1 rs
    end
  | mEL =>
    match popL ls with
    | PLErr => SROk mAR0 ls rs
    | PLOk d b l1 => sweepK true d b l1 rs
    end
  | mDR =>
    match popR rs with
    | PRErr => SROk mAR (bumpLK ls) rs
    | PROk z o r1 =>
      if N.eqb z 0 then
        let r2 := if N.eqb o 0 then push0RK r1 2 else pushR1C r1 1 (o - 1) 1 in
        SROk mEL ls r2
      else
        SROk mAR (bumpLK ls) (pushR1C r1 (z - 1) o 1)
    end
  | mER =>
    match popR rs with
    | PRErr => SROk mAR0 ls rs
    | PROk z o r1 =>
      if N.eqb z 0 then
        let r2 := if N.eqb o 0 then push0RK r1 2 else pushR1C r1 1 (o - 1) 1 in
        SROk mDL ls r2
      else
        SROk mAR0 ls (pushR1C r1 (z - 1) o 1)
    end
  end.

Definition tryELBulkK (ls : list LRun) (rs : list RRun) : StepRes :=
  match popR rs with
  | PROk rz ro r_rest =>
    if N.eqb rz 1 && N.eqb ro 0 then
      match popL ls with
      | PLOk d0 false (blk :: l_rest) =>
        if N.leb 2 d0 && N.eqb (N.modulo d0 2) 0 then
          match blk with
          | LOne bd false bk =>
            if N.eqb bd (d0 - 2) && N.leb 1 bk then
              SROk mEL (pushL1C l_rest d0 false 1) (pushR1C (pushR1C r_rest bd 0 bk) 1 0 1)
            else stepSingleRLEK mEL ls rs
          | LTwo bd1 false bd2 false bk =>
            if N.eqb d0 4 && N.eqb bd1 0 && N.eqb bd2 2 && N.leb 1 bk then
              SROk mEL (pushL1C l_rest 4 false 1) (pushR1C (pushR2 r_rest 0 0 2 0 bk) 1 0 1)
            else if N.eqb d0 2 && N.eqb bd1 2 && N.eqb bd2 0 && N.leb 1 bk then
              SROk mEL (pushL1C l_rest 2 false 1) (pushR1C (pushR2 r_rest 2 0 0 0 bk) 1 0 1)
            else if N.eqb d0 2 && N.eqb bd1 0 && N.eqb bd2 2 && N.leb 2 bk then
              SROk mEL (pushL1C (pushL1C l_rest 2 false 1) 2 false 1)
                (pushR1C (pushR2 (pushR1C r_rest 0 0 1) 2 0 0 0 (bk - 1)) 1 0 1)
            else if N.eqb d0 4 && N.eqb bd1 2 && N.eqb bd2 0 && N.leb 2 bk then
              SROk mEL (pushL1C (pushL1C l_rest 0 false 1) 4 false 1)
                (pushR1C (pushR2 (pushR1C r_rest 2 0 1) 0 0 2 0 (bk - 1)) 1 0 1)
            else stepSingleRLEK mEL ls rs
          | _ => stepSingleRLEK mEL ls rs
          end
        else stepSingleRLEK mEL ls rs
      | _ => stepSingleRLEK mEL ls rs
      end
    else stepSingleRLEK mEL ls rs
  | PRErr => stepSingleRLEK mEL ls rs
  end.

Definition stepRLEK (m : SegMode) (ls : list LRun) (rs : list RRun) : StepRes :=
  match m with
  | mAR0 =>
    match rs with
    | ROne z o k :: rest =>
      if negb (N.eqb o 0) then stepSingleRLEK mAR0 ls rs
      else if N.eqb z 0 && N.leb 1 k then
        SROk mAR0 (pushL1C ls 0 false k) rest
      else if N.eqb z 2 && N.eqb k 1 then
        match rest with
        | RTwo z1 o1 z2 o2 k2 :: rest2 =>
          if N.eqb z1 0 && N.eqb o1 0 && N.eqb z2 2 && N.eqb o2 0 && N.leb 1 k2 then
            SROk mAR0 (pushL2 ls 2 false 0 false k2) (pushR1C rest2 2 0 1)
          else stepSingleRLEK mAR0 ls rs
        | _ => stepSingleRLEK mAR0 ls rs
        end
      else if N.eqb z 4 && N.leb 1 k then
        match popL ls with
        | PLOk d b l1 =>
          let l2 := pushL1C l1 (d + 2) b 1 in
          let l3 := if N.eqb k 1 then l2 else pushL1C l2 4 false (k - 1) in
          SROk mAR0 (pushL1C l3 2 false 1) rest
        | PLErr => stepSingleRLEK mAR0 ls rs
        end
      else if N.eqb z 2 && N.leb 2 k then
        let l1 := pushL1C ls 0 false 1 in
        let l2 := if N.eqb k 2 then l1 else pushL1C l1 2 false (k - 2) in
        SROk mDR (pushL1C l2 0 false 1) (pushR1C rest 3 0 1)
      else stepSingleRLEK mAR0 ls rs
    | RTwo z1 o1 z2 o2 k :: rest =>
      if negb (N.eqb o1 0 && N.eqb o2 0) then stepSingleRLEK mAR0 ls rs
      else if N.eqb z1 2 && N.eqb z2 0 && N.leb 1 k then
        SROk mAR0 (pushL2 ls 2 false 0 false k) rest
      else if N.eqb z1 0 && N.eqb z2 2 && N.leb 2 k then
        SROk mAR0 (pushL2 (pushL1C ls 0 false 1) 2 false 0 false (k - 1)) (pushR1C rest 2 0 1)
      else stepSingleRLEK mAR0 ls rs
    | [] => stepSingleRLEK mAR0 ls []
    end
  | mEL =>
    match rs with
    | ROne z1 o1 _ :: _ =>
      if N.eqb z1 1 && N.eqb o1 0 then tryELBulkK ls rs else stepSingleRLEK mEL ls rs
    | RTwo z1 o1 _ _ _ :: _ =>
      if N.eqb z1 1 && N.eqb o1 0 then tryELBulkK ls rs else stepSingleRLEK mEL ls rs
    | [] => stepSingleRLEK mEL ls []
    end
  | _ => stepSingleRLEK m ls rs
  end.

Definition stepBind (sr : StepRes) : StepRes :=
  match sr with
  | SROk m ls rs => stepRLEK m ls rs
  | SRHalted => SRHalted
  | SRErr => SRErr
  end.

Definition runRLEK (steps : N) (m : SegMode) (ls : list LRun) (rs : list RRun) : StepRes :=
  N.iter steps stepBind (SROk m ls rs).

Fixpoint splitOnesL (ls : list LRun) : list LRun :=
  match ls with
  | [] => []
  | LTwo d1 b1 d2 b2 c :: rest =>
    if N.eqb c 1 then LOne d1 b1 1 :: LOne d2 b2 1 :: splitOnesL rest
    else LTwo d1 b1 d2 b2 c :: splitOnesL rest
  | r :: rest => r :: splitOnesL rest
  end.

Definition mergeConsL (r : LRun) (ls : list LRun) : list LRun :=
  match ls with
  | [] => [r]
  | h :: rest =>
    match r, h with
    | LOne d1 b1 c1, LOne d2 b2 c2 =>
      if N.eqb d1 d2 && Bool.eqb b1 b2 then LOne d1 b1 (c1 + c2) :: rest
      else r :: h :: rest
    | LTwo d1 b1 d2 b2 c1, LTwo d1' b1' d2' b2' c2 =>
      if N.eqb d1 d1' && Bool.eqb b1 b1' && N.eqb d2 d2' && Bool.eqb b2 b2' then
        LTwo d1 b1 d2 b2 (c1 + c2) :: rest
      else r :: h :: rest
    | _, _ => r :: h :: rest
    end
  end.

Fixpoint mergeAdjL (ls : list LRun) : list LRun :=
  match ls with
  | [] => []
  | r :: rest => mergeConsL r (mergeAdjL rest)
  end.

Definition normL (ls : list LRun) : list LRun := mergeAdjL (splitOnesL ls).

Fixpoint peelRun (d : N) (b : bool) (ls : list LRun) (k : N) : option (list LRun) :=
  if N.eqb k 0 then Some ls else
  match ls with
  | [] => None
  | LOne d1 b1 cnt :: rest =>
    if N.eqb d1 d && Bool.eqb b1 b && N.leb 1 cnt then
      if N.leb k cnt then
        let rem := cnt - k in
        if N.eqb rem 0 then Some rest else Some (LOne d1 b1 rem :: rest)
      else peelRun d b rest (k - cnt)
    else None
  | LTwo d1 b1 d2 b2 cnt :: rest =>
    if N.eqb d1 d && Bool.eqb b1 b && N.leb 1 cnt && N.eqb k 1 then
      if N.eqb cnt 1 then Some (LOne d2 b2 1 :: rest)
      else Some (LOne d2 b2 1 :: LTwo d1 b1 d2 b2 (cnt - 1) :: rest)
    else None
  end.

Fixpoint peelW (w : list bool) (ls : list LRun) : option (list LRun) :=
  match w with
  | [] => Some ls
  | bit :: bs =>
    match peelRun (if bit then 2 else 0) false ls 1 with
    | None => None
    | Some l1 => peelW bs l1
    end
  end.

Fixpoint pushW (w : list bool) (ls : list LRun) : list LRun :=
  match w with
  | [] => ls
  | bit :: bs => pushL1 (pushW bs ls) (if bit then 2 else 0) false 1
  end.

Definition scIs0 (c : SymCnt) : bool := match c with SCConst a => N.eqb a 0 | _ => false end.
Definition scIs1 (c : SymCnt) : bool := match c with SCConst a => N.eqb a 1 | _ => false end.
Definition scIs2 (c : SymCnt) : bool := match c with SCConst a => N.eqb a 2 | _ => false end.
Definition scBase (c : SymCnt) : N := match c with SCConst a | SCInc a _ | SCDec a _ => a end.

Definition scSub (c : SymCnt) (k : N) : SymCnt :=
  match c with
  | SCConst a => SCConst (a - k)
  | SCInc a d => SCInc (a - k) d
  | SCDec a d => SCDec (a - k) d
  end.

Definition scAdd (c1 c2 : SymCnt) : option SymCnt :=
  match c1, c2 with
  | SCConst a1, SCConst a2 => Some (SCConst (a1 + a2))
  | SCConst a1, SCInc a2 d2 => Some (SCInc (a1 + a2) d2)
  | SCInc a1 d1, SCConst a2 => Some (SCInc (a1 + a2) d1)
  | SCInc a1 d1, SCInc a2 d2 => Some (SCInc (a1 + a2) (d1 + d2))
  | SCConst a1, SCDec a2 d2 => Some (SCDec (a1 + a2) d2)
  | SCDec a1 d1, SCConst a2 => Some (SCDec (a1 + a2) d1)
  | SCDec a1 d1, SCDec a2 d2 => Some (SCDec (a1 + a2) (d1 + d2))
  | _, _ => None
  end.

Definition foldSLStep (next : list SLRun -> option (list SLRun)) (ls : list SLRun) : option (list SLRun) :=
  match ls with
  | SLOne d1 b1 c1 :: SLOne d2 b2 c2 :: rest =>
    if N.eqb d1 d2 && Bool.eqb b1 b2 then
      match scAdd c1 c2 with
      | None => None
      | Some s => next (SLOne d1 b1 s :: rest)
      end
    else if scIs1 c1 && scIs1 c2 then
      match rest with
      | SLTwo td1 tb1 td2 tb2 tc :: rest2 =>
        if N.eqb td1 d1 && Bool.eqb tb1 b1 && N.eqb td2 d2 && Bool.eqb tb2 b2 then
          match scAdd tc (SCConst 1) with
          | None => None
          | Some s => next (SLTwo td1 tb1 td2 tb2 s :: rest2)
          end
        else Some ls
      | SLOne d3 b3 c3 :: SLOne d4 b4 c4 :: rest2 =>
        if scIs1 c3 && scIs1 c4 &&
           N.eqb d1 d3 && Bool.eqb b1 b3 && N.eqb d2 d4 && Bool.eqb b2 b4 then
          next (SLTwo d1 b1 d2 b2 (SCConst 2) :: rest2)
        else Some ls
      | _ => Some ls
      end
    else Some ls
  | SLTwo d1 b1 d2 b2 c1 :: SLTwo d1' b1' d2' b2' c2 :: rest =>
    if N.eqb d1 d1' && Bool.eqb b1 b1' && N.eqb d2 d2' && Bool.eqb b2 b2' then
      match scAdd c1 c2 with
      | None => None
      | Some s => next (SLTwo d1 b1 d2 b2 s :: rest)
      end
    else Some ls
  | _ => Some ls
  end.

Definition foldSL3 (ls : list SLRun) : option (list SLRun) :=
  foldSLStep (foldSLStep (foldSLStep (@Some _))) ls.

Definition foldSRStep (next : list SRRun -> option (list SRRun)) (rs : list SRRun) : option (list SRRun) :=
  match rs with
  | SROne z1 o1 c1 :: SROne z2 o2 c2 :: rest =>
    if N.eqb z1 z2 && N.eqb o1 o2 then
      match scAdd c1 c2 with
      | None => None
      | Some s => next (SROne z1 o1 s :: rest)
      end
    else if scIs1 c1 && scIs1 c2 then
      match rest with
      | SRTwo tz1 to1 tz2 to2 tc :: rest2 =>
        if N.eqb tz1 z1 && N.eqb to1 o1 && N.eqb tz2 z2 && N.eqb to2 o2 then
          match scAdd tc (SCConst 1) with
          | None => None
          | Some s => next (SRTwo tz1 to1 tz2 to2 s :: rest2)
          end
        else Some rs
      | SROne z3 o3 c3 :: SROne z4 o4 c4 :: rest2 =>
        if scIs1 c3 && scIs1 c4 &&
           N.eqb z1 z3 && N.eqb o1 o3 && N.eqb z2 z4 && N.eqb o2 o4 then
          next (SRTwo z1 o1 z2 o2 (SCConst 2) :: rest2)
        else Some rs
      | _ => Some rs
      end
    else Some rs
  | SRTwo z1 o1 z2 o2 c1 :: SRTwo z1' o1' z2' o2' c2 :: rest =>
    if N.eqb z1 z1' && N.eqb o1 o1' && N.eqb z2 z2' && N.eqb o2 o2' then
      match scAdd c1 c2 with
      | None => None
      | Some s => next (SRTwo z1 o1 z2 o2 s :: rest)
      end
    else Some rs
  | _ => Some rs
  end.

Definition foldSR3 (rs : list SRRun) : option (list SRRun) :=
  foldSRStep (foldSRStep (foldSRStep (@Some _))) rs.

Definition pushSL1 (ls : list SLRun) (d : N) (b : bool) (c : SymCnt) : option (list SLRun) :=
  if scIs0 c then Some ls else foldSL3 (SLOne d b c :: ls).

Definition pushSL2 (ls : list SLRun) (d1 : N) (b1 : bool) (d2 : N) (b2 : bool) (c : SymCnt) : option (list SLRun) :=
  if scIs0 c then Some ls else foldSL3 (SLTwo d1 b1 d2 b2 c :: ls).

Definition pushSR1 (rs : list SRRun) (z o : N) (c : SymCnt) : option (list SRRun) :=
  if scIs0 c then Some rs else foldSR3 (SROne z o c :: rs).

Definition pushSR2 (rs : list SRRun) (z1 o1 z2 o2 : N) (c : SymCnt) : option (list SRRun) :=
  if scIs0 c then Some rs else foldSR3 (SRTwo z1 o1 z2 o2 c :: rs).

Definition popSL (ls : list SLRun) : PopSLRes :=
  match ls with
  | [] => PSLErr
  | SLOne d b c :: rest =>
    if scIs1 c then PSLOk d b rest
    else if N.leb 2 (scBase c) then PSLOk d b (SLOne d b (scSub c 1) :: rest)
    else PSLErr
  | SLTwo d1 b1 d2 b2 c :: rest =>
    if scIs1 c then
      match pushSL1 rest d2 b2 (SCConst 1) with
      | None => PSLErr
      | Some rest' => PSLOk d1 b1 rest'
      end
    else if N.leb 2 (scBase c) then
      PSLOk d1 b1 (SLOne d2 b2 (SCConst 1) :: SLTwo d1 b1 d2 b2 (scSub c 1) :: rest)
    else PSLErr
  end.

Definition popSR (rs : list SRRun) : PopSRRes :=
  match rs with
  | [] => PSRErr
  | SROne z o c :: rest =>
    if scIs1 c then PSROk z o rest
    else if N.leb 2 (scBase c) then PSROk z o (SROne z o (scSub c 1) :: rest)
    else PSRErr
  | SRTwo z1 o1 z2 o2 c :: rest =>
    if scIs1 c then
      match pushSR1 rest z2 o2 (SCConst 1) with
      | None => PSRErr
      | Some rest' => PSROk z1 o1 rest'
      end
    else if N.leb 2 (scBase c) then
      PSROk z1 o1 (SROne z2 o2 (SCConst 1) :: SRTwo z1 o1 z2 o2 (scSub c 1) :: rest)
    else PSRErr
  end.

Fixpoint splitOnesSL (ls : list SLRun) : list SLRun :=
  match ls with
  | [] => []
  | SLTwo d1 b1 d2 b2 c :: rest =>
    if scIs1 c then SLOne d1 b1 (SCConst 1) :: SLOne d2 b2 (SCConst 1) :: splitOnesSL rest
    else SLTwo d1 b1 d2 b2 c :: splitOnesSL rest
  | r :: rest => r :: splitOnesSL rest
  end.

Definition mergeConsSL (r : SLRun) (ls : list SLRun) : option (list SLRun) :=
  match ls with
  | [] => Some [r]
  | h :: rest =>
    match r, h with
    | SLOne d1 b1 c1, SLOne d2 b2 c2 =>
      if N.eqb d1 d2 && Bool.eqb b1 b2 then
        match scAdd c1 c2 with
        | None => None
        | Some s => Some (SLOne d1 b1 s :: rest)
        end
      else Some (r :: h :: rest)
    | SLTwo d1 b1 d2 b2 c1, SLTwo d1' b1' d2' b2' c2 =>
      if N.eqb d1 d1' && Bool.eqb b1 b1' && N.eqb d2 d2' && Bool.eqb b2 b2' then
        match scAdd c1 c2 with
        | None => None
        | Some s => Some (SLTwo d1 b1 d2 b2 s :: rest)
        end
      else Some (r :: h :: rest)
    | _, _ => Some (r :: h :: rest)
    end
  end.

Fixpoint mergeAdjSL (ls : list SLRun) : option (list SLRun) :=
  match ls with
  | [] => Some []
  | r :: rest =>
    match mergeAdjSL rest with
    | None => None
    | Some rs => mergeConsSL r rs
    end
  end.

Definition normSL (ls : list SLRun) : option (list SLRun) := mergeAdjSL (splitOnesSL ls).

Definition sBumpLK (ls : list SLRun) : option (list SLRun) :=
  match ls with
  | [] => pushSL1 [] 0 false (SCConst 1)
  | _ =>
    match popSL ls with
    | PSLErr => None
    | PSLOk d b rest => pushSL1 rest (d + 1) b (SCConst 1)
    end
  end.

Definition sPush100LK (ls : list SLRun) : option (list SLRun) :=
  match ls with
  | [] => pushSL1 [] 0 false (SCConst 1)
  | _ => pushSL1 ls 0 true (SCConst 1)
  end.

Definition sPush0RK (rs : list SRRun) (k : N) : option (list SRRun) :=
  match popSR rs with
  | PSRErr => None
  | PSROk z o rest => pushSR1 rest (z + k) o (SCConst 1)
  end.

Definition sPush1RK (rs : list SRRun) : option (list SRRun) :=
  match popSR rs with
  | PSRErr => None
  | PSROk z o rest =>
    if N.eqb z 0 then pushSR1 rest 0 (o + 1) (SCConst 1)
    else
      match pushSR1 rest (z - 1) o (SCConst 1) with
      | None => None
      | Some r1 => pushSR1 r1 0 0 (SCConst 1)
      end
  end.

Definition sStepAK (ls : list SLRun) (rs : list SRRun) : SymState :=
  match popSR rs with
  | PSRErr => SSErr
  | PSROk z o r1 =>
    if N.eqb z 0 then
      let oR := if N.eqb o 0 then sPush0RK r1 1 else pushSR1 r1 0 (o - 1) (SCConst 1) in
      match oR with None => SSErr | Some r2 => SSOk mER ls r2 end
    else if N.eqb z 1 then
      if N.eqb o 0 then SSOk mAR00 ls r1 else SSErr
    else if N.eqb z 2 then
      match pushSL1 ls 0 false (SCConst 1) with
      | None => SSErr
      | Some l1 =>
        let oR := if N.eqb o 0 then sPush0RK r1 1 else pushSR1 r1 0 (o - 1) (SCConst 1) in
        match oR with None => SSErr | Some r2 => SSOk mDR l1 r2 end
      end
    else
      match pushSR1 r1 (z - 3) o (SCConst 1) with
      | None => SSErr
      | Some r2 =>
        match sPush1RK r2 with
        | None => SSErr
        | Some r3 =>
          match sPush1RK r3 with
          | None => SSErr
          | Some r4 => SSOk mCL ls r4
          end
        end
      end
  end.

Definition sSweepK (isE : bool) (d : N) (b : bool) (ls : list SLRun) (rs : list SRRun) : SymState :=
  match sPush0RK rs (d + 1) with
  | None => SSErr
  | Some r1 =>
    let finE := if N.eqb (N.modulo d 2) 0 then isE else negb isE in
    if finE then
      let oL := if b then pushSL1 ls 0 false (SCConst 1) else sBumpLK ls in
      match oL with None => SSErr | Some l1 => SSOk mAR l1 r1 end
    else
      SSOk (if b then mAR00 else mAR0) ls r1
  end.

Definition symStepSingleK (m : SegMode) (ls : list SLRun) (rs : list SRRun) : SymState :=
  match m with
  | mAR => match sBumpLK ls with None => SSErr | Some l1 => sStepAK l1 rs end
  | mAR0 => match pushSL1 ls 0 false (SCConst 1) with None => SSErr | Some l1 => sStepAK l1 rs end
  | mAR00 => match sPush100LK ls with None => SSErr | Some l1 => sStepAK l1 rs end
  | mCL => match ls with [] => SSErr | _ => SSOk mDR ls rs end
  | mDL => match popSL ls with PSLErr => SSErr | PSLOk d b l1 => sSweepK false d b l1 rs end
  | mEL => match popSL ls with PSLErr => SSErr | PSLOk d b l1 => sSweepK true d b l1 rs end
  | mDR =>
    match popSR rs with
    | PSRErr => SSErr
    | PSROk z o r1 =>
      if N.eqb z 0 then
        let oR := if N.eqb o 0 then sPush0RK r1 2 else pushSR1 r1 1 (o - 1) (SCConst 1) in
        match oR with None => SSErr | Some r2 => SSOk mEL ls r2 end
      else
        match pushSR1 r1 (z - 1) o (SCConst 1), sBumpLK ls with
        | Some r2, Some l1 => SSOk mAR l1 r2
        | _, _ => SSErr
        end
    end
  | mER =>
    match popSR rs with
    | PSRErr => SSErr
    | PSROk z o r1 =>
      if N.eqb z 0 then
        let oR := if N.eqb o 0 then sPush0RK r1 2 else pushSR1 r1 1 (o - 1) (SCConst 1) in
        match oR with None => SSErr | Some r2 => SSOk mDL ls r2 end
      else
        match pushSR1 r1 (z - 1) o (SCConst 1) with
        | None => SSErr
        | Some r2 => SSOk mAR0 ls r2
        end
    end
  end.

Definition symStepRLEK (m : SegMode) (ls : list SLRun) (rs : list SRRun) : SymState :=
  match rs with
  | [] => SSErr
  | _ =>
    match m with
    | mAR0 =>
      match rs with
      | SROne z o c :: rest =>
        if N.eqb z 0 && N.eqb o 0 && N.leb 1 (scBase c) then
          match pushSL1 ls 0 false c with Some l1 => SSOk mAR0 l1 rest | None => SSErr end
        else if N.eqb z 2 && N.eqb o 0 && scIs1 c then
          match rest with
          | SRTwo z1 o1 z2 o2 c2 :: rest2 =>
            if N.eqb z1 0 && N.eqb o1 0 && N.eqb z2 2 && N.eqb o2 0 && N.leb 1 (scBase c2) then
              match pushSL2 ls 2 false 0 false c2, pushSR1 rest2 2 0 (SCConst 1) with
              | Some l1, Some r1 => SSOk mAR0 l1 r1
              | _, _ => SSErr
              end
            else symStepSingleK mAR0 ls rs
          | _ => symStepSingleK mAR0 ls rs
          end
        else if N.eqb z 4 && N.eqb o 0 && (scIs1 c || N.leb 2 (scBase c)) then
          match popSL ls with
          | PSLOk d b l1 =>
            match pushSL1 l1 (d + 2) b (SCConst 1) with
            | None => SSErr
            | Some l2 =>
              let oL3 := if scIs1 c then Some l2 else pushSL1 l2 4 false (scSub c 1) in
              match oL3 with
              | None => SSErr
              | Some l3 =>
                match pushSL1 l3 2 false (SCConst 1) with
                | None => SSErr
                | Some l4 => SSOk mAR0 l4 rest
                end
              end
            end
          | PSLErr => symStepSingleK mAR0 ls rs
          end
        else if N.eqb z 2 && N.eqb o 0 && (scIs2 c || N.leb 3 (scBase c)) then
          match pushSL1 ls 0 false (SCConst 1) with
          | None => SSErr
          | Some l1 =>
            let oL2 := if scIs2 c then Some l1 else pushSL1 l1 2 false (scSub c 2) in
            match oL2 with
            | None => SSErr
            | Some l2 =>
              match pushSL1 l2 0 false (SCConst 1), pushSR1 rest 3 0 (SCConst 1) with
              | Some l3, Some r1 => SSOk mDR l3 r1
              | _, _ => SSErr
              end
            end
          end
        else symStepSingleK mAR0 ls rs
      | SRTwo z1 o1 z2 o2 c :: rest =>
        if N.eqb z1 2 && N.eqb o1 0 && N.eqb z2 0 && N.eqb o2 0 && N.leb 1 (scBase c) then
          match pushSL2 ls 2 false 0 false c with Some l1 => SSOk mAR0 l1 rest | None => SSErr end
        else if N.eqb z1 0 && N.eqb o1 0 && N.eqb z2 2 && N.eqb o2 0 && N.leb 2 (scBase c) then
          match pushSL1 ls 0 false (SCConst 1) with
          | None => SSErr
          | Some l1 =>
            match pushSL2 l1 2 false 0 false (scSub c 1), pushSR1 rest 2 0 (SCConst 1) with
            | Some l2, Some r1 => SSOk mAR0 l2 r1
            | _, _ => SSErr
            end
          end
        else symStepSingleK mAR0 ls rs
      | [] => SSErr
      end
    | mEL =>
      match popSR rs with
      | PSROk rz ro r_rest =>
        if N.eqb rz 1 && N.eqb ro 0 then
          match popSL ls with
          | PSLOk d0 false (blk :: l_rest) =>
            if N.leb 2 d0 && N.eqb (N.modulo d0 2) 0 then
              match blk with
              | SLOne bd false bc =>
                if N.eqb bd (d0 - 2) && N.leb 1 (scBase bc) then
                  match pushSL1 l_rest d0 false (SCConst 1), pushSR1 r_rest bd 0 bc with
                  | Some l1, Some r1 =>
                    match pushSR1 r1 1 0 (SCConst 1) with
                    | Some r2 => SSOk mEL l1 r2
                    | None => SSErr
                    end
                  | _, _ => SSErr
                  end
                else symStepSingleK mEL ls rs
              | SLTwo bd1 false bd2 false bc =>
                if N.eqb d0 4 && N.eqb bd1 0 && N.eqb bd2 2 && N.leb 1 (scBase bc) then
                  match pushSL1 l_rest 4 false (SCConst 1), pushSR2 r_rest 0 0 2 0 bc with
                  | Some l1, Some r1 =>
                    match pushSR1 r1 1 0 (SCConst 1) with
                    | Some r2 => SSOk mEL l1 r2
                    | None => SSErr
                    end
                  | _, _ => SSErr
                  end
                else if N.eqb d0 2 && N.eqb bd1 2 && N.eqb bd2 0 && N.leb 1 (scBase bc) then
                  match pushSL1 l_rest 2 false (SCConst 1), pushSR2 r_rest 2 0 0 0 bc with
                  | Some l1, Some r1 =>
                    match pushSR1 r1 1 0 (SCConst 1) with
                    | Some r2 => SSOk mEL l1 r2
                    | None => SSErr
                    end
                  | _, _ => SSErr
                  end
                else if N.eqb d0 2 && N.eqb bd1 0 && N.eqb bd2 2 && N.leb 2 (scBase bc) then
                  match pushSL1 l_rest 2 false (SCConst 1) with
                  | None => SSErr
                  | Some l1 =>
                    match pushSL1 l1 2 false (SCConst 1), pushSR1 r_rest 0 0 (SCConst 1) with
                    | Some l2, Some r1 =>
                      match pushSR2 r1 2 0 0 0 (scSub bc 1) with
                      | None => SSErr
                      | Some r2 =>
                        match pushSR1 r2 1 0 (SCConst 1) with
                        | Some r3 => SSOk mEL l2 r3
                        | None => SSErr
                        end
                      end
                    | _, _ => SSErr
                    end
                  end
                else if N.eqb d0 4 && N.eqb bd1 2 && N.eqb bd2 0 && N.leb 2 (scBase bc) then
                  match pushSL1 l_rest 0 false (SCConst 1) with
                  | None => SSErr
                  | Some l1 =>
                    match pushSL1 l1 4 false (SCConst 1), pushSR1 r_rest 2 0 (SCConst 1) with
                    | Some l2, Some r1 =>
                      match pushSR2 r1 0 0 2 0 (scSub bc 1) with
                      | None => SSErr
                      | Some r2 =>
                        match pushSR1 r2 1 0 (SCConst 1) with
                        | Some r3 => SSOk mEL l2 r3
                        | None => SSErr
                        end
                      end
                    | _, _ => SSErr
                    end
                  end
                else symStepSingleK mEL ls rs
              | _ => symStepSingleK mEL ls rs
              end
            else symStepSingleK mEL ls rs
          | _ => symStepSingleK mEL ls rs
          end
        else symStepSingleK mEL ls rs
      | PSRErr => symStepSingleK mEL ls rs
      end
    | _ => symStepSingleK m ls rs
    end
  end.

Definition symStepBind (st : SymState) : SymState :=
  match st with
  | SSOk m ls rs => symStepRLEK m ls rs
  | SSErr => SSErr
  end.

Definition runSymRLEK (steps : N) (m : SegMode) (ls : list SLRun) (rs : list SRRun) : SymState :=
  N.iter steps symStepBind (SSOk m ls rs).

Definition prePostStep (pp : N * N) : N * N :=
  let '(pr, po) := pp in (2 * pr + po + 2, 2 * pr + 3 * po + 2).

Definition prePostK (k : N) : N * N :=
  N.iter k prePostStep (2, 2).

Fixpoint carryWFuel (w : list bool) (fuel : N) : CarryRes :=
  match w with
  | [] => CRErr
  | false :: u => CROk (true :: u) 1
  | [true] => CRErr
  | true :: true :: u => CROk (false :: false :: u) 2
  | true :: false :: u =>
    if N.eqb fuel 0 then CRErr
    else
      match carryWFuel u (fuel - 1) with
      | CRErr => CRErr
      | CROk u' e => CROk (false :: true :: u') e
      end
  end.

Definition buildSymOne (P : N) (r : LRun) (sl : SlopeSpec) (rest : SymBuildRes) : SymBuildRes :=
  match rest with
  | SBErr => SBErr
  | SBOk sL sTarg bFin =>
    let cnt := match r with LOne _ _ c | LTwo _ _ _ _ c => c end in
    if N.eqb cnt 0 then SBErr
    else
      let mkS := fun c => match r with LOne d b _ => SLOne d b c | LTwo d1 b1 d2 b2 _ => SLTwo d1 b1 d2 b2 c end in
      let mkC := fun c => match r with LOne d b _ => LOne d b c | LTwo d1 b1 d2 b2 _ => LTwo d1 b1 d2 b2 c end in
      match sl with
      | SlZ => SBOk (mkS (SCConst cnt) :: sL) (mkS (SCConst cnt) :: sTarg) (r :: bFin)
      | SlP d => SBOk (mkS (SCInc cnt d) :: sL) (mkS (SCInc (cnt + d) d) :: sTarg) (mkC (cnt + P * d) :: bFin)
      | SlN d =>
        let pd := P * d in
        if N.leb (pd + 1) cnt then
          let finc := cnt - pd in
          SBOk (mkS (SCDec (finc + d) d) :: sL) (mkS (SCDec finc d) :: sTarg) (mkC finc :: bFin)
        else SBErr
      end
  end.

Fixpoint buildSym (P : N) (b0 : list LRun) (slopes : list SlopeSpec) : SymBuildRes :=
  match b0, slopes with
  | [], [] => SBOk [] [] []
  | r :: rs, sl :: sls => buildSymOne P r sl (buildSym P rs sls)
  | _, _ => SBErr
  end.

Definition applyJumpK (ls : list LRun) (p m ssteps : N) (w : list bool) (slopes : list SlopeSpec) : option (list LRun) :=
  if N.eqb m 0 then None
  else
    let k := m - 1 in
    let '(pre, post) := prePostK k in
    match carryWFuel w post with
    | CRErr => None
    | CROk w_out extra =>
      let P := pre + post + extra in
      match peelRun 0 true ls p with
      | None => None
      | Some l1 =>
        match peelRun 0 false l1 (2 * m) with
        | None => None
        | Some l2 =>
          match peelW w l2 with
          | None => None
          | Some l3 =>
            match peelRun 0 false l3 1 with
            | None => None
            | Some l4 =>
              let b0 := normL l4 in
              match buildSym P b0 slopes with
              | SBErr => None
              | SBOk sL_body sTarg b_fin =>
                match pushSL1 sL_body 2 false (SCConst 1) with
                | None => None
                | Some sL0 =>
                  match runSymRLEK ssteps mEL sL0 [SROne 1 0 (SCConst 1)] with
                  | SSOk mAR0 sL_end [] =>
                    match normSL sL_end with
                    | None => None
                    | Some sL_norm =>
                      if beqListSLRun sL_norm sTarg then
                        let l' := pushL1 b_fin 0 false 1 in
                        let l'' := pushW w_out l' in
                        let l''' := pushL1 l'' 0 false (2 * m) in
                        Some (pushL1 l''' 0 true p)
                      else None
                    end
                  | _ => None
                  end
                end
              end
            end
          end
        end
      end
    end.

Definition execOpK (op : Op) (ls : list LRun) : option (list LRun) :=
  match op with
  | OpRun steps =>
    match runRLEK steps mAR0 ls [] with
    | SROk mAR0 ls' [] => Some ls'
    | _ => None
    end
  | OpJump p m ssteps w slopes => applyJumpK ls p m ssteps w slopes
  end.

Fixpoint execOpsK (ops : list Op) (ls : list LRun) : option (list LRun) :=
  match ops with
  | [] => Some ls
  | op :: rest =>
    match execOpK op ls with
    | None => None
    | Some ls' => execOpsK rest ls'
    end
  end.

Definition check_all_ops (ops : list Op) : bool :=
  match runRLEK 22 mCL [LOne 0 false 1] [ROne 0 1 1] with
  | SROk mAR0 l0 [] =>
    match execOpsK ops l0 with
    | None => false
    | Some l_fin =>
      match runRLEK 251 mAR0 l_fin [] with
      | SRHalted => true
      | _ => false
      end
    end
  | _ => false
  end.

Local Close Scope sym_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Arguments evalSegCfg : simpl never.
Arguments evalA : simpl never.

(* ========================================================================= *)
(* Section 2: Binary-N RLE Representation & Primitives Soundness             *)
(* ========================================================================= *)

Definition expandLRun (r : LRun) : list (nat * bool) :=
  match r with
  | LOne d b k => repeat (N.to_nat d, b) (N.to_nat k)
  | LTwo d1 b1 d2 b2 k => repPair (N.to_nat d1, b1) (N.to_nat d2, b2) (N.to_nat k)
  end.

Fixpoint expandL (ls : list LRun) : list (nat * bool) :=
  match ls with
  | [] => []
  | r :: rs => expandLRun r ++ expandL rs
  end.

Definition expandRRun (r : RRun) : list (nat * nat) :=
  match r with
  | ROne z o k => repeat (N.to_nat z, N.to_nat o) (N.to_nat k)
  | RTwo z1 o1 z2 o2 k => repPair (N.to_nat z1, N.to_nat o1) (N.to_nat z2, N.to_nat o2) (N.to_nat k)
  end.

Fixpoint expandR (rs : list RRun) : list (nat * nat) :=
  match rs with
  | [] => []
  | r :: rest => expandRRun r ++ expandR rest
  end.

Definition PosLRun (r : LRun) : Prop :=
  match r with
  | LOne _ _ c => 1 <= N.to_nat c
  | LTwo _ _ _ _ c => 1 <= N.to_nat c
  end.

Fixpoint PosL (ls : list LRun) : Prop :=
  match ls with
  | [] => True
  | r :: rs => PosLRun r /\ PosL rs
  end.

Definition PosRRun (r : RRun) : Prop :=
  match r with
  | ROne _ _ c => 1 <= N.to_nat c
  | RTwo _ _ _ _ c => 1 <= N.to_nat c
  end.

Fixpoint PosR (rs : list RRun) : Prop :=
  match rs with
  | [] => True
  | r :: rest => PosRRun r /\ PosR rest
  end.

Lemma N_mod2_eqb (d : N) :
  N.eqb (N.modulo d 2) 0 = Nat.eqb ((N.to_nat d) mod 2) 0.
Proof.
  assert (Hmod : N.to_nat (N.modulo d 2) = (N.to_nat d) mod 2).
  { apply N2Nat.inj_mod. }
  destruct (N.eqb (N.modulo d 2) 0) eqn:H1, (Nat.eqb ((N.to_nat d) mod 2) 0) eqn:H2; try reflexivity.
  - apply N.eqb_eq in H1. apply Nat.eqb_neq in H2. lia.
  - apply N.eqb_neq in H1. apply Nat.eqb_eq in H2. lia.
Qed.

Lemma N_iter_succ_r {X : Type} (n : N) (f : X -> X) (x : X) :
  N.iter (N.succ n) f x = N.iter n f (f x).
Proof.
  revert x. pattern n. apply N.peano_ind; clear n.
  - intros x. reflexivity.
  - intros n IH x. rewrite N.iter_succ, IH, N.iter_succ. reflexivity.
Qed.

Lemma bool_eqb_eq (x y : bool) : Bool.eqb x y = true -> x = y.
Proof. destruct x, y; simpl; congruence. Qed.

Lemma beqSC_iff (a b : SymCnt) : beqSC a b = true <-> a = b.
Proof.
  destruct a as [a1 | a1 d1 | a1 d1], b as [a2 | a2 d2 | a2 d2];
    simpl; split; intros H; try discriminate.
  - apply N.eqb_eq in H; subst; reflexivity.
  - injection H as ->; apply N.eqb_refl.
  - apply andb_true_iff in H as [Ha Hd]; apply N.eqb_eq in Ha; apply N.eqb_eq in Hd; subst; reflexivity.
  - injection H as -> ->; rewrite !N.eqb_refl; reflexivity.
  - apply andb_true_iff in H as [Ha Hd]; apply N.eqb_eq in Ha; apply N.eqb_eq in Hd; subst; reflexivity.
  - injection H as -> ->; rewrite !N.eqb_refl; reflexivity.
Qed.

Lemma beqSLRun_iff (a b : SLRun) : beqSLRun a b = true <-> a = b.
Proof.
  destruct a as [d1 b1 c1 | d1 b1 d2 b2 c1], b as [d1' b1' c2 | d1' b1' d2' b2' c2];
    simpl; split; intros H; try discriminate.
  - repeat rewrite andb_true_iff in H.
    destruct H as [[He1 He2] He3].
    apply N.eqb_eq in He1; apply bool_eqb_eq in He2; apply beqSC_iff in He3.
    subst; reflexivity.
  - injection H as -> -> ->.
    rewrite !N.eqb_refl, !Bool.eqb_reflx.
    simpl. apply beqSC_iff; reflexivity.
  - repeat rewrite andb_true_iff in H.
    destruct H as [[[[He1 He2] He3] He4] He5].
    apply N.eqb_eq in He1; apply bool_eqb_eq in He2;
    apply N.eqb_eq in He3; apply bool_eqb_eq in He4; apply beqSC_iff in He5.
    subst; reflexivity.
  - injection H as -> -> -> -> ->.
    rewrite !N.eqb_refl, !Bool.eqb_reflx.
    simpl. apply beqSC_iff; reflexivity.
Qed.

Lemma beqListSLRun_iff (xs ys : list SLRun) : beqListSLRun xs ys = true <-> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl; split; intros H;
    try reflexivity; try discriminate.
  - apply andb_true_iff in H as [H1 H2].
    apply beqSLRun_iff in H1; apply IH in H2; subst; reflexivity.
  - inversion H; subst.
    apply andb_true_iff; split; [apply beqSLRun_iff | apply IH]; reflexivity.
Qed.

Lemma expandL_nil_of_pos {ls : list LRun} (hPos : PosL ls) (h : expandL ls = []) : ls = [].
Proof.
  destruct ls as [|[d b c | d1 b1 d2 b2 c] rs]; [reflexivity | |];
    destruct hPos as [hr _]; simpl in hr, h;
    destruct (N.to_nat c) as [|c']; try lia; simpl in h; discriminate.
Qed.

Lemma expandL_eq_nil_iff {ls : list LRun} (hPos : PosL ls) : expandL ls = [] <-> ls = [].
Proof.
  split; [exact (expandL_nil_of_pos hPos) | intros ->; reflexivity].
Qed.

Lemma foldLStep_sound (next : list LRun -> list LRun)
    (hnext : forall xs, PosL xs -> expandL (next xs) = expandL xs /\ PosL (next xs))
    (ls : list LRun) (hPos : PosL ls) :
  expandL (foldLStep next ls) = expandL ls /\ PosL (foldLStep next ls).
Proof.
  destruct ls as [|[d1 b1 c1 | d1 b1 d2 b2 c1] rs]; [exact (conj eq_refl hPos) | |].
  - (* LOne :: rs *)
    destruct rs as [|[d2 b2 c2 | ? ? ? ? ?] rest]; try (exact (conj eq_refl hPos)).
    destruct hPos as [h1 [h2 hr]]; simpl in h1, h2.
    unfold foldLStep.
    destruct (N.eqb d1 d2 && Bool.eqb b1 b2) eqn:heq.
    + apply andb_true_iff in heq as [hd hb]; apply N.eqb_eq in hd; apply bool_eqb_eq in hb; subst.
      assert (hpos' : PosL (LOne d2 b2 (c1 + c2) :: rest)) by (simpl; split; [lia | exact hr]).
      destruct (hnext _ hpos') as [he hp]; split; [| exact hp].
      rewrite he; simpl. rewrite N2Nat.inj_add, repeat_add, <- app_assoc. reflexivity.
    + destruct (N.eqb c1 1 && N.eqb c2 1) eqn:hc12; [| exact (conj eq_refl (conj h1 (conj h2 hr)))].
      apply andb_true_iff in hc12 as [hc1 hc2]; apply N.eqb_eq in hc1; apply N.eqb_eq in hc2; subst.
      destruct rest as [|[d3 b3 c3 | td1 tb1 td2 tb2 tc] rest2].
      * exact (conj eq_refl (conj h1 (conj h2 hr))).
      * destruct rest2 as [|[d4 b4 c4 | ? ? ? ? ?] rest3];
          try (exact (conj eq_refl (conj h1 (conj h2 hr)))).
        destruct hr as [h3 [h4 hr3]].
        destruct (N.eqb c3 1 && N.eqb c4 1 &&
                  N.eqb d1 d3 && Bool.eqb b1 b3 && N.eqb d2 d4 && Bool.eqb b2 b4) eqn:hm;
          [| exact (conj eq_refl (conj h1 (conj h2 (conj h3 (conj h4 hr3)))))].
        repeat rewrite andb_true_iff in hm.
        destruct hm as [[[[[hc3 hc4] hd13] hb13] hd24] hb24].
        apply N.eqb_eq in hc3; apply N.eqb_eq in hc4;
        apply N.eqb_eq in hd13; apply bool_eqb_eq in hb13;
        apply N.eqb_eq in hd24; apply bool_eqb_eq in hb24; subst.
        assert (hpos' : PosL (LTwo d3 b3 d4 b4 2 :: rest3)) by (simpl; split; [lia | exact hr3]).
        destruct (hnext _ hpos') as [he hp]; split; [| exact hp].
        rewrite he; reflexivity.
      * destruct hr as [htc hr2]; simpl in htc.
        destruct (N.eqb td1 d1 && Bool.eqb tb1 b1 && N.eqb td2 d2 && Bool.eqb tb2 b2) eqn:hm;
          [| exact (conj eq_refl (conj h1 (conj h2 (conj htc hr2))))].
        repeat rewrite andb_true_iff in hm.
        destruct hm as [[[hd1 hb1] hd2] hb2].
        apply N.eqb_eq in hd1; apply bool_eqb_eq in hb1;
        apply N.eqb_eq in hd2; apply bool_eqb_eq in hb2; subst.
        assert (hpos' : PosL (LTwo d1 b1 d2 b2 (tc + 1) :: rest2)) by (simpl; split; [lia | exact hr2]).
        destruct (hnext _ hpos') as [he hp]; split; [| exact hp].
        rewrite he; simpl.
        replace (N.to_nat (tc + 1)) with (S (N.to_nat tc)) by lia.
        reflexivity.
  - (* LTwo :: rs *)
    destruct rs as [|[? ? ? | d1' b1' d2' b2' c2] rest]; try (exact (conj eq_refl hPos)).
    destruct hPos as [h1 [h2 hr]]; simpl in h1, h2.
    unfold foldLStep.
    destruct (N.eqb d1 d1' && Bool.eqb b1 b1' && N.eqb d2 d2' && Bool.eqb b2 b2') eqn:hm;
      [| exact (conj eq_refl (conj h1 (conj h2 hr)))].
    repeat rewrite andb_true_iff in hm.
    destruct hm as [[[hd1 hb1] hd2] hb2].
    apply N.eqb_eq in hd1; apply bool_eqb_eq in hb1;
    apply N.eqb_eq in hd2; apply bool_eqb_eq in hb2; subst.
    assert (hpos' : PosL (LTwo d1' b1' d2' b2' (c1 + c2) :: rest)) by (simpl; split; [lia | exact hr]).
    destruct (hnext _ hpos') as [he hp]; split; [| exact hp].
    rewrite he; simpl. rewrite N2Nat.inj_add, repPair_add, <- app_assoc. reflexivity.
Qed.

Lemma foldL3_sound (ls : list LRun) (hPos : PosL ls) :
  expandL (foldL3 ls) = expandL ls /\ PosL (foldL3 ls).
Proof.
  unfold foldL3.
  apply foldLStep_sound; [| exact hPos].
  intros x hx; apply foldLStep_sound; [| exact hx].
  intros y hy; apply foldLStep_sound; [| exact hy].
  intros z hz; exact (conj eq_refl hz).
Qed.

Lemma pushL1C_sound (ls : list LRun) (d : N) (b : bool) (k : N)
    (hk : 1 <= N.to_nat k) (hPos : PosL ls) :
  expandL (pushL1C ls d b k) = repeat (N.to_nat d, b) (N.to_nat k) ++ expandL ls /\
  PosL (pushL1C ls d b k).
Proof.
  exact (foldL3_sound (LOne d b k :: ls) (conj hk hPos)).
Qed.

Lemma pushL1_sound (ls : list LRun) (d : N) (b : bool) (k : N) (hPos : PosL ls) :
  expandL (pushL1 ls d b k) = repeat (N.to_nat d, b) (N.to_nat k) ++ expandL ls /\
  PosL (pushL1 ls d b k).
Proof.
  unfold pushL1. destruct (N.eqb k 0) eqn:hk.
  - apply N.eqb_eq in hk; subst. exact (conj eq_refl hPos).
  - apply N.eqb_neq in hk.
    apply foldL3_sound. simpl; split; [lia | exact hPos].
Qed.

Lemma pushL2_sound (ls : list LRun) (d1 : N) (b1 : bool) (d2 : N) (b2 : bool) (k : N)
    (hPos : PosL ls) :
  expandL (pushL2 ls d1 b1 d2 b2 k) =
    repPair (N.to_nat d1, b1) (N.to_nat d2, b2) (N.to_nat k) ++ expandL ls /\
  PosL (pushL2 ls d1 b1 d2 b2 k).
Proof.
  unfold pushL2. destruct (N.eqb k 0) eqn:hk.
  - apply N.eqb_eq in hk; subst. exact (conj eq_refl hPos).
  - apply N.eqb_neq in hk.
    apply foldL3_sound. simpl; split; [lia | exact hPos].
Qed.

Lemma foldRStep_sound (next : list RRun -> list RRun)
    (hnext : forall xs, PosR xs -> expandR (next xs) = expandR xs /\ PosR (next xs))
    (rs : list RRun) (hPos : PosR rs) :
  expandR (foldRStep next rs) = expandR rs /\ PosR (foldRStep next rs).
Proof.
  destruct rs as [|[z1 o1 c1 | z1 o1 z2 o2 c1] rs']; [exact (conj eq_refl hPos) | |].
  - (* ROne :: rs' *)
    destruct rs' as [|[z2 o2 c2 | ? ? ? ? ?] rest]; try (exact (conj eq_refl hPos)).
    destruct hPos as [h1 [h2 hr]]; simpl in h1, h2.
    unfold foldRStep.
    destruct (N.eqb z1 z2 && N.eqb o1 o2) eqn:heq.
    + apply andb_true_iff in heq as [hz ho]; apply N.eqb_eq in hz; apply N.eqb_eq in ho; subst.
      assert (hpos' : PosR (ROne z2 o2 (c1 + c2) :: rest)) by (simpl; split; [lia | exact hr]).
      destruct (hnext _ hpos') as [he hp]; split; [| exact hp].
      rewrite he; simpl. rewrite N2Nat.inj_add, repeat_add, <- app_assoc. reflexivity.
    + destruct (N.eqb c1 1 && N.eqb c2 1) eqn:hc12; [| exact (conj eq_refl (conj h1 (conj h2 hr)))].
      apply andb_true_iff in hc12 as [hc1 hc2]; apply N.eqb_eq in hc1; apply N.eqb_eq in hc2; subst.
      destruct rest as [|[z3 o3 c3 | tz1 to1 tz2 to2 tc] rest2].
      * exact (conj eq_refl (conj h1 (conj h2 hr))).
      * destruct rest2 as [|[z4 o4 c4 | ? ? ? ? ?] rest3];
          try (exact (conj eq_refl (conj h1 (conj h2 hr)))).
        destruct hr as [h3 [h4 hr3]].
        destruct (N.eqb c3 1 && N.eqb c4 1 &&
                  N.eqb z1 z3 && N.eqb o1 o3 && N.eqb z2 z4 && N.eqb o2 o4) eqn:hm;
          [| exact (conj eq_refl (conj h1 (conj h2 (conj h3 (conj h4 hr3)))))].
        repeat rewrite andb_true_iff in hm.
        destruct hm as [[[[[hc3 hc4] hz13] ho13] hz24] ho24].
        apply N.eqb_eq in hc3; apply N.eqb_eq in hc4;
        apply N.eqb_eq in hz13; apply N.eqb_eq in ho13;
        apply N.eqb_eq in hz24; apply N.eqb_eq in ho24; subst.
        assert (hpos' : PosR (RTwo z3 o3 z4 o4 2 :: rest3)) by (simpl; split; [lia | exact hr3]).
        destruct (hnext _ hpos') as [he hp]; split; [| exact hp].
        rewrite he; reflexivity.
      * destruct hr as [htc hr2]; simpl in htc.
        destruct (N.eqb tz1 z1 && N.eqb to1 o1 && N.eqb tz2 z2 && N.eqb to2 o2) eqn:hm;
          [| exact (conj eq_refl (conj h1 (conj h2 (conj htc hr2))))].
        repeat rewrite andb_true_iff in hm.
        destruct hm as [[[hz1 ho1] hz2] ho2].
        apply N.eqb_eq in hz1; apply N.eqb_eq in ho1;
        apply N.eqb_eq in hz2; apply N.eqb_eq in ho2; subst.
        assert (hpos' : PosR (RTwo z1 o1 z2 o2 (tc + 1) :: rest2)) by (simpl; split; [lia | exact hr2]).
        destruct (hnext _ hpos') as [he hp]; split; [| exact hp].
        rewrite he; simpl.
        replace (N.to_nat (tc + 1)) with (S (N.to_nat tc)) by lia.
        reflexivity.
  - (* RTwo :: rs' *)
    destruct rs' as [|[? ? ? | z1' o1' z2' o2' c2] rest]; try (exact (conj eq_refl hPos)).
    destruct hPos as [h1 [h2 hr]]; simpl in h1, h2.
    unfold foldRStep.
    destruct (N.eqb z1 z1' && N.eqb o1 o1' && N.eqb z2 z2' && N.eqb o2 o2') eqn:hm;
      [| exact (conj eq_refl (conj h1 (conj h2 hr)))].
    repeat rewrite andb_true_iff in hm.
    destruct hm as [[[hz1 ho1] hz2] ho2].
    apply N.eqb_eq in hz1; apply N.eqb_eq in ho1;
    apply N.eqb_eq in hz2; apply N.eqb_eq in ho2; subst.
    assert (hpos' : PosR (RTwo z1' o1' z2' o2' (c1 + c2) :: rest)) by (simpl; split; [lia | exact hr]).
    destruct (hnext _ hpos') as [he hp]; split; [| exact hp].
    rewrite he; simpl. rewrite N2Nat.inj_add, repPair_add, <- app_assoc. reflexivity.
Qed.

Lemma foldR3_sound (rs : list RRun) (hPos : PosR rs) :
  expandR (foldR3 rs) = expandR rs /\ PosR (foldR3 rs).
Proof.
  unfold foldR3.
  apply foldRStep_sound; [| exact hPos].
  intros x hx; apply foldRStep_sound; [| exact hx].
  intros y hy; apply foldRStep_sound; [| exact hy].
  intros z hz; exact (conj eq_refl hz).
Qed.

Lemma pushR1C_sound (rs : list RRun) (z o k : N)
    (hk : 1 <= N.to_nat k) (hPos : PosR rs) :
  expandR (pushR1C rs z o k) = repeat (N.to_nat z, N.to_nat o) (N.to_nat k) ++ expandR rs /\
  PosR (pushR1C rs z o k).
Proof.
  exact (foldR3_sound (ROne z o k :: rs) (conj hk hPos)).
Qed.

Lemma pushR1_sound (rs : list RRun) (z o k : N) (hPos : PosR rs) :
  expandR (pushR1 rs z o k) = repeat (N.to_nat z, N.to_nat o) (N.to_nat k) ++ expandR rs /\
  PosR (pushR1 rs z o k).
Proof.
  unfold pushR1. destruct (N.eqb k 0) eqn:hk.
  - apply N.eqb_eq in hk; subst. exact (conj eq_refl hPos).
  - apply N.eqb_neq in hk.
    apply foldR3_sound. simpl; split; [lia | exact hPos].
Qed.

Lemma pushR2_sound (rs : list RRun) (z1 o1 z2 o2 k : N) (hPos : PosR rs) :
  expandR (pushR2 rs z1 o1 z2 o2 k) =
    repPair (N.to_nat z1, N.to_nat o1) (N.to_nat z2, N.to_nat o2) (N.to_nat k) ++ expandR rs /\
  PosR (pushR2 rs z1 o1 z2 o2 k).
Proof.
  unfold pushR2. destruct (N.eqb k 0) eqn:hk.
  - apply N.eqb_eq in hk; subst. exact (conj eq_refl hPos).
  - apply N.eqb_neq in hk.
    apply foldR3_sound. simpl; split; [lia | exact hPos].
Qed.

Lemma popL_ok_sound {ls rest : list LRun} {d : N} {b : bool}
    (h : popL ls = PLOk d b rest) (hPos : PosL ls) :
  expandL ls = (N.to_nat d, b) :: expandL rest /\ PosL rest.
Proof.
  destruct ls as [|[d1 b1 cnt | d1 b1 d2 b2 cnt] rs]; [discriminate | |];
    destruct hPos as [hr hrs]; simpl in hr, h.
  - destruct (N.eqb cnt 0) eqn:h0; [apply N.eqb_eq in h0; lia |].
    destruct (N.eqb cnt 1) eqn:h1.
    + apply N.eqb_eq in h1; subst. injection h as <- <- <-.
      exact (conj eq_refl hrs).
    + apply N.eqb_neq in h1. injection h as <- <- <-.
      split; [| simpl; split; [lia | exact hrs]].
      simpl. replace (N.to_nat cnt) with (S (N.to_nat (cnt - 1))) by lia.
      reflexivity.
  - destruct (N.eqb cnt 0) eqn:h0; [apply N.eqb_eq in h0; lia |].
    destruct (N.eqb cnt 1) eqn:h1.
    + apply N.eqb_eq in h1; subst. injection h as <- <- <-.
      split; [reflexivity | simpl; split; [lia | exact hrs]].
    + apply N.eqb_neq in h1. injection h as <- <- <-.
      split; [| simpl; split; [lia | split; [lia | exact hrs]]].
      simpl. replace (N.to_nat cnt) with (S (N.to_nat (cnt - 1))) by lia.
      reflexivity.
Qed.

Lemma popL_err_eq_nil {ls : list LRun} (h : popL ls = PLErr) (hPos : PosL ls) : ls = [].
Proof.
  destruct ls as [|[d b cnt | d1 b1 d2 b2 cnt] rs]; [reflexivity | |].
  - destruct hPos as [hr _]; simpl in hr, h.
    destruct (N.eqb cnt 0) eqn:h0; [apply N.eqb_eq in h0; lia |].
    destruct (N.eqb cnt 1); discriminate.
  - destruct hPos as [hr _]; simpl in hr, h.
    destruct (N.eqb cnt 0) eqn:h0; [apply N.eqb_eq in h0; lia |].
    destruct (N.eqb cnt 1); discriminate.
Qed.

Lemma popR_ok_sound {rs rest : list RRun} {z o : N}
    (h : popR rs = PROk z o rest) (hPos : PosR rs) :
  expandR rs = (N.to_nat z, N.to_nat o) :: expandR rest /\ PosR rest.
Proof.
  destruct rs as [|[z1 o1 cnt | z1 o1 z2 o2 cnt] rrest]; [discriminate | |];
    destruct hPos as [hr hrs]; simpl in hr, h.
  - destruct (N.eqb cnt 0) eqn:h0; [apply N.eqb_eq in h0; lia |].
    destruct (N.eqb cnt 1) eqn:h1.
    + apply N.eqb_eq in h1; subst. injection h as <- <- <-.
      exact (conj eq_refl hrs).
    + apply N.eqb_neq in h1. injection h as <- <- <-.
      split; [| simpl; split; [lia | exact hrs]].
      simpl. replace (N.to_nat cnt) with (S (N.to_nat (cnt - 1))) by lia.
      reflexivity.
  - destruct (N.eqb cnt 0) eqn:h0; [apply N.eqb_eq in h0; lia |].
    destruct (N.eqb cnt 1) eqn:h1.
    + apply N.eqb_eq in h1; subst. injection h as <- <- <-.
      split; [reflexivity | simpl; split; [lia | exact hrs]].
    + apply N.eqb_neq in h1. injection h as <- <- <-.
      split; [| simpl; split; [lia | split; [lia | exact hrs]]].
      simpl. replace (N.to_nat cnt) with (S (N.to_nat (cnt - 1))) by lia.
      reflexivity.
Qed.

Lemma popR_err_eq_nil {rs : list RRun} (h : popR rs = PRErr) (hPos : PosR rs) : rs = [].
Proof.
  destruct rs as [|[z o cnt | z1 o1 z2 o2 cnt] rrest]; [reflexivity | |].
  - destruct hPos as [hr _]; simpl in hr, h.
    destruct (N.eqb cnt 0) eqn:h0; [apply N.eqb_eq in h0; lia |].
    destruct (N.eqb cnt 1); discriminate.
  - destruct hPos as [hr _]; simpl in hr, h.
    destruct (N.eqb cnt 0) eqn:h0; [apply N.eqb_eq in h0; lia |].
    destruct (N.eqb cnt 1); discriminate.
Qed.

Lemma bumpLK_sound (ls : list LRun) (hPos : PosL ls) :
  expandL (bumpLK ls) = bumpL (expandL ls) /\ PosL (bumpLK ls).
Proof.
  unfold bumpLK. destruct (popL ls) as [d b rest |] eqn:hp.
  - destruct (popL_ok_sound hp hPos) as [he hPr].
    destruct (pushL1C_sound rest (d + 1)%N b 1%N ltac:(simpl; lia) hPr) as [he2 hP2].
    split; [| exact hP2].
    rewrite he, he2; simpl.
    replace (N.to_nat (d + 1)) with (S (N.to_nat d)) by lia.
    reflexivity.
  - pose proof (popL_err_eq_nil hp hPos) as ->.
    exact (pushL1C_sound [] 0%N false 1%N ltac:(simpl; lia) I).
Qed.

Lemma push100LK_sound (ls : list LRun) (hPos : PosL ls) :
  expandL (push100LK ls) = push100L (expandL ls) /\ PosL (push100LK ls).
Proof.
  destruct ls as [|r rs].
  - simpl. split; [reflexivity | split; [lia | exact I]].
  - assert (hne : expandL (r :: rs) <> []).
    { intros h0. pose proof (expandL_nil_of_pos hPos h0); discriminate. }
    unfold push100LK.
    destruct (pushL1C_sound (r :: rs) 0%N true 1%N ltac:(simpl; lia) hPos) as [he hP].
    split; [| exact hP].
    rewrite he. destruct (expandL (r :: rs)) as [|p ps]; [contradiction | reflexivity].
Qed.

Lemma push0RK_sound (rs : list RRun) (k : N) (hPos : PosR rs) :
  expandR (push0RK rs k) = push0R_iter (N.to_nat k) (expandR rs) /\ PosR (push0RK rs k).
Proof.
  unfold push0RK. destruct (popR rs) as [z o rest |] eqn:hp.
  - destruct (popR_ok_sound hp hPos) as [he hPr].
    destruct (pushR1C_sound rest (z + k)%N o 1%N ltac:(simpl; lia) hPr) as [he2 hP2].
    split; [| exact hP2].
    rewrite he, he2, push0R_iter_cons; simpl.
    replace (N.to_nat (z + k)) with (N.to_nat z + N.to_nat k) by lia.
    reflexivity.
  - pose proof (popR_err_eq_nil hp hPos) as ->.
    simpl. split; [symmetry; apply push0R_iter_nil | exact I].
Qed.

Lemma push1RK_sound (rs : list RRun) (hPos : PosR rs) :
  expandR (push1RK rs) = push1R (expandR rs) /\ PosR (push1RK rs).
Proof.
  unfold push1RK. destruct (popR rs) as [z o rest |] eqn:hp.
  - destruct (popR_ok_sound hp hPos) as [he hPr].
    destruct (N.eqb z 0) eqn:hz.
    + apply N.eqb_eq in hz; subst.
      destruct (pushR1C_sound rest 0%N (o + 1)%N 1%N ltac:(simpl; lia) hPr) as [he2 hP2].
      split; [| exact hP2].
      rewrite he, he2; simpl.
      replace (N.to_nat (o + 1)) with (S (N.to_nat o)) by lia.
      reflexivity.
    + apply N.eqb_neq in hz.
      destruct (pushR1C_sound rest (z - 1)%N o 1%N ltac:(simpl; lia) hPr) as [he1 hP1].
      destruct (pushR1C_sound (pushR1C rest (z - 1)%N o 1%N) 0%N 0%N 1%N ltac:(simpl; lia) hP1) as [he2 hP2].
      split; [| exact hP2].
      rewrite he, he2, he1; simpl.
      replace (N.to_nat z) with (S (N.to_nat (z - 1))) by lia.
      reflexivity.
  - pose proof (popR_err_eq_nil hp hPos) as ->.
    exact (pushR1C_sound [] 0%N 0%N 1%N ltac:(simpl; lia) I).
Qed.

Lemma splitOnesL_sound (ls : list LRun) (hPos : PosL ls) :
  expandL (splitOnesL ls) = expandL ls /\ PosL (splitOnesL ls).
Proof.
  induction ls as [|[d b c | d1 b1 d2 b2 c] rs IH].
  - exact (conj eq_refl I).
  - destruct hPos as [hr hrs]; destruct (IH hrs) as [ihe ihp].
    simpl; rewrite ihe; exact (conj eq_refl (conj hr ihp)).
  - destruct hPos as [hr hrs]; destruct (IH hrs) as [ihe ihp].
    simpl splitOnesL. destruct (N.eqb c 1) eqn:hc.
    + apply N.eqb_eq in hc; subst.
      simpl; rewrite ihe; split; [reflexivity | split; [lia | split; [lia | exact ihp]]].
    + simpl; rewrite ihe; exact (conj eq_refl (conj hr ihp)).
Qed.

Lemma mergeConsL_sound (r : LRun) (rs : list LRun) (hr : PosLRun r) (hrs : PosL rs) :
  expandL (mergeConsL r rs) = expandLRun r ++ expandL rs /\ PosL (mergeConsL r rs).
Proof.
  destruct rs as [|h rest]; [exact (conj eq_refl (conj hr I)) |].
  destruct hrs as [hh hrest].
  destruct r as [d1 b1 c1 | d1 b1 d2 b2 c1].
  - destruct h as [d2 b2 c2 | ? ? ? ? ?];
      simpl mergeConsL; try (exact (conj eq_refl (conj hr (conj hh hrest)))).
    simpl in hr, hh.
    destruct (N.eqb d1 d2 && Bool.eqb b1 b2) eqn:hm;
      [| exact (conj eq_refl (conj hr (conj hh hrest)))].
    apply andb_true_iff in hm as [hd hb]; apply N.eqb_eq in hd; apply bool_eqb_eq in hb; subst.
    simpl; rewrite N2Nat.inj_add, repeat_add, <- app_assoc.
    split; [reflexivity | split; [lia | exact hrest]].
  - destruct h as [? ? ? | d1' b1' d2' b2' c2];
      simpl mergeConsL; try (exact (conj eq_refl (conj hr (conj hh hrest)))).
    simpl in hr, hh.
    destruct (N.eqb d1 d1' && Bool.eqb b1 b1' && N.eqb d2 d2' && Bool.eqb b2 b2') eqn:hm;
      [| exact (conj eq_refl (conj hr (conj hh hrest)))].
    repeat rewrite andb_true_iff in hm.
    destruct hm as [[[hd1 hb1] hd2] hb2].
    apply N.eqb_eq in hd1; apply bool_eqb_eq in hb1;
    apply N.eqb_eq in hd2; apply bool_eqb_eq in hb2; subst.
    simpl; rewrite N2Nat.inj_add, repPair_add, <- app_assoc.
    split; [reflexivity | split; [lia | exact hrest]].
Qed.

Lemma mergeAdjL_sound (ls : list LRun) (hPos : PosL ls) :
  expandL (mergeAdjL ls) = expandL ls /\ PosL (mergeAdjL ls).
Proof.
  induction ls as [|r rs IH]; [exact (conj eq_refl I) |].
  destruct hPos as [hr hrs]; destruct (IH hrs) as [ihe ihp].
  simpl mergeAdjL.
  destruct (mergeConsL_sound r (mergeAdjL rs) hr ihp) as [me mp].
  rewrite me, ihe; exact (conj eq_refl mp).
Qed.

Lemma normL_sound (ls : list LRun) (hPos : PosL ls) :
  expandL (normL ls) = expandL ls /\ PosL (normL ls).
Proof.
  unfold normL.
  destruct (splitOnesL_sound ls hPos) as [se sp].
  destruct (mergeAdjL_sound (splitOnesL ls) sp) as [me mp].
  rewrite me, se; exact (conj eq_refl mp).
Qed.

Lemma peelRun_sound (d : N) (b : bool) (ls : list LRun) :
  forall (k : N) (ls' : list LRun),
    peelRun d b ls k = Some ls' -> PosL ls ->
    expandL ls = repeat (N.to_nat d, b) (N.to_nat k) ++ expandL ls' /\ PosL ls'.
Proof.
  induction ls as [|[d1 b1 cnt | d1 b1 d2 b2 cnt] rs IH]; intros k ls' h hPos.
  - unfold peelRun in h. destruct (N.eqb k 0) eqn:hk0; [| discriminate].
    apply N.eqb_eq in hk0; subst. injection h as <-. exact (conj eq_refl I).
  - simpl peelRun in h. destruct (N.eqb k 0) eqn:hk0.
    + apply N.eqb_eq in hk0; subst. injection h as <-. exact (conj eq_refl hPos).
    + apply N.eqb_neq in hk0.
      destruct hPos as [hr hrs]; simpl in hr.
      destruct (N.eqb d1 d && Bool.eqb b1 b && N.leb 1 cnt) eqn:hm; [| discriminate].
      repeat rewrite andb_true_iff in hm.
      destruct hm as [[hd hb] hcnt].
      apply N.eqb_eq in hd; apply bool_eqb_eq in hb; apply N.leb_le in hcnt; subst.
      destruct (N.leb k cnt) eqn:hle.
      * apply N.leb_le in hle.
        destruct (N.eqb (cnt - k) 0) eqn:hrem.
        -- apply N.eqb_eq in hrem. assert (cnt = k) by lia; subst.
           injection h as <-. exact (conj eq_refl hrs).
        -- apply N.eqb_neq in hrem. injection h as <-.
           split; [| simpl; split; [lia | exact hrs]].
           simpl. replace (N.to_nat cnt) with (N.to_nat k + N.to_nat (cnt - k)) by lia.
           rewrite repeat_add, <- app_assoc. reflexivity.
      * apply N.leb_gt in hle.
        destruct (IH (k - cnt)%N ls' h hrs) as [ihe ihp].
        split; [| exact ihp].
        simpl expandL. rewrite ihe.
        replace (N.to_nat k) with (N.to_nat cnt + N.to_nat (k - cnt)) by lia.
        rewrite repeat_add, <- app_assoc. reflexivity.
  - simpl peelRun in h. destruct (N.eqb k 0) eqn:hk0.
    + apply N.eqb_eq in hk0; subst. injection h as <-. exact (conj eq_refl hPos).
    + destruct hPos as [hr hrs]; simpl in hr.
      destruct (N.eqb d1 d && Bool.eqb b1 b && N.leb 1 cnt && N.eqb k 1) eqn:hm; [| discriminate].
      repeat rewrite andb_true_iff in hm.
      destruct hm as [[[hd hb] hcnt] hk1].
      apply N.eqb_eq in hd; apply bool_eqb_eq in hb;
      apply N.leb_le in hcnt; apply N.eqb_eq in hk1; subst.
      destruct (N.eqb cnt 1) eqn:hc1.
      * apply N.eqb_eq in hc1; subst. injection h as <-.
        simpl. split; [reflexivity | split; [lia | exact hrs]].
      * apply N.eqb_neq in hc1. injection h as <-.
        split; [| simpl; split; [lia | split; [lia | exact hrs]]].
        simpl. replace (N.to_nat cnt) with (S (N.to_nat (cnt - 1))) by lia.
        reflexivity.
Qed.

Lemma peelW_sound (w : list bool) :
  forall (ls ls' : list LRun),
    peelW w ls = Some ls' -> PosL ls ->
    expandL ls = encW w ++ expandL ls' /\ PosL ls'.
Proof.
  induction w as [|[|] bs IH]; intros ls ls' h hPos; simpl in h.
  - injection h as <-; exact (conj eq_refl hPos).
  - destruct (peelRun 2 false ls 1) as [l1 |] eqn:hp; [| discriminate].
    destruct (peelRun_sound 2 false ls 1 l1 hp hPos) as [h1 hP1].
    destruct (IH l1 ls' h hP1) as [h2 hP2].
    rewrite h1, h2; exact (conj eq_refl hP2).
  - destruct (peelRun 0 false ls 1) as [l1 |] eqn:hp; [| discriminate].
    destruct (peelRun_sound 0 false ls 1 l1 hp hPos) as [h1 hP1].
    destruct (IH l1 ls' h hP1) as [h2 hP2].
    rewrite h1, h2; exact (conj eq_refl hP2).
Qed.

Lemma pushW_sound (w : list bool) (ls : list LRun) (hPos : PosL ls) :
  expandL (pushW w ls) = encW w ++ expandL ls /\ PosL (pushW w ls).
Proof.
  induction w as [|[|] bs [ihe ihp]]; simpl.
  - exact (conj eq_refl hPos).
  - destruct (pushL1_sound (pushW bs ls) 2 false 1 ihp) as [he hp].
    rewrite he, ihe; exact (conj eq_refl hp).
  - destruct (pushL1_sound (pushW bs ls) 0 false 1 ihp) as [he hp].
    rewrite he, ihe; exact (conj eq_refl hp).
Qed.

(* ========================================================================= *)
(* Section 4: RLE Evaluator Soundness                                        *)
(* ========================================================================= *)

Lemma stepAK_sound (l : side) (ls : list LRun) (rs : list RRun)
    (hl : (S1 >> l) = encLeft (expandL ls))
    (hPL : PosL ls) (hPR : PosR rs) :
  (forall m' ls' rs', stepAK ls rs = SROk m' ls' rs' ->
    PosL ls' /\ PosR rs' /\
      (l {{A}}> encRight (expandR rs)) -[ tm ]->+ evalSegCfg m' (expandL ls') (expandR rs')) /\
  (stepAK ls rs = SRHalted -> halts tm (l {{A}}> encRight (expandR rs))).
Proof.
  destruct rs as [|r rrest].
  - simpl stepAK. split.
    + intros m' ls' rs' h; injection h as <- <- <-.
      refine (conj hPL (conj _ _)); [simpl; split; [lia | exact I] |].
      exact (step_A_common l (expandL ls) hl [] mCL (expandL ls) [(0, 1)] eq_refl).
    + discriminate.
  - unfold stepAK; fold (popR (r :: rrest)).
    destruct (popR (r :: rrest)) as [z o r1 |] eqn:hpop; [| split; intros; discriminate].
    destruct (popR_ok_sound hpop hPR) as [heR hPR1].
    rewrite heR.
    destruct (N.eqb z 0) eqn:hz0.
    + apply N.eqb_eq in hz0; subst. simpl (N.to_nat 0).
      destruct (N.eqb o 0) eqn:ho0.
      * apply N.eqb_eq in ho0; subst. simpl (N.to_nat 0).
        split; [| discriminate].
        intros m' ls' rs' h; injection h as <- <- <-.
        destruct (push0RK_sound r1 1 hPR1) as [he2 hP2].
        refine (conj hPL (conj hP2 _)).
        rewrite he2; simpl push0R_iter.
        exact (step_A_common l (expandL ls) hl ((0, 0) :: expandR r1)
          mER (expandL ls) (push0R (expandR r1)) eq_refl).
      * apply N.eqb_neq in ho0.
        split; [| discriminate].
        intros m' ls' rs' h; injection h as <- <- <-.
        destruct (pushR1C_sound r1 0 (o - 1) 1 ltac:(simpl; lia) hPR1) as [he2 hP2].
        refine (conj hPL (conj hP2 _)).
        rewrite he2; simpl repeat; simpl app.
        replace (N.to_nat o) with (S (N.to_nat (o - 1))) by lia.
        exact (step_A_common l (expandL ls) hl ((0, S (N.to_nat (o - 1))) :: expandR r1)
          mER (expandL ls) ((0, N.to_nat (o - 1)) :: expandR r1) eq_refl).
    + apply N.eqb_neq in hz0.
      destruct (N.eqb z 1) eqn:hz1.
      * apply N.eqb_eq in hz1; subst. simpl (N.to_nat 1).
        destruct (N.eqb o 0) eqn:ho0.
        -- apply N.eqb_eq in ho0; subst. simpl (N.to_nat 0).
           split; [| discriminate].
           intros m' ls' rs' h; injection h as <- <- <-.
           refine (conj hPL (conj hPR1 _)).
           exact (step_A_common l (expandL ls) hl ((1, 0) :: expandR r1)
             mAR00 (expandL ls) (expandR r1) eq_refl).
        -- apply N.eqb_neq in ho0.
           split; [intros; discriminate | intros _].
           replace (N.to_nat o) with (S (N.to_nat (o - 1))) by lia.
           exact (step_A_halts l (N.to_nat (o - 1)) (expandR r1)).
      * apply N.eqb_neq in hz1.
        destruct (N.eqb z 2) eqn:hz2.
        -- apply N.eqb_eq in hz2; subst. simpl (N.to_nat 2).
           destruct (pushL1C_sound ls 0 false 1 ltac:(simpl; lia) hPL) as [heL1 hPL1].
           destruct (N.eqb o 0) eqn:ho0.
           ++ apply N.eqb_eq in ho0; subst. simpl (N.to_nat 0).
              split; [| discriminate].
              intros m' ls' rs' h; injection h as <- <- <-.
              destruct (push0RK_sound r1 1 hPR1) as [he2 hP2].
              refine (conj hPL1 (conj hP2 _)).
              rewrite heL1, he2; simpl repeat; simpl app; simpl push0R_iter.
              exact (step_A_common l (expandL ls) hl ((2, 0) :: expandR r1)
                mDR ((0, false) :: expandL ls) (push0R (expandR r1)) eq_refl).
           ++ apply N.eqb_neq in ho0.
              split; [| discriminate].
              intros m' ls' rs' h; injection h as <- <- <-.
              destruct (pushR1C_sound r1 0 (o - 1) 1 ltac:(simpl; lia) hPR1) as [he2 hP2].
              refine (conj hPL1 (conj hP2 _)).
              rewrite heL1, he2; simpl repeat; simpl app.
              replace (N.to_nat o) with (S (N.to_nat (o - 1))) by lia.
              exact (step_A_common l (expandL ls) hl ((2, S (N.to_nat (o - 1))) :: expandR r1)
                mDR ((0, false) :: expandL ls) ((0, N.to_nat (o - 1)) :: expandR r1) eq_refl).
        -- apply N.eqb_neq in hz2.
           split; [| discriminate].
           intros m' ls' rs' h.
           assert (m' = mCL /\ ls' = ls /\ rs' = push1RK (push1RK (pushR1C r1 (z - 3) o 1)))
             as [-> [-> ->]] by (inversion h; repeat split).
           destruct (pushR1C_sound r1 (z - 3) o 1 ltac:(simpl; lia) hPR1) as [he1 hP1].
           destruct (push1RK_sound _ hP1) as [he2 hP2].
           destruct (push1RK_sound _ hP2) as [he3 hP3].
           refine (conj hPL (conj hP3 _)).
           rewrite he3, he2, he1; simpl repeat; simpl app.
           replace (N.to_nat z) with (S (S (S (N.to_nat (z - 3))))) by lia.
           exact (step_A_common l (expandL ls) hl ((S (S (S (N.to_nat (z - 3)))), N.to_nat o) :: expandR r1)
             mCL (expandL ls) (push1R (push1R ((N.to_nat (z - 3), N.to_nat o) :: expandR r1))) eq_refl).
Qed.

Lemma sweepK_sound (isE : bool) (d : N) (b : bool) (ls : list LRun) (rs : list RRun)
    (hPL : PosL ls) (hPR : PosR rs) :
  (forall m' ls' rs', sweepK isE d b ls rs = SROk m' ls' rs' ->
    PosL ls' /\ PosR rs' /\
      evalSegCfg (sweepMode isE) ((N.to_nat d, b) :: expandL ls) (expandR rs) -[ tm ]->+
        evalSegCfg m' (expandL ls') (expandR rs')) /\
  (sweepK isE d b ls rs <> SRHalted).
Proof.
  pose proof (step_sweepDLEL (N.to_nat d) isE b (expandL ls) (expandR rs)) as hstep.
  rewrite sweepDLEL_closed in hstep.
  destruct (push0RK_sound rs (d + 1) hPR) as [heR1 hPR1].
  replace (N.to_nat (d + 1)) with (N.to_nat d + 1) in heR1 by lia.
  unfold sweepK. rewrite N_mod2_eqb.
  destruct (Nat.eqb ((N.to_nat d) mod 2) 0), isE, b; simpl in hstep |- *;
    (split; [| discriminate]);
    intros m' ls' rs' h; injection h as <- <- <-.
  - destruct (pushL1C_sound ls 0 false 1 ltac:(simpl; lia) hPL) as [heL1 hPL1].
    refine (conj hPL1 (conj hPR1 _)). rewrite heL1, heR1; exact hstep.
  - destruct (bumpLK_sound ls hPL) as [heL1 hPL1].
    refine (conj hPL1 (conj hPR1 _)). rewrite heL1, heR1; exact hstep.
  - refine (conj hPL (conj hPR1 _)). rewrite heR1; exact hstep.
  - refine (conj hPL (conj hPR1 _)). rewrite heR1; exact hstep.
  - refine (conj hPL (conj hPR1 _)). rewrite heR1; exact hstep.
  - refine (conj hPL (conj hPR1 _)). rewrite heR1; exact hstep.
  - destruct (pushL1C_sound ls 0 false 1 ltac:(simpl; lia) hPL) as [heL1 hPL1].
    refine (conj hPL1 (conj hPR1 _)). rewrite heL1, heR1; exact hstep.
  - destruct (bumpLK_sound ls hPL) as [heL1 hPL1].
    refine (conj hPL1 (conj hPR1 _)). rewrite heL1, heR1; exact hstep.
Qed.

Lemma stepSingleRLEK_sound (m : SegMode) (ls : list LRun) (rs : list RRun)
    (hPL : PosL ls) (hPR : PosR rs) :
  (forall m' ls' rs', stepSingleRLEK m ls rs = SROk m' ls' rs' ->
    PosL ls' /\ PosR rs' /\
      evalSegCfg m (expandL ls) (expandR rs) -[ tm ]->+
        evalSegCfg m' (expandL ls') (expandR rs')) /\
  (stepSingleRLEK m ls rs = SRHalted -> halts tm (evalSegCfg m (expandL ls) (expandR rs))).
Proof.
  destruct m; simpl stepSingleRLEK.
  - (* mAR *)
    unfold evalSegCfg at 1 3.
    destruct (bumpLK_sound ls hPL) as [heL hPL1].
    apply (stepAK_sound (encLeft (expandL ls)) (bumpLK ls) rs); [| exact hPL1 | exact hPR].
    rewrite heL; exact (cons_one_encLeft (expandL ls)).
  - (* mAR0 *)
    unfold evalSegCfg at 1 3.
    destruct (pushL1C_sound ls 0 false 1 ltac:(simpl; lia) hPL) as [heL hPL1].
    apply (stepAK_sound (S0 >> encLeft (expandL ls)) (pushL1C ls 0 false 1) rs); [| exact hPL1 | exact hPR].
    rewrite heL; reflexivity.
  - (* mAR00 *)
    unfold evalSegCfg at 1 3.
    destruct (push100LK_sound ls hPL) as [heL hPL1].
    apply (stepAK_sound (S0 >> S0 >> encLeft (expandL ls)) (push100LK ls) rs); [| exact hPL1 | exact hPR].
    rewrite heL; exact (cons_100_encLeft (expandL ls)).
  - (* mCL *)
    destruct ls as [|r lrest].
    + split; [| discriminate].
      intros m' ls' rs' h; injection h as <- <- <-.
      destruct (push1RK_sound rs hPR) as [heR hPR1].
      refine (conj I (conj hPR1 _)).
      rewrite heR; apply mstep; reflexivity.
    + split; [| discriminate].
      intros m' ls' rs' h; injection h as <- <- <-.
      refine (conj hPL (conj hPR _)).
      assert (hne : expandL (r :: lrest) <> []).
      { intros h0. pose proof (expandL_nil_of_pos hPL h0); discriminate. }
      destruct (expandL (r :: lrest)) as [|p l0]; [contradiction | apply mstep; reflexivity].
  - (* mDL *)
    destruct (popL ls) as [d b l1 |] eqn:hpop.
    + destruct (popL_ok_sound hpop hPL) as [heL hPL1].
      rewrite heL.
      destruct (sweepK_sound false d b l1 rs hPL1 hPR) as [h1 h2].
      split; [exact h1 | intros hh; contradiction].
    + pose proof (popL_err_eq_nil hpop hPL) as ->.
      split; [| discriminate].
      intros m' ls' rs' h; injection h as <- <- <-.
      destruct (pushL1C_sound [] 0 false 1 ltac:(simpl; lia) I) as [heL hPL1].
      refine (conj hPL1 (conj hPR _)).
      rewrite heL; apply mstep; reflexivity.
  - (* mEL *)
    destruct (popL ls) as [d b l1 |] eqn:hpop.
    + destruct (popL_ok_sound hpop hPL) as [heL hPL1].
      rewrite heL.
      destruct (sweepK_sound true d b l1 rs hPL1 hPR) as [h1 h2].
      split; [exact h1 | intros hh; contradiction].
    + pose proof (popL_err_eq_nil hpop hPL) as ->.
      split; [| discriminate].
      intros m' ls' rs' h; injection h as <- <- <-.
      refine (conj I (conj hPR _)); apply mstep; reflexivity.
  - (* mDR *)
    destruct (popR rs) as [z o r1 |] eqn:hpop.
    + destruct (popR_ok_sound hpop hPR) as [heR hPR1].
      rewrite heR.
      destruct (N.eqb z 0) eqn:hz0.
      * apply N.eqb_eq in hz0; subst. simpl (N.to_nat 0).
        destruct (N.eqb o 0) eqn:ho0.
        -- apply N.eqb_eq in ho0; subst. simpl (N.to_nat 0).
           split; [| discriminate].
           intros m' ls' rs' h; injection h as <- <- <-.
           destruct (push0RK_sound r1 2 hPR1) as [he2 hP2].
           refine (conj hPL (conj hP2 _)).
           rewrite he2; apply mstep; reflexivity.
        -- apply N.eqb_neq in ho0.
           split; [| discriminate].
           intros m' ls' rs' h; injection h as <- <- <-.
           destruct (pushR1C_sound r1 1 (o - 1) 1 ltac:(simpl; lia) hPR1) as [he2 hP2].
           refine (conj hPL (conj hP2 _)).
           rewrite he2; simpl repeat; simpl app.
           replace (N.to_nat o) with (S (N.to_nat (o - 1))) by lia.
           apply mstep; reflexivity.
      * apply N.eqb_neq in hz0.
        split; [| discriminate].
        intros m' ls' rs' h; injection h as <- <- <-.
        destruct (bumpLK_sound ls hPL) as [heL hPL1].
        destruct (pushR1C_sound r1 (z - 1) o 1 ltac:(simpl; lia) hPR1) as [he2 hP2].
        refine (conj hPL1 (conj hP2 _)).
        rewrite heL, he2; simpl repeat; simpl app.
        replace (N.to_nat z) with (S (N.to_nat (z - 1))) by lia.
        apply mstep; reflexivity.
    + pose proof (popR_err_eq_nil hpop hPR) as ->.
      split; [| discriminate].
      intros m' ls' rs' h; injection h as <- <- <-.
      destruct (bumpLK_sound ls hPL) as [heL hPL1].
      refine (conj hPL1 (conj I _)).
      rewrite heL; apply mstep; reflexivity.
  - (* mER *)
    destruct (popR rs) as [z o r1 |] eqn:hpop.
    + destruct (popR_ok_sound hpop hPR) as [heR hPR1].
      rewrite heR.
      destruct (N.eqb z 0) eqn:hz0.
      * apply N.eqb_eq in hz0; subst. simpl (N.to_nat 0).
        destruct (N.eqb o 0) eqn:ho0.
        -- apply N.eqb_eq in ho0; subst. simpl (N.to_nat 0).
           split; [| discriminate].
           intros m' ls' rs' h; injection h as <- <- <-.
           destruct (push0RK_sound r1 2 hPR1) as [he2 hP2].
           refine (conj hPL (conj hP2 _)).
           rewrite he2; apply mstep; reflexivity.
        -- apply N.eqb_neq in ho0.
           split; [| discriminate].
           intros m' ls' rs' h; injection h as <- <- <-.
           destruct (pushR1C_sound r1 1 (o - 1) 1 ltac:(simpl; lia) hPR1) as [he2 hP2].
           refine (conj hPL (conj hP2 _)).
           rewrite he2; simpl repeat; simpl app.
           replace (N.to_nat o) with (S (N.to_nat (o - 1))) by lia.
           apply mstep; reflexivity.
      * apply N.eqb_neq in hz0.
        split; [| discriminate].
        intros m' ls' rs' h; injection h as <- <- <-.
        destruct (pushR1C_sound r1 (z - 1) o 1 ltac:(simpl; lia) hPR1) as [he2 hP2].
        refine (conj hPL (conj hP2 _)).
        rewrite he2; simpl repeat; simpl app.
        replace (N.to_nat z) with (S (N.to_nat (z - 1))) by lia.
        apply mstep; reflexivity.
    + pose proof (popR_err_eq_nil hpop hPR) as ->.
      split; [| discriminate].
      intros m' ls' rs' h; injection h as <- <- <-.
      refine (conj hPL (conj I _)); apply mstep; reflexivity.
Qed.

Lemma tryELBulkK_sound (ls : list LRun) (rs : list RRun)
    (hPL : PosL ls) (hPR : PosR rs) :
  (forall m' ls' rs', tryELBulkK ls rs = SROk m' ls' rs' ->
    PosL ls' /\ PosR rs' /\
      evalSegCfg mEL (expandL ls) (expandR rs) -[ tm ]->+
        evalSegCfg m' (expandL ls') (expandR rs')) /\
  (tryELBulkK ls rs = SRHalted -> halts tm (evalSegCfg mEL (expandL ls) (expandR rs))).
Proof.
  pose proof (stepSingleRLEK_sound mEL ls rs hPL hPR) as hfb.
  unfold tryELBulkK.
  destruct (popR rs) as [rz ro r_rest |] eqn:hpopR; [| exact hfb].
  destruct (N.eqb rz 1 && N.eqb ro 0) eqn:hrz; [| exact hfb].
  apply andb_true_iff in hrz as [hrz1 hro0]; apply N.eqb_eq in hrz1; apply N.eqb_eq in hro0; subst.
  destruct (popR_ok_sound hpopR hPR) as [heR hPRr].
  destruct (popL ls) as [d0 [|] [|blk l_rest] |] eqn:hpopL; try exact hfb.
  destruct (N.leb 2 d0 && N.eqb (N.modulo d0 2) 0) eqn:hd0; [| exact hfb].
  apply andb_true_iff in hd0 as [hd0_ge hd0_even].
  apply N.leb_le in hd0_ge. rewrite N_mod2_eqb in hd0_even; apply Nat.eqb_eq in hd0_even.
  destruct (popL_ok_sound hpopL hPL) as [heL [hPblk hPLr]].
  destruct blk as [bd [|] bk | bd1 [|] bd2 [|] bk]; try exact hfb.
  - (* LOne *)
    destruct (N.eqb bd (d0 - 2) && N.leb 1 bk) eqn:hcond; [| exact hfb].
    apply andb_true_iff in hcond as [hbd hbk]; apply N.eqb_eq in hbd; apply N.leb_le in hbk; subst.
    split; [| discriminate].
    intros m' ls' rs' h; injection h as <- <- <-.
    destruct (pushL1C_sound l_rest d0 false 1 ltac:(simpl; lia) hPLr) as [heL' hPL'].
    destruct (pushR1C_sound r_rest (d0 - 2) 0 bk ltac:(lia) hPRr) as [heR1 hPR1].
    destruct (pushR1C_sound _ 1 0 1 ltac:(simpl; lia) hPR1) as [heR' hPR'].
    refine (conj hPL' (conj hPR' _)).
    rewrite heL, heR, heL', heR', heR1; simpl expandL; simpl expandLRun; simpl repeat; simpl app.
    set (q := (N.to_nat d0 - 2) / 2).
    assert (hq1 : N.to_nat d0 = 2 * q + 2) by (unfold q; lia).
    assert (hq2 : N.to_nat (d0 - 2) = 2 * q) by (unfold q; lia).
    rewrite hq1, hq2.
    exact (rule_B1 q (N.to_nat bk) ltac:(lia) (expandL l_rest) (expandR r_rest)).
  - (* LTwo *)
    destruct (N.eqb d0 4 && N.eqb bd1 0 && N.eqb bd2 2 && N.leb 1 bk) eqn:hc2.
    + repeat rewrite andb_true_iff in hc2; destruct hc2 as [[[hd04 hbd1] hbd2] hbk].
      apply N.eqb_eq in hd04; apply N.eqb_eq in hbd1; apply N.eqb_eq in hbd2; apply N.leb_le in hbk; subst.
      split; [| discriminate].
      intros m' ls' rs' h; injection h as <- <- <-.
      destruct (pushL1C_sound l_rest 4 false 1 ltac:(simpl; lia) hPLr) as [heL' hPL'].
      destruct (pushR2_sound r_rest 0 0 2 0 bk hPRr) as [heR1 hPR1].
      destruct (pushR1C_sound _ 1 0 1 ltac:(simpl; lia) hPR1) as [heR' hPR'].
      refine (conj hPL' (conj hPR' _)).
      rewrite heL, heR, heL', heR', heR1; simpl.
      exact (rule_B2 (N.to_nat bk) ltac:(lia) (expandL l_rest) (expandR r_rest)).
    + destruct (N.eqb d0 2 && N.eqb bd1 2 && N.eqb bd2 0 && N.leb 1 bk) eqn:hc3.
      * repeat rewrite andb_true_iff in hc3; destruct hc3 as [[[hd02 hbd1] hbd2] hbk].
        apply N.eqb_eq in hd02; apply N.eqb_eq in hbd1; apply N.eqb_eq in hbd2; apply N.leb_le in hbk; subst.
        split; [| discriminate].
        intros m' ls' rs' h; injection h as <- <- <-.
        destruct (pushL1C_sound l_rest 2 false 1 ltac:(simpl; lia) hPLr) as [heL' hPL'].
        destruct (pushR2_sound r_rest 2 0 0 0 bk hPRr) as [heR1 hPR1].
        destruct (pushR1C_sound _ 1 0 1 ltac:(simpl; lia) hPR1) as [heR' hPR'].
        refine (conj hPL' (conj hPR' _)).
        rewrite heL, heR, heL', heR', heR1; simpl.
        exact (rule_B3 (N.to_nat bk) ltac:(lia) (expandL l_rest) (expandR r_rest)).
      * destruct (N.eqb d0 2 && N.eqb bd1 0 && N.eqb bd2 2 && N.leb 2 bk) eqn:hc4.
        -- repeat rewrite andb_true_iff in hc4; destruct hc4 as [[[hd02 hbd1] hbd2] hbk].
           apply N.eqb_eq in hd02; apply N.eqb_eq in hbd1; apply N.eqb_eq in hbd2; apply N.leb_le in hbk; subst.
           split; [| discriminate].
           intros m' ls' rs' h; injection h as <- <- <-.
           destruct (pushL1C_sound l_rest 2 false 1 ltac:(simpl; lia) hPLr) as [heL1 hPL1].
           destruct (pushL1C_sound _ 2 false 1 ltac:(simpl; lia) hPL1) as [heL' hPL'].
           destruct (pushR1C_sound r_rest 0 0 1 ltac:(simpl; lia) hPRr) as [heR0 hPR0].
           destruct (pushR2_sound _ 2 0 0 0 (bk - 1) hPR0) as [heR1 hPR1].
           destruct (pushR1C_sound _ 1 0 1 ltac:(simpl; lia) hPR1) as [heR' hPR'].
           refine (conj hPL' (conj hPR' _)).
           rewrite heL, heR, heL', heL1, heR', heR1, heR0; simpl.
           replace (N.to_nat (bk - 1)) with (N.to_nat bk - 1) by lia.
           exact (rule_B4 (N.to_nat bk) ltac:(lia) (expandL l_rest) (expandR r_rest)).
        -- destruct (N.eqb d0 4 && N.eqb bd1 2 && N.eqb bd2 0 && N.leb 2 bk) eqn:hc5; [| exact hfb].
           repeat rewrite andb_true_iff in hc5; destruct hc5 as [[[hd04 hbd1] hbd2] hbk].
           apply N.eqb_eq in hd04; apply N.eqb_eq in hbd1; apply N.eqb_eq in hbd2; apply N.leb_le in hbk; subst.
           split; [| discriminate].
           intros m' ls' rs' h; injection h as <- <- <-.
           destruct (pushL1C_sound l_rest 0 false 1 ltac:(simpl; lia) hPLr) as [heL1 hPL1].
           destruct (pushL1C_sound _ 4 false 1 ltac:(simpl; lia) hPL1) as [heL' hPL'].
           destruct (pushR1C_sound r_rest 2 0 1 ltac:(simpl; lia) hPRr) as [heR0 hPR0].
           destruct (pushR2_sound _ 0 0 2 0 (bk - 1) hPR0) as [heR1 hPR1].
           destruct (pushR1C_sound _ 1 0 1 ltac:(simpl; lia) hPR1) as [heR' hPR'].
           refine (conj hPL' (conj hPR' _)).
           rewrite heL, heR, heL', heL1, heR', heR1, heR0; simpl.
           replace (N.to_nat (bk - 1)) with (N.to_nat bk - 1) by lia.
           exact (rule_B5 (N.to_nat bk) ltac:(lia) (expandL l_rest) (expandR r_rest)).
Qed.

Lemma stepRLEK_sound (m : SegMode) (ls : list LRun) (rs : list RRun)
    (hPL : PosL ls) (hPR : PosR rs) :
  (forall m' ls' rs', stepRLEK m ls rs = SROk m' ls' rs' ->
    PosL ls' /\ PosR rs' /\
      evalSegCfg m (expandL ls) (expandR rs) -[ tm ]->+
        evalSegCfg m' (expandL ls') (expandR rs')) /\
  (stepRLEK m ls rs = SRHalted -> halts tm (evalSegCfg m (expandL ls) (expandR rs))).
Proof.
  pose proof (stepSingleRLEK_sound m ls rs hPL hPR) as hfb.
  destruct m; try exact hfb.
  - (* mAR0 *)
    simpl stepRLEK.
    destruct rs as [|[z o k | z1 o1 z2 o2 k] rest]; [exact hfb | |];
      destruct hPR as [hPr hPrest].
    + (* ROne *)
      destruct (N.eqb o 0) eqn:ho0; simpl negb; [| exact hfb].
      apply N.eqb_eq in ho0; subst.
      destruct (N.eqb z 0 && N.leb 1 k) eqn:ha1.
      * apply andb_true_iff in ha1 as [hz0 hk]; apply N.eqb_eq in hz0; apply N.leb_le in hk; subst.
        split; [| discriminate].
        intros m' ls' rs' h; injection h as <- <- <-.
        destruct (pushL1C_sound ls 0 false k ltac:(lia) hPL) as [heL' hPL'].
        refine (conj hPL' (conj hPrest _)).
        rewrite heL'; simpl expandR; simpl expandRRun.
        exact (rule_A1 (N.to_nat k) ltac:(lia) (expandL ls) (expandR rest)).
      * destruct (N.eqb z 2 && N.eqb k 1) eqn:ha2c.
        -- apply andb_true_iff in ha2c as [hz2 hk1]; apply N.eqb_eq in hz2; apply N.eqb_eq in hk1; subst.
           destruct rest as [|[? ? ? | z1 o1 z2 o2 k2] rest2]; try exact hfb.
           destruct hPrest as [hPr2 hPrest2].
           destruct (N.eqb z1 0 && N.eqb o1 0 && N.eqb z2 2 && N.eqb o2 0 && N.leb 1 k2) eqn:hc2c;
             [| exact hfb].
           repeat rewrite andb_true_iff in hc2c; destruct hc2c as [[[[hz1 ho1] hz2] ho2] hk2].
           apply N.eqb_eq in hz1; apply N.eqb_eq in ho1; apply N.eqb_eq in hz2;
           apply N.eqb_eq in ho2; apply N.leb_le in hk2; subst.
           split; [| discriminate].
           intros m' ls' rs' h; injection h as <- <- <-.
           destruct (pushL2_sound ls 2 false 0 false k2 hPL) as [heL' hPL'].
           destruct (pushR1C_sound rest2 2 0 1 ltac:(simpl; lia) hPrest2) as [heR' hPR'].
           refine (conj hPL' (conj hPR' _)).
           rewrite heL', heR'; simpl.
           exact (rule_A2c (N.to_nat k2) ltac:(lia) (expandL ls) (expandR rest2)).
        -- destruct (N.eqb z 4 && N.leb 1 k) eqn:ha3.
           ++ apply andb_true_iff in ha3 as [hz4 hk]; apply N.eqb_eq in hz4; apply N.leb_le in hk; subst.
              destruct (popL ls) as [d b l1 |] eqn:hpopL; [| exact hfb].
              destruct (popL_ok_sound hpopL hPL) as [heL hPL1].
              destruct (pushL1C_sound l1 (d + 2) b 1 ltac:(simpl; lia) hPL1) as [heL2 hPL2].
              destruct (N.eqb k 1) eqn:hk1.
              ** apply N.eqb_eq in hk1; subst.
                 split; [| discriminate].
                 intros m' ls' rs' h; injection h as <- <- <-.
                 destruct (pushL1C_sound _ 2 false 1 ltac:(simpl; lia) hPL2) as [heL' hPL'].
                 refine (conj hPL' (conj hPrest _)).
                 rewrite heL, heL', heL2; simpl.
                 replace (N.to_nat (d + 2)) with (N.to_nat d + 2) by lia.
                 pose proof (rule_A3 1 ltac:(lia) (N.to_nat d) b (expandL l1) (expandR rest)) as hr3.
                 simpl in hr3; exact hr3.
              ** apply N.eqb_neq in hk1.
                 split; [| discriminate].
                 intros m' ls' rs' h; injection h as <- <- <-.
                 destruct (pushL1C_sound _ 4 false (k - 1) ltac:(lia) hPL2) as [heL3 hPL3].
                 destruct (pushL1C_sound _ 2 false 1 ltac:(simpl; lia) hPL3) as [heL' hPL'].
                 refine (conj hPL' (conj hPrest _)).
                 rewrite heL, heL', heL3, heL2; simpl.
                 replace (N.to_nat (k - 1)) with (N.to_nat k - 1) by lia.
                 replace (N.to_nat (d + 2)) with (N.to_nat d + 2) by lia.
                 exact (rule_A3 (N.to_nat k) ltac:(lia) (N.to_nat d) b (expandL l1) (expandR rest)).
           ++ destruct (N.eqb z 2 && N.leb 2 k) eqn:ha4; [| exact hfb].
              apply andb_true_iff in ha4 as [hz2 hk]; apply N.eqb_eq in hz2; apply N.leb_le in hk; subst.
              destruct (pushL1C_sound ls 0 false 1 ltac:(simpl; lia) hPL) as [heL1 hPL1].
              destruct (N.eqb k 2) eqn:hk2.
              ** apply N.eqb_eq in hk2; subst.
                 split; [| discriminate].
                 intros m' ls' rs' h; injection h as <- <- <-.
                 destruct (pushL1C_sound _ 0 false 1 ltac:(simpl; lia) hPL1) as [heL' hPL'].
                 destruct (pushR1C_sound rest 3 0 1 ltac:(simpl; lia) hPrest) as [heR' hPR'].
                 refine (conj hPL' (conj hPR' _)).
                 rewrite heL', heL1, heR'; simpl.
                 pose proof (rule_A4 2 ltac:(lia) (expandL ls) (expandR rest)) as hr4.
                 simpl in hr4; exact hr4.
              ** apply N.eqb_neq in hk2.
                 split; [| discriminate].
                 intros m' ls' rs' h; injection h as <- <- <-.
                 destruct (pushL1C_sound _ 2 false (k - 2) ltac:(lia) hPL1) as [heL2 hPL2].
                 destruct (pushL1C_sound _ 0 false 1 ltac:(simpl; lia) hPL2) as [heL' hPL'].
                 destruct (pushR1C_sound rest 3 0 1 ltac:(simpl; lia) hPrest) as [heR' hPR'].
                 refine (conj hPL' (conj hPR' _)).
                 rewrite heL', heL2, heL1, heR'; simpl.
                 replace (N.to_nat (k - 2)) with (N.to_nat k - 2) by lia.
                 exact (rule_A4 (N.to_nat k) ltac:(lia) (expandL ls) (expandR rest)).
    + (* RTwo *)
      destruct (N.eqb o1 0 && N.eqb o2 0) eqn:ho0; simpl negb; [| exact hfb].
      apply andb_true_iff in ho0 as [ho1 ho2]; apply N.eqb_eq in ho1; apply N.eqb_eq in ho2; subst.
      destruct (N.eqb z1 2 && N.eqb z2 0 && N.leb 1 k) eqn:ha2a.
      * repeat rewrite andb_true_iff in ha2a; destruct ha2a as [[hz1 hz2] hk].
        apply N.eqb_eq in hz1; apply N.eqb_eq in hz2; apply N.leb_le in hk; subst.
        split; [| discriminate].
        intros m' ls' rs' h; injection h as <- <- <-.
        destruct (pushL2_sound ls 2 false 0 false k hPL) as [heL' hPL'].
        refine (conj hPL' (conj hPrest _)).
        rewrite heL'; simpl.
        exact (rule_A2a (N.to_nat k) ltac:(lia) (expandL ls) (expandR rest)).
      * destruct (N.eqb z1 0 && N.eqb z2 2 && N.leb 2 k) eqn:ha2b; [| exact hfb].
        repeat rewrite andb_true_iff in ha2b; destruct ha2b as [[hz1 hz2] hk].
        apply N.eqb_eq in hz1; apply N.eqb_eq in hz2; apply N.leb_le in hk; subst.
        split; [| discriminate].
        intros m' ls' rs' h; injection h as <- <- <-.
        destruct (pushL1C_sound ls 0 false 1 ltac:(simpl; lia) hPL) as [heL1 hPL1].
        destruct (pushL2_sound _ 2 false 0 false (k - 1) hPL1) as [heL' hPL'].
        destruct (pushR1C_sound rest 2 0 1 ltac:(simpl; lia) hPrest) as [heR' hPR'].
        refine (conj hPL' (conj hPR' _)).
        rewrite heL', heL1, heR'; simpl.
        replace (N.to_nat (k - 1)) with (N.to_nat k - 1) by lia.
        exact (rule_A2b (N.to_nat k) ltac:(lia) (expandL ls) (expandR rest)).
  - (* mEL *)
    simpl stepRLEK.
    destruct rs as [|[z1 o1 k | z1 o1 z2 o2 k] rest]; [exact hfb | |].
    + destruct (N.eqb z1 1 && N.eqb o1 0); [exact (tryELBulkK_sound ls _ hPL hPR) | exact hfb].
    + destruct (N.eqb z1 1 && N.eqb o1 0); [exact (tryELBulkK_sound ls _ hPL hPR) | exact hfb].
Qed.

Lemma iter_stepBind_halted (n : N) : N.iter n stepBind SRHalted = SRHalted.
Proof.
  pattern n; apply N.peano_ind; [reflexivity | intros k IH; rewrite N.iter_succ, IH; reflexivity].
Qed.

Lemma iter_stepBind_err (n : N) : N.iter n stepBind SRErr = SRErr.
Proof.
  pattern n; apply N.peano_ind; [reflexivity | intros k IH; rewrite N.iter_succ, IH; reflexivity].
Qed.

Lemma runRLEK_sound (n : N) :
  forall (m : SegMode) (ls : list LRun) (rs : list RRun),
    PosL ls -> PosR rs ->
    (forall m' ls' rs', runRLEK n m ls rs = SROk m' ls' rs' ->
      PosL ls' /\ PosR rs' /\
        evalSegCfg m (expandL ls) (expandR rs) -[ tm ]->*
          evalSegCfg m' (expandL ls') (expandR rs')) /\
    (runRLEK n m ls rs = SRHalted -> halts tm (evalSegCfg m (expandL ls) (expandR rs))).
Proof.
  pattern n; apply N.peano_ind; clear n.
  - intros m ls rs hPL hPR; unfold runRLEK; simpl N.iter.
    split; [| discriminate].
    intros m' ls' rs' h; injection h as <- <- <-.
    exact (conj hPL (conj hPR (evstep_refl tm _))).
  - intros n IH m ls rs hPL hPR.
    unfold runRLEK. rewrite N_iter_succ_r. simpl stepBind.
    pose proof (stepRLEK_sound m ls rs hPL hPR) as [hstep_ok hstep_halt].
    destruct (stepRLEK m ls rs) as [m1 ls1 rs1 | |] eqn:hs.
    + fold (runRLEK n m1 ls1 rs1).
      destruct (hstep_ok m1 ls1 rs1 eq_refl) as [hPL1 [hPR1 h1]].
      destruct (IH m1 ls1 rs1 hPL1 hPR1) as [ih_ok ih_halt].
      split.
      * intros m' ls' rs' h.
        destruct (ih_ok m' ls' rs' h) as [hPL' [hPR' h2]].
        refine (conj hPL' (conj hPR' _)).
        exact (evstep_trans tm _ _ _ (progress_evstep _ _ _ h1) h2).
      * intros h.
        exact (halts_evstep tm _ _ (ih_halt h) (progress_evstep _ _ _ h1)).
    + rewrite iter_stepBind_halted.
      split; [intros; discriminate | intros _; exact (hstep_halt eq_refl)].
    + rewrite iter_stepBind_err.
      split; intros; discriminate.
Qed.

(* ========================================================================= *)
(* Section 5b: prePostK & carryWFuel Soundness                               *)
(* ========================================================================= *)

Lemma prePostK_eq (k : N) :
  prePostK k = (N.of_nat (preVal (N.to_nat k)), N.of_nat (postVal (N.to_nat k))).
Proof.
  pattern k; apply N.peano_ind; clear k.
  - reflexivity.
  - intros k IH.
    unfold prePostK; rewrite N.iter_succ; fold (prePostK k).
    rewrite IH, N2Nat.inj_succ, preVal_S, postVal_S.
    unfold prePostStep. f_equal; lia.
Qed.

Lemma carryW_fuel_sound_aux :
  forall (n : nat) (w : list bool), length w <= n ->
  forall (fuel : N) (w_out : list bool) (extra : N) (fn : nat -> list (nat * bool)),
    carryWFuel w fuel = CROk w_out extra ->
    (forall t, fn t <> []) ->
    P24N (N.to_nat fuel + N.to_nat extra) fn ->
    exists gn : nat -> list (nat * bool),
      Step4 (encW w ++ fn 0) (gn 0) /\
      P24N (N.to_nat fuel) gn /\
      gn (N.to_nat fuel) = encW w_out ++ fn (N.to_nat fuel + N.to_nat extra).
Proof.
  induction n as [|n IH]; intros w hw fuel w_out extra fn hc hFne hF.
  - destruct w; [discriminate | simpl in hw; lia].
  - destruct w as [|[|] rest]; [discriminate | |].
    + (* true :: rest *)
      destruct rest as [|[|] u]; [discriminate | |].
      * (* true :: true :: u *)
        simpl in hc; injection hc as <- <-.
        exists (fun t => encW (false :: false :: u) ++ fn (t + 2)).
        split; [| split].
        -- simpl encW; simpl app.
           exact (step4_22 (proj2 (p24_append_w u (hF 0 ltac:(lia))))
                           (proj1 (p24_append_w u (hF 1 ltac:(lia))))).
        -- intros t ht.
           replace (t + 1 + 2) with ((t + 2) + 1) by lia.
           exact (p24_append_w (false :: false :: u) (hF (t + 2) ltac:(lia))).
        -- simpl (N.to_nat 2). reflexivity.
      * (* true :: false :: u *)
        simpl carryWFuel in hc.
        destruct (N.eqb fuel 0) eqn:hf0; [discriminate |].
        apply N.eqb_neq in hf0.
        destruct (carryWFuel u (fuel - 1)) as [u' e |] eqn:hcu; [| discriminate].
        injection hc as <- <-.
        assert (hulen : length u <= n) by (simpl in hw; lia).
        destruct (IH u hulen (fuel - 1)%N u' e (fun t => fn (t + 1)) hcu
          (fun t => hFne (t + 1))
          (fun t ht => ltac:(replace (t + 1 + 1) with ((t + 1) + 1) by lia; apply hF; lia)))
          as [gu [hS4u [hPgu hguf]]].
        assert (hu1_ne : encW u ++ fn 1 <> []).
        { intros h0. apply app_eq_nil in h0 as [_ h0]; exact (hFne 1 h0). }
        exists (fun t =>
          match t with
          | 0 => (0, false) :: (2, false) :: bump2 (encW u ++ fn 1)
          | S t' => (0, false) :: (2, false) :: gu t'
          end).
        split; [| split].
        -- simpl. exact (step4_20 (proj1 (p24_append_w u (hF 0 ltac:(lia)))) hu1_ne).
        -- intros t ht. destruct t as [|t'].
           ++ simpl. exact (p24_cons0 (p24_cons2 (p24_of_step4 hu1_ne hS4u))).
           ++ replace (S t' + 1) with (S (t' + 1)) by lia.
              exact (p24_cons0 (p24_cons2 (hPgu t' ltac:(lia)))).
        -- replace (N.to_nat fuel) with (S (N.to_nat (fuel - 1))) at 1 by lia.
           simpl. rewrite hguf. f_equal; f_equal; f_equal; f_equal. lia.
    + (* false :: rest *)
      simpl in hc; injection hc as <- <-.
      exists (fun t => encW (true :: rest) ++ fn (t + 1)).
      split; [| split].
      * simpl. exact (step4_0 (proj2 (p24_append_w rest (hF 0 ltac:(lia))))).
      * intros t ht. exact (p24_append_w (true :: rest) (hF (t + 1) ltac:(lia))).
      * simpl (N.to_nat 1). reflexivity.
Qed.

Lemma carryW_fuel_sound (w : list bool) (fuel : N) (w_out : list bool) (extra : N)
    (fn : nat -> list (nat * bool))
    (hc : carryWFuel w fuel = CROk w_out extra)
    (hFne : forall t, fn t <> [])
    (hF : P24N (N.to_nat fuel + N.to_nat extra) fn) :
  exists gn : nat -> list (nat * bool),
    Step4 (encW w ++ fn 0) (gn 0) /\
    P24N (N.to_nat fuel) gn /\
    gn (N.to_nat fuel) = encW w_out ++ fn (N.to_nat fuel + N.to_nat extra).
Proof.
  exact (carryW_fuel_sound_aux (length w) w (Nat.le_refl _) fuel w_out extra fn hc hFne hF).
Qed.

Lemma odom_carryW_jump (p k : nat) (w w_out : list bool) (extra : N)
    (bfn : nat -> list (nat * bool))
    (hc : carryWFuel w (N.of_nat (postVal k)) = CROk w_out extra)
    (hB : forall t, t < preVal k + postVal k + N.to_nat extra -> P2 (bfn t) (bfn (t + 1))) :
  evalSegCfg mAR0
    (repeat (0, true) p ++ repeat (0, false) (2 * (k + 1)) ++ encW w ++ (0, false) :: bfn 0) []
    -[ tm ]->*
  evalSegCfg mAR0
    (repeat (0, true) p ++ repeat (0, false) (2 * (k + 1)) ++ encW w_out ++
      (0, false) :: bfn (preVal k + postVal k + N.to_nat extra)) [].
Proof.
  set (hfn := fun t => (0, false) :: bfn t).
  assert (hHP : P24N (preVal k + postVal k + N.to_nat extra) hfn).
  { intros t ht. exact (p24_of_cons0 (hB t ht)). }
  destruct (carryW_fuel_sound w (N.of_nat (postVal k)) w_out extra
    (fun t => hfn (preVal k + t)) hc
    (fun t => cons_neq_nil _ _)
    (fun t ht => ltac:(cbv beta; replace (preVal k + (t + 1)) with ((preVal k + t) + 1) by lia;
                       apply hHP; lia)))
    as [gn [hS4 [hPG hGend]]].
  rewrite Nat2N.id in hPG, hGend.
  replace (preVal k + 0) with (preVal k) in hS4 by lia.
  assert (hFne : encW w ++ hfn (preVal k) <> []).
  { intros h0. apply app_eq_nil in h0 as [_ h0]; exact (cons_neq_nil _ _ h0). }
  pose proof (odom_master p k (fun t => encW w ++ hfn t) gn hFne
    (@p24N_append_w w (preVal k) hfn (fun t ht => hHP t ltac:(lia)))
    hS4 hPG) as hmain.
  cbv beta in hmain.
  rewrite hGend in hmain.
  replace (preVal k + (postVal k + N.to_nat extra)) with
    (preVal k + postVal k + N.to_nat extra) in hmain by lia.
  unfold hfn in hmain.
  repeat rewrite <- app_assoc in hmain |- *.
  exact hmain.
Qed.

Local Close Scope sym_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Arguments evalSegCfg : simpl never.
Arguments evalA : simpl never.

(* ========================================================================= *)
(* Section 6: Symbolic RLE & Odometer Jump Soundness                         *)
(* ========================================================================= *)

Definition evalSC (t Tmax : nat) (c : SymCnt) : nat :=
  match c with
  | SCConst a => N.to_nat a
  | SCInc a d => N.to_nat a + t * N.to_nat d
  | SCDec a d => N.to_nat a + (Tmax - t) * N.to_nat d
  end.

Definition evalSLRun (t Tmax : nat) (r : SLRun) : list (nat * bool) :=
  match r with
  | SLOne d b c => repeat (N.to_nat d, b) (evalSC t Tmax c)
  | SLTwo d1 b1 d2 b2 c => repPair (N.to_nat d1, b1) (N.to_nat d2, b2) (evalSC t Tmax c)
  end.

Fixpoint evalSL (t Tmax : nat) (ls : list SLRun) : list (nat * bool) :=
  match ls with
  | [] => []
  | r :: rs => evalSLRun t Tmax r ++ evalSL t Tmax rs
  end.

Definition evalSRRun (t Tmax : nat) (r : SRRun) : list (nat * nat) :=
  match r with
  | SROne z o c => repeat (N.to_nat z, N.to_nat o) (evalSC t Tmax c)
  | SRTwo z1 o1 z2 o2 c => repPair (N.to_nat z1, N.to_nat o1) (N.to_nat z2, N.to_nat o2) (evalSC t Tmax c)
  end.

Fixpoint evalSR (t Tmax : nat) (rs : list SRRun) : list (nat * nat) :=
  match rs with
  | [] => []
  | r :: rest => evalSRRun t Tmax r ++ evalSR t Tmax rest
  end.

Definition PosSLRun (r : SLRun) : Prop :=
  match r with
  | SLOne _ _ c => 1 <= N.to_nat (scBase c)
  | SLTwo _ _ _ _ c => 1 <= N.to_nat (scBase c)
  end.

Fixpoint PosSL (ls : list SLRun) : Prop :=
  match ls with
  | [] => True
  | r :: rs => PosSLRun r /\ PosSL rs
  end.

Definition PosSRRun (r : SRRun) : Prop :=
  match r with
  | SROne _ _ c => 1 <= N.to_nat (scBase c)
  | SRTwo _ _ _ _ c => 1 <= N.to_nat (scBase c)
  end.

Fixpoint PosSR (rs : list SRRun) : Prop :=
  match rs with
  | [] => True
  | r :: rest => PosSRRun r /\ PosSR rest
  end.

Lemma scBase_le_evalSC (t Tmax : nat) (c : SymCnt) :
  N.to_nat (scBase c) <= evalSC t Tmax c.
Proof.
  destruct c; simpl; nia.
Qed.

Lemma scIs0_eq {c : SymCnt} (h : scIs0 c = true) : c = SCConst 0.
Proof.
  destruct c; simpl in h; try discriminate.
  apply N.eqb_eq in h; subst; reflexivity.
Qed.

Lemma scIs1_eq {c : SymCnt} (h : scIs1 c = true) : c = SCConst 1.
Proof.
  destruct c; simpl in h; try discriminate.
  apply N.eqb_eq in h; subst; reflexivity.
Qed.

Lemma scIs2_eq {c : SymCnt} (h : scIs2 c = true) : c = SCConst 2.
Proof.
  destruct c; simpl in h; try discriminate.
  apply N.eqb_eq in h; subst; reflexivity.
Qed.

Lemma scSub_base (c : SymCnt) (k : N) :
  N.to_nat (scBase (scSub c k)) = N.to_nat (scBase c) - N.to_nat k.
Proof.
  destruct c; simpl; lia.
Qed.

Lemma evalSC_scSub (t Tmax : nat) (c : SymCnt) (k : N)
    (hk : N.to_nat k <= N.to_nat (scBase c)) :
  evalSC t Tmax (scSub c k) = evalSC t Tmax c - N.to_nat k.
Proof.
  destruct c; simpl in hk |- *; nia.
Qed.

Lemma scAdd_sound {c1 c2 s : SymCnt} (h : scAdd c1 c2 = Some s) :
  N.to_nat (scBase s) = N.to_nat (scBase c1) + N.to_nat (scBase c2) /\
  forall t Tmax, evalSC t Tmax s = evalSC t Tmax c1 + evalSC t Tmax c2.
Proof.
  destruct c1 as [a1 | a1 d1 | a1 d1], c2 as [a2 | a2 d2 | a2 d2];
    simpl in h; try discriminate; injection h as <-; simpl;
    (split; [lia | intros t Tmax; repeat rewrite N2Nat.inj_add; try rewrite Nat.mul_add_distr_l; lia]).
Qed.

Lemma evalSL_nil_of_pos {t Tmax : nat} {ls : list SLRun}
    (hPos : PosSL ls) (h : evalSL t Tmax ls = []) : ls = [].
Proof.
  destruct ls as [|[d b c | d1 b1 d2 b2 c] rs]; [reflexivity | |].
  - destruct hPos as [hr _]; simpl in hr, h.
    pose proof (scBase_le_evalSC t Tmax c) as hge.
    destruct (evalSC t Tmax c) as [|k]; [lia | simpl in h; discriminate].
  - destruct hPos as [hr _]; simpl in hr, h.
    pose proof (scBase_le_evalSC t Tmax c) as hge.
    destruct (evalSC t Tmax c) as [|k]; [lia | simpl in h; discriminate].
Qed.

Lemma foldSLStep_sound (next : list SLRun -> option (list SLRun))
    (hnext : forall ls ls', next ls = Some ls' -> PosSL ls ->
      PosSL ls' /\ forall t Tmax, evalSL t Tmax ls' = evalSL t Tmax ls) :
  forall ls ls', foldSLStep next ls = Some ls' -> PosSL ls ->
    PosSL ls' /\ forall t Tmax, evalSL t Tmax ls' = evalSL t Tmax ls.
Proof.
  intros ls ls' h hPos.
  unfold foldSLStep in h.
  destruct ls as [|r1 rest1]; [injection h as <-; exact (conj hPos (fun _ _ => eq_refl)) |].
  destruct rest1 as [|r2 rest]; [destruct r1; injection h as <-; exact (conj hPos (fun _ _ => eq_refl)) |].
  destruct hPos as [hP1 [hP2 hPrest]].
  destruct r1 as [d1 b1 c1 | d1 b1 d2 b2 c1].
  - (* SLOne *)
    destruct r2 as [d2 b2 c2 | ? ? ? ? ?].
    + simpl foldSLStep in h.
      destruct (N.eqb d1 d2 && Bool.eqb b1 b2) eqn:hm.
      * apply andb_true_iff in hm as [hd hb]; apply N.eqb_eq in hd; apply bool_eqb_eq in hb; subst.
        destruct (scAdd c1 c2) as [s |] eqn:ha; [| discriminate].
        destruct (scAdd_sound ha) as [hb he].
        assert (hPmid : PosSL (SLOne d2 b2 s :: rest)).
        { simpl in hP1, hP2 |- *; split; [lia | exact hPrest]. }
        destruct (hnext _ _ h hPmid) as [hP' he'].
        refine (conj hP' (fun t Tmax => _)).
        rewrite (he' t Tmax); simpl.
        rewrite (he t Tmax), repeat_add, <- app_assoc. reflexivity.
      * destruct (scIs1 c1 && scIs1 c2) eqn:h11.
        -- apply andb_true_iff in h11 as [hc1 hc2].
           pose proof (scIs1_eq hc1) as ->; pose proof (scIs1_eq hc2) as ->.
           destruct rest as [|r3 rest2].
           ++ injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)).
           ++ destruct r3 as [d3 b3 c3 | td1 tb1 td2 tb2 tc].
              ** destruct rest2 as [|r4 rest3].
                 { injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)). }
                 destruct r4 as [d4 b4 c4 | ? ? ? ? ?].
                 { destruct hPrest as [hP3 [hP4 hPr3]].
                   destruct (scIs1 c3 && scIs1 c4 &&
                             N.eqb d1 d3 && Bool.eqb b1 b3 && N.eqb d2 d4 && Bool.eqb b2 b4) eqn:h4m.
                   - repeat rewrite andb_true_iff in h4m.
                     destruct h4m as [[[[[hc3 hc4] hd13] hb13] hd24] hb24].
                     pose proof (scIs1_eq hc3) as ->; pose proof (scIs1_eq hc4) as ->.
                     apply N.eqb_eq in hd13; apply bool_eqb_eq in hb13;
                     apply N.eqb_eq in hd24; apply bool_eqb_eq in hb24; subst.
                     assert (hPmid : PosSL (SLTwo d3 b3 d4 b4 (SCConst 2) :: rest3)).
                     { simpl; split; [lia | exact hPr3]. }
                     destruct (hnext _ _ h hPmid) as [hP' he'].
                     refine (conj hP' (fun t Tmax => _)).
                     rewrite (he' t Tmax). reflexivity.
                   - injection h as <-; exact (conj (conj hP1 (conj hP2 (conj hP3 (conj hP4 hPr3)))) (fun _ _ => eq_refl)). }
                 { injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)). }
              ** destruct hPrest as [hP3 hPr2].
                 destruct (N.eqb td1 d1 && Bool.eqb tb1 b1 && N.eqb td2 d2 && Bool.eqb tb2 b2) eqn:htm.
                 { repeat rewrite andb_true_iff in htm.
                   destruct htm as [[[hd1 hb1] hd2] hb2].
                   apply N.eqb_eq in hd1; apply bool_eqb_eq in hb1;
                   apply N.eqb_eq in hd2; apply bool_eqb_eq in hb2; subst.
                   destruct (scAdd tc (SCConst 1)) as [s |] eqn:ha; [| discriminate].
                   destruct (scAdd_sound ha) as [hb he].
                   assert (hPmid : PosSL (SLTwo d1 b1 d2 b2 s :: rest2)).
                   { simpl in hP3 |- *; split; [lia | exact hPr2]. }
                   destruct (hnext _ _ h hPmid) as [hP' he'].
                   refine (conj hP' (fun t Tmax => _)).
                   rewrite (he' t Tmax); simpl evalSL; simpl evalSLRun.
                   replace (evalSC t Tmax s) with (S (evalSC t Tmax tc))
                     by (rewrite (he t Tmax); simpl; lia).
                   reflexivity. }
                 { injection h as <-; exact (conj (conj hP1 (conj hP2 (conj hP3 hPr2))) (fun _ _ => eq_refl)). }
        -- injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)).
    + simpl in h; injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)).
  - (* SLTwo *)
    destruct r2 as [? ? ? | d1' b1' d2' b2' c2].
    + simpl in h; injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)).
    + simpl foldSLStep in h.
      destruct (N.eqb d1 d1' && Bool.eqb b1 b1' && N.eqb d2 d2' && Bool.eqb b2 b2') eqn:hm.
      * repeat rewrite andb_true_iff in hm.
        destruct hm as [[[hd1 hb1] hd2] hb2].
        apply N.eqb_eq in hd1; apply bool_eqb_eq in hb1;
        apply N.eqb_eq in hd2; apply bool_eqb_eq in hb2; subst.
        destruct (scAdd c1 c2) as [s |] eqn:ha; [| discriminate].
        destruct (scAdd_sound ha) as [hb he].
        assert (hPmid : PosSL (SLTwo d1' b1' d2' b2' s :: rest)).
        { simpl in hP1, hP2 |- *; split; [lia | exact hPrest]. }
        destruct (hnext _ _ h hPmid) as [hP' he'].
        refine (conj hP' (fun t Tmax => _)).
        rewrite (he' t Tmax); simpl.
        rewrite (he t Tmax), repPair_add, <- app_assoc. reflexivity.
      * injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)).
Qed.

Lemma foldSL3_sound {ls ls' : list SLRun} (h : foldSL3 ls = Some ls') (hPos : PosSL ls) :
  PosSL ls' /\ forall t Tmax, evalSL t Tmax ls' = evalSL t Tmax ls.
Proof.
  unfold foldSL3 in h.
  eapply foldSLStep_sound; [| exact h | exact hPos].
  intros x x' hx hPx; eapply foldSLStep_sound; [| exact hx | exact hPx].
  intros y y' hy hPy; eapply foldSLStep_sound; [| exact hy | exact hPy].
  intros z z' hz hPz; injection hz as <-; exact (conj hPz (fun _ _ => eq_refl)).
Qed.

Lemma foldSRStep_sound (next : list SRRun -> option (list SRRun))
    (hnext : forall rs rs', next rs = Some rs' -> PosSR rs ->
      PosSR rs' /\ forall t Tmax, evalSR t Tmax rs' = evalSR t Tmax rs) :
  forall rs rs', foldSRStep next rs = Some rs' -> PosSR rs ->
    PosSR rs' /\ forall t Tmax, evalSR t Tmax rs' = evalSR t Tmax rs.
Proof.
  intros rs rs' h hPos.
  unfold foldSRStep in h.
  destruct rs as [|r1 rest1]; [injection h as <-; exact (conj hPos (fun _ _ => eq_refl)) |].
  destruct rest1 as [|r2 rest]; [destruct r1; injection h as <-; exact (conj hPos (fun _ _ => eq_refl)) |].
  destruct hPos as [hP1 [hP2 hPrest]].
  destruct r1 as [z1 o1 c1 | z1 o1 z2 o2 c1].
  - (* SROne *)
    destruct r2 as [z2 o2 c2 | ? ? ? ? ?].
    + simpl foldSRStep in h.
      destruct (N.eqb z1 z2 && N.eqb o1 o2) eqn:hm.
      * apply andb_true_iff in hm as [hz ho]; apply N.eqb_eq in hz; apply N.eqb_eq in ho; subst.
        destruct (scAdd c1 c2) as [s |] eqn:ha; [| discriminate].
        destruct (scAdd_sound ha) as [hb he].
        assert (hPmid : PosSR (SROne z2 o2 s :: rest)).
        { simpl in hP1, hP2 |- *; split; [lia | exact hPrest]. }
        destruct (hnext _ _ h hPmid) as [hP' he'].
        refine (conj hP' (fun t Tmax => _)).
        rewrite (he' t Tmax); simpl.
        rewrite (he t Tmax), repeat_add, <- app_assoc. reflexivity.
      * destruct (scIs1 c1 && scIs1 c2) eqn:h11.
        -- apply andb_true_iff in h11 as [hc1 hc2].
           pose proof (scIs1_eq hc1) as ->; pose proof (scIs1_eq hc2) as ->.
           destruct rest as [|r3 rest2].
           ++ injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)).
           ++ destruct r3 as [z3 o3 c3 | tz1 to1 tz2 to2 tc].
              ** destruct rest2 as [|r4 rest3].
                 { injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)). }
                 destruct r4 as [z4 o4 c4 | ? ? ? ? ?].
                 { destruct hPrest as [hP3 [hP4 hPr3]].
                   destruct (scIs1 c3 && scIs1 c4 &&
                             N.eqb z1 z3 && N.eqb o1 o3 && N.eqb z2 z4 && N.eqb o2 o4) eqn:h4m.
                   - repeat rewrite andb_true_iff in h4m.
                     destruct h4m as [[[[[hc3 hc4] hz13] ho13] hz24] ho24].
                     pose proof (scIs1_eq hc3) as ->; pose proof (scIs1_eq hc4) as ->.
                     apply N.eqb_eq in hz13; apply N.eqb_eq in ho13;
                     apply N.eqb_eq in hz24; apply N.eqb_eq in ho24; subst.
                     assert (hPmid : PosSR (SRTwo z3 o3 z4 o4 (SCConst 2) :: rest3)).
                     { simpl; split; [lia | exact hPr3]. }
                     destruct (hnext _ _ h hPmid) as [hP' he'].
                     refine (conj hP' (fun t Tmax => _)).
                     rewrite (he' t Tmax). reflexivity.
                   - injection h as <-; exact (conj (conj hP1 (conj hP2 (conj hP3 (conj hP4 hPr3)))) (fun _ _ => eq_refl)). }
                 { injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)). }
              ** destruct hPrest as [hP3 hPr2].
                 destruct (N.eqb tz1 z1 && N.eqb to1 o1 && N.eqb tz2 z2 && N.eqb to2 o2) eqn:htm.
                 { repeat rewrite andb_true_iff in htm.
                   destruct htm as [[[hz1 ho1] hz2] ho2].
                   apply N.eqb_eq in hz1; apply N.eqb_eq in ho1;
                   apply N.eqb_eq in hz2; apply N.eqb_eq in ho2; subst.
                   destruct (scAdd tc (SCConst 1)) as [s |] eqn:ha; [| discriminate].
                   destruct (scAdd_sound ha) as [hb he].
                   assert (hPmid : PosSR (SRTwo z1 o1 z2 o2 s :: rest2)).
                   { simpl in hP3 |- *; split; [lia | exact hPr2]. }
                   destruct (hnext _ _ h hPmid) as [hP' he'].
                   refine (conj hP' (fun t Tmax => _)).
                   rewrite (he' t Tmax); simpl evalSR; simpl evalSRRun.
                   replace (evalSC t Tmax s) with (S (evalSC t Tmax tc))
                     by (rewrite (he t Tmax); simpl; lia).
                   reflexivity. }
                 { injection h as <-; exact (conj (conj hP1 (conj hP2 (conj hP3 hPr2))) (fun _ _ => eq_refl)). }
        -- injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)).
    + simpl in h; injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)).
  - (* SRTwo *)
    destruct r2 as [? ? ? | z1' o1' z2' o2' c2].
    + simpl in h; injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)).
    + simpl foldSRStep in h.
      destruct (N.eqb z1 z1' && N.eqb o1 o1' && N.eqb z2 z2' && N.eqb o2 o2') eqn:hm.
      * repeat rewrite andb_true_iff in hm.
        destruct hm as [[[hz1 ho1] hz2] ho2].
        apply N.eqb_eq in hz1; apply N.eqb_eq in ho1;
        apply N.eqb_eq in hz2; apply N.eqb_eq in ho2; subst.
        destruct (scAdd c1 c2) as [s |] eqn:ha; [| discriminate].
        destruct (scAdd_sound ha) as [hb he].
        assert (hPmid : PosSR (SRTwo z1' o1' z2' o2' s :: rest)).
        { simpl in hP1, hP2 |- *; split; [lia | exact hPrest]. }
        destruct (hnext _ _ h hPmid) as [hP' he'].
        refine (conj hP' (fun t Tmax => _)).
        rewrite (he' t Tmax); simpl.
        rewrite (he t Tmax), repPair_add, <- app_assoc. reflexivity.
      * injection h as <-; exact (conj (conj hP1 (conj hP2 hPrest)) (fun _ _ => eq_refl)).
Qed.

Lemma foldSR3_sound {rs rs' : list SRRun} (h : foldSR3 rs = Some rs') (hPos : PosSR rs) :
  PosSR rs' /\ forall t Tmax, evalSR t Tmax rs' = evalSR t Tmax rs.
Proof.
  unfold foldSR3 in h.
  eapply foldSRStep_sound; [| exact h | exact hPos].
  intros x x' hx hPx; eapply foldSRStep_sound; [| exact hx | exact hPx].
  intros y y' hy hPy; eapply foldSRStep_sound; [| exact hy | exact hPy].
  intros z z' hz hPz; injection hz as <-; exact (conj hPz (fun _ _ => eq_refl)).
Qed.

Lemma pushSL1_sound {ls ls' : list SLRun} {d : N} {b : bool} {c : SymCnt}
    (h : pushSL1 ls d b c = Some ls') (hc : 1 <= N.to_nat (scBase c)) (hPos : PosSL ls) :
  PosSL ls' /\
  forall t Tmax, evalSL t Tmax ls' = repeat (N.to_nat d, b) (evalSC t Tmax c) ++ evalSL t Tmax ls.
Proof.
  unfold pushSL1 in h.
  destruct (scIs0 c) eqn:h0.
  - pose proof (scIs0_eq h0) as ->; simpl in hc; lia.
  - exact (foldSL3_sound h (conj hc hPos)).
Qed.

Lemma pushSL2_sound {ls ls' : list SLRun} {d1 : N} {b1 : bool} {d2 : N} {b2 : bool} {c : SymCnt}
    (h : pushSL2 ls d1 b1 d2 b2 c = Some ls') (hc : 1 <= N.to_nat (scBase c)) (hPos : PosSL ls) :
  PosSL ls' /\
  forall t Tmax,
    evalSL t Tmax ls' = repPair (N.to_nat d1, b1) (N.to_nat d2, b2) (evalSC t Tmax c) ++ evalSL t Tmax ls.
Proof.
  unfold pushSL2 in h.
  destruct (scIs0 c) eqn:h0.
  - pose proof (scIs0_eq h0) as ->; simpl in hc; lia.
  - exact (foldSL3_sound h (conj hc hPos)).
Qed.

Lemma pushSR1_sound {rs rs' : list SRRun} {z o : N} {c : SymCnt}
    (h : pushSR1 rs z o c = Some rs') (hc : 1 <= N.to_nat (scBase c)) (hPos : PosSR rs) :
  PosSR rs' /\
  forall t Tmax, evalSR t Tmax rs' = repeat (N.to_nat z, N.to_nat o) (evalSC t Tmax c) ++ evalSR t Tmax rs.
Proof.
  unfold pushSR1 in h.
  destruct (scIs0 c) eqn:h0.
  - pose proof (scIs0_eq h0) as ->; simpl in hc; lia.
  - exact (foldSR3_sound h (conj hc hPos)).
Qed.

Lemma pushSR2_sound {rs rs' : list SRRun} {z1 o1 z2 o2 : N} {c : SymCnt}
    (h : pushSR2 rs z1 o1 z2 o2 c = Some rs') (hc : 1 <= N.to_nat (scBase c)) (hPos : PosSR rs) :
  PosSR rs' /\
  forall t Tmax,
    evalSR t Tmax rs' = repPair (N.to_nat z1, N.to_nat o1) (N.to_nat z2, N.to_nat o2) (evalSC t Tmax c) ++ evalSR t Tmax rs.
Proof.
  unfold pushSR2 in h.
  destruct (scIs0 c) eqn:h0.
  - pose proof (scIs0_eq h0) as ->; simpl in hc; lia.
  - exact (foldSR3_sound h (conj hc hPos)).
Qed.

Lemma popSL_ok_sound {ls rest : list SLRun} {d : N} {b : bool}
    (h : popSL ls = PSLOk d b rest) (hPos : PosSL ls) :
  PosSL rest /\ forall t Tmax, evalSL t Tmax ls = (N.to_nat d, b) :: evalSL t Tmax rest.
Proof.
  destruct ls as [|[dr br c | d1 b1 d2 b2 c] rs]; [discriminate | |];
    destruct hPos as [hPr hPrs]; simpl popSL in h.
  - destruct (scIs1 c) eqn:h1.
    + pose proof (scIs1_eq h1) as ->; injection h as <- <- <-.
      exact (conj hPrs (fun _ _ => eq_refl)).
    + destruct (N.leb 2 (scBase c)) eqn:h2; [| discriminate].
      apply N.leb_le in h2. injection h as <- <- <-.
      split.
      * simpl; rewrite scSub_base; split; [lia | exact hPrs].
      * intros t Tmax.
        pose proof (scBase_le_evalSC t Tmax c) as hge.
        simpl evalSL; simpl evalSLRun.
        rewrite (evalSC_scSub t Tmax c 1 ltac:(lia)).
        replace (evalSC t Tmax c) with (S (evalSC t Tmax c - 1)) at 1 by lia.
        reflexivity.
  - destruct (scIs1 c) eqn:h1.
    + pose proof (scIs1_eq h1) as ->.
      destruct (pushSL1 rs d2 b2 (SCConst 1)) as [rest' |] eqn:hp; [| discriminate].
      injection h as <- <- <-.
      destruct (pushSL1_sound hp ltac:(simpl; lia) hPrs) as [hP' he'].
      refine (conj hP' (fun t Tmax => _)).
      rewrite (he' t Tmax). reflexivity.
    + destruct (N.leb 2 (scBase c)) eqn:h2; [| discriminate].
      apply N.leb_le in h2. injection h as <- <- <-.
      split.
      * simpl; rewrite scSub_base; split; [lia | split; [lia | exact hPrs]].
      * intros t Tmax.
        pose proof (scBase_le_evalSC t Tmax c) as hge.
        simpl evalSL; simpl evalSLRun.
        rewrite (evalSC_scSub t Tmax c 1 ltac:(lia)).
        replace (evalSC t Tmax c) with (S (evalSC t Tmax c - 1)) at 1 by lia.
        reflexivity.
Qed.

Lemma popSR_ok_sound {rs rest : list SRRun} {z o : N}
    (h : popSR rs = PSROk z o rest) (hPos : PosSR rs) :
  PosSR rest /\ forall t Tmax, evalSR t Tmax rs = (N.to_nat z, N.to_nat o) :: evalSR t Tmax rest.
Proof.
  destruct rs as [|[zr or_ c | z1 o1 z2 o2 c] rrest]; [discriminate | |];
    destruct hPos as [hPr hPrs]; simpl popSR in h.
  - destruct (scIs1 c) eqn:h1.
    + pose proof (scIs1_eq h1) as ->; injection h as <- <- <-.
      exact (conj hPrs (fun _ _ => eq_refl)).
    + destruct (N.leb 2 (scBase c)) eqn:h2; [| discriminate].
      apply N.leb_le in h2. injection h as <- <- <-.
      split.
      * simpl; rewrite scSub_base; split; [lia | exact hPrs].
      * intros t Tmax.
        pose proof (scBase_le_evalSC t Tmax c) as hge.
        simpl evalSR; simpl evalSRRun.
        rewrite (evalSC_scSub t Tmax c 1 ltac:(lia)).
        replace (evalSC t Tmax c) with (S (evalSC t Tmax c - 1)) at 1 by lia.
        reflexivity.
  - destruct (scIs1 c) eqn:h1.
    + pose proof (scIs1_eq h1) as ->.
      destruct (pushSR1 rrest z2 o2 (SCConst 1)) as [rest' |] eqn:hp; [| discriminate].
      injection h as <- <- <-.
      destruct (pushSR1_sound hp ltac:(simpl; lia) hPrs) as [hP' he'].
      refine (conj hP' (fun t Tmax => _)).
      rewrite (he' t Tmax). reflexivity.
    + destruct (N.leb 2 (scBase c)) eqn:h2; [| discriminate].
      apply N.leb_le in h2. injection h as <- <- <-.
      split.
      * simpl; rewrite scSub_base; split; [lia | split; [lia | exact hPrs]].
      * intros t Tmax.
        pose proof (scBase_le_evalSC t Tmax c) as hge.
        simpl evalSR; simpl evalSRRun.
        rewrite (evalSC_scSub t Tmax c 1 ltac:(lia)).
        replace (evalSC t Tmax c) with (S (evalSC t Tmax c - 1)) at 1 by lia.
        reflexivity.
Qed.

Lemma splitOnesSL_sound (ls : list SLRun) (hPos : PosSL ls) :
  PosSL (splitOnesSL ls) /\ forall t Tmax, evalSL t Tmax (splitOnesSL ls) = evalSL t Tmax ls.
Proof.
  induction ls as [|[d b c | d1 b1 d2 b2 c] rs IH].
  - exact (conj I (fun _ _ => eq_refl)).
  - destruct hPos as [hPr hPrs]; destruct (IH hPrs) as [ihP ihe].
    refine (conj (conj hPr ihP) (fun t Tmax => _)).
    simpl; rewrite (ihe t Tmax); reflexivity.
  - destruct hPos as [hPr hPrs]; destruct (IH hPrs) as [ihP ihe].
    simpl splitOnesSL. destruct (scIs1 c) eqn:h1.
    + pose proof (scIs1_eq h1) as ->.
      split; [simpl; split; [lia | split; [lia | exact ihP]] |].
      intros t Tmax; simpl; rewrite (ihe t Tmax); reflexivity.
    + refine (conj (conj hPr ihP) (fun t Tmax => _)).
      simpl; rewrite (ihe t Tmax); reflexivity.
Qed.

Lemma mergeConsSL_sound (r : SLRun) (ls ls' : list SLRun)
    (h : mergeConsSL r ls = Some ls') (hPr : PosSLRun r) (hPL : PosSL ls) :
  PosSL ls' /\ forall t Tmax, evalSL t Tmax ls' = evalSLRun t Tmax r ++ evalSL t Tmax ls.
Proof.
  unfold mergeConsSL in h.
  destruct ls as [|h0 rest].
  - injection h as <-; exact (conj (conj hPr I) (fun _ _ => eq_refl)).
  - destruct hPL as [hPh hPrest].
    destruct r as [d1 b1 c1 | d1 b1 d2 b2 c1].
    + destruct h0 as [d2 b2 c2 | ? ? ? ? ?].
      * simpl mergeConsSL in h.
        destruct (N.eqb d1 d2 && Bool.eqb b1 b2) eqn:hm.
        -- apply andb_true_iff in hm as [hd hb]; apply N.eqb_eq in hd; apply bool_eqb_eq in hb; subst.
           destruct (scAdd c1 c2) as [s |] eqn:ha; [| discriminate].
           injection h as <-.
           destruct (scAdd_sound ha) as [hb he].
           split; [simpl in hPr, hPh |- *; split; [lia | exact hPrest] |].
           intros t Tmax; simpl; rewrite (he t Tmax), repeat_add, <- app_assoc; reflexivity.
        -- injection h as <-; exact (conj (conj hPr (conj hPh hPrest)) (fun _ _ => eq_refl)).
      * simpl in h; injection h as <-; exact (conj (conj hPr (conj hPh hPrest)) (fun _ _ => eq_refl)).
    + destruct h0 as [? ? ? | d1' b1' d2' b2' c2].
      * simpl in h; injection h as <-; exact (conj (conj hPr (conj hPh hPrest)) (fun _ _ => eq_refl)).
      * simpl mergeConsSL in h.
        destruct (N.eqb d1 d1' && Bool.eqb b1 b1' && N.eqb d2 d2' && Bool.eqb b2 b2') eqn:hm.
        -- repeat rewrite andb_true_iff in hm.
           destruct hm as [[[hd1 hb1] hd2] hb2].
           apply N.eqb_eq in hd1; apply bool_eqb_eq in hb1;
           apply N.eqb_eq in hd2; apply bool_eqb_eq in hb2; subst.
           destruct (scAdd c1 c2) as [s |] eqn:ha; [| discriminate].
           injection h as <-.
           destruct (scAdd_sound ha) as [hb he].
           split; [simpl in hPr, hPh |- *; split; [lia | exact hPrest] |].
           intros t Tmax; simpl; rewrite (he t Tmax), repPair_add, <- app_assoc; reflexivity.
        -- injection h as <-; exact (conj (conj hPr (conj hPh hPrest)) (fun _ _ => eq_refl)).
Qed.

Lemma mergeAdjSL_sound (ls : list SLRun) :
  forall ls', mergeAdjSL ls = Some ls' -> PosSL ls ->
    PosSL ls' /\ forall t Tmax, evalSL t Tmax ls' = evalSL t Tmax ls.
Proof.
  induction ls as [|r rs IH]; intros ls' h hPos.
  - simpl in h; injection h as <-; exact (conj I (fun _ _ => eq_refl)).
  - destruct hPos as [hPr hPrs]; simpl in h.
    destruct (mergeAdjSL rs) as [rs' |] eqn:hm; [| discriminate].
    destruct (IH rs' eq_refl hPrs) as [hPrs' hers'].
    destruct (mergeConsSL_sound r rs' ls' h hPr hPrs') as [hPL' heL'].
    refine (conj hPL' (fun t Tmax => _)).
    rewrite (heL' t Tmax), (hers' t Tmax); reflexivity.
Qed.

Lemma normSL_sound {ls ls' : list SLRun} (h : normSL ls = Some ls') (hPos : PosSL ls) :
  PosSL ls' /\ forall t Tmax, evalSL t Tmax ls' = evalSL t Tmax ls.
Proof.
  unfold normSL in h.
  destruct (splitOnesSL_sound ls hPos) as [hP1 he1].
  destruct (mergeAdjSL_sound (splitOnesSL ls) ls' h hP1) as [hP2 he2].
  refine (conj hP2 (fun t Tmax => _)).
  rewrite (he2 t Tmax), (he1 t Tmax); reflexivity.
Qed.

Lemma sBumpLK_sound {ls ls' : list SLRun} (h : sBumpLK ls = Some ls') (hPos : PosSL ls) :
  PosSL ls' /\ forall t Tmax, evalSL t Tmax ls' = bumpL (evalSL t Tmax ls).
Proof.
  destruct ls as [|r rs].
  - simpl in h.
    destruct (pushSL1_sound h ltac:(simpl; lia) I) as [hP' he'].
    refine (conj hP' (fun t Tmax => _)).
    rewrite (he' t Tmax); reflexivity.
  - unfold sBumpLK in h; fold (popSL (r :: rs)) in h.
    destruct (popSL (r :: rs)) as [d b rest |] eqn:hp; [| discriminate].
    destruct (popSL_ok_sound hp hPos) as [hPrest hepop].
    destruct (pushSL1_sound h ltac:(simpl; lia) hPrest) as [hP' he'].
    refine (conj hP' (fun t Tmax => _)).
    rewrite (he' t Tmax), (hepop t Tmax); simpl.
    replace (N.to_nat (d + 1)) with (S (N.to_nat d)) by lia.
    reflexivity.
Qed.

Lemma sPush100LK_sound {ls ls' : list SLRun} (h : sPush100LK ls = Some ls') (hPos : PosSL ls) :
  PosSL ls' /\ forall t Tmax, evalSL t Tmax ls' = push100L (evalSL t Tmax ls).
Proof.
  destruct ls as [|r rs].
  - simpl in h.
    destruct (pushSL1_sound h ltac:(simpl; lia) I) as [hP' he'].
    refine (conj hP' (fun t Tmax => _)).
    rewrite (he' t Tmax); reflexivity.
  - simpl in h.
    destruct (pushSL1_sound h ltac:(simpl; lia) hPos) as [hP' he'].
    refine (conj hP' (fun t Tmax => _)).
    rewrite (he' t Tmax).
    assert (hne : evalSL t Tmax (r :: rs) <> []).
    { intros h0. pose proof (evalSL_nil_of_pos hPos h0); discriminate. }
    destruct (evalSL t Tmax (r :: rs)) as [|p xs]; [contradiction | reflexivity].
Qed.

Lemma sPush0RK_sound {rs rs' : list SRRun} {k : N}
    (h : sPush0RK rs k = Some rs') (hPos : PosSR rs) :
  PosSR rs' /\
  forall t Tmax R_tail,
    evalSR t Tmax rs' ++ R_tail = push0R_iter (N.to_nat k) (evalSR t Tmax rs ++ R_tail).
Proof.
  unfold sPush0RK in h.
  destruct (popSR rs) as [z o rest |] eqn:hp; [| discriminate].
  destruct (popSR_ok_sound hp hPos) as [hPrest hepop].
  destruct (pushSR1_sound h ltac:(simpl; lia) hPrest) as [hP' he'].
  refine (conj hP' (fun t Tmax R_tail => _)).
  rewrite (he' t Tmax), (hepop t Tmax); simpl.
  rewrite push0R_iter_cons.
  replace (N.to_nat (z + k)) with (N.to_nat z + N.to_nat k) by lia.
  reflexivity.
Qed.

Lemma sPush1RK_sound {rs rs' : list SRRun}
    (h : sPush1RK rs = Some rs') (hPos : PosSR rs) :
  PosSR rs' /\
  forall t Tmax R_tail,
    evalSR t Tmax rs' ++ R_tail = push1R (evalSR t Tmax rs ++ R_tail).
Proof.
  unfold sPush1RK in h.
  destruct (popSR rs) as [z o rest |] eqn:hp; [| discriminate].
  destruct (popSR_ok_sound hp hPos) as [hPrest hepop].
  destruct (N.eqb z 0) eqn:hz0.
  - apply N.eqb_eq in hz0; subst.
    destruct (pushSR1_sound h ltac:(simpl; lia) hPrest) as [hP' he'].
    refine (conj hP' (fun t Tmax R_tail => _)).
    rewrite (he' t Tmax), (hepop t Tmax); simpl.
    replace (N.to_nat (o + 1)) with (S (N.to_nat o)) by lia.
    reflexivity.
  - apply N.eqb_neq in hz0.
    destruct (pushSR1 rest (z - 1) o (SCConst 1)) as [r1 |] eqn:hp1; [| discriminate].
    destruct (pushSR1_sound hp1 ltac:(simpl; lia) hPrest) as [hP1 he1].
    destruct (pushSR1_sound h ltac:(simpl; lia) hP1) as [hP' he'].
    refine (conj hP' (fun t Tmax R_tail => _)).
    rewrite (he' t Tmax), (he1 t Tmax), (hepop t Tmax); simpl.
    replace (N.to_nat z) with (S (N.to_nat (z - 1))) by lia.
    reflexivity.
Qed.

Lemma sStepAK_sound {ls ls' : list SLRun} {rs rs' : list SRRun} {m' : SegMode}
    (h : sStepAK ls rs = SSOk m' ls' rs') (hPL : PosSL ls) (hPR : PosSR rs) :
  PosSL ls' /\ PosSR rs' /\
  forall t Tmax (l : side) (R_tail : list (nat * nat)),
    (S1 >> l) = encLeft (evalSL t Tmax ls) ->
    (l {{A}}> encRight (evalSR t Tmax rs ++ R_tail)) -[ tm ]->+
      evalSegCfg m' (evalSL t Tmax ls') (evalSR t Tmax rs' ++ R_tail).
Proof.
  unfold sStepAK in h.
  destruct (popSR rs) as [z o r1 |] eqn:hp; [| discriminate].
  destruct (popSR_ok_sound hp hPR) as [hPR1 hepop].
  destruct (N.eqb z 0) eqn:hz0.
  - apply N.eqb_eq in hz0; subst.
    destruct (N.eqb o 0) eqn:ho0.
    + apply N.eqb_eq in ho0; subst.
      destruct (sPush0RK r1 1) as [r2 |] eqn:hr2; [| discriminate].
      injection h as <- <- <-.
      destruct (sPush0RK_sound hr2 hPR1) as [hPR2 heR2].
      refine (conj hPL (conj hPR2 (fun t Tmax l R_tail hl => _))).
      rewrite (hepop t Tmax), <- app_comm_cons, (heR2 t Tmax R_tail); simpl push0R_iter.
      exact (step_A_common l (evalSL t Tmax ls) hl ((0, 0) :: (evalSR t Tmax r1 ++ R_tail))
        mER (evalSL t Tmax ls) (push0R (evalSR t Tmax r1 ++ R_tail)) eq_refl).
    + apply N.eqb_neq in ho0.
      destruct (pushSR1 r1 0 (o - 1) (SCConst 1)) as [r2 |] eqn:hr2; [| discriminate].
      injection h as <- <- <-.
      destruct (pushSR1_sound hr2 ltac:(simpl; lia) hPR1) as [hPR2 heR2].
      refine (conj hPL (conj hPR2 (fun t Tmax l R_tail hl => _))).
      rewrite (hepop t Tmax), <- app_comm_cons, (heR2 t Tmax); simpl.
      replace (N.to_nat o) with (S (N.to_nat (o - 1))) by lia.
      exact (step_A_common l (evalSL t Tmax ls) hl
        ((0, S (N.to_nat (o - 1))) :: (evalSR t Tmax r1 ++ R_tail))
        mER (evalSL t Tmax ls) ((0, N.to_nat (o - 1)) :: (evalSR t Tmax r1 ++ R_tail)) eq_refl).
  - apply N.eqb_neq in hz0.
    destruct (N.eqb z 1) eqn:hz1.
    + apply N.eqb_eq in hz1; subst.
      destruct (N.eqb o 0) eqn:ho0; [| discriminate].
      apply N.eqb_eq in ho0; subst.
      injection h as <- <- <-.
      refine (conj hPL (conj hPR1 (fun t Tmax l R_tail hl => _))).
      rewrite (hepop t Tmax); simpl (N.to_nat 1); simpl (N.to_nat 0); rewrite <- app_comm_cons.
      exact (step_A_common l (evalSL t Tmax ls) hl ((1, 0) :: (evalSR t Tmax r1 ++ R_tail))
        mAR00 (evalSL t Tmax ls) (evalSR t Tmax r1 ++ R_tail) eq_refl).
    + apply N.eqb_neq in hz1.
      destruct (N.eqb z 2) eqn:hz2.
      * apply N.eqb_eq in hz2; subst.
        destruct (pushSL1 ls 0 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
        destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPL) as [hPL1 heL1].
        destruct (N.eqb o 0) eqn:ho0.
        -- apply N.eqb_eq in ho0; subst.
           destruct (sPush0RK r1 1) as [r2 |] eqn:hr2; [| discriminate].
           injection h as <- <- <-.
           destruct (sPush0RK_sound hr2 hPR1) as [hPR2 heR2].
           refine (conj hPL1 (conj hPR2 (fun t Tmax l R_tail hl => _))).
           rewrite (hepop t Tmax), (heL1 t Tmax), (heR2 t Tmax R_tail); simpl.
           exact (step_A_common l (evalSL t Tmax ls) hl ((2, 0) :: (evalSR t Tmax r1 ++ R_tail))
             mDR ((0, false) :: evalSL t Tmax ls) (push0R (evalSR t Tmax r1 ++ R_tail)) eq_refl).
        -- apply N.eqb_neq in ho0.
           destruct (pushSR1 r1 0 (o - 1) (SCConst 1)) as [r2 |] eqn:hr2; [| discriminate].
           injection h as <- <- <-.
           destruct (pushSR1_sound hr2 ltac:(simpl; lia) hPR1) as [hPR2 heR2].
           refine (conj hPL1 (conj hPR2 (fun t Tmax l R_tail hl => _))).
           rewrite (hepop t Tmax), (heL1 t Tmax), (heR2 t Tmax); simpl.
           replace (N.to_nat o) with (S (N.to_nat (o - 1))) by lia.
           exact (step_A_common l (evalSL t Tmax ls) hl
             ((2, S (N.to_nat (o - 1))) :: (evalSR t Tmax r1 ++ R_tail))
             mDR ((0, false) :: evalSL t Tmax ls)
             ((0, N.to_nat (o - 1)) :: (evalSR t Tmax r1 ++ R_tail)) eq_refl).
      * apply N.eqb_neq in hz2.
        destruct (pushSR1 r1 (z - 3) o (SCConst 1)) as [r2 |] eqn:hr2; [| discriminate].
        destruct (sPush1RK r2) as [r3 |] eqn:hr3; [| discriminate].
        destruct (sPush1RK r3) as [r4 |] eqn:hr4; [| discriminate].
        injection h as <- <- <-.
        destruct (pushSR1_sound hr2 ltac:(simpl; lia) hPR1) as [hPR2 heR2].
        destruct (sPush1RK_sound hr3 hPR2) as [hPR3 heR3].
        destruct (sPush1RK_sound hr4 hPR3) as [hPR4 heR4].
        refine (conj hPL (conj hPR4 (fun t Tmax l R_tail hl => _))).
        rewrite (hepop t Tmax), <- app_comm_cons, (heR4 t Tmax R_tail), (heR3 t Tmax R_tail), (heR2 t Tmax); simpl.
        replace (N.to_nat z) with (S (S (S (N.to_nat (z - 3))))) by lia.
        exact (step_A_common l (evalSL t Tmax ls) hl
          ((S (S (S (N.to_nat (z - 3)))), N.to_nat o) :: (evalSR t Tmax r1 ++ R_tail))
          mCL (evalSL t Tmax ls)
          (push1R (push1R ((N.to_nat (z - 3), N.to_nat o) :: (evalSR t Tmax r1 ++ R_tail)))) eq_refl).
Qed.

Lemma sSweepK_sound {isE : bool} {d : N} {b : bool} {ls ls' : list SLRun} {rs rs' : list SRRun}
    {m' : SegMode} (h : sSweepK isE d b ls rs = SSOk m' ls' rs') (hPL : PosSL ls) (hPR : PosSR rs) :
  PosSL ls' /\ PosSR rs' /\
  forall t Tmax R_tail,
    evalSegCfg (sweepMode isE) ((N.to_nat d, b) :: evalSL t Tmax ls) (evalSR t Tmax rs ++ R_tail)
      -[ tm ]->+
    evalSegCfg m' (evalSL t Tmax ls') (evalSR t Tmax rs' ++ R_tail).
Proof.
  unfold sSweepK in h.
  destruct (sPush0RK rs (d + 1)) as [r1 |] eqn:hr1; [| discriminate].
  destruct (sPush0RK_sound hr1 hPR) as [hPR1 heR1].
  rewrite N_mod2_eqb in h.
  pose proof (fun t Tmax R_tail =>
    step_sweepDLEL (N.to_nat d) isE b (evalSL t Tmax ls) (evalSR t Tmax rs ++ R_tail)) as hstep_all.
  cbv beta in hstep_all.
  destruct (Nat.eqb ((N.to_nat d) mod 2) 0) eqn:hmod, isE, b; simpl in h.
  - destruct (pushSL1 ls 0 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
    injection h as <- <- <-.
    destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPL) as [hPL1 heL1].
    refine (conj hPL1 (conj hPR1 (fun t Tmax R_tail => _))).
    pose proof (hstep_all t Tmax R_tail) as hs; rewrite sweepDLEL_closed, hmod in hs; simpl in hs.
    rewrite (heL1 t Tmax), (heR1 t Tmax R_tail); simpl.
    replace (N.to_nat (d + 1)) with (N.to_nat d + 1) by lia; exact hs.
  - destruct (sBumpLK ls) as [l1 |] eqn:hl1; [| discriminate].
    injection h as <- <- <-.
    destruct (sBumpLK_sound hl1 hPL) as [hPL1 heL1].
    refine (conj hPL1 (conj hPR1 (fun t Tmax R_tail => _))).
    pose proof (hstep_all t Tmax R_tail) as hs; rewrite sweepDLEL_closed, hmod in hs; simpl in hs.
    rewrite (heL1 t Tmax), (heR1 t Tmax R_tail).
    replace (N.to_nat (d + 1)) with (N.to_nat d + 1) by lia; exact hs.
  - injection h as <- <- <-.
    refine (conj hPL (conj hPR1 (fun t Tmax R_tail => _))).
    pose proof (hstep_all t Tmax R_tail) as hs; rewrite sweepDLEL_closed, hmod in hs; simpl in hs.
    rewrite (heR1 t Tmax R_tail).
    replace (N.to_nat (d + 1)) with (N.to_nat d + 1) by lia; exact hs.
  - injection h as <- <- <-.
    refine (conj hPL (conj hPR1 (fun t Tmax R_tail => _))).
    pose proof (hstep_all t Tmax R_tail) as hs; rewrite sweepDLEL_closed, hmod in hs; simpl in hs.
    rewrite (heR1 t Tmax R_tail).
    replace (N.to_nat (d + 1)) with (N.to_nat d + 1) by lia; exact hs.
  - injection h as <- <- <-.
    refine (conj hPL (conj hPR1 (fun t Tmax R_tail => _))).
    pose proof (hstep_all t Tmax R_tail) as hs; rewrite sweepDLEL_closed, hmod in hs; simpl in hs.
    rewrite (heR1 t Tmax R_tail).
    replace (N.to_nat (d + 1)) with (N.to_nat d + 1) by lia; exact hs.
  - injection h as <- <- <-.
    refine (conj hPL (conj hPR1 (fun t Tmax R_tail => _))).
    pose proof (hstep_all t Tmax R_tail) as hs; rewrite sweepDLEL_closed, hmod in hs; simpl in hs.
    rewrite (heR1 t Tmax R_tail).
    replace (N.to_nat (d + 1)) with (N.to_nat d + 1) by lia; exact hs.
  - destruct (pushSL1 ls 0 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
    injection h as <- <- <-.
    destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPL) as [hPL1 heL1].
    refine (conj hPL1 (conj hPR1 (fun t Tmax R_tail => _))).
    pose proof (hstep_all t Tmax R_tail) as hs; rewrite sweepDLEL_closed, hmod in hs; simpl in hs.
    rewrite (heL1 t Tmax), (heR1 t Tmax R_tail); simpl.
    replace (N.to_nat (d + 1)) with (N.to_nat d + 1) by lia; exact hs.
  - destruct (sBumpLK ls) as [l1 |] eqn:hl1; [| discriminate].
    injection h as <- <- <-.
    destruct (sBumpLK_sound hl1 hPL) as [hPL1 heL1].
    refine (conj hPL1 (conj hPR1 (fun t Tmax R_tail => _))).
    pose proof (hstep_all t Tmax R_tail) as hs; rewrite sweepDLEL_closed, hmod in hs; simpl in hs.
    rewrite (heL1 t Tmax), (heR1 t Tmax R_tail).
    replace (N.to_nat (d + 1)) with (N.to_nat d + 1) by lia; exact hs.
Qed.

Lemma symStepSingleK_sound {m m' : SegMode} {ls ls' : list SLRun} {rs rs' : list SRRun}
    (h : symStepSingleK m ls rs = SSOk m' ls' rs') (hPL : PosSL ls) (hPR : PosSR rs) :
  PosSL ls' /\ PosSR rs' /\
  forall t Tmax R_tail,
    evalSegCfg m (evalSL t Tmax ls) (evalSR t Tmax rs ++ R_tail) -[ tm ]->+
      evalSegCfg m' (evalSL t Tmax ls') (evalSR t Tmax rs' ++ R_tail).
Proof.
  destruct m; simpl symStepSingleK in h.
  - (* mAR *)
    destruct (sBumpLK ls) as [l1 |] eqn:hl1; [| discriminate].
    destruct (sBumpLK_sound hl1 hPL) as [hPL1 heL1].
    destruct (sStepAK_sound h hPL1 hPR) as [hPL' [hPR' hstep]].
    refine (conj hPL' (conj hPR' (fun t Tmax R_tail => _))).
    unfold evalSegCfg at 1.
    apply (hstep t Tmax (encLeft (evalSL t Tmax ls)) R_tail).
    rewrite (heL1 t Tmax); exact (cons_one_encLeft _).
  - (* mAR0 *)
    destruct (pushSL1 ls 0 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
    destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPL) as [hPL1 heL1].
    destruct (sStepAK_sound h hPL1 hPR) as [hPL' [hPR' hstep]].
    refine (conj hPL' (conj hPR' (fun t Tmax R_tail => _))).
    unfold evalSegCfg at 1.
    apply (hstep t Tmax (S0 >> encLeft (evalSL t Tmax ls)) R_tail).
    rewrite (heL1 t Tmax); reflexivity.
  - (* mAR00 *)
    destruct (sPush100LK ls) as [l1 |] eqn:hl1; [| discriminate].
    destruct (sPush100LK_sound hl1 hPL) as [hPL1 heL1].
    destruct (sStepAK_sound h hPL1 hPR) as [hPL' [hPR' hstep]].
    refine (conj hPL' (conj hPR' (fun t Tmax R_tail => _))).
    unfold evalSegCfg at 1.
    apply (hstep t Tmax (S0 >> S0 >> encLeft (evalSL t Tmax ls)) R_tail).
    rewrite (heL1 t Tmax); exact (cons_100_encLeft _).
  - (* mCL *)
    destruct ls as [|r lrest]; [discriminate |].
    injection h as <- <- <-.
    refine (conj hPL (conj hPR (fun t Tmax R_tail => _))).
    assert (hne : evalSL t Tmax (r :: lrest) <> []).
    { intros h0. pose proof (evalSL_nil_of_pos hPL h0); discriminate. }
    destruct (evalSL t Tmax (r :: lrest)) as [|p xs]; [contradiction | apply mstep; reflexivity].
  - (* mDL *)
    destruct (popSL ls) as [d b l1 |] eqn:hp; [| discriminate].
    destruct (popSL_ok_sound hp hPL) as [hPL1 heL1].
    destruct (sSweepK_sound h hPL1 hPR) as [hPL' [hPR' hstep]].
    refine (conj hPL' (conj hPR' (fun t Tmax R_tail => _))).
    rewrite (heL1 t Tmax); exact (hstep t Tmax R_tail).
  - (* mEL *)
    destruct (popSL ls) as [d b l1 |] eqn:hp; [| discriminate].
    destruct (popSL_ok_sound hp hPL) as [hPL1 heL1].
    destruct (sSweepK_sound h hPL1 hPR) as [hPL' [hPR' hstep]].
    refine (conj hPL' (conj hPR' (fun t Tmax R_tail => _))).
    rewrite (heL1 t Tmax); exact (hstep t Tmax R_tail).
  - (* mDR *)
    destruct (popSR rs) as [z o r1 |] eqn:hp; [| discriminate].
    destruct (popSR_ok_sound hp hPR) as [hPR1 hepop].
    destruct (N.eqb z 0) eqn:hz0.
    + apply N.eqb_eq in hz0; subst.
      destruct (N.eqb o 0) eqn:ho0.
      * apply N.eqb_eq in ho0; subst.
        destruct (sPush0RK r1 2) as [r2 |] eqn:hr2; [| discriminate].
        injection h as <- <- <-.
        destruct (sPush0RK_sound hr2 hPR1) as [hPR2 heR2].
        refine (conj hPL (conj hPR2 (fun t Tmax R_tail => _))).
        rewrite (hepop t Tmax), <- app_comm_cons, (heR2 t Tmax R_tail); simpl.
        apply mstep; reflexivity.
      * apply N.eqb_neq in ho0.
        destruct (pushSR1 r1 1 (o - 1) (SCConst 1)) as [r2 |] eqn:hr2; [| discriminate].
        injection h as <- <- <-.
        destruct (pushSR1_sound hr2 ltac:(simpl; lia) hPR1) as [hPR2 heR2].
        refine (conj hPL (conj hPR2 (fun t Tmax R_tail => _))).
        rewrite (hepop t Tmax), <- app_comm_cons, (heR2 t Tmax); simpl.
        replace (N.to_nat o) with (S (N.to_nat (o - 1))) by lia.
        apply mstep; reflexivity.
    + apply N.eqb_neq in hz0.
      destruct (pushSR1 r1 (z - 1) o (SCConst 1)) as [r2 |] eqn:hr2; [| discriminate].
      destruct (sBumpLK ls) as [l1 |] eqn:hl1; [| discriminate].
      injection h as <- <- <-.
      destruct (pushSR1_sound hr2 ltac:(simpl; lia) hPR1) as [hPR2 heR2].
      destruct (sBumpLK_sound hl1 hPL) as [hPL1 heL1].
      refine (conj hPL1 (conj hPR2 (fun t Tmax R_tail => _))).
      rewrite (hepop t Tmax), <- app_comm_cons, (heL1 t Tmax), (heR2 t Tmax); simpl.
      replace (N.to_nat z) with (S (N.to_nat (z - 1))) by lia.
      apply mstep; reflexivity.
  - (* mER *)
    destruct (popSR rs) as [z o r1 |] eqn:hp; [| discriminate].
    destruct (popSR_ok_sound hp hPR) as [hPR1 hepop].
    destruct (N.eqb z 0) eqn:hz0.
    + apply N.eqb_eq in hz0; subst.
      destruct (N.eqb o 0) eqn:ho0.
      * apply N.eqb_eq in ho0; subst.
        destruct (sPush0RK r1 2) as [r2 |] eqn:hr2; [| discriminate].
        injection h as <- <- <-.
        destruct (sPush0RK_sound hr2 hPR1) as [hPR2 heR2].
        refine (conj hPL (conj hPR2 (fun t Tmax R_tail => _))).
        rewrite (hepop t Tmax), <- app_comm_cons, (heR2 t Tmax R_tail); simpl.
        apply mstep; reflexivity.
      * apply N.eqb_neq in ho0.
        destruct (pushSR1 r1 1 (o - 1) (SCConst 1)) as [r2 |] eqn:hr2; [| discriminate].
        injection h as <- <- <-.
        destruct (pushSR1_sound hr2 ltac:(simpl; lia) hPR1) as [hPR2 heR2].
        refine (conj hPL (conj hPR2 (fun t Tmax R_tail => _))).
        rewrite (hepop t Tmax), <- app_comm_cons, (heR2 t Tmax); simpl.
        replace (N.to_nat o) with (S (N.to_nat (o - 1))) by lia.
        apply mstep; reflexivity.
    + apply N.eqb_neq in hz0.
      destruct (pushSR1 r1 (z - 1) o (SCConst 1)) as [r2 |] eqn:hr2; [| discriminate].
      injection h as <- <- <-.
      destruct (pushSR1_sound hr2 ltac:(simpl; lia) hPR1) as [hPR2 heR2].
      refine (conj hPL (conj hPR2 (fun t Tmax R_tail => _))).
      rewrite (hepop t Tmax), <- app_comm_cons, (heR2 t Tmax); simpl.
      replace (N.to_nat z) with (S (N.to_nat (z - 1))) by lia.
      apply mstep; reflexivity.
Qed.

Arguments symStepSingleK : simpl never.
Arguments popSR : simpl never.
Arguments popSL : simpl never.

Lemma symStepRLEK_sound {m m' : SegMode} {ls ls' : list SLRun} {rs rs' : list SRRun}
    (h : symStepRLEK m ls rs = SSOk m' ls' rs') (hPL : PosSL ls) (hPR : PosSR rs) :
  PosSL ls' /\ PosSR rs' /\
  forall t Tmax R_tail,
    evalSegCfg m (evalSL t Tmax ls) (evalSR t Tmax rs ++ R_tail) -[ tm ]->+
      evalSegCfg m' (evalSL t Tmax ls') (evalSR t Tmax rs' ++ R_tail).
Proof.
  destruct rs as [|r rest]; [simpl in h; discriminate |].
  destruct m; simpl symStepRLEK in h; try exact (symStepSingleK_sound h hPL hPR).
  - (* mAR0 *)
    destruct hPR as [hPr hPrest].
    destruct r as [z o c | z1 o1 z2 o2 c]; simpl in h.
    + (* SROne *)
      destruct (N.eqb z 0 && N.eqb o 0 && N.leb 1 (scBase c)) eqn:ha1; simpl in h.
      * repeat rewrite andb_true_iff in ha1; destruct ha1 as [[hz0 ho0] hc].
        apply N.eqb_eq in hz0; apply N.eqb_eq in ho0; apply N.leb_le in hc; subst.
        destruct (pushSL1 ls 0 false c) as [l1 |] eqn:hl1; [| discriminate].
        injection h as <- <- <-.
        destruct (pushSL1_sound hl1 ltac:(lia) hPL) as [hPL1 heL1].
        refine (conj hPL1 (conj hPrest (fun t Tmax R_tail => _))).
        rewrite (heL1 t Tmax); simpl evalSR; simpl evalSRRun; rewrite <- app_assoc.
        pose proof (scBase_le_evalSC t Tmax c) as hge.
        exact (rule_A1 (evalSC t Tmax c) ltac:(lia) (evalSL t Tmax ls) (evalSR t Tmax rest ++ R_tail)).
      * destruct (N.eqb z 2 && N.eqb o 0 && scIs1 c) eqn:ha2c; simpl in h.
        -- repeat rewrite andb_true_iff in ha2c; destruct ha2c as [[hz2 ho0] hc1].
           apply N.eqb_eq in hz2; apply N.eqb_eq in ho0; pose proof (scIs1_eq hc1) as ->; subst.
           destruct rest as [|[? ? ? | z1 o1 z2 o2 c2] rest2]; simpl in h;
             try exact (symStepSingleK_sound h hPL (conj hPr hPrest)).
           destruct hPrest as [hPr2 hPrest2].
           destruct (N.eqb z1 0 && N.eqb o1 0 && N.eqb z2 2 && N.eqb o2 0 && N.leb 1 (scBase c2)) eqn:hc2c;
             simpl in h; [| exact (symStepSingleK_sound h hPL (conj hPr (conj hPr2 hPrest2)))].
           repeat rewrite andb_true_iff in hc2c; destruct hc2c as [[[[hz1 ho1] hz2] ho2] hc2].
           apply N.eqb_eq in hz1; apply N.eqb_eq in ho1; apply N.eqb_eq in hz2;
           apply N.eqb_eq in ho2; apply N.leb_le in hc2; subst.
           destruct (pushSL2 ls 2 false 0 false c2) as [l1 |] eqn:hl1; [| discriminate].
           destruct (pushSR1 rest2 2 0 (SCConst 1)) as [r1 |] eqn:hr1; [| discriminate].
           injection h as <- <- <-.
           destruct (pushSL2_sound hl1 ltac:(lia) hPL) as [hPL1 heL1].
           destruct (pushSR1_sound hr1 ltac:(simpl; lia) hPrest2) as [hPR1 heR1].
           refine (conj hPL1 (conj hPR1 (fun t Tmax R_tail => _))).
           rewrite (heL1 t Tmax), (heR1 t Tmax); simpl; rewrite <- app_assoc.
           pose proof (scBase_le_evalSC t Tmax c2) as hge.
           exact (rule_A2c (evalSC t Tmax c2) ltac:(lia) (evalSL t Tmax ls) (evalSR t Tmax rest2 ++ R_tail)).
        -- destruct (N.eqb z 4 && N.eqb o 0 && (scIs1 c || N.leb 2 (scBase c))) eqn:ha3; simpl in h.
           ++ repeat rewrite andb_true_iff in ha3; destruct ha3 as [[hz4 ho0] hcor].
              apply N.eqb_eq in hz4; apply N.eqb_eq in ho0; subst.
              destruct (popSL ls) as [d b l1 |] eqn:hpop; simpl in h;
                [| exact (symStepSingleK_sound h hPL (conj hPr hPrest))].
              destruct (popSL_ok_sound hpop hPL) as [hPL1 heL1].
              destruct (pushSL1 l1 (d + 2) b (SCConst 1)) as [l2 |] eqn:hl2; [| discriminate].
              destruct (pushSL1_sound hl2 ltac:(simpl; lia) hPL1) as [hPL2 heL2].
              destruct (scIs1 c) eqn:h1.
              ** pose proof (scIs1_eq h1) as ->; simpl in h.
                 destruct (pushSL1 l2 2 false (SCConst 1)) as [l4 |] eqn:hl4; [| discriminate].
                 injection h as <- <- <-.
                 destruct (pushSL1_sound hl4 ltac:(simpl; lia) hPL2) as [hPL4 heL4].
                 refine (conj hPL4 (conj hPrest (fun t Tmax R_tail => _))).
                 rewrite (heL1 t Tmax), (heL4 t Tmax), (heL2 t Tmax); simpl.
                 replace (N.to_nat (d + 2)) with (N.to_nat d + 2) by lia.
                 pose proof (rule_A3 1 ltac:(lia) (N.to_nat d) b (evalSL t Tmax l1) (evalSR t Tmax rest ++ R_tail)) as hr3.
                 simpl in hr3; exact hr3.
              ** simpl in hcor, h; apply N.leb_le in hcor.
                 destruct (pushSL1 l2 4 false (scSub c 1)) as [l3 |] eqn:hl3; [| discriminate].
                 destruct (pushSL1_sound hl3 ltac:(rewrite scSub_base; lia) hPL2) as [hPL3 heL3].
                 destruct (pushSL1 l3 2 false (SCConst 1)) as [l4 |] eqn:hl4; [| discriminate].
                 injection h as <- <- <-.
                 destruct (pushSL1_sound hl4 ltac:(simpl; lia) hPL3) as [hPL4 heL4].
                 refine (conj hPL4 (conj hPrest (fun t Tmax R_tail => _))).
                 rewrite (heL1 t Tmax), (heL4 t Tmax), (heL3 t Tmax), (heL2 t Tmax),
                   (evalSC_scSub t Tmax c 1 ltac:(lia)); simpl; rewrite <- app_assoc.
                 replace (N.to_nat (d + 2)) with (N.to_nat d + 2) by lia.
                 pose proof (scBase_le_evalSC t Tmax c) as hge.
                 exact (rule_A3 (evalSC t Tmax c) ltac:(lia) (N.to_nat d) b
                   (evalSL t Tmax l1) (evalSR t Tmax rest ++ R_tail)).
           ++ destruct (N.eqb z 2 && N.eqb o 0 && (scIs2 c || N.leb 3 (scBase c))) eqn:ha4; simpl in h;
                [| exact (symStepSingleK_sound h hPL (conj hPr hPrest))].
              repeat rewrite andb_true_iff in ha4; destruct ha4 as [[hz2 ho0] hcor].
              apply N.eqb_eq in hz2; apply N.eqb_eq in ho0; subst.
              destruct (pushSL1 ls 0 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
              destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPL) as [hPL1 heL1].
              destruct (scIs2 c) eqn:h2.
              ** pose proof (scIs2_eq h2) as ->; simpl in h.
                 destruct (pushSL1 l1 0 false (SCConst 1)) as [l3 |] eqn:hl3; [| discriminate].
                 destruct (pushSR1 rest 3 0 (SCConst 1)) as [r1 |] eqn:hr1; [| discriminate].
                 injection h as <- <- <-.
                 destruct (pushSL1_sound hl3 ltac:(simpl; lia) hPL1) as [hPL3 heL3].
                 destruct (pushSR1_sound hr1 ltac:(simpl; lia) hPrest) as [hPR1 heR1].
                 refine (conj hPL3 (conj hPR1 (fun t Tmax R_tail => _))).
                 rewrite (heL3 t Tmax), (heL1 t Tmax), (heR1 t Tmax); simpl.
                 pose proof (rule_A4 2 ltac:(lia) (evalSL t Tmax ls) (evalSR t Tmax rest ++ R_tail)) as hr4.
                 simpl in hr4; exact hr4.
              ** simpl in hcor, h; apply N.leb_le in hcor.
                 destruct (pushSL1 l1 2 false (scSub c 2)) as [l2 |] eqn:hl2; [| discriminate].
                 destruct (pushSL1_sound hl2 ltac:(rewrite scSub_base; lia) hPL1) as [hPL2 heL2].
                 destruct (pushSL1 l2 0 false (SCConst 1)) as [l3 |] eqn:hl3; [| discriminate].
                 destruct (pushSR1 rest 3 0 (SCConst 1)) as [r1 |] eqn:hr1; [| discriminate].
                 injection h as <- <- <-.
                 destruct (pushSL1_sound hl3 ltac:(simpl; lia) hPL2) as [hPL3 heL3].
                 destruct (pushSR1_sound hr1 ltac:(simpl; lia) hPrest) as [hPR1 heR1].
                 refine (conj hPL3 (conj hPR1 (fun t Tmax R_tail => _))).
                 rewrite (heL3 t Tmax), (heL2 t Tmax), (heL1 t Tmax), (heR1 t Tmax),
                   (evalSC_scSub t Tmax c 2 ltac:(lia)); simpl; rewrite <- app_assoc.
                 pose proof (scBase_le_evalSC t Tmax c) as hge.
                 exact (rule_A4 (evalSC t Tmax c) ltac:(lia)
                   (evalSL t Tmax ls) (evalSR t Tmax rest ++ R_tail)).
    + (* SRTwo *)
      destruct (N.eqb z1 2 && N.eqb o1 0 && N.eqb z2 0 && N.eqb o2 0 && N.leb 1 (scBase c)) eqn:ha2a; simpl in h.
      * repeat rewrite andb_true_iff in ha2a; destruct ha2a as [[[[hz1 ho1] hz2] ho2] hc].
        apply N.eqb_eq in hz1; apply N.eqb_eq in ho1; apply N.eqb_eq in hz2;
        apply N.eqb_eq in ho2; apply N.leb_le in hc; subst.
        destruct (pushSL2 ls 2 false 0 false c) as [l1 |] eqn:hl1; [| discriminate].
        injection h as <- <- <-.
        destruct (pushSL2_sound hl1 ltac:(lia) hPL) as [hPL1 heL1].
        refine (conj hPL1 (conj hPrest (fun t Tmax R_tail => _))).
        rewrite (heL1 t Tmax); simpl; rewrite <- app_assoc.
        pose proof (scBase_le_evalSC t Tmax c) as hge.
        exact (rule_A2a (evalSC t Tmax c) ltac:(lia) (evalSL t Tmax ls) (evalSR t Tmax rest ++ R_tail)).
      * destruct (N.eqb z1 0 && N.eqb o1 0 && N.eqb z2 2 && N.eqb o2 0 && N.leb 2 (scBase c)) eqn:ha2b;
          simpl in h; [| exact (symStepSingleK_sound h hPL (conj hPr hPrest))].
        repeat rewrite andb_true_iff in ha2b; destruct ha2b as [[[[hz1 ho1] hz2] ho2] hc].
        apply N.eqb_eq in hz1; apply N.eqb_eq in ho1; apply N.eqb_eq in hz2;
        apply N.eqb_eq in ho2; apply N.leb_le in hc; subst.
        destruct (pushSL1 ls 0 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
        destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPL) as [hPL1 heL1].
        destruct (pushSL2 l1 2 false 0 false (scSub c 1)) as [l2 |] eqn:hl2; [| discriminate].
        destruct (pushSR1 rest 2 0 (SCConst 1)) as [r1 |] eqn:hr1; [| discriminate].
        injection h as <- <- <-.
        destruct (pushSL2_sound hl2 ltac:(rewrite scSub_base; lia) hPL1) as [hPL2 heL2].
        destruct (pushSR1_sound hr1 ltac:(simpl; lia) hPrest) as [hPR1 heR1].
        refine (conj hPL2 (conj hPR1 (fun t Tmax R_tail => _))).
        rewrite (heL2 t Tmax), (heL1 t Tmax), (heR1 t Tmax), (evalSC_scSub t Tmax c 1 ltac:(lia));
          simpl; rewrite <- app_assoc.
        pose proof (scBase_le_evalSC t Tmax c) as hge.
        exact (rule_A2b (evalSC t Tmax c) ltac:(lia) (evalSL t Tmax ls) (evalSR t Tmax rest ++ R_tail)).
  - (* mEL *)
    destruct (popSR (r :: rest)) as [rz ro r_rest |] eqn:hpopR; simpl in h;
      [| exact (symStepSingleK_sound h hPL hPR)].
    destruct (N.eqb rz 1 && N.eqb ro 0) eqn:hrz; simpl in h;
      [| exact (symStepSingleK_sound h hPL hPR)].
    apply andb_true_iff in hrz as [hrz1 hro0]; apply N.eqb_eq in hrz1; apply N.eqb_eq in hro0; subst.
    destruct (popSR_ok_sound hpopR hPR) as [hPRr heR].
    destruct (popSL ls) as [d0 [|] [|blk l_rest] |] eqn:hpopL; simpl in h;
      try exact (symStepSingleK_sound h hPL hPR).
    destruct (N.leb 2 d0 && N.eqb (N.modulo d0 2) 0) eqn:hd0; simpl in h;
      [| exact (symStepSingleK_sound h hPL hPR)].
    apply andb_true_iff in hd0 as [hd0_ge hd0_even].
    apply N.leb_le in hd0_ge. rewrite N_mod2_eqb in hd0_even; apply Nat.eqb_eq in hd0_even.
    destruct (popSL_ok_sound hpopL hPL) as [[hPblk hPLr] heL].
    destruct blk as [bd [|] bc | bd1 [|] bd2 [|] bc]; simpl in h;
      try exact (symStepSingleK_sound h hPL hPR).
    + (* SLOne *)
      destruct (N.eqb bd (d0 - 2) && N.leb 1 (scBase bc)) eqn:hcond; simpl in h;
        [| exact (symStepSingleK_sound h hPL hPR)].
      apply andb_true_iff in hcond as [hbd hbc]; apply N.eqb_eq in hbd; apply N.leb_le in hbc; subst.
      destruct (pushSL1 l_rest d0 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
      destruct (pushSR1 r_rest (d0 - 2) 0 bc) as [r1 |] eqn:hr1; [| discriminate].
      destruct (pushSR1 r1 1 0 (SCConst 1)) as [r2 |] eqn:hr2; [| discriminate].
      injection h as <- <- <-.
      destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPLr) as [hPL1 heL1].
      destruct (pushSR1_sound hr1 ltac:(lia) hPRr) as [hPR1 heR1].
      destruct (pushSR1_sound hr2 ltac:(simpl; lia) hPR1) as [hPR2 heR2].
      refine (conj hPL1 (conj hPR2 (fun t Tmax R_tail => _))).
      rewrite (heL t Tmax), (heR t Tmax), (heL1 t Tmax), (heR2 t Tmax), (heR1 t Tmax);
        simpl evalSL; simpl evalSLRun; simpl repeat; simpl app; rewrite <- app_assoc.
      set (q := (N.to_nat d0 - 2) / 2).
      assert (hq1 : N.to_nat d0 = 2 * q + 2) by (unfold q; lia).
      assert (hq2 : N.to_nat (d0 - 2) = 2 * q) by (unfold q; lia).
      rewrite hq1, hq2.
      pose proof (scBase_le_evalSC t Tmax bc) as hge.
      exact (rule_B1 q (evalSC t Tmax bc) ltac:(lia) (evalSL t Tmax l_rest) (evalSR t Tmax r_rest ++ R_tail)).
    + (* SLTwo *)
      destruct (N.eqb d0 4 && N.eqb bd1 0 && N.eqb bd2 2 && N.leb 1 (scBase bc)) eqn:hc2; simpl in h.
      * repeat rewrite andb_true_iff in hc2; destruct hc2 as [[[hd04 hbd1] hbd2] hbc].
        apply N.eqb_eq in hd04; apply N.eqb_eq in hbd1; apply N.eqb_eq in hbd2; apply N.leb_le in hbc; subst.
        destruct (pushSL1 l_rest 4 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
        destruct (pushSR2 r_rest 0 0 2 0 bc) as [r1 |] eqn:hr1; [| discriminate].
        destruct (pushSR1 r1 1 0 (SCConst 1)) as [r2 |] eqn:hr2; [| discriminate].
        injection h as <- <- <-.
        destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPLr) as [hPL1 heL1].
        destruct (pushSR2_sound hr1 ltac:(lia) hPRr) as [hPR1 heR1].
        destruct (pushSR1_sound hr2 ltac:(simpl; lia) hPR1) as [hPR2 heR2].
        refine (conj hPL1 (conj hPR2 (fun t Tmax R_tail => _))).
        rewrite (heL t Tmax), (heR t Tmax), (heL1 t Tmax), (heR2 t Tmax), (heR1 t Tmax);
          simpl; rewrite <- app_assoc.
        pose proof (scBase_le_evalSC t Tmax bc) as hge.
        exact (rule_B2 (evalSC t Tmax bc) ltac:(lia) (evalSL t Tmax l_rest) (evalSR t Tmax r_rest ++ R_tail)).
      * destruct (N.eqb d0 2 && N.eqb bd1 2 && N.eqb bd2 0 && N.leb 1 (scBase bc)) eqn:hc3; simpl in h.
        -- repeat rewrite andb_true_iff in hc3; destruct hc3 as [[[hd02 hbd1] hbd2] hbc].
           apply N.eqb_eq in hd02; apply N.eqb_eq in hbd1; apply N.eqb_eq in hbd2; apply N.leb_le in hbc; subst.
           destruct (pushSL1 l_rest 2 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
           destruct (pushSR2 r_rest 2 0 0 0 bc) as [r1 |] eqn:hr1; [| discriminate].
           destruct (pushSR1 r1 1 0 (SCConst 1)) as [r2 |] eqn:hr2; [| discriminate].
           injection h as <- <- <-.
           destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPLr) as [hPL1 heL1].
           destruct (pushSR2_sound hr1 ltac:(lia) hPRr) as [hPR1 heR1].
           destruct (pushSR1_sound hr2 ltac:(simpl; lia) hPR1) as [hPR2 heR2].
           refine (conj hPL1 (conj hPR2 (fun t Tmax R_tail => _))).
           rewrite (heL t Tmax), (heR t Tmax), (heL1 t Tmax), (heR2 t Tmax), (heR1 t Tmax);
             simpl; rewrite <- app_assoc.
           pose proof (scBase_le_evalSC t Tmax bc) as hge.
           exact (rule_B3 (evalSC t Tmax bc) ltac:(lia) (evalSL t Tmax l_rest) (evalSR t Tmax r_rest ++ R_tail)).
        -- destruct (N.eqb d0 2 && N.eqb bd1 0 && N.eqb bd2 2 && N.leb 2 (scBase bc)) eqn:hc4; simpl in h.
           ++ repeat rewrite andb_true_iff in hc4; destruct hc4 as [[[hd02 hbd1] hbd2] hbc].
              apply N.eqb_eq in hd02; apply N.eqb_eq in hbd1; apply N.eqb_eq in hbd2; apply N.leb_le in hbc; subst.
              destruct (pushSL1 l_rest 2 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
              destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPLr) as [hPL1 heL1].
              destruct (pushSL1 l1 2 false (SCConst 1)) as [l2 |] eqn:hl2; [| discriminate].
              destruct (pushSR1 r_rest 0 0 (SCConst 1)) as [r1 |] eqn:hr1; [| discriminate].
              destruct (pushSR2 r1 2 0 0 0 (scSub bc 1)) as [r2 |] eqn:hr2; [| discriminate].
              destruct (pushSR1 r2 1 0 (SCConst 1)) as [r3 |] eqn:hr3; [| discriminate].
              injection h as <- <- <-.
              destruct (pushSL1_sound hl2 ltac:(simpl; lia) hPL1) as [hPL2 heL2].
              destruct (pushSR1_sound hr1 ltac:(simpl; lia) hPRr) as [hPR1 heR1].
              destruct (pushSR2_sound hr2 ltac:(rewrite scSub_base; lia) hPR1) as [hPR2 heR2].
              destruct (pushSR1_sound hr3 ltac:(simpl; lia) hPR2) as [hPR3 heR3].
              refine (conj hPL2 (conj hPR3 (fun t Tmax R_tail => _))).
              rewrite (heL t Tmax), (heR t Tmax), (heL2 t Tmax), (heL1 t Tmax),
                (heR3 t Tmax), (heR2 t Tmax), (heR1 t Tmax),
                (evalSC_scSub t Tmax bc 1 ltac:(lia)); simpl; repeat rewrite <- app_assoc.
              pose proof (scBase_le_evalSC t Tmax bc) as hge.
              exact (rule_B4 (evalSC t Tmax bc) ltac:(lia) (evalSL t Tmax l_rest) (evalSR t Tmax r_rest ++ R_tail)).
           ++ destruct (N.eqb d0 4 && N.eqb bd1 2 && N.eqb bd2 0 && N.leb 2 (scBase bc)) eqn:hc5; simpl in h;
                [| exact (symStepSingleK_sound h hPL hPR)].
              repeat rewrite andb_true_iff in hc5; destruct hc5 as [[[hd04 hbd1] hbd2] hbc].
              apply N.eqb_eq in hd04; apply N.eqb_eq in hbd1; apply N.eqb_eq in hbd2; apply N.leb_le in hbc; subst.
              destruct (pushSL1 l_rest 0 false (SCConst 1)) as [l1 |] eqn:hl1; [| discriminate].
              destruct (pushSL1_sound hl1 ltac:(simpl; lia) hPLr) as [hPL1 heL1].
              destruct (pushSL1 l1 4 false (SCConst 1)) as [l2 |] eqn:hl2; [| discriminate].
              destruct (pushSR1 r_rest 2 0 (SCConst 1)) as [r1 |] eqn:hr1; [| discriminate].
              destruct (pushSR2 r1 0 0 2 0 (scSub bc 1)) as [r2 |] eqn:hr2; [| discriminate].
              destruct (pushSR1 r2 1 0 (SCConst 1)) as [r3 |] eqn:hr3; [| discriminate].
              injection h as <- <- <-.
              destruct (pushSL1_sound hl2 ltac:(simpl; lia) hPL1) as [hPL2 heL2].
              destruct (pushSR1_sound hr1 ltac:(simpl; lia) hPRr) as [hPR1 heR1].
              destruct (pushSR2_sound hr2 ltac:(rewrite scSub_base; lia) hPR1) as [hPR2 heR2].
              destruct (pushSR1_sound hr3 ltac:(simpl; lia) hPR2) as [hPR3 heR3].
              refine (conj hPL2 (conj hPR3 (fun t Tmax R_tail => _))).
              rewrite (heL t Tmax), (heR t Tmax), (heL2 t Tmax), (heL1 t Tmax),
                (heR3 t Tmax), (heR2 t Tmax), (heR1 t Tmax),
                (evalSC_scSub t Tmax bc 1 ltac:(lia)); simpl; repeat rewrite <- app_assoc.
              pose proof (scBase_le_evalSC t Tmax bc) as hge.
              exact (rule_B5 (evalSC t Tmax bc) ltac:(lia) (evalSL t Tmax l_rest) (evalSR t Tmax r_rest ++ R_tail)).
Qed.

Lemma iter_symStepBind_err (n : N) : N.iter n symStepBind SSErr = SSErr.
Proof.
  pattern n; apply N.peano_ind; [reflexivity | intros k IH; rewrite N.iter_succ, IH; reflexivity].
Qed.

Lemma runSymRLEK_sound (n : N) :
  forall (m : SegMode) (ls : list SLRun) (rs : list SRRun)
         (m' : SegMode) (ls' : list SLRun) (rs' : list SRRun),
    runSymRLEK n m ls rs = SSOk m' ls' rs' -> PosSL ls -> PosSR rs ->
    PosSL ls' /\ PosSR rs' /\
    forall t Tmax R_tail,
      evalSegCfg m (evalSL t Tmax ls) (evalSR t Tmax rs ++ R_tail) -[ tm ]->*
        evalSegCfg m' (evalSL t Tmax ls') (evalSR t Tmax rs' ++ R_tail).
Proof.
  pattern n; apply N.peano_ind; clear n.
  - intros m ls rs m' ls' rs' h hPL hPR.
    unfold runSymRLEK in h; simpl N.iter in h; injection h as <- <- <-.
    exact (conj hPL (conj hPR (fun _ _ _ => evstep_refl tm _))).
  - intros n IH m ls rs m' ls' rs' h hPL hPR.
    unfold runSymRLEK in h; rewrite N_iter_succ_r in h;
      change (N.iter n symStepBind (symStepRLEK m ls rs) = SSOk m' ls' rs') in h.
    destruct (symStepRLEK m ls rs) as [m1 ls1 rs1 |] eqn:hs.
    + fold (runSymRLEK n m1 ls1 rs1) in h.
      destruct (symStepRLEK_sound hs hPL hPR) as [hPL1 [hPR1 h1]].
      destruct (IH m1 ls1 rs1 m' ls' rs' h hPL1 hPR1) as [hPL' [hPR' h2]].
      refine (conj hPL' (conj hPR' (fun t Tmax R_tail => _))).
      exact (evstep_trans tm _ _ _ (progress_evstep _ _ _ (h1 t Tmax R_tail)) (h2 t Tmax R_tail)).
    + rewrite iter_symStepBind_err in h; discriminate.
Qed.

Lemma buildSym_sound (P : N) (hP : 1 <= N.to_nat P) (b0 : list LRun) :
  forall (slopes : list SlopeSpec) (sL sTarg : list SLRun) (bFin : list LRun),
    buildSym P b0 slopes = SBOk sL sTarg bFin ->
    PosSL sL /\ PosSL sTarg /\ PosL bFin /\
    evalSL 0 (N.to_nat P - 1) sL = expandL b0 /\
    evalSL (N.to_nat P - 1) (N.to_nat P - 1) sTarg = expandL bFin /\
    forall t, t + 1 <= N.to_nat P - 1 ->
      evalSL (t + 1) (N.to_nat P - 1) sL = evalSL t (N.to_nat P - 1) sTarg.
Proof.
  induction b0 as [|r rs IH]; intros slopes sL sTarg bFin h.
  - destruct slopes as [|? ?]; simpl in h; [| discriminate].
    injection h as <- <- <-.
    exact (conj I (conj I (conj I (conj eq_refl (conj eq_refl (fun _ _ => eq_refl)))))).
  - destruct slopes as [|sl sls]; simpl buildSym in h; [discriminate |].
    destruct (buildSym P rs sls) as [sL1 sTarg1 bFin1 |] eqn:hrest;
      [| simpl in h; discriminate].
    destruct (IH sls sL1 sTarg1 bFin1 hrest) as [hPsL1 [hPsT1 [hPb1 [h0 [hfin hstep]]]]].
    destruct r as [d b cnt | d1 b1 d2 b2 cnt]; unfold buildSymOne in h; cbv beta iota zeta in h;
      destruct (N.eqb cnt 0) eqn:hc0; try discriminate; apply N.eqb_neq in hc0.
    + (* LOne *)
      destruct sl as [| dd | dd].
      * injection h as <- <- <-.
        split; [simpl; split; [lia | exact hPsL1] |].
        split; [simpl; split; [lia | exact hPsT1] |].
        split; [simpl; split; [lia | exact hPb1] |].
        split; [simpl; rewrite h0; reflexivity |].
        split; [simpl; rewrite hfin; reflexivity |].
        intros t ht; simpl; rewrite (hstep t ht); reflexivity.
      * injection h as <- <- <-.
        split; [simpl; split; [lia | exact hPsL1] |].
        split; [simpl; split; [lia | exact hPsT1] |].
        split; [simpl; split; [lia | exact hPb1] |].
        split; [simpl; rewrite Nat.add_0_r, h0; reflexivity |].
        split.
        -- simpl; rewrite hfin; f_equal; f_equal.
           rewrite !N2Nat.inj_add, !N2Nat.inj_mul; nia.
        -- intros t ht; simpl; rewrite (hstep t ht); f_equal; f_equal.
           rewrite !N2Nat.inj_add; nia.
      * cbv zeta in h.
        destruct (N.leb (P * dd + 1) cnt) eqn:hble; [| discriminate].
        apply N.leb_le in hble. injection h as <- <- <-.
        assert (hge : N.to_nat P * N.to_nat dd + 1 <= N.to_nat cnt) by lia.
        split; [simpl; split; [lia | exact hPsL1] |].
        split; [simpl; split; [lia | exact hPsT1] |].
        split; [simpl; split; [lia | exact hPb1] |].
        split.
        -- simpl; rewrite Nat.sub_0_r, h0; f_equal; f_equal.
           rewrite !N2Nat.inj_add, !N2Nat.inj_sub, !N2Nat.inj_mul; nia.
        -- split.
           ++ simpl; rewrite Nat.sub_diag, Nat.add_0_r, hfin; reflexivity.
           ++ intros t ht; simpl; rewrite (hstep t ht); f_equal; f_equal.
              rewrite !N2Nat.inj_add, !N2Nat.inj_sub, !N2Nat.inj_mul; nia.
    + (* LTwo *)
      destruct sl as [| dd | dd].
      * injection h as <- <- <-.
        split; [simpl; split; [lia | exact hPsL1] |].
        split; [simpl; split; [lia | exact hPsT1] |].
        split; [simpl; split; [lia | exact hPb1] |].
        split; [simpl; rewrite h0; reflexivity |].
        split; [simpl; rewrite hfin; reflexivity |].
        intros t ht; simpl; rewrite (hstep t ht); reflexivity.
      * injection h as <- <- <-.
        split; [simpl; split; [lia | exact hPsL1] |].
        split; [simpl; split; [lia | exact hPsT1] |].
        split; [simpl; split; [lia | exact hPb1] |].
        split; [simpl; rewrite Nat.add_0_r, h0; reflexivity |].
        split.
        -- simpl; rewrite hfin; f_equal; f_equal.
           rewrite !N2Nat.inj_add, !N2Nat.inj_mul; nia.
        -- intros t ht; simpl; rewrite (hstep t ht); f_equal; f_equal.
           rewrite !N2Nat.inj_add; nia.
      * cbv zeta in h.
        destruct (N.leb (P * dd + 1) cnt) eqn:hble; [| discriminate].
        apply N.leb_le in hble. injection h as <- <- <-.
        assert (hge : N.to_nat P * N.to_nat dd + 1 <= N.to_nat cnt) by lia.
        split; [simpl; split; [lia | exact hPsL1] |].
        split; [simpl; split; [lia | exact hPsT1] |].
        split; [simpl; split; [lia | exact hPb1] |].
        split.
        -- simpl; rewrite Nat.sub_0_r, h0; f_equal; f_equal.
           rewrite !N2Nat.inj_add, !N2Nat.inj_sub, !N2Nat.inj_mul; nia.
        -- split.
           ++ simpl; rewrite Nat.sub_diag, Nat.add_0_r, hfin; reflexivity.
           ++ intros t ht; simpl; rewrite (hstep t ht); f_equal; f_equal.
              rewrite !N2Nat.inj_add, !N2Nat.inj_sub, !N2Nat.inj_mul; nia.
Qed.

Lemma applyJumpK_sound {ls l_out : list LRun} {p m ssteps : N} {w : list bool}
    {slopes : list SlopeSpec}
    (h : applyJumpK ls p m ssteps w slopes = Some l_out) (hPL : PosL ls) :
  PosL l_out /\
  evalSegCfg mAR0 (expandL ls) [] -[ tm ]->* evalSegCfg mAR0 (expandL l_out) [].
Proof.
  unfold applyJumpK in h.
  destruct (N.eqb m 0) eqn:hm0; [discriminate |].
  apply N.eqb_neq in hm0.
  cbv beta iota zeta in h.
  rewrite (prePostK_eq (m - 1)%N) in h; cbv beta iota in h.
  set (kn := N.to_nat (m - 1)%N) in *.
  destruct (carryWFuel w (N.of_nat (postVal kn))) as [w_out extra |] eqn:hcw; [| discriminate].
  set (P := (N.of_nat (preVal kn) + N.of_nat (postVal kn) + extra)%N) in h.
  set (Pn := N.to_nat P).
  assert (hPn_eq : Pn = preVal kn + postVal kn + N.to_nat extra) by (unfold Pn, P; lia).
  assert (hP1 : 1 <= N.to_nat P).
  { pose proof (postVal_ge_two kn); unfold Pn in hPn_eq; lia. }
  destruct (peelRun 0 true ls p) as [l1 |] eqn:hp1; [| discriminate].
  destruct (peelRun 0 false l1 (2 * m)) as [l2 |] eqn:hp2; [| discriminate].
  destruct (peelW w l2) as [l3 |] eqn:hp3; [| discriminate].
  destruct (peelRun 0 false l3 1) as [l4 |] eqn:hp4; [| discriminate].
  destruct (peelRun_sound 0 true ls p l1 hp1 hPL) as [he1 hPL1].
  destruct (peelRun_sound 0 false l1 (2 * m) l2 hp2 hPL1) as [he2 hPL2].
  destruct (peelW_sound w l2 l3 hp3 hPL2) as [he3 hPL3].
  destruct (peelRun_sound 0 false l3 1 l4 hp4 hPL3) as [he4 hPL4].
  destruct (normL_sound l4 hPL4) as [heB0 hPB0].
  destruct (buildSym P (normL l4) slopes) as [sL_body sTarg b_fin |] eqn:hbs; [| discriminate].
  destruct (buildSym_sound P hP1 (normL l4) slopes sL_body sTarg b_fin hbs)
    as [hPsL [hPsT [hPBfin [hsL0 [hsTfin hsStep]]]]].
  fold Pn in hsL0, hsTfin, hsStep.
  destruct (pushSL1 sL_body 2 false (SCConst 1)) as [sL0 |] eqn:hps0; [| discriminate].
  destruct (pushSL1_sound hps0 ltac:(simpl; lia) hPsL) as [hPsL0 heps0].
  destruct (runSymRLEK ssteps mEL sL0 [SROne 1 0 (SCConst 1)]) as [m_end sL_end r_end |] eqn:hrun;
    [| discriminate].
  destruct m_end; try discriminate.
  destruct r_end as [|? ?]; [| discriminate].
  assert (hPsR0 : PosSR [SROne 1 0 (SCConst 1)]) by (simpl; split; [lia | exact I]).
  destruct (runSymRLEK_sound ssteps mEL sL0 [SROne 1 0 (SCConst 1)] mAR0 sL_end [] hrun hPsL0 hPsR0)
    as [hPsLend [_ hsym_run]].
  destruct (normSL sL_end) as [sL_norm |] eqn:hnm; [| discriminate].
  destruct (beqListSLRun sL_norm sTarg) eqn:hbeq; [| discriminate].
  apply beqListSLRun_iff in hbeq; subst sL_norm.
  injection h as <-.
  destruct (normSL_sound hnm hPsLend) as [_ henm].
  destruct (pushL1_sound b_fin 0 false 1 hPBfin) as [heo1 hPo1].
  destruct (pushW_sound w_out _ hPo1) as [heo2 hPo2].
  destruct (pushL1_sound _ 0 false (2 * m) hPo2) as [heo3 hPo3].
  destruct (pushL1_sound _ 0 true p hPo3) as [heo4 hPo4].
  refine (conj hPo4 _).
  change (evalSegCfg mAR0 (expandL ls) [] -[ tm ]->*
    evalSegCfg mAR0 (expandL (pushL1 (pushL1 (pushW w_out (pushL1 b_fin 0 false 1)) 0 false (2 * m)) 0 true p)) []).
  set (bfn := fun t : nat =>
    if Nat.leb t (Pn - 1) then evalSL t (Pn - 1) sL_body else expandL b_fin).
  assert (hB0 : bfn 0 = expandL (normL l4)).
  { unfold bfn; simpl Nat.leb; exact hsL0. }
  assert (hBP : bfn Pn = expandL b_fin).
  { unfold bfn.
    assert (hgt : Nat.leb Pn (Pn - 1) = false) by (apply Nat.leb_gt; lia).
    rewrite hgt; reflexivity. }
  assert (hBP2 : forall t, t < preVal kn + postVal kn + N.to_nat extra -> P2 (bfn t) (bfn (t + 1))).
  { intros t ht rs_tail.
    assert (htle : Nat.leb t (Pn - 1) = true) by (apply Nat.leb_le; lia).
    assert (hBt : bfn t = evalSL t (Pn - 1) sL_body) by (unfold bfn; rewrite htle; reflexivity).
    assert (hBt1 : bfn (t + 1) = evalSL t (Pn - 1) sTarg).
    { unfold bfn. destruct (Nat.leb (t + 1) (Pn - 1)) eqn:ht1.
      - apply Nat.leb_le in ht1; exact (hsStep t ht1).
      - apply Nat.leb_gt in ht1.
        assert (hteq : t = Pn - 1) by lia.
        rewrite hteq, hsTfin; reflexivity. }
    rewrite hBt, hBt1, evalA_zero_false.
    pose proof (hsym_run t (Pn - 1) rs_tail) as hr.
    rewrite (heps0 t (Pn - 1)), <- (henm t (Pn - 1)) in hr.
    simpl in hr; exact hr. }
  pose proof (odom_carryW_jump (N.to_nat p) kn w w_out extra bfn hcw hBP2) as hj.
  rewrite <- hPn_eq in hj.
  assert (hm2 : N.to_nat (2 * m) = 2 * (kn + 1)) by (unfold kn; lia).
  assert (hL_eq : expandL ls =
      repeat (0, true) (N.to_nat p) ++ repeat (0, false) (2 * (kn + 1)) ++
      encW w ++ (0, false) :: bfn 0).
  { rewrite he1, he2, he3, he4, <- heB0, hB0, hm2; simpl (N.to_nat 0); simpl (N.to_nat 1);
      simpl repeat; repeat rewrite <- app_assoc; reflexivity. }
  assert (hLout_eq :
      expandL (pushL1 (pushL1 (pushW w_out (pushL1 b_fin 0 false 1)) 0 false (2 * m)) 0 true p) =
      repeat (0, true) (N.to_nat p) ++ repeat (0, false) (2 * (kn + 1)) ++
      encW w_out ++ (0, false) :: bfn Pn).
  { rewrite heo4, heo3, heo2, heo1, hBP, hm2; simpl (N.to_nat 0); simpl (N.to_nat 1);
      simpl repeat; repeat rewrite <- app_assoc; reflexivity. }
  rewrite hL_eq, hLout_eq; exact hj.
Qed.

Lemma execOpK_sound (op : Op) (ls ls' : list LRun)
    (h : execOpK op ls = Some ls') (hPL : PosL ls) :
  PosL ls' /\ evalSegCfg mAR0 (expandL ls) [] -[ tm ]->* evalSegCfg mAR0 (expandL ls') [].
Proof.
  destruct op as [steps | p m ssteps w slopes].
  - unfold execOpK in h.
    destruct (runRLEK steps mAR0 ls []) as [m' l1 r1 | |] eqn:hr; try discriminate.
    destruct m'; try discriminate.
    destruct r1 as [|? ?]; [| discriminate].
    injection h as <-.
    destruct (proj1 (runRLEK_sound steps mAR0 ls [] hPL I) mAR0 l1 [] hr) as [hPL' [_ hstep]].
    exact (conj hPL' hstep).
  - exact (applyJumpK_sound h hPL).
Qed.

Lemma execOpsK_sound (ops : list Op) :
  forall (ls ls' : list LRun), execOpsK ops ls = Some ls' -> PosL ls ->
    PosL ls' /\ evalSegCfg mAR0 (expandL ls) [] -[ tm ]->* evalSegCfg mAR0 (expandL ls') [].
Proof.
  induction ops as [|op rest IH]; intros ls ls' h hPL.
  - simpl in h; injection h as <-; exact (conj hPL (evstep_refl tm _)).
  - simpl in h.
    destruct (execOpK op ls) as [l1 |] eqn:ho; [| discriminate].
    destruct (execOpK_sound op ls l1 ho hPL) as [hPL1 h1].
    destruct (IH l1 ls' h hPL1) as [hPL' h2].
    exact (conj hPL' (evstep_trans tm _ _ _ h1 h2)).
Qed.

Lemma check_all_ops_sound (ops : list Op) (h : check_all_ops ops = true) :
  halts tm c0.
Proof.
  unfold check_all_ops in h.
  destruct (runRLEK 22 mCL [LOne 0 false 1] [ROne 0 1 1]) as [m0 l0 r0 | |] eqn:hr0; try discriminate.
  destruct m0; try discriminate.
  destruct r0 as [|? ?]; [| discriminate].
  destruct (execOpsK ops l0) as [l_fin |] eqn:hex; [| discriminate].
  destruct (runRLEK 251 mAR0 l_fin []) as [? ? ? | |] eqn:hrf; try discriminate.
  assert (hPinitL : PosL [LOne 0 false 1]) by (simpl; split; [lia | exact I]).
  assert (hPinitR : PosR [ROne 0 1 1]) by (simpl; split; [lia | exact I]).
  destruct (proj1 (runRLEK_sound 22 mCL [LOne 0 false 1] [ROne 0 1 1] hPinitL hPinitR) mAR0 l0 [] hr0)
    as [hPl0 [_ hstep0]].
  simpl expandL in hstep0; simpl expandR in hstep0.
  destruct (execOpsK_sound ops l0 l_fin hex hPl0) as [hPlfin hstep_ops].
  pose proof (proj2 (runRLEK_sound 251 mAR0 l_fin [] hPlfin I) hrf) as hhalt_fin.
  simpl expandR in hhalt_fin.
  eapply halts_evstep; [| exact (progress_evstep _ _ _ init_reaches_segmented_system)].
  eapply halts_evstep; [| exact hstep0].
  eapply halts_evstep; [exact hhalt_fin | exact hstep_ops].
Qed.

(* ========================================================================= *)
(* Section 7: Certificate Verification & Main Theorem                        *)
(* ========================================================================= *)

Local Open Scope N_scope.

Definition ops_chunk_0 : list Op := [
  OpRun 51;
  OpRun 51;
  OpRun 158;
  OpRun 66;
  OpRun 174;
  OpRun 64;
  OpRun 192;
  OpRun 93;
  OpRun 100;
  OpRun 107;
  OpRun 247;
  OpRun 93;
  OpRun 194;
  OpRun 184;
  OpRun 225;
  OpRun 80;
  OpRun 208;
  OpRun 109;
  OpRun 116;
  OpRun 125;
  OpRun 180;
  OpRun 134;
  OpRun 133;
  OpRun 135;
  OpRun 195;
  OpRun 229;
  OpRun 120;
  OpRun 345;
  OpRun 338;
  OpRun 208;
  OpRun 210;
  OpRun 210;
  OpRun 287;
  OpRun 188;
  OpRun 169;
  OpRun 96;
  OpRun 428;
  OpRun 194;
  OpRun 126;
  OpRun 132;
  OpRun 187;
  OpRun 180;
  OpRun 121;
  OpRun 120;
  OpRun 124;
  OpRun 196;
  OpRun 120;
  OpRun 108;
  OpRun 202;
  OpRun 244;
  OpRun 210;
  OpRun 236;
  OpRun 225;
  OpRun 401;
  OpJump 3 1 153 [true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 238;
  OpRun 237;
  OpRun 239;
  OpRun 412;
  OpRun 229;
  OpRun 228;
  OpRun 537;
  OpRun 192;
  OpRun 93;
  OpRun 148;
  OpRun 102;
  OpRun 101;
  OpRun 103;
  OpRun 172;
  OpJump 2 1 54 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 54 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpRun 110;
  OpRun 103;
  OpRun 110;
  OpRun 186;
  OpJump 2 1 54 [false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpRun 122;
  OpRun 114;
  OpRun 181;
  OpRun 184;
  OpRun 109;
  OpRun 205;
  OpRun 92;
  OpRun 332;
  OpRun 182;
  OpRun 192;
  OpRun 196;
  OpRun 446;
  OpJump 2 1 121 [false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 121 [true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 121 [false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 121 [true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 193;
  OpRun 192;
  OpRun 179;
  OpRun 326;
  OpRun 186;
  OpRun 130;
  OpRun 250;
  OpRun 263;
  OpRun 64;
  OpRun 232;
  OpRun 64;
  OpRun 345;
  OpRun 144;
  OpRun 151;
  OpRun 160;
  OpRun 266;
  OpRun 169;
  OpRun 168;
  OpRun 170;
  OpRun 290;
  OpJump 3 1 112 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 112 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 112 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 112 [false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 112 [true; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 200;
  OpRun 183;
  OpRun 158;
  OpRun 336;
  OpRun 333;
  OpRun 379;
  OpRun 190;
  OpRun 665;
  OpJump 3 1 153 [false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 234;
  OpRun 225;
  OpRun 234;
  OpRun 415;
  OpJump 3 1 153 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 1 153 [true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 153 [false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 153 [true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 238;
  OpRun 237;
  OpRun 241;
  OpRun 430;
  OpRun 237;
  OpRun 306;
  OpRun 704;
  OpRun 589;
  OpRun 142;
  OpRun 92;
  OpRun 98;
  OpRun 135;
  OpRun 128;
  OpJump 2 2 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 101;
  OpRun 100;
  OpRun 104;
  OpRun 172;
  OpRun 101;
  OpRun 92;
  OpRun 331;
  OpRun 655;
  OpJump 2 1 271 [false; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 271 [true; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 271 [false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 271 [true; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 271 [false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 271 [true; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpRun 340;
  OpRun 339;
  OpRun 343;
  OpRun 994;
  OpJump 2 1 627 [true; false; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 1 627 [false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 1 627 [true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 1 627 [false; false; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 1 627 [true; false; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpRun 696;
  OpRun 695;
  OpRun 685;
  OpRun 1324;
  OpRun 379;
  OpRun 371;
  OpRun 733;
  OpRun 726;
  OpRun 386;
  OpRun 390;
  OpRun 179;
  OpRun 322;
  OpJump 2 1 121 [true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [false; true; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [true; true; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [false; false; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [true; false; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [false; true; true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpRun 191;
  OpRun 190;
  OpRun 334;
  OpRun 343;
  OpRun 191;
  OpRun 187;
  OpRun 134;
  OpRun 439
].

Definition ops_chunk_1 : list Op := [
  OpRun 243;
  OpRun 121;
  OpRun 176;
  OpRun 107;
  OpRun 194;
  OpRun 104;
  OpRun 146;
  OpRun 317;
  OpRun 213;
  OpRun 362;
  OpRun 386;
  OpRun 227;
  OpRun 229;
  OpRun 222;
  OpRun 299;
  OpRun 163;
  OpRun 316;
  OpRun 130;
  OpRun 222;
  OpRun 139;
  OpRun 138;
  OpRun 140;
  OpRun 246;
  OpJump 2 1 84 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 84 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 84 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 84 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 84 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 84 [false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 84 [true; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 1 84 [false; false; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 1 84 [true; false; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 156;
  OpRun 155;
  OpRun 142;
  OpRun 249;
  OpRun 144;
  OpRun 242;
  OpRun 441;
  OpRun 341;
  OpJump 2 1 68 [false; false; true; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpRun 143;
  OpRun 142;
  OpRun 146;
  OpRun 318;
  OpRun 139;
  OpRun 126;
  OpRun 217;
  OpRun 473;
  OpRun 235;
  OpRun 236;
  OpRun 407;
  OpRun 398;
  OpJump 2 2 153 [false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 153 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 209;
  OpRun 209;
  OpRun 218;
  OpRun 396;
  OpJump 2 1 153 [false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 153 [true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 2 153 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 2 153 [true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 3 153 [false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 3 153 [true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 2 153 [false; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 153 [false; false; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 153 [true; false; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 153 [false; true; false; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 250;
  OpRun 241;
  OpRun 498;
  OpRun 279;
  OpRun 303;
  OpRun 338;
  OpRun 128;
  OpRun 222;
  OpRun 226;
  OpRun 224;
  OpRun 214;
  OpRun 226;
  OpJump 1 1 89 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 2 89 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 2 89 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 3 89 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 3 89 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 4 89 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 2 89 [false; false; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 1 89 [false; false; true; false; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 1 89 [true; false; true; false; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 1 89 [false; true; false; true; true; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 170;
  OpRun 155;
  OpRun 263;
  OpRun 247;
  OpRun 366;
  OpRun 113;
  OpRun 346;
  OpRun 888;
  OpJump 1 1 381 [true; false; false; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 1 381 [false; true; true; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 1 381 [true; true; true; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 2 381 [true; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 2 381 [false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 2 381 [true; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 1 381 [false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 1 381 [true; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 1 381 [false; true; true; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpRun 447;
  OpRun 446;
  OpRun 504;
  OpRun 498;
  OpRun 264;
  OpRun 263;
  OpRun 265;
  OpRun 662;
  OpRun 523;
  OpRun 533;
  OpRun 537;
  OpRun 1501;
  OpJump 1 1 474 [false; true; false; false; false; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 1 474 [true; true; false; false; false; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 3 474 [false; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 1 3 474 [true; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpRun 513;
  OpRun 512;
  OpRun 521;
  OpRun 1086;
  OpRun 483;
  OpRun 369;
  OpRun 378;
  OpRun 742;
  OpJump 1 1 331 [false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 4; SlZ];
  OpRun 385;
  OpRun 384;
  OpRun 511;
  OpRun 318;
  OpJump 1 2 121 [true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 2 121 [false; true; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 2 121 [true; true; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 3 121 [true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 3 121 [false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 2 121 [false; false; true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 2 121 [true; false; true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 1 121 [false; false; false; true; false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 1 121 [true; false; false; true; false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 191;
  OpRun 190;
  OpRun 177;
  OpRun 328;
  OpRun 177;
  OpRun 119;
  OpRun 265;
  OpRun 425;
  OpRun 147;
  OpRun 447;
  OpRun 145;
  OpRun 254;
  OpRun 152;
  OpRun 151;
  OpRun 160;
  OpRun 282;
  OpRun 169;
  OpRun 166;
  OpRun 156;
  OpRun 480;
  OpRun 623;
  OpRun 752;
  OpRun 426;
  OpRun 681;
  OpRun 339;
  OpRun 483;
  OpRun 487;
  OpRun 938;
  OpRun 485;
  OpRun 485;
  OpRun 492;
  OpRun 950;
  OpRun 498;
  OpRun 494;
  OpRun 346;
  OpRun 678;
  OpRun 372;
  OpRun 316;
  OpRun 178;
  OpRun 177;
  OpRun 179;
  OpRun 340;
  OpJump 1 1 139 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 139 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 139 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 139 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 139 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 139 [false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 190;
  OpRun 134;
  OpRun 136;
  OpRun 220;
  OpRun 123;
  OpRun 122
].

Definition ops_chunk_2 : list Op := [
  OpRun 129;
  OpRun 323;
  OpRun 184;
  OpRun 125;
  OpRun 122;
  OpRun 227;
  OpRun 134;
  OpRun 131;
  OpRun 298;
  OpRun 390;
  OpJump 1 1 154 [false; false; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 154 [true; false; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 154 [false; true; true; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 211;
  OpRun 205;
  OpRun 646;
  OpRun 504;
  OpJump 1 2 139 [true; true; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 139 [false; false; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 139 [false; false; true; false; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 179;
  OpRun 179;
  OpRun 188;
  OpRun 352;
  OpJump 1 1 139 [false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 139 [true; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 139 [false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 139 [true; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 139 [false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 139 [true; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 139 [false; false; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 139 [true; false; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 139 [false; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 139 [false; false; true; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 139 [true; false; true; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 139 [false; true; false; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 139 [false; false; true; true; false; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 198;
  OpRun 197;
  OpRun 201;
  OpRun 485;
  OpRun 170;
  OpRun 298;
  OpRun 167;
  OpRun 309;
  OpJump 1 1 121 [true; true; false; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 121 [false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 121 [true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 121 [false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 121 [false; false; false; false; true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 121 [true; false; false; false; true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 121 [false; true; true; false; true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 190;
  OpRun 192;
  OpRun 338;
  OpRun 258;
  OpRun 299;
  OpRun 243;
  OpRun 48;
  OpRun 403;
  OpRun 144;
  OpJump 0 1 50 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 2 50 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 2 50 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 3 50 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 3 50 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 4 50 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 4 50 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 4 50 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 3 50 [false; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 2 50 [false; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 1 50 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 74;
  OpRun 73;
  OpRun 83;
  OpRun 158;
  OpRun 90;
  OpRun 90;
  OpRun 91;
  OpRun 180;
  OpJump 0 1 50 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 2 50 [false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 2 50 [true; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 3 50 [false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 3 50 [true; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 3 50 [false; false; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 3 50 [true; false; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 2 50 [false; false; false; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 2 50 [true; false; false; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 2 50 [false; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 1 50 [false; false; true; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 1 50 [true; false; true; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 0 1 50 [false; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 103;
  OpRun 101;
  OpRun 169;
  OpRun 220;
  OpRun 70;
  OpRun 66;
  OpRun 63;
  OpRun 448;
  OpRun 164;
  OpRun 189;
  OpRun 199;
  OpRun 394;
  OpJump 0 1 153 [false; true; true; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 0 1 153 [true; true; true; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 0 2 153 [true; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 0 2 153 [false; true; false; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 0 2 153 [true; true; false; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 0 4 153 [true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 0 5 153 [true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 0 2 153 [false; false; false; false; false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 0 2 153 [true; false; false; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 0 1 153 [false; false; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 0 1 153 [true; false; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 196;
  OpRun 204;
  OpRun 175;
  OpRun 338;
  OpRun 358;
  OpRun 401;
  OpRun 509;
  OpRun 219;
  OpRun 112;
  OpRun 204;
  OpRun 119;
  OpRun 118;
  OpRun 127;
  OpRun 232;
  OpRun 136;
  OpRun 135;
  OpRun 137;
  OpRun 256;
  OpJump 1 1 104 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 2 104 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 2 104 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 3 104 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 3 104 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 4 104 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 4 104 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 5 104 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 5 104 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 2 104 [false; false; false; false; false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 1 104 [false; false; true; false; false; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 1 1 104 [true; false; true; false; false; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpRun 165;
  OpRun 157;
  OpRun 154;
  OpRun 275;
  OpRun 231;
  OpRun 316;
  OpRun 305;
  OpRun 174;
  OpRun 93;
  OpRun 386;
  OpRun 435;
  OpRun 377;
  OpRun 280;
  OpRun 240;
  OpRun 249;
  OpRun 450;
  OpJump 1 1 185 [false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 185 [true; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 185 [true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 185 [true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 185 [false; true; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 185 [true; true; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 4 185 [true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 4 185 [false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 4 185 [true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 4 185 [false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 185 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 185 [false; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 185 [false; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 225;
  OpRun 225;
  OpRun 234;
  OpRun 446;
  OpRun 243;
  OpRun 240;
  OpRun 242;
  OpRun 468;
  OpJump 1 1 185 [true; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 185 [false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 185 [true; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 185 [false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 185 [true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 4 185 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 4 185 [true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 4 185 [false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 4 185 [true; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 185 [false; false; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 185 [true; false; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 3 185 [false; true; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 185 [false; false; true; true; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 2 185 [true; false; true; true; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 185 [false; false; false; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 185 [true; false; false; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 256
].

Definition ops_chunk_3 : list Op := [
  OpRun 255;
  OpRun 242;
  OpRun 470;
  OpRun 245;
  OpRun 255;
  OpRun 586;
  OpRun 491;
  OpRun 280;
  OpRun 226;
  OpRun 442;
  OpRun 735;
  OpRun 263;
  OpRun 258;
  OpRun 143;
  OpRun 248;
  OpRun 152;
  OpRun 151;
  OpRun 153;
  OpRun 272;
  OpJump 2 1 111 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 111 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 111 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 111 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 111 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 111 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 111 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 111 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 111 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 111 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 111 [false; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 111 [false; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 111 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 111 [false; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 167;
  OpRun 153;
  OpRun 162;
  OpRun 286;
  OpRun 171;
  OpRun 168;
  OpRun 170;
  OpRun 308;
  OpJump 2 1 111 [true; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 111 [false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 111 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 111 [false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 111 [true; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 111 [false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 111 [true; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 111 [false; false; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 111 [true; false; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 111 [false; false; false; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 111 [true; false; false; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 111 [false; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 111 [false; false; true; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 111 [true; false; true; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 111 [false; false; false; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 111 [true; false; false; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 198;
  OpRun 181;
  OpRun 156;
  OpRun 841;
  OpRun 437;
  OpRun 903;
  OpRun 790;
  OpRun 944;
  OpRun 452;
  OpRun 453;
  OpRun 455;
  OpRun 874;
  OpJump 2 1 367 [true; false; true; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 367 [false; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 367 [true; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 4 367 [true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 5 367 [true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 3 367 [false; false; false; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 367 [false; false; false; false; true; false; false; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 367 [true; false; false; false; true; false; false; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 367 [false; true; true; false; true; false; false; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpRun 463;
  OpRun 377;
  OpRun 550;
  OpRun 542;
  OpRun 294;
  OpRun 293;
  OpRun 338;
  OpRun 856;
  OpRun 342;
  OpRun 507;
  OpRun 706;
  OpRun 1372;
  OpJump 2 1 627 [false; true; false; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 1 627 [true; true; false; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 2 627 [false; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 2 627 [true; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 3 627 [false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 3 627 [true; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 4 627 [true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 4 627 [false; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 4 627 [true; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 4 627 [false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 3 627 [false; false; true; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 3 627 [true; false; true; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 2 627 [false; false; false; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 2 627 [true; false; false; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 2 627 [false; true; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 1 627 [false; false; true; true; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpRun 704;
  OpRun 690;
  OpRun 389;
  OpRun 1086;
  OpJump 2 1 331 [false; true; false; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 4; SlZ];
  OpRun 420;
  OpRun 418;
  OpRun 771;
  OpRun 765;
  OpRun 301;
  OpRun 193;
  OpRun 197;
  OpRun 358;
  OpJump 2 1 121 [true; false; false; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [false; true; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [true; true; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [false; true; false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [true; true; false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 121 [false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 121 [true; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 121 [false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 121 [true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 121 [false; false; false; false; false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [false; false; true; false; false; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [true; false; true; false; false; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [false; true; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [false; false; true; true; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [true; false; true; true; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [false; true; false; false; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpRun 208;
  OpRun 207;
  OpRun 349;
  OpRun 349;
  OpRun 189;
  OpRun 134;
  OpRun 237;
  OpRun 448;
  OpRun 164;
  OpRun 361;
  OpRun 406;
  OpRun 319;
  OpRun 178;
  OpRun 304;
  OpRun 185;
  OpRun 184;
  OpRun 193;
  OpRun 332;
  OpRun 202;
  OpRun 199;
  OpRun 189;
  OpRun 572;
  OpRun 270;
  OpRun 397;
  OpRun 179;
  OpRun 317;
  OpRun 270;
  OpRun 252;
  OpRun 240;
  OpRun 600;
  OpRun 324;
  OpRun 324;
  OpRun 331;
  OpRun 612;
  OpRun 338;
  OpRun 337;
  OpRun 324;
  OpRun 608;
  OpRun 334;
  OpRun 251;
  OpRun 256;
  OpRun 304;
  OpRun 178;
  OpRun 359;
  OpRun 144;
  OpRun 250;
  OpRun 153;
  OpRun 152;
  OpRun 154;
  OpRun 274;
  OpJump 2 1 98 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 98 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 98 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 98 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 98 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 4 98 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 4 98 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 5 98 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 5 98 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 6 98 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 6 98 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 98 [false; false; false; false; false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 98 [false; false; true; false; false; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 98 [true; false; true; false; false; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ]
].

Definition ops_chunk_4 : list Op := [
  OpJump 2 2 98 [false; true; false; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 185;
  OpRun 182;
  OpRun 176;
  OpRun 499;
  OpRun 162;
  OpRun 256;
  OpRun 269;
  OpRun 332;
  OpRun 142;
  OpRun 141;
  OpRun 145;
  OpRun 247;
  OpRun 143;
  OpRun 273;
  OpRun 481;
  OpRun 472;
  OpJump 2 1 187 [false; false; false; false; false; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 261;
  OpRun 260;
  OpRun 267;
  OpRun 503;
  OpRun 263;
  OpRun 138;
  OpRun 125;
  OpRun 201;
  OpRun 405;
  OpRun 108;
  OpRun 460;
  OpRun 692;
  OpJump 2 2 204 [true; false; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 2 204 [false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 2 204 [true; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 3 204 [true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 4 204 [true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 4 204 [false; true; true; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 4 204 [true; true; true; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 5 204 [true; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 5 204 [false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 5 204 [true; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 5 204 [false; false; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 4 204 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 3 204 [false; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 2 204 [false; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 1 204 [false; false; true; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpRun 260;
  OpRun 260;
  OpRun 269;
  OpRun 500;
  OpRun 278;
  OpRun 277;
  OpRun 277;
  OpRun 522;
  OpJump 2 1 204 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 2 204 [false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 2 204 [true; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 3 204 [false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 3 204 [true; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 4 204 [false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 4 204 [true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 5 204 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 4 204 [false; false; true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 3 204 [false; false; true; false; true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 2 204 [false; false; true; false; true; false; true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 2 1 204 [false; false; true; false; true; false; true; false; true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpRun 289;
  OpRun 288;
  OpRun 297;
  OpRun 559;
  OpRun 304;
  OpRun 597;
  OpRun 338;
  OpRun 428;
  OpJump 2 1 156 [true; true; false; true; false; true; false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ; SlZ; SlZ; SlZ];
  OpRun 238;
  OpRun 229;
  OpRun 233;
  OpRun 418;
  OpJump 2 1 423 [true; false; false; true; false; true; false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 1 423 [false; true; true; true; false; true; false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 1 423 [true; true; true; true; false; true; false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 2 423 [true; true; false; true; false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 3 423 [false; true; false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 3 423 [true; true; false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 4 423 [false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 4 423 [true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 5 423 [false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 5 423 [true; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 4 423 [false; false; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 4 423 [true; false; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 4 423 [false; true; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 3 423 [false; false; true; true; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 3 423 [true; false; true; true; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 2 423 [false; false; false; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 2 423 [true; false; false; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 2 423 [false; true; true; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 1 423 [false; false; true; true; true; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 1 423 [true; false; true; true; true; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 2 1 423 [false; true; false; false; true; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpRun 525;
  OpRun 524;
  OpRun 983;
  OpRun 983;
  OpRun 512;
  OpRun 372;
  OpRun 374;
  OpRun 750;
  OpRun 532;
  OpRun 394;
  OpRun 258;
  OpRun 869;
  OpRun 269;
  OpRun 664;
  OpRun 235;
  OpRun 448;
  OpRun 244;
  OpRun 243;
  OpRun 245;
  OpRun 472;
  OpJump 1 1 212 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 1 1 212 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 252;
  OpRun 248;
  OpRun 254;
  OpRun 276;
  OpRun 154;
  OpRun 151;
  OpRun 126;
  OpRun 386;
  OpRun 193;
  OpRun 339;
  OpRun 450;
  OpRun 380;
  OpJump 1 2 153 [true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 192;
  OpRun 191;
  OpRun 198;
  OpRun 372;
  OpRun 119;
  OpRun 332;
  OpRun 48;
  OpRun 278;
  OpRun 111;
  OpRun 118;
  OpRun 127;
  OpRun 216;
  OpRun 136;
  OpRun 135;
  OpRun 137;
  OpRun 240;
  OpJump 2 1 88 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 88 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 88 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 88 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 88 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 4 88 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 4 88 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 5 88 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 5 88 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 6 88 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 6 88 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 6 88 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 5 88 [false; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 4 88 [false; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 88 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 88 [false; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 1 88 [false; false; true; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 144;
  OpRun 137;
  OpRun 146;
  OpRun 254;
  OpRun 155;
  OpRun 154;
  OpRun 154;
  OpRun 276;
  OpJump 2 1 88 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 88 [false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 88 [true; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 88 [false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 88 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 4 88 [false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 4 88 [true; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 5 88 [false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 5 88 [true; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 5 88 [false; false; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 5 88 [true; false; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 4 88 [false; false; false; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 4 88 [true; false; false; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 4 88 [false; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 88 [false; false; true; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 3 88 [true; false; true; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 88 [false; false; false; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 88 [true; false; false; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 2 88 [false; true; true; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 1 88 [false; false; true; true; true; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 2 1 88 [true; false; true; true; true; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 189;
  OpRun 181;
  OpRun 171;
  OpRun 309
].

Definition ops_chunk_5 : list Op := [
  OpRun 181;
  OpRun 172;
  OpRun 477;
  OpRun 468;
  OpRun 260;
  OpRun 258;
  OpRun 155;
  OpRun 274;
  OpJump 2 1 72 [true; false; false; false; true; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 72 [false; true; true; false; true; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 72 [true; true; true; false; true; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 72 [true; false; true; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 72 [false; false; false; true; false; false; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 72 [true; false; false; true; false; false; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 72 [false; true; true; true; false; false; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpRun 157;
  OpRun 149;
  OpRun 236;
  OpRun 314;
  OpRun 134;
  OpRun 131;
  OpRun 128;
  OpRun 430;
  OpRun 348;
  OpRun 220;
  OpRun 217;
  OpRun 587;
  OpJump 2 1 153 [false; true; false; false; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 153 [true; true; false; false; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 5 153 [true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 6 153 [true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 7 153 [true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 4 153 [false; false; false; false; false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 4 153 [true; false; false; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 3 153 [false; false; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 3 153 [true; false; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 153 [false; false; false; false; false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 2 1 153 [true; false; false; false; false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 242;
  OpRun 241;
  OpRun 231;
  OpRun 425;
  OpRun 166;
  OpRun 296;
  OpRun 546;
  OpRun 770;
  OpRun 384;
  OpRun 266;
  OpRun 478;
  OpRun 275;
  OpRun 277;
  OpRun 278;
  OpRun 292;
  OpJump 3 1 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 2 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 2 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 3 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 3 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 4 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 4 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 5 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 5 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 6 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 6 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 7 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 7 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 4 106 [false; false; false; false; false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 4 106 [true; false; false; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 3 106 [false; false; false; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 3 106 [true; false; false; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 3 1 106 [false; false; false; false; false; true; true; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpRun 196;
  OpRun 188;
  OpRun 195;
  OpRun 328;
  OpRun 269;
  OpRun 354;
  OpRun 262;
  OpRun 231;
  OpRun 150;
  OpRun 137;
  OpRun 604;
  OpRun 641;
  OpRun 285;
  OpRun 286;
  OpRun 288;
  OpRun 491;
  OpJump 3 1 185 [true; false; true; false; false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 1 185 [false; true; false; true; true; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 1 185 [true; true; false; true; true; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 185 [false; true; true; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 185 [true; true; true; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [true; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 185 [true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [false; true; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [true; true; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 185 [false; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [false; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 185 [false; false; true; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 271;
  OpRun 259;
  OpRun 260;
  OpRun 456;
  OpRun 258;
  OpRun 257;
  OpRun 266;
  OpRun 478;
  OpRun 275;
  OpRun 274;
  OpRun 276;
  OpRun 498;
  OpJump 3 1 204 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 185 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 185 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [true; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 185 [false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 185 [true; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [true; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [false; false; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [true; false; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [false; true; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 185 [false; false; true; true; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 185 [true; false; true; true; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 185 [false; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [false; false; true; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [true; false; true; true; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 185 [false; false; false; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 185 [true; false; false; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 185 [false; true; true; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 1 185 [false; false; true; true; true; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 1 185 [true; false; true; true; true; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 1 185 [false; true; false; false; true; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 303;
  OpRun 302;
  OpRun 526;
  OpRun 507;
  OpRun 346;
  OpRun 339;
  OpRun 186;
  OpRun 575;
  OpRun 321;
  OpRun 204;
  OpRun 615;
  OpRun 562;
  OpRun 254;
  OpRun 526;
  OpRun 292;
  OpRun 290;
  OpRun 280;
  OpRun 278;
  OpJump 2 1 107 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 107 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 107 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 107 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 107 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 107 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 107 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 107 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 107 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 6 107 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 6 107 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 7 107 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 7 107 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 7 107 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 6 107 [false; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 107 [false; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 107 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 107 [false; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 107 [false; false; true; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 177;
  OpRun 158;
  OpRun 159;
  OpRun 270;
  OpRun 157;
  OpRun 156;
  OpRun 165;
  OpRun 292;
  OpRun 174;
  OpRun 173;
  OpRun 175;
  OpRun 312;
  OpJump 2 1 126 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 107 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 107 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 107 [false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 107 [true; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 107 [false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 107 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ]
].

Definition ops_chunk_6 : list Op := [
  OpJump 2 5 107 [false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 107 [true; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 6 107 [false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 6 107 [true; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 6 107 [false; false; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 6 107 [true; false; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 107 [false; false; false; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 107 [true; false; false; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 107 [false; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 107 [false; false; true; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 107 [true; false; true; true; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 107 [false; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 107 [false; false; true; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 107 [true; false; true; true; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 107 [false; false; false; true; false; false; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 107 [true; false; false; true; false; false; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 107 [false; true; true; true; false; false; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 107 [false; false; true; true; true; true; false; false; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 107 [true; false; true; true; true; true; false; false; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 107 [false; true; false; false; true; true; false; false; false; false; true; true; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 209;
  OpRun 201;
  OpRun 321;
  OpRun 1168;
  OpRun 150;
  OpRun 137;
  OpRun 773;
  OpRun 529;
  OpRun 412;
  OpRun 408;
  OpRun 591;
  OpRun 888;
  OpJump 2 1 367 [false; true; true; false; true; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 367 [true; true; true; false; true; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 2 367 [true; false; true; true; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 2 367 [false; true; false; false; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 2 367 [true; true; false; false; false; false; false; false; true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 6 367 [true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 7 367 [true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 5 367 [false; false; false; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 4 367 [false; false; true; false; false; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 4 367 [true; false; true; false; false; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 3 367 [false; false; false; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 2 367 [false; false; true; false; false; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 367 [false; false; true; false; true; false; false; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpRun 459;
  OpRun 459;
  OpRun 468;
  OpRun 896;
  OpRun 395;
  OpRun 323;
  OpRun 325;
  OpRun 619;
  OpRun 329;
  OpRun 335;
  OpRun 727;
  OpRun 848;
  OpRun 605;
  OpRun 383;
  OpRun 378;
  OpRun 1337;
  OpJump 2 1 627 [true; false; false; true; false; true; true; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 1 627 [false; true; true; true; false; true; true; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 1 627 [true; true; true; true; false; true; true; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 2 627 [true; true; false; true; true; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 3 627 [false; true; true; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 3 627 [true; true; true; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 4 627 [true; true; false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 5 627 [false; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 5 627 [true; true; true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 6 627 [true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 6 627 [false; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 6 627 [true; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 6 627 [false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 5 627 [false; false; true; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 5 627 [true; false; true; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 5 627 [false; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 3 627 [false; false; false; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 3 627 [true; false; false; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 3 627 [false; true; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 2 627 [false; false; true; true; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 2 627 [true; false; true; true; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 2 627 [false; true; false; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 2 1 627 [false; false; true; true; false; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpRun 726;
  OpRun 710;
  OpRun 409;
  OpRun 1122;
  OpJump 2 1 331 [false; true; false; false; false; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 4; SlZ];
  OpJump 2 1 331 [true; true; false; false; false; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 4; SlZ];
  OpRun 417;
  OpRun 415;
  OpRun 419;
  OpRun 683;
  OpRun 208;
  OpRun 207;
  OpRun 214;
  OpRun 398;
  OpJump 2 1 121 [false; true; true; false; false; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [true; true; true; false; false; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [true; false; false; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [false; true; true; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [true; true; true; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 121 [true; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 121 [false; true; false; true; false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 3 121 [true; true; false; true; false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 121 [false; true; false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 121 [true; true; false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 6 121 [false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 6 121 [true; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 7 121 [false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 7 121 [true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 121 [false; false; false; false; false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 5 121 [true; false; false; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 121 [false; false; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 4 121 [true; false; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [false; false; false; false; false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 2 121 [true; false; false; false; false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [false; false; false; true; true; false; false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 2 1 121 [true; false; false; true; true; false; false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 210;
  OpRun 209;
  OpRun 196;
  OpRun 362;
  OpRun 214;
  OpRun 203;
  OpRun 351;
  OpRun 475;
  OpRun 642;
  OpRun 167;
  OpRun 256;
  OpRun 394;
  OpRun 161;
  OpRun 168;
  OpRun 177;
  OpRun 300;
  OpRun 186;
  OpRun 185;
  OpRun 187;
  OpRun 324;
  OpRun 191;
  OpRun 197;
  OpRun 315;
  OpRun 494;
  OpRun 637;
  OpRun 407;
  OpRun 139;
  OpRun 226;
  OpRun 135;
  OpRun 123;
  OpRun 715;
  OpRun 193;
  OpRun 1383;
  OpRun 398;
  OpRun 378;
  OpRun 763;
  OpJump 3 1 335 [true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 3 1 335 [false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpRun 423;
  OpRun 422;
  OpRun 426;
  OpRun 1106;
  OpRun 406;
  OpRun 246;
  OpRun 542;
  OpRun 606;
  OpRun 440;
  OpRun 258;
  OpRun 267;
  OpRun 464;
  OpRun 276;
  OpRun 275;
  OpRun 277;
  OpRun 488;
  OpJump 4 1 196 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 196 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 196 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 196 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 196 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 196 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 196 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 196 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 196 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 196 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 196 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 196 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 196 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 196 [false; false; false; false; false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 196 [true; false; false; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 196 [false; false; false; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 196 [false; false; true; false; false; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 196 [false; false; true; false; true; false; false; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 299;
  OpRun 237;
  OpRun 246;
  OpRun 457;
  OpJump 4 1 123 [false; true; false; true; false; true; true; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 1 123 [true; true; false; true; false; true; true; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 239;
  OpRun 231
].

Definition ops_chunk_7 : list Op := [
  OpRun 228;
  OpRun 386;
  OpJump 4 1 164 [true; false; false; true; false; true; true; true; true; false; false; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 283;
  OpRun 275;
  OpRun 262;
  OpRun 459;
  OpRun 262;
  OpRun 451;
  OpRun 824;
  OpRun 830;
  OpRun 454;
  OpRun 453;
  OpRun 455;
  OpRun 840;
  OpRun 307;
  OpRun 295;
  OpRun 294;
  OpRun 903;
  OpJump 4 1 139 [false; true; false; false; false; true; true; true; true; false; false; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 139 [true; true; false; false; false; true; true; true; true; false; false; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [false; true; true; true; true; false; false; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [true; true; true; true; true; false; false; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 139 [true; true; true; false; false; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [true; false; false; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [false; true; true; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [true; true; true; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 139 [true; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 139 [false; true; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 139 [true; true; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 139 [false; false; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [false; false; true; false; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 139 [false; false; true; false; true; false; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [false; false; true; false; true; false; true; false; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 139 [false; false; true; false; true; false; true; false; true; false; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 241;
  OpRun 229;
  OpRun 230;
  OpRun 380;
  OpRun 228;
  OpRun 227;
  OpRun 236;
  OpRun 402;
  OpRun 245;
  OpRun 244;
  OpRun 246;
  OpRun 421;
  OpJump 4 1 157 [true; true] [SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 139 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 139 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [false; true; false; true; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [true; true; false; true; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 139 [false; true; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 139 [true; true; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [true; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 139 [false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 139 [true; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 139 [false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 139 [true; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 139 [false; false; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 139 [false; false; true; false; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [false; false; true; false; true; false; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [true; false; true; false; true; false; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [false; true; false; true; false; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [false; false; false; false; true; true; false; true; false; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [true; false; false; false; true; true; false; true; false; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [false; true; true; false; true; true; false; true; false; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 139 [false; false; true; true; true; false; true; true; false; true; false; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 139 [true; false; true; true; true; false; true; true; false; true; false; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 139 [false; false; false; true; false; false; true; false; true; true; false; true; false; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 139 [true; false; false; true; false; false; true; false; true; true; false; true; false; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 139 [false; true; true; true; false; false; true; false; true; true; false; true; false; true; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 265;
  OpRun 262;
  OpRun 446;
  OpRun 451;
  OpRun 253;
  OpRun 381;
  OpRun 248;
  OpRun 428;
  OpJump 4 1 121 [true; false; true; true; false; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 121 [false; true; false; false; false; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 121 [true; true; false; false; false; false; true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [false; true; false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [true; true; false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [true; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 121 [false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 121 [true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [false; false; false; false; false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [true; false; false; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [false; false; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [true; false; false; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 121 [false; false; false; false; false; false; false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 121 [true; false; false; false; false; false; false; true; true; true; true; false; false; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 242;
  OpRun 241;
  OpRun 228;
  OpRun 400;
  OpRun 236;
  OpRun 181;
  OpRun 510;
  OpRun 679;
  OpRun 394;
  OpRun 438;
  OpRun 96;
  OpRun 696;
  OpRun 292;
  OpJump 3 1 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 7 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 7 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 8 106 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 8 106 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 8 106 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 7 106 [false; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 106 [false; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 106 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 106 [false; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 106 [false; false; true; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 192;
  OpRun 173;
  OpRun 177;
  OpRun 302;
  OpJump 3 1 110 [true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 110 [false; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 110 [true; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 110 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 179;
  OpRun 171;
  OpRun 180;
  OpRun 306;
  OpRun 189;
  OpRun 188;
  OpRun 190;
  OpRun 328;
  OpJump 3 1 125 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 125 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 125 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 106 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 106 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 106 [false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 106 [true; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 106 [false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 106 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 106 [false; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 106 [false; false; false; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 106 [true; false; false; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 106 [false; false; false; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 106 [true; false; false; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 106 [false; false; false; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 106 [true; false; false; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 225;
  OpRun 217;
  OpRun 204;
  OpRun 359;
  OpRun 214;
  OpRun 201;
  OpRun 584;
  OpRun 394;
  OpRun 154;
  OpRun 400;
  OpRun 258;
  OpRun 594;
  OpJump 3 1 185 [true; false; true; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 1 185 [false; true; false; false; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 1 185 [true; true; false; false; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [false; false; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [true; false; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [false; true; false; true; false; true; true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 185 [true; true; false; true; false; true; true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 185 [false; true; false; true; true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 185 [true; true; false; true; true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [false; true; true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [true; true; true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 7 185 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 7 185 [true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 8 185 [false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 8 185 [true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 8 185 [false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 7 185 [false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [false; false; true; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [true; false; true; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 6 185 [false; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 185 [false; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 287;
  OpRun 285
].

Definition ops_chunk_8 : list Op := [
  OpRun 292;
  OpRun 527;
  OpRun 197;
  OpRun 345;
  OpRun 393;
  OpRun 636;
  OpRun 308;
  OpRun 369;
  OpRun 284;
  OpRun 1254;
  OpRun 334;
  OpRun 378;
  OpRun 80;
  OpRun 508;
  OpRun 209;
  OpRun 216;
  OpRun 225;
  OpRun 380;
  OpRun 234;
  OpRun 233;
  OpRun 235;
  OpRun 404;
  OpJump 4 1 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 9 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 161 [false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 161 [false; false; true; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 161 [false; false; true; false; true; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 161 [true; false; true; false; true; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 161 [false; true; false; true; false; true; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 161 [false; false; false; false; true; true; false; true; false; true; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 161 [true; false; false; false; true; true; false; true; false; true; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 161 [false; true; true; false; true; true; false; true; false; true; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 161 [false; false; true; true; true; false; true; true; false; true; false; true; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 161 [true; false; true; true; true; false; true; true; false; true; false; true; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 161 [false; true; false; false; true; false; true; true; false; true; false; true; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 161 [false; false; true; true; false; false; true; false; true; true; false; true; false; true; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 161 [true; false; true; true; false; false; true; false; true; true; false; true; false; true; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 161 [false; true; false; false; false; false; true; false; true; true; false; true; false; true; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 296;
  OpRun 278;
  OpRun 268;
  OpRun 1029;
  OpRun 712;
  OpRun 710;
  OpRun 542;
  OpRun 1543;
  OpRun 498;
  OpRun 500;
  OpRun 171;
  OpRun 267;
  OpRun 172;
  OpRun 880;
  OpRun 910;
  OpRun 1045;
  OpJump 4 5 525 [true; false; true; true; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 5 525 [false; true; false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 5 525 [true; true; false; false; false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 7 525 [false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 7 525 [true; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 7 525 [false; false; false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 7 525 [true; false; false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 7 525 [false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 5 525 [false; false; false; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 5 525 [true; false; false; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 5 525 [false; true; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 4 525 [false; false; true; true; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 4 525 [true; false; true; true; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 3 525 [false; false; false; true; false; false; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 2 525 [false; false; true; false; false; true; false; false; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 2 525 [true; false; true; false; false; true; false; false; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 1 525 [false; false; false; true; false; true; true; true; false; false; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 1 525 [true; false; false; true; false; true; true; true; false; false; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlP 6; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 6; SlZ; SlZ; SlP 6; SlZ];
  OpRun 666;
  OpRun 663;
  OpRun 433;
  OpRun 801;
  OpRun 500;
  OpRun 381;
  OpRun 827;
  OpRun 962;
  OpJump 4 2 474 [true; true; false; true; true; true; false; false; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 3 474 [false; true; true; true; false; false; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 3 474 [true; true; true; true; false; false; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 4 474 [true; true; false; false; true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 6 474 [true; false; true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 6 474 [false; true; false; false; true; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 6 474 [true; true; false; false; true; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 8 474 [true; true; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 8 474 [false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 7 474 [false; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 7 474 [true; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 4 474 [false; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 4 474 [true; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 4 474 [false; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 3 474 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 1 474 [false; false; false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 1 474 [true; false; false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 4 1 474 [false; true; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 1; SlZ; SlZ; SlN 3; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpRun 622;
  OpRun 626;
  OpRun 1222;
  OpRun 963;
  OpJump 4 1 331 [false; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 4; SlZ];
  OpRun 450;
  OpRun 253;
  OpRun 262;
  OpRun 455;
  OpRun 430;
  OpRun 254;
  OpRun 255;
  OpRun 445;
  OpJump 4 1 121 [true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 121 [false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 121 [true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 121 [false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 121 [true; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 121 [true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 121 [false; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 121 [true; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 121 [true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 121 [false; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 121 [true; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 121 [true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 121 [false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 121 [true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 121 [false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 121 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 121 [false; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 121 [false; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 121 [false; false; true; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 223;
  OpRun 211;
  OpRun 215;
  OpRun 362;
  OpJump 4 1 125 [true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 1 125 [false; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 1 125 [true; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 125 [true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 125 [false; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 125 [true; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 125 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 1 125 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 210;
  OpRun 209;
  OpRun 218;
  OpRun 366;
  OpRun 227;
  OpRun 226;
  OpRun 228;
  OpRun 390;
  OpRun 230;
  OpRun 236;
  OpRun 383;
  OpRun 376;
  OpJump 4 2 140 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 140 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 140 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 140 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 121 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 121 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 121 [false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 121 [true; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 121 [false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 121 [true; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 121 [false; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 121 [false; false; false; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 121 [true; false; false; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 121 [false; false; false; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 121 [true; false; false; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 121 [false; false; false; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 1 121 [false; false; true; false; false; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 1 121 [true; false; true; false; false; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 1 121 [false; true; false; true; true; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 269;
  OpRun 268;
  OpRun 441;
  OpRun 420;
  OpRun 274;
  OpRun 185;
  OpRun 233;
  OpRun 398;
  OpRun 214;
  OpRun 367;
  OpRun 413;
  OpRun 1547;
  OpRun 828
].

Definition ops_chunk_9 : list Op := [
  OpRun 148;
  OpRun 180;
  OpRun 189;
  OpRun 96;
  OpRun 187;
  OpRun 96;
  OpRun 1071;
  OpRun 125;
  OpRun 130;
  OpRun 134;
  OpRun 748;
  OpRun 839;
  OpRun 794;
  OpRun 216;
  OpRun 362;
  OpRun 225;
  OpRun 224;
  OpRun 226;
  OpRun 386;
  OpJump 4 1 138 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 138 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 138 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 138 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 138 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 138 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 138 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 138 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 138 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 138 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 138 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 138 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 138 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 8 138 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 8 138 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 8 138 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 138 [false; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 138 [false; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 138 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 138 [false; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 138 [false; false; true; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 240;
  OpRun 228;
  OpRun 232;
  OpRun 396;
  OpJump 4 1 142 [true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 142 [false; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 142 [true; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 142 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 227;
  OpRun 226;
  OpRun 235;
  OpRun 400;
  OpRun 244;
  OpRun 243;
  OpRun 245;
  OpRun 422;
  OpJump 4 1 157 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 157 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 157 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 138 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 138 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 138 [false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 138 [true; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 138 [false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 138 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 138 [false; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 138 [false; false; false; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 138 [true; false; false; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 138 [false; false; false; false; false; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 138 [true; false; false; false; false; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 138 [false; true; true; false; false; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 288;
  OpRun 276;
  OpRun 469;
  OpRun 414;
  OpRun 217;
  OpRun 216;
  OpRun 221;
  OpRun 375;
  OpJump 4 1 122 [true; false; true; false; false; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 262;
  OpRun 261;
  OpRun 258;
  OpRun 335;
  OpJump 4 1 64 [true; true; false; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 199;
  OpRun 198;
  OpRun 205;
  OpRun 374;
  OpRun 183;
  OpRun 175;
  OpRun 281;
  OpRun 466;
  OpJump 4 1 139 [false; true; true; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 139 [true; true; true; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 139 [true; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [false; false; true; false; true; false; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [true; false; true; false; true; false; false; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [false; true; false; true; false; true; true; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [true; true; false; true; false; true; true; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 139 [false; true; false; true; true; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 139 [true; true; false; true; true; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [false; true; true; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 139 [true; true; true; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 139 [true; true; false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 139 [false; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 139 [true; true; false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 8 139 [false; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 8 139 [true; true; true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 9 139 [true; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 8 139 [false; false; false; false; false; true] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 139 [false; false; true; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 139 [true; false; true; false; false; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 139 [false; false; false; false; false; false; false; true; false; true; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 139 [true; false; false; false; false; false; false; true; false; true; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 139 [false; true; true; false; false; false; false; true; false; true; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 139 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 139 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 139 [true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 281;
  OpRun 272;
  OpRun 276;
  OpRun 471;
  OpRun 391;
  OpRun 256;
  OpRun 263;
  OpRun 458;
  OpJump 4 1 121 [false; true; true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 121 [true; true; true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 121 [true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 121 [false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 121 [true; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [false; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [true; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [false; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [true; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 121 [true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 8 121 [false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 8 121 [true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 8 121 [false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 7 121 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [false; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [false; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [false; false; true; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 223;
  OpRun 211;
  OpRun 215;
  OpRun 362;
  OpJump 4 1 125 [true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 125 [false; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 125 [true; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 125 [true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 125 [false; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 125 [true; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 125 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 125 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 210;
  OpRun 209;
  OpRun 218;
  OpRun 366;
  OpRun 227;
  OpRun 226;
  OpRun 228;
  OpRun 390;
  OpRun 230;
  OpRun 236;
  OpRun 383;
  OpRun 376;
  OpJump 4 2 140 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 140 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 140 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 140 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [true; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [true; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [false; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [false; false; false; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [true; false; false; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 121 [false; false; false; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 121 [true; false; false; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 121 [false; false; false; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 2 121 [true; false; false; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 121 [false; false; false; true; true; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 121 [true; false; false; true; true; true; true; true; true; false; true; false; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 256;
  OpRun 255;
  OpRun 241;
  OpRun 424;
  OpRun 184;
  OpRun 227;
  OpRun 376;
  OpRun 501;
  OpRun 407;
  OpRun 315
].

Definition ops_chunk_10 : list Op := [
  OpRun 443;
  OpRun 901;
  OpRun 295;
  OpRun 177;
  OpRun 183;
  OpRun 289;
  OpRun 282;
  OpJump 3 2 101 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 101 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 101 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 101 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 101 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 101 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 101 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 101 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 101 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 101 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 7 101 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 7 101 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 8 101 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 8 101 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 9 101 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 9 101 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 9 101 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 8 101 [false; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 7 101 [false; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 101 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 101 [false; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 101 [false; false; true; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 187;
  OpRun 175;
  OpRun 179;
  OpRun 306;
  OpJump 3 1 105 [true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 105 [false; true; true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 105 [true; true; true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 105 [true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 105 [false; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 105 [true; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 105 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 105 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 174;
  OpRun 173;
  OpRun 182;
  OpRun 310;
  OpRun 191;
  OpRun 190;
  OpRun 192;
  OpRun 334;
  OpRun 194;
  OpRun 200;
  OpRun 327;
  OpRun 320;
  OpJump 3 2 120 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 120 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 120 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 120 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 101 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 101 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 101 [false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 5 101 [true; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 101 [false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 101 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 7 101 [false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 7 101 [true; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 8 101 [false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 8 101 [true; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 9 101 [false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 8 101 [false; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 7 101 [false; false; true; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 7 101 [true; false; true; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 101 [false; false; false; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 101 [true; false; false; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 6 101 [false; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 4 101 [false; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 3 101 [false; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 101 [false; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 2 101 [true; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 3 1 101 [false; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 233;
  OpRun 231;
  OpRun 226;
  OpRun 471;
  OpRun 504;
  OpRun 183;
  OpRun 304;
  OpRun 431;
  OpRun 186;
  OpRun 185;
  OpRun 295;
  OpRun 403;
  OpJump 3 2 153 [true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 153 [false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 153 [true; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 153 [false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 153 [true; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 153 [true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 153 [false; true; false; false; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 153 [true; true; false; false; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 7 153 [true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 8 153 [false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 8 153 [true; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 10 153 [true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 9 153 [false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 8 153 [false; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 8 153 [true; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 153 [false; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 153 [true; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 5 153 [false; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 4 153 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 3 153 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 153 [false; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 153 [true; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 2 153 [false; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 1 153 [false; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 3 1 153 [true; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 293;
  OpRun 284;
  OpRun 277;
  OpRun 492;
  OpRun 208;
  OpRun 260;
  OpRun 503;
  OpRun 556;
  OpRun 282;
  OpRun 460;
  OpRun 200;
  OpRun 447;
  OpRun 451;
  OpRun 351;
  OpRun 217;
  OpRun 377;
  OpRun 80;
  OpRun 575;
  OpRun 232;
  OpRun 239;
  OpRun 248;
  OpRun 426;
  OpRun 257;
  OpRun 256;
  OpRun 258;
  OpRun 450;
  OpJump 4 1 184 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 184 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 184 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 184 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 184 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 184 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 184 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 184 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 184 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 184 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 184 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 184 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 184 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 184 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 184 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 9 184 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 9 184 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 10 184 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 10 184 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 9 184 [false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 184 [false; false; true; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 184 [true; false; true; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 184 [false; false; false; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 184 [true; false; false; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 184 [false; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 184 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 184 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 184 [false; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 184 [true; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 1 184 [false; false; false; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 1 184 [true; false; false; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 332;
  OpRun 317;
  OpRun 304;
  OpRun 545;
  OpRun 315;
  OpRun 302;
  OpRun 741;
  OpRun 520;
  OpRun 297;
  OpRun 284;
  OpRun 807;
  OpRun 466;
  OpRun 963;
  OpRun 251;
  OpRun 836;
  OpRun 1011;
  OpRun 729;
  OpRun 184;
  OpRun 186;
  OpRun 834;
  OpRun 171;
  OpRun 706;
  OpRun 754;
  OpRun 794;
  OpJump 4 3 303 [false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 3 303 [true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 4 303 [false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ]
].

Definition ops_chunk_11 : list Op := [
  OpJump 4 4 303 [true; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 6 303 [true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 6 303 [false; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 6 303 [true; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 7 303 [true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 7 303 [false; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 7 303 [true; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 8 303 [true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 9 303 [false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 9 303 [true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 8 303 [false; false; false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 8 303 [true; false; false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 6 303 [false; false; false; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 6 303 [true; false; false; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 6 303 [false; true; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 5 303 [false; false; true; true; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 5 303 [true; false; true; true; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 4 303 [false; false; false; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 4 303 [true; false; false; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 4 303 [false; true; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 3 303 [false; false; true; true; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 2 303 [false; false; true; false; true; true; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 2 303 [true; false; true; false; true; true; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 2 303 [false; true; false; true; false; false; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 1 303 [false; false; true; true; false; true; false; false; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 4 1 303 [true; false; true; true; false; true; false; false; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 4; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpRun 478;
  OpRun 466;
  OpRun 455;
  OpRun 729;
  OpRun 351;
  OpRun 350;
  OpRun 601;
  OpRun 851;
  OpJump 4 1 365 [false; false; false; false; false; true; false; false; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlN 2; SlZ; SlZ; SlN 2; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 4; SlZ];
  OpRun 528;
  OpRun 516;
  OpRun 522;
  OpRun 1114;
  OpJump 4 1 627 [false; true; true; false; false; true; false; false; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 1 627 [true; true; true; false; false; true; false; false; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 2 627 [true; false; false; true; false; false; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 2 627 [false; true; true; true; false; false; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 2 627 [true; true; true; true; false; false; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 3 627 [true; true; false; false; true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 5 627 [true; true; false; false; true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 7 627 [true; false; false; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 7 627 [false; true; true; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 7 627 [true; true; true; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 8 627 [true; true; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 8 627 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 7 627 [false; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 6 627 [false; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 5 627 [false; false; true; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpRun 729;
  OpRun 717;
  OpRun 721;
  OpRun 1374;
  OpJump 4 1 631 [true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 1 631 [false; true; true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 1 631 [true; true; true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 2 631 [true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 2 631 [false; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 2 631 [true; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 3 631 [true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 3 631 [false; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 3 631 [true; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 3 631 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 2 631 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 1 631 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpRun 716;
  OpRun 715;
  OpRun 724;
  OpRun 1378;
  OpRun 733;
  OpRun 732;
  OpRun 734;
  OpRun 1402;
  OpRun 738;
  OpRun 742;
  OpRun 1395;
  OpRun 1388;
  OpJump 4 2 646 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 2 646 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 3 646 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 3 646 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 4 646 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 4 646 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 5 627 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 5 627 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 6 627 [false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 6 627 [true; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 7 627 [false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 7 627 [true; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 8 627 [false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 8 627 [true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 9 627 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 8 627 [false; false; true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 8 627 [true; false; true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 7 627 [false; false; false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 6 627 [false; false; true; false; false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 6 627 [true; false; true; false; false; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 5 627 [false; false; false; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 5 627 [true; false; false; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 4 627 [false; false; false; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 3 627 [false; false; true; false; false; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 3 627 [true; false; true; false; false; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 1 627 [false; false; false; false; false; true; false; true; true; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 1 627 [true; false; false; false; false; true; false; true; true; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 4 1 627 [false; true; true; false; false; true; false; true; true; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpRun 781;
  OpRun 780;
  OpRun 1479;
  OpRun 1105;
  OpJump 4 2 121 [true; false; false; true; false; true; true; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 121 [false; true; true; true; false; true; true; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 121 [true; true; true; true; false; true; true; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 121 [true; true; false; true; true; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 121 [false; true; true; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 121 [true; true; true; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 121 [true; true; true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 6 121 [true; true; false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 121 [false; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 121 [true; true; true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 121 [true; true; false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 10 121 [false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 9 121 [false; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 121 [false; false; true; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 8 121 [true; false; true; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 121 [false; false; false; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 121 [true; false; false; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 7 121 [false; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 5 121 [false; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 4 121 [false; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 121 [false; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 3 121 [true; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 2 121 [false; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 1 121 [false; false; true; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 4 1 121 [true; false; true; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpRun 290;
  OpRun 289;
  OpRun 284;
  OpRun 503;
  OpRun 295;
  OpRun 283;
  OpRun 602;
  OpRun 434;
  OpRun 238;
  OpRun 274;
  OpRun 304;
  OpRun 195;
  OpRun 127;
  OpRun 135;
  OpRun 142;
  OpRun 188;
  OpJump 4 1 32 [false; true; true; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 1 32 [true; true; true; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 2 32 [true; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 3 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 4 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 4 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 5 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 5 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 6 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 6 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 7 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 7 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 8 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 8 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 9 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 9 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 10 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 10 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 10 32 [false; false; false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 9 32 [false; false; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 8 32 [false; false; true; false; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 7 32 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 6 32 [false; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 5 32 [false; false; true; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 134;
  OpRun 122;
  OpRun 126;
  OpRun 184;
  OpJump 4 1 36 [true; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 1 36 [false; true; true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 1 36 [true; true; true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 2 36 [true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 2 36 [false; true; true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 2 36 [true; true; true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 3 36 [true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 3 36 [false; true; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 3 36 [true; true; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 3 36 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 2 36 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 1 36 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 121;
  OpRun 120;
  OpRun 129;
  OpRun 188;
  OpRun 138
].

Definition ops_chunk_12 : list Op := [
  OpRun 137;
  OpRun 139;
  OpRun 212;
  OpRun 143;
  OpRun 147;
  OpRun 205;
  OpRun 198;
  OpJump 4 2 51 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 2 51 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 3 51 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 3 51 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 4 51 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 4 51 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 5 32 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 5 32 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 6 32 [false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 6 32 [true; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 7 32 [false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 7 32 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 8 32 [false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 8 32 [true; true; false; true; false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 9 32 [false; true; false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 9 32 [true; true; false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 10 32 [false; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 9 32 [false; false; true; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 8 32 [false; false; true; false; true; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 8 32 [true; false; true; false; true; true; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 7 32 [false; false; false; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 7 32 [true; false; false; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 7 32 [false; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 5 32 [false; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 4 32 [false; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 3 32 [false; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 3 32 [true; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 3 32 [false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 2 32 [false; false; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 2 32 [true; false; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 2 32 [false; true; false; false; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 1 32 [false; false; true; true; false; false; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 4 1 32 [true; false; true; true; false; false; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 203;
  OpRun 202;
  OpRun 192;
  OpRun 317;
  OpRun 194;
  OpRun 292;
  OpRun 487;
  OpRun 478;
  OpJump 4 4 121 [false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [true; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [true; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [false; true; false; false; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [true; true; false; false; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 8 121 [true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 9 121 [false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 9 121 [true; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 11 121 [true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 10 121 [false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 9 121 [false; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 9 121 [true; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [false; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [true; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 6 121 [false; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 5 121 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 4 121 [true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 3 121 [false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 121 [false; false; false; false; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 121 [true; false; false; false; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 4 1 121 [false; true; true; false; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 278;
  OpRun 273;
  OpRun 440;
  OpRun 353;
  OpRun 270;
  OpRun 261;
  OpRun 190;
  OpRun 517;
  OpRun 275;
  OpRun 207;
  OpRun 314;
  OpRun 744;
  OpRun 498;
  OpRun 654;
  OpRun 226;
  OpRun 355;
  OpRun 223;
  OpRun 222;
  OpRun 231;
  OpRun 376;
  OpRun 240;
  OpRun 239;
  OpRun 241;
  OpRun 400;
  OpJump 5 1 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 137 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 137 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 137 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 137 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 137 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 7 137 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 7 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 8 137 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 8 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 9 137 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 9 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 137 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 11 137 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 11 137 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 137 [false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 9 137 [false; false; true; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 9 137 [true; false; true; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 137 [false; false; false; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 137 [true; false; false; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 137 [false; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 137 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 137 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 137 [false; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 137 [true; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 137 [false; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 137 [false; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 137 [true; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 137 [false; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 312;
  OpRun 303;
  OpRun 305;
  OpRun 510;
  OpRun 381;
  OpRun 288;
  OpRun 292;
  OpRun 615;
  OpRun 480;
  OpRun 252;
  OpRun 244;
  OpRun 710;
  OpRun 515;
  OpRun 462;
  OpRun 464;
  OpRun 551;
  OpRun 320;
  OpRun 258;
  OpRun 259;
  OpRun 548;
  OpJump 5 1 153 [true; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 1 153 [false; true; true; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 1 153 [true; true; true; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 2 153 [true; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 2 153 [false; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 2 153 [true; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 153 [true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 153 [false; true; true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 153 [true; true; true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 4 153 [true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 5 153 [false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 5 153 [true; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 7 153 [true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 7 153 [false; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 7 153 [true; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 8 153 [true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 8 153 [false; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 8 153 [true; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 9 153 [true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 10 153 [false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 10 153 [true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 10 153 [false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 9 153 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 8 153 [false; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 7 153 [false; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 6 153 [false; false; true; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 271;
  OpRun 259;
  OpRun 263;
  OpRun 442;
  OpJump 5 1 157 [true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 1 157 [false; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 1 157 [true; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 2 157 [true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 2 157 [false; true; true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 2 157 [true; true; true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 157 [true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 157 [false; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 157 [true; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 4 157 [true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 4 157 [false; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 4 157 [true; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 4 157 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 157 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 2 157 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 1 157 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 258;
  OpRun 257;
  OpRun 266
].

Definition ops_chunk_13 : list Op := [
  OpRun 446;
  OpRun 275;
  OpRun 274;
  OpRun 276;
  OpRun 470;
  OpRun 280;
  OpRun 286;
  OpRun 461;
  OpRun 456;
  OpJump 5 2 172 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 2 172 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 172 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 172 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 4 172 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 4 172 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 5 172 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 5 172 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 6 153 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 6 153 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 7 153 [false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 7 153 [true; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 8 153 [false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 8 153 [true; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 9 153 [false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 9 153 [true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 10 153 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 10 153 [true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 11 153 [false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 10 153 [false; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 9 153 [false; false; true; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 9 153 [true; false; true; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 8 153 [false; false; false; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 8 153 [true; false; false; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 8 153 [false; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 6 153 [false; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 5 153 [false; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 4 153 [false; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 4 153 [true; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 153 [false; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 3 153 [true; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 2 153 [false; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 2 153 [true; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 5 1 153 [false; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 332;
  OpRun 335;
  OpRun 346;
  OpRun 1259;
  OpRun 618;
  OpRun 462;
  OpRun 717;
  OpRun 494;
  OpRun 299;
  OpRun 304;
  OpRun 158;
  OpRun 227;
  OpRun 112;
  OpRun 334;
  OpRun 173;
  OpRun 180;
  OpRun 189;
  OpRun 276;
  OpRun 198;
  OpRun 197;
  OpRun 199;
  OpRun 300;
  OpJump 6 1 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 93 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 93 [false; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 93 [false; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 93 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 93 [false; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 93 [false; false; true; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpRun 227;
  OpRun 201;
  OpRun 205;
  OpRun 310;
  OpJump 6 1 97 [true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 1 97 [false; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 1 97 [true; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 97 [true; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 97 [false; true; true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 97 [true; true; true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 97 [true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 97 [false; true; true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 97 [true; true; true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 97 [true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 97 [false; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 97 [true; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 97 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 97 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 97 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 1 97 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpRun 214;
  OpRun 199;
  OpRun 208;
  OpRun 314;
  OpRun 217;
  OpRun 216;
  OpRun 218;
  OpRun 338;
  OpRun 222;
  OpRun 228;
  OpRun 329;
  OpRun 324;
  OpJump 6 2 112 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 112 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 112 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 112 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 112 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 112 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 112 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 112 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 93 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 93 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 93 [false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 93 [true; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 93 [false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 93 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 93 [false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 93 [true; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 93 [false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 93 [true; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 93 [false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 93 [false; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 93 [false; false; true; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 93 [true; false; true; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 93 [false; false; false; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 93 [true; false; false; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 93 [false; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 93 [false; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 93 [false; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 93 [false; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 93 [true; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 93 [false; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 93 [true; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 93 [false; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 1 93 [false; false; true; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ];
  OpRun 297;
  OpRun 272;
  OpRun 273;
  OpRun 631;
  OpRun 265;
  OpRun 271;
  OpRun 268;
  OpRun 439;
  OpRun 278;
  OpRun 272;
  OpRun 506;
  OpRun 383;
  OpRun 341;
  OpRun 225;
  OpRun 328;
  OpRun 556;
  OpJump 6 1 121 [true; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 1 121 [false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 1 121 [true; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 121 [true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 121 [true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 121 [true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 121 [false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 121 [true; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 121 [false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 121 [true; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 121 [true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 121 [false; true; false; false; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 121 [true; true; false; false; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 9 121 [true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [true; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 12 121 [true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 11 121 [false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [false; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [true; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 121 [false; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 121 [true; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 121 [false; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 121 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 121 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 121 [false; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 121 [true; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ]
].

Definition ops_chunk_14 : list Op := [
  OpJump 6 4 121 [false; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 121 [false; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 121 [true; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 121 [false; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 121 [false; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 1 121 [false; false; true; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 1 121 [true; false; true; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 1 121 [false; true; false; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 322;
  OpRun 303;
  OpRun 479;
  OpRun 473;
  OpRun 286;
  OpRun 228;
  OpRun 269;
  OpRun 502;
  OpRun 223;
  OpRun 433;
  OpRun 237;
  OpRun 484;
  OpRun 353;
  OpRun 269;
  OpRun 499;
  OpRun 852;
  OpRun 771;
  OpRun 280;
  OpRun 442;
  OpRun 289;
  OpRun 288;
  OpRun 290;
  OpRun 466;
  OpJump 7 1 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 2 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 2 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 3 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 3 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 4 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 4 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 5 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 5 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 6 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 6 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 7 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 7 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 8 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 8 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 9 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 9 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 10 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 10 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 11 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 11 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 12 161 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 12 161 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 11 161 [false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 10 161 [false; false; true; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 10 161 [true; false; true; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 7 161 [false; false; false; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 7 161 [true; false; false; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 7 161 [false; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 6 161 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 5 161 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 4 161 [false; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 4 161 [true; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 4 161 [false; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 3 161 [false; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 3 161 [true; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 3 161 [false; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 2 161 [false; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 2 161 [true; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 2 161 [false; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 368;
  OpRun 352;
  OpRun 352;
  OpRun 652;
  OpRun 338;
  OpRun 337;
  OpRun 341;
  OpRun 905;
  OpRun 302;
  OpRun 289;
  OpRun 622;
  OpRun 710;
  OpRun 518;
  OpRun 237;
  OpRun 673;
  OpRun 493;
  OpRun 333;
  OpRun 334;
  OpRun 338;
  OpRun 560;
  OpJump 7 1 153 [true; false; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 1 153 [false; true; true; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 1 153 [true; true; true; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 2 153 [true; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 2 153 [false; true; true; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 2 153 [true; true; true; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 153 [true; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 153 [false; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 153 [true; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 153 [true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 153 [false; true; true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 153 [true; true; true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 5 153 [true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 6 153 [false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 6 153 [true; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 8 153 [true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 8 153 [false; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 8 153 [true; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 9 153 [true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 9 153 [false; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 9 153 [true; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 10 153 [true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 11 153 [false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 11 153 [true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 11 153 [false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 10 153 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 9 153 [false; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 8 153 [false; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 7 153 [false; false; true; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 303;
  OpRun 291;
  OpRun 295;
  OpRun 474;
  OpJump 7 1 157 [true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 1 157 [false; true; true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 1 157 [true; true; true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 2 157 [true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 2 157 [false; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 2 157 [true; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 157 [true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 157 [false; true; true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 157 [true; true; true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 157 [true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 157 [false; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 157 [true; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 5 157 [true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 5 157 [false; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 5 157 [true; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 5 157 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 157 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 157 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 2 157 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 1 157 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 290;
  OpRun 289;
  OpRun 298;
  OpRun 478;
  OpRun 307;
  OpRun 306;
  OpRun 308;
  OpRun 502;
  OpRun 312;
  OpRun 318;
  OpRun 493;
  OpRun 488;
  OpJump 7 2 172 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 2 172 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 172 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 172 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 172 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 172 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 5 172 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 5 172 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 6 172 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 6 172 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 7 153 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 7 153 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 8 153 [false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 8 153 [true; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 9 153 [false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 9 153 [true; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 10 153 [false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 10 153 [true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 11 153 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 11 153 [true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 12 153 [false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 11 153 [false; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 10 153 [false; false; true; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 10 153 [true; false; true; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 9 153 [false; false; false; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 9 153 [true; false; false; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 9 153 [false; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 7 153 [false; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 6 153 [false; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 5 153 [false; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 5 153 [true; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 153 [false; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 4 153 [true; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 153 [false; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 3 153 [true; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 2 153 [false; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 1 153 [false; false; true; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 1 153 [true; false; true; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpJump 7 1 153 [false; true; false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 376;
  OpRun 378;
  OpRun 627;
  OpRun 620;
  OpRun 372
].

Definition ops_chunk_15 : list Op := [
  OpRun 360;
  OpRun 703;
  OpRun 1035;
  OpRun 761;
  OpRun 598;
  OpRun 266;
  OpRun 548;
  OpRun 283;
  OpRun 216;
  OpRun 144;
  OpRun 467;
  OpRun 238;
  OpRun 172;
  OpRun 178;
  OpRun 231;
  OpRun 224;
  OpJump 6 2 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 12 48 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 12 48 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 12 48 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 48 [false; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 48 [false; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 48 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 48 [false; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 48 [false; false; true; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 182;
  OpRun 170;
  OpRun 174;
  OpRun 248;
  OpJump 6 1 52 [true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 1 52 [false; true; true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 1 52 [true; true; true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 52 [true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 52 [false; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 52 [true; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 52 [true; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 52 [false; true; true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 52 [true; true; true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 52 [true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 52 [false; true; true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 52 [true; true; true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 52 [true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 52 [false; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 52 [true; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 52 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 52 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 52 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 52 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 1 52 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 169;
  OpRun 168;
  OpRun 177;
  OpRun 252;
  OpRun 186;
  OpRun 185;
  OpRun 187;
  OpRun 276;
  OpRun 191;
  OpRun 197;
  OpRun 267;
  OpRun 262;
  OpJump 6 2 67 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 67 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 67 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 67 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 67 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 67 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 67 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 67 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 67 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 67 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 48 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 48 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 48 [false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 48 [true; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 48 [false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 48 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 48 [false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 48 [true; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 48 [false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 48 [true; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 12 48 [false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 48 [false; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 48 [false; false; true; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 10 48 [true; false; true; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 48 [false; false; false; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 48 [true; false; false; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 48 [false; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 48 [false; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 48 [false; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 48 [false; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 48 [true; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 48 [false; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 48 [true; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 48 [false; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 48 [true; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 48 [false; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 1 48 [false; false; true; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 252;
  OpRun 244;
  OpRun 252;
  OpRun 872;
  OpJump 6 1 32 [false; true; false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 239;
  OpRun 241;
  OpRun 357;
  OpRun 840;
  OpJump 6 2 271 [false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 2 271 [true; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 3 271 [true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 4 271 [true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 5 271 [true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 6 271 [false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 6 271 [true; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 7 271 [false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 7 271 [true; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 8 271 [true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 8 271 [false; true; false; false; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 8 271 [true; true; false; false; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 10 271 [true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 11 271 [false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 11 271 [true; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 11 271 [false; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 11 271 [true; false; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 11 271 [false; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 10 271 [false; false; true; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 10 271 [true; false; true; true; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 10 271 [false; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 8 271 [false; false; false; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 8 271 [true; false; false; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 6 271 [false; false; false; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 5 271 [false; false; true; false; false; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 5 271 [true; false; true; false; false; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 4 271 [false; false; false; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 4 271 [true; false; false; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 4 271 [false; true; true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 3 271 [false; false; true; true; true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 3 271 [true; false; true; true; true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 3 271 [false; true; false; false; true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 2 271 [false; false; true; true; false; false; true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 2 271 [true; false; true; true; false; false; true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 6 2 271 [false; true; false; false; false; false; true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpRun 489;
  OpRun 476;
  OpRun 846;
  OpRun 1592;
  OpJump 6 1 627 [true; false; true; true; false; false; false; false; true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 1 627 [false; true; false; false; false; false; false; false; true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 1 627 [true; true; false; false; false; false; false; false; true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 5 627 [true; true; false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 6 627 [false; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 6 627 [true; true; true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 7 627 [true; false; false; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 7 627 [false; true; true; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 7 627 [true; true; true; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 8 627 [true; true; true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 9 627 [true; false; true; true; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 9 627 [false; true; false; false; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 9 627 [true; true; false; false; false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 11 627 [false; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 11 627 [true; false; true; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 11 627 [false; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 11 627 [true; true; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 11 627 [false; false; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 10 627 [false; false; true; false; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 10 627 [true; false; true; false; false; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 10 627 [false; true; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 9 627 [false; false; true; true; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 8 627 [false; false; true; false; true; true; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 8 627 [true; false; true; false; true; true; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 8 627 [false; true; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 7 627 [false; false; true; true; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 7 627 [true; false; true; true; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 7 627 [false; true; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 6 627 [false; false; true; true; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 5 627 [false; false; true; false; true; true; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 5 627 [true; false; true; false; true; true; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 5 627 [false; true; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 4 627 [false; false; true; true; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpJump 6 3 627 [false; false; true; false; true; true; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 8; SlZ];
  OpRun 805
].

Definition ops_chunk_16 : list Op := [
  OpRun 783;
  OpRun 482;
  OpRun 877;
  OpRun 503;
  OpRun 502;
  OpRun 509;
  OpRun 706;
  OpJump 6 1 121 [false; true; true; false; true; false; true; false; true; true; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 1 121 [true; true; true; false; true; false; true; false; true; true; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 121 [true; false; true; false; true; false; true; true; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 121 [false; true; false; true; false; true; false; false; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 121 [true; true; false; true; false; true; false; false; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 121 [false; true; false; true; false; false; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 121 [true; true; false; true; false; false; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 121 [false; true; false; false; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 121 [true; true; false; false; false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 121 [false; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 121 [true; true; false; false; false; false; false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 121 [false; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 9 121 [true; true; false; false; false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 121 [false; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 121 [true; true; true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 12 121 [true; true; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 12 121 [false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 121 [false; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 11 121 [true; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 121 [false; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 121 [true; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 8 121 [false; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 7 121 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 6 121 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 121 [false; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 121 [true; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 5 121 [false; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 121 [false; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 121 [true; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 4 121 [false; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 121 [false; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 121 [true; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 3 121 [false; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 2 121 [false; false; true; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpJump 6 1 121 [false; false; true; false; true; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlZ];
  OpRun 312;
  OpRun 303;
  OpRun 315;
  OpRun 682;
  OpRun 286;
  OpRun 228;
  OpRun 267;
  OpRun 500;
  OpRun 227;
  OpRun 427;
  OpRun 481;
  OpRun 409;
  OpRun 446;
  OpRun 691;
  OpRun 856;
  OpRun 433;
  OpJump 6 1 32 [true; false; false; true; false; true; false; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 1 32 [false; true; true; true; false; true; false; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 1 32 [true; true; true; true; false; true; false; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 2 32 [true; true; false; true; false; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 3 32 [false; true; false; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 3 32 [true; true; false; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 5 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 5 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 6 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 6 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 7 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 7 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 8 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 8 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 9 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 9 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 10 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 10 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 11 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 11 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 12 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 12 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 13 32 [false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 13 32 [true; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 12 32 [false; false; false; false; false; true] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 11 32 [false; false; true; false; false; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 11 32 [true; false; true; false; false; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 8 32 [false; false; false; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 8 32 [true; false; false; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 8 32 [false; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 7 32 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 6 32 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 6 32 [true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 4 32 [false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 3 32 [false; false; true; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 3 32 [true; false; true; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 3 32 [false; true; false; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 2 32 [false; false; true; true; false; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 2 32 [true; false; true; true; false; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 1 32 [false; false; false; true; false; false; false; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 6 1 32 [true; false; false; true; false; false; false; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 239;
  OpRun 231;
  OpRun 216;
  OpRun 418;
  OpJump 6 1 121 [true; true; true; true; false; false; false; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 121 [true; true; false; false; false; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 121 [false; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 121 [true; true; true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 121 [true; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 121 [false; true; true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 121 [true; true; true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 121 [true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 121 [false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 121 [true; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 9 121 [true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 9 121 [false; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 9 121 [true; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [false; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [true; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 11 121 [true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 12 121 [false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 12 121 [true; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 12 121 [false; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 11 121 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [false; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 9 121 [false; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 8 121 [false; false; true; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 255;
  OpRun 243;
  OpRun 247;
  OpRun 394;
  OpJump 6 1 125 [true; false; false; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 1 125 [false; true; true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 1 125 [true; true; true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 125 [true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 125 [false; true; true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 125 [true; true; true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 125 [true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 125 [false; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 125 [true; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 125 [true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 125 [false; true; true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 125 [true; true; true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 125 [true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 125 [false; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 125 [true; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 125 [true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 125 [false; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 125 [true; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 125 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 125 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 125 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 125 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 125 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 1 125 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 242;
  OpRun 241;
  OpRun 250;
  OpRun 398;
  OpRun 259;
  OpRun 258;
  OpRun 260;
  OpRun 422;
  OpRun 264;
  OpRun 270;
  OpRun 415;
  OpRun 406;
  OpJump 6 2 140 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 140 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 140 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 140 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 140 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 4 140 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 140 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 140 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 140 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 140 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 140 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 140 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 8 121 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 8 121 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 9 121 [false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 9 121 [true; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [true; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 11 121 [false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 11 121 [true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 12 121 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 12 121 [true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 13 121 [false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 12 121 [false; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 11 121 [false; false; true; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 11 121 [true; false; true; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [false; false; false; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [true; false; false; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 10 121 [false; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 8 121 [false; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 7 121 [false; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 121 [false; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 6 121 [true; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ]
].

Definition ops_chunk_17 : list Op := [
  OpJump 6 5 121 [false; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 121 [true; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 5 121 [false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 3 121 [false; false; false; false; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 121 [false; false; true; false; false; false; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 121 [true; false; true; false; false; false; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 2 121 [false; true; false; true; true; false; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 1 121 [false; false; true; true; false; true; true; false; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpJump 6 1 121 [true; false; true; true; false; true; true; false; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 2; SlZ];
  OpRun 344;
  OpRun 346;
  OpRun 343;
  OpRun 576;
  OpRun 468;
  OpRun 348;
  OpRun 522;
  OpRun 430;
  OpRun 364;
  OpRun 244;
  OpRun 211;
  OpRun 579;
  OpRun 243;
  OpRun 460;
  OpRun 210;
  OpRun 334;
  OpRun 219;
  OpRun 218;
  OpRun 220;
  OpRun 358;
  OpJump 5 1 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 7 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 7 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 8 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 8 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 9 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 9 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 11 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 11 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 12 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 12 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 13 123 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 13 123 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 13 123 [false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 12 123 [false; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 11 123 [false; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 123 [false; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 9 123 [false; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 8 123 [false; false; true; false; true; false; true; false; true; false; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 241;
  OpRun 222;
  OpRun 226;
  OpRun 368;
  OpJump 5 1 127 [true; false; false; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 1 127 [false; true; true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 1 127 [true; true; true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 127 [true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 127 [false; true; true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 127 [true; true; true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 127 [true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 127 [false; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 127 [true; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 127 [true; false; false; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 127 [false; true; true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 127 [true; true; true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 127 [true; false; false; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 127 [false; true; true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 127 [true; true; true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 127 [true; false; false] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 127 [false; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 127 [true; true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 127 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 127 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 127 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 127 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 127 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 1 127 [false; false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 228;
  OpRun 220;
  OpRun 229;
  OpRun 372;
  OpRun 238;
  OpRun 237;
  OpRun 239;
  OpRun 396;
  OpRun 243;
  OpRun 249;
  OpRun 389;
  OpRun 380;
  OpJump 5 2 142 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 142 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 142 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 142 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 142 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 142 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 142 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 142 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 142 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 142 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 7 142 [false; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 7 142 [true; true] [SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 8 123 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 8 123 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 9 123 [false; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 9 123 [true; true; false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 123 [false; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 123 [true; true; false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 11 123 [false; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 11 123 [true; true; false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 12 123 [false; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 12 123 [true; true; false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 13 123 [false; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 12 123 [false; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 11 123 [false; false; true; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 11 123 [true; false; true; false; true; true; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 123 [false; false; false; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 123 [true; false; false; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 10 123 [false; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 8 123 [false; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 7 123 [false; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 123 [false; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 6 123 [true; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 123 [false; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 5 123 [true; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 123 [false; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 4 123 [true; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 3 123 [false; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 123 [false; false; true; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 123 [true; false; true; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 2 123 [false; true; false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 1 123 [false; false; true; true; false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 5 1 123 [true; false; true; true; false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 315;
  OpRun 310;
  OpRun 307;
  OpRun 521;
  OpRun 411;
  OpRun 409;
  OpRun 489;
  OpRun 565;
  OpRun 259;
  OpRun 337;
  OpRun 417;
  OpRun 644;
  OpJump 5 1 156 [true; false; false; false; false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 1 156 [false; true; true; false; false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 1 156 [true; true; true; false; false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 2 156 [true; false; false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 2 156 [false; true; true; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 2 156 [true; true; true; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 3 156 [true; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 4 156 [true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 5 156 [true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 6 156 [true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 7 156 [false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 7 156 [true; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 8 156 [false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 8 156 [true; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 9 156 [true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 9 156 [false; true; false; false; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 9 156 [true; true; false; false; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 11 156 [true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 12 156 [false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 12 156 [true; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 13 156 [false; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 13 156 [true; false; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 13 156 [false; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 12 156 [false; false; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 11 156 [false; false; true; false; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 11 156 [true; false; true; false; true; true; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 11 156 [false; true; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 10 156 [false; false; true; true; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 10 156 [true; false; true; true; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 9 156 [false; false; false; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 9 156 [true; false; false; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 9 156 [false; true; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 8 156 [false; false; true; true; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 8 156 [true; false; true; true; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 7 156 [false; false; false; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 7 156 [true; false; false; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 7 156 [false; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 5 156 [false; false; false; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 5 156 [true; false; false; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 5 156 [false; true; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 4 156 [false; false; true; true; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 3 156 [false; false; true; false; true; true; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 3 156 [true; false; true; false; true; true; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 3 156 [false; true; false; true; false; false; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 2 156 [false; false; true; true; false; true; false; false; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ]
].

Definition ops_chunk_18 : list Op := [
  OpJump 5 2 156 [true; false; true; true; false; true; false; false; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 2 156 [false; true; false; false; false; true; false; false; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 5 1 156 [false; false; true; true; false; false; false; true; false; false; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpRun 346;
  OpRun 333;
  OpRun 616;
  OpRun 1603;
  OpJump 5 1 423 [false; true; false; false; false; false; false; true; false; false; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 1 423 [true; true; false; false; false; false; false; true; false; false; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 4 423 [false; true; false; false; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 4 423 [true; true; false; false; true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 6 423 [true; false; true; true; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 6 423 [false; true; false; false; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 6 423 [true; true; false; false; true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 8 423 [true; true; false; false; true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 10 423 [true; true; false; false; false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 12 423 [false; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 12 423 [true; true; false; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 13 423 [false; false; false; false; false; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 12 423 [false; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 12 423 [true; false; true; false; false; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 9 423 [false; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 9 423 [true; false; false; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 9 423 [false; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 8 423 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 7 423 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 6 423 [false; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 6 423 [true; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 6 423 [false; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 5 423 [false; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 5 423 [true; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 5 423 [false; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 4 423 [false; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 4 423 [true; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 4 423 [false; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 3 423 [false; false; true; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 3 423 [true; false; true; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 2 423 [false; false; false; true; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 5 2 423 [true; false; false; true; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpRun 598;
  OpRun 592;
  OpRun 592;
  OpRun 1103;
  OpRun 466;
  OpRun 307;
  OpRun 785;
  OpRun 705;
  OpRun 333;
  OpRun 510;
  OpRun 327;
  OpRun 1461;
  OpRun 603;
  OpRun 891;
  OpRun 882;
  OpRun 629;
  OpRun 112;
  OpRun 623;
  OpRun 112;
  OpRun 604;
  OpRun 249;
  OpRun 475;
  OpRun 259;
  OpRun 613;
  OpRun 238;
  OpRun 471;
  OpRun 615;
  OpRun 268;
  OpRun 187;
  OpRun 193;
  OpRun 249;
  OpRun 501;
  OpRun 166;
  OpRun 165;
  OpRun 167;
  OpRun 353;
  OpRun 142;
  OpRun 273;
  OpRun 280;
  OpRun 462;
  OpJump 6 1 153 [false; true; true; true] [SlN 1; SlZ; SlZ; SlZ; SlP 2; SlZ; SlZ; SlZ; SlN 2; SlZ; SlZ; SlP 2; SlZ];
  OpRun 285;
  OpRun 284;
  OpRun 457;
  OpRun 462;
  OpRun 285;
  OpRun 273;
  OpRun 364;
  OpRun 243;
  OpRun 128;
  OpRun 350;
  OpRun 189;
  OpRun 196;
  OpRun 205;
  OpRun 292;
  OpRun 214;
  OpRun 213;
  OpRun 215;
  OpRun 316;
  OpJump 7 1 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 2 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 2 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 3 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 3 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 4 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 4 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 5 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 5 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 6 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 6 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 7 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 7 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 8 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 8 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 9 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 9 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 10 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 10 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 11 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 11 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 12 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 12 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 13 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 13 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 14 93 [false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 14 93 [true; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 13 93 [false; false; false; false; false; true] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 12 93 [false; false; true; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 12 93 [true; false; true; false; false; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 9 93 [false; false; false; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 9 93 [true; false; false; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 9 93 [false; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 8 93 [false; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 7 93 [false; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 6 93 [false; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 6 93 [true; false; true; false; true; false; true; true; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 6 93 [false; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 5 93 [false; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 5 93 [true; false; true; true; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 5 93 [false; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 4 93 [false; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 4 93 [true; false; true; true; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 4 93 [false; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 3 93 [false; false; true; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpJump 7 3 93 [true; false; true; true; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ];
  OpRun 297;
  OpRun 274;
  OpRun 278;
  OpRun 438;
  OpRun 267;
  OpRun 365;
  OpRun 372;
  OpRun 634;
  OpRun 381;
  OpRun 380;
  OpRun 367;
  OpRun 620;
  OpRun 366;
  OpRun 273;
  OpRun 417;
  OpRun 420;
  OpJump 7 2 77 [true; false; false; true; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpJump 7 2 77 [false; true; true; true; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 1; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ];
  OpRun 284;
  OpRun 261;
  OpRun 263;
  OpRun 410;
  OpRun 263;
  OpRun 257;
  OpRun 492;
  OpRun 473;
  OpRun 490;
  OpRun 224;
  OpRun 477;
  OpRun 833;
  OpJump 7 1 271 [true; true; false; false; true; true; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 7 1 271 [false; false; false; false; true; true; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 7 1 271 [true; false; false; false; true; true; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpJump 7 1 271 [false; true; true; false; true; true; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlZ; SlN 2; SlZ; SlP 4; SlZ; SlN 4; SlZ; SlZ; SlP 4; SlZ];
  OpRun 491;
  OpRun 480;
  OpRun 731;
  OpRun 601;
  OpJump 7 2 156 [true; false; true; true; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 2 156 [false; true; false; false; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 2 156 [true; true; false; false; false; false; false; false; false; false; false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 7 156 [false; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 7 156 [true; true; false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 8 156 [false; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 8 156 [true; true; false; false; true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 10 156 [true; false; false; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 10 156 [false; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 10 156 [true; true; true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 11 156 [true; false; false; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 11 156 [false; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 11 156 [true; true; true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 12 156 [true; true; false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 13 156 [false; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 13 156 [true; true; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 13 156 [false; false; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 12 156 [false; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ]
].

Definition ops_chunk_19 : list Op := [
  OpJump 7 11 156 [false; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 10 156 [false; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 9 156 [false; false; true; false; true; false; true; false; true; false; true; false] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpRun 306;
  OpRun 294;
  OpRun 298;
  OpRun 480;
  OpJump 7 1 160 [true; false; false; false; false; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 1 160 [false; true; true; false; false; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 1 160 [true; true; true; false; false; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 2 160 [true; false; false; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 2 160 [false; true; true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 2 160 [true; true; true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 3 160 [true; false; false; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 3 160 [false; true; true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 3 160 [true; true; true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 4 160 [true; false; false; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 4 160 [false; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 4 160 [true; true; true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 5 160 [true; false; false; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 5 160 [false; true; true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 5 160 [true; true; true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 6 160 [true; false; false; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 6 160 [false; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 6 160 [true; true; true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 7 160 [true; false; false] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 7 160 [false; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 7 160 [true; true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 7 160 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 6 160 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 5 160 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 4 160 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 3 160 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 2 160 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 1 160 [false; false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpRun 293;
  OpRun 292;
  OpRun 301;
  OpRun 484;
  OpRun 310;
  OpRun 309;
  OpRun 311;
  OpRun 508;
  OpRun 315;
  OpRun 321;
  OpRun 501;
  OpRun 492;
  OpJump 7 2 175 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 2 175 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 3 175 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 3 175 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 4 175 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 4 175 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 5 175 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 5 175 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 6 175 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 6 175 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 7 175 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 7 175 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 8 175 [false; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 8 175 [true; true] [SlZ; SlZ; SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 9 156 [false; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 9 156 [true; true; false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 10 156 [false; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 10 156 [true; true; false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 11 156 [false; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 11 156 [true; true; false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 12 156 [false; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 12 156 [true; true; false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 13 156 [false; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 13 156 [true; true; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 13 156 [false; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 12 156 [false; false; true; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 12 156 [true; false; true; false; false; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 11 156 [false; false; false; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 11 156 [true; false; false; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 9 156 [false; false; false; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 9 156 [true; false; false; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 7 156 [false; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 5 156 [false; false; false; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 4 156 [false; false; true; false; false; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 4 156 [true; false; true; false; false; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 3 156 [false; false; false; true; false; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 3 156 [true; false; false; true; false; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 2 156 [false; false; false; true; true; true; false; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpJump 7 1 156 [false; false; true; false; false; true; true; true; false; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlP 2; SlZ; SlN 3; SlZ; SlZ; SlP 3; SlZ];
  OpRun 392;
  OpRun 373;
  OpRun 374;
  OpRun 691;
  OpJump 7 1 423 [false; true; false; true; true; true; true; true; false; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpRun 662;
  OpRun 651;
  OpRun 1157;
  OpRun 1150;
  OpJump 7 2 423 [false; true; true; true; true; true; false; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 2 423 [true; true; true; true; true; true; false; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 3 423 [true; true; true; true; false; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 4 423 [true; true; false; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 5 423 [false; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 5 423 [true; true; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 5 423 [false; false; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 5 423 [true; false; true; false; true; false; false; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 5 423 [false; true; false; true; false; true; true; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 5 423 [true; true; false; true; false; true; true; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 6 423 [false; true; false; true; true; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 6 423 [true; true; false; true; true; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 7 423 [false; true; true; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 7 423 [true; true; true; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 8 423 [true; false; false; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 8 423 [false; true; true; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 8 423 [true; true; true; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 9 423 [true; true; true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 10 423 [true; false; false; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 10 423 [false; true; true; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 10 423 [true; true; true; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 11 423 [true; true; true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 12 423 [true; true; false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 13 423 [false; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 13 423 [true; true; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 13 423 [false; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 12 423 [false; false; true; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 12 423 [true; false; true; false; true; true; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 11 423 [false; false; false; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 11 423 [true; false; false; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 11 423 [false; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 9 423 [false; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 8 423 [false; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 7 423 [false; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 7 423 [true; false; true; false; true; false; false; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 6 423 [false; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 6 423 [true; false; false; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 5 423 [false; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 5 423 [true; false; false; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 4 423 [false; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 4 423 [true; false; false; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpJump 7 2 423 [false; false; false; false; false; true; true; true; true; true; true; true; false; true; false; true; true; false; true; true; true; true; false; true; false; false; true; true] [SlN 1; SlZ; SlZ; SlN 4; SlZ; SlZ; SlZ; SlZ; SlZ; SlZ; SlP 6; SlZ];
  OpRun 647;
  OpRun 552
].

Definition all_ops : list Op :=
  ops_chunk_0 ++
  ops_chunk_1 ++
  ops_chunk_2 ++
  ops_chunk_3 ++
  ops_chunk_4 ++
  ops_chunk_5 ++
  ops_chunk_6 ++
  ops_chunk_7 ++
  ops_chunk_8 ++
  ops_chunk_9 ++
  ops_chunk_10 ++
  ops_chunk_11 ++
  ops_chunk_12 ++
  ops_chunk_13 ++
  ops_chunk_14 ++
  ops_chunk_15 ++
  ops_chunk_16 ++
  ops_chunk_17 ++
  ops_chunk_18 ++
  ops_chunk_19.

Lemma cert_ok : check_all_ops all_ops = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma halt_internal : halts tm c0.
Proof.
  exact (check_all_ops_sound all_ops cert_ok).
Qed.

End Internal.

Theorem halt : halts tm c0.
Proof.
  exact Internal.halt_internal.
Qed.
