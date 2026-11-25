(* 1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC--- never halts. *)

From Coq Require Import Bool List Lists.Streams PeanoNat Lia String.
From BusyCoq Require Import Individual62.
Import ListNotations.

Set Default Goal Selector "!".

Definition tm : TM := TM_from_str "1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---".
Arguments tm _ : simpl never.

Module Internal.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (@const Sym S0).

(* ========================================================================== *)
(* Section 1: Tape & Stream Helpers, Fast Execution Tactics                   *)
(* ========================================================================== *)

Definition ptrans {c1 c2 c3 : Q * tape}
    (h1 : c1 -[ tm ]->+ c2) (h2 : c2 -[ tm ]->+ c3) : c1 -[ tm ]->+ c3 :=
  progress_trans tm c1 c2 c3 h1 h2.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  lazymatch goal with
  | |- (?q, (_, ?s, _)) -[ _ ]->* (?q, (_, ?s, _)) =>
    apply evstep_refl';
    (reflexivity || (repeat rewrite <- const_unfold; reflexivity))
  end.

Ltac run_steps :=
  cbn [Str_app Streams.hd Streams.tl];
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  repeat (try solve [fast_finish]; fast_step).

Ltac step_via mid :=
  eapply (@ptrans _ mid _); [run_steps |].

(* ========================================================================== *)
(* Section 2: Step-Indexed Safety                                             *)
(* ========================================================================== *)

Definition Safe (k : nat) (c : Q * tape) : Prop :=
  forall j, j <= k -> ~ halts_in tm c j.

Arguments Safe _ _ : simpl never.

Lemma Safe_of_stepPlus {k : nat} {c c' : Q * tape}
    (Hstep : c -[ tm ]->+ c')
    (Hsafe : forall k', k' < k -> Safe k' c') :
  Safe k c.
Proof.
  intros j Hj Hhalt.
  destruct (progress_multistep _ _ _ Hstep) as [n Hms].
  destruct (Nat.leb_spec (S n) j) as [Hle | Hlt].
  - assert (Hlt_k : j - S n < k) by lia.
    apply (Hsafe (j - S n) Hlt_k (j - S n) (Nat.le_refl _)).
    exact (preceeds_halt _ _ _ _ _ Hhalt Hms Hle).
  - assert (Hgt : S n > j) by lia.
    exact (exceeds_halt _ _ _ _ _ Hhalt Hgt Hms).
Qed.

Lemma nonhalt_of_forall_safe (c_start : Q * tape)
    (Hinit : c0 -[ tm ]->+ c_start)
    (Hsafe : forall k, Safe k c_start) :
  ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact (progress_evstep _ _ _ Hinit).
  - intros [k Hhalt].
    exact (Hsafe k k (Nat.le_refl k) Hhalt).
Qed.

(* ========================================================================== *)
(* Section 3: 16-Block Transducer Encoding & BoxStep Contracts                *)
(* ========================================================================== *)

Inductive Blk : Type :=
  | bU
  | bV
  | bAP
  | bQAA
  | bRAA
  | bAAA4
  | bA4B
  | bB7
  | bBC
  | bCB
  | bRA4
  | bQA4
  | bA47
  | bC7
  | bA4C
  | bCC.

Definition blkBits (b : Blk) : list Sym :=
  match b with
  | bU => [S0; S0; S1; S0; S0; S1; S0; S0; S1; S0; S0; S1]
  | bV => [S0; S0; S0; S0; S0; S1; S0; S0; S0; S0; S0; S1]
  | bAP => [S0; S0; S1; S0; S0; S1; S0; S1; S0; S1; S1; S1; S0; S1]
  | bQAA => [S0; S0; S0; S0; S1; S0; S1; S1; S0; S0; S1; S0; S0; S1]
  | bRAA => [S0; S0; S1; S0; S1; S1; S1; S1; S0; S0; S1; S0; S0; S1]
  | bAAA4 => [S0; S0; S1; S0; S0; S1; S0; S0; S1; S0; S0; S0; S0; S1]
  | bA4B => [S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S0; S0; S0; S1]
  | bB7 => [S0; S0; S0; S0; S0; S1; S0; S0; S0; S0; S0; S0; S0; S1]
  | bBC => [S0; S0; S0; S0; S0; S1; S0; S0; S1; S0; S1; S1; S0; S1]
  | bCB => [S0; S0; S1; S0; S1; S1; S0; S1; S0; S0; S0; S0; S0; S1]
  | bRA4 => [S0; S0; S1; S0; S1; S1; S1; S1; S0; S0; S1; S0; S0; S0; S0; S1]
  | bQA4 => [S0; S0; S0; S0; S1; S0; S1; S1; S0; S0; S1; S0; S0; S0; S0; S1]
  | bA47 => [S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S0; S0; S0; S0; S0; S1]
  | bC7 => [S0; S0; S1; S0; S1; S1; S0; S1; S0; S0; S0; S0; S0; S0; S0; S1]
  | bA4C => [S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S1; S0; S1; S1; S0; S1]
  | bCC => [S0; S0; S1; S0; S1; S1; S0; S1; S0; S0; S1; S0; S1; S1; S0; S1]
  end.

Definition endBits : list Sym := [S0; S0; S1; S0; S1; S1; S1; S1; S0; S1; S0; S1; S1; S1].
Definition h0Bits : list Sym := [S0; S0; S0; S0; S0; S0; S1].
Definition h1Bits : list Sym := [S0; S0; S0; S1; S0; S1; S1; S0; S0; S1; S0; S0; S1].

Fixpoint enc (xs : list Blk) : side :=
  match xs with
  | [] => endBits *> 0inf
  | b :: rest => blkBits b *> enc rest
  end.

Lemma enc_nil : enc [] = endBits *> 0inf.
Proof. reflexivity. Qed.

Lemma enc_cons (b : Blk) (xs : list Blk) : enc (b :: xs) = blkBits b *> enc xs.
Proof. reflexivity. Qed.

Arguments enc _ : simpl never.

Definition outCol (c : bool) (r : side) : side :=
  match c with
  | true => [S0; S1] *> r
  | false => [S0; S0; S0; S1] *> r
  end.

Definition BoxStep (u : side) (c : bool) (v : side) : Prop :=
  forall (x : Sym) (l : side),
    ([S0; S0; x] *> l) {{A}}> u -[ tm ]->+ l {{E}}> (x >> outCol c v).

Definition IsH1Lead (b : Blk) : Prop :=
  match b with
  | bAP | bAAA4 | bU => True
  | _ => False
  end.

Definition cfgH0 (xs : list Blk) : Q * tape :=
  (S1 >> 0inf) {{B}}> (h0Bits *> enc xs).

Definition cfgH1 (xs : list Blk) : Q * tape :=
  (S1 >> 0inf) {{B}}> (h1Bits *> enc xs).

Definition BoxIH (xs : list Blk) : Prop :=
  forall ws : list Blk,
    List.length ws = List.length xs ->
    exists (c : bool) (ys : list Blk),
      List.length ys = List.length ws /\ BoxStep (enc ws) c (enc ys).

Definition BoxConsOut (b : Blk) (xs : list Blk) : Prop :=
  exists (c : bool) (b' : Blk) (ys : list Blk),
    List.length ys = List.length xs /\
    (IsH1Lead b -> c = true) /\
    BoxStep (enc (b :: xs)) c (enc (b' :: ys)).

(* ========================================================================== *)
(* Section 4: Per-Block Transducer Step Lemmas                                *)
(* ========================================================================== *)

Lemma box_end : BoxStep (enc []) false (enc []).
Proof.
  intros x l.
  rewrite enc_nil; unfold endBits, outCol.
  step_via (([S0; S1; S1; S1; S1; S0; S1; S1; S0; S0] *> (x >> l)) {{A}}> ([S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S1; S1] *> (x >> l)) {{E}}> ([S1; S1; S0; S0; S1; S0; S1; S1; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  run_steps.
Qed.

Lemma box_bU (xs : list Blk) (ih : BoxIH xs) : BoxConsOut bU xs.
Proof.
  destruct (ih xs eq_refl) as [c1 [ys1 [hlen1 hcall1]]].
  assert (hs1 : forall (x : Sym) (l : side),
    ([S0; S0; x] *> l) {{A}}> (blkBits bU *> enc xs) -[ tm ]->+
    (([S0; S0; S1] *> ([S1; S1; S0; S1; S1; S1; S1; S1; S0; S1; S1] *> (x >> l))) {{A}}> enc xs)).
  { intros x l; unfold blkBits.
    step_via (([S1; S1; S1; S1; S1; S0; S1; S1] *> (x >> l)) {{F}}> ([S0; S0; S1; S1; S1; S1] *> enc xs)).
    run_steps.
  }
  destruct c1.
  - exists true, bV, ys1.
    split; [exact hlen1 | split; [exact (fun _ => eq_refl) | intros x l]].
    rewrite (enc_cons bU xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S1 _) |].
    rewrite (enc_cons bV ys1); unfold outCol, blkBits.
    run_steps.
  - exists true, bB7, ys1.
    split; [exact hlen1 | split; [exact (fun _ => eq_refl) | intros x l]].
    rewrite (enc_cons bU xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S1 _) |].
    rewrite (enc_cons bB7 ys1); unfold outCol, blkBits.
    run_steps.
Qed.

Lemma box_bV (xs : list Blk) (ih : BoxIH xs) : BoxConsOut bV xs.
Proof.
  destruct (ih xs eq_refl) as [c1 [ys1 [hlen1 hcall1]]].
  assert (hs1 : forall (x : Sym) (l : side),
    ([S0; S0; x] *> l) {{A}}> (blkBits bV *> enc xs) -[ tm ]->+
    (([S0; S0; S0] *> ([S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1] *> (x >> l))) {{A}}> enc xs)).
  { intros x l; unfold blkBits.
    step_via (([S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1] *> (x >> l)) {{C}}> ([S0; S1] *> enc xs)).
    run_steps.
  }
  destruct c1.
  - exists true, bU, ys1.
    split; [exact hlen1 | split; [exact (fun _ => eq_refl) | intros x l]].
    rewrite (enc_cons bV xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S0 _) |].
    rewrite (enc_cons bU ys1); unfold outCol, blkBits.
    run_steps.
  - exists true, bAAA4, ys1.
    split; [exact hlen1 | split; [exact (fun _ => eq_refl) | intros x l]].
    rewrite (enc_cons bV xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S0 _) |].
    rewrite (enc_cons bAAA4 ys1); unfold outCol, blkBits.
    run_steps.
Qed.

Lemma box_bAP (xs : list Blk) (ih : BoxIH xs) : BoxConsOut bAP xs.
Proof.
  destruct (ih xs eq_refl) as [c1 [ys1 [hlen1 hcall1]]].
  assert (hs1 : forall (x : Sym) (l : side),
    ([S0; S0; x] *> l) {{A}}> (blkBits bAP *> enc xs) -[ tm ]->+
    (([S0; S0; S0] *> ([S1; S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1] *> (x >> l))) {{A}}> enc xs)).
  { intros x l; unfold blkBits.
    run_steps.
  }
  destruct c1.
  - exists true, bQAA, ys1.
    split; [exact hlen1 | split; [exact (fun _ => eq_refl) | intros x l]].
    rewrite (enc_cons bAP xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S0 _) |].
    rewrite (enc_cons bQAA ys1); unfold outCol, blkBits.
    run_steps.
  - exists true, bQA4, ys1.
    split; [exact hlen1 | split; [exact (fun _ => eq_refl) | intros x l]].
    rewrite (enc_cons bAP xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S0 _) |].
    rewrite (enc_cons bQA4 ys1); unfold outCol, blkBits.
    run_steps.
Qed.

Lemma box_bQAA (xs : list Blk) : BoxConsOut bQAA xs.
Proof.
  exists true, bRAA, xs.
  split; [reflexivity | split; [exact (fun _ => eq_refl) | intros x l]].
  rewrite (enc_cons bQAA xs), (enc_cons bRAA xs); unfold blkBits, outCol.
  run_steps.
Qed.

Lemma box_bRAA (xs : list Blk) (ih : BoxIH xs) : BoxConsOut bRAA xs.
Proof.
  destruct (ih xs eq_refl) as [c1 [ys1 [hlen1 hcall1]]].
  assert (hs1 : forall (x : Sym) (l : side),
    ([S0; S0; x] *> l) {{A}}> (blkBits bRAA *> enc xs) -[ tm ]->+
    (([S0; S0; S1] *> ([S1; S1; S0; S1; S1; S1; S1; S1; S0; S1; S1; S0; S0] *> (x >> l))) {{A}}> enc xs)).
  { intros x l; unfold blkBits.
    run_steps.
  }
  destruct c1.
  - destruct (ih ys1 hlen1) as [c2 [ys2 [hlen2 hcall2]]].
    assert (hs2 : forall (x : Sym) (l : side),
      (([S1; S1; S0; S1; S1; S1; S1; S1; S0; S1; S1; S0; S0] *> (x >> l)) {{E}}> (S1 >> outCol true (enc ys1))) -[ tm ]->+
      (([S0; S0; S0] *> ([S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S1; S1] *> (x >> l))) {{A}}> enc ys1)).
    { intros x l; unfold outCol.
      step_via (([S1; S0; S0; S0; S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{E}}> ([S0; S1; S1; S0; S1] *> enc ys1)).
      run_steps.
    }
    destruct c2.
    + exists false, bU, ys2.
      split; [exact (eq_trans hlen2 hlen1) | split; [exact (fun h => False_ind _ h) | intros x l]].
      rewrite (enc_cons bRAA xs).
      eapply ptrans; [exact (hs1 x l) |].
      eapply ptrans; [exact (hcall1 S1 _) |].
      eapply ptrans; [exact (hs2 x l) |].
      eapply ptrans; [exact (hcall2 S0 _) |].
      rewrite (enc_cons bU ys2); unfold outCol, blkBits.
      run_steps.
    + exists false, bAAA4, ys2.
      split; [exact (eq_trans hlen2 hlen1) | split; [exact (fun h => False_ind _ h) | intros x l]].
      rewrite (enc_cons bRAA xs).
      eapply ptrans; [exact (hs1 x l) |].
      eapply ptrans; [exact (hcall1 S1 _) |].
      eapply ptrans; [exact (hs2 x l) |].
      eapply ptrans; [exact (hcall2 S0 _) |].
      rewrite (enc_cons bAAA4 ys2); unfold outCol, blkBits.
      run_steps.
  - exists false, bAP, ys1.
    split; [exact hlen1 | split; [exact (fun h => False_ind _ h) | intros x l]].
    rewrite (enc_cons bRAA xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S1 _) |].
    rewrite (enc_cons bAP ys1); unfold outCol, blkBits.
    step_via (([S1; S0; S0; S0; S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{E}}> ([S0; S1; S1; S0; S0; S0; S1] *> enc ys1)).
    run_steps.
Qed.

Lemma box_bAAA4 (xs : list Blk) : BoxConsOut bAAA4 xs.
Proof.
  exists true, bBC, xs.
  split; [reflexivity | split; [exact (fun _ => eq_refl) | intros x l]].
  rewrite (enc_cons bAAA4 xs), (enc_cons bBC xs); unfold blkBits, outCol.
  step_via (([S1; S1; S1; S1; S1; S0; S1; S1] *> (x >> l)) {{F}}> ([S0; S0; S1; S1; S1; S0; S0; S1] *> enc xs)).
  run_steps.
Qed.

Lemma box_bA4B (xs : list Blk) : BoxConsOut bA4B xs.
Proof.
  exists true, bCB, xs.
  split; [reflexivity | split; [exact (fun _ => eq_refl) | intros x l]].
  rewrite (enc_cons bA4B xs), (enc_cons bCB xs); unfold blkBits, outCol.
  run_steps.
Qed.

Lemma box_bB7 (xs : list Blk) : BoxConsOut bB7 xs.
Proof.
  exists true, bAP, xs.
  split; [reflexivity | split; [exact (fun _ => eq_refl) | intros x l]].
  rewrite (enc_cons bB7 xs), (enc_cons bAP xs); unfold blkBits, outCol.
  step_via (([S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1] *> (x >> l)) {{C}}> ([S0; S0; S0; S1] *> enc xs)).
  run_steps.
Qed.

Lemma box_bBC (xs : list Blk) (ih : BoxIH xs) : BoxConsOut bBC xs.
Proof.
  destruct (ih xs eq_refl) as [c1 [ys1 [hlen1 hcall1]]].
  assert (hs1 : forall (x : Sym) (l : side),
    ([S0; S0; x] *> l) {{A}}> (blkBits bBC *> enc xs) -[ tm ]->+
    (([S0; S0; S0] *> ([S1; S1; S0; S1; S1; S0; S0; S0; S1; S1; S0; S1; S1] *> (x >> l))) {{A}}> enc xs)).
  { intros x l; unfold blkBits.
    run_steps.
  }
  destruct c1.
  - destruct (ih ys1 hlen1) as [c2 [ys2 [hlen2 hcall2]]].
    assert (hs2 : forall (x : Sym) (l : side),
      (([S1; S1; S0; S1; S1; S0; S0; S0; S1; S1; S0; S1; S1] *> (x >> l)) {{E}}> (S0 >> outCol true (enc ys1))) -[ tm ]->+
      (([S0; S0; S1] *> ([S1; S1; S0; S1; S1; S1; S1; S0; S1; S1; S0; S1; S1] *> (x >> l))) {{A}}> enc ys1)).
    { intros x l; unfold outCol.
      run_steps.
    }
    destruct c2.
    + exists true, bA4B, ys2.
      split; [exact (eq_trans hlen2 hlen1) | split; [exact (fun _ => eq_refl) | intros x l]].
      rewrite (enc_cons bBC xs).
      eapply ptrans; [exact (hs1 x l) |].
      eapply ptrans; [exact (hcall1 S0 _) |].
      eapply ptrans; [exact (hs2 x l) |].
      eapply ptrans; [exact (hcall2 S1 _) |].
      rewrite (enc_cons bA4B ys2); unfold outCol, blkBits.
      run_steps.
    + exists true, bA47, ys2.
      split; [exact (eq_trans hlen2 hlen1) | split; [exact (fun _ => eq_refl) | intros x l]].
      rewrite (enc_cons bBC xs).
      eapply ptrans; [exact (hs1 x l) |].
      eapply ptrans; [exact (hcall1 S0 _) |].
      eapply ptrans; [exact (hs2 x l) |].
      eapply ptrans; [exact (hcall2 S1 _) |].
      rewrite (enc_cons bA47 ys2); unfold outCol, blkBits.
      run_steps.
  - exists true, bA4C, ys1.
    split; [exact hlen1 | split; [exact (fun _ => eq_refl) | intros x l]].
    rewrite (enc_cons bBC xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S0 _) |].
    rewrite (enc_cons bA4C ys1); unfold outCol, blkBits.
    step_via (([S1; S1; S1; S0; S1; S1; S0; S1; S1] *> (x >> l)) {{A}}> ([S1; S0; S0; S1; S0; S1; S1; S0; S1] *> enc ys1)).
    run_steps.
Qed.

Lemma box_bCB (xs : list Blk) (ih : BoxIH xs) : BoxConsOut bCB xs.
Proof.
  destruct (ih xs eq_refl) as [c1 [ys1 [hlen1 hcall1]]].
  assert (hs1 : forall (x : Sym) (l : side),
    ([S0; S0; x] *> l) {{A}}> (blkBits bCB *> enc xs) -[ tm ]->+
    (([S0; S0; S0] *> ([S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0] *> (x >> l))) {{A}}> enc xs)).
  { intros x l; unfold blkBits.
    run_steps.
  }
  destruct c1.
  - destruct (ih ys1 hlen1) as [c2 [ys2 [hlen2 hcall2]]].
    assert (hs2 : forall (x : Sym) (l : side),
      (([S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0] *> (x >> l)) {{E}}> (S0 >> outCol true (enc ys1))) -[ tm ]->+
      (([S0; S0; S1] *> ([S1; S1; S0; S1; S1; S1; S1; S1; S0; S1; S1; S1; S1] *> (x >> l))) {{A}}> enc ys1)).
    { intros x l; unfold outCol.
      step_via (([S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{B}}> ([S0; S1; S0; S0; S1] *> enc ys1)).
      run_steps.
    }
    destruct c2.
    + exists false, bV, ys2.
      split; [exact (eq_trans hlen2 hlen1) | split; [exact (fun h => False_ind _ h) | intros x l]].
      rewrite (enc_cons bCB xs).
      eapply ptrans; [exact (hs1 x l) |].
      eapply ptrans; [exact (hcall1 S0 _) |].
      eapply ptrans; [exact (hs2 x l) |].
      eapply ptrans; [exact (hcall2 S1 _) |].
      rewrite (enc_cons bV ys2); unfold outCol, blkBits.
      run_steps.
    + exists false, bB7, ys2.
      split; [exact (eq_trans hlen2 hlen1) | split; [exact (fun h => False_ind _ h) | intros x l]].
      rewrite (enc_cons bCB xs).
      eapply ptrans; [exact (hs1 x l) |].
      eapply ptrans; [exact (hcall1 S0 _) |].
      eapply ptrans; [exact (hs2 x l) |].
      eapply ptrans; [exact (hcall2 S1 _) |].
      rewrite (enc_cons bB7 ys2); unfold outCol, blkBits.
      run_steps.
  - exists false, bBC, ys1.
    split; [exact hlen1 | split; [exact (fun h => False_ind _ h) | intros x l]].
    rewrite (enc_cons bCB xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S0 _) |].
    rewrite (enc_cons bBC ys1); unfold outCol, blkBits.
    step_via (([S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{B}}> ([S0; S1; S0; S0; S0; S0; S1] *> enc ys1)).
    run_steps.
Qed.

Lemma box_bRA4 (xs : list Blk) (ih : BoxIH xs) : BoxConsOut bRA4 xs.
Proof.
  destruct (ih xs eq_refl) as [c1 [ys1 [hlen1 hcall1]]].
  assert (hs1 : forall (x : Sym) (l : side),
    ([S0; S0; x] *> l) {{A}}> (blkBits bRA4 *> enc xs) -[ tm ]->+
    (([S0; S0; S0] *> ([S1; S1; S0; S1; S1; S0; S0; S0; S1; S1; S0; S1; S1; S1; S1] *> (x >> l))) {{A}}> enc xs)).
  { intros x l; unfold blkBits.
    step_via (([S1; S1; S1; S0; S1; S1; S1; S1; S1; S0; S1; S1; S0; S0] *> (x >> l)) {{D}}> ([S0; S1; S0; S1] *> enc xs)).
    step_via (([S1; S1; S0; S0; S0; S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{F}}> ([S0; S0; S1; S1; S0; S1] *> enc xs)).
    run_steps.
  }
  destruct c1.
  - destruct (ih ys1 hlen1) as [c2 [ys2 [hlen2 hcall2]]].
    assert (hs2 : forall (x : Sym) (l : side),
      (([S1; S1; S0; S1; S1; S0; S0; S0; S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{E}}> (S0 >> outCol true (enc ys1))) -[ tm ]->+
      (([S0; S0; S1] *> ([S1; S1; S0; S1; S1; S1; S1; S0; S1; S1; S0; S1; S1; S1; S1] *> (x >> l))) {{A}}> enc ys1)).
    { intros x l; unfold outCol.
      run_steps.
    }
    destruct c2.
    + exists false, bA4B, ys2.
      split; [exact (eq_trans hlen2 hlen1) | split; [exact (fun h => False_ind _ h) | intros x l]].
      rewrite (enc_cons bRA4 xs).
      eapply ptrans; [exact (hs1 x l) |].
      eapply ptrans; [exact (hcall1 S0 _) |].
      eapply ptrans; [exact (hs2 x l) |].
      eapply ptrans; [exact (hcall2 S1 _) |].
      rewrite (enc_cons bA4B ys2); unfold outCol, blkBits.
      run_steps.
    + exists false, bA47, ys2.
      split; [exact (eq_trans hlen2 hlen1) | split; [exact (fun h => False_ind _ h) | intros x l]].
      rewrite (enc_cons bRA4 xs).
      eapply ptrans; [exact (hs1 x l) |].
      eapply ptrans; [exact (hcall1 S0 _) |].
      eapply ptrans; [exact (hs2 x l) |].
      eapply ptrans; [exact (hcall2 S1 _) |].
      rewrite (enc_cons bA47 ys2); unfold outCol, blkBits.
      run_steps.
  - exists false, bA4C, ys1.
    split; [exact hlen1 | split; [exact (fun h => False_ind _ h) | intros x l]].
    rewrite (enc_cons bRA4 xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S0 _) |].
    rewrite (enc_cons bA4C ys1); unfold outCol, blkBits.
    step_via (([S1; S1; S1; S0; S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{A}}> ([S1; S0; S0; S1; S0; S1; S1; S0; S1] *> enc ys1)).
    run_steps.
Qed.

Lemma box_bQA4 (xs : list Blk) : BoxConsOut bQA4 xs.
Proof.
  exists true, bRA4, xs.
  split; [reflexivity | split; [exact (fun _ => eq_refl) | intros x l]].
  rewrite (enc_cons bQA4 xs), (enc_cons bRA4 xs); unfold blkBits, outCol.
  run_steps.
Qed.

Lemma box_bA47 (xs : list Blk) : BoxConsOut bA47 xs.
Proof.
  exists true, bC7, xs.
  split; [reflexivity | split; [exact (fun _ => eq_refl) | intros x l]].
  rewrite (enc_cons bA47 xs), (enc_cons bC7 xs); unfold blkBits, outCol.
  run_steps.
Qed.

Lemma box_bC7 (xs : list Blk) (ih : BoxIH xs) : BoxConsOut bC7 xs.
Proof.
  destruct (ih xs eq_refl) as [c1 [ys1 [hlen1 hcall1]]].
  assert (hs1 : forall (x : Sym) (l : side),
    ([S0; S0; x] *> l) {{A}}> (blkBits bC7 *> enc xs) -[ tm ]->+
    (([S0; S0; S0] *> ([S1; S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1] *> (x >> l))) {{A}}> enc xs)).
  { intros x l; unfold blkBits.
    step_via (([S0; S1; S1; S0; S1; S1; S0; S0] *> (x >> l)) {{E}}> ([S1; S1; S0; S1; S0; S1; S1; S1; S0; S1] *> enc xs)).
    step_via (([S0; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{D}}> ([S1; S1; S0; S1] *> enc xs)).
    run_steps.
  }
  destruct c1.
  - exists false, bQAA, ys1.
    split; [exact hlen1 | split; [exact (fun h => False_ind _ h) | intros x l]].
    rewrite (enc_cons bC7 xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S0 _) |].
    rewrite (enc_cons bQAA ys1); unfold outCol, blkBits.
    run_steps.
  - exists false, bQA4, ys1.
    split; [exact hlen1 | split; [exact (fun h => False_ind _ h) | intros x l]].
    rewrite (enc_cons bC7 xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S0 _) |].
    rewrite (enc_cons bQA4 ys1); unfold outCol, blkBits.
    run_steps.
Qed.

Lemma box_bA4C (xs : list Blk) : BoxConsOut bA4C xs.
Proof.
  exists true, bCC, xs.
  split; [reflexivity | split; [exact (fun _ => eq_refl) | intros x l]].
  rewrite (enc_cons bA4C xs), (enc_cons bCC xs); unfold blkBits, outCol.
  run_steps.
Qed.

Lemma box_bCC (xs : list Blk) (ih : BoxIH xs) : BoxConsOut bCC xs.
Proof.
  destruct (ih xs eq_refl) as [c1 [ys1 [hlen1 hcall1]]].
  assert (hs1 : forall (x : Sym) (l : side),
    ([S0; S0; x] *> l) {{A}}> (blkBits bCC *> enc xs) -[ tm ]->+
    (([S0; S0; S0] *> ([S1; S1; S0; S1; S1; S0; S0; S0; S1; S1; S0; S1; S1; S0; S0] *> (x >> l))) {{A}}> enc xs)).
  { intros x l; unfold blkBits.
    run_steps.
  }
  destruct c1.
  - destruct (ih ys1 hlen1) as [c2 [ys2 [hlen2 hcall2]]].
    assert (hs2 : forall (x : Sym) (l : side),
      (([S1; S1; S0; S1; S1; S0; S0; S0; S1; S1; S0; S1; S1; S0; S0] *> (x >> l)) {{E}}> (S0 >> outCol true (enc ys1))) -[ tm ]->+
      (([S0; S0; S1] *> ([S1; S1; S0; S1; S1; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0] *> (x >> l))) {{A}}> enc ys1)).
    { intros x l; unfold outCol.
      run_steps.
    }
    destruct c2.
    + exists false, bCB, ys2.
      split; [exact (eq_trans hlen2 hlen1) | split; [exact (fun h => False_ind _ h) | intros x l]].
      rewrite (enc_cons bCC xs).
      eapply ptrans; [exact (hs1 x l) |].
      eapply ptrans; [exact (hcall1 S0 _) |].
      eapply ptrans; [exact (hs2 x l) |].
      eapply ptrans; [exact (hcall2 S1 _) |].
      rewrite (enc_cons bCB ys2); unfold outCol, blkBits.
      step_via (([S0; S1; S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{D}}> ([S0; S0; S1; S0; S0; S0; S0; S0; S1] *> enc ys2)).
      run_steps.
    + exists false, bC7, ys2.
      split; [exact (eq_trans hlen2 hlen1) | split; [exact (fun h => False_ind _ h) | intros x l]].
      rewrite (enc_cons bCC xs).
      eapply ptrans; [exact (hs1 x l) |].
      eapply ptrans; [exact (hcall1 S0 _) |].
      eapply ptrans; [exact (hs2 x l) |].
      eapply ptrans; [exact (hcall2 S1 _) |].
      rewrite (enc_cons bC7 ys2); unfold outCol, blkBits.
      step_via (([S0; S1; S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{D}}> ([S0; S0; S1; S0; S0; S0; S0; S0; S0; S0; S1] *> enc ys2)).
      run_steps.
  - exists false, bCC, ys1.
    split; [exact hlen1 | split; [exact (fun h => False_ind _ h) | intros x l]].
    rewrite (enc_cons bCC xs).
    eapply ptrans; [exact (hs1 x l) |].
    eapply ptrans; [exact (hcall1 S0 _) |].
    rewrite (enc_cons bCC ys1); unfold outCol, blkBits.
    step_via (([S1; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0] *> (x >> l)) {{A}}> ([S1; S0; S0; S1; S0; S1; S1; S0; S1] *> enc ys1)).
    step_via (([S1; S1; S0; S1; S1; S1; S1] *> (x >> l)) {{E}}> ([S0; S1; S1; S0; S1; S0; S0; S1; S0; S1; S1; S0; S1] *> enc ys1)).
    run_steps.
Qed.

Lemma box_cons (b : Blk) (xs : list Blk) (ih : BoxIH xs) : BoxConsOut b xs.
Proof.
  exact (
    match b with
    | bU => box_bU xs ih
    | bV => box_bV xs ih
    | bAP => box_bAP xs ih
    | bQAA => box_bQAA xs
    | bRAA => box_bRAA xs ih
    | bAAA4 => box_bAAA4 xs
    | bA4B => box_bA4B xs
    | bB7 => box_bB7 xs
    | bBC => box_bBC xs ih
    | bCB => box_bCB xs ih
    | bRA4 => box_bRA4 xs ih
    | bQA4 => box_bQA4 xs
    | bA47 => box_bA47 xs
    | bC7 => box_bC7 xs ih
    | bA4C => box_bA4C xs
    | bCC => box_bCC xs ih
    end).
Qed.

Lemma box_len : forall (n : nat) (xs : list Blk),
    List.length xs = n ->
    exists (c : bool) (ys : list Blk),
      List.length ys = List.length xs /\ BoxStep (enc xs) c (enc ys).
Proof.
  induction n as [| n ih]; intros [| b xs] hlen.
  - exists false, (@nil Blk). split; [reflexivity | exact box_end].
  - discriminate hlen.
  - discriminate hlen.
  - injection hlen as hxs.
    destruct (box_cons b xs (fun ws hws => ih ws (eq_trans hws hxs)))
      as [c [b' [ys [hys [_ hst]]]]].
    exists c, (b' :: ys).
    split; [cbn [List.length]; f_equal; exact hys | exact hst].
Qed.

Lemma box_all (xs : list Blk) :
  exists (c : bool) (ys : list Blk),
    List.length ys = List.length xs /\ BoxStep (enc xs) c (enc ys).
Proof.
  exact (box_len (List.length xs) xs eq_refl).
Qed.

(* ========================================================================== *)
(* Section 5: Top-Level Cycle Closure & Non-Halting Theorem                   *)
(* ========================================================================== *)

Lemma step_h0 {b : Blk} (hb : IsH1Lead b) (ys : list Blk) :
  exists zs : list Blk, cfgH0 (b :: ys) -[ tm ]->+ cfgH1 zs.
Proof.
  destruct (box_cons b ys (fun ws _ => box_all ws))
    as [c [b' [ys' [_ [hlead hcall]]]]].
  pose proof (hlead hb) as hc; subst c.
  exists (b' :: ys').
  assert (hs1 : cfgH0 (b :: ys) -[ tm ]->+
    ([S0; S0; S0] *> ([S1; S1; S1; S1; S1; S0; S0; S1; S1] *> 0inf)) {{A}}> enc (b :: ys)).
  { unfold cfgH0, h0Bits.
     step_via (([S1; S1; S1; S1; S1; S0; S0; S1; S1] *> 0inf) {{C}}> ([S1; S0; S1] *> enc (b :: ys))).
     run_steps. }
  eapply ptrans; [exact hs1 |].
  eapply ptrans; [exact (hcall S0 _) |].
  unfold outCol, cfgH1, h1Bits.
  run_steps.
Qed.

Lemma step_h1 (xs : list Blk) :
  exists (b : Blk) (ys : list Blk),
    IsH1Lead b /\ (cfgH1 xs -[ tm ]->+ cfgH0 (b :: ys)).
Proof.
  destruct (box_all xs) as [c1 [ys1 [_ hcall1]]].
  assert (hs1 : cfgH1 xs -[ tm ]->+
    ([S0; S0; S1] *> ([S1; S1; S0; S1; S1; S1; S1; S1; S0; S1; S1; S0; S0; S1; S1] *> 0inf)) {{A}}> enc xs).
  { unfold cfgH1, h1Bits.
     step_via (([S0; S1; S1; S0; S0; S1; S1] *> 0inf) {{A}}> ([S0; S0; S1; S1; S1; S0; S0; S1; S0; S0; S1] *> enc xs)).
     run_steps. }
  destruct c1.
  - destruct (box_all ys1) as [c2 [ys2 [_ hcall2]]].
    assert (hs2 :
      ([S1; S1; S0; S1; S1; S1; S1; S1; S0; S1; S1; S0; S0; S1; S1] *> 0inf) {{E}}> (S1 >> outCol true (enc ys1)) -[ tm ]->+
      ([S0; S0; S0] *> ([S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S1; S1; S1; S1] *> 0inf)) {{A}}> enc ys1).
    { unfold outCol.
       step_via (([S1; S0; S0; S0; S1; S1; S0; S1; S1; S1; S1; S1; S1] *> 0inf) {{E}}> ([S0; S1; S1; S0; S1] *> enc ys1)).
       run_steps. }
    destruct c2.
    + exists bU, ys2.
      split; [exact I |].
      eapply ptrans; [exact hs1 |].
      eapply ptrans; [exact (hcall1 S1 _) |].
      eapply ptrans; [exact hs2 |].
      eapply ptrans; [exact (hcall2 S0 _) |].
      unfold outCol, cfgH0, h0Bits; rewrite (enc_cons bU ys2); unfold blkBits.
      run_steps.
    + exists bAAA4, ys2.
      split; [exact I |].
      eapply ptrans; [exact hs1 |].
      eapply ptrans; [exact (hcall1 S1 _) |].
      eapply ptrans; [exact hs2 |].
      eapply ptrans; [exact (hcall2 S0 _) |].
      unfold outCol, cfgH0, h0Bits; rewrite (enc_cons bAAA4 ys2); unfold blkBits.
      run_steps.
  - exists bAP, ys1.
    split; [exact I |].
    eapply ptrans; [exact hs1 |].
    eapply ptrans; [exact (hcall1 S1 _) |].
    unfold outCol, cfgH0, h0Bits; rewrite (enc_cons bAP ys1); unfold blkBits.
    step_via (([S1; S0; S0; S0; S1; S1; S0; S1; S1; S1; S1; S1; S1] *> 0inf) {{E}}> ([S0; S1; S1; S0; S0; S0; S1] *> enc ys1)).
    run_steps.
Qed.

Lemma top_step (xs : list Blk) :
  exists zs : list Blk, cfgH1 xs -[ tm ]->+ cfgH1 zs.
Proof.
  destruct (step_h1 xs) as [b [ys [hb h1]]].
  destruct (step_h0 hb ys) as [zs h2].
  exists zs.
  exact (ptrans h1 h2).
Qed.

Lemma init_to_h1 : c0 -[ tm ]->+ cfgH1 [bCC].
Proof.
  unfold c0, tape0, cfgH1, h1Bits.
  rewrite (enc_cons bCC (@nil Blk)), enc_nil; unfold blkBits, endBits.
  step_via (([S1; S1; S1; S1; S0; S0; S1; S1] *> 0inf) {{B}}> ([S0; S1] *> 0inf)).
  step_via (([S1; S0; S1; S1] *> 0inf) {{B}}> ([S1; S0; S1; S0; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S0; S0; S1; S1] *> 0inf) {{B}}> ([S1] *> 0inf)).
  step_via (([S0; S0; S1; S1; S1; S1; S1; S1] *> 0inf) {{D}}> ([S1; S1; S1; S0; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S0; S1; S1; S0; S1; S1] *> 0inf) {{C}}> ([S0; S0; S0; S1; S0; S0; S1; S0; S1; S1; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S0; S0; S1; S1; S1; S0; S1; S1; S0; S0; S0; S1; S1; S1; S1; S1; S0; S0; S1; S1] *> 0inf) {{A}}> ([S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S1; S1; S0; S0; S1; S1; S0; S1; S1; S1; S1; S1; S0; S0; S1; S1] *> 0inf) {{D}}> ([S0; S1; S1; S0; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S1; S1] *> 0inf) {{A}}> ([S1; S0; S1; S1; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S1; S0; S1; S1; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S1; S1; S0; S0; S1; S1] *> 0inf) {{F}}> ([S0; S0; S1; S1; S1; S1; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S1; S0; S1; S1; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S1; S0; S1; S1; S1; S1; S1; S0; S1; S1; S0; S0; S1; S1] *> 0inf) {{A}}> ([S1; S0; S1; S1; S0; S1; S0; S0; S1; S0; S1; S1; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S0; S0; S1; S1; S0; S0; S0; S1; S1; S0; S1; S1; S1; S1; S1; S1] *> 0inf) {{E}}> ([S0; S1; S0; S1; S0; S0; S1; S0; S1; S1; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S0; S0; S1; S1; S1; S0; S1; S1; S0; S0; S0; S1; S1; S0; S1; S1; S0; S0; S0; S1; S1; S0; S1; S1; S1; S1; S1; S1] *> 0inf) {{E}}> ([S1; S0; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S1; S1; S1; S0; S1; S1; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0; S0; S1; S1; S0; S1; S1; S1; S1; S1; S1] *> 0inf) {{D}}> ([S0; S1; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S0; S1; S1; S0; S1; S1; S1; S1; S0; S1; S1; S0; S1; S1; S1; S1; S1; S1] *> 0inf) {{C}}> ([S1; S0; S0; S1; S0; S0; S1; S0; S1; S1; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S0; S1; S1; S0; S1; S1] *> 0inf) {{C}}> ([S0; S0; S0; S1; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S1; S0; S1; S1; S0; S1; S0; S0; S1; S0; S1; S1; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  step_via (([S1; S1; S0; S1; S1; S1; S1; S1; S0; S0; S1; S1] *> 0inf) {{F}}> ([S0; S0; S1; S1; S1; S0; S0; S1; S0; S0; S1; S0; S1; S1; S0; S1; S0; S0; S1; S0; S1; S1; S1; S1; S0; S1; S0; S1; S1; S1] *> 0inf)).
  run_steps.
Qed.

Lemma top_safe (k : nat) : forall xs : list Blk, Safe k (cfgH1 xs).
Proof.
  induction k as [k ih] using strong_induction.
  intro xs.
  destruct (top_step xs) as [zs hstep].
  exact (Safe_of_stepPlus hstep (fun k' hk' => ih k' hk' zs)).
Qed.

Theorem nonhalt_internal : ~ halts tm c0.
Proof.
  exact (nonhalt_of_forall_safe (cfgH1 [bCC]) init_to_h1 (fun k => top_safe k [bCC])).
Qed.

End Internal.

Theorem nonhalt : ~ halts tm c0.
Proof. exact Internal.nonhalt_internal. Qed.
