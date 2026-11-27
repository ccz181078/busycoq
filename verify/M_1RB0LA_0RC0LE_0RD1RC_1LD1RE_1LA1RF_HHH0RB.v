(* PR #107: compute passive-frame returns from the input at each call.
   The tape simulation and passive frame soundness are adapted from the archived PR.
   The schedule specifies composition; the inputs, outputs and return counts
   are not loaded from transition dictionaries. *)
From BusyCoq Require Export Individual62.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Lists.Streams.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import PArith.BinPos.
From Coq Require Import NArith.BinNat.
From Coq Require Import NArith.Nnat.
From Coq Require Import Lia FSets.FMapPositive.
Import ListNotations.

Set Default Goal Selector "!".
Close Scope sym_scope.
Open Scope string_scope.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB").

Close Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Module M137.

(* Fast transition lookup lemmas so stepping never unfolds TM_from_str *)
Lemma tm_A0 : tm (A, S0) = Some (S1, R, B). Proof. reflexivity. Qed.
Lemma tm_A1 : tm (A, S1) = Some (S0, L, A). Proof. reflexivity. Qed.
Lemma tm_B0 : tm (B, S0) = Some (S0, R, C). Proof. reflexivity. Qed.
Lemma tm_B1 : tm (B, S1) = Some (S0, L, E). Proof. reflexivity. Qed.
Lemma tm_C0 : tm (C, S0) = Some (S0, R, D). Proof. reflexivity. Qed.
Lemma tm_C1 : tm (C, S1) = Some (S1, R, C). Proof. reflexivity. Qed.
Lemma tm_D0 : tm (D, S0) = Some (S1, L, D). Proof. reflexivity. Qed.
Lemma tm_D1 : tm (D, S1) = Some (S1, R, E). Proof. reflexivity. Qed.
Lemma tm_E0 : tm (E, S0) = Some (S1, L, A). Proof. reflexivity. Qed.
Lemma tm_E1 : tm (E, S1) = Some (S1, R, F). Proof. reflexivity. Qed.
Lemma tm_F1 : tm (F, S1) = Some (S0, R, B). Proof. reflexivity. Qed.

Ltac raw_step :=
  lazymatch goal with
  | |- (A, (_, S0, _)) -[ tm ]-> _ => eapply step_right; exact tm_A0
  | |- (A, (_, S1, _)) -[ tm ]-> _ => eapply step_left; exact tm_A1
  | |- (B, (_, S0, _)) -[ tm ]-> _ => eapply step_right; exact tm_B0
  | |- (B, (_, S1, _)) -[ tm ]-> _ => eapply step_left; exact tm_B1
  | |- (C, (_, S0, _)) -[ tm ]-> _ => eapply step_right; exact tm_C0
  | |- (C, (_, S1, _)) -[ tm ]-> _ => eapply step_right; exact tm_C1
  | |- (D, (_, S0, _)) -[ tm ]-> _ => eapply step_left; exact tm_D0
  | |- (D, (_, S1, _)) -[ tm ]-> _ => eapply step_right; exact tm_D1
  | |- (E, (_, S0, _)) -[ tm ]-> _ => eapply step_left; exact tm_E0
  | |- (E, (_, S1, _)) -[ tm ]-> _ => eapply step_right; exact tm_E1
  | |- (F, (_, S1, _)) -[ tm ]-> _ => eapply step_right; exact tm_F1
  end.

Lemma progress_one : forall c1 c2 c3,
  c1 -[ tm ]-> c2 -> c2 = c3 -> c1 -[ tm ]->+ c3.
Proof.
  intros c1 c2 c3 H Heq. subst c3. exact (progress_base H).
Qed.

Lemma progress_cons : forall c1 c2 c3,
  c1 -[ tm ]-> c2 -> c2 -[ tm ]->+ c3 -> c1 -[ tm ]->+ c3.
Proof.
  intros c1 c2 c3 H1 H2. exact (progress_step H1 H2).
Qed.

(* ========================================================================= *)
(* 1. Core Stack Types & Tape Encoding                                       *)
(* ========================================================================= *)

Inductive Sep3 : Type := sep0 | sep1 | sep2.

Inductive ElemL : Type :=
| el_single (d : nat) (b : Sep3)
| el_run10 (k : N).

Inductive ElemR : Type :=
| er_single (z : nat) (o : nat)
| er_run10 (k : N).

Inductive BaseState : Type :=
| bs_Init
| bs_Halt (ls0 : list ElemL) (rs0 : list ElemR)
| bs_AL (ls0 : list ElemL) (rs0 : list ElemR)
| bs_BR (ls0 : list ElemL) (rs0 : list ElemR)
| bs_BR0 (ls0 : list ElemL) (rs0 : list ElemR)
| bs_CR (ls0 : list ElemL) (rs0 : list ElemR)
| bs_DL (ls0 : list ElemL) (rs0 : list ElemR)
| bs_ER (ls0 : list ElemL) (rs0 : list ElemR).

Inductive FlatState : Type :=
| fs_Init
| fs_Halt (ls0 : list (nat * Sep3)) (rs0 : list (nat * nat))
| fs_AL (ls0 : list (nat * Sep3)) (rs0 : list (nat * nat))
| fs_BR (ls0 : list (nat * Sep3)) (rs0 : list (nat * nat))
| fs_BR0 (ls0 : list (nat * Sep3)) (rs0 : list (nat * nat))
| fs_CR (ls0 : list (nat * Sep3)) (rs0 : list (nat * nat))
| fs_DL (ls0 : list (nat * Sep3)) (rs0 : list (nat * nat))
| fs_ER (ls0 : list (nat * Sep3)) (rs0 : list (nat * nat)).

Fixpoint lWordAux (d : nat) (b : Sep3) : list Sym :=
  match d with
  | 0 =>
    match b with
    | sep0 => [S1; S0]
    | sep1 => [S1; S0; S0]
    | sep2 => [S1; S0; S0; S0]
    end
  | S d' => S1 :: lWordAux d' b
  end.

Definition lWord (p : nat * Sep3) : list Sym :=
  let (d, b) := p in lWordAux d b.

Fixpoint oWord (o : nat) : list Sym :=
  match o with
  | 0 => [S1; S0]
  | S o' => S1 :: oWord o'
  end.

Fixpoint rWordAux (z o : nat) : list Sym :=
  match z with
  | 0 => oWord o
  | S z' => S0 :: rWordAux z' o
  end.

Definition rWord (p : nat * nat) : list Sym :=
  let (z, o) := p in rWordAux z o.

Fixpoint encLeft (ls0 : list (nat * Sep3)) : Stream Sym :=
  match ls0 with
  | [] => const S0
  | p :: ls => lWord p *> encLeft ls
  end.

Fixpoint encRight (rs0 : list (nat * nat)) : Stream Sym :=
  match rs0 with
  | [] => const S0
  | p :: rs => rWord p *> encRight rs
  end.

Definition headLeftCfg (q : Q) (l r : Stream Sym) : Q * tape :=
  (q, (tl l, hd l, r)).

Definition headRightCfg (q : Q) (l r : Stream Sym) : Q * tape :=
  (q, (l, hd r, tl r)).

Definition encodeFlat (fs : FlatState) : Q * tape :=
  match fs with
  | fs_Init => c0
  | fs_Halt ls0 rs0 => headRightCfg F (encLeft ls0) (S0 >> encRight rs0)
  | fs_AL ls0 rs0 => headLeftCfg A (encLeft ls0) (encRight rs0)
  | fs_BR ls0 rs0 => headRightCfg B (encLeft ls0) (encRight rs0)
  | fs_BR0 ls0 rs0 => headRightCfg B (S0 >> encLeft ls0) (encRight rs0)
  | fs_CR ls0 rs0 => headRightCfg C (encLeft ls0) (encRight rs0)
  | fs_DL ls0 rs0 => headLeftCfg D (encLeft ls0) (encRight rs0)
  | fs_ER ls0 rs0 => headRightCfg E (encLeft ls0) (encRight rs0)
  end.

(* ========================================================================= *)
(* 2. Flat Stack Operations & Micro-Step Soundness                           *)
(* ========================================================================= *)

Definition bumpL (ls0 : list (nat * Sep3)) : list (nat * Sep3) :=
  match ls0 with
  | [] => [(0, sep0)]
  | (d, b) :: ls => (S d, b) :: ls
  end.

Definition push100L (ls0 : list (nat * Sep3)) : list (nat * Sep3) :=
  match ls0 with
  | [] => [(0, sep0)]
  | p :: ls => (0, sep1) :: p :: ls
  end.

Definition push1000L (ls0 : list (nat * Sep3)) : list (nat * Sep3) :=
  match ls0 with
  | [] => [(0, sep0)]
  | p :: ls => (0, sep2) :: p :: ls
  end.

Definition push0R (rs0 : list (nat * nat)) : list (nat * nat) :=
  match rs0 with
  | [] => []
  | (z, o) :: rs => (S z, o) :: rs
  end.

Definition push1R (rs0 : list (nat * nat)) : list (nat * nat) :=
  match rs0 with
  | [] => [(0, 0)]
  | (0, o) :: rs => (0, S o) :: rs
  | (S z, o) :: rs => (0, 0) :: (z, o) :: rs
  end.

Fixpoint push0RN (d : nat) (rs0 : list (nat * nat)) : list (nat * nat) :=
  match d with
  | 0 => rs0
  | S d' => push0RN d' (push0R rs0)
  end.

Definition consume1R (o : nat) (rs0 : list (nat * nat)) : list (nat * nat) :=
  match o with
  | 0 => push0R rs0
  | S o' => (0, o') :: rs0
  end.

Definition stepFlat (fs : FlatState) : option FlatState :=
  match fs with
  | fs_Halt _ _ => None
  | fs_Init => Some (fs_BR [(0, sep0)] [])
  | fs_AL [] rs0 => Some (fs_BR [(0, sep0)] rs0)
  | fs_AL ((d, b) :: ls0) rs0 =>
    let rs0' := push0RN d (push0R rs0) in
    let ls0' :=
      match b with
      | sep0 => bumpL ls0
      | sep1 => (0, sep0) :: ls0
      | sep2 => push100L ls0
      end in
    Some (fs_BR ls0' rs0')
  | fs_BR ls0 [] => Some (fs_DL ls0 [(0, 2)])
  | fs_BR ls0 ((0, o) :: rs0) =>
    match ls0 with
    | [] =>
      let rs0' :=
        match o with
        | 0 => push1R (push0R (push0R rs0))
        | S o' => (0, 0) :: (0, o') :: rs0
        end in
      Some (fs_AL [] rs0')
    | p :: ls0' => Some (fs_Halt (p :: ls0') (consume1R o rs0))
    end
  | fs_BR ls0 ((1, o) :: rs0) => Some (fs_CR ((0, sep0) :: ls0) (consume1R o rs0))
  | fs_BR ls0 ((2, o) :: rs0) => Some (fs_ER (push100L ls0) (consume1R o rs0))
  | fs_BR ls0 ((S (S (S z)), o) :: rs0) =>
    Some (fs_DL ls0 (push1R (push1R (push1R ((z, o) :: rs0)))))
  | fs_BR0 ls0 [] => Some (fs_DL ls0 [(0, 3)])
  | fs_BR0 ls0 ((0, o) :: rs0) =>
    let rs0' :=
      match o with
      | 0 => push1R (push0R (push0R rs0))
      | S o' => (0, 0) :: (0, o') :: rs0
      end in
    Some (fs_AL ls0 rs0')
  | fs_BR0 ls0 ((1, o) :: rs0) => Some (fs_CR (push100L ls0) (consume1R o rs0))
  | fs_BR0 ls0 ((2, o) :: rs0) => Some (fs_ER (push1000L ls0) (consume1R o rs0))
  | fs_BR0 ls0 ((S (S (S z)), o) :: rs0) =>
    Some (fs_DL ls0 (push1R (push1R (push1R (push1R ((z, o) :: rs0))))))
  | fs_CR ls0 [] => Some (fs_DL ls0 [(0, 1)])
  | fs_CR ls0 ((0, o) :: rs0) => Some (fs_CR (bumpL ls0) (consume1R o rs0))
  | fs_CR ls0 ((1, o) :: rs0) => Some (fs_ER ((0, sep0) :: ls0) (consume1R o rs0))
  | fs_CR ls0 ((S (S z), o) :: rs0) =>
    Some (fs_DL ls0 (push1R (push1R ((z, o) :: rs0))))
  | fs_DL [] rs0 => Some (fs_DL [] (push1R rs0))
  | fs_DL (p :: ls0) rs0 => Some (fs_ER (p :: ls0) rs0)
  | fs_ER ls0 [] => Some (fs_AL ls0 [(0, 0)])
  | fs_ER ls0 ((0, 0) :: rs0) => Some (fs_Halt (bumpL ls0) rs0)
  | fs_ER ls0 ((0, S o) :: rs0) => Some (fs_BR0 (bumpL ls0) (consume1R o rs0))
  | fs_ER ls0 ((S z, o) :: rs0) => Some (fs_AL ls0 (push1R ((z, o) :: rs0)))
  end.

Fixpoint iterStepFlat (n : nat) (fs : FlatState) : option FlatState :=
  match n with
  | 0 => Some fs
  | S n' =>
    match stepFlat fs with
    | None => None
    | Some fs' => iterStepFlat n' fs'
    end
  end.

Lemma cons_one_encLeft : forall ls0,
  (S1 >> encLeft ls0) = encLeft (bumpL ls0).
Proof.
  intros [| [[| d] b] ls0]; cbn.
  - f_equal. apply const_unfold.
  - destruct b; reflexivity.
  - reflexivity.
Qed.

Lemma cons_10_encLeft : forall ls0,
  (S1 >> S0 >> encLeft ls0) = encLeft ((0, sep0) :: ls0).
Proof. reflexivity. Qed.

Lemma cons_100_encLeft : forall ls0,
  (S1 >> S0 >> S0 >> encLeft ls0) = encLeft (push100L ls0).
Proof.
  intros [| p ls0]; cbn.
  - do 2 f_equal. symmetry. apply const_unfold.
  - reflexivity.
Qed.

Lemma cons_1000_encLeft : forall ls0,
  (S1 >> S0 >> S0 >> S0 >> encLeft ls0) = encLeft (push1000L ls0).
Proof.
  intros [| p ls0]; cbn.
  - do 2 f_equal. rewrite <- const_unfold, <- const_unfold. reflexivity.
  - reflexivity.
Qed.

Lemma cons_zero_encRight : forall rs0,
  (S0 >> encRight rs0) = encRight (push0R rs0).
Proof.
  intros [| [z o] rs0]; cbn.
  - symmetry. apply const_unfold.
  - reflexivity.
Qed.

Lemma cons_one_encRight : forall rs0,
  (S1 >> encRight rs0) = encRight (push1R rs0).
Proof.
  intros [| [[| z] o] rs0]; cbn.
  - f_equal. apply const_unfold.
  - reflexivity.
  - reflexivity.
Qed.

Ltac step_loop n :=
  lazymatch n with
  | O => fail "step_loop: out of fuel"
  | S ?m =>
    first
    [ eapply progress_one; [raw_step | cbn [move_left move_right hd tl const];
        repeat rewrite <- const_unfold; reflexivity]
    | eapply progress_cons; [raw_step | cbn [move_left move_right hd tl const]; step_loop m] ]
  end.

Ltac run_raw_plus :=
  try unfold encodeFlat; try unfold headLeftCfg; try unfold headRightCfg;
  try unfold c0; try unfold tape0; try unfold q0; try unfold s0;
  cbn [encLeft encRight];
  try unfold lWord; try unfold rWord;
  cbn [lWordAux rWordAux oWord Str_app hd tl const move_left move_right];
  step_loop 8.

Lemma step_Init : encodeFlat fs_Init -[ tm ]->+ encodeFlat (fs_BR [(0, sep0)] []).
Proof. run_raw_plus. Qed.

Lemma step_AL_nil : forall rs0,
  encodeFlat (fs_AL [] rs0) -[ tm ]->+ encodeFlat (fs_BR [(0, sep0)] rs0).
Proof. intros rs0. run_raw_plus. Qed.

Lemma step_AL_0_s0 : forall ls0 rs0,
  encodeFlat (fs_AL ((0, sep0) :: ls0) rs0) -[ tm ]->+ encodeFlat (fs_BR (bumpL ls0) (push0R rs0)).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_one_encLeft, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_AL_0_s1 : forall ls0 rs0,
  encodeFlat (fs_AL ((0, sep1) :: ls0) rs0) -[ tm ]->+ encodeFlat (fs_BR ((0, sep0) :: ls0) (push0R rs0)).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_10_encLeft, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_AL_0_s2 : forall ls0 rs0,
  encodeFlat (fs_AL ((0, sep2) :: ls0) rs0) -[ tm ]->+ encodeFlat (fs_BR (push100L ls0) (push0R rs0)).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_100_encLeft, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_AL_succ : forall d b ls0 rs0,
  encodeFlat (fs_AL ((S d, b) :: ls0) rs0) -[ tm ]-> encodeFlat (fs_AL ((d, b) :: ls0) (push0R rs0)).
Proof.
  intros d b ls0 rs0. destruct b; unfold encodeFlat; rewrite <- cons_zero_encRight;
    unfold headLeftCfg; cbn [encLeft]; unfold lWord; cbn [lWordAux Str_app hd tl]; raw_step.
Qed.

Lemma phase_mAL_drain : forall d b ls0 rs0,
  encodeFlat (fs_AL ((d, b) :: ls0) rs0) -[ tm ]->* encodeFlat (fs_AL ((0, b) :: ls0) (push0RN d rs0)).
Proof.
  induction d as [| d IH]; intros b ls0 rs0.
  - apply evstep_refl.
  - cbn [push0RN]. eapply evstep_step.
    + apply step_AL_succ.
    + apply IH.
Qed.

Lemma push0RN_push0R : forall d rs0,
  push0RN d (push0R rs0) = push0R (push0RN d rs0).
Proof.
  induction d as [| d IH]; intros rs0; [reflexivity | exact (IH (push0R rs0))].
Qed.

Lemma step_BR_nil : forall ls0,
  encodeFlat (fs_BR ls0 []) -[ tm ]->+ encodeFlat (fs_DL ls0 [(0, 2)]).
Proof. intros ls0. run_raw_plus. Qed.

Lemma step_BR_nil_0_0 : forall rs0,
  encodeFlat (fs_BR [] ((0, 0) :: rs0)) -[ tm ]->+
  encodeFlat (fs_AL [] (push1R (push0R (push0R rs0)))).
Proof.
  intros rs0. unfold encodeFlat.
  rewrite <- cons_one_encRight, <- cons_zero_encRight, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_BR_nil_0_succ : forall o rs0,
  encodeFlat (fs_BR [] ((0, S o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_AL [] ((0, 0) :: (0, o) :: rs0)).
Proof. intros o rs0. run_raw_plus. Qed.

Lemma step_BR_halt_0 : forall p ls0 rs0,
  encodeFlat (fs_BR (p :: ls0) ((0, 0) :: rs0)) -[ tm ]->+
  encodeFlat (fs_Halt (p :: ls0) (push0R rs0)).
Proof.
  intros [[| d] [| |]] ls0 rs0; unfold encodeFlat; rewrite <- cons_zero_encRight; run_raw_plus.
Qed.

Lemma step_BR_halt_succ : forall p ls0 o rs0,
  encodeFlat (fs_BR (p :: ls0) ((0, S o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_Halt (p :: ls0) ((0, o) :: rs0)).
Proof.
  intros [[| d] [| |]] ls0 o rs0; run_raw_plus.
Qed.

Lemma step_BR_1_0 : forall ls0 rs0,
  encodeFlat (fs_BR ls0 ((1, 0) :: rs0)) -[ tm ]->+
  encodeFlat (fs_CR ((0, sep0) :: ls0) (push0R rs0)).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_10_encLeft, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_BR_1_succ : forall ls0 o rs0,
  encodeFlat (fs_BR ls0 ((1, S o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_CR ((0, sep0) :: ls0) ((0, o) :: rs0)).
Proof.
  intros ls0 o rs0. unfold encodeFlat. rewrite <- cons_10_encLeft. run_raw_plus.
Qed.

Lemma step_BR_2_0 : forall ls0 rs0,
  encodeFlat (fs_BR ls0 ((2, 0) :: rs0)) -[ tm ]->+
  encodeFlat (fs_ER (push100L ls0) (push0R rs0)).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_100_encLeft, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_BR_2_succ : forall ls0 o rs0,
  encodeFlat (fs_BR ls0 ((2, S o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_ER (push100L ls0) ((0, o) :: rs0)).
Proof.
  intros ls0 o rs0. unfold encodeFlat. rewrite <- cons_100_encLeft. run_raw_plus.
Qed.

Lemma step_BR_3_ge : forall ls0 z o rs0,
  encodeFlat (fs_BR ls0 ((S (S (S z)), o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_DL ls0 (push1R (push1R (push1R ((z, o) :: rs0))))).
Proof.
  intros ls0 z [| o'] rs0; unfold encodeFlat;
    rewrite <- cons_one_encRight, <- cons_one_encRight, <- cons_one_encRight;
    run_raw_plus.
Qed.

Lemma step_BR0_nil : forall ls0,
  encodeFlat (fs_BR0 ls0 []) -[ tm ]->+ encodeFlat (fs_DL ls0 [(0, 3)]).
Proof. intros ls0. run_raw_plus. Qed.

Lemma step_BR0_0_0 : forall ls0 rs0,
  encodeFlat (fs_BR0 ls0 ((0, 0) :: rs0)) -[ tm ]->+
  encodeFlat (fs_AL ls0 (push1R (push0R (push0R rs0)))).
Proof.
  intros ls0 rs0. unfold encodeFlat.
  rewrite <- cons_one_encRight, <- cons_zero_encRight, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_BR0_0_succ : forall ls0 o rs0,
  encodeFlat (fs_BR0 ls0 ((0, S o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_AL ls0 ((0, 0) :: (0, o) :: rs0)).
Proof. intros ls0 o rs0. run_raw_plus. Qed.

Lemma step_BR0_1_0 : forall ls0 rs0,
  encodeFlat (fs_BR0 ls0 ((1, 0) :: rs0)) -[ tm ]->+
  encodeFlat (fs_CR (push100L ls0) (push0R rs0)).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_100_encLeft, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_BR0_1_succ : forall ls0 o rs0,
  encodeFlat (fs_BR0 ls0 ((1, S o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_CR (push100L ls0) ((0, o) :: rs0)).
Proof.
  intros ls0 o rs0. unfold encodeFlat. rewrite <- cons_100_encLeft. run_raw_plus.
Qed.

Lemma step_BR0_2_0 : forall ls0 rs0,
  encodeFlat (fs_BR0 ls0 ((2, 0) :: rs0)) -[ tm ]->+
  encodeFlat (fs_ER (push1000L ls0) (push0R rs0)).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_1000_encLeft, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_BR0_2_succ : forall ls0 o rs0,
  encodeFlat (fs_BR0 ls0 ((2, S o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_ER (push1000L ls0) ((0, o) :: rs0)).
Proof.
  intros ls0 o rs0. unfold encodeFlat. rewrite <- cons_1000_encLeft. run_raw_plus.
Qed.

Lemma step_BR0_3_ge : forall ls0 z o rs0,
  encodeFlat (fs_BR0 ls0 ((S (S (S z)), o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_DL ls0 (push1R (push1R (push1R (push1R ((z, o) :: rs0)))))).
Proof.
  intros ls0 z [| o'] rs0; unfold encodeFlat;
    rewrite <- cons_one_encRight, <- cons_one_encRight, <- cons_one_encRight, <- cons_one_encRight;
    run_raw_plus.
Qed.

Lemma step_CR_nil : forall ls0,
  encodeFlat (fs_CR ls0 []) -[ tm ]->+ encodeFlat (fs_DL ls0 [(0, 1)]).
Proof. intros ls0. run_raw_plus. Qed.

Lemma step_CR_0_0 : forall ls0 rs0,
  encodeFlat (fs_CR ls0 ((0, 0) :: rs0)) -[ tm ]->+ encodeFlat (fs_CR (bumpL ls0) (push0R rs0)).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_one_encLeft, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_CR_0_succ : forall ls0 o rs0,
  encodeFlat (fs_CR ls0 ((0, S o) :: rs0)) -[ tm ]->+ encodeFlat (fs_CR (bumpL ls0) ((0, o) :: rs0)).
Proof.
  intros ls0 o rs0. unfold encodeFlat. rewrite <- cons_one_encLeft. run_raw_plus.
Qed.

Lemma step_CR_1_0 : forall ls0 rs0,
  encodeFlat (fs_CR ls0 ((1, 0) :: rs0)) -[ tm ]->+ encodeFlat (fs_ER ((0, sep0) :: ls0) (push0R rs0)).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_10_encLeft, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_CR_1_succ : forall ls0 o rs0,
  encodeFlat (fs_CR ls0 ((1, S o) :: rs0)) -[ tm ]->+ encodeFlat (fs_ER ((0, sep0) :: ls0) ((0, o) :: rs0)).
Proof.
  intros ls0 o rs0. unfold encodeFlat. rewrite <- cons_10_encLeft. run_raw_plus.
Qed.

Lemma step_CR_2_ge : forall ls0 z o rs0,
  encodeFlat (fs_CR ls0 ((S (S z), o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_DL ls0 (push1R (push1R ((z, o) :: rs0)))).
Proof.
  intros ls0 z [| o'] rs0; unfold encodeFlat;
    rewrite <- cons_one_encRight, <- cons_one_encRight; run_raw_plus.
Qed.

Lemma step_DL_nil : forall rs0,
  encodeFlat (fs_DL [] rs0) -[ tm ]->+ encodeFlat (fs_DL [] (push1R rs0)).
Proof.
  intros rs0. unfold encodeFlat. rewrite <- cons_one_encRight. run_raw_plus.
Qed.

Lemma step_DL_cons : forall p ls0 rs0,
  encodeFlat (fs_DL (p :: ls0) rs0) -[ tm ]->+ encodeFlat (fs_ER (p :: ls0) rs0).
Proof.
  intros [[| d] [| |]] ls0 rs0; run_raw_plus.
Qed.

Lemma step_ER_nil : forall ls0,
  encodeFlat (fs_ER ls0 []) -[ tm ]->+ encodeFlat (fs_AL ls0 [(0, 0)]).
Proof. intros ls0. run_raw_plus. Qed.

Lemma step_ER_halt : forall ls0 rs0,
  encodeFlat (fs_ER ls0 ((0, 0) :: rs0)) -[ tm ]->+ encodeFlat (fs_Halt (bumpL ls0) rs0).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_one_encLeft. run_raw_plus.
Qed.

Lemma step_ER_0_1 : forall ls0 rs0,
  encodeFlat (fs_ER ls0 ((0, 1) :: rs0)) -[ tm ]->+ encodeFlat (fs_BR0 (bumpL ls0) (push0R rs0)).
Proof.
  intros ls0 rs0. unfold encodeFlat. rewrite <- cons_one_encLeft, <- cons_zero_encRight.
  run_raw_plus.
Qed.

Lemma step_ER_0_succ2 : forall ls0 o rs0,
  encodeFlat (fs_ER ls0 ((0, S (S o)) :: rs0)) -[ tm ]->+ encodeFlat (fs_BR0 (bumpL ls0) ((0, o) :: rs0)).
Proof.
  intros ls0 o rs0. unfold encodeFlat. rewrite <- cons_one_encLeft. run_raw_plus.
Qed.

Lemma step_ER_zs : forall ls0 z o rs0,
  encodeFlat (fs_ER ls0 ((S z, o) :: rs0)) -[ tm ]->+
  encodeFlat (fs_AL ls0 (push1R ((z, o) :: rs0))).
Proof.
  intros ls0 z [| o'] rs0; unfold encodeFlat; rewrite <- cons_one_encRight; run_raw_plus.
Qed.

Lemma stepFlat_some : forall fs fs',
  stepFlat fs = Some fs' -> encodeFlat fs -[ tm ]->+ encodeFlat fs'.
Proof.
  intros fs fs' H.
  destruct fs as [| ls0 rs0 | ls0 rs0 | ls0 rs0 | ls0 rs0 | ls0 rs0 | ls0 rs0 | ls0 rs0].
  - injection H as <-. apply step_Init.
  - discriminate H.
  - destruct ls0 as [| [d [| |]] ls0]; injection H as <-.
    + apply step_AL_nil.
    + rewrite push0RN_push0R. eapply evstep_progress_trans; [apply phase_mAL_drain | apply step_AL_0_s0].
    + rewrite push0RN_push0R. eapply evstep_progress_trans; [apply phase_mAL_drain | apply step_AL_0_s1].
    + rewrite push0RN_push0R. eapply evstep_progress_trans; [apply phase_mAL_drain | apply step_AL_0_s2].
  - destruct rs0 as [| [[| [| [| z]]] [| o]] rs0].
    + destruct ls0 as [| p ls0]; injection H as <-; apply step_BR_nil.
    + destruct ls0 as [| p ls0]; injection H as <-; [apply step_BR_nil_0_0 | apply step_BR_halt_0].
    + destruct ls0 as [| p ls0]; injection H as <-; [apply step_BR_nil_0_succ | apply step_BR_halt_succ].
    + injection H as <-. apply step_BR_1_0.
    + injection H as <-. apply step_BR_1_succ.
    + injection H as <-. apply step_BR_2_0.
    + injection H as <-. apply step_BR_2_succ.
    + injection H as <-. apply step_BR_3_ge.
    + injection H as <-. apply step_BR_3_ge.
  - destruct rs0 as [| [[| [| [| z]]] [| o]] rs0]; injection H as <-.
    + apply step_BR0_nil.
    + apply step_BR0_0_0.
    + apply step_BR0_0_succ.
    + apply step_BR0_1_0.
    + apply step_BR0_1_succ.
    + apply step_BR0_2_0.
    + apply step_BR0_2_succ.
    + apply step_BR0_3_ge.
    + apply step_BR0_3_ge.
  - destruct rs0 as [| [[| [| z]] [| o]] rs0]; injection H as <-.
    + apply step_CR_nil.
    + apply step_CR_0_0.
    + apply step_CR_0_succ.
    + apply step_CR_1_0.
    + apply step_CR_1_succ.
    + apply step_CR_2_ge.
    + apply step_CR_2_ge.
  - destruct ls0 as [| p ls0]; injection H as <-; [apply step_DL_nil | apply step_DL_cons].
  - destruct rs0 as [| [[| z] [| [| o]]] rs0]; injection H as <-.
    + apply step_ER_nil.
    + apply step_ER_halt.
    + apply step_ER_0_1.
    + apply step_ER_0_succ2.
    + apply step_ER_zs.
    + apply step_ER_zs.
    + apply step_ER_zs.
Qed.

Lemma iterStepFlat_star : forall n fs fs',
  iterStepFlat n fs = Some fs' -> encodeFlat fs -[ tm ]->* encodeFlat fs'.
Proof.
  induction n as [| n IH]; intros fs fs' H; cbn [iterStepFlat] in H.
  - injection H as <-. apply evstep_refl.
  - destruct (stepFlat fs) as [fs1 |] eqn:Hs; [| discriminate H].
    eapply evstep_trans; [apply progress_evstep, stepFlat_some, Hs | exact (IH _ _ H)].
Qed.

Lemma iterStepFlat_plus : forall n fs fs',
  iterStepFlat (S n) fs = Some fs' -> encodeFlat fs -[ tm ]->+ encodeFlat fs'.
Proof.
  intros n fs fs' H. cbn [iterStepFlat] in H.
  destruct (stepFlat fs) as [fs1 |] eqn:Hs; [| discriminate H].
  eapply progress_evstep_trans; [apply stepFlat_some, Hs | exact (iterStepFlat_star n fs1 fs' H)].
Qed.

(* ========================================================================= *)
(* 3. Binary-N Run Repetition & RLE Stack Operations                         *)
(* ========================================================================= *)

Lemma Pos_iter_swap : forall { X : Type } (f : X -> X) (p : positive) (x : X),
  Pos.iter f (f x) p = f (Pos.iter f x p).
Proof.
  intros X f p. induction p as [p IHp | p IHp |]; intros x; cbn [Pos.iter].
  - rewrite IHp, IHp. reflexivity.
  - rewrite IHp, IHp. reflexivity.
  - reflexivity.
Qed.

Lemma Pos_iter_succ : forall { X : Type } (f : X -> X) (p : positive) (x : X),
  Pos.iter f x (Pos.succ p) = f (Pos.iter f x p).
Proof.
  intros X f p. induction p as [p IHp | p IHp |]; intros x; cbn [Pos.succ Pos.iter].
  - rewrite !IHp, Pos_iter_swap. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma N_iter_succ : forall { X : Type } (f : X -> X) (n : N) (x : X),
  N.iter (N.succ n) f x = f (N.iter n f x).
Proof.
  intros X f [| p] x; [reflexivity | exact (Pos_iter_succ f p x)].
Qed.

Lemma N_iter_swap : forall { X : Type } (f : X -> X) (n : N) (x : X),
  N.iter n f (f x) = f (N.iter n f x).
Proof.
  intros X f [| p] x; [reflexivity | exact (Pos_iter_swap f p x)].
Qed.

Lemma N_iter_add : forall { X : Type } (f : X -> X) (m n : N) (x : X),
  N.iter (m + n)%N f x = N.iter m f (N.iter n f x).
Proof.
  intros X f m. pattern m. apply N.peano_ind.
  - intros n x. reflexivity.
  - intros m' IH n x. replace (N.succ m' + n)%N with (N.succ (m' + n))%N by lia.
    rewrite !N_iter_succ, IH. reflexivity.
Qed.

Definition prependRepL (n : N) (xs : list (nat * Sep3)) : list (nat * Sep3) :=
  N.iter n (cons (1, sep0)) xs.

Definition prependRepR (n : N) (xs : list (nat * nat)) : list (nat * nat) :=
  N.iter n (cons (1, 0)) xs.

Arguments prependRepL : simpl never.
Arguments prependRepR : simpl never.

Lemma prependRepL_0 : forall xs, prependRepL 0%N xs = xs.
Proof. reflexivity. Qed.

Lemma prependRepL_1 : forall xs, prependRepL 1%N xs = (1, sep0) :: xs.
Proof. reflexivity. Qed.

Lemma prependRepL_01 : forall xs, prependRepL (0 + 1)%N xs = (1, sep0) :: xs.
Proof. reflexivity. Qed.

Lemma prependRepL_2 : forall xs, prependRepL 2%N xs = (1, sep0) :: (1, sep0) :: xs.
Proof. reflexivity. Qed.

Lemma prependRepL_succ : forall n xs,
  prependRepL (N.succ n) xs = (1, sep0) :: prependRepL n xs.
Proof. intros n xs. unfold prependRepL. apply N_iter_succ. Qed.

Lemma prependRepL_add1 : forall n xs,
  prependRepL (n + 1)%N xs = (1, sep0) :: prependRepL n xs.
Proof.
  intros n xs. replace (n + 1)%N with (N.succ n) by lia. apply prependRepL_succ.
Qed.

Lemma prependRepL_cons : forall n xs,
  prependRepL n ((1, sep0) :: xs) = (1, sep0) :: prependRepL n xs.
Proof. intros n xs. unfold prependRepL. apply N_iter_swap. Qed.

Lemma prependRepL_add : forall m n xs,
  prependRepL (m + n)%N xs = prependRepL m (prependRepL n xs).
Proof. intros m n xs. unfold prependRepL. apply N_iter_add. Qed.

Lemma prependRepL_append_eq : forall n xs ys,
  prependRepL n xs ++ ys = prependRepL n (xs ++ ys).
Proof.
  intros n. pattern n. apply N.peano_ind.
  - intros xs ys. reflexivity.
  - intros n' IH xs ys. rewrite !prependRepL_succ. cbn [app]. rewrite IH. reflexivity.
Qed.

Lemma prependRepR_0 : forall xs, prependRepR 0%N xs = xs.
Proof. reflexivity. Qed.

Lemma prependRepR_1 : forall xs, prependRepR 1%N xs = (1, 0) :: xs.
Proof. reflexivity. Qed.

Lemma prependRepR_01 : forall xs, prependRepR (0 + 1)%N xs = (1, 0) :: xs.
Proof. reflexivity. Qed.

Lemma prependRepR_2 : forall xs, prependRepR 2%N xs = (1, 0) :: (1, 0) :: xs.
Proof. reflexivity. Qed.

Lemma prependRepR_succ : forall n xs,
  prependRepR (N.succ n) xs = (1, 0) :: prependRepR n xs.
Proof. intros n xs. unfold prependRepR. apply N_iter_succ. Qed.

Lemma prependRepR_add1 : forall n xs,
  prependRepR (n + 1)%N xs = (1, 0) :: prependRepR n xs.
Proof.
  intros n xs. replace (n + 1)%N with (N.succ n) by lia. apply prependRepR_succ.
Qed.

Lemma prependRepR_cons : forall n xs,
  prependRepR n ((1, 0) :: xs) = (1, 0) :: prependRepR n xs.
Proof. intros n xs. unfold prependRepR. apply N_iter_swap. Qed.

Lemma prependRepR_add : forall m n xs,
  prependRepR (m + n)%N xs = prependRepR m (prependRepR n xs).
Proof. intros m n xs. unfold prependRepR. apply N_iter_add. Qed.

Lemma prependRepR_append_eq : forall n xs ys,
  prependRepR n xs ++ ys = prependRepR n (xs ++ ys).
Proof.
  intros n. pattern n. apply N.peano_ind.
  - intros xs ys. reflexivity.
  - intros n' IH xs ys. rewrite !prependRepR_succ. cbn [app]. rewrite IH. reflexivity.
Qed.

Fixpoint expandL (ls : list ElemL) : list (nat * Sep3) :=
  match ls with
  | [] => []
  | el_single d b :: rest => (d, b) :: expandL rest
  | el_run10 k :: rest => prependRepL (k + 1)%N (expandL rest)
  end.

Fixpoint expandR (rs : list ElemR) : list (nat * nat) :=
  match rs with
  | [] => []
  | er_single z o :: rest => (z, o) :: expandR rest
  | er_run10 k :: rest => prependRepR (k + 1)%N (expandR rest)
  end.

Definition toFlat (bs : BaseState) : FlatState :=
  match bs with
  | bs_Init => fs_Init
  | bs_Halt ls rs => fs_Halt (expandL ls) (expandR rs)
  | bs_AL ls rs => fs_AL (expandL ls) (expandR rs)
  | bs_BR ls rs => fs_BR (expandL ls) (expandR rs)
  | bs_BR0 ls rs => fs_BR0 (expandL ls) (expandR rs)
  | bs_CR ls rs => fs_CR (expandL ls) (expandR rs)
  | bs_DL ls rs => fs_DL (expandL ls) (expandR rs)
  | bs_ER ls rs => fs_ER (expandL ls) (expandR rs)
  end.

Definition push10L (n : N) (ls : list ElemL) : list ElemL :=
  match n with
  | N0 => ls
  | Npos p =>
    match ls with
    | [] => [el_run10 (N.pred (Npos p))]
    | el_run10 k2 :: rest => el_run10 (Npos p + k2)%N :: rest
    | e :: rest => el_run10 (N.pred (Npos p)) :: e :: rest
    end
  end.

Definition pushSL (d : nat) (b : Sep3) (ls : list ElemL) : list ElemL :=
  match d, b with
  | 1, sep0 => push10L 1%N ls
  | _, _ => el_single d b :: ls
  end.

Definition peel10L (k : N) (ls : list ElemL) : list ElemL :=
  match k with
  | N0 => ls
  | Npos p => el_run10 (N.pred (Npos p)) :: ls
  end.

Definition pop1L (ls : list ElemL) : option ((nat * Sep3) * list ElemL) :=
  match ls with
  | [] => None
  | el_single d b :: rest => Some ((d, b), rest)
  | el_run10 k :: rest => Some ((1, sep0), peel10L k rest)
  end.

Definition push10R (n : N) (rs : list ElemR) : list ElemR :=
  match n with
  | N0 => rs
  | Npos p =>
    match rs with
    | [] => [er_run10 (N.pred (Npos p))]
    | er_run10 k2 :: rest => er_run10 (Npos p + k2)%N :: rest
    | e :: rest => er_run10 (N.pred (Npos p)) :: e :: rest
    end
  end.

Definition pushSR (z o : nat) (rs : list ElemR) : list ElemR :=
  match z, o with
  | 1, 0 => push10R 1%N rs
  | _, _ => er_single z o :: rs
  end.

Definition peel10R (k : N) (rs : list ElemR) : list ElemR :=
  match k with
  | N0 => rs
  | Npos p => er_run10 (N.pred (Npos p)) :: rs
  end.

Definition pop1R (rs : list ElemR) : option ((nat * nat) * list ElemR) :=
  match rs with
  | [] => None
  | er_single z o :: rest => Some ((z, o), rest)
  | er_run10 k :: rest => Some ((1, 0), peel10R k rest)
  end.

Definition bumpLElem (ls : list ElemL) : list ElemL :=
  match pop1L ls with
  | None => [el_single 0 sep0]
  | Some ((d, b), rest) => pushSL (S d) b rest
  end.

Definition push100LElem (ls : list ElemL) : list ElemL :=
  match ls with
  | [] => [el_single 0 sep0]
  | e :: rest => el_single 0 sep1 :: e :: rest
  end.

Definition push1000LElem (ls : list ElemL) : list ElemL :=
  match ls with
  | [] => [el_single 0 sep0]
  | e :: rest => el_single 0 sep2 :: e :: rest
  end.

Definition push0RElem (rs : list ElemR) : list ElemR :=
  match pop1R rs with
  | None => []
  | Some ((z, o), rest) => pushSR (S z) o rest
  end.

Definition push0RNElem (d : nat) (rs : list ElemR) : list ElemR :=
  match d with
  | 0 => rs
  | S nm =>
    match pop1R rs with
    | None => []
    | Some ((z, o), rest) => pushSR (z + S nm) o rest
    end
  end.

Definition push1RElem (rs : list ElemR) : list ElemR :=
  match pop1R rs with
  | None => [er_single 0 0]
  | Some ((0, o), rest) => er_single 0 (S o) :: rest
  | Some ((S zm, o), rest) => er_single 0 0 :: pushSR zm o rest
  end.

Definition consume1RElem (o : nat) (rs : list ElemR) : list ElemR :=
  match o with
  | 0 => push0RElem rs
  | S o' => er_single 0 o' :: rs
  end.

Definition step1Elem (bs : BaseState) : option BaseState :=
  match bs with
  | bs_Halt _ _ => None
  | bs_Init => Some (bs_BR [el_single 0 sep0] [])
  | bs_AL ls rs =>
    match pop1L ls with
    | None => Some (bs_BR [el_single 0 sep0] rs)
    | Some ((d, b), ls') =>
      let rs' := push0RNElem d (push0RElem rs) in
      let ls'' :=
        match b with
        | sep0 => bumpLElem ls'
        | sep1 => el_single 0 sep0 :: ls'
        | sep2 => push100LElem ls'
        end in
      Some (bs_BR ls'' rs')
    end
  | bs_BR ls rs =>
    match pop1R rs with
    | None => Some (bs_DL ls [er_single 0 2])
    | Some ((0, o), rs') =>
      match ls with
      | [] =>
        let rs'' :=
          match o with
          | 0 => push1RElem (push0RElem (push0RElem rs'))
          | S o' => er_single 0 0 :: er_single 0 o' :: rs'
          end in
        Some (bs_AL [] rs'')
      | e :: ls' => Some (bs_Halt (e :: ls') (consume1RElem o rs'))
      end
    | Some ((1, o), rs') => Some (bs_CR (el_single 0 sep0 :: ls) (consume1RElem o rs'))
    | Some ((2, o), rs') => Some (bs_ER (push100LElem ls) (consume1RElem o rs'))
    | Some ((S (S (S z)), o), rs') =>
      Some (bs_DL ls (push1RElem (push1RElem (push1RElem (pushSR z o rs')))))
    end
  | bs_BR0 ls rs =>
    match pop1R rs with
    | None => Some (bs_DL ls [er_single 0 3])
    | Some ((0, o), rs') =>
      let rs'' :=
        match o with
        | 0 => push1RElem (push0RElem (push0RElem rs'))
        | S o' => er_single 0 0 :: er_single 0 o' :: rs'
        end in
      Some (bs_AL ls rs'')
    | Some ((1, o), rs') => Some (bs_CR (push100LElem ls) (consume1RElem o rs'))
    | Some ((2, o), rs') => Some (bs_ER (push1000LElem ls) (consume1RElem o rs'))
    | Some ((S (S (S z)), o), rs') =>
      Some (bs_DL ls (push1RElem (push1RElem (push1RElem (push1RElem (pushSR z o rs'))))))
    end
  | bs_CR ls rs =>
    match pop1R rs with
    | None => Some (bs_DL ls [er_single 0 1])
    | Some ((0, o), rs') => Some (bs_CR (bumpLElem ls) (consume1RElem o rs'))
    | Some ((1, o), rs') => Some (bs_ER (el_single 0 sep0 :: ls) (consume1RElem o rs'))
    | Some ((S (S z), o), rs') =>
      Some (bs_DL ls (push1RElem (push1RElem (pushSR z o rs'))))
    end
  | bs_DL ls rs =>
    match ls with
    | [] => Some (bs_DL [] (push1RElem rs))
    | e :: ls' => Some (bs_ER (e :: ls') rs)
    end
  | bs_ER ls rs =>
    match pop1R rs with
    | None => Some (bs_AL ls [er_single 0 0])
    | Some ((0, 0), rs') => Some (bs_Halt (bumpLElem ls) rs')
    | Some ((0, S o), rs') => Some (bs_BR0 (bumpLElem ls) (consume1RElem o rs'))
    | Some ((S z, o), rs') => Some (bs_AL ls (push1RElem (pushSR z o rs')))
    end
  end.

Definition tryBR0 (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match ls, rs with
  | el_single 3 sep0 :: el_run10 k :: ls', er_single 0 0 :: er_single 0 0 :: rs' =>
    Some (bs_BR0 (el_single 3 sep0 :: ls') (er_single 0 0 :: er_single 0 0 :: push10R (k + 1)%N rs'))
  | el_single 3 sep0 :: [], er_single 0 0 :: er_single 0 0 :: rs' =>
    Some (bs_BR0 (bumpLElem (bumpLElem [])) (er_single 0 0 :: er_single 0 0 :: push10R 1%N rs'))
  | el_single 3 sep0 :: el_single d b :: ls', er_single 0 0 :: er_single 0 0 :: rs' =>
    Some (bs_BR0 (bumpLElem (bumpLElem (el_single d b :: ls')))
      (er_single 0 0 :: er_single 0 0 :: push10R 1%N rs'))
  | el_single 2 sep0 :: ls', er_single 0 0 :: er_single 0 0 :: rs' =>
    Some (bs_AL (bumpLElem (bumpLElem ls')) (er_single 0 0 :: er_single 0 0 :: push10R 1%N rs'))
  | el_single 4 sep0 :: ls', er_single 0 0 :: er_single 0 0 :: rs' =>
    Some (bs_AL (bumpLElem (bumpLElem ls')) (er_single 0 0 :: er_single 2 0 :: push10R 1%N rs'))
  | el_run10 k :: ls', er_single 0 0 :: er_single 0 0 :: rs' =>
    Some (bs_BR (el_single 0 sep0 :: bumpLElem (peel10L k ls')) (er_run10 0%N :: er_single 0 0 :: rs'))
  | _, _ => None
  end.

Definition tryALBot2 (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match ls with
  | [el_single 4 sep0; el_single 0 sep0; el_single 3 sep0; el_single 0 sep0; el_single 0 sep0] =>
    Some (bs_BR [el_single 0 sep0; el_single 2 sep1; el_run10 0%N; el_single 2 sep0;
      el_single 0 sep0; el_single 0 sep0] (er_run10 0%N :: er_single 0 0 :: rs))
  | [el_single 4 sep1; el_run10 0%N; el_single 2 sep0; el_single 0 sep0; el_single 0 sep0] =>
    Some (bs_BR [el_single 0 sep0; el_run10 0%N; el_single 2 sep0; el_single 2 sep0;
      el_single 0 sep0; el_single 0 sep0] (er_run10 0%N :: er_single 0 0 :: rs))
  | [el_single 3 sep0; el_single 2 sep0; el_single 2 sep0; el_single 0 sep0; el_single 0 sep0] =>
    Some (bs_BR [el_single 0 sep0; el_single 0 sep0; el_run10 0%N; el_single 0 sep0;
      el_single 3 sep0; el_single 0 sep0; el_single 0 sep0] (er_run10 0%N :: er_single 0 0 :: rs))
  | [el_run10 0%N] =>
    Some (bs_CR [el_single 0 sep0; el_single 0 sep0; el_single 0 sep0] (er_single 0 0 :: rs))
  | _ => None
  end.

Definition tryALBot1 (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match ls with
  | [el_single 3 sep1; el_run10 0%N; el_single 0 sep0; el_single 3 sep0; el_single 0 sep0; el_single 0 sep0] =>
    Some (bs_BR [el_single 0 sep0; el_single 2 sep0; el_single 0 sep0; el_single 3 sep0;
      el_single 0 sep0; el_single 0 sep0] (er_run10 0%N :: er_single 0 0 :: rs))
  | [el_single 3 sep0; el_single 0 sep0; el_single 3 sep0; el_single 0 sep0; el_single 0 sep0] =>
    Some (bs_BR [el_single 1 sep1; el_run10 0%N; el_single 2 sep0; el_single 0 sep0; el_single 0 sep0]
      (er_run10 0%N :: er_single 0 0 :: rs))
  | [el_single 3 sep0; el_single 1 sep1; el_run10 0%N; el_single 2 sep0; el_single 0 sep0; el_single 0 sep0] =>
    Some (bs_BR [el_run10 0%N; el_single 0 sep0; el_single 2 sep0; el_single 2 sep0;
      el_single 0 sep0; el_single 0 sep0] (er_run10 0%N :: er_single 0 0 :: rs))
  | [el_single 3 sep1; el_run10 0%N; el_single 2 sep0; el_single 0 sep0; el_single 0 sep0] =>
    Some (bs_BR [el_single 0 sep0; el_single 2 sep0; el_single 2 sep0; el_single 0 sep0; el_single 0 sep0]
      (er_run10 0%N :: er_single 0 0 :: rs))
  | [el_single 3 sep0; el_single 0 sep0; el_single 2 sep0; el_single 2 sep0; el_single 0 sep0; el_single 0 sep0] =>
    Some (bs_BR [el_single 1 sep1; el_run10 0%N; el_single 0 sep0; el_single 3 sep0;
      el_single 0 sep0; el_single 0 sep0] (er_run10 0%N :: er_single 0 0 :: rs))
  | _ => None
  end.

Definition tryALGen (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match ls, rs with
  | el_single 3 sep0 :: ls', er_single 0 0 :: rs' =>
    Some (bs_BR0 (bumpLElem (bumpLElem ls')) (er_single 0 0 :: er_single 0 0 :: rs'))
  | el_single 2 sep0 :: ls', er_single 0 0 :: rs' =>
    Some (bs_AL (bumpLElem (bumpLElem ls')) (er_single 0 0 :: er_single 0 0 :: rs'))
  | el_single 4 sep0 :: ls', er_single 0 0 :: er_single 0 0 :: rs' =>
    Some (bs_AL (bumpLElem (bumpLElem ls')) (er_single 0 0 :: er_single 2 0 :: er_single 0 0 :: rs'))
  | el_single 0 sep1 :: ls', er_single 0 0 :: er_run10 (Npos p) :: rs' =>
    Some (bs_AL (el_single 0 sep1 :: push10L (Npos p) ls') (er_single 0 0 :: push10R 1%N rs'))
  | _, _ => None
  end.

Definition tryAL (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match rs with
  | er_single 0 0 :: er_single 0 0 :: rs' =>
    match tryALBot2 ls rs' with
    | Some res => Some res
    | None =>
      match tryALBot1 ls (er_single 0 0 :: rs') with
      | Some res => Some res
      | None => tryALGen ls (er_single 0 0 :: er_single 0 0 :: rs')
      end
    end
  | er_single 0 0 :: rs' =>
    match tryALBot1 ls rs' with
    | Some res => Some res
    | None => tryALGen ls (er_single 0 0 :: rs')
    end
  | _ => None
  end.

Definition tryBR (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match rs with
  | er_run10 N0 :: er_single 0 0 :: er_run10 k :: rs' =>
    Some (bs_BR (push10L (k + 1)%N ls) (er_run10 N0 :: er_single 0 0 :: rs'))
  | er_run10 N0 :: er_single 0 0 :: er_single 2 0 :: rs' =>
    Some (bs_BR0 (push10L 2%N ls) (er_single 0 0 :: rs'))
  | _ => None
  end.

Definition tryCR (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match ls, rs with
  | el_single 0 sep0 :: ls', er_single 2 0 :: rs' =>
    Some (bs_BR0 (push10L 1%N ls') (er_single 0 0 :: rs'))
  | _, _ => None
  end.

Definition outPassStep (ls : list ElemL) (rs : list ElemR) : option (list ElemL * list ElemR) :=
  match ls with
  | el_run10 k :: ls' =>
    Some (ls', push10R (k + 1)%N rs)
  | el_single 0 sep0 :: el_single 2 sep0 :: el_run10 (Npos p) :: ls' =>
    Some (ls', push10R (N.pred (Npos p)) (er_single 2 0 :: er_single 0 0 :: push10R 2%N rs))
  | el_single 0 sep0 :: el_run10 (Npos p) :: ls' =>
    Some (ls', push10R (N.pred (Npos p)) (er_single 0 0 :: push10R 2%N rs))
  | el_single 2 sep0 :: el_run10 (Npos p) :: ls' =>
    Some (ls', push10R (N.pred (Npos p)) (er_single 2 0 :: push10R 2%N rs))
  | el_single 0 sep0 :: el_single 2 sep0 :: el_single 0 sep0 :: el_run10 (Npos p) :: ls' =>
    Some (ls', push10R (N.pred (Npos p)) (er_single 0 0 :: er_single 2 0 :: er_single 0 0 :: push10R 2%N rs))
  | el_single 2 sep0 :: el_single 0 sep0 :: el_run10 (Npos p) :: ls' =>
    Some (ls', push10R (N.pred (Npos p)) (er_single 0 0 :: er_single 2 0 :: push10R 2%N rs))
  | el_single 0 sep0 :: el_run10 N0 :: el_single 2 sep0 :: el_run10 (Npos p) :: ls' =>
    Some (ls', push10R (N.pred (Npos p)) (er_single 2 0 :: er_run10 N0 :: er_single 0 0 :: push10R 2%N rs))
  | el_single 0 sep0 :: el_single 2 sep0 :: el_single 0 sep0 :: el_run10 N0 :: el_single 2 sep0 ::
      el_run10 (Npos p) :: ls' =>
    Some (ls', push10R (N.pred (Npos p))
      (er_single 2 0 :: er_run10 N0 :: er_single 0 0 :: er_single 2 0 :: er_single 0 0 :: push10R 2%N rs))
  | el_single 0 sep0 :: el_single 2 sep0 :: el_run10 N0 :: el_single 0 sep0 :: el_single 2 sep0 ::
      el_run10 (Npos p) :: ls' =>
    Some (ls', push10R (N.pred (Npos p))
      (er_single 2 0 :: er_single 0 0 :: er_run10 N0 :: er_single 2 0 :: er_single 0 0 :: push10R 2%N rs))
  | el_single 0 sep0 :: el_single 2 sep0 :: el_single 0 sep0 :: el_single 2 sep0 ::
      el_run10 (Npos p) :: ls' =>
    Some (ls', push10R (N.pred (Npos p))
      (er_single 2 0 :: er_single 0 0 :: er_single 2 0 :: er_single 0 0 :: push10R 2%N rs))
  | _ => None
  end.

Fixpoint outPassAux (cnt : nat) (ls : list ElemL) (rs : list ElemR) (moved : bool)
    : BaseState * bool :=
  match cnt with
  | 0 => (bs_BR0 (el_single 3 sep0 :: ls) (er_single 0 0 :: er_single 0 0 :: rs), moved)
  | S cnt' =>
    match outPassStep ls rs with
    | None => (bs_BR0 (el_single 3 sep0 :: ls) (er_single 0 0 :: er_single 0 0 :: rs), moved)
    | Some (ls', rs') => outPassAux cnt' ls' rs' true
    end
  end.

Definition outPass (ls : list ElemL) (rs : list ElemR) (moved : bool) : BaseState * bool :=
  outPassAux 128 ls rs moved.

Definition inPassStep (ls : list ElemL) (rs : list ElemR) : option (list ElemL * list ElemR) :=
  match rs with
  | er_run10 k :: rs' =>
    Some (push10L (k + 1)%N ls, rs')
  | er_single 2 0 :: er_single 0 0 :: rs' =>
    Some (el_single 0 sep0 :: el_single 2 sep0 :: ls, rs')
  | er_single 2 0 :: er_run10 k :: er_single 0 0 :: rs' =>
    Some (el_single 0 sep0 :: el_run10 k :: el_single 2 sep0 :: ls, rs')
  | _ => None
  end.

Fixpoint inPassLocalAux (cnt : nat) (ls : list ElemL) (rs : list ElemR) (moved : bool)
    : BaseState * bool :=
  match cnt with
  | 0 => (bs_BR ls (er_run10 N0 :: er_single 0 0 :: rs), moved)
  | S cnt' =>
    match inPassStep ls rs with
    | None => (bs_BR ls (er_run10 N0 :: er_single 0 0 :: rs), moved)
    | Some (ls', rs') => inPassLocalAux cnt' ls' rs' true
    end
  end.

Definition inPassLocal (ls : list ElemL) (rs : list ElemR) (moved : bool) : BaseState * bool :=
  inPassLocalAux 128 ls rs moved.

Definition isEnd00 (rs : list ElemR) : bool :=
  match rs with
  | [er_single 0 0] => true
  | _ => false
  end.

Fixpoint inPassFullAux (cnt : nat) (ls : list ElemL) (rs : list ElemR) (moved : bool)
    : BaseState * bool :=
  if isEnd00 rs then (bs_CR (push10L 2%N ls) [], true)
  else
    match cnt with
    | 0 => (bs_BR ls (er_run10 N0 :: er_single 0 0 :: rs), moved)
    | S cnt' =>
      match inPassStep ls rs with
      | None => (bs_BR ls (er_run10 N0 :: er_single 0 0 :: rs), moved)
      | Some (ls', rs') => inPassFullAux cnt' ls' rs' true
      end
    end.

Definition inPassFull (ls : list ElemL) (rs : list ElemR) (moved : bool) : BaseState * bool :=
  inPassFullAux 128 ls rs moved.

Definition stepBR0Fast (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match ls, rs with
  | el_single 3 sep0 :: ls', er_single 0 0 :: er_single 0 0 :: rs' =>
    let (bs', mv) := outPass ls' rs' false in
    if mv then Some bs' else tryBR0 ls rs
  | _, _ => tryBR0 ls rs
  end.

Definition stepBRFullFast (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match rs with
  | er_run10 N0 :: er_single 0 0 :: rs' =>
    let (bs', mv) := inPassFull ls rs' false in
    if mv then Some bs' else tryBR ls rs
  | _ => None
  end.

Definition stepBRLocalFast (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match rs with
  | er_run10 N0 :: er_single 0 0 :: rs' =>
    let (bs', mv) := inPassLocal ls rs' false in
    if mv then Some bs' else tryBR ls rs
  | _ => None
  end.

Definition stepCRFast (ls : list ElemL) (rs : list ElemR) : option BaseState :=
  match ls, rs with
  | el_run10 (Npos p) :: ls', [] => Some (fst (outPass (peel10L (N.pred (Npos p)) ls') [er_single 0 0] true))
  | _, _ => tryCR ls rs
  end.

Definition stepSuper (bs : BaseState) : option BaseState :=
  match bs with
  | bs_Halt _ _ => None
  | bs_BR0 ls rs =>
    match stepBR0Fast ls rs with
    | Some res => Some res
    | None => step1Elem bs
    end
  | bs_AL ls rs =>
    match tryAL ls rs with
    | Some res => Some res
    | None => step1Elem bs
    end
  | bs_BR ls rs =>
    match stepBRFullFast ls rs with
    | Some res => Some res
    | None => step1Elem bs
    end
  | bs_CR ls rs =>
    match stepCRFast ls rs with
    | Some res => Some res
    | None => step1Elem bs
    end
  | _ => step1Elem bs
  end.

Definition has3R (rs : list ElemR) : bool :=
  match rs with
  | er_run10 (Npos (xO _)) :: _ => true
  | er_run10 (Npos (xI _)) :: _ => true
  | er_run10 (Npos xH) :: _ :: _ => true
  | _ :: er_run10 (Npos _) :: _ => true
  | _ :: _ :: _ :: _ => true
  | _ => false
  end.

Definition miniStep (bs : BaseState) : option BaseState :=
  match bs with
  | bs_Halt _ _ | bs_Init => None
  | bs_BR0 ls rs =>
    match stepBR0Fast ls rs with
    | Some res => Some res
    | None => if has3R rs then step1Elem bs else None
    end
  | bs_AL ls rs =>
    match tryAL ls rs with
    | Some res => Some res
    | None => if has3R rs then step1Elem bs else None
    end
  | bs_BR ls rs =>
    match stepBRLocalFast ls rs with
    | Some res => Some res
    | None => if has3R rs then step1Elem bs else None
    end
  | bs_CR ls rs =>
    match tryCR ls rs with
    | Some res => Some res
    | None => if has3R rs then step1Elem bs else None
    end
  | bs_DL _ rs | bs_ER _ rs =>
    if has3R rs then step1Elem bs else None
  end.

Fixpoint miniLoop (rem : nat) (bs : BaseState) (moved : bool) : option (list ElemL) :=
  match rem with
  | 0 => None
  | S rem' =>
    match bs with
    | bs_BR (el_run10 (Npos p) :: ls) [er_run10 N0; er_single 0 0] =>
      if moved then Some (peel10L (N.pred (Npos p)) ls) else None
    | _ =>
      match miniStep bs with
      | None => None
      | Some bs' => miniLoop rem' bs' true
      end
    end
  end.

Fixpoint iterMiniStep (n : nat) (bs : BaseState) : option BaseState :=
  match n with
  | 0 => Some bs
  | S n' =>
    match miniStep bs with
    | None => None
    | Some bs' => iterMiniStep n' bs'
    end
  end.

Fixpoint iterStepSuper (n : nat) (bs : BaseState) : option BaseState :=
  match n with
  | 0 => Some bs
  | S n' =>
    match stepSuper bs with
    | None => None
    | Some bs' => iterStepSuper n' bs'
    end
  end.

(* ========================================================================= *)
(* 4. RLE Expansion Equivalence & Shortcut / Sweep Soundness                 *)
(* ========================================================================= *)

Lemma expandL_push10L : forall n ls,
  expandL (push10L n ls) = prependRepL n (expandL ls).
Proof.
  intros [| p] ls.
  - reflexivity.
  - destruct ls as [| [d b | k2] rest]; cbn [push10L expandL].
    + replace (N.pred (Npos p) + 1)%N with (Npos p) by lia. reflexivity.
    + replace (N.pred (Npos p) + 1)%N with (Npos p) by lia. reflexivity.
    + replace (Npos p + k2 + 1)%N with (Npos p + (k2 + 1))%N by lia.
      rewrite prependRepL_add. reflexivity.
Qed.

Lemma expandL_pushSL : forall d b ls,
  expandL (pushSL d b ls) = (d, b) :: expandL ls.
Proof.
  intros [| [| dm]] [| |] ls; cbn [pushSL expandL]; try reflexivity.
  rewrite expandL_push10L, prependRepL_1. reflexivity.
Qed.

Lemma expandL_peel10L : forall k ls,
  expandL (el_run10 k :: ls) = (1, sep0) :: expandL (peel10L k ls).
Proof.
  intros [| p] ls; cbn [peel10L expandL].
  - reflexivity.
  - replace (Npos p + 1)%N with ((N.pred (Npos p) + 1) + 1)%N by lia.
    rewrite prependRepL_add1. reflexivity.
Qed.

Lemma expandL_peel2 : forall p ls,
  expandL (el_run10 (Npos p) :: ls) = prependRepL 2%N (expandL (peel10L (N.pred (Npos p)) ls)).
Proof.
  intros p ls. rewrite expandL_peel10L, prependRepL_2.
  cbn [peel10L]. rewrite expandL_peel10L. reflexivity.
Qed.

Lemma pop1L_none : forall ls, pop1L ls = None -> expandL ls = [].
Proof.
  intros [| [d b | k] rest] H; [reflexivity | discriminate H | discriminate H].
Qed.

Lemma pop1L_some : forall ls rest p,
  pop1L ls = Some (p, rest) -> expandL ls = p :: expandL rest.
Proof.
  intros [| [d b | k] ls'] rest p H; cbn [pop1L] in H.
  - discriminate H.
  - injection H as <- <-. reflexivity.
  - injection H as <- <-. apply expandL_peel10L.
Qed.

Lemma expandR_push10R : forall n rs,
  expandR (push10R n rs) = prependRepR n (expandR rs).
Proof.
  intros [| p] rs.
  - reflexivity.
  - destruct rs as [| [z o | k2] rest]; cbn [push10R expandR].
    + replace (N.pred (Npos p) + 1)%N with (Npos p) by lia. reflexivity.
    + replace (N.pred (Npos p) + 1)%N with (Npos p) by lia. reflexivity.
    + replace (Npos p + k2 + 1)%N with (Npos p + (k2 + 1))%N by lia.
      rewrite prependRepR_add. reflexivity.
Qed.

Lemma expandR_pushSR : forall z o rs,
  expandR (pushSR z o rs) = (z, o) :: expandR rs.
Proof.
  intros [| [| zm]] [| om] rs; cbn [pushSR expandR]; try reflexivity.
  rewrite expandR_push10R, prependRepR_1. reflexivity.
Qed.

Lemma expandR_peel10R : forall k rs,
  expandR (er_run10 k :: rs) = (1, 0) :: expandR (peel10R k rs).
Proof.
  intros [| p] rs; cbn [peel10R expandR].
  - reflexivity.
  - replace (Npos p + 1)%N with ((N.pred (Npos p) + 1) + 1)%N by lia.
    rewrite prependRepR_add1. reflexivity.
Qed.

Lemma pop1R_none : forall rs, pop1R rs = None -> expandR rs = [].
Proof.
  intros [| [z o | k] rest] H; [reflexivity | discriminate H | discriminate H].
Qed.

Lemma pop1R_some : forall rs rest p,
  pop1R rs = Some (p, rest) -> expandR rs = p :: expandR rest.
Proof.
  intros [| [z o | k] rs'] rest p H; cbn [pop1R] in H.
  - discriminate H.
  - injection H as <- <-. reflexivity.
  - injection H as <- <-. apply expandR_peel10R.
Qed.

Lemma expandL_bumpLElem : forall ls, expandL (bumpLElem ls) = bumpL (expandL ls).
Proof.
  intros ls. unfold bumpLElem.
  destruct (pop1L ls) as [[[d b] rest] |] eqn:Hp.
  - rewrite (pop1L_some _ _ _ Hp), expandL_pushSL. reflexivity.
  - rewrite (pop1L_none _ Hp). reflexivity.
Qed.

Lemma expandL_push100LElem : forall ls, expandL (push100LElem ls) = push100L (expandL ls).
Proof.
  intros [| [d b | k] rest]; cbn [push100LElem expandL push100L]; try reflexivity.
  rewrite prependRepL_add1. reflexivity.
Qed.

Lemma expandL_push1000LElem : forall ls, expandL (push1000LElem ls) = push1000L (expandL ls).
Proof.
  intros [| [d b | k] rest]; cbn [push1000LElem expandL push1000L]; try reflexivity.
  rewrite prependRepL_add1. reflexivity.
Qed.

Lemma expandR_push0RElem : forall rs, expandR (push0RElem rs) = push0R (expandR rs).
Proof.
  intros rs. unfold push0RElem.
  destruct (pop1R rs) as [[[z o] rest] |] eqn:Hp.
  - rewrite (pop1R_some _ _ _ Hp), expandR_pushSR. reflexivity.
  - rewrite (pop1R_none _ Hp). reflexivity.
Qed.

Lemma push0RN_nil : forall d, push0RN d [] = [].
Proof. induction d as [| d IH]; [reflexivity | exact IH]. Qed.

Lemma push0RN_cons : forall d z o rs, push0RN d ((z, o) :: rs) = (z + d, o) :: rs.
Proof.
  induction d as [| d IH]; intros z o rs; cbn [push0RN push0R].
  - f_equal. f_equal. lia.
  - rewrite IH. f_equal. f_equal. lia.
Qed.

Lemma expandR_push0RNElem : forall d rs, expandR (push0RNElem d rs) = push0RN d (expandR rs).
Proof.
  intros [| nm] rs; cbn [push0RNElem].
  - reflexivity.
  - destruct (pop1R rs) as [[[z o] rest] |] eqn:Hp.
    + rewrite (pop1R_some _ _ _ Hp), expandR_pushSR, push0RN_cons. reflexivity.
    + rewrite (pop1R_none _ Hp), push0RN_nil. reflexivity.
Qed.

Lemma expandR_push1RElem : forall rs, expandR (push1RElem rs) = push1R (expandR rs).
Proof.
  intros rs. unfold push1RElem.
  destruct (pop1R rs) as [[[[| zm] o] rest] |] eqn:Hp.
  - rewrite (pop1R_some _ _ _ Hp). reflexivity.
  - rewrite (pop1R_some _ _ _ Hp). cbn [expandR push1R]. rewrite expandR_pushSR. reflexivity.
  - rewrite (pop1R_none _ Hp). reflexivity.
Qed.

Lemma expandR_consume1RElem : forall o rs,
  expandR (consume1RElem o rs) = consume1R o (expandR rs).
Proof.
  intros [| o'] rs; cbn [consume1RElem consume1R].
  - apply expandR_push0RElem.
  - reflexivity.
Qed.

Lemma step1Elem_toFlat : forall bs bs',
  step1Elem bs = Some bs' -> stepFlat (toFlat bs) = Some (toFlat bs').
Proof.
  intros bs bs' H.
  destruct bs as [| ls rs | ls rs | ls rs | ls rs | ls rs | ls rs | ls rs]; cbn [step1Elem] in H.
  - injection H as <-. reflexivity.
  - discriminate H.
  - destruct (pop1L ls) as [[[d [| |]] ls'] |] eqn:Hp; injection H as <-;
      cbn [toFlat];
      try rewrite (pop1L_some _ _ _ Hp);
      try rewrite (pop1L_none _ Hp);
      cbn [stepFlat expandL];
      repeat rewrite expandL_bumpLElem;
      repeat rewrite expandL_push100LElem;
      repeat rewrite expandR_push0RNElem;
      repeat rewrite expandR_push0RElem;
      reflexivity.
  - destruct (pop1R rs) as [[[[| [| [| z]]] o] rs'] |] eqn:Hp.
    + destruct ls as [| [d b | k] ls'].
      * destruct o as [| o']; injection H as <-; cbn [toFlat];
          rewrite (pop1R_some _ _ _ Hp); cbn [stepFlat expandL expandR];
          repeat rewrite expandR_push1RElem; repeat rewrite expandR_push0RElem; reflexivity.
      * injection H as <-. cbn [toFlat]. rewrite (pop1R_some _ _ _ Hp).
        cbn [stepFlat expandL]. rewrite expandR_consume1RElem. reflexivity.
      * injection H as <-. cbn [toFlat]. rewrite (pop1R_some _ _ _ Hp).
        cbn [expandL]. rewrite prependRepL_add1. cbn [stepFlat].
        rewrite expandR_consume1RElem. reflexivity.
    + injection H as <-. cbn [toFlat]. rewrite (pop1R_some _ _ _ Hp).
      cbn [stepFlat expandL]. rewrite expandR_consume1RElem. reflexivity.
    + injection H as <-. cbn [toFlat]. rewrite (pop1R_some _ _ _ Hp).
      cbn [stepFlat]. rewrite expandL_push100LElem, expandR_consume1RElem. reflexivity.
    + injection H as <-. cbn [toFlat]. rewrite (pop1R_some _ _ _ Hp).
      cbn [stepFlat]. repeat rewrite expandR_push1RElem. rewrite expandR_pushSR. reflexivity.
    + injection H as <-. cbn [toFlat]. rewrite (pop1R_none _ Hp). reflexivity.
  - destruct (pop1R rs) as [[[[| [| [| z]]] o] rs'] |] eqn:Hp.
    + destruct o as [| o']; injection H as <-; cbn [toFlat];
        rewrite (pop1R_some _ _ _ Hp); cbn [stepFlat expandR];
        repeat rewrite expandR_push1RElem; repeat rewrite expandR_push0RElem; reflexivity.
    + injection H as <-. cbn [toFlat]. rewrite (pop1R_some _ _ _ Hp).
      cbn [stepFlat]. rewrite expandL_push100LElem, expandR_consume1RElem. reflexivity.
    + injection H as <-. cbn [toFlat]. rewrite (pop1R_some _ _ _ Hp).
      cbn [stepFlat]. rewrite expandL_push1000LElem, expandR_consume1RElem. reflexivity.
    + injection H as <-. cbn [toFlat]. rewrite (pop1R_some _ _ _ Hp).
      cbn [stepFlat]. repeat rewrite expandR_push1RElem. rewrite expandR_pushSR. reflexivity.
    + injection H as <-. cbn [toFlat]. rewrite (pop1R_none _ Hp). reflexivity.
  - destruct (pop1R rs) as [[[[| [| z]] o] rs'] |] eqn:Hp; injection H as <-; cbn [toFlat];
      try rewrite (pop1R_some _ _ _ Hp); try rewrite (pop1R_none _ Hp); cbn [stepFlat expandL expandR];
      repeat rewrite expandL_bumpLElem; repeat rewrite expandR_consume1RElem;
      repeat rewrite expandR_push1RElem; repeat rewrite expandR_pushSR; reflexivity.
  - destruct ls as [| [d b | k] ls']; injection H as <-; cbn [toFlat stepFlat expandL];
      try rewrite expandR_push1RElem; try rewrite prependRepL_add1; reflexivity.
  - destruct (pop1R rs) as [[[[| z] [| o]] rs'] |] eqn:Hp; injection H as <-; cbn [toFlat];
      try rewrite (pop1R_some _ _ _ Hp); try rewrite (pop1R_none _ Hp); cbn [stepFlat expandR];
      repeat rewrite expandL_bumpLElem; repeat rewrite expandR_consume1RElem;
      repeat rewrite expandR_push1RElem; repeat rewrite expandR_pushSR; reflexivity.
Qed.

Lemma step1Elem_some : forall bs bs',
  step1Elem bs = Some bs' -> encodeFlat (toFlat bs) -[ tm ]->+ encodeFlat (toFlat bs').
Proof.
  intros bs bs' H. exact (stepFlat_some _ _ (step1Elem_toFlat bs bs' H)).
Qed.

Lemma expandL_append : forall l1 l2, expandL (l1 ++ l2) = expandL l1 ++ expandL l2.
Proof.
  induction l1 as [| [d b | k] rest IH]; intros l2; cbn [app expandL].
  - reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH, prependRepL_append_eq. reflexivity.
Qed.

(* Finite-Step Flat Shortcuts & N-Sweeps *)

Ltac close_flat_sc k :=
  lazymatch goal with
  | |- forall (_ : list (nat * Sep3)) (_ : list (nat * nat)), _ =>
    intros [| [? ?] ?] [| [? ?] ?]; apply (iterStepFlat_plus k); reflexivity
  | |- forall (_ : list (nat * Sep3)), _ =>
    intros [| [? ?] ?]; apply (iterStepFlat_plus k); reflexivity
  | |- forall (_ : list (nat * nat)), _ =>
    intros [| [? ?] ?]; apply (iterStepFlat_plus k); reflexivity
  end.

Lemma sw_out15_step : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (1, sep0) :: ls) ((0, 0) :: (0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls) ((0, 0) :: (0, 0) :: (1, 0) :: rs)).
Proof. intros ls rs. apply (iterStepFlat_plus 4); reflexivity. Qed.

Lemma sw_out15_rep : forall (n : N) ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: prependRepL n ls) ((0, 0) :: (0, 0) :: rs))
    -[ tm ]->*
  encodeFlat (fs_BR0 ((3, sep0) :: ls) ((0, 0) :: (0, 0) :: prependRepR n rs)).
Proof.
  intros n. pattern n. apply N.peano_ind.
  - intros ls rs. rewrite prependRepL_0, prependRepR_0. apply evstep_refl.
  - intros n' IH ls rs. rewrite prependRepL_succ, prependRepR_succ, <- prependRepR_cons.
    eapply evstep_trans; [apply progress_evstep, sw_out15_step | apply IH].
Qed.

Lemma sw_out15_rep_plus : forall (n : N) ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: prependRepL (n + 1)%N ls) ((0, 0) :: (0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls) ((0, 0) :: (0, 0) :: prependRepR (n + 1)%N rs)).
Proof.
  intros n ls rs. rewrite prependRepL_add1, prependRepR_add1, <- prependRepR_cons.
  eapply progress_evstep_trans; [apply sw_out15_step | apply sw_out15_rep].
Qed.

Lemma sc_br0_3_flat : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: ls) ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 (bumpL (bumpL ls)) ((0, 0) :: (0, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 4. Qed.

Lemma sc_br0_2_flat : forall ls rs,
  encodeFlat (fs_BR0 ((2, sep0) :: ls) ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_AL (bumpL (bumpL ls)) ((0, 0) :: (0, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 5. Qed.

Lemma sc_br0_4_flat : forall ls rs,
  encodeFlat (fs_BR0 ((4, sep0) :: ls) ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_AL (bumpL (bumpL ls)) ((0, 0) :: (2, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 5. Qed.

Lemma sc_br0_10_flat : forall ls rs,
  encodeFlat (fs_BR0 ((1, sep0) :: ls) ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR ((0, sep0) :: bumpL ls) ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 4. Qed.

Lemma al2_bot_1_flat : forall rs,
  encodeFlat (fs_AL [(4, sep0); (0, sep0); (3, sep0); (0, sep0); (0, sep0)] ((0, 0) :: (0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR [(0, sep0); (2, sep1); (1, sep0); (2, sep0); (0, sep0); (0, sep0)]
    ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 50. Qed.

Lemma al2_bot_2_flat : forall rs,
  encodeFlat (fs_AL [(4, sep1); (1, sep0); (2, sep0); (0, sep0); (0, sep0)] ((0, 0) :: (0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR [(0, sep0); (1, sep0); (2, sep0); (2, sep0); (0, sep0); (0, sep0)]
    ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 17. Qed.

Lemma al2_bot_3_flat : forall rs,
  encodeFlat (fs_AL [(3, sep0); (2, sep0); (2, sep0); (0, sep0); (0, sep0)] ((0, 0) :: (0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR [(0, sep0); (0, sep0); (1, sep0); (0, sep0); (3, sep0); (0, sep0); (0, sep0)]
    ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 55. Qed.

Lemma sc_bot1_flat : forall rs,
  encodeFlat (fs_AL [(1, sep0)] ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_CR [(0, sep0); (0, sep0); (0, sep0)] ((0, 0) :: rs)).
Proof. close_flat_sc 4. Qed.

Lemma al1_bot_1_flat : forall rs,
  encodeFlat (fs_AL [(3, sep1); (1, sep0); (0, sep0); (3, sep0); (0, sep0); (0, sep0)] ((0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR [(0, sep0); (2, sep0); (0, sep0); (3, sep0); (0, sep0); (0, sep0)]
    ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 8. Qed.

Lemma al1_bot_2_flat : forall rs,
  encodeFlat (fs_AL [(3, sep0); (0, sep0); (3, sep0); (0, sep0); (0, sep0)] ((0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR [(1, sep1); (1, sep0); (2, sep0); (0, sep0); (0, sep0)]
    ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 41. Qed.

Lemma al1_bot_3_flat : forall rs,
  encodeFlat (fs_AL [(3, sep0); (1, sep1); (1, sep0); (2, sep0); (0, sep0); (0, sep0)] ((0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR [(1, sep0); (0, sep0); (2, sep0); (2, sep0); (0, sep0); (0, sep0)]
    ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 17. Qed.

Lemma al1_bot_4_flat : forall rs,
  encodeFlat (fs_AL [(3, sep1); (1, sep0); (2, sep0); (0, sep0); (0, sep0)] ((0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR [(0, sep0); (2, sep0); (2, sep0); (0, sep0); (0, sep0)]
    ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 8. Qed.

Lemma al1_bot_5_flat : forall rs,
  encodeFlat (fs_AL [(3, sep0); (0, sep0); (2, sep0); (2, sep0); (0, sep0); (0, sep0)] ((0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR [(1, sep1); (1, sep0); (0, sep0); (3, sep0); (0, sep0); (0, sep0)]
    ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 55. Qed.

Lemma sc_al_3_flat : forall ls rs,
  encodeFlat (fs_AL ((3, sep0) :: ls) ((0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 (bumpL (bumpL ls)) ((0, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 3. Qed.

Lemma sc_al_2_flat : forall ls rs,
  encodeFlat (fs_AL ((2, sep0) :: ls) ((0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_AL (bumpL (bumpL ls)) ((0, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 4. Qed.

Lemma sc_al_4_flat : forall ls rs,
  encodeFlat (fs_AL ((4, sep0) :: ls) ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_AL (bumpL (bumpL ls)) ((0, 0) :: (2, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 4. Qed.

Lemma sw_in19_step : forall ls rs,
  encodeFlat (fs_AL ((0, sep1) :: ls) ((0, 0) :: (1, 0) :: (1, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_AL ((0, sep1) :: (1, sep0) :: ls) ((0, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 8. Qed.

Lemma sw_in19_rep : forall (n : N) ls rs,
  encodeFlat (fs_AL ((0, sep1) :: ls) ((0, 0) :: prependRepR (n + 1)%N rs))
    -[ tm ]->*
  encodeFlat (fs_AL ((0, sep1) :: prependRepL n ls) ((0, 0) :: (1, 0) :: rs)).
Proof.
  intros n. pattern n. apply N.peano_ind.
  - intros ls rs. rewrite prependRepR_1, prependRepL_0. apply evstep_refl.
  - intros n' IH ls rs.
    replace (N.succ n' + 1)%N with (N.succ (n' + 1))%N by lia.
    rewrite prependRepR_succ, prependRepR_add1, prependRepL_succ, <- prependRepL_cons.
    eapply evstep_trans; [apply progress_evstep, sw_in19_step | rewrite <- prependRepR_add1; apply IH].
Qed.

Lemma sw_in19_rep_plus : forall p ls rs,
  encodeFlat (fs_AL ((0, sep1) :: ls) ((0, 0) :: prependRepR (Npos p + 1)%N rs))
    -[ tm ]->+
  encodeFlat (fs_AL ((0, sep1) :: prependRepL (Npos p) ls) ((0, 0) :: (1, 0) :: rs)).
Proof.
  intros p ls rs.
  replace (Npos p) with (N.succ (N.pred (Npos p))) by lia.
  replace (N.succ (N.pred (Npos p)) + 1)%N with ((N.pred (Npos p) + 1) + 1)%N by lia.
  rewrite prependRepR_add1, prependRepR_add1, prependRepL_succ, <- prependRepL_cons.
  eapply progress_evstep_trans; [apply sw_in19_step | rewrite <- prependRepR_add1; apply sw_in19_rep].
Qed.

Lemma sw_in7_step : forall ls rs,
  encodeFlat (fs_BR ls ((1, 0) :: (0, 0) :: (1, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR ((1, sep0) :: ls) ((1, 0) :: (0, 0) :: rs)).
Proof. intros ls rs. apply (iterStepFlat_plus 3); reflexivity. Qed.

Lemma sw_in7_rep : forall (n : N) ls rs,
  encodeFlat (fs_BR ls ((1, 0) :: (0, 0) :: prependRepR n rs))
    -[ tm ]->*
  encodeFlat (fs_BR (prependRepL n ls) ((1, 0) :: (0, 0) :: rs)).
Proof.
  intros n. pattern n. apply N.peano_ind.
  - intros ls rs. rewrite prependRepR_0, prependRepL_0. apply evstep_refl.
  - intros n' IH ls rs. rewrite prependRepR_succ, prependRepL_succ, <- prependRepL_cons.
    eapply evstep_trans; [apply progress_evstep, sw_in7_step | apply IH].
Qed.

Lemma sw_in7_rep_plus : forall (n : N) ls rs,
  encodeFlat (fs_BR ls ((1, 0) :: (0, 0) :: prependRepR (n + 1)%N rs))
    -[ tm ]->+
  encodeFlat (fs_BR (prependRepL (n + 1)%N ls) ((1, 0) :: (0, 0) :: rs)).
Proof.
  intros n ls rs. rewrite prependRepR_add1, prependRepL_add1, <- prependRepL_cons.
  eapply progress_evstep_trans; [apply sw_in7_step | apply sw_in7_rep].
Qed.

Lemma sc_br_10_0_2_flat : forall ls rs,
  encodeFlat (fs_BR ls ((1, 0) :: (0, 0) :: (2, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((1, sep0) :: (1, sep0) :: ls) ((0, 0) :: rs)).
Proof. close_flat_sc 7. Qed.

Lemma sc_cr_02_flat : forall ls rs,
  encodeFlat (fs_CR ((0, sep0) :: ls) ((2, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((1, sep0) :: ls) ((0, 0) :: rs)).
Proof. close_flat_sc 2. Qed.

Lemma topOut_flat : forall ls,
  encodeFlat (fs_CR ((1, sep0) :: (1, sep0) :: ls) []) -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls) [(0, 0); (0, 0); (0, 0)]).
Proof. close_flat_sc 10. Qed.

Lemma out_hdr_02_flat : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (0, sep0) :: (2, sep0) :: (1, sep0) :: (1, sep0) :: ls)
    ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    ((0, 0) :: (0, 0) :: (2, 0) :: (0, 0) :: (1, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 19. Qed.

Lemma out_hdr_0_flat : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (0, sep0) :: (1, sep0) :: (1, sep0) :: ls)
    ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    ((0, 0) :: (0, 0) :: (0, 0) :: (1, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 14. Qed.

Lemma out_hdr_2_flat : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (2, sep0) :: (1, sep0) :: (1, sep0) :: ls)
    ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    ((0, 0) :: (0, 0) :: (2, 0) :: (1, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 14. Qed.

Lemma out_hdr_020_flat : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (0, sep0) :: (2, sep0) :: (0, sep0) :: (1, sep0) :: (1, sep0) :: ls)
    ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    ((0, 0) :: (0, 0) :: (0, 0) :: (2, 0) :: (0, 0) :: (1, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 24. Qed.

Lemma out_hdr_20_flat : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (2, sep0) :: (0, sep0) :: (1, sep0) :: (1, sep0) :: ls)
    ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    ((0, 0) :: (0, 0) :: (0, 0) :: (2, 0) :: (1, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 19. Qed.

Lemma out_hdr_0_10_2_flat : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (0, sep0) :: (1, sep0) :: (2, sep0) :: (1, sep0) :: (1, sep0) :: ls)
    ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    ((0, 0) :: (0, 0) :: (2, 0) :: (1, 0) :: (0, 0) :: (1, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 24. Qed.

Lemma out_hdr_020_10_2_flat : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (0, sep0) :: (2, sep0) :: (0, sep0) :: (1, sep0) ::
    (2, sep0) :: (1, sep0) :: (1, sep0) :: ls) ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    ((0, 0) :: (0, 0) :: (2, 0) :: (1, 0) :: (0, 0) :: (2, 0) :: (0, 0) ::
      (1, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 34. Qed.

Lemma out_hdr_02_10_02_flat : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (0, sep0) :: (2, sep0) :: (1, sep0) :: (0, sep0) ::
    (2, sep0) :: (1, sep0) :: (1, sep0) :: ls) ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    ((0, 0) :: (0, 0) :: (2, 0) :: (0, 0) :: (1, 0) :: (2, 0) :: (0, 0) ::
      (1, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 34. Qed.

Lemma out_hdr_02_02_flat : forall ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (0, sep0) :: (2, sep0) :: (0, sep0) ::
    (2, sep0) :: (1, sep0) :: (1, sep0) :: ls) ((0, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    ((0, 0) :: (0, 0) :: (2, 0) :: (0, 0) :: (2, 0) :: (0, 0) ::
      (1, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 29. Qed.

Lemma in_20_flat : forall ls rs,
  encodeFlat (fs_BR ls ((1, 0) :: (0, 0) :: (2, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR ((0, sep0) :: (2, sep0) :: ls) ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 12. Qed.

Lemma in_2_10_entry_flat : forall ls rs,
  encodeFlat (fs_BR ls ((1, 0) :: (0, 0) :: (2, 0) :: (1, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_AL ((0, sep1) :: (2, sep0) :: ls) ((0, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 11. Qed.

Lemma in_2_10_exit_flat : forall ls rs,
  encodeFlat (fs_AL ((0, sep1) :: ls) ((0, 0) :: (1, 0) :: (0, 0) :: rs)) -[ tm ]->+
  encodeFlat (fs_BR ((0, sep0) :: (1, sep0) :: ls) ((1, 0) :: (0, 0) :: rs)).
Proof. close_flat_sc 9. Qed.

Lemma in_2_10_flat : forall (k : N) ls rs,
  encodeFlat (fs_BR ls ((1, 0) :: (0, 0) :: (2, 0) :: prependRepR (k + 1)%N ((0, 0) :: rs)))
    -[ tm ]->+
  encodeFlat (fs_BR ((0, sep0) :: prependRepL (k + 1)%N ((2, sep0) :: ls))
    ((1, 0) :: (0, 0) :: rs)).
Proof.
  intros k ls rs.
  rewrite prependRepR_add1, prependRepL_add1.
  eapply progress_evstep_trans.
  - apply in_2_10_entry_flat.
  - eapply evstep_trans.
    + pose proof (sw_in19_rep k ((2, sep0) :: ls) ((0, 0) :: rs)) as H2.
      rewrite prependRepR_add1 in H2. exact H2.
    + apply progress_evstep, in_2_10_exit_flat.
Qed.

Lemma in_top_end_flat : forall ls,
  encodeFlat (fs_BR ls [(1, 0); (0, 0); (0, 0)]) -[ tm ]->+
  encodeFlat (fs_CR ((1, sep0) :: (1, sep0) :: ls) []).
Proof. close_flat_sc 5. Qed.

(* R-Base Polymorphic Soundness *)

Definition fsR (fs : FlatState) : list (nat * nat) :=
  match fs with
  | fs_Init => []
  | fs_Halt _ rs | fs_AL _ rs | fs_BR _ rs | fs_BR0 _ rs
  | fs_CR _ rs | fs_DL _ rs | fs_ER _ rs => rs
  end.

Definition fsApp (fs : FlatState) (rb : list (nat * nat)) : FlatState :=
  match fs with
  | fs_Init => fs_Init
  | fs_Halt ls rs => fs_Halt ls (rs ++ rb)
  | fs_AL ls rs => fs_AL ls (rs ++ rb)
  | fs_BR ls rs => fs_BR ls (rs ++ rb)
  | fs_BR0 ls rs => fs_BR0 ls (rs ++ rb)
  | fs_CR ls rs => fs_CR ls (rs ++ rb)
  | fs_DL ls rs => fs_DL ls (rs ++ rb)
  | fs_ER ls rs => fs_ER ls (rs ++ rb)
  end.

Definition toFlatBase (bs : BaseState) (rb : list (nat * nat)) : FlatState :=
  fsApp (toFlat bs) rb.

Lemma toFlatBase_nil : forall bs, toFlatBase bs [] = toFlat bs.
Proof.
  intros [| ? ? | ? ? | ? ? | ? ? | ? ? | ? ? | ? ?];
    cbn [toFlatBase fsApp toFlat]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma prependRepR_len_ge : forall n xs,
  length xs <= length (prependRepR n xs).
Proof.
  intros n. pattern n. apply N.peano_ind.
  - intros xs. rewrite prependRepR_0. lia.
  - intros n' IH xs. rewrite prependRepR_succ. cbn [length]. specialize (IH xs). lia.
Qed.

Lemma expandR_cons_len : forall e rs,
  1 + length (expandR rs) <= length (expandR (e :: rs)).
Proof.
  intros [z o | k] rs; cbn [expandR].
  - cbn [length]. lia.
  - rewrite prependRepR_add1. cbn [length].
    pose proof (prependRepR_len_ge k (expandR rs)). lia.
Qed.

Lemma has3R_len : forall rs, has3R rs = true -> 2 <= length (expandR rs).
Proof.
  intros rs H.
  destruct rs as [| e1 [| e2 rest]].
  - discriminate H.
  - destruct e1 as [z1 o1 | [| [q1 | q1 |]]]; try discriminate H; cbn [expandR].
    + replace (Npos (xI q1) + 1)%N with (((Npos (xI q1) - 1) + 1) + 1)%N by lia.
      rewrite !prependRepR_add1. cbn [length].
      pose proof (prependRepR_len_ge (Npos (xI q1) - 1)%N []). lia.
    + replace (Npos (xO q1) + 1)%N with (((Npos (xO q1) - 1) + 1) + 1)%N by lia.
      rewrite !prependRepR_add1. cbn [length].
      pose proof (prependRepR_len_ge (Npos (xO q1) - 1)%N []). lia.
  - pose proof (expandR_cons_len e1 (e2 :: rest)).
    pose proof (expandR_cons_len e2 rest).
    lia.
Qed.

Lemma stepFlat_app_of_len2 : forall fs fs' rb,
  fs <> fs_Init -> 2 <= length (fsR fs) ->
  stepFlat fs = Some fs' ->
  stepFlat (fsApp fs rb) = Some (fsApp fs' rb).
Proof.
  intros fs fs' rb Hni Hlen Hs.
  destruct fs as [| ls rs | ls rs | ls rs | ls rs | ls rs | ls rs | ls rs].
  - contradiction.
  - discriminate Hs.
  - destruct rs as [| [z1 o1] [| [z2 o2] rt]]; cbn [fsR length] in Hlen; try lia.
    destruct ls as [| [d [| |]] ls']; injection Hs as <-;
      cbn [fsApp app stepFlat push0R]; rewrite ?push0RN_cons; reflexivity.
  - destruct rs as [| [[| [| [| z1]]] [| o1]] [| [z2 o2] rt]]; cbn [fsR length] in Hlen; try lia.
    + destruct ls as [| p ls']; injection Hs as <-; cbn [fsApp app stepFlat push1R push0R consume1R]; reflexivity.
    + destruct ls as [| p ls']; injection Hs as <-; cbn [fsApp app stepFlat consume1R]; reflexivity.
    + injection Hs as <-. cbn [fsApp app stepFlat consume1R push0R]. reflexivity.
    + injection Hs as <-. cbn [fsApp app stepFlat consume1R]. reflexivity.
    + injection Hs as <-. cbn [fsApp app stepFlat consume1R push0R]. reflexivity.
    + injection Hs as <-. cbn [fsApp app stepFlat consume1R]. reflexivity.
    + injection Hs as <-. destruct z1 as [| z1']; cbn [fsApp app stepFlat push1R]; reflexivity.
    + injection Hs as <-. destruct z1 as [| z1']; cbn [fsApp app stepFlat push1R]; reflexivity.
  - destruct rs as [| [[| [| [| z1]]] [| o1]] [| [z2 o2] rt]]; cbn [fsR length] in Hlen; try lia;
      injection Hs as <-; try (destruct z1 as [| z1']);
      cbn [fsApp app stepFlat push1R push0R consume1R]; reflexivity.
  - destruct rs as [| [[| [| z1]] [| o1]] [| [z2 o2] rt]]; cbn [fsR length] in Hlen; try lia;
      injection Hs as <-; try (destruct z1 as [| z1']);
      cbn [fsApp app stepFlat push1R push0R consume1R]; reflexivity.
  - destruct rs as [| [[| z1] o1] [| [z2 o2] rt]]; cbn [fsR length] in Hlen; try lia;
      destruct ls as [| p ls']; injection Hs as <-;
      cbn [fsApp app stepFlat push1R]; reflexivity.
  - destruct rs as [| [[| z1] [| [| o1]]] [| [z2 o2] rt]]; cbn [fsR length] in Hlen; try lia;
      injection Hs as <-; try (destruct z1 as [| z1']);
      cbn [fsApp app stepFlat push1R push0R consume1R]; reflexivity.
Qed.

Lemma step1Elem_base_some : forall bs bs' rb,
  toFlat bs <> fs_Init -> 2 <= length (fsR (toFlat bs)) ->
  step1Elem bs = Some bs' ->
  encodeFlat (toFlatBase bs rb) -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros bs bs' rb Hni Hlen H.
  apply stepFlat_some.
  exact (stepFlat_app_of_len2 (toFlat bs) (toFlat bs') rb Hni Hlen (step1Elem_toFlat bs bs' H)).
Qed.

End M137.

Module M137Ext.
Import M137.
Arguments push10R : simpl never.
Arguments push10L : simpl never.
Arguments peel10L : simpl never.
Arguments bumpLElem : simpl never.
Ltac discr_none H :=
  cbn iota in H;
  (discriminate H ||
   lazymatch type of H with
   | match ?x with _ => _ end = _ => is_var x; destruct x; discr_none H
   end).

Lemma tryBR0_base_sound : forall ls rs bs' rb,
  tryBR0 ls rs = Some bs' ->
  encodeFlat (toFlatBase (bs_BR0 ls rs) rb) -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros ls rs bs' rb H. unfold tryBR0 in H.
  destruct ls as [| [d1 b1 | k1] ls1], rs as [| [[| ?] [| ?] | ?] [| [[| ?] [| ?] | ?] rs']];
    try (discr_none H).
  - destruct d1 as [| [| [| [| [| d1']]]]]; try (discr_none H);
      destruct b1; try (discr_none H).
    + injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
      rewrite !expandL_bumpLElem, expandR_push10R, ?prependRepR_01, ?prependRepR_1. apply sc_br0_2_flat.
    + destruct ls1 as [| [d2 b2 | k2] ls2]; injection H as <-;
        cbn [toFlatBase fsApp toFlat expandL expandR app].
      * rewrite !expandL_bumpLElem, expandR_push10R, ?prependRepR_01, ?prependRepR_1. apply sc_br0_3_flat.
      * rewrite !expandL_bumpLElem, expandR_push10R, ?prependRepR_01, ?prependRepR_1.
        exact (sc_br0_3_flat ((d2, b2) :: expandL ls2) (expandR rs' ++ rb)).
      * rewrite expandR_push10R, prependRepR_append_eq. apply sw_out15_rep_plus.
    + injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
      rewrite !expandL_bumpLElem, expandR_push10R, ?prependRepR_01, ?prependRepR_1. apply sc_br0_4_flat.
  - injection H as <-. unfold toFlatBase, fsApp, toFlat.
    rewrite expandL_peel10L. cbn [expandL expandR app].
    rewrite expandL_bumpLElem, ?prependRepR_01, ?prependRepR_1. apply sc_br0_10_flat.
Qed.

Lemma tryALBot2_base_sound : forall ls rs bs' rb,
  tryALBot2 ls rs = Some bs' ->
  encodeFlat (toFlatBase (bs_AL ls (er_single 0 0 :: er_single 0 0 :: rs)) rb)
    -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros ls rs bs' rb H. unfold tryALBot2 in H.
  destruct ls as [| [[| [| [| [| [|]]]]] [| |] | [|]] ls1]; try discriminate H.
  - destruct ls1 as [| [[| [| [|]]] [| |] | ?] ls2]; try discriminate H.
    destruct ls2 as [| [[| [| [|]]] [| |] | ?] ls3]; try discriminate H.
    destruct ls3 as [| [[|] [| |] | ?] ls4]; try discriminate H.
    destruct ls4 as [| [[|] [| |] | ?] [|]]; try discriminate H.
    injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite ?prependRepL_01, ?prependRepL_1, ?prependRepR_01, ?prependRepR_1.
    apply al2_bot_3_flat.
  - destruct ls1 as [| [[|] [| |] | ?] ls2]; try discriminate H.
    destruct ls2 as [| [[| [| [| [|]]]] [| |] | ?] ls3]; try discriminate H.
    destruct ls3 as [| [[|] [| |] | ?] ls4]; try discriminate H.
    destruct ls4 as [| [[|] [| |] | ?] [|]]; try discriminate H.
    injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite ?prependRepL_01, ?prependRepL_1, ?prependRepR_01, ?prependRepR_1.
    apply al2_bot_1_flat.
  - destruct ls1 as [| [? ? | [|]] ls2]; try discriminate H.
    destruct ls2 as [| [[| [| [|]]] [| |] | ?] ls3]; try discriminate H.
    destruct ls3 as [| [[|] [| |] | ?] ls4]; try discriminate H.
    destruct ls4 as [| [[|] [| |] | ?] [|]]; try discriminate H.
    injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite ?prependRepL_01, ?prependRepL_1, ?prependRepR_01, ?prependRepR_1.
    apply al2_bot_2_flat.
  - destruct ls1; try discriminate H.
    injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite ?prependRepL_01, ?prependRepL_1. apply sc_bot1_flat.
Qed.

Lemma tryALBot1_base_sound : forall ls rs bs' rb,
  tryALBot1 ls rs = Some bs' ->
  encodeFlat (toFlatBase (bs_AL ls (er_single 0 0 :: rs)) rb)
    -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros ls rs bs' rb H. unfold tryALBot1 in H.
  destruct ls as [| [[| [| [| [|]]]] [| |] | ?] ls1]; try discriminate H.
  - destruct ls1 as [| [[| [|]] [| |] | ?] ls2]; try discriminate H.
    + destruct ls2 as [| [[| [| [| [|]]]] [| |] | ?] ls3]; try discriminate H.
      * destruct ls3 as [| [[| [| [|]]] [| |] | ?] ls4]; try discriminate H.
        destruct ls4 as [| [[|] [| |] | ?] ls5]; try discriminate H.
        destruct ls5 as [| [[|] [| |] | ?] [|]]; try discriminate H.
        injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
        rewrite ?prependRepL_01, ?prependRepL_1, ?prependRepR_01, ?prependRepR_1.
        apply al1_bot_5_flat.
      * destruct ls3 as [| [[|] [| |] | ?] ls4]; try discriminate H.
        destruct ls4 as [| [[|] [| |] | ?] [|]]; try discriminate H.
        injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
        rewrite ?prependRepL_01, ?prependRepL_1, ?prependRepR_01, ?prependRepR_1.
        apply al1_bot_2_flat.
    + destruct ls2 as [| [? ? | [|]] ls3]; try discriminate H.
      destruct ls3 as [| [[| [| [|]]] [| |] | ?] ls4]; try discriminate H.
      destruct ls4 as [| [[|] [| |] | ?] ls5]; try discriminate H.
      destruct ls5 as [| [[|] [| |] | ?] [|]]; try discriminate H.
      injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
      rewrite ?prependRepL_01, ?prependRepL_1, ?prependRepR_01, ?prependRepR_1.
      apply al1_bot_3_flat.
  - destruct ls1 as [| [? ? | [|]] ls2]; try discriminate H.
    destruct ls2 as [| [[| [| [|]]] [| |] | ?] ls3]; try discriminate H.
    + destruct ls3 as [| [[| [| [| [|]]]] [| |] | ?] ls4]; try discriminate H.
      destruct ls4 as [| [[|] [| |] | ?] ls5]; try discriminate H.
      destruct ls5 as [| [[|] [| |] | ?] [|]]; try discriminate H.
      injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
      rewrite ?prependRepL_01, ?prependRepL_1, ?prependRepR_01, ?prependRepR_1.
      apply al1_bot_1_flat.
    + destruct ls3 as [| [[|] [| |] | ?] ls4]; try discriminate H.
      destruct ls4 as [| [[|] [| |] | ?] [|]]; try discriminate H.
      injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
      rewrite ?prependRepL_01, ?prependRepL_1, ?prependRepR_01, ?prependRepR_1.
      apply al1_bot_4_flat.
Qed.

Lemma tryALGen_base_sound : forall ls rs bs' rb,
  tryALGen ls rs = Some bs' ->
  encodeFlat (toFlatBase (bs_AL ls rs) rb) -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros ls rs bs' rb H. unfold tryALGen in H.
  destruct ls as [| [[| [| [| [| [|]]]]] [| |] | ?] ls'], rs as [| [[|] [|] | ?] rs1];
    try (discr_none H).
  - destruct rs1 as [| [? ? | [| p]] rs']; try (discr_none H).
    injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite expandL_push10L, expandR_push10R, ?prependRepR_01, ?prependRepR_1, prependRepR_append_eq.
    apply sw_in19_rep_plus.
  - injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite !expandL_bumpLElem. apply sc_al_2_flat.
  - injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite !expandL_bumpLElem. apply sc_al_3_flat.
  - destruct rs1 as [| [[|] [|] | ?] rs']; try (discr_none H).
    injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite !expandL_bumpLElem. apply sc_al_4_flat.
Qed.

Lemma tryAL_base_sound : forall ls rs bs' rb,
  tryAL ls rs = Some bs' ->
  encodeFlat (toFlatBase (bs_AL ls rs) rb) -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros ls rs bs' rb H. unfold tryAL in H.
  destruct rs as [| [[| z1] [| o1] | r1] rs1]; try discriminate H.
  destruct rs1 as [| [[| z2] [| o2] | r2] rs2].
  - destruct (tryALBot1 ls []) eqn:Hb1; [injection H as <-; exact (tryALBot1_base_sound _ _ _ rb Hb1) |].
    exact (tryALGen_base_sound _ _ _ rb H).
  - destruct (tryALBot2 ls rs2) eqn:Hb2; [injection H as <-; exact (tryALBot2_base_sound _ _ _ rb Hb2) |].
    destruct (tryALBot1 ls (er_single 0 0 :: rs2)) eqn:Hb1;
      [injection H as <-; exact (tryALBot1_base_sound _ _ _ rb Hb1) |].
    exact (tryALGen_base_sound _ _ _ rb H).
  - destruct (tryALBot1 ls (er_single 0 (S o2) :: rs2)) eqn:Hb1;
      [injection H as <-; exact (tryALBot1_base_sound _ _ _ rb Hb1) | exact (tryALGen_base_sound _ _ _ rb H)].
  - destruct (tryALBot1 ls (er_single (S z2) 0 :: rs2)) eqn:Hb1;
      [injection H as <-; exact (tryALBot1_base_sound _ _ _ rb Hb1) | exact (tryALGen_base_sound _ _ _ rb H)].
  - destruct (tryALBot1 ls (er_single (S z2) (S o2) :: rs2)) eqn:Hb1;
      [injection H as <-; exact (tryALBot1_base_sound _ _ _ rb Hb1) | exact (tryALGen_base_sound _ _ _ rb H)].
  - destruct (tryALBot1 ls (er_run10 r2 :: rs2)) eqn:Hb1;
      [injection H as <-; exact (tryALBot1_base_sound _ _ _ rb Hb1) | exact (tryALGen_base_sound _ _ _ rb H)].
Qed.

Lemma tryBR_base_sound : forall ls rs bs' rb,
  tryBR ls rs = Some bs' ->
  encodeFlat (toFlatBase (bs_BR ls rs) rb) -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros ls rs bs' rb H. unfold tryBR in H.
  destruct rs as [| [? ? | [|]] rs1]; try discriminate H.
  destruct rs1 as [| [[|] [|] | ?] rs2]; try discriminate H.
  destruct rs2 as [| [[| [| [|]]] [|] | k] rs']; try discriminate H.
  - injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite expandL_push10L, prependRepL_2, ?prependRepR_01, ?prependRepR_1. cbn [app].
    apply sc_br_10_0_2_flat.
  - injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite expandL_push10L, ?prependRepR_01, ?prependRepR_1. cbn [app].
    rewrite prependRepR_append_eq. apply sw_in7_rep_plus.
Qed.

Lemma tryCR_base_sound : forall ls rs bs' rb,
  tryCR ls rs = Some bs' ->
  encodeFlat (toFlatBase (bs_CR ls rs) rb) -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros ls rs bs' rb H. unfold tryCR in H.
  destruct ls as [| [[|] [| |] | ?] ls'], rs as [| [[| [| [|]]] [|] | ?] rs']; try (discr_none H).
  injection H as <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
  rewrite expandL_push10L, ?prependRepL_01, ?prependRepL_1. apply sc_cr_02_flat.
Qed.

Ltac finish_out_hdr Hhdr p :=
  cbn [toFlatBase fsApp toFlat expandL expandR app];
  repeat (rewrite expandR_push10R; cbn [expandR app]);
  rewrite ?prependRepL_01, ?prependRepR_01, ?prependRepR_2, ?prependRepR_1;
  cbn [app];
  rewrite ?prependRepR_append_eq;
  cbn [app];
  replace (Npos p + 1)%N with (1 + (1 + N.pred (Npos p)))%N by lia;
  rewrite !prependRepL_add, !prependRepL_1;
  cbn [app];
  eapply progress_evstep_trans; [apply Hhdr | apply sw_out15_rep].

Lemma outPassStep_base_sound : forall ls rs ls' rs' rb,
  outPassStep ls rs = Some (ls', rs') ->
  encodeFlat (toFlatBase (bs_BR0 (el_single 3 sep0 :: ls) (er_single 0 0 :: er_single 0 0 :: rs)) rb)
    -[ tm ]->+
  encodeFlat (toFlatBase (bs_BR0 (el_single 3 sep0 :: ls') (er_single 0 0 :: er_single 0 0 :: rs')) rb).
Proof.
  intros ls rs ls' rs' rb H. unfold outPassStep in H.
  destruct ls as [| [d1 b1 | k1] ls1]; try discriminate H.
  - destruct d1 as [| [| [|]]]; try discriminate H; destruct b1; try discriminate H.
    + (* d1 = 0 *)
      destruct ls1 as [| [d2 b2 | k2] ls2]; try discriminate H.
      * destruct d2 as [| [| [|]]]; try discriminate H; destruct b2; try discriminate H.
        destruct ls2 as [| [d3 b3 | k3] ls3]; try discriminate H.
        -- destruct d3 as [|]; try discriminate H; destruct b3; try discriminate H.
           destruct ls3 as [| [d4 b4 | k4] ls4]; try discriminate H.
           ++ destruct d4 as [| [| [|]]]; try discriminate H; destruct b4; try discriminate H.
              destruct ls4 as [| [? ? | [| p5]] ls5]; try discriminate H.
              injection H as <- <-. finish_out_hdr out_hdr_02_02_flat p5.
           ++ destruct k4 as [| p4].
              ** destruct ls4 as [| [[| [| [|]]] [| |] | ?] ls5]; try discriminate H.
                 destruct ls5 as [| [? ? | [| p6]] ls6]; try discriminate H.
                 injection H as <- <-. finish_out_hdr out_hdr_020_10_2_flat p6.
              ** injection H as <- <-. finish_out_hdr out_hdr_020_flat p4.
        -- destruct k3 as [| p3].
           ++ destruct ls3 as [| [[|] [| |] | ?] ls4]; try discriminate H.
              destruct ls4 as [| [[| [| [|]]] [| |] | ?] ls5]; try discriminate H.
              destruct ls5 as [| [? ? | [| p6]] ls6]; try discriminate H.
              injection H as <- <-. finish_out_hdr out_hdr_02_10_02_flat p6.
           ++ injection H as <- <-. finish_out_hdr out_hdr_02_flat p3.
      * destruct k2 as [| p2].
        -- destruct ls2 as [| [[| [| [|]]] [| |] | ?] ls3]; try discriminate H.
           destruct ls3 as [| [? ? | [| p4]] ls4]; try discriminate H.
           injection H as <- <-. finish_out_hdr out_hdr_0_10_2_flat p4.
        -- injection H as <- <-. finish_out_hdr out_hdr_0_flat p2.
    + (* d1 = 2 *)
      destruct ls1 as [| [d2 b2 | k2] ls2]; try discriminate H.
      * destruct d2 as [|]; try discriminate H; destruct b2; try discriminate H.
        destruct ls2 as [| [? ? | [| p3]] ls3]; try discriminate H.
        injection H as <- <-. finish_out_hdr out_hdr_20_flat p3.
      * destruct k2 as [| p2]; try discriminate H.
        injection H as <- <-. finish_out_hdr out_hdr_2_flat p2.
  - injection H as <- <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite expandR_push10R, prependRepR_append_eq. apply sw_out15_rep_plus.
Qed.

Lemma outPassAux_base_star : forall cnt ls rs mv rb,
  encodeFlat (toFlatBase (bs_BR0 (el_single 3 sep0 :: ls) (er_single 0 0 :: er_single 0 0 :: rs)) rb)
    -[ tm ]->*
  encodeFlat (toFlatBase (fst (outPassAux cnt ls rs mv)) rb).
Proof.
  induction cnt as [| cnt IH]; intros ls rs mv rb; cbn [outPassAux].
  - apply evstep_refl.
  - destruct (outPassStep ls rs) as [[ls' rs'] |] eqn:Hs; [| apply evstep_refl].
    eapply evstep_trans; [apply progress_evstep, (outPassStep_base_sound _ _ _ _ rb Hs) | apply IH].
Qed.

Lemma outPassAux_base_plus : forall cnt ls rs rb,
  snd (outPassAux cnt ls rs false) = true ->
  encodeFlat (toFlatBase (bs_BR0 (el_single 3 sep0 :: ls) (er_single 0 0 :: er_single 0 0 :: rs)) rb)
    -[ tm ]->+
  encodeFlat (toFlatBase (fst (outPassAux cnt ls rs false)) rb).
Proof.
  intros [| cnt] ls rs rb H; cbn [outPassAux] in H.
  - discriminate H.
  - cbn [outPassAux]. destruct (outPassStep ls rs) as [[ls' rs'] |] eqn:Hs; [| discriminate H].
    eapply progress_evstep_trans;
      [exact (outPassStep_base_sound _ _ _ _ rb Hs) | apply outPassAux_base_star].
Qed.

Lemma inPassStep_base_sound : forall ls rs ls' rs' rb,
  inPassStep ls rs = Some (ls', rs') ->
  encodeFlat (toFlatBase (bs_BR ls (er_run10 N0 :: er_single 0 0 :: rs)) rb)
    -[ tm ]->+
  encodeFlat (toFlatBase (bs_BR ls' (er_run10 N0 :: er_single 0 0 :: rs')) rb).
Proof.
  intros ls rs ls' rs' rb H. unfold inPassStep in H.
  destruct rs as [| [[| [| [|]]] [|] | k1] rs1]; try discriminate H.
  - destruct rs1 as [| [[|] [|] | k2] rs2]; try discriminate H.
    + injection H as <- <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
      rewrite ?prependRepR_01, ?prependRepR_1. cbn [app]. apply in_20_flat.
    + destruct rs2 as [| [[|] [|] | ?] rs3]; try discriminate H.
      injection H as <- <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
      rewrite ?prependRepR_01, ?prependRepR_1. cbn [app].
      rewrite prependRepR_append_eq. apply in_2_10_flat.
  - injection H as <- <-. cbn [toFlatBase fsApp toFlat expandL expandR app].
    rewrite expandL_push10L, ?prependRepR_01, ?prependRepR_1. cbn [app].
    rewrite prependRepR_append_eq. apply sw_in7_rep_plus.
Qed.

Lemma inPassLocalAux_base_star : forall cnt ls rs mv rb,
  encodeFlat (toFlatBase (bs_BR ls (er_run10 N0 :: er_single 0 0 :: rs)) rb)
    -[ tm ]->*
  encodeFlat (toFlatBase (fst (inPassLocalAux cnt ls rs mv)) rb).
Proof.
  induction cnt as [| cnt IH]; intros ls rs mv rb; cbn [inPassLocalAux].
  - apply evstep_refl.
  - destruct (inPassStep ls rs) as [[ls' rs'] |] eqn:Hs; [| apply evstep_refl].
    eapply evstep_trans; [apply progress_evstep, (inPassStep_base_sound _ _ _ _ rb Hs) | apply IH].
Qed.

Lemma inPassLocalAux_base_plus : forall cnt ls rs rb,
  snd (inPassLocalAux cnt ls rs false) = true ->
  encodeFlat (toFlatBase (bs_BR ls (er_run10 N0 :: er_single 0 0 :: rs)) rb)
    -[ tm ]->+
  encodeFlat (toFlatBase (fst (inPassLocalAux cnt ls rs false)) rb).
Proof.
  intros [| cnt] ls rs rb H; cbn [inPassLocalAux] in H.
  - discriminate H.
  - cbn [inPassLocalAux]. destruct (inPassStep ls rs) as [[ls' rs'] |] eqn:Hs; [| discriminate H].
    eapply progress_evstep_trans;
      [exact (inPassStep_base_sound _ _ _ _ rb Hs) | apply inPassLocalAux_base_star].
Qed.

Lemma isEnd00_true : forall rs, isEnd00 rs = true -> rs = [er_single 0 0].
Proof.
  intros [| [[| z] [| o] | k] [| e2 rest]] H; try discriminate H; reflexivity.
Qed.

Lemma inPassFullAux_star : forall cnt ls rs mv,
  encodeFlat (toFlat (bs_BR ls (er_run10 N0 :: er_single 0 0 :: rs)))
    -[ tm ]->*
  encodeFlat (toFlat (fst (inPassFullAux cnt ls rs mv))).
Proof.
  induction cnt as [| cnt IH]; intros ls rs mv; cbn [inPassFullAux].
  - destruct (isEnd00 rs) eqn:He; [| apply evstep_refl].
    rewrite (isEnd00_true _ He).
    cbn [fst toFlat expandL expandR]. rewrite expandL_push10L, prependRepL_2, ?prependRepR_01, ?prependRepR_1.
    apply progress_evstep, in_top_end_flat.
  - destruct (isEnd00 rs) eqn:He.
    + rewrite (isEnd00_true _ He).
      cbn [fst toFlat expandL expandR]. rewrite expandL_push10L, prependRepL_2, ?prependRepR_01, ?prependRepR_1.
      apply progress_evstep, in_top_end_flat.
    + destruct (inPassStep ls rs) as [[ls' rs'] |] eqn:Hs; [| apply evstep_refl].
      pose proof (inPassStep_base_sound ls rs ls' rs' [] Hs) as H1.
      rewrite !toFlatBase_nil in H1.
      eapply evstep_trans; [apply progress_evstep, H1 | apply IH].
Qed.

Lemma inPassFullAux_plus : forall cnt ls rs,
  snd (inPassFullAux cnt ls rs false) = true ->
  encodeFlat (toFlat (bs_BR ls (er_run10 N0 :: er_single 0 0 :: rs)))
    -[ tm ]->+
  encodeFlat (toFlat (fst (inPassFullAux cnt ls rs false))).
Proof.
  intros [| cnt] ls rs H; cbn [inPassFullAux] in H |- *.
  - destruct (isEnd00 rs) eqn:He; [| discriminate H].
    rewrite (isEnd00_true _ He).
    cbn [fst toFlat expandL expandR]. rewrite expandL_push10L, prependRepL_2, ?prependRepR_01, ?prependRepR_1.
    apply in_top_end_flat.
  - destruct (isEnd00 rs) eqn:He.
    + rewrite (isEnd00_true _ He).
      cbn [fst toFlat expandL expandR]. rewrite expandL_push10L, prependRepL_2, ?prependRepR_01, ?prependRepR_1.
      apply in_top_end_flat.
    + destruct (inPassStep ls rs) as [[ls' rs'] |] eqn:Hs; [| discriminate H].
      pose proof (inPassStep_base_sound ls rs ls' rs' [] Hs) as H1.
      rewrite !toFlatBase_nil in H1.
      eapply progress_evstep_trans; [exact H1 | apply inPassFullAux_star].
Qed.

Lemma stepBR0Fast_base_sound : forall ls rs bs' rb,
  stepBR0Fast ls rs = Some bs' ->
  encodeFlat (toFlatBase (bs_BR0 ls rs) rb) -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros ls rs bs' rb H. unfold stepBR0Fast in H.
  destruct ls as [| [[| [| [| [|]]]] [| |] | ?] ls'],
           rs as [| [[|] [|] | ?] [| [[|] [|] | ?] rs']];
    try exact (tryBR0_base_sound _ _ _ rb H).
  unfold outPass in H. set (n := 128) in H. clearbody n.
  destruct (outPassAux n ls' rs' false) as [b_out mv] eqn:Hout.
  destruct mv.
  - injection H as <-.
    pose proof (outPassAux_base_plus n ls' rs' rb) as Hp.
    rewrite Hout in Hp. exact (Hp eq_refl).
  - exact (tryBR0_base_sound _ _ _ rb H).
Qed.

Lemma stepBRLocalFast_base_sound : forall ls rs bs' rb,
  stepBRLocalFast ls rs = Some bs' ->
  encodeFlat (toFlatBase (bs_BR ls rs) rb) -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros ls rs bs' rb H. unfold stepBRLocalFast in H.
  destruct rs as [| [? ? | [|]] rs1]; try discriminate H.
  destruct rs1 as [| [[|] [|] | ?] rs']; try discriminate H.
  unfold inPassLocal in H. set (n := 128) in H. clearbody n.
  destruct (inPassLocalAux n ls rs' false) as [b_out mv] eqn:Hin.
  destruct mv.
  - injection H as <-.
    pose proof (inPassLocalAux_base_plus n ls rs' rb) as Hp.
    rewrite Hin in Hp. exact (Hp eq_refl).
  - exact (tryBR_base_sound _ _ _ rb H).
Qed.

Lemma stepBRFullFast_sound : forall ls rs bs',
  stepBRFullFast ls rs = Some bs' ->
  encodeFlat (toFlat (bs_BR ls rs)) -[ tm ]->+ encodeFlat (toFlat bs').
Proof.
  intros ls rs bs' H. unfold stepBRFullFast in H.
  destruct rs as [| [? ? | [|]] rs1]; try discriminate H.
  destruct rs1 as [| [[|] [|] | ?] rs']; try discriminate H.
  unfold inPassFull in H. set (n := 128) in H. clearbody n.
  destruct (inPassFullAux n ls rs' false) as [b_out mv] eqn:Hin.
  destruct mv.
  - injection H as <-.
    pose proof (inPassFullAux_plus n ls rs') as Hp.
    rewrite Hin in Hp. exact (Hp eq_refl).
  - pose proof (tryBR_base_sound ls (er_run10 N0 :: er_single 0 0 :: rs') bs' [] H) as Hb.
    rewrite !toFlatBase_nil in Hb. exact Hb.
Qed.

Lemma stepCRFast_sound : forall ls rs bs',
  stepCRFast ls rs = Some bs' ->
  encodeFlat (toFlat (bs_CR ls rs)) -[ tm ]->+ encodeFlat (toFlat bs').
Proof.
  intros ls rs bs' H. unfold stepCRFast in H.
  destruct ls as [| [d b | [| p]] ls'], rs as [| e rs'];
    try (pose proof (tryCR_base_sound _ _ _ [] H) as Hb; rewrite !toFlatBase_nil in Hb; exact Hb).
  unfold outPass in H. set (n := 128) in H. clearbody n.
  injection H as <-.
  unfold toFlat at 1. rewrite expandL_peel2, prependRepL_2. cbn [expandR].
  eapply progress_evstep_trans.
  - apply topOut_flat.
  - pose proof (outPassAux_base_star n (peel10L (N.pred (Npos p)) ls') [er_single 0 0] true []) as Hs.
    rewrite !toFlatBase_nil in Hs. exact Hs.
Qed.

Lemma stepSuper_some : forall bs bs',
  stepSuper bs = Some bs' -> encodeFlat (toFlat bs) -[ tm ]->+ encodeFlat (toFlat bs').
Proof.
  intros bs bs' H.
  destruct bs as [| ls rs | ls rs | ls rs | ls rs | ls rs | ls rs | ls rs]; cbn [stepSuper] in H.
  - exact (step1Elem_some _ _ H).
  - discriminate H.
  - destruct (tryAL ls rs) eqn:Ht;
      [injection H as <-; pose proof (tryAL_base_sound _ _ _ [] Ht) as Hb; rewrite !toFlatBase_nil in Hb; exact Hb
      | exact (step1Elem_some _ _ H)].
  - destruct (stepBRFullFast ls rs) eqn:Ht;
      [injection H as <-; exact (stepBRFullFast_sound _ _ _ Ht) | exact (step1Elem_some _ _ H)].
  - destruct (stepBR0Fast ls rs) eqn:Ht;
      [injection H as <-; pose proof (stepBR0Fast_base_sound _ _ _ [] Ht) as Hb; rewrite !toFlatBase_nil in Hb; exact Hb
      | exact (step1Elem_some _ _ H)].
  - destruct (stepCRFast ls rs) eqn:Ht;
      [injection H as <-; exact (stepCRFast_sound _ _ _ Ht) | exact (step1Elem_some _ _ H)].
  - exact (step1Elem_some _ _ H).
  - exact (step1Elem_some _ _ H).
Qed.

Lemma miniStep_base_sound : forall bs bs' rb,
  miniStep bs = Some bs' ->
  encodeFlat (toFlatBase bs rb) -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros bs bs' rb H.
  destruct bs as [| ls rs | ls rs | ls rs | ls rs | ls rs | ls rs | ls rs]; cbn [miniStep] in H.
  - discriminate H.
  - discriminate H.
  - destruct (tryAL ls rs) eqn:Ht; [injection H as <-; exact (tryAL_base_sound _ _ _ rb Ht) |].
    destruct (has3R rs) eqn:H3; [| discriminate H].
    exact (step1Elem_base_some (bs_AL ls rs) bs' rb ltac:(discriminate) (has3R_len rs H3) H).
  - destruct (stepBRLocalFast ls rs) eqn:Ht; [injection H as <-; exact (stepBRLocalFast_base_sound _ _ _ rb Ht) |].
    destruct (has3R rs) eqn:H3; [| discriminate H].
    exact (step1Elem_base_some (bs_BR ls rs) bs' rb ltac:(discriminate) (has3R_len rs H3) H).
  - destruct (stepBR0Fast ls rs) eqn:Ht; [injection H as <-; exact (stepBR0Fast_base_sound _ _ _ rb Ht) |].
    destruct (has3R rs) eqn:H3; [| discriminate H].
    exact (step1Elem_base_some (bs_BR0 ls rs) bs' rb ltac:(discriminate) (has3R_len rs H3) H).
  - destruct (tryCR ls rs) eqn:Ht; [injection H as <-; exact (tryCR_base_sound _ _ _ rb Ht) |].
    destruct (has3R rs) eqn:H3; [| discriminate H].
    exact (step1Elem_base_some (bs_CR ls rs) bs' rb ltac:(discriminate) (has3R_len rs H3) H).
  - destruct (has3R rs) eqn:H3; [| discriminate H].
    exact (step1Elem_base_some (bs_DL ls rs) bs' rb ltac:(discriminate) (has3R_len rs H3) H).
  - destruct (has3R rs) eqn:H3; [| discriminate H].
    exact (step1Elem_base_some (bs_ER ls rs) bs' rb ltac:(discriminate) (has3R_len rs H3) H).
Qed.

Ltac ml_star_step H IH :=
  cbn [miniLoop] in H;
  lazymatch type of H with
  | match miniStep ?b with Some _ => _ | None => None end = Some _ =>
    let bs1 := fresh "bs1" in
    let Hm := fresh "Hm" in
    destruct (miniStep b) as [bs1 |] eqn:Hm; [| discriminate H];
    eapply evstep_trans;
      [apply progress_evstep, (miniStep_base_sound _ _ _ Hm) | exact (IH _ _ _ H)]
  end.

Lemma miniLoop_star : forall rem bs t2 rb,
  miniLoop rem bs true = Some t2 ->
  encodeFlat (toFlatBase bs rb) -[ tm ]->*
    encodeFlat (fs_BR (prependRepL 2%N (expandL t2)) ((1, 0) :: (0, 0) :: rb)).
Proof.
  induction rem as [| rem IH]; intros bs t2 rb H.
  - cbn [miniLoop] in H. discriminate H.
  - destruct bs as [| ? ? | ? ? | ls rs | ? ? | ? ? | ? ? | ? ?]; try (ml_star_step H IH).
    destruct ls as [| [? ? | [| p]] ls']; try (ml_star_step H IH).
    destruct rs as [| [? ? | [|]] [| [[|] [|] | ?] [|]]]; try (ml_star_step H IH).
    cbn [miniLoop] in H. injection H as <-. unfold toFlatBase, fsApp, toFlat.
    rewrite expandL_peel2. cbn [expandR app]. rewrite ?prependRepR_01, ?prependRepR_1. apply evstep_refl.
Qed.

Ltac ml_plus_step H :=
  cbn [miniLoop] in H;
  lazymatch type of H with
  | match miniStep ?b with Some _ => _ | None => None end = Some _ =>
    let bs1 := fresh "bs1" in
    let Hm := fresh "Hm" in
    destruct (miniStep b) as [bs1 |] eqn:Hm; [| discriminate H];
    eapply progress_evstep_trans;
      [exact (miniStep_base_sound _ _ _ Hm) | exact (miniLoop_star _ _ _ _ H)]
  end.

Lemma miniLoop_sound : forall rem bs t2 rb,
  miniLoop rem bs false = Some t2 ->
  encodeFlat (toFlatBase bs rb) -[ tm ]->+
    encodeFlat (fs_BR (prependRepL 2%N (expandL t2)) ((1, 0) :: (0, 0) :: rb)).
Proof.
  intros [| rem] bs t2 rb H.
  - cbn [miniLoop] in H. discriminate H.
  - destruct bs as [| ? ? | ? ? | ls rs | ? ? | ? ? | ? ? | ? ?]; try (ml_plus_step H).
    destruct ls as [| [? ? | [| p]] ls']; try (ml_plus_step H).
    destruct rs as [| [? ? | [|]] [| [[|] [|] | ?] [|]]]; try (ml_plus_step H).
    cbn [miniLoop] in H. discriminate H.
Qed.

Lemma iterMiniStep_star : forall n bs bs' rb,
  iterMiniStep n bs = Some bs' ->
  encodeFlat (toFlatBase bs rb) -[ tm ]->* encodeFlat (toFlatBase bs' rb).
Proof.
  induction n as [| n IH]; intros bs bs' rb H; cbn [iterMiniStep] in H.
  - injection H as <-. apply evstep_refl.
  - destruct (miniStep bs) as [bs1 |] eqn:Hm; [| discriminate H].
    eapply evstep_trans; [apply progress_evstep, (miniStep_base_sound _ _ rb Hm) | exact (IH _ _ rb H)].
Qed.

Lemma iterMiniStep_plus : forall n bs bs' rb,
  iterMiniStep (S n) bs = Some bs' ->
  encodeFlat (toFlatBase bs rb) -[ tm ]->+ encodeFlat (toFlatBase bs' rb).
Proof.
  intros n bs bs' rb H. cbn [iterMiniStep] in H.
  destruct (miniStep bs) as [bs1 |] eqn:Hm; [| discriminate H].
  eapply progress_evstep_trans;
    [exact (miniStep_base_sound _ _ rb Hm) | exact (iterMiniStep_star n bs1 bs' rb H)].
Qed.

Lemma iterStepSuper_star : forall n bs bs',
  iterStepSuper n bs = Some bs' ->
  encodeFlat (toFlat bs) -[ tm ]->* encodeFlat (toFlat bs').
Proof.
  induction n as [| n IH]; intros bs bs' H; cbn [iterStepSuper] in H.
  - injection H as <-. apply evstep_refl.
  - destruct (stepSuper bs) as [bs1 |] eqn:Hs; [| discriminate H].
    eapply evstep_trans; [apply progress_evstep, (stepSuper_some _ _ Hs) | exact (IH _ _ H)].
Qed.

Lemma iterStepSuper_plus : forall n bs bs',
  iterStepSuper (S n) bs = Some bs' ->
  encodeFlat (toFlat bs) -[ tm ]->+ encodeFlat (toFlat bs').
Proof.
  intros n bs bs' H. cbn [iterStepSuper] in H.
  destruct (stepSuper bs) as [bs1 |] eqn:Hs; [| discriminate H].
  eapply progress_evstep_trans;
    [exact (stepSuper_some _ _ Hs) | exact (iterStepSuper_star n bs1 bs' H)].
Qed.

End M137Ext.

Module M137Sec56.
Import M137 M137Ext.
Arguments push10R : simpl never.
Arguments push10L : simpl never.
Arguments peel10L : simpl never.
Arguments bumpLElem : simpl never.
(* ========================================================================= *)
(* 5. Universal Passive-Block Conjugacy (PAtom & 1-Token Transducer)         *)
(* ========================================================================= *)

Definition TailBounce (ls1 ls2 : list (nat * Sep3)) : Prop :=
  forall rb : list (nat * nat),
    encodeFlat (fs_BR0 ((3, sep0) :: ls1) ((0, 0) :: (0, 0) :: rb))
      -[ tm ]->+
    encodeFlat (fs_BR (prependRepL 2%N ls2) ((1, 0) :: (0, 0) :: rb)).

Inductive TailBounces : N -> list (nat * Sep3) -> list (nat * Sep3) -> Prop :=
| tb_zero (ls : list (nat * Sep3)) : TailBounces 0%N ls ls
| tb_one {ls1 ls2 : list (nat * Sep3)} : TailBounce ls1 ls2 -> TailBounces 1%N ls1 ls2
| tb_trans {n1 n2 : N} {ls1 ls2 ls3 : list (nat * Sep3)} :
    TailBounces n1 ls1 ls2 -> TailBounces n2 ls2 ls3 -> TailBounces (n1 + n2)%N ls1 ls3.

Lemma tailBounce_frame_run : forall (m : N) {ls1 ls2 : list (nat * Sep3)},
  TailBounce ls1 ls2 -> TailBounce (prependRepL m ls1) (prependRepL m ls2).
Proof.
  intros m ls1 ls2 H rb.
  eapply evstep_progress_trans; [apply sw_out15_rep |].
  eapply progress_evstep_trans; [exact (H (prependRepR m rb)) |].
  pose proof (sw_in7_rep m (prependRepL 2%N ls2) rb) as H3.
  rewrite <- prependRepL_add in H3.
  replace (m + 2)%N with (2 + m)%N in H3 by lia.
  rewrite prependRepL_add in H3.
  exact H3.
Qed.

Lemma tailBounces_frame_run : forall (m : N) {n : N} {ls1 ls2 : list (nat * Sep3)},
  TailBounces n ls1 ls2 -> TailBounces n (prependRepL m ls1) (prependRepL m ls2).
Proof.
  intros m n ls1 ls2 H.
  induction H as [ls | ls1 ls2 Hb | n1 n2 ls1 ls2 ls3 _ IH1 _ IH2].
  - apply tb_zero.
  - exact (tb_one (tailBounce_frame_run m Hb)).
  - exact (tb_trans IH1 IH2).
Qed.

Inductive Fin3 : Type := f3_0 | f3_1 | f3_2.

Definition f3Val (x : Fin3) : nat :=
  match x with
  | f3_0 => 0
  | f3_1 => 1
  | f3_2 => 2
  end.

Definition hdrR (prev : Fin3) (rs : list (nat * nat)) : list (nat * nat) :=
  match prev with
  | f3_0 => (0, 1) :: rs
  | f3_1 => (0, 0) :: (0, 0) :: rs
  | f3_2 => (0, 0) :: (1, 0) :: rs
  end.

Lemma shift_out_step : forall (d nxt prev : Fin3) ls rs,
  encodeFlat (fs_BR0 ((f3Val d + 2, sep0) :: (f3Val nxt, sep0) :: ls) (hdrR prev rs))
    -[ tm ]->+
  encodeFlat (fs_BR0 ((f3Val nxt + 2, sep0) :: ls) (hdrR d ((f3Val prev, 0) :: rs))).
Proof.
  intros [] [] [] [| [? ?] ?] [| [? ?] ?]; apply (iterStepFlat_plus 4); reflexivity.
Qed.

Fixpoint listToL (xs : list Fin3) : list (nat * Sep3) :=
  match xs with
  | [] => []
  | x :: rest => (f3Val x, sep0) :: listToL rest
  end.

Fixpoint listToR (xs : list Fin3) : list (nat * nat) :=
  match xs with
  | [] => []
  | x :: rest => (f3Val x, 0) :: listToR rest
  end.

Lemma listToL_append : forall a b, listToL (a ++ b) = listToL a ++ listToL b.
Proof.
  induction a as [| x xs IH]; intros b; [reflexivity | cbn [app listToL]; rewrite IH; reflexivity].
Qed.

Lemma listToR_append : forall a b, listToR (a ++ b) = listToR a ++ listToR b.
Proof.
  induction a as [| x xs IH]; intros b; [reflexivity | cbn [app listToR]; rewrite IH; reflexivity].
Qed.

Lemma shift_out_list : forall xs (d prev : Fin3) ls rs,
  encodeFlat (fs_BR0 ((f3Val d + 2, sep0) :: (listToL xs ++ (1, sep0) :: (1, sep0) :: ls)) (hdrR prev rs))
    -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    (hdrR f3_1 (listToR (rev xs) ++ [(f3Val d, 0); (f3Val prev, 0)] ++ rs))).
Proof.
  induction xs as [| x xs IH]; intros d prev ls rs; cbn [listToL rev app].
  - eapply progress_trans.
    + exact (shift_out_step d f3_1 prev ((1, sep0) :: ls) rs).
    + exact (shift_out_step f3_1 f3_1 d ls ((f3Val prev, 0) :: rs)).
  - eapply progress_trans.
    + exact (shift_out_step d x prev (listToL xs ++ (1, sep0) :: (1, sep0) :: ls) rs).
    + pose proof (IH x d ls ((f3Val prev, 0) :: rs)) as H2.
      rewrite listToR_append in *. cbn [listToR app] in *.
      rewrite <- ?app_assoc. cbn [app].
      exact H2.
Qed.

Inductive PAtom : Type :=
| pa_r (n : N)
| pa_z2
| pa_zr2 (a : N).

Definition prependF3_1 (n : N) (xs : list Fin3) : list Fin3 :=
  N.iter n (cons f3_1) xs.

Arguments prependF3_1 : simpl never.

Lemma prependF3_1_0 : forall xs, prependF3_1 0%N xs = xs.
Proof. reflexivity. Qed.

Lemma prependF3_1_succ : forall n xs, prependF3_1 (N.succ n) xs = f3_1 :: prependF3_1 n xs.
Proof. intros n xs. unfold prependF3_1. apply N_iter_succ. Qed.

Lemma prependF3_1_cons : forall n xs, prependF3_1 n (f3_1 :: xs) = f3_1 :: prependF3_1 n xs.
Proof. intros n xs. unfold prependF3_1. apply N_iter_swap. Qed.

Lemma prependF3_1_append : forall n xs ys,
  prependF3_1 n xs ++ ys = prependF3_1 n (xs ++ ys).
Proof.
  intros n. pattern n. apply N.peano_ind.
  - intros xs ys. reflexivity.
  - intros n' IH xs ys. rewrite !prependF3_1_succ. cbn [app]. rewrite IH. reflexivity.
Qed.

Lemma rev_prependF3_1 : forall n xs,
  rev (prependF3_1 n xs) = rev xs ++ prependF3_1 n [].
Proof.
  intros n. pattern n. apply N.peano_ind.
  - intros xs. rewrite !prependF3_1_0, app_nil_r. reflexivity.
  - intros n' IH xs. rewrite !prependF3_1_succ.
    cbn [rev]. rewrite IH, <- app_assoc, prependF3_1_append. cbn [app].
    rewrite prependF3_1_cons, <- prependF3_1_succ. reflexivity.
Qed.

Lemma listToL_rep1 : forall n xs,
  listToL (prependF3_1 n xs) = prependRepL n (listToL xs).
Proof.
  intros n. pattern n. apply N.peano_ind.
  - intros xs. rewrite prependF3_1_0, prependRepL_0. reflexivity.
  - intros n' IH xs. rewrite prependF3_1_succ, prependRepL_succ.
    cbn [listToL f3Val]. rewrite IH. reflexivity.
Qed.

Lemma listToR_rep1_app : forall n xs rs,
  listToR (prependF3_1 n xs) ++ rs = prependRepR n (listToR xs ++ rs).
Proof.
  intros n. pattern n. apply N.peano_ind.
  - intros xs rs. rewrite prependF3_1_0, prependRepR_0. reflexivity.
  - intros n' IH xs rs. rewrite prependF3_1_succ, prependRepR_succ.
    cbn [listToR f3Val app]. rewrite IH. reflexivity.
Qed.

Definition atomToFin3 (a : PAtom) : list Fin3 :=
  match a with
  | pa_r n => prependF3_1 (n + 1)%N []
  | pa_z2 => [f3_0; f3_2]
  | pa_zr2 k => f3_0 :: prependF3_1 (k + 1)%N [f3_2]
  end.

Fixpoint atomsToFin3 (ps : list PAtom) : list Fin3 :=
  match ps with
  | [] => []
  | a :: rest => atomToFin3 a ++ atomsToFin3 rest
  end.

Definition atomToElem (a : PAtom) : list ElemL :=
  match a with
  | pa_r n => [el_run10 n]
  | pa_z2 => [el_single 0 sep0; el_single 2 sep0]
  | pa_zr2 k => [el_single 0 sep0; el_run10 k; el_single 2 sep0]
  end.

Fixpoint atomsToElem (ps : list PAtom) : list ElemL :=
  match ps with
  | [] => []
  | a :: rest => atomToElem a ++ atomsToElem rest
  end.

Lemma expandL_atomToElem : forall a, expandL (atomToElem a) = listToL (atomToFin3 a).
Proof.
  intros [n | | k]; cbn [atomToElem atomToFin3 expandL listToL f3Val].
  - rewrite listToL_rep1. reflexivity.
  - reflexivity.
  - rewrite listToL_rep1. reflexivity.
Qed.

Lemma expandL_atomsToElem : forall ps, expandL (atomsToElem ps) = listToL (atomsToFin3 ps).
Proof.
  induction ps as [| a rest IH]; cbn [atomsToElem atomsToFin3 expandL].
  - reflexivity.
  - rewrite expandL_append, listToL_append, expandL_atomToElem, IH. reflexivity.
Qed.

Lemma inPass_atom : forall a ls rs,
  encodeFlat (fs_BR ls ((1, 0) :: (0, 0) :: (listToR (rev (atomToFin3 a)) ++ rs)))
    -[ tm ]->*
  encodeFlat (fs_BR (listToL (atomToFin3 a) ++ ls) ((1, 0) :: (0, 0) :: rs)).
Proof.
  intros [n | | k] ls rs.
  - cbn [atomToFin3]. rewrite rev_prependF3_1. cbn [rev app].
    rewrite listToR_rep1_app, listToL_rep1. cbn [listToR listToL app].
    rewrite prependRepL_append_eq. cbn [app].
    apply sw_in7_rep.
  - cbn [atomToFin3 rev listToR listToL f3Val app].
    apply progress_evstep, in_20_flat.
  - cbn [atomToFin3 rev]. rewrite rev_prependF3_1. cbn [rev app].
    rewrite <- ?app_assoc, prependF3_1_append. cbn [app listToR listToL f3Val].
    rewrite listToR_rep1_app, listToL_rep1. cbn [listToR listToL f3Val app].
    rewrite prependRepL_append_eq. cbn [app].
    apply progress_evstep, in_2_10_flat.
Qed.

Lemma inPass_atoms : forall ps ls rs,
  encodeFlat (fs_BR ls ((1, 0) :: (0, 0) :: (listToR (rev (atomsToFin3 ps)) ++ rs)))
    -[ tm ]->*
  encodeFlat (fs_BR (listToL (atomsToFin3 ps) ++ ls) ((1, 0) :: (0, 0) :: rs)).
Proof.
  induction ps as [| a rest IH]; intros ls rs; cbn [atomsToFin3 rev app].
  - apply evstep_refl.
  - rewrite rev_app_distr, listToR_append, <- app_assoc.
    eapply evstep_trans.
    + exact (IH ls (listToR (rev (atomToFin3 a)) ++ rs)).
    + rewrite listToL_append, <- app_assoc.
      exact (inPass_atom a (listToL (atomsToFin3 rest) ++ ls) rs).
Qed.

Lemma tailBounce_frame_atoms : forall (ps : list PAtom) {ls1 ls2 : list (nat * Sep3)},
  TailBounce ls1 ls2 ->
  TailBounce (expandL (atomsToElem ps) ++ prependRepL 2%N ls1)
             (expandL (atomsToElem ps) ++ prependRepL 2%N ls2).
Proof.
  intros ps ls1 ls2 H rb.
  rewrite !expandL_atomsToElem, !prependRepL_2.
  eapply progress_evstep_trans.
  - exact (shift_out_list (atomsToFin3 ps) f3_1 f3_1 ls1 rb).
  - cbn [hdrR f3Val].
    eapply evstep_trans.
    + apply progress_evstep.
      exact (H (listToR (rev (atomsToFin3 ps)) ++ [(1, 0); (1, 0)] ++ rb)).
    + eapply evstep_trans.
      * rewrite <- ?app_assoc.
        exact (inPass_atoms ps (prependRepL 2%N ls2) ([(1, 0); (1, 0)] ++ rb)).
      * rewrite prependRepL_2.
        pose proof (sw_in7_rep 2%N (listToL (atomsToFin3 ps) ++ (1, sep0) :: (1, sep0) :: ls2) rb) as H4.
        rewrite prependRepR_2, prependRepL_2 in H4.
        exact H4.
Qed.

Lemma tailBounces_frame_atoms : forall (ps : list PAtom) {n : N} {ls1 ls2 : list (nat * Sep3)},
  TailBounces n ls1 ls2 ->
  TailBounces n (expandL (atomsToElem ps) ++ prependRepL 2%N ls1)
                (expandL (atomsToElem ps) ++ prependRepL 2%N ls2).
Proof.
  intros ps n ls1 ls2 H.
  induction H as [ls | ls1 ls2 Hb | n1 n2 ls1 ls2 ls3 _ IH1 _ IH2].
  - apply tb_zero.
  - exact (tb_one (tailBounce_frame_atoms ps Hb)).
  - exact (tb_trans IH1 IH2).
Qed.

Lemma topWrap_one : forall (k : N) {ls1 ls2 : list (nat * Sep3)},
  TailBounce ls1 ls2 ->
  encodeFlat (fs_CR (prependRepL (k + 2)%N ls1) [])
    -[ tm ]->+
  encodeFlat (fs_CR (prependRepL (k + 4)%N ls2) []).
Proof.
  intros k ls1 ls2 H.
  replace (k + 2)%N with (2 + k)%N by lia.
  rewrite prependRepL_add, prependRepL_2.
  eapply progress_evstep_trans; [apply topOut_flat |].
  eapply evstep_trans; [exact (sw_out15_rep k ls1 [(0, 0)]) |].
  eapply evstep_trans; [apply progress_evstep, (H (prependRepR k [(0, 0)])) |].
  eapply evstep_trans; [exact (sw_in7_rep k (prependRepL 2%N ls2) [(0, 0)]) |].
  apply progress_evstep.
  pose proof (in_top_end_flat (prependRepL k (prependRepL 2%N ls2))) as Hend.
  replace (k + 4)%N with (2 + (k + 2))%N by lia.
  rewrite !prependRepL_add, prependRepL_2.
  exact Hend.
Qed.

Lemma topWrap_bounces_aux : forall {n : N} {ls1 ls2 : list (nat * Sep3)},
  TailBounces n ls1 ls2 ->
  (n = 0%N /\ ls1 = ls2) \/
  ((0 < n)%N /\ forall k : N,
    encodeFlat (fs_CR (prependRepL (k + 2)%N ls1) [])
      -[ tm ]->+
    encodeFlat (fs_CR (prependRepL (k + 2 * n + 2)%N ls2) [])).
Proof.
  intros n ls1 ls2 H.
  induction H as [ls | ls1 ls2 Hb | n1 n2 ls1 ls2 ls3 _ IH1 _ IH2].
  - left. split; reflexivity.
  - right. split; [lia |].
    intros k. replace (k + 2 * 1 + 2)%N with (k + 4)%N by lia.
    exact (topWrap_one k Hb).
  - destruct IH1 as [[-> ->] | [Hp1 Hk1]].
    + destruct IH2 as [[-> ->] | [Hp2 Hk2]].
      * left. split; [lia | reflexivity].
      * right. split; [lia |].
        intros k. replace (k + 2 * (0 + n2) + 2)%N with (k + 2 * n2 + 2)%N by lia.
        exact (Hk2 k).
    + destruct IH2 as [[-> <-] | [Hp2 Hk2]].
      * right. split; [lia |].
        intros k. replace (k + 2 * (n1 + 0) + 2)%N with (k + 2 * n1 + 2)%N by lia.
        exact (Hk1 k).
      * right. split; [lia |].
        intros k.
        eapply progress_trans; [exact (Hk1 k) |].
        replace (k + 2 * (n1 + n2) + 2)%N with ((k + 2 * n1) + 2 * n2 + 2)%N by lia.
        exact (Hk2 (k + 2 * n1)%N).
Qed.

Lemma topWrap_bounces : forall {n : N} (k : N) {ls1 ls2 : list (nat * Sep3)},
  TailBounces n ls1 ls2 -> (0 < n)%N ->
  encodeFlat (fs_CR (prependRepL (k + 2)%N ls1) [])
    -[ tm ]->+
  encodeFlat (fs_CR (prependRepL (k + 2 * n + 2)%N ls2) []).
Proof.
  intros n k ls1 ls2 H Hpos.
  destruct (topWrap_bounces_aux H) as [[-> _] | [_ Hk]]; [lia | exact (Hk k)].
Qed.

(* ========================================================================= *)
(* 6. Bit-Slicing, decN, & N Prefix Algebra       *)
(* ========================================================================= *)

Definition div2N (n : N) : N :=
  match n with
  | N0 => 0%N
  | Npos (xO p) => Npos p
  | Npos (xI p) => Npos p
  | Npos xH => 0%N
  end.

Definition bit0N (n : N) : N :=
  match n with
  | N0 => 0%N
  | Npos (xO _) => 0%N
  | Npos (xI _) => 1%N
  | Npos xH => 1%N
  end.

Definition consBit (b hi : N) : N :=
  match hi with
  | N0 =>
    match b with
    | N0 => 0%N
    | _ => 1%N
    end
  | Npos p =>
    match b with
    | N0 => Npos (xO p)
    | _ => Npos (xI p)
    end
  end.

Fixpoint splitBits (k : nat) (n : N) : N * N :=
  match k with
  | 0 => (0%N, n)
  | S k' =>
    let b := bit0N n in
    let (lo', hi) := splitBits k' (div2N n) in
    (consBit b lo', hi)
  end.

Fixpoint joinBits (k : nat) (lo hi : N) : N :=
  match k with
  | 0 => hi
  | S k' => consBit (bit0N lo) (joinBits k' (div2N lo) hi)
  end.

Fixpoint pow2N (k : nat) : N :=
  match k with
  | 0 => 1%N
  | S k' => (2 * pow2N k')%N
  end.

Lemma bit0N_or : forall n, bit0N n = 0%N \/ bit0N n = 1%N.
Proof.
  intros [| [p | p |]]; cbn [bit0N]; auto.
Qed.

Lemma bit0_div2_eq : forall n, (bit0N n + 2 * div2N n)%N = n.
Proof.
  intros [| [p | p |]]; reflexivity.
Qed.

Lemma div2N_consBit : forall b x, div2N (consBit b x) = x.
Proof.
  intros [| ?] [| ?]; reflexivity.
Qed.

Lemma bit0N_consBit : forall b x,
  (b = 0%N \/ b = 1%N) -> bit0N (consBit b x) = b.
Proof.
  intros b [| p] [-> | ->]; reflexivity.
Qed.

Lemma consBit_bit0_div2 : forall n, consBit (bit0N n) (div2N n) = n.
Proof.
  intros [| [p | p |]]; reflexivity.
Qed.

Lemma splitBits_0 : forall k, splitBits k 0%N = (0%N, 0%N).
Proof.
  induction k as [| k' IH]; [reflexivity |].
  cbn [splitBits bit0N div2N]. rewrite IH. reflexivity.
Qed.

Lemma splitBits_joinBits : forall k lo hi,
  (lo < pow2N k)%N -> splitBits k (joinBits k lo hi) = (lo, hi).
Proof.
  induction k as [| k' IH]; intros lo hi Hlo; cbn [pow2N] in Hlo.
  - assert (lo = 0%N) as -> by lia. reflexivity.
  - cbn [joinBits splitBits].
    rewrite (bit0N_consBit (bit0N lo) _ (bit0N_or lo)).
    rewrite div2N_consBit.
    assert (Hdiv : (div2N lo < pow2N k')%N).
    { destruct (bit0N_or lo) as [Hb | Hb]; pose proof (bit0_div2_eq lo); lia. }
    rewrite (IH (div2N lo) hi Hdiv).
    rewrite consBit_bit0_div2. reflexivity.
Qed.

Lemma joinBits_eq0_false : forall k lo hi,
  (0 < lo)%N -> (lo < pow2N k)%N -> (joinBits k lo hi =? 0)%N = false.
Proof.
  intros k lo hi Hpos Hlt.
  destruct (joinBits k lo hi =? 0)%N eqn:Heq; [| reflexivity].
  apply N.eqb_eq in Heq.
  pose proof (splitBits_joinBits k lo hi Hlt) as Hs.
  rewrite Heq, splitBits_0 in Hs. injection Hs as Hlo _. lia.
Qed.

Fixpoint posBits (p : positive) : nat :=
  match p with
  | xH => 1
  | xO q => S (posBits q)
  | xI q => S (posBits q)
  end.

Definition nBits (n : N) : nat :=
  match n with
  | N0 => 0
  | Npos p => posBits p
  end.

Lemma div2N_bits_le : forall n, nBits (div2N n) <= nBits n.
Proof.
  intros [| [p | p |]]; cbn [div2N nBits posBits]; lia.
Qed.

Lemma div2N_bits_lt : forall n, n <> 0%N -> nBits (div2N n) < nBits n.
Proof.
  intros [| [p | p |]] H; [contradiction | | |]; cbn [div2N nBits posBits]; lia.
Qed.

Lemma splitBits_bits_le : forall k n, nBits (snd (splitBits k n)) <= nBits n.
Proof.
  induction k as [| k' IH]; intros n; cbn [splitBits snd].
  - lia.
  - destruct (splitBits k' (div2N n)) as [lo' hi] eqn:Hs.
    pose proof (IH (div2N n)) as H1. rewrite Hs in H1. cbn [snd] in H1 |- *.
    pose proof (div2N_bits_le n) as H2. lia.
Qed.

Lemma splitBits_bits_lt : forall k n, n <> 0%N -> nBits (snd (splitBits (S k) n)) < nBits n.
Proof.
  intros k n Hnz. cbn [splitBits].
  destruct (splitBits k (div2N n)) as [lo' hi] eqn:Hs.
  pose proof (splitBits_bits_le k (div2N n)) as H1. rewrite Hs in H1. cbn [snd] in H1 |- *.
  pose proof (div2N_bits_lt n Hnz) as H2. lia.
Qed.

Arguments joinBits : simpl never.
Arguments splitBits : simpl never.

Definition decHead (n : N) : option (ElemL * N) :=
  if (n =? 0)%N then None
  else
    let (tag, rest) := splitBits 4 n in
    if (tag <? 8)%N then
      if (tag <? 4)%N then
        if (tag =? 1)%N then Some (el_single 0 sep0, rest)
        else if (tag =? 2)%N then Some (el_single 2 sep0, rest)
        else if (tag =? 3)%N then Some (el_single 3 sep0, rest)
        else None
      else
        if (tag =? 4)%N then Some (el_single 0 sep1, rest)
        else if (tag =? 5)%N then Some (el_single 1 sep1, rest)
        else if (tag =? 6)%N then Some (el_single 2 sep1, rest)
        else Some (el_run10 0%N, rest)
    else
      if (tag <? 12)%N then
        if (tag =? 8)%N then Some (el_run10 1%N, rest)
        else if (tag =? 9)%N then Some (el_run10 2%N, rest)
        else if (tag =? 10)%N then Some (el_run10 3%N, rest)
        else Some (el_run10 4%N, rest)
      else
        if (tag =? 12)%N then Some (el_run10 5%N, rest)
        else if (tag =? 13)%N then Some (el_run10 6%N, rest)
        else if (tag =? 14)%N then Some (el_run10 8%N, rest)
        else
          let (k, rest2) := splitBits 24 rest in
          Some (el_run10 k, rest2).

Lemma decHead_bits_lt : forall n e r,
  decHead n = Some (e, r) -> nBits r < nBits n.
Proof.
  intros n e r H. unfold decHead in H.
  destruct (n =? 0)%N eqn:Hz; [discriminate H |].
  apply N.eqb_neq in Hz.
  pose proof (splitBits_bits_lt 3 n Hz) as Hlt4.
  destruct (splitBits 4 n) as [tag rest] eqn:Hs4. cbn [snd] in Hlt4.
  pose proof (splitBits_bits_le 24 rest) as Hle24.
  destruct (splitBits 24 rest) as [k rest2] eqn:Hs24. cbn [snd] in Hle24.
  repeat match goal with
  | H0 : (if ?c then _ else _) = Some _ |- _ => destruct c; try discriminate H0
  end; injection H as _ <-; lia.
Qed.

Fixpoint decNAux (fuel : nat) (n : N) : list ElemL :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match decHead n with
    | None => []
    | Some (e, r) => e :: decNAux fuel' r
    end
  end.

Definition decN (n : N) : list ElemL := decNAux (nBits n) n.

Lemma decNAux_eq : forall f1 f2 n,
  nBits n <= f1 -> nBits n <= f2 -> decNAux f1 n = decNAux f2 n.
Proof.
  induction f1 as [| f1' IH]; intros f2 n Hf1 Hf2.
  - destruct n as [| [p | p |]]; [| cbn [nBits posBits] in Hf1; lia ..].
    destruct f2 as [| f2']; reflexivity.
  - destruct f2 as [| f2'].
    + destruct n as [| [p | p |]]; [reflexivity | cbn [nBits posBits] in Hf2; lia ..].
    + cbn [decNAux].
      destruct (decHead n) as [[e r] |] eqn:Hd; [| reflexivity].
      pose proof (decHead_bits_lt n e r Hd) as Hlt.
      f_equal. apply IH; lia.
Qed.

Lemma decN_zero : decN 0%N = [].
Proof. reflexivity. Qed.

Lemma decN_of_decHead : forall n e r,
  decHead n = Some (e, r) -> decN n = e :: decN r.
Proof.
  intros n e r H. unfold decN.
  pose proof (decHead_bits_lt n e r H) as Hlt.
  destruct (nBits n) as [| fuel'] eqn:Hbn; [lia |].
  cbn [decNAux]. rewrite H. f_equal.
  apply decNAux_eq; lia.
Qed.

Definition eqSep3 (a b : Sep3) : bool :=
  match a, b with
  | sep0, sep0 | sep1, sep1 | sep2, sep2 => true
  | _, _ => false
  end.

Lemma eqSep3_sound : forall a b, eqSep3 a b = true -> a = b.
Proof.
  intros [] [] H; try reflexivity; discriminate H.
Qed.

Definition eqElemL (a b : ElemL) : bool :=
  match a, b with
  | el_single d1 b1, el_single d2 b2 => andb (Nat.eqb d1 d2) (eqSep3 b1 b2)
  | el_run10 k1, el_run10 k2 => (k1 =? k2)%N
  | _, _ => false
  end.

Lemma eqElemL_sound : forall a b, eqElemL a b = true -> a = b.
Proof.
  intros [d1 b1 | k1] [d2 b2 | k2] H; cbn [eqElemL] in H; try discriminate H.
  - apply andb_true_iff in H. destruct H as [Hd Hb].
    apply Nat.eqb_eq in Hd. pose proof (eqSep3_sound _ _ Hb). congruence.
  - apply N.eqb_eq in H. congruence.
Qed.

Fixpoint eqListL (xs ys : list ElemL) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => andb (eqElemL x y) (eqListL xs' ys')
  | _, _ => false
  end.

Lemma eqListL_sound : forall xs ys, eqListL xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] H; cbn [eqListL] in H;
    try reflexivity; try discriminate H.
  apply andb_true_iff in H. destruct H as [Hx Hxs].
  f_equal; [exact (eqElemL_sound _ _ Hx) | exact (IH _ Hxs)].
Qed.

Definition packRunOpt (k rest : N) : option N :=
  if (k <? 7)%N then Some (joinBits 4 (k + 7)%N rest)
  else if (k =? 8)%N then Some (joinBits 4 14%N rest)
  else if (k <? 16777216)%N then Some (joinBits 4 15%N (joinBits 24 k rest))
  else None.

Lemma packRunOpt_sound : forall k rest m,
  packRunOpt k rest = Some m -> decN m = el_run10 k :: decN rest.
Proof.
  intros k rest m H. unfold packRunOpt in H.
  destruct (k <? 7)%N eqn:H7.
  - injection H as <-. apply N.ltb_lt in H7.
    apply decN_of_decHead. unfold decHead.
    rewrite (joinBits_eq0_false 4 (k + 7)%N rest ltac:(lia) ltac:(cbn [pow2N]; lia)).
    rewrite (splitBits_joinBits 4 (k + 7)%N rest ltac:(cbn [pow2N]; lia)).
    assert (Hk : k = 0%N \/ k = 1%N \/ k = 2%N \/ k = 3%N \/ k = 4%N \/ k = 5%N \/ k = 6%N) by lia.
    destruct Hk as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; reflexivity.
  - destruct (k =? 8)%N eqn:H8.
    + injection H as <-. apply N.eqb_eq in H8. subst k.
      apply decN_of_decHead. unfold decHead.
      rewrite (joinBits_eq0_false 4 14%N rest ltac:(lia) ltac:(cbn [pow2N]; lia)).
      rewrite (splitBits_joinBits 4 14%N rest ltac:(cbn [pow2N]; lia)).
      reflexivity.
    + destruct (k <? 16777216)%N eqn:Hbig; [| discriminate H].
      injection H as <-. apply N.ltb_lt in Hbig.
      apply decN_of_decHead. unfold decHead.
      rewrite (joinBits_eq0_false 4 15%N (joinBits 24 k rest) ltac:(lia) ltac:(cbn [pow2N]; lia)).
      rewrite (splitBits_joinBits 4 15%N (joinBits 24 k rest) ltac:(cbn [pow2N]; lia)).
      assert (H24 : (k < pow2N 24)%N) by (change (pow2N 24) with 16777216%N; exact Hbig).
      rewrite (splitBits_joinBits 24 k rest H24).
      reflexivity.
Qed.

Definition unpackRun (n : N) : option (N * N) :=
  match decHead n with
  | Some (el_run10 k, rest) => Some (k, rest)
  | _ => None
  end.

Lemma unpackRun_sound : forall n k r,
  unpackRun n = Some (k, r) -> decN n = el_run10 k :: decN r.
Proof.
  intros n k r H. unfold unpackRun in H.
  destruct (decHead n) as [[[d b | k'] r'] |] eqn:Hd; try discriminate H.
  injection H as <- <-. exact (decN_of_decHead _ _ _ Hd).
Qed.

Definition stripRunN (ex cur : N) : option N :=
  if (ex =? 0)%N then None
  else match unpackRun cur with
  | None => None
  | Some (k, rest) =>
    let k1 := (k + 1)%N in
    if (k1 =? ex)%N then Some rest
    else if (ex <? k1)%N then packRunOpt (k - ex)%N rest
    else None
  end.

Lemma stripRunN_sound : forall ex cur rem,
  stripRunN ex cur = Some rem ->
  expandL (decN cur) = prependRepL ex (expandL (decN rem)).
Proof.
  intros ex cur rem H. unfold stripRunN in H.
  destruct (ex =? 0)%N eqn:H0; [discriminate H |].
  destruct (unpackRun cur) as [[k rest] |] eqn:Hu; [| discriminate H].
  rewrite (unpackRun_sound _ _ _ Hu).
  destruct ((k + 1)%N =? ex)%N eqn:He.
  - injection H as <-. apply N.eqb_eq in He. cbn [expandL]. rewrite He. reflexivity.
  - destruct (ex <? (k + 1)%N)%N eqn:Hlt; [| discriminate H].
    apply N.ltb_lt in Hlt.
    rewrite (packRunOpt_sound _ _ _ H). cbn [expandL].
    rewrite <- prependRepL_add. f_equal. lia.
Qed.

Definition pushRunN (ex tail : N) : option N :=
  if (ex =? 0)%N then Some tail
  else match unpackRun tail with
  | Some (k2, rest) => packRunOpt (ex + k2)%N rest
  | None => packRunOpt (ex - 1)%N tail
  end.

Lemma pushRunN_sound : forall ex tail out,
  pushRunN ex tail = Some out ->
  expandL (decN out) = prependRepL ex (expandL (decN tail)).
Proof.
  intros ex tail out H. unfold pushRunN in H.
  destruct (ex =? 0)%N eqn:H0.
  - injection H as <-. apply N.eqb_eq in H0. subst ex. reflexivity.
  - apply N.eqb_neq in H0.
    destruct (unpackRun tail) as [[k2 rest] |] eqn:Hu.
    + rewrite (packRunOpt_sound _ _ _ H), (unpackRun_sound _ _ _ Hu).
      cbn [expandL]. rewrite <- prependRepL_add. f_equal. lia.
    + rewrite (packRunOpt_sound _ _ _ H). cbn [expandL]. f_equal. lia.
Qed.

Definition stripZ0 (cur : N) : option N :=
  match decHead cur with
  | Some (el_single 0 sep0, r) => Some r
  | _ => None
  end.

Lemma stripZ0_sound : forall cur r,
  stripZ0 cur = Some r -> decN cur = el_single 0 sep0 :: decN r.
Proof.
  intros cur r H. unfold stripZ0 in H.
  destruct (decHead cur) as [[[[| ?] [| |] | ?] r'] |] eqn:Hd; try discriminate H.
  injection H as <-. exact (decN_of_decHead _ _ _ Hd).
Qed.

Definition stripZ2 (cur : N) : option N :=
  match decHead cur with
  | Some (el_single 2 sep0, r) => Some r
  | _ => None
  end.

Lemma stripZ2_sound : forall cur r,
  stripZ2 cur = Some r -> decN cur = el_single 2 sep0 :: decN r.
Proof.
  intros cur r H. unfold stripZ2 in H.
  destruct (decHead cur) as [[[[| [| [| ?]]] [| |] | ?] r'] |] eqn:Hd; try discriminate H.
  injection H as <-. exact (decN_of_decHead _ _ _ Hd).
Qed.

Lemma decN_cons_z0 : forall r, decN (joinBits 4 1%N r) = el_single 0 sep0 :: decN r.
Proof.
  intros r. apply decN_of_decHead. unfold decHead.
  rewrite (joinBits_eq0_false 4 1%N r ltac:(lia) ltac:(cbn [pow2N]; lia)).
  rewrite (splitBits_joinBits 4 1%N r ltac:(cbn [pow2N]; lia)).
  reflexivity.
Qed.

Lemma decN_cons_z2 : forall r, decN (joinBits 4 2%N r) = el_single 2 sep0 :: decN r.
Proof.
  intros r. apply decN_of_decHead. unfold decHead.
  rewrite (joinBits_eq0_false 4 2%N r ltac:(lia) ltac:(cbn [pow2N]; lia)).
  rewrite (splitBits_joinBits 4 2%N r ltac:(cbn [pow2N]; lia)).
  reflexivity.
Qed.

Definition stripAtomN (a : PAtom) (cur : N) : option N :=
  match a with
  | pa_r n =>
    match unpackRun cur with
    | Some (k, r) => if (k =? n)%N then Some r else None
    | None => None
    end
  | pa_z2 =>
    match stripZ0 cur with
    | None => None
    | Some r1 => stripZ2 r1
    end
  | pa_zr2 k =>
    match stripZ0 cur with
    | None => None
    | Some r1 =>
      match unpackRun r1 with
      | Some (k2, r2) => if (k2 =? k)%N then stripZ2 r2 else None
      | None => None
      end
    end
  end.

Lemma stripAtomN_sound : forall a cur rem,
  stripAtomN a cur = Some rem -> decN cur = atomToElem a ++ decN rem.
Proof.
  intros [n | | k] cur rem H; cbn [stripAtomN] in H.
  - destruct (unpackRun cur) as [[k' r] |] eqn:Hu; [| discriminate H].
    destruct (k' =? n)%N eqn:He; [| discriminate H].
    injection H as <-. apply N.eqb_eq in He. subst k'.
    exact (unpackRun_sound _ _ _ Hu).
  - destruct (stripZ0 cur) as [r1 |] eqn:H1; [| discriminate H].
    rewrite (stripZ0_sound _ _ H1), (stripZ2_sound _ _ H). reflexivity.
  - destruct (stripZ0 cur) as [r1 |] eqn:H1; [| discriminate H].
    destruct (unpackRun r1) as [[k2 r2] |] eqn:Hu; [| discriminate H].
    destruct (k2 =? k)%N eqn:He; [| discriminate H].
    apply N.eqb_eq in He. subst k2.
    rewrite (stripZ0_sound _ _ H1), (unpackRun_sound _ _ _ Hu), (stripZ2_sound _ _ H).
    reflexivity.
Qed.

Fixpoint stripAtomsExactN (ps : list PAtom) (cur : N) : option N :=
  match ps with
  | [] => Some cur
  | a :: rest =>
    match stripAtomN a cur with
    | None => None
    | Some r => stripAtomsExactN rest r
    end
  end.

Lemma stripAtomsExactN_sound : forall ps cur rem,
  stripAtomsExactN ps cur = Some rem -> decN cur = atomsToElem ps ++ decN rem.
Proof.
  induction ps as [| a rest IH]; intros cur rem H; cbn [stripAtomsExactN] in H.
  - injection H as <-. reflexivity.
  - destruct (stripAtomN a cur) as [r |] eqn:H1; [| discriminate H].
    cbn [atomsToElem]. rewrite (stripAtomN_sound _ _ _ H1), (IH _ _ H), <- app_assoc. reflexivity.
Qed.

Definition stripAtomsN (ps : list PAtom) (cur : N) : option N :=
  match stripAtomsExactN ps cur with
  | None => None
  | Some mid => stripRunN 2%N mid
  end.

Lemma stripAtomsN_sound : forall ps cur rem,
  stripAtomsN ps cur = Some rem ->
  expandL (decN cur) = expandL (atomsToElem ps) ++ prependRepL 2%N (expandL (decN rem)).
Proof.
  intros ps cur rem H. unfold stripAtomsN in H.
  destruct (stripAtomsExactN ps cur) as [mid |] eqn:H1; [| discriminate H].
  rewrite (stripAtomsExactN_sound _ _ _ H1), expandL_append, (stripRunN_sound _ _ _ H).
  reflexivity.
Qed.

Definition prependAtomN (a : PAtom) (tail : N) : option N :=
  match a with
  | pa_r n => packRunOpt n tail
  | pa_z2 => Some (joinBits 4 1%N (joinBits 4 2%N tail))
  | pa_zr2 k =>
    match packRunOpt k (joinBits 4 2%N tail) with
    | None => None
    | Some r2 => Some (joinBits 4 1%N r2)
    end
  end.

Lemma prependAtomN_sound : forall a tail out,
  prependAtomN a tail = Some out -> decN out = atomToElem a ++ decN tail.
Proof.
  intros [n | | k] tail out H; cbn [prependAtomN] in H.
  - exact (packRunOpt_sound _ _ _ H).
  - injection H as <-. rewrite decN_cons_z0, decN_cons_z2. reflexivity.
  - destruct (packRunOpt k (joinBits 4 2%N tail)) as [r2 |] eqn:Hp; [| discriminate H].
    injection H as <-. rewrite decN_cons_z0, (packRunOpt_sound _ _ _ Hp), decN_cons_z2.
    reflexivity.
Qed.

Fixpoint prependAtomsN (ps : list PAtom) (tail : N) : option N :=
  match ps with
  | [] => Some tail
  | a :: rest =>
    match prependAtomsN rest tail with
    | None => None
    | Some mid => prependAtomN a mid
    end
  end.

Lemma prependAtomsN_sound : forall ps tail out,
  prependAtomsN ps tail = Some out -> decN out = atomsToElem ps ++ decN tail.
Proof.
  induction ps as [| a rest IH]; intros tail out H; cbn [prependAtomsN] in H.
  - injection H as <-. reflexivity.
  - destruct (prependAtomsN rest tail) as [mid |] eqn:H1; [| discriminate H].
    cbn [atomsToElem]. rewrite (prependAtomN_sound _ _ _ H), (IH _ _ H1), <- app_assoc. reflexivity.
Qed.

Definition joinAtomsN (ps : list PAtom) (tail : N) : option N :=
  match pushRunN 2%N tail with
  | None => None
  | Some mid => prependAtomsN ps mid
  end.

Lemma joinAtomsN_sound : forall ps tail out,
  joinAtomsN ps tail = Some out ->
  expandL (decN out) = expandL (atomsToElem ps) ++ prependRepL 2%N (expandL (decN tail)).
Proof.
  intros ps tail out H. unfold joinAtomsN in H.
  destruct (pushRunN 2%N tail) as [mid |] eqn:H1; [| discriminate H].
  rewrite (prependAtomsN_sound _ _ _ H), expandL_append, (pushRunN_sound _ _ _ H1).
  reflexivity.
Qed.

End M137Sec56.

Module M137Certs.
Import M137 M137Ext M137Sec56.

(* Index by the frame id carried by the schedule. The order is the
   archived eight-bit catalogue order; the common leading frames are
   named once rather than copied under each trie leaf. *)
Section PeelCatalog.
Local Notation Z := pa_z2.
Local Notation P := pa_zr2.
Local Notation R0 := pa_r.
Definition lead_zz4 : list PAtom := [Z; Z; P 4].
Definition lead_z100 : list PAtom := [Z; P 100].
Definition lead_zr0z : list PAtom := [Z; R0 0; Z].
Definition lead_z2 : list PAtom := [Z; P 2].
Definition peelCatalog : list (list PAtom) := [
  [Z; Z; Z; Z; Z; Z]; [Z; Z; Z; Z; Z]; [Z; Z; Z; Z]; [Z; Z; Z]; [Z; Z; P 0; R0 0; Z; Z]; [Z; Z; P 0; R0 0; Z];
  [Z; Z; P 0]; [Z; Z; P 117]; [Z; Z; P 1]; [Z; Z; P 21]; [Z; Z; P 2]; (lead_zz4 ++ [Z; Z; Z; Z; Z; Z]);
  (lead_zz4 ++ [Z; Z; Z; Z; Z]); (lead_zz4 ++ [Z; Z; Z; Z]); (lead_zz4 ++ [Z; Z; P 0; R0 0; Z; Z]);
  (lead_zz4 ++ [Z; Z; P 0; R0 0; Z]); (lead_zz4 ++ [Z; Z; P 0]); (lead_zz4 ++ [Z; Z; R0 0; Z; R0 0; Z; Z]);
  (lead_zz4 ++ [Z; Z; R0 0; Z; R0 0; Z]); (lead_zz4 ++ [Z; Z; R0 0; Z]); (lead_zz4 ++ [Z; Z]);
  (lead_zz4 ++ [P 0; R0 0; Z; Z; Z; Z]); (lead_zz4 ++ [P 0; R0 0; Z; Z; Z]); (lead_zz4 ++ [P 0; R0 0; Z; Z]);
  (lead_zz4 ++ [P 0; R0 0; P 0; R0 0; Z; Z]); (lead_zz4 ++ [P 0; R0 0; P 0; R0 0; Z]); (lead_zz4 ++ [P 0; R0 0; P 0]);
  (lead_zz4 ++ [P 0]); (lead_zz4 ++ [R0 0; Z; R0 0; Z; Z; Z; Z]); (lead_zz4 ++ [R0 0; Z; R0 0; Z; Z; Z]);
  (lead_zz4 ++ [R0 0; Z; R0 0; Z; Z]); (lead_zz4 ++ [R0 0; Z; R0 0; P 0; R0 0; Z; Z]);
  (lead_zz4 ++ [R0 0; Z; R0 0; P 0; R0 0; Z]); (lead_zz4 ++ [R0 0; Z; R0 0; P 0]); (lead_zz4 ++ [R0 0; Z]);
  (lead_zz4 ++ []); [Z; Z; R0 0; Z; R0 0; Z; Z]; [Z; Z; R0 0; Z; R0 0; Z]; [Z; Z; R0 0; Z]; [Z; Z]; [Z; P 0; Z];
  [Z; P 0; R0 0; Z; Z]; [Z; P 0; R0 0; Z]; [Z; P 0]; (lead_z100 ++ [Z; Z; Z; Z; Z; Z]); (lead_z100 ++ [Z; Z; Z; Z; Z]);
  (lead_z100 ++ [Z; Z; Z; Z]); (lead_z100 ++ [Z; Z; P 0; R0 0; Z; Z]); (lead_z100 ++ [Z; Z; P 0; R0 0; Z]);
  (lead_z100 ++ [Z; Z; P 0]); (lead_z100 ++ [Z; Z; R0 0; Z; R0 0; Z; Z]); (lead_z100 ++ [Z; Z; R0 0; Z; R0 0; Z]);
  (lead_z100 ++ [Z; Z; R0 0; Z]); (lead_z100 ++ [Z; Z]); (lead_z100 ++ [P 0; R0 0; Z; Z; Z; Z]);
  (lead_z100 ++ [P 0; R0 0; Z; Z; Z]); (lead_z100 ++ [P 0; R0 0; Z; Z]); (lead_z100 ++ [P 0; R0 0; P 0; R0 0; Z; Z]);
  (lead_z100 ++ [P 0; R0 0; P 0; R0 0; Z]); (lead_z100 ++ [P 0; R0 0; P 0]); (lead_z100 ++ [P 0]);
  (lead_z100 ++ [R0 0; Z; R0 0; Z; Z; Z; Z]); (lead_z100 ++ [R0 0; Z; R0 0; Z; Z; Z]);
  (lead_z100 ++ [R0 0; Z; R0 0; Z; Z]); (lead_z100 ++ [R0 0; Z; R0 0; P 0; R0 0; Z; Z]);
  (lead_z100 ++ [R0 0; Z; R0 0; P 0; R0 0; Z]); (lead_z100 ++ [R0 0; Z; R0 0; P 0]); (lead_z100 ++ [R0 0; Z]);
  (lead_z100 ++ []); [Z; P 108]; [Z; P 1; Z; Z; Z; Z]; [Z; P 1; Z; Z; Z]; [Z; P 1; Z; Z]; [Z; P 1; P 0; R0 0; Z; Z];
  [Z; P 1; P 0; R0 0; Z]; [Z; P 1; P 0]; [Z; P 1; R0 0; Z; R0 0; Z; Z]; [Z; P 1; R0 0; Z; R0 0; Z]; [Z; P 1; R0 0; Z];
  [Z; P 1]; (lead_z2 ++ [Z; Z; Z; Z; Z; Z]); (lead_z2 ++ [Z; Z; Z; Z; Z]); (lead_z2 ++ [Z; Z; Z; Z]);
  (lead_z2 ++ [Z; Z; Z]); (lead_z2 ++ [Z; Z; P 0; R0 0; Z; Z]); (lead_z2 ++ [Z; Z; P 0; R0 0; Z]);
  (lead_z2 ++ [Z; Z; P 0]); (lead_z2 ++ [Z; Z; R0 0; Z; R0 0; Z; Z]); (lead_z2 ++ [Z; Z; R0 0; Z; R0 0; Z]);
  (lead_z2 ++ [Z; Z; R0 0; Z]); (lead_z2 ++ [Z; Z]); (lead_z2 ++ [Z]); (lead_z2 ++ [P 0; R0 0; Z; Z; Z; Z]);
  (lead_z2 ++ [P 0; R0 0; Z; Z; Z]); (lead_z2 ++ [P 0; R0 0; Z; Z]); (lead_z2 ++ [P 0; R0 0; Z]);
  (lead_z2 ++ [P 0; R0 0; P 0; R0 0; Z; Z]); (lead_z2 ++ [P 0; R0 0; P 0; R0 0; Z]); (lead_z2 ++ [P 0; R0 0; P 0]);
  (lead_z2 ++ [P 0]); (lead_z2 ++ [R0 0; Z; R0 0; Z; Z; Z; Z]); (lead_z2 ++ [R0 0; Z; R0 0; Z; Z; Z]);
  (lead_z2 ++ [R0 0; Z; R0 0; Z; Z]); (lead_z2 ++ [R0 0; Z; R0 0; Z]); (lead_z2 ++ [R0 0; Z; R0 0; P 0; R0 0; Z; Z]);
  (lead_z2 ++ [R0 0; Z; R0 0; P 0; R0 0; Z]); (lead_z2 ++ [R0 0; Z; R0 0; P 0]); (lead_z2 ++ [R0 0; Z]);
  (lead_z2 ++ []); [Z; P 4; Z; Z]; [Z; P 4]; [Z; P 72]; [Z; P 84]; [Z; P 96]; (lead_zr0z ++ [Z; Z; Z]);
  (lead_zr0z ++ [Z; Z]); (lead_zr0z ++ [Z]); (lead_zr0z ++ [P 0]); (lead_zr0z ++ [P 125]); (lead_zr0z ++ [P 1]);
  (lead_zr0z ++ [P 27]); (lead_zr0z ++ [P 2; Z; Z; Z; Z]); (lead_zr0z ++ [P 2; Z; Z; Z]); (lead_zr0z ++ [P 2; Z; Z]);
  (lead_zr0z ++ [P 2; Z]); (lead_zr0z ++ [P 2; P 0; R0 0; Z; Z]); (lead_zr0z ++ [P 2; P 0; R0 0; Z]);
  (lead_zr0z ++ [P 2; P 0]); (lead_zr0z ++ [P 2; R0 0; Z; R0 0; Z; Z]); (lead_zr0z ++ [P 2; R0 0; Z; R0 0; Z]);
  (lead_zr0z ++ [P 2; R0 0; Z]); (lead_zr0z ++ [P 2]); (lead_zr0z ++ [P 3915]); (lead_zr0z ++ [R0 0; Z; Z]);
  (lead_zr0z ++ [R0 0; Z]); (lead_zr0z ++ []); [Z; R0 0; P 0; Z]; [Z; R0 0; P 0; P 5; Z; Z]; [Z; R0 0; P 0; P 5; Z];
  [Z; R0 0; P 0; P 5]; [Z; R0 0; P 0; R0 0; Z; Z]; [Z; R0 0; P 0; R0 0; Z]; [Z; R0 0; P 0]; [Z; R0 0; P 1];
  [Z; R0 0; P 2]; [Z]; [P 0; Z]; [P 0; P 0; Z; Z]; [P 0; P 0; Z]; [P 0; P 0]; [P 0; P 4; Z; Z]; [P 0; P 4];
  [P 0; P 5; Z; Z; Z; Z]; [P 0; P 5; Z; Z; Z]; [P 0; P 5; Z; Z]; [P 0; P 5; P 0; R0 0; Z; Z]; [P 0; P 5; P 0; R0 0; Z];
  [P 0; P 5; P 0]; [P 0; P 5; R0 0; Z; R0 0; Z; Z]; [P 0; P 5; R0 0; Z; R0 0; Z]; [P 0; P 5; R0 0; Z]; [P 0; P 5];
  [P 0; R0 0; Z; Z; Z; Z]; [P 0; R0 0; Z; Z; Z]; [P 0; R0 0; Z; Z]; [P 0; R0 0; Z]; [P 0; R0 0; P 0; R0 0; Z; Z];
  [P 0; R0 0; P 0; R0 0; Z]; [P 0; R0 0; P 0]; [P 0]; [P 11730945]; [P 11; Z; R0 0; Z; P 1]; [P 11; Z]; [P 11]; [P 128];
  [P 131]; [P 1; P 4; Z; Z; Z; Z]; [P 1; P 4; Z; Z; Z]; [P 1; P 4; Z; Z]; [P 1; P 4; P 0; R0 0; Z; Z];
  [P 1; P 4; P 0; R0 0; Z]; [P 1; P 4; P 0]; [P 1; P 4; R0 0; Z; R0 0; Z; Z]; [P 1; P 4; R0 0; Z; R0 0; Z];
  [P 1; P 4; R0 0; Z]; [P 1; P 4]; [P 21]; [P 24]; [P 2]; [P 30]; [P 33]; [P 386567]; [P 3921]; [P 3; Z; Z]; [P 3; Z];
  [P 3]; [P 4; Z; Z]; [P 4; Z]; [P 4]; [P 5; Z; Z; Z; Z; Z; Z]; [P 5; Z; Z; Z; Z; Z]; [P 5; Z; Z; Z; Z]; [P 5; Z; Z; Z];
  [P 5; Z; Z; P 0; R0 0; Z; Z]; [P 5; Z; Z; P 0; R0 0; Z]; [P 5; Z; Z; P 0]; [P 5; Z; Z; R0 0; Z; R0 0; Z; Z];
  [P 5; Z; Z; R0 0; Z; R0 0; Z]; [P 5; Z; Z; R0 0; Z]; [P 5; Z; Z]; [P 5; Z]; [P 5; P 0; R0 0; Z; Z; Z; Z];
  [P 5; P 0; R0 0; Z; Z; Z]; [P 5; P 0; R0 0; Z; Z]; [P 5; P 0; R0 0; Z]; [P 5; P 0; R0 0; P 0; R0 0; Z; Z];
  [P 5; P 0; R0 0; P 0; R0 0; Z]; [P 5; P 0; R0 0; P 0]; [P 5; P 0]; [P 5; R0 0; Z; R0 0; Z; Z; Z; Z];
  [P 5; R0 0; Z; R0 0; Z; Z; Z]; [P 5; R0 0; Z; R0 0; Z; Z]; [P 5; R0 0; Z; R0 0; Z];
  [P 5; R0 0; Z; R0 0; P 0; R0 0; Z; Z]; [P 5; R0 0; Z; R0 0; P 0; R0 0; Z]; [P 5; R0 0; Z; R0 0; P 0]; [P 5; R0 0; Z];
  [P 5]
].
End PeelCatalog.

Definition getPeel (pid : N) : option (list PAtom) :=
  nth_error peelCatalog (N.to_nat pid).

Definition d7_c0 : list N := [
  0x15%N; 0x555%N; 0x646%N; 0x15%N;
  0x15555%N; 0x20000010013%N; 0xa016ea%N; 0x1a46%N;
  0x15%N; 0x5%N; 0x2027%N; 0x2a46%N;
  0x1%N; 0x1%N; 0x155555%N; 0x80000080ed%N;
  0x3e46%N; 0x4%N; 0x1022ef2810919%N; 0x1%N;
  0x55%N; 0x6053%N; 0x102a572a00000204f400000809680000180dd000004019800000800000a02f%N; 0x5a46%N;
  0x2000002013%N; 0x6246%N; 0x8114f9%N; 0x4035800000800000a067%N;
  0x155037112aa05e46%N; 0x24073%N; 0xa076fa%N; 0x7a46%N;
  0x15%N; 0x200000203b%N; 0x8646%N; 0x1035a00000408b%N;
  0xaaa08dd2%N; 0x1%N; 0x6097%N; 0x9a46%N;
  0x1%N; 0x1%N; 0x1035a000004043%N; 0x55232800000829d000002051a00000609f%N;
  0x15%N; 0x60b3%N; 0xb646%N; 0xa0000020bb%N;
  0x2a919%N; 0x154000004186800001029d000003051a00000809f%N; 0x1555055492a82fa59418d4caaaa0a80a5505e072aa82b279%N; 0x1000001065a000004093%N;
  0xce46%N; 0xaa465000001053a0000040a3%N; 0x2aa82a039541793caaa0d646%N
].
Definition d7_c1 : list N := [
  0xaaaa82a4995417a54a0c52e55550548d2a82f47955415a44aaaa0a9325505e9b28314e941b27ca0000020d3%N; 0xde46%N; 0x2aa82a039541793caaa0c246%N; 0xaaa0a9d25505f0f2831919%N;
  0x800002032c000004000005075800001000000c0e7%N; 0xaaaaa82ab395417da4a0c6d65555055612a82fb1955415d94aaaa0aada5505f6f2831b8941b5cca0ee4a55%N; 0xd079800005000001c0e3%N; 0xf646%N;
  0x55555%N; 0x20000020ff%N; 0x10246%N; 0x1035a000004107%N;
  0x10a46%N; 0x2aa82a039541793caaa10e46%N; 0x800001032d000003075a000008113%N; 0x11646%N;
  0xaaaaaa82a7d95417bf4a0c5fe5555054f32a82f7a955415bdcaaaa0aa025505f03283182941b41ca11a46%N; 0xaa46%N; 0x2aa82a039541793caaa12246%N; 0x2000002832c000008000006075800001800000e127%N;
  0x155555055372a82f9c9418cecaaaa0aa625505f332aa82b9a95554154f4aa0be7e5063412836a1942513ca00000211f%N; 0x12e46%N; 0x15%N; 0x1c00000b09b8000040000018133%N;
  0x42754caaa0fa46%N; 0xd000003c13f%N; 0xa142be%N; 0x14646%N;
  0x15%N; 0x206b%N; 0x15246%N; 0x2aa82a039541793caaa15646%N;
  0x800001032d000003075a00000815b%N; 0x15e46%N; 0x2aaaaa82a5e95417afca0c58e5555054a52a82f53955415ad4aaaa0a99a5505ecf28316b941b364a000002163%N; 0x216646%N;
  0x284a2b9%N; 0x1548ca0000020a7%N
].
Definition d7_c2 : list N := [
  0x2aa82a039541793caaa17246%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a1778e%N; 0x217b%N; 0x5f919%N;
  0x2800000860d0000020b7a00000616b%N; 0x8e46%N; 0x2aa82a039541793caaa18a46%N; 0x800001032d000003075a00000818f%N;
  0x19246%N; 0x555555054bd2a82f5f9418b1caaaa0a94a5505ea72aa82b5a9555415334aa0bd9e5062d728366c9%N; 0x10000010cda000004197%N; 0x19e46%N;
  0xaa84aab9434564aa186b6%N; 0xa1a6f6%N; 0x21ab%N; 0x1ae46%N;
  0x1%N; 0x1%N; 0x555%N; 0x20000021bf%N;
  0x1c246%N; 0x1035a0000041c7%N; 0x1ca46%N; 0x2aa82a039541793caaa1ce46%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a1d38e%N; 0x61d7%N; 0x21daa6%N; 0x21df%N;
  0x1e246%N; 0x1%N; 0x1%N; 0x1555%N;
  0x20000021f3%N; 0x1f646%N; 0x1035a0000041fb%N; 0x1fe46%N;
  0x2aa82a039541793caaa20246%N; 0x800001032d000003075a000008207%N; 0x20a46%N; 0x10000010cda00000420f%N;
  0x21246%N; 0x84a4f9%N; 0x310da000008217%N; 0x21e46%N;
  0xaaa000002223%N; 0x889919%N; 0x1035a000004067%N; 0x22e46%N;
  0x2aa82a039541793caaa23246%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a2378e%N; 0x623b%N; 0x23e46%N;
  0x1%N; 0x1%N; 0x110da0000041a3%N
].
Definition d7_c3 : list N := [
  0x93919%N; 0x1540000044a6800001092d000003123a000008243%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a1278e%N; 0x625b%N;
  0x25e46%N; 0xa000002263%N; 0xaaaa24ca6551325528952b9%N; 0x5555%N;
  0x200000226f%N; 0x27246%N; 0x1035a000004277%N; 0x27a46%N;
  0x2aa82a039541793caaa27e46%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a2838e%N; 0x6287%N; 0x28a46%N;
  0x127232800000892d000002123a00000628f%N; 0x2aa893039544c93caaa29246%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a1138e%N; 0x629b%N;
  0x29e46%N; 0x1540000044a6800001092d000003123a0000082a3%N; 0x555126e92a899879454c8ca000002297%N; 0x127232800000892d000002123a0000062a3%N;
  0xaaaa24e32551331b28a98e9555449b94aa265ce555156e928aa919%N; 0xaaaa893a69544cd3ca2a6a25555127452a899a3955455d24a2aaa655555126092a899059454834aaaa24c0255132032aa8ab029555449924aa2649651524d28a5279%N; 0x8000020adc000004000005159800001000000c26b000003000001c45600000800000407bc0000140000090f580000300000141e7%N; 0x1da46%N;
  0x127232800000892d000002123a0000062bf%N; 0x2aa893039544c93caaa2c246%N
].
Definition d7_c4 : list N := [
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca2c646%N; 0x55555554498c4aa264665152352aaa893159544c8b4aaa2ac5e5154372aaaa8930e9544c87ca2a4425555126172a8990c95545586caaaa24c46551322528a91394528a4aaaaa24c7e551324128a92195554498e4aa264765551563d28aa22945911ca2ba1e%N; 0xb80000362cf%N; 0x2d246%N;
  0x1%N; 0x2da46%N; 0x1035a0000042df%N; 0x2e246%N;
  0x2aa82a039541793caaa2e646%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a2eb8e%N; 0x62ef%N; 0x2f246%N;
  0x127232800000892d000002123a0000062f7%N; 0x2aa893039544c93caaa2fa46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca2fe46%N; 0x8000010add000003159a000008303%N;
  0x30646%N
].
Definition d7_c5 : list N := [
  0x2aaaaaa893609544cb0ca2a58a5555126b92a8995d955455af4a2a98e55555126a92a899559454ab4aaaa24d4255132a32aa8ab529555449abcaa265625152b328a55a95555449b44aa265a65152d52aaa893649544cb2caaa2ad9a5154d728b26c9%N; 0x1000002187a00000630b%N; 0x20453e%N; 0x2317%N;
  0x31a46%N; 0x2aa82a039541793caaa31e46%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a3238e%N; 0x6327%N;
  0x32a46%N; 0x127232800000892d000002123a00000632f%N; 0x2aa893039544c93caaa33246%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca33646%N;
  0x20000028adc000008000006159800001800000e33b%N; 0x233ef2%N; 0xa000002343%N; 0x15%N;
  0x200000234b%N; 0x34e46%N; 0x1035a000004353%N; 0x35646%N;
  0x2aa82a039541793caaa35a46%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a35f8e%N; 0x6363%N; 0x36646%N;
  0x127232800000892d000002123a00000636b%N; 0x2aa893039544c93caaa36e46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca37246%N
].
Definition d7_c6 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a3778e%N; 0x437b%N; 0x5546fc3ca34646%N; 0xa0000030383%N;
  0x2386a6555188f128b5919%N; 0x7c00002007160000fa00004086ec0001f80000820db80003f80001061b3%N; 0xa38f02%N; 0x39246%N;
  0x15%N; 0xa00000209f%N; 0x15541501caa39c9e%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a3a38e%N;
  0x63a7%N; 0x3aa46%N; 0x127232800000892d000002123a0000063af%N; 0x2aa893039544c93caaa3b246%N;
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca3b646%N; 0x8000010add000003159a0000083bb%N; 0x3be46%N; 0x1000001187a0000043c3%N;
  0x3c646%N; 0x1%N; 0x20000023cf%N; 0x3d246%N;
  0x1035a0000043d7%N; 0x3da46%N; 0x2aa82a039541793caaa3de46%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a3e38e%N;
  0x63e7%N; 0x3ea46%N; 0x127232800000892d000002123a0000063ef%N; 0x2aa893039544c93caaa3f246%N
].
Definition d7_c7 : list N := [
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca3f646%N; 0x20000028adc000008000006159800001800000e3fb%N; 0x8ff4f9%N; 0x2201a0000063cb%N;
  0x2a406ee%N; 0xa40aba%N; 0x240f%N; 0x41246%N;
  0x1%N; 0x1%N; 0x15541501caa0bc9e55%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a4238e%N;
  0x6427%N; 0x42a46%N; 0x127232800000892d000002123a00000642f%N; 0x2aa893039544c93caaa43246%N;
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca43646%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a43b8e%N; 0x643f%N; 0x44246%N;
  0x1%N; 0x5000001225a000004447%N; 0x1000001187a00000430b%N; 0x45246%N;
  0x1201a000004457%N
].
Definition d7_c8 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a3fb8e%N; 0x645f%N; 0x46246%N; 0xa000002467%N;
  0x15522d112a91a8e95548b434a44e1e%N; 0x15%N; 0x44000015239800009000002c46f%N; 0x15541501caa0bc9e555%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a47b8e%N; 0x647f%N; 0x48246%N; 0x127232800000892d000002123a000006487%N;
  0x2aa893039544c93caaa48a46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca48e46%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a4938e%N; 0x6497%N;
  0x49a46%N; 0x1%N; 0x116919%N; 0x15%N;
  0x15522c4f2a91a919%N
].
Definition d7_c9 : list N := [
  0x1000003257a0000084ab000001000001494e000004000003128c00000c000007225800002000001049f%N; 0x5549604ca4761e%N; 0x3c80000fa4b7%N; 0x4ba46%N;
  0x22d232800000928d000002225a000006447%N; 0x2aaa916c19548d614aaa4c30e%N; 0x24c7%N; 0x4ca46%N;
  0x1%N; 0x1%N; 0x1000002257a0000064ab400001094e000002000002928c000008000006225800001800000e447%N; 0x4da46%N;
  0x81ad%N; 0x4e246%N; 0x2aa82a039541793caaa4e646%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a4eb8e%N;
  0x64ef%N; 0x4f246%N; 0x127232800000892d000002123a0000064f7%N; 0x2aa893039544c93caaa4fa46%N;
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca4fe46%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a5038e%N; 0x6507%N; 0x50a46%N;
  0x22d232800000928d000002225a00000650f%N; 0x15555522cf72a91a7c9554a241ca4de46%N; 0x555054072a82f27955%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a51b8e%N;
  0x651f%N; 0x52246%N; 0x127232800000892d000002123a000006527%N
].
Definition d7_c10 : list N := [
  0x2aa893039544c93caaa52a46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca52e46%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a5338e%N; 0x6537%N;
  0x53a46%N; 0x4000005257800001000000c4ab000003000001c94e000008000004128c000014000009225800003000001453f%N; 0xaaaa916899548d454aaa5122e52a0e92945919%N; 0x44a8e00001c000009135c00003c00001326980000800000284cf%N;
  0x1%N; 0x6027%N; 0x55246%N; 0xa000002557%N;
  0x15541501caa5589e%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a55f8e%N; 0x6563%N; 0x56646%N;
  0x127232800000892d000002123a00000656b%N; 0x2aa893039544c93caaa56e46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca57246%N
].
Definition d7_c11 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a5778e%N; 0x657b%N; 0x57e46%N; 0x1000002257a0000064ab400001094e000002000002928c000008000006225800001800000e583%N;
  0x58646%N; 0x5555522cb52a91a5b9554a2364a00000258b%N; 0x258e46%N; 0x14a815ca000002593%N;
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a33b8e%N; 0x659b%N; 0x59e46%N; 0x22d232800000928d000002225a0000065a3%N;
  0x2aaa916d19548d694aaa5a78e%N; 0x25ab%N; 0x554b5c3ca59646%N; 0x20000025b3%N;
  0x5b646%N; 0x15541501caa0bc9e5%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a5bf8e%N; 0x65c3%N;
  0x5c646%N; 0x127232800000892d000002123a0000065cb%N; 0x2aa893039544c93caaa5ce46%N
].
Definition d7_c12 : list N := [
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca5d246%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a5d78e%N; 0x65db%N; 0x5de46%N;
  0x1000002257a0000064ab400001094e000002000002928c000008000006225800001800000e5e3%N; 0x5e646%N; 0xaaaaa4596a55234b72aa9446c9%N; 0x10000012f7a0000045eb%N;
  0x5f246%N; 0x9504f9%N; 0x12fda0000045f7%N; 0x97f4f9%N;
  0x22d232800000928d000002225a00000653f%N; 0x2aaa916d19548d694aaa6078e%N; 0x660b%N; 0x60e46%N;
  0x10000012f7a0000044df%N; 0x61646%N; 0x12fda00000461b%N; 0x1530f212aa9848f9%N;
  0x1%N; 0x28c4e00000e000005988c00002000000c301800004800001a5bb%N; 0x62a46%N; 0x555054072a82f279%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a6338e%N; 0x6637%N; 0x63a46%N; 0x127232800000892d000002123a00000663f%N;
  0x2aa893039544c93caaa64246%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca64646%N
].
Definition d7_c13 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a64b8e%N; 0x664f%N; 0x65246%N; 0x22d232800000928d000002225a000006657%N;
  0x2aaa916d19548d694aaa65b8e%N; 0x665f%N; 0x66246%N; 0x54c3c1caaa665de%N;
  0x200000266b%N; 0x66e46%N; 0x1%N; 0x533b800001000000c673%N;
  0x133d532aaa98b919%N; 0x7300001dccfe0000e800003c153c0001d4%N; 0x2682a65552a4ed292f919%N; 0xf4a0003d38d0e001e960007a7907c003d30000f5020d8007a68001ea2417%N;
  0xa68afe%N; 0x68e46%N; 0x15%N; 0xaaa2780e%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a69b8e%N; 0x669f%N; 0x6a246%N; 0x127232800000892d000002123a0000066a7%N;
  0x2aa893039544c93caaa6aa46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca6ae46%N
].
Definition d7_c14 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a6b38e%N; 0x66b7%N; 0x6ba46%N; 0x22d232800000928d000002225a0000066bf%N;
  0x2aaa916d19548d694aaa6c38e%N; 0x66c7%N; 0x6ca46%N; 0x54c3b64aaa6cd3e%N;
  0x200000106d3%N; 0x6d646%N; 0xa0000026db%N; 0x54c3b64aaa6653e%N;
  0x26e3%N; 0xaa6e49e%N; 0x20000086eb%N; 0x26e646%N;
  0x22d232800000928d000002225a0000065e3%N; 0x2aaa916d19548d694aaa6f78e%N; 0x66fb%N; 0x6fe46%N;
  0x54c3b64aaa7013e%N; 0x2707%N; 0x15554e14b4aa9bc9794dd93caa6de46%N; 0x470f%N;
  0x2aa7121e%N; 0x3880000ea717%N; 0x2aa82a039%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a71f8e%N;
  0x6723%N; 0x72646%N; 0x127232800000892d000002123a00000672b%N; 0x2aa893039544c93caaa72e46%N;
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca73246%N
].
Definition d7_c15 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a7378e%N; 0x673b%N; 0x73e46%N; 0x22d232800000928d000002225a000006743%N;
  0x2aaa916d19548d694aaa7478e%N; 0x674b%N; 0x74e46%N; 0x54c3b64aaa7513e%N;
  0x2757%N; 0x275a46%N; 0x1%N; 0xaa7089e5%N;
  0x8000011d9d0000033b1a00000875f%N; 0x76a46%N; 0xaaaaa709ee554de41ca76e46%N; 0x15541501caa0a09e%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a7778e%N; 0x677b%N; 0x77e46%N; 0x127232800000892d000002123a000006783%N;
  0x2aa893039544c93caaa78646%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca78a46%N
].
Definition d7_c16 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a78f8e%N; 0x6793%N; 0x79646%N; 0x22d232800000928d000002225a00000679b%N;
  0x2aaa916d19548d694aaa79f8e%N; 0x67a3%N; 0x7a646%N; 0x54c3b64aaa7a93e%N;
  0x27af%N; 0x27b246%N; 0x20000029d9c0000080000063b1800001800000e7b7%N; 0x15554e144caa9bc8b94f73a4a77246%N;
  0x67bf%N; 0x554f803ca71a1e%N; 0x7a38001e967c7%N; 0x7ca46%N;
  0x2aaaa7096a554de364a00000276f%N; 0x27d246%N; 0x14f715ca0000027d7%N; 0x22d232800000928d000002225a000006583%N;
  0x2aaa916d19548d694aaa7df8e%N; 0x67e3%N; 0x7e646%N; 0x54c3b64aaa7e93e%N;
  0x27ef%N; 0x27f246%N; 0x1555385a32aa7f78e%N; 0x27fb%N;
  0x554ffc3ca7da46%N; 0x2000004803%N; 0xaaa0a80e5%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a80b8e%N;
  0x680f%N; 0x81246%N; 0x127232800000892d000002123a000006817%N; 0x2aa893039544c93caaa81a46%N;
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca81e46%N
].
Definition d7_c17 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a8238e%N; 0x6827%N; 0x82a46%N; 0x22d232800000928d000002225a00000682f%N;
  0x2aaa916d19548d694aaa8338e%N; 0x6837%N; 0x83a46%N; 0x54c3b64aaa83d3e%N;
  0x2843%N; 0x284646%N; 0x8000011d9d0000033b1a00000884b%N; 0x84e46%N;
  0x55554e12d4aa9bc6c9%N; 0x100000142ba000004853%N; 0x85a46%N; 0x9ee4f9%N;
  0x1431a00000485f%N; 0x550c854a8061e%N; 0x1%N; 0x1bc00007343780003800000e886b%N;
  0x155%N; 0x2000002877%N; 0x87a46%N; 0x1035a00000487f%N;
  0xaaa8800e%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a8878e%N; 0x688b%N; 0x88e46%N;
  0x127232800000892d000002123a000006893%N; 0x2aa893039544c93caaa89646%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca89a46%N
].
Definition d7_c18 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a89f8e%N; 0x68a3%N; 0x8a646%N; 0x22d232800000928d000002225a0000068ab%N;
  0x2aaa916d19548d694aaa8af8e%N; 0x68b3%N; 0x8b646%N; 0x54c3b64aaa8b93e%N;
  0x28bf%N; 0x28c246%N; 0x1555385a32aa8c78e%N; 0x68cb%N;
  0x8ce46%N; 0xaaa0a80e55%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a8d78e%N; 0x68db%N;
  0x8de46%N; 0x127232800000892d000002123a0000068e3%N; 0x2aa893039544c93caaa8e646%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca8ea46%N
].
Definition d7_c19 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a8ef8e%N; 0x68f3%N; 0x8f646%N; 0x22d232800000928d000002225a0000068fb%N;
  0x2aaa916d19548d694aaa8ff8e%N; 0x6903%N; 0x90646%N; 0x54c3b64aaa9093e%N;
  0x290f%N; 0x291246%N; 0x8000011d9d0000033b1a000008917%N; 0x91a46%N;
  0x100000142ba00000491f%N; 0x92246%N; 0x1431a000004927%N; 0x5525364aaa8d13e%N;
  0x800000a92f%N; 0x93246%N; 0x1%N; 0x1%N;
  0x1555385a32aa75f8e%N; 0x6943%N; 0x94646%N; 0x5525364aaa9493e%N;
  0x294f%N; 0xaa9509e%N; 0x2000002957%N; 0x256919%N;
  0x295246%N; 0x1555385a32aa84b8e%N; 0x6967%N; 0x96a46%N;
  0x5525364aaa96d3e%N; 0x2973%N; 0x15552ea44aaa584f9%N; 0xe097b00006d00001c52be0000dc00003924fc0001bc00007349d80003800000e8937%N;
  0x97e46%N; 0x15%N; 0x1%N; 0xaaa1c80e%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a98f8e%N; 0x6993%N; 0x99646%N; 0x127232800000892d000002123a00000699b%N;
  0x2aa893039544c93caaa99e46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3ca9a246%N
].
Definition d7_c20 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714a9a78e%N; 0x69ab%N; 0x9ae46%N; 0x22d232800000928d000002225a0000069b3%N;
  0x2aaa916d19548d694aaa9b78e%N; 0x69bb%N; 0x9be46%N; 0x54c3b64aaa9c13e%N;
  0x29c7%N; 0x29ca46%N; 0x1555385a32aa9cf8e%N; 0x69d3%N;
  0x9d646%N; 0x5525364aaa9d93e%N; 0x29df%N; 0x29e246%N;
  0x1%N; 0xaa9749e5%N; 0x80000227bc0000040000054f5800001000000c9e7%N; 0x9f246%N;
  0x2aaa975b65552c374a0000029f7%N; 0xaaa22c0e%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14a9ff8e%N; 0x6a03%N;
  0xa0646%N; 0x127232800000892d000002123a000006a0b%N; 0x2aa893039544c93caaaa0e46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3caa1246%N
].
Definition d7_c21 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714aa178e%N; 0x6a1b%N; 0xa1e46%N; 0x22d232800000928d000002225a000006a23%N;
  0x2aaa916d19548d694aaaa278e%N; 0x6a2b%N; 0xa2e46%N; 0x54c3b64aaaa313e%N;
  0x2a37%N; 0x2a3a46%N; 0x1555385a32aaa3f8e%N; 0x6a43%N;
  0xa4646%N; 0x5525364aaaa493e%N; 0x2a4f%N; 0x2a5246%N;
  0x80000127bd0000034f5a000008a57%N; 0xa5a46%N; 0x2aaaa9756a5552c364a000002a5f%N; 0x26d3%N;
  0x2a6646%N; 0x1555385a32aaa6b8e%N; 0x6a6f%N; 0xa7246%N;
  0x5525364aaaa753e%N; 0x2a7b%N; 0x2a7e46%N; 0x2000002a7bc0000080000064f5800001800000ea83%N;
  0x2aa8656554c13caa9fa46%N; 0x3400000d8a8b%N; 0x2a3919%N; 0x15554bba32aaa578e%N;
  0x6a97%N; 0x2aa6459%N; 0x1%N; 0x55%N;
  0x2000002aa7%N; 0xaaa46%N; 0x1035a000004aaf%N; 0xaaaab00e%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14aab78e%N; 0x6abb%N; 0xabe46%N; 0x127232800000892d000002123a000006ac3%N;
  0x2aa893039544c93caaaac646%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3caaca46%N
].
Definition d7_c22 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714aacf8e%N; 0x6ad3%N; 0xad646%N; 0x22d232800000928d000002225a000006adb%N;
  0x2aaa916d19548d694aaaadf8e%N; 0x6ae3%N; 0xae646%N; 0x54c3b64aaaae93e%N;
  0x2aef%N; 0x2af246%N; 0x1555385a32aaaf78e%N; 0x6afb%N;
  0xafe46%N; 0x5525364aaab013e%N
].
Definition d8_c0 : list N := [
  0x2b07%N; 0x2b0a46%N; 0x80000127bd0000034f5a000008b0f%N; 0xb1246%N;
  0x555552ead4aaa586c9%N; 0x100000158da000004b17%N; 0xb1e46%N; 0xaa14f9%N;
  0x2593a000006b23%N; 0xb2a46%N; 0x5%N; 0x6959980003300000d4b2f%N;
  0x2cd919%N; 0x15%N; 0x1%N; 0xaaa3540e%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14ab478e%N; 0x6b4b%N; 0xb4e46%N; 0x127232800000892d000002123a000006b53%N;
  0x2aa893039544c93caaab5646%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cab5a46%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714ab5f8e%N; 0x6b63%N;
  0xb6646%N; 0x22d232800000928d000002225a000006b6b%N; 0x2aaa916d19548d694aaab6f8e%N; 0x6b73%N;
  0xb7646%N; 0x54c3b64aaab793e%N; 0x2b7f%N; 0x2b8246%N;
  0x1555385a32aab878e%N; 0x6b8b%N; 0xb8e46%N; 0x5525364aaab913e%N;
  0x2b97%N; 0x2b9a46%N; 0x15554bba32aab9f8e%N; 0x6ba3%N;
  0xba646%N; 0x1%N; 0x1%N; 0xaaa1fc0e%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14abb78e%N; 0x6bbb%N; 0xbbe46%N
].
Definition d8_c1 : list N := [
  0x127232800000892d000002123a000006bc3%N; 0x2aa893039544c93caaabc646%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cabca46%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714abcf8e%N;
  0x6bd3%N; 0xbd646%N; 0x22d232800000928d000002225a000006bdb%N; 0x2aaa916d19548d694aaabdf8e%N;
  0x6be3%N; 0xbe646%N; 0x54c3b64aaabe93e%N; 0x2bef%N;
  0x2bf246%N; 0x1555385a32aabf78e%N; 0x6bfb%N; 0xbfe46%N;
  0x5525364aaac013e%N; 0x2c07%N; 0x2c0a46%N; 0x80000127bd0000034f5a000008c0f%N;
  0xc1246%N; 0x100000158da000004c17%N; 0xc1a46%N; 0x1593a000004c1f%N;
  0x611232800000aecd0000025d7a000006bab%N; 0x15554bba32aaa838e%N; 0x6c2b%N; 0xc2e46%N;
  0xa000002c33%N; 0x2aab08039558693caaac2646%N; 0x15554bba32aa9e78e%N; 0x6c3f%N;
  0xc4246%N; 0x308919%N; 0x1540000058968000012ecd0000035d7a000008c47%N; 0x555610e92ab0d879589c8ca000002c3b%N;
  0x611232800000aecd0000025d7a000006c47%N; 0x2aaab088c95586c6cac4e3a5555610e52ab0d7395558aba4ac5246%N; 0x15554bba32aab0f8e%N; 0x6c5f%N;
  0xc6246%N; 0x611232800000aecd0000025d7a000006c67%N; 0x2aab08039558693caaac6a46%N
].
Definition d8_c2 : list N := [
  0x555610e92ab0d879589c8ca000002c6f%N; 0xaaaab08a695586d3cac4ea25555611452ab0da395558ad24ac72a655555610092ab0d059589834aaaac20025561a032aab15029555584124aac349656264d2b1b279%N; 0x18000006463b80003080000cac5b%N; 0x31e919%N;
  0x5%N; 0x2000002c83%N; 0xc8646%N; 0x1035a000004c8b%N;
  0xaaac8c0e%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14ac938e%N; 0x6c97%N; 0xc9a46%N;
  0x127232800000892d000002123a000006c9f%N; 0x2aa893039544c93caaaca246%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3caca646%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714acab8e%N;
  0x6caf%N; 0xcb246%N; 0x22d232800000928d000002225a000006cb7%N; 0x2aaa916d19548d694aaacbb8e%N;
  0x6cbf%N; 0xcc246%N; 0x54c3b64aaacc53e%N; 0x2ccb%N;
  0x2cce46%N; 0x1555385a32aacd38e%N; 0x6cd7%N; 0xcda46%N;
  0x5525364aaacdd3e%N; 0x2ce3%N; 0x2ce646%N
].
Definition d8_c3 : list N := [
  0x15554bba32aaceb8e%N; 0x6cef%N; 0xcf246%N; 0x611232800000aecd0000025d7a000006cf7%N;
  0x2aab08039558693caaacfa46%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cacfe46%N; 0x2aaaaab0839955869d4ac4cee55556106d2ab0d3795558a9c4ac70f2555556105f2ab0d30958998caaaac20b25561a5b2aab152e9555584194aac34ce5626692b1b3595555584204aac35065626852aaab083d955869f4aaac54fe5638872b40449%N; 0x1%N;
  0xaaa1500e%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14ad0f8e%N; 0x6d13%N; 0xd1646%N;
  0x127232800000892d000002123a000006d1b%N; 0x2aa893039544c93caaad1e46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cad2246%N
].
Definition d8_c4 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714ad278e%N; 0x6d2b%N; 0xd2e46%N; 0x22d232800000928d000002225a000006d33%N;
  0x2aaa916d19548d694aaad378e%N; 0x6d3b%N; 0xd3e46%N; 0x54c3b64aaad413e%N;
  0x2d47%N; 0x2d4a46%N; 0x1555385a32aad4f8e%N; 0x6d53%N;
  0xd5646%N; 0x5525364aaad593e%N; 0x2d5f%N; 0x2d6246%N;
  0x15554bba32aad678e%N; 0x6d6b%N; 0xd6e46%N; 0x611232800000aecd0000025d7a000006d73%N;
  0x2aab08039558693caaad7646%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cad7a46%N; 0xaaaac22325561b1b2b138e9555584394aac35ce55562ae92b1c919%N; 0x80000131dd0000036c1a000008d7f%N;
  0xd8646%N
].
Definition d8_c5 : list N := [
  0x2aaaaaab086095586b0cac4d8a5555610b92ab0d5d95558aaf4ac718e55555610a92ab0d559589ab4aaaac21425561aa32aab155295555842bcaac35625626b32b1b5a95555584344aac35a65626d52aaab086495586b2caaac559a5638d72b406c9%N; 0x1700000606c780002e80000c2d8b%N; 0x364919%N; 0xaaa3180e%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14ad9b8e%N; 0x6d9f%N; 0xda246%N; 0x127232800000892d000002123a000006da7%N;
  0x2aa893039544c93caaadaa46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cadae46%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714adb38e%N; 0x6db7%N;
  0xdba46%N; 0x22d232800000928d000002225a000006dbf%N; 0x2aaa916d19548d694aaadc38e%N; 0x6dc7%N;
  0xdca46%N; 0x54c3b64aaadcd3e%N; 0x2dd3%N; 0x2dd646%N
].
Definition d8_c6 : list N := [
  0x1555385a32aaddb8e%N; 0x6ddf%N; 0xde246%N; 0x5525364aaade53e%N;
  0x2deb%N; 0x2dee46%N; 0x15554bba32aadf38e%N; 0x6df7%N;
  0xdfa46%N; 0x611232800000aecd0000025d7a000006dff%N; 0x2aab08039558693caaae0246%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cae0646%N;
  0x2000002b1dc0000080000066c1800001800000ee0b%N; 0x2b83719%N; 0x1%N; 0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714ad7f8e%N;
  0x2e1b%N; 0xe1e46%N; 0x1%N; 0x1%N;
  0x1%N; 0x2e2f%N; 0xaaae300e%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14ae378e%N;
  0x6e3b%N; 0xe3e46%N; 0x127232800000892d000002123a000006e43%N; 0x2aa893039544c93caaae4646%N;
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cae4a46%N
].
Definition d8_c7 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714ae4f8e%N; 0x6e53%N; 0xe5646%N; 0x22d232800000928d000002225a000006e5b%N;
  0x2aaa916d19548d694aaae5f8e%N; 0x6e63%N; 0xe6646%N; 0x54c3b64aaae693e%N;
  0x2e6f%N; 0x2e7246%N; 0x1555385a32aae778e%N; 0x6e7b%N;
  0xe7e46%N; 0x5525364aaae813e%N; 0x2e87%N; 0x2e8a46%N;
  0x15554bba32aae8f8e%N; 0x6e93%N; 0xe9646%N; 0x611232800000aecd0000025d7a000006e9b%N;
  0x2aab08039558693caaae9e46%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3caea246%N; 0x80000131dd0000036c1a000008ea7%N; 0xeaa46%N;
  0x10000016c7a000004eaf%N; 0xeb246%N; 0x1706ef2bad919%N; 0x1%N;
  0x6e1b%N; 0x2ec0ae5%N; 0x5876380002a80000b2ebf0000560000169d760000ae00002db8ac00016000005c71380002c80000bae23%N; 0x3b2919%N;
  0x15%N; 0x1%N; 0x1%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14aedb8e%N;
  0x6edf%N; 0xee246%N; 0x127232800000892d000002123a000006ee7%N; 0x2aa893039544c93caaaeea46%N;
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3caeee46%N
].
Definition d8_c8 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714aef38e%N; 0x6ef7%N; 0xefa46%N; 0x22d232800000928d000002225a000006eff%N;
  0x2aaa916d19548d694aaaf038e%N; 0x6f07%N; 0xf0a46%N; 0x54c3b64aaaf0d3e%N;
  0x2f13%N; 0x2f1646%N; 0x1555385a32aaf1b8e%N; 0x6f1f%N;
  0xf2246%N; 0x5525364aaaf253e%N; 0x2f2b%N; 0x2f2e46%N;
  0x15554bba32aaf338e%N; 0x6f37%N; 0xf3a46%N; 0x611232800000aecd0000025d7a000006f3f%N;
  0x2aab08039558693caaaf4246%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3caf4646%N; 0x80000131dd0000036c1a000008f4b%N; 0xf4e46%N;
  0x10000016c7a000004f53%N; 0xf5646%N; 0xb834f9%N; 0x47af800000800000af5b%N;
  0xf6246%N; 0xaa000002f67%N; 0x555%N; 0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14af6f8e%N;
  0x6f73%N; 0xf7646%N; 0x127232800000892d000002123a000006f7b%N; 0x2aa893039544c93caaaf7e46%N;
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3caf8246%N
].
Definition d8_c9 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714af878e%N; 0x6f8b%N; 0xf8e46%N; 0x22d232800000928d000002225a000006f93%N;
  0x2aaa916d19548d694aaaf978e%N; 0x6f9b%N; 0xf9e46%N; 0x54c3b64aaafa13e%N;
  0x2fa7%N; 0x2faa46%N; 0x1555385a32aafaf8e%N; 0x6fb3%N;
  0xfb646%N; 0x5525364aaafb93e%N; 0x2fbf%N; 0x2fc246%N;
  0x15554bba32aafc78e%N; 0x6fcb%N; 0xfce46%N; 0x611232800000aecd0000025d7a000006fd3%N;
  0x2aab08039558693caaafd646%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cafda46%N; 0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714afdf8e%N; 0x6fe3%N;
  0xfe646%N; 0xa000002feb%N; 0x17afa000004eb7%N; 0x555fe13caafee46%N;
  0x1%N; 0x1%N; 0x7f9232800000bffd0000027fda000006feb%N
].
Definition d8_c10 : list N := [
  0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714ae0b8e%N; 0x7007%N; 0x100a46%N; 0xa00000300f%N;
  0xaaaabfc93956024a4aab0025655fe93caaf6a46%N; 0x2800000a9017%N; 0x406919%N; 0x5%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14b0238e%N; 0x7027%N; 0x102a46%N; 0x127232800000892d000002123a00000702f%N;
  0x2aa893039544c93caab03246%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cb03646%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714b03b8e%N; 0x703f%N;
  0x104246%N; 0x22d232800000928d000002225a000007047%N
].
Definition d8_c11 : list N := [
  0x2aaa916d19548d694aab04b8e%N; 0x704f%N; 0x105246%N; 0x54c3b64aab0553e%N;
  0x305b%N; 0x305e46%N; 0x1555385a32ab0638e%N; 0x7067%N;
  0x106a46%N; 0x5525364aab06d3e%N; 0x3073%N; 0x307646%N;
  0x15554bba32ab07b8e%N; 0x707f%N; 0x108246%N; 0x611232800000aecd0000025d7a000007087%N;
  0x2aab08039558693caab08a46%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cb08e46%N; 0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714b0938e%N; 0x7097%N;
  0x109a46%N; 0x3fc919%N; 0x15%N; 0x1557f84f2ac04919%N;
  0x1000004855800000800000b0a7000002000001a146000006000003bffc0000100000087fd800002800001309f%N; 0x2c2b709%N; 0x1%N; 0x7f9232800000bffd0000027fda00000709f%N;
  0x2aaabfcc49560262caab0bb1a%N; 0x30bf%N; 0x10c246%N; 0x1%N;
  0x1%N; 0xaaaaa0ab565505fad2831da955541564caa0bf2a555057a32aaa82add95417ef4a0c78a5%N; 0x70d3%N; 0x10d646%N;
  0x127232800000892d000002123a0000070db%N; 0x2aa893039544c93caab0de46%N
].
Definition d8_c12 : list N := [
  0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cb0e246%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714b0e78e%N; 0x70eb%N; 0x10ee46%N;
  0x22d232800000928d000002225a0000070f3%N; 0x2aaa916d19548d694aab0f78e%N; 0x70fb%N; 0x10fe46%N;
  0x54c3b64aab1013e%N; 0x3107%N; 0x310a46%N; 0x1555385a32ab10f8e%N;
  0x7113%N; 0x111646%N; 0x5525364aab1193e%N; 0x311f%N;
  0x312246%N; 0x15554bba32ab1278e%N; 0x712b%N; 0x112e46%N;
  0x611232800000aecd0000025d7a000007133%N; 0x2aab08039558693caab13646%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cb13a46%N
].
Definition d8_c13 : list N := [
  0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714b13f8e%N; 0x7143%N; 0x114646%N; 0x1000002855a0000070a74000012146000002000002bffc0000080000067fd800001800000f14b%N;
  0x114e46%N; 0x555557f8b52ac045b955600364a000003153%N; 0x315646%N; 0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714af4b8e%N;
  0x715f%N; 0x116246%N; 0x4000005855800001000000d0a7000003000001e1460000080000043ffc0000140000097fd8000030000015167%N; 0x55%N;
  0x155554156acaa0bf5a5063b52aaa82ac995417e54aaa0af465555055bb2a82fde9418f14b16f8e%N; 0x7173%N; 0x117646%N; 0x127232800000892d000002123a00000717b%N;
  0x2aa893039544c93caab17e46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cb18246%N
].
Definition d8_c14 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714b1878e%N; 0x718b%N; 0x118e46%N; 0x22d232800000928d000002225a000007193%N;
  0x2aaa916d19548d694aab1978e%N; 0x719b%N; 0x119e46%N; 0x54c3b64aab1a13e%N;
  0x31a7%N; 0x31aa46%N; 0x1555385a32ab1af8e%N; 0x71b3%N;
  0x11b646%N; 0x5525364aab1b93e%N; 0x31bf%N; 0x31c246%N;
  0x15554bba32ab1c78e%N; 0x71cb%N; 0x11ce46%N; 0x611232800000aecd0000025d7a0000071d3%N;
  0x2aab08039558693caab1d646%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cb1da46%N; 0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714b1df8e%N; 0x71e3%N;
  0x11e646%N; 0x7f9232800000bffd0000027fda0000071eb%N; 0x2aaabfcd195602694aab1ef8e%N; 0x31f3%N
].
Definition d8_c15 : list N := [
  0x2b1f49e558b4eb2c56919%N; 0x13a3f6000096000027c33c00013000005086580002680000a30c7%N; 0x47f919%N; 0x1%N;
  0x1%N; 0xaa0000020c3400000814e800001828d%N; 0xaaaaa0ab565505fad2831da955541564caa0bf2a555057a32aaa82add95417ef4b20f8a%N; 0x7213%N;
  0x121646%N; 0x127232800000892d000002123a00000721b%N; 0x2aa893039544c93caab21e46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cb22246%N;
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714b2278e%N; 0x722b%N; 0x122e46%N; 0x22d232800000928d000002225a000007233%N;
  0x2aaa916d19548d694aab2378e%N; 0x723b%N; 0x123e46%N; 0x54c3b64aab2413e%N;
  0x3247%N; 0x324a46%N; 0x1555385a32ab24f8e%N; 0x7253%N;
  0x125646%N; 0x5525364aab2593e%N; 0x325f%N; 0x326246%N;
  0x15554bba32ab2678e%N; 0x726b%N; 0x126e46%N; 0x611232800000aecd0000025d7a000007273%N;
  0x2aab08039558693caab27646%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cb27a46%N
].
Definition d8_c16 : list N := [
  0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714b27f8e%N; 0x7283%N; 0x128646%N; 0x1000002855a0000070a74000012146000002000002bffc0000080000067fd800001800000f28b%N;
  0x128e46%N; 0xaaaaaff16a55808b72aac006c9%N; 0x100000194ba000005293%N; 0x62d044b29a1e%N;
  0xb29e46%N; 0x1%N; 0x2aaabfcd195602694aab0bb8e%N; 0x72ab%N;
  0xacab2895%N; 0x1%N; 0x2aaaa82ad595417eb4a0c76a5555055932a82fca955415e8caaaa0ab765505fbd2831e29%N; 0x72bb%N;
  0x12be46%N; 0x127232800000892d000002123a0000072c3%N; 0x2aa893039544c93caab2c646%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cb2ca46%N
].
Definition d8_c17 : list N := [
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714b2cf8e%N; 0x72d3%N; 0x12d646%N; 0x22d232800000928d000002225a0000072db%N;
  0x2aaa916d19548d694aab2df8e%N; 0x72e3%N; 0x12e646%N; 0x54c3b64aab2e93e%N;
  0x32ef%N; 0x32f246%N; 0x1555385a32ab2f78e%N; 0x72fb%N;
  0x12fe46%N; 0x5525364aab3013e%N; 0x3307%N; 0x330a46%N;
  0x15554bba32ab30f8e%N; 0x7313%N; 0x131646%N; 0x611232800000aecd0000025d7a00000731b%N;
  0x2aab08039558693caab31e46%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cb32246%N; 0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714b3278e%N; 0x732b%N;
  0x132e46%N; 0x1000002855a0000070a74000012146000002000002bffc0000080000067fd800001800000f333%N; 0x133646%N; 0x100000194ba00000533b%N;
  0x133e46%N; 0x62d27ca000003343%N; 0x134646%N; 0x15957252aa00000334b%N;
  0x4d3919%N
].
Definition d8_c18 : list N := [
  0x15%N; 0x1100000489ab8000228000093353000046000012a56e00008e000025cacc00012000004c953800024800009b2a3%N; 0x4d6919%N; 0x2a800000830d000002053a0000060a3%N;
  0xaaaaa0ab565505fad2831da955541564caa0bf2a555057a32aaa82add95417ef4b3638a%N; 0x7367%N; 0x136a46%N; 0x127232800000892d000002123a00000736f%N;
  0x2aa893039544c93caab37246%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cb37646%N; 0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714b37b8e%N; 0x737f%N;
  0x138246%N; 0x22d232800000928d000002225a000007387%N; 0x2aaa916d19548d694aab38b8e%N; 0x738f%N;
  0x139246%N; 0x54c3b64aab3953e%N; 0x339b%N; 0x339e46%N;
  0x1555385a32ab3a38e%N; 0x73a7%N; 0x13aa46%N; 0x5525364aab3ad3e%N;
  0x33b3%N; 0x33b646%N; 0x15554bba32ab3bb8e%N; 0x73bf%N;
  0x13c246%N; 0x611232800000aecd0000025d7a0000073c7%N; 0x2aab08039558693caab3ca46%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cb3ce46%N
].
Definition d8_c19 : list N := [
  0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714b3d38e%N; 0x73d7%N; 0x13da46%N; 0x1000002855a0000070a74000012146000002000002bffc0000080000067fd800001800000f3df%N;
  0x13e246%N; 0x100000194ba0000053e7%N; 0x13ea46%N; 0x62d27ca0000033ef%N;
  0x13f246%N; 0x2b2ae4a55%N; 0x39fda0000093f7%N; 0x2cff6f9%N;
  0x1%N; 0x55000001061a0000040a7%N; 0xaaaaa0ab565505fad2831da955541564caa0bf2a555057a32aaa82add95417ef4b40b8a%N; 0x740f%N;
  0x141246%N; 0x127232800000892d000002123a000007417%N; 0x2aa893039544c93caab41a46%N; 0x155544994caa264aa5152572aaa893019544c814aaa2ac0e55551270b2a899869454c3cb41e46%N;
  0xaaaaaa24f5e55133b128a9d99555449e9caa26752555157ab28aada95555449e5caa2673251539b2aaa893c79544ce44aaa2af2655551279d2a899cf9454e84a2974655555127bf2a899e09454f0caaaa24f6e55133b92aa8abdd9455714b4238e%N; 0x7427%N; 0x142a46%N; 0x22d232800000928d000002225a00000742f%N
].
Definition d8_c20 : list N := [
  0x2aaa916d19548d694aab4338e%N; 0x7437%N; 0x143a46%N; 0x54c3b64aab43d3e%N;
  0x3443%N; 0x344646%N; 0x1555385a32ab44b8e%N; 0x744f%N;
  0x145246%N; 0x5525364aab4553e%N; 0x345b%N; 0x345e46%N;
  0x15554bba32ab4638e%N; 0x7467%N; 0x146a46%N; 0x611232800000aecd0000025d7a00000746f%N;
  0x2aab08039558693caab47246%N; 0x155558414caac34aa5626572aaab080195586814aaac540e55556110b2ab0d869589c3cb47646%N; 0xaaaaaac235e5561bb12b13d9955558469caac375255562bab2b1cda9555558465caac373256279b2aaab08c795586e44aaac572655556119d2ab0dcf9589e84ac6f4655555611bf2ab0de09589f0caaaac236e5561bb92aab15dd958e714b47b8e%N; 0x747f%N;
  0x148246%N; 0x1000002855a0000070a74000012146000002000002bffc0000080000067fd800001800000f487%N; 0x148a46%N; 0x100000194ba00000548f%N;
  0x149246%N; 0x62d27ca000003497%N; 0x149a46%N; 0x15957252aa00000349f%N;
  0x14a246%N; 0x10000029aba0000074a7%N; 0x14aa46%N; 0x2cff6c9%N;
  0x1%N; 0x5559ff072d2b919%N; 0x10e97600008000002252dc000104000045a59800021000008d4af%N; 0x52f919%N;
  0x3cae986001e50000796501c003ca4000f2da018007950001e5d35f000f2b0003cbe416001e58000798481c003cb4000f319018007970001e650b7000f2f0003cce166001e6000079a407c003cc4000f3576b8007990001e6ced3000f330003cddd9e001e6800079c385c003cd4000f3970980079b0001e74d97000f370003ceda16001e7000079e341c003ce4000f3d63f80079d0001e7cb43000f3b0003cfd67e001e780007a02cec003cf4000f4155180079f0001e84a9f000f3f0003d0d526001e800007a2262c003d04000f454c38007a10001e8c983%N; 0x14c6a6555550e424a7ce46%N; 0xbcc094cb%N; 0x14ceaa%N;
  0x14d246%N
].

Definition dag_chunks : list (list N) := [
  d7_c0; d7_c1; d7_c2; d7_c3; d7_c4; d7_c5; d7_c6; d7_c7;
  d7_c8; d7_c9; d7_c10; d7_c11; d7_c12; d7_c13; d7_c14; d7_c15;
  d7_c16; d7_c17; d7_c18; d7_c19; d7_c20; d7_c21; d7_c22; d8_c0;
  d8_c1; d8_c2; d8_c3; d8_c4; d8_c5; d8_c6; d8_c7; d8_c8;
  d8_c9; d8_c10; d8_c11; d8_c12; d8_c13; d8_c14; d8_c15; d8_c16;
  d8_c17; d8_c18; d8_c19; d8_c20
].


(* A scheduled return consists of four kinds of instructions. The least
   significant two bits distinguish a run-framed leaf (0), a leaf (1),
   an atom-framed cached return (2), and a run-framed cached return (3).
   Run lengths occupy 24 bits, atom-frame ids 8, and rule ids 11.
   The evaluator computes both the endpoint and the number of bounces;
   the schedule contains neither. *)
Definition packElt (e : ElemL) (rest : N) : option N :=
  match e with
  | el_run10 k => packRunOpt k rest
  | el_single d b =>
      let tag : N :=
        match d, b with
        | 0, sep0 => 1%N | 2, sep0 => 2%N | 3, sep0 => 3%N
        | 0, sep1 => 4%N | 1, sep1 => 5%N | 2, sep1 => 6%N
        | _, _ => 0%N
        end in
      if (tag =? 0)%N then None else Some (joinBits 4 tag rest)
  end.

Lemma packElt_sound e rest out :
  packElt e rest = Some out -> decN out = e :: decN rest.
Proof.
  destruct e as [d b|k]; [|apply packRunOpt_sound].
  destruct d as [|[|[|[|d]]]]; destruct b; cbn [packElt];
    intro H; try discriminate H; injection H as <-;
    apply decN_of_decHead; unfold decHead;
    rewrite joinBits_eq0_false by (cbn [pow2N]; lia);
    rewrite splitBits_joinBits by (cbn [pow2N]; lia); reflexivity.
Qed.

Fixpoint packL (l : list ElemL) : option N :=
  match l with
  | [] => Some 0%N
  | e :: l' =>
      match packL l' with
      | Some rest => packElt e rest
      | None => None
      end
  end.

Lemma packL_sound l out : packL l = Some out -> decN out = l.
Proof.
  revert out. induction l as [|e l IH]; intros out H; cbn [packL] in H.
  - injection H as <-. reflexivity.
  - destruct (packL l) eqn:E; [|discriminate].
    rewrite (packElt_sound _ _ _ H). f_equal. eapply IH; eauto.
Qed.

Definition leafWithFuel fuel cur : option (N * N) :=
  match miniLoop fuel (bs_BR0 (el_single 3 sep0 :: decN cur)
                          [er_single 0 0; er_single 0 0]) false with
  | Some got =>
      match packL got with
      | Some out => Some (out, 1%N)
      | None => None
      end
  | None => None
  end.

Definition Returns (f : N -> option (N * N)) : Prop :=
  forall cur out n, f cur = Some (out, n) ->
    TailBounces n (expandL (decN cur)) (expandL (decN out)).

Lemma leafWithFuel_sound fuel : Returns (leafWithFuel fuel).
Proof.
  intros cur out n H. unfold leafWithFuel in H.
  destruct (miniLoop fuel (bs_BR0 (el_single 3 sep0 :: decN cur)
             [er_single 0 0; er_single 0 0]) false) as [got|] eqn:E; [|discriminate].
  destruct (packL got) eqn:P; [|discriminate].
  injection H as <- <-. apply tb_one.
  rewrite (packL_sound _ _ P).
  intro rb. pose proof (miniLoop_sound _ _ _ rb E) as Hs.
  cbn [toFlatBase fsApp toFlat expandL expandR app] in Hs. exact Hs.
Qed.

Definition leaf := leafWithFuel 320.
Lemma leaf_sound : Returns leaf.
Proof. exact (leafWithFuel_sound 320). Qed.

Inductive Frame := no_frame | run_frame (k : N) | atom_frame (ps : list PAtom).
Definition strip f :=
  match f with no_frame => @Some N | run_frame k => stripRunN k | atom_frame ps => stripAtomsN ps end.
Definition join f :=
  match f with no_frame => @Some N | run_frame k => pushRunN k | atom_frame ps => joinAtomsN ps end.

(* A schedule says how to compose a return, not where it starts or ends.
   A call gets its start from the actual tape after stripping the frame.
   The memo records only checked returns; a different input for a cached
   identifier is a failed search, not permission to reuse the return. *)
Definition Rule := (N * N * N)%type.
Definition Table := PositiveMap.t Rule.
Definition ruleKey (rid : N) : positive :=
  match N.succ rid with Npos p => p | N0 => xH end.
Definition lookup (st : Table) (rid : N) : option Rule :=
  PositiveMap.find (ruleKey rid) st.
Definition Bounces cur out n :=
  TailBounces n (expandL (decN cur)) (expandL (decN out)).
Definition table_sound (st : Table) :=
  forall rid cur out n, lookup st rid = Some (cur,out,n) -> Bounces cur out n.
Definition empty : Table := PositiveMap.empty Rule.
Lemma empty_sound : table_sound empty.
Proof. intros i a b n H. unfold lookup, empty in H. now rewrite PositiveMap.gempty in H. Qed.

Lemma add_sound st rid cur out n :
  table_sound st -> Bounces cur out n ->
  table_sound (PositiveMap.add (ruleKey rid) (cur,out,n) st).
Proof.
  intros Ht Hr i a b k L. unfold lookup in L.
  destruct (Pos.eq_dec (ruleKey i) (ruleKey rid)) as [E|E].
  - rewrite E, PositiveMap.gss in L. now injection L as <- <- <-.
  - rewrite PositiveMap.gso in L by exact E. exact (Ht _ _ _ _ L).
Qed.

Definition Reply := (option (N * N) * Table)%type.
Definition Call := N -> N -> Table -> Reply.
Definition reply_sound cur (r : Reply) :=
  let '(ret,t) := r in
  table_sound t /\
    match ret with Some (out,n) => Bounces cur out n | None => True end.
Definition call_sound (call : Call) :=
  forall rid cur t, table_sound t -> reply_sound cur (call rid cur t).

Definition decodeOp (code : N) : option (Frame * option N * N) :=
  let (tag, r0) := splitBits 2 code in
  match tag with
  | 1%N => Some (no_frame, None, r0)
  | 2%N =>
      let (pid,r1) := splitBits 8 r0 in let (rid,nxt) := splitBits 11 r1 in
      option_map (fun ps => (atom_frame ps, Some rid, nxt)) (getPeel pid)
  | 3%N =>
      let (rid,r1) := splitBits 11 r0 in let (ex,nxt) := splitBits 24 r1 in
      Some (run_frame ex, Some rid, nxt)
  | _ =>
      let (ex,nxt) := splitBits 24 r0 in
      Some (run_frame ex, None, nxt)
  end.

Definition runOp (call : Call) f op cur t : Reply :=
  match strip f cur with
  | None => (None,t)
  | Some sub =>
    let '(ret,t') :=
      match op with None => (leaf sub,t) | Some child => call child sub t end in
    match ret with
    | None => (None,t')
    | Some (mid,n) => (option_map (fun out => (out,n)) (join f mid),t')
    end
  end.

Lemma reframe_sound f cur sub mid out n :
  strip f cur = Some sub -> join f mid = Some out ->
  Bounces sub mid n -> Bounces cur out n.
Proof.
  intros Hs Hj Hr. unfold Bounces in *.
  destruct f; cbn [strip join] in Hs, Hj.
  - now injection Hs as <-; injection Hj as <-.
  - pose proof (tailBounces_frame_run k Hr) as H.
    now rewrite <- (stripRunN_sound _ _ _ Hs), <- (pushRunN_sound _ _ _ Hj) in H.
  - pose proof (tailBounces_frame_atoms ps Hr) as H.
    now rewrite <- (stripAtomsN_sound _ _ _ Hs), <- (joinAtomsN_sound _ _ _ Hj) in H.
Qed.

Lemma runOp_sound call (Hcall : call_sound call) f op cur t :
  table_sound t -> reply_sound cur (runOp call f op cur t).
Proof.
  intros Ht. unfold runOp.
  destruct (strip f cur) as [sub|] eqn:E; [|exact (conj Ht I)].
  assert (H : reply_sound sub
      (match op with None => (leaf sub,t) | Some child => call child sub t end)).
  { destruct op as [child|]; [now apply Hcall|].
    unfold reply_sound. destruct (leaf sub) as [[mid n]|] eqn:F;
      split; [exact Ht|exact (leaf_sound _ _ _ F)|exact Ht|exact I]. }
  destruct (match op with None => (leaf sub,t) | Some child => call child sub t end)
    as [[[mid n]|] t'] eqn:F; [|exact H].
  destruct H as [Ht' Hr].
  destruct (join f mid) as [out|] eqn:J; split; try exact Ht'; try exact I.
  exact (reframe_sound _ _ _ _ _ _ E J Hr).
Qed.

Fixpoint replay {Cursor : Type}
    (next : Cursor -> option (Frame * option N * Cursor))
    (done : Cursor -> bool) (call : Call) (fuel : nat) code cur acc t : Reply :=
  if done code then (Some (cur,acc),t) else
  match fuel with
  | O => (None,t)
  | S k =>
    match next code with
    | Some (f,op,nxt) =>
      match runOp call f op cur t with
      | (Some (out,n),t') => replay next done call k nxt out (acc+n)%N t'
      | (None,t') => (None,t')
      end
    | None => (None,t)
    end
  end.

Local Opaque runOp leaf.

Lemma replay_sound {Cursor : Type} next done call (Hcall : call_sound call) fuel :
  forall code cur acc t, table_sound t ->
    let '(ret,t') := @replay Cursor next done call fuel code cur acc t in
    table_sound t' /\
    match ret with
    | Some (out,total) => exists n, total = (acc+n)%N /\ Bounces cur out n
    | None => True
    end.
Proof.
  induction fuel as [|fuel IH]; intros code cur acc t Ht;
    cbn [replay]; destruct (done code);
    try (split; [exact Ht| exists 0%N; split; [lia|apply tb_zero]]);
    try exact (conj Ht I).
  destruct (next code) as [[[f op] nxt]|]; [|exact (conj Ht I)].
  pose proof (runOp_sound call Hcall f op cur t Ht) as H.
  destruct (runOp call f op cur t) as [[[out n]|] t']; [|exact H].
  destruct H as [Ht' Hr]. specialize (IH nxt out (acc+n)%N t' Ht').
  destruct (replay next done call fuel nxt out (acc+n)%N t') as [[[out' total]|] t''];
    [|exact IH].
  destruct IH as [Ht'' [k [-> Hn]]]. split; [exact Ht''|].
  exists (n+k)%N. split; [lia|exact (tb_trans Hr Hn)].
Qed.

Local Opaque replay.

Definition packedReplay := replay decodeOp (fun code => (code =? 0)%N).

Fixpoint evalRule codes (depth : nat) rid cur t : Reply :=
  match depth with
  | O => (None,t)
  | S d =>
    match lookup t rid with
    | Some (inp,out,n) =>
      if (inp =? cur)%N then (Some (out,n),t) else (None,t)
    | None =>
      match nth_error codes (N.to_nat rid) with
      | None => (None,t)
      | Some code =>
        match packedReplay (evalRule codes d) 160 code cur 0%N t with
        | (Some (out,n),t') =>
          (Some (out,n),PositiveMap.add (ruleKey rid) (cur,out,n) t')
        | (None,t') => (None,t')
        end
      end
    end
  end.

Lemma evalRule_sound codes depth : call_sound (evalRule codes depth).
Proof.
  induction depth as [|d IH]; intros rid cur t Ht; [exact (conj Ht I)|].
  cbn [evalRule]. destruct (lookup t rid) as [[[inp out] n]|] eqn:E.
  - destruct (inp =? cur)%N eqn:F; [|exact (conj Ht I)].
    apply N.eqb_eq in F. subst inp. exact (conj Ht (Ht _ _ _ _ E)).
  - destruct (nth_error codes (N.to_nat rid)) as [code|]; [|exact (conj Ht I)].
    pose proof (replay_sound decodeOp (fun code => (code =? 0)%N) _ IH 160 code cur 0%N t Ht) as H.
    unfold packedReplay.
    destruct (replay decodeOp (fun code => (code =? 0)%N) (evalRule codes d) 160 code cur 0%N t)
      as [[[out n]|] t'];
      [|exact H].
    destruct H as [Ht' [k [-> Hr]]].
    exact (conj (add_sound _ _ _ _ _ Ht' Hr) Hr).
Qed.

Definition runRule : Call := evalRule (concat dag_chunks) 72.
Lemma runRule_sound : call_sound runRule.
Proof. apply evalRule_sound. Qed.

Definition Ops := list (Frame * option N).
Definition firstOp (ops : Ops) : option (Frame * option N * Ops) :=
  match ops with [] => None | op::rest => Some (op,rest) end.
Definition noOps (ops : Ops) := match ops with [] => true | _ => false end.

Definition runPass (ops : Ops) : Call :=
  fun _ cur t => replay firstOp noOps runRule (length ops) ops cur 0%N t.
Lemma runPass_sound ops : call_sound (runPass ops).
Proof.
  intros rid cur t Ht. unfold runPass.
  pose proof (replay_sound firstOp noOps runRule runRule_sound (length ops) ops cur 0%N t Ht) as H.
  destruct (replay firstOp noOps runRule (length ops) ops cur 0%N t)
    as [[[out total]|] t']; [|exact H].
  destruct H as [Ht' [n [-> Hr]]]. exact (conj Ht' Hr).
Qed.

Local Transparent replay runOp leaf.

End M137Certs.


Module M137Main.
Import M137 M137Ext M137Sec56 M137Certs.
Strategy 1000 [prependRepL prependRepR].

(* ========================================================================= *)
(* 8. Concrete Rule Extraction, 51-Step Prefix, and Parametric Closure       *)
(* ========================================================================= *)

Definition eqElemR (a b : ElemR) : bool :=
  match a, b with
  | er_single z1 o1, er_single z2 o2 => andb (Nat.eqb z1 z2) (Nat.eqb o1 o2)
  | er_run10 k1, er_run10 k2 => (k1 =? k2)%N
  | _, _ => false
  end.

Lemma eqElemR_sound : forall a b, eqElemR a b = true -> a = b.
Proof.
  intros [z1 o1 | k1] [z2 o2 | k2] H; cbn [eqElemR] in H; try discriminate H.
  - apply andb_true_iff in H. destruct H as [Hz Ho].
    apply Nat.eqb_eq in Hz. apply Nat.eqb_eq in Ho. congruence.
  - apply N.eqb_eq in H. congruence.
Qed.

Fixpoint eqListR (xs ys : list ElemR) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => andb (eqElemR x y) (eqListR xs' ys')
  | _, _ => false
  end.

Lemma eqListR_sound : forall xs ys, eqListR xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] H; cbn [eqListR] in H;
    try reflexivity; try discriminate H.
  apply andb_true_iff in H. destruct H as [Hx Hxs].
  f_equal; [exact (eqElemR_sound _ _ Hx) | exact (IH _ Hxs)].
Qed.

Definition eqBaseState (a b : BaseState) : bool :=
  match a, b with
  | bs_Init, bs_Init => true
  | bs_Halt l1 r1, bs_Halt l2 r2 => andb (eqListL l1 l2) (eqListR r1 r2)
  | bs_AL l1 r1, bs_AL l2 r2 => andb (eqListL l1 l2) (eqListR r1 r2)
  | bs_BR l1 r1, bs_BR l2 r2 => andb (eqListL l1 l2) (eqListR r1 r2)
  | bs_BR0 l1 r1, bs_BR0 l2 r2 => andb (eqListL l1 l2) (eqListR r1 r2)
  | bs_CR l1 r1, bs_CR l2 r2 => andb (eqListL l1 l2) (eqListR r1 r2)
  | bs_DL l1 r1, bs_DL l2 r2 => andb (eqListL l1 l2) (eqListR r1 r2)
  | bs_ER l1 r1, bs_ER l2 r2 => andb (eqListL l1 l2) (eqListR r1 r2)
  | _, _ => false
  end.

Lemma eqBaseState_sound : forall a b, eqBaseState a b = true -> a = b.
Proof.
  intros [] [] H; cbn [eqBaseState] in H; try reflexivity; try discriminate H;
    apply andb_true_iff in H; destruct H as [Hl Hr];
    rewrite (eqListL_sound _ _ Hl), (eqListR_sound _ _ Hr); reflexivity.
Qed.

Definition checkReturn (run : Call) (rid expN : N) (inL outL : list ElemL) : bool :=
  match packL inL with
  | Some x =>
    match fst (run rid x empty) with
    | Some (y,n) => (n =? expN)%N && eqListL (decN y) outL
    | None => false
    end
  | None => false
  end.

Local Opaque packL.

Lemma checkReturn_sound run (Hrun : call_sound run) rid expN inL outL :
  checkReturn run rid expN inL outL = true ->
  TailBounces expN (expandL inL) (expandL outL).
Proof.
  unfold checkReturn. destruct (packL inL) as [x|] eqn:E; [|discriminate].
  pose proof (Hrun rid x empty empty_sound) as Hr.
  destruct (run rid x empty) as [[[y n]|] t]; [|discriminate].
  cbn [fst]. intros H. apply andb_true_iff in H as [Hn Hy].
  apply N.eqb_eq in Hn. apply eqListL_sound in Hy. subst n outL.
  rewrite <- (packL_sound _ _ E). exact (proj2 Hr).
Qed.

Local Transparent packL.

Definition checkRuleIO := checkReturn runRule.
Lemma rule_io_sound rid expN inL outL :
  checkRuleIO rid expN inL outL = true ->
  TailBounces expN (expandL inL) (expandL outL).
Proof. apply checkReturn_sound, runRule_sound. Qed.

Definition checkMiniIter (ticks_m1 : nat) (bs1 bs2 : BaseState) : bool :=
  match iterMiniStep (S ticks_m1) bs1 with
  | Some got => eqBaseState got bs2
  | None => false
  end.

Lemma checkMiniIter_sound : forall ticks_m1 bs1 bs2,
  checkMiniIter ticks_m1 bs1 bs2 = true ->
  forall rb : list (nat * nat),
    encodeFlat (toFlatBase bs1 rb) -[ tm ]->+ encodeFlat (toFlatBase bs2 rb).
Proof.
  intros ticks_m1 bs1 bs2 H rb. unfold checkMiniIter in H.
  destruct (iterMiniStep (S ticks_m1) bs1) as [got |] eqn:Hm; [| discriminate H].
  rewrite (eqBaseState_sound _ _ H) in Hm.
  exact (iterMiniStep_plus ticks_m1 bs1 bs2 rb Hm).
Qed.

Lemma topWrap_elem : forall {n : N} (k_in k_out : N) {inL outL : list ElemL},
  TailBounces n (expandL inL) (expandL outL) ->
  (0 < n)%N -> (2 <= k_in)%N -> k_out = (k_in + 2 * n)%N ->
  encodeFlat (toFlat (bs_CR (el_run10 (k_in - 1)%N :: inL) []))
    -[ tm ]->+
  encodeFlat (toFlat (bs_CR (el_run10 (k_out - 1)%N :: outL) [])).
Proof.
  intros n k_in k_out inL outL Hrule Hn Hk Heq.
  cbn [toFlat expandL expandR].
  replace (k_in - 1 + 1)%N with ((k_in - 2) + 2)%N by lia.
  replace (k_out - 1 + 1)%N with ((k_in - 2) + 2 * n + 2)%N by lia.
  exact (topWrap_bounces (k_in - 2)%N Hrule Hn).
Qed.

(* The 80-element passive body is identical in every phase. Only
   the short windows on either side change. Share those intact bodies
   and carry a phase's output window directly into the next phase. *)
Section PhaseWords.
Local Notation z := (el_single 0 sep0).
Local Notation d := (el_single 2 sep0).
Local Notation t := (el_single 3 sep0).
Local Notation s := (el_single 1 sep1).
Local Notation d1 := (el_single 2 sep1).
Local Notation r := el_run10.

Definition cycleBody : list ElemL :=
  [
    z; d; r 2; z; d; r 3; z; d; r 8; z; d; r 4;
    z; r 5; d; r 1; z; d; r 1; z; d; r 4; z; d;
    r 4; z; r 5; d; r 1; z; d; r 2; z; d; z; r 1;
    d; r 1; z; d; r 4; z; r 5; d; r 1; z; d; r 2;
    z; d; z; r 1; d; r 1; z; d; r 4; z; r 5; d;
    r 4; z; d; r 4; z; r 5; d; r 1; z; d; r 1; z;
    d; r 4; z; d; r 4; z; r 5; d
  ].
Definition rIn_1323 : list ElemL :=
  [z; d; r 4; z; d; r 2] ++ cycleBody ++ [r 0; z; d; r 3; s; d; r 2; z; d; r 3; z; d; r 3; z; z; r 0; z; t; z; z].
Definition rOut_1323 : list ElemL :=
  [z; d; r 2; d; r 5] ++ cycleBody ++ [r 0; z; d; r 5; z; d; r 4; z; r 1; z; d; r 3; z; d; z; t; z; z].
Definition r1279_in_tail : list ElemL :=
  cycleBody ++ [r 0; z; d; r 4; s; r 0; z; r 1; z; d; r 3; z; d; r 3; z; r 0; d; d; z; z].
Definition r1279_out_tail : list ElemL :=
  [z; r 0] ++ cycleBody ++ [r 1; z; d; z; z; r 3; z; d; r 4; z; r 5; d; z; z; r 0; z; t; z; z].
Definition rIn_1279 : list ElemL := [r 3] ++ r1279_in_tail.
Definition rOut_1279 : list ElemL := [r 2] ++ r1279_out_tail.
Definition cycIn_0 : list ElemL := [d; r 1] ++ rIn_1323.
Definition cycIn_1 : list ElemL := [d; r 1] ++ rOut_1323.
Definition cycOut_1 : list ElemL := [r 0; s; r 0; z; r 2; d; r 5] ++ r1279_in_tail.
Definition cycIn_2 : list ElemL := [d] ++ cycOut_1.
Definition cycOut_2 : list ElemL := [r 0; z; d; z; r 2; d; r 5] ++ r1279_in_tail.
Definition cycIn_3 : list ElemL := [d] ++ cycOut_2.
Definition cycIn_4 : list ElemL := [d; r 0; z; d; z; r 2; d; r 4] ++ r1279_out_tail.
Definition cycOut_4 : list ElemL :=
  [r 0; z; d; z; r 1; z; r 0; z; r 1; z; d; r 2] ++ cycleBody ++ [r 0; s; r 6; z; d; r 4; z; r 4; z; r 2; z; d; d; z; z].
Definition cycIn_5 : list ElemL := [d] ++ cycOut_4.
Definition cycOut_5 : list ElemL := [r 0; z; d; z; z; d; r 4; z; d; r 2] ++ r1279_in_tail.
Definition cycIn_6 : list ElemL := [d] ++ cycOut_5.
Definition bridgeTail : list ElemL :=
  cycleBody ++ [r 0; z; d; r 4; z; d; z; r 1; z; d; r 3; z; d; r 3; z; r 0; d; d; z; z].
Definition cycOut_6 : list ElemL := [s; d; r 0; z; d; r 4; z; d; r 2] ++ bridgeTail.
Definition cycIn_7 : list ElemL := [d] ++ cycOut_6.
Definition cycOut_7 : list ElemL := [z; t; r 0; z; d; r 4; z; d; r 2] ++ bridgeTail.
Definition cycIn_8 : list ElemL := [d] ++ cycOut_7.
Definition cycOut_8 : list ElemL := [r 2] ++ rIn_1323.
Definition cycIn_9 : list ElemL := [d1] ++ cycOut_8.
Definition k1_0 : list ElemL := [z; r 0] ++ cycIn_0.
Definition k1_10 : list ElemL := [z; r 1] ++ cycIn_0.
Definition frozenPrefix : list ElemL :=
  [z; d; r 1; z; r 11730945; d; r 386565; z; r 0; d; r 3884; z; d].
Definition frozenRawHead : list ElemL := frozenPrefix ++ [r 68].
Definition topL_50 : list ElemL := [r 1274955169813] ++ frozenRawHead ++ k1_0.

End PhaseWords.

Lemma rule_1323 : TailBounces 68719476732%N (expandL rIn_1323) (expandL rOut_1323).
Proof. apply (rule_io_sound 1323%N 68719476732%N rIn_1323 rOut_1323); vm_check_eq. Qed.

Lemma rule_1279 : TailBounces 68719476729%N (expandL rIn_1279) (expandL rOut_1279).
Proof. apply (rule_io_sound 1279%N 68719476729%N rIn_1279 rOut_1279); vm_check_eq. Qed.

Definition topJump rid (bs : BaseState) t : option BaseState * Table :=
  match bs with
  | bs_CR (el_run10 k :: tail) [] =>
    if (0 <? k)%N then
      match packL tail with
      | Some inp =>
        match runRule rid inp t with
        | (Some (out,n),t') =>
          if (0 <? n)%N then (Some (bs_CR (el_run10 (k + 2*n)%N :: decN out) []),t')
          else (None,t')
        | (None,t') => (None,t')
        end
      | None => (None,t)
      end
    else (None,t)
  | _ => (None,t)
  end.

Definition entry_sound bs (r : option BaseState * Table) :=
  let '(ret,t) := r in
  table_sound t /\
  match ret with
  | Some out => encodeFlat (toFlat bs) -[ tm ]->* encodeFlat (toFlat out)
  | None => True
  end.

Local Opaque runRule packL.

Lemma topJump_sound rid bs t : table_sound t -> entry_sound bs (topJump rid bs t).
Proof.
  intros Ht. unfold topJump.
  destruct bs as [|l r|l r|l r|l r|l r|l r|l r]; try exact (conj Ht I).
  destruct l as [|[d s|k] l], r; try exact (conj Ht I).
  destruct (0 <? k)%N eqn:Ek; [|exact (conj Ht I)].
  destruct (packL l) as [x|] eqn:Ex; [|exact (conj Ht I)].
  pose proof (runRule_sound rid x t Ht) as H.
  destruct (runRule rid x t) as [[[y n]|] t']; destruct H as [Ht' Hn]; [|exact (conj Ht' I)].
  destruct (0 <? n)%N eqn:En; [|exact (conj Ht' I)].
  apply N.ltb_lt in Ek, En. split; [exact Ht'|].
  unfold Bounces in Hn. rewrite (packL_sound _ _ Ex) in Hn.
  pose proof (topWrap_elem (k+1)%N (k+1+2*n)%N Hn En ltac:(lia) eq_refl) as H.
  replace (k + 1 - 1)%N with k in H by lia.
  replace (k + 1 + 2 * n - 1)%N with (k + 2*n)%N in H by lia.
  exact (progress_evstep tm _ _ H).
Qed.

Inductive EntryOp := local_steps (ticks_minus_one : nat) | return_jump (rid : N).
Definition entryStep op bs t :=
  match op with
  | local_steps k => (iterStepSuper (S k) bs,t)
  | return_jump rid => topJump rid bs t
  end.

Lemma entryStep_sound op bs t : table_sound t -> entry_sound bs (entryStep op bs t).
Proof.
  intros Ht. destruct op as [k|rid]; [|now apply topJump_sound].
  cbn [entryStep entry_sound].
  destruct (iterStepSuper (S k) bs) as [out|] eqn:E; split; try exact Ht; try exact I.
  apply progress_evstep. now apply iterStepSuper_plus in E.
Qed.

Local Opaque entryStep.

Fixpoint runEntry (ops : list EntryOp) (bs : BaseState) t : option BaseState * Table :=
  match ops with
  | [] => (Some bs,t)
  | op::ops' =>
      match entryStep op bs t with
      | (Some mid,t') => runEntry ops' mid t'
      | (None,t') => (None,t')
      end
  end.

Lemma runEntry_sound ops bs t : table_sound t -> entry_sound bs (runEntry ops bs t).
Proof.
  revert bs t. induction ops as [|op ops IH]; intros bs t Ht; cbn [runEntry].
  - split; [exact Ht|apply evstep_refl].
  - pose proof (entryStep_sound op bs t Ht) as H.
    destruct (entryStep op bs t) as [[mid|] t']; [|exact H].
    destruct H as [Ht' Hstep]. specialize (IH mid t' Ht').
    destruct (runEntry ops mid t') as [[out|] t'']; [|exact IH].
    destruct IH as [Ht'' Hnext].
    exact (conj Ht'' (evstep_trans tm _ _ _ Hstep Hnext)).
Qed.

Lemma reachesEntry ops out :
  fst (runEntry ops bs_Init empty) = Some out ->
  c0 -[ tm ]->* encodeFlat (toFlat out).
Proof.
  pose proof (runEntry_sound ops bs_Init empty empty_sound) as H.
  destruct (runEntry ops bs_Init empty) as [[out'|] t]; [|discriminate].
  intros E. injection E as <-. exact (proj2 H).
Qed.

Local Transparent entryStep runRule packL.

Definition entryPlan := [
  local_steps 30; local_steps 37; local_steps 10; return_jump 0%N; local_steps 14;
  local_steps 9; local_steps 25; local_steps 14; return_jump 2%N; local_steps 39;
  return_jump 3%N; local_steps 29; local_steps 31; local_steps 29; local_steps 14;
  return_jump 7%N; local_steps 131; return_jump 8%N; local_steps 42; local_steps 13;
  local_steps 72; local_steps 18; return_jump 31%N; local_steps 111; return_jump 32%N;
  local_steps 23; local_steps 42; local_steps 29; local_steps 46; return_jump 82%N;
  local_steps 87; return_jump 83%N; local_steps 30; local_steps 38; local_steps 40;
  local_steps 37; return_jump 229%N; local_steps 95; return_jump 230%N; local_steps 45;
  local_steps 14; local_steps 47; local_steps 40; return_jump 420%N; local_steps 125;
  return_jump 421%N; local_steps 23; local_steps 43; local_steps 29; local_steps 23;
  return_jump 1333%N
].


Lemma prefix_reaches_top50 : c0 -[ tm ]->* encodeFlat (fs_CR (expandL topL_50) []).
Proof.
  change (encodeFlat (toFlat bs_Init) -[ tm ]->* encodeFlat (toFlat (bs_CR topL_50 []))).
  apply (reachesEntry entryPlan). vm_check_eq.
Qed.


Definition frozenAtoms : list PAtom :=
  [pa_z2; pa_r 1%N; pa_zr2 11730945%N; pa_r 386565%N; pa_zr2 0%N; pa_r 3884%N; pa_z2; pa_r 66%N].

Lemma expandL_frozenRaw : forall tail,
  expandL (frozenRawHead ++ tail) = expandL (atomsToElem frozenAtoms) ++ prependRepL 2%N (expandL tail).
Proof.
  intros tail.
  assert (Hraw : frozenRawHead ++ tail = frozenPrefix ++ (el_run10 68%N :: tail)) by reflexivity.
  assert (Hatoms : atomsToElem frozenAtoms = frozenPrefix ++ [el_run10 66%N]) by reflexivity.
  rewrite Hraw, Hatoms, !expandL_append, <- app_assoc.
  apply f_equal2; [reflexivity |].
  cbn [expandL].
  rewrite prependRepL_append_eq. cbn [app].
  rewrite <- prependRepL_add. reflexivity.
Qed.

Definition entryPass : Ops :=
  [(atom_frame [pa_zr2 0%N], Some 1323%N);
   (no_frame, None);
   (no_frame, None);
   (atom_frame [pa_zr2 0%N; pa_r 0%N; pa_z2; pa_zr2 2%N], Some 1279%N)] ++
  repeat (no_frame, None) 6.

Lemma k1_cycle : TailBounces 137438953469%N (expandL k1_0) (expandL k1_10).
Proof.
  apply (checkReturn_sound (runPass entryPass) (runPass_sound entryPass) 0%N).
  vm_check_eq.
Qed.

Lemma out_0_run : forall (m : N) ls rs,
  encodeFlat (fs_BR0 ((3, sep0) :: (0, sep0) :: prependRepL (m + 2)%N ls) ((0, 0) :: (0, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_BR0 ((3, sep0) :: ls)
    ((0, 0) :: (0, 0) :: prependRepR m ((0, 0) :: (1, 0) :: (1, 0) :: rs))).
Proof.
  intros m ls rs.
  replace (m + 2)%N with (1 + (1 + m))%N by lia.
  rewrite !prependRepL_add, !prependRepL_1.
  eapply progress_trans; [exact (shift_out_step f3_1 f3_0 f3_1 ((1, sep0) :: (1, sep0) :: prependRepL m ls) rs) |].
  eapply progress_trans; [exact (shift_out_step f3_0 f3_1 f3_1 ((1, sep0) :: prependRepL m ls) ((1, 0) :: rs)) |].
  eapply progress_evstep_trans; [exact (shift_out_step f3_1 f3_1 f3_0 (prependRepL m ls) ((1, 0) :: (1, 0) :: rs)) |].
  cbn [hdrR f3Val].
  exact (sw_out15_rep m ls ((0, 0) :: (1, 0) :: (1, 0) :: rs)).
Qed.

Lemma sym_br_bounce : forall ticks_m1 inInner outInner,
  checkMiniIter ticks_m1
    (bs_BR0 (el_single 3 sep0 :: inInner) [er_single 0 0; er_single 0 0])
    (bs_BR outInner [er_run10 0%N; er_single 0 0; er_single 2 0; er_run10 1%N]) = true ->
  forall m : N,
    TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL inInner))
               ((0, sep0) :: prependRepL (m + 2)%N ((2, sep0) :: expandL outInner)).
Proof.
  intros ticks_m1 inInner outInner Hchk m rb.
  pose proof (checkMiniIter_sound _ _ _ Hchk (prependRepR m ((0, 0) :: (1, 0) :: (1, 0) :: rb))) as Hmid.
  cbn [toFlatBase fsApp toFlat expandL expandR app] in Hmid.
  rewrite ?prependRepR_01, ?prependRepR_2 in Hmid. cbn [app] in Hmid.
  eapply progress_trans; [exact (out_0_run m (expandL inInner) rb) |].
  eapply progress_trans; [exact Hmid |].
  assert (Hreq : (1, 0) :: (1, 0) :: prependRepR m ((0, 0) :: (1, 0) :: (1, 0) :: rb) =
                 prependRepR ((m + 1) + 1)%N ((0, 0) :: (1, 0) :: (1, 0) :: rb)).
  { replace ((m + 1) + 1)%N with (2 + m)%N by lia.
    rewrite prependRepR_add, prependRepR_2. reflexivity. }
  rewrite Hreq.
  eapply progress_evstep_trans;
    [exact (in_2_10_flat (m + 1)%N (expandL outInner) ((1, 0) :: (1, 0) :: rb)) |].
  replace ((m + 1) + 1)%N with (m + 2)%N by lia.
  pose proof (sw_in7_rep 2%N ((0, sep0) :: prependRepL (m + 2)%N ((2, sep0) :: expandL outInner)) rb) as H4.
  rewrite prependRepR_2 in H4.
  exact H4.
Qed.

Lemma step8_mid_flat : forall ls rs,
  encodeFlat (fs_AL ((0, sep0) :: (0, sep1) :: ls) ((0, 0) :: (1, 0) :: (1, 0) :: (1, 0) :: rs))
    -[ tm ]->+
  encodeFlat (fs_AL ((0, sep1) :: (2, sep1) :: ls) ((0, 0) :: (1, 0) :: (1, 0) :: rs)).
Proof. close_flat_sc 8. Qed.

Lemma sym_s8_bounce : forall ticks_m1 inInner outTail,
  checkMiniIter ticks_m1
    (bs_BR0 (el_single 3 sep0 :: inInner) [er_single 0 0; er_single 0 0])
    (bs_AL (el_single 0 sep0 :: el_single 0 sep1 :: outTail) [er_single 0 0; er_run10 2%N]) = true ->
  forall m : N,
    TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL inInner))
               ((0, sep0) :: prependRepL (m + 2)%N ((2, sep1) :: expandL outTail)).
Proof.
  intros ticks_m1 inInner outTail Hchk m rb.
  pose proof (checkMiniIter_sound _ _ _ Hchk (prependRepR m ((0, 0) :: (1, 0) :: (1, 0) :: rb))) as Hmid.
  cbn [toFlatBase fsApp toFlat expandL expandR app] in Hmid.
  change (prependRepR (2 + 1)%N []) with [(1, 0); (1, 0); (1, 0)] in Hmid.
  cbn [app] in Hmid.
  eapply progress_trans; [exact (out_0_run m (expandL inInner) rb) |].
  eapply progress_trans; [exact Hmid |].
  eapply progress_evstep_trans;
    [exact (step8_mid_flat (expandL outTail) (prependRepR m ((0, 0) :: (1, 0) :: (1, 0) :: rb))) |].
  assert (Hreq : (1, 0) :: (1, 0) :: prependRepR m ((0, 0) :: (1, 0) :: (1, 0) :: rb) =
                 prependRepR ((m + 1) + 1)%N ((0, 0) :: (1, 0) :: (1, 0) :: rb)).
  { replace ((m + 1) + 1)%N with (2 + m)%N by lia.
    rewrite prependRepR_add, prependRepR_2. reflexivity. }
  rewrite Hreq.
  eapply evstep_trans;
    [exact (sw_in19_rep (m + 1)%N ((2, sep1) :: expandL outTail) ((0, 0) :: (1, 0) :: (1, 0) :: rb)) |].
  eapply evstep_trans;
    [apply progress_evstep, (in_2_10_exit_flat (prependRepL (m + 1)%N ((2, sep1) :: expandL outTail)) ((1, 0) :: (1, 0) :: rb)) |].
  assert (Hleq : (1, sep0) :: prependRepL (m + 1)%N ((2, sep1) :: expandL outTail) =
                 prependRepL (m + 2)%N ((2, sep1) :: expandL outTail)).
  { replace (m + 2)%N with (1 + (m + 1))%N by lia.
    rewrite (prependRepL_add 1%N (m + 1)%N), prependRepL_1. reflexivity. }
  rewrite Hleq.
  pose proof (sw_in7_rep 2%N ((0, sep0) :: prependRepL (m + 2)%N ((2, sep1) :: expandL outTail)) rb) as H6.
  rewrite prependRepR_2 in H6.
  exact H6.
Qed.

Lemma sym_s9_bounce : forall ticks_m1 inInner outTail,
  checkMiniIter ticks_m1
    (bs_BR0 (el_single 3 sep0 :: inInner) [er_single 0 0; er_single 0 0])
    (bs_AL (el_single 0 sep1 :: el_run10 1%N :: outTail) [er_single 0 0; er_run10 0%N]) = true ->
  forall m : N,
    TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL inInner))
               ((0, sep0) :: prependRepL (m + 3)%N (expandL outTail)).
Proof.
  intros ticks_m1 inInner outTail Hchk m rb.
  pose proof (checkMiniIter_sound _ _ _ Hchk (prependRepR m ((0, 0) :: (1, 0) :: (1, 0) :: rb))) as Hmid.
  cbn [toFlatBase fsApp toFlat expandL expandR app] in Hmid.
  rewrite ?prependRepL_2, ?prependRepR_01, ?prependRepR_1 in Hmid. cbn [app] in Hmid.
  eapply progress_trans; [exact (out_0_run m (expandL inInner) rb) |].
  eapply progress_evstep_trans; [exact Hmid |].
  rewrite <- prependRepR_add1.
  eapply evstep_trans;
    [exact (sw_in19_rep m ((1, sep0) :: (1, sep0) :: expandL outTail) ((0, 0) :: (1, 0) :: (1, 0) :: rb)) |].
  eapply evstep_trans;
    [apply progress_evstep, (in_2_10_exit_flat (prependRepL m ((1, sep0) :: (1, sep0) :: expandL outTail)) ((1, 0) :: (1, 0) :: rb)) |].
  assert (Hleq : (1, sep0) :: prependRepL m ((1, sep0) :: (1, sep0) :: expandL outTail) =
                 prependRepL (m + 3)%N (expandL outTail)).
  { replace (m + 3)%N with (1 + (m + 2))%N by lia.
    rewrite !prependRepL_add, prependRepL_1, prependRepL_2. reflexivity. }
  rewrite Hleq.
  pose proof (sw_in7_rep 2%N ((0, sep0) :: prependRepL (m + 3)%N (expandL outTail)) rb) as H5.
  rewrite prependRepR_2 in H5.
  exact H5.
Qed.

Definition cycState (m : N) : list (nat * Sep3) :=
  (0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_0).

Lemma k1_10_eq_cycState0 : expandL k1_10 = cycState 0%N.
Proof. reflexivity. Qed.

Lemma cyc_step_0 : forall m : N,
  TailBounces 68719476732%N
    ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_0))
    ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_1)).
Proof.
  intros m.
  pose proof (tailBounces_frame_atoms [pa_zr2 (m + 1)%N] rule_1323) as H.
  cbn [atomsToElem atomToElem expandL app] in H.
  repeat (rewrite prependRepL_append_eq in H; cbn [app] in H).
  replace (m + 1 + 1)%N with (m + 2)%N in H by lia.
  exact H.
Qed.

Lemma cyc_step_1 : forall m : N,
  TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_1))
             ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_2)).
Proof.
  intros m. refine (sym_br_bounce 86 cycIn_1 cycOut_1 _ m).
  vm_compute. reflexivity.
Qed.

Lemma cyc_step_2 : forall m : N,
  TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_2))
             ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_3)).
Proof.
  intros m. refine (sym_br_bounce 9 cycIn_2 cycOut_2 _ m).
  vm_compute. reflexivity.
Qed.

Lemma cyc_step_3 : forall m : N,
  TailBounces 68719476729%N
    ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_3))
    ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_4)).
Proof.
  intros m.
  pose proof (tailBounces_frame_atoms [pa_zr2 (m + 1)%N; pa_r 0%N; pa_z2; pa_zr2 2%N] rule_1279) as H.
  assert (Hin : rIn_1279 = el_run10 3%N :: r1279_in_tail) by reflexivity.
  assert (Hout : rOut_1279 = el_run10 2%N :: r1279_out_tail) by reflexivity.
  assert (Hc3 : cycIn_3 = [el_single 2 sep0; el_run10 0%N; el_single 0 sep0; el_single 2 sep0;
    el_single 0 sep0; el_run10 2%N; el_single 2 sep0; el_run10 5%N] ++ r1279_in_tail) by reflexivity.
  assert (Hc4 : cycIn_4 = [el_single 2 sep0; el_run10 0%N; el_single 0 sep0; el_single 2 sep0;
    el_single 0 sep0; el_run10 2%N; el_single 2 sep0; el_run10 4%N] ++ r1279_out_tail) by reflexivity.
  rewrite Hin, Hout in H.
  cbn [atomsToElem atomToElem expandL app] in H.
  repeat (rewrite prependRepL_append_eq in H; cbn [app] in H).
  rewrite <- (prependRepL_add 2%N (3 + 1)%N) in H.
  rewrite <- (prependRepL_add 2%N (2 + 1)%N) in H.
  replace (m + 1 + 1)%N with (m + 2)%N in H by lia.
  rewrite Hc3, Hc4, !expandL_append. cbn [expandL app].
  repeat (rewrite prependRepL_append_eq; cbn [app]).
  exact H.
Qed.

Lemma cyc_step_4 : forall m : N,
  TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_4))
             ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_5)).
Proof.
  intros m. refine (sym_br_bounce 169 cycIn_4 cycOut_4 _ m).
  vm_compute. reflexivity.
Qed.

Lemma cyc_step_5 : forall m : N,
  TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_5))
             ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_6)).
Proof.
  intros m. refine (sym_br_bounce 207 cycIn_5 cycOut_5 _ m).
  vm_compute. reflexivity.
Qed.

Lemma cyc_step_6 : forall m : N,
  TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_6))
             ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_7)).
Proof.
  intros m. refine (sym_br_bounce 37 cycIn_6 cycOut_6 _ m).
  vm_compute. reflexivity.
Qed.

Lemma cyc_step_7 : forall m : N,
  TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_7))
             ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_8)).
Proof.
  intros m. refine (sym_br_bounce 6 cycIn_7 cycOut_7 _ m).
  vm_compute. reflexivity.
Qed.

Lemma cyc_step_8 : forall m : N,
  TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_8))
             ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_9)).
Proof.
  intros m. refine (sym_s8_bounce 48 cycIn_8 cycOut_8 _ m).
  vm_compute. reflexivity.
Qed.

Lemma cyc_step_9 : forall m : N,
  TailBounce ((0, sep0) :: prependRepL (m + 2)%N (expandL cycIn_9))
             ((0, sep0) :: prependRepL (m + 3)%N (expandL cycIn_0)).
Proof.
  apply (sym_s9_bounce 10 cycIn_9 cycIn_0); vm_compute; reflexivity.
Qed.

Lemma sym_cycle : forall m : N,
  TailBounces 137438953469%N (cycState m) (cycState (m + 1)%N).
Proof.
  intros m. unfold cycState.
  pose proof (tb_trans (cyc_step_0 m) (tb_one (cyc_step_1 m))) as H1.
  pose proof (tb_trans H1 (tb_one (cyc_step_2 m))) as H2. clear H1.
  pose proof (tb_trans H2 (cyc_step_3 m)) as H3. clear H2.
  pose proof (tb_trans H3 (tb_one (cyc_step_4 m))) as H4. clear H3.
  pose proof (tb_trans H4 (tb_one (cyc_step_5 m))) as H5. clear H4.
  pose proof (tb_trans H5 (tb_one (cyc_step_6 m))) as H6. clear H5.
  pose proof (tb_trans H6 (tb_one (cyc_step_7 m))) as H7. clear H6.
  pose proof (tb_trans H7 (tb_one (cyc_step_8 m))) as H8. clear H7.
  pose proof (tb_trans H8 (tb_one (cyc_step_9 m))) as H9. clear H8.
  replace (m + 1 + 2)%N with (m + 3)%N by lia.
  exact H9.
Qed.

Definition invCfg (topR m : N) : Q * tape :=
  encodeFlat (fs_CR (prependRepL (topR + 2)%N
    (expandL (atomsToElem frozenAtoms) ++ prependRepL 2%N (cycState m))) []).

Lemma entry_reaches_inv : c0 -[ tm ]->* invCfg 1549833076750%N 0%N.
Proof.
  pose proof prefix_reaches_top50 as Hpre.
  pose proof (topWrap_bounces 1274955169812%N
    (tailBounces_frame_atoms frozenAtoms k1_cycle) ltac:(lia)) as Hstep.
  change (c0 -[ tm ]->*
    encodeFlat (fs_CR (prependRepL (1274955169813 + 1)%N
      (expandL (frozenRawHead ++ k1_0))) [])) in Hpre.
  rewrite (expandL_frozenRaw k1_0) in Hpre.
  change (1274955169813 + 1)%N with (1274955169812 + 2)%N in Hpre.
  rewrite k1_10_eq_cycState0 in Hstep.
  change (1274955169812 + 2 * 137438953469 + 2)%N with (1549833076750 + 2)%N in Hstep.
  exact (evstep_trans tm _ _ _ Hpre (progress_evstep tm _ _ Hstep)).
Qed.

Lemma inv_step : forall topR m : N,
  invCfg topR m -[ tm ]->+ invCfg (topR + 2 * 137438953469)%N (m + 1)%N.
Proof.
  intros topR m. unfold invCfg.
  exact (topWrap_bounces topR (tailBounces_frame_atoms frozenAtoms (sym_cycle m)) ltac:(lia)).
Qed.

Definition invPair (p : N * N) : Q * tape :=
  let (topR, m) := p in invCfg topR m.

Lemma nonhalt_from_inv : ~ halts tm (invPair (1549833076750%N, 0%N)).
Proof.
  apply (progress_nonhalt_simple tm (N * N) invPair (1549833076750%N, 0%N)).
  intros [topR m].
  exists ((topR + 2 * 137438953469)%N, (m + 1)%N).
  exact (inv_step topR m).
Qed.

End M137Main.

Theorem nonhalt : ~ halts tm c0.
Proof.
  exact (multistep_nonhalt tm c0
    (M137Main.invCfg 1549833076750%N 0%N)
    M137Main.entry_reaches_inv
    M137Main.nonhalt_from_inv).
Qed.

End TM1.

Print Assumptions TM1.nonhalt.
