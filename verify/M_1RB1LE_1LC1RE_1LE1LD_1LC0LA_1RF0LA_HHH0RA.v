From Coq Require Import Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import NArith.BinNat.
From Coq Require Import NArith.Nnat.
From Coq Require Import String.
From Coq Require Import Lia.
From BusyCoq Require Import Individual62.
Import ListNotations.

Set Default Goal Selector "!".

Open Scope string_scope.
Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA").
Close Scope string_scope.

Module MachineProof.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope nat_scope.

(** * Section 1: Core Tape Encoding and 4-Mode Machine Semantics *)

Definition Reach (c1 c2 : Q * tape) : Prop :=
  c1 -[ tm ]->* c2.

Lemma reach_refl (c : Q * tape) : Reach c c.
Proof.
  exact (evstep_refl tm c).
Qed.

Lemma reach_trans {c1 c2 c3 : Q * tape} (h1 : Reach c1 c2) (h2 : Reach c2 c3) :
  Reach c1 c3.
Proof.
  exact (evstep_trans tm c1 c2 c3 h1 h2).
Qed.

Fixpoint onesWord (k : nat) : list Sym :=
  match k with
  | 0 => []
  | S k' => S1 :: onesWord k'
  end.

Fixpoint enc1 (L : list nat) : side :=
  match L with
  | [] => const S0
  | a :: L' => (S1 :: onesWord a) *> (S0 >> enc1 L')
  end.

Fixpoint rep4 (k : nat) : list nat :=
  match k with
  | 0 => []
  | S k' => 4 :: rep4 k'
  end.

Fixpoint rep02 (k : nat) : list nat :=
  match k with
  | 0 => []
  | S k' => 0 :: 2 :: rep02 k'
  end.

Definition inc1 (L : list nat) : list nat :=
  match L with
  | [] => [0]
  | a :: L' => (a + 1) :: L'
  end.

Fixpoint addTop (n : nat) (L : list nat) : list nat :=
  match n with
  | 0 => L
  | S n' => addTop n' (inc1 L)
  end.

Definition cfg_EL1 (L R : list nat) : Q * tape := (enc1 L) <{{E}} (enc1 R).
Definition cfg_CL1 (L R : list nat) : Q * tape := (enc1 L) <{{C}} (enc1 R).
Definition cfg_EB1 (L R : list nat) : Q * tape := (E, (enc1 L, S0, enc1 R)).
Definition cfg_BR1 (L R : list nat) : Q * tape := (enc1 L) {{B}}> (enc1 R).
Definition cfg_halt (L : list nat) : Q * tape := ((S1 >> enc1 L) {{F}}> const S0).

Lemma addTop_cons (n : nat) : forall (a : nat) (L : list nat),
  addTop n (a :: L) = (a + n) :: L.
Proof.
  induction n as [| n' IH]; intros a L.
  - cbn. f_equal. lia.
  - cbn [addTop inc1]. rewrite IH. f_equal. lia.
Qed.

Lemma addTop_succ_nil (d : nat) : addTop (d + 1) [] = [d].
Proof.
  replace (d + 1) with (S d) by lia.
  cbn [addTop inc1].
  rewrite addTop_cons.
  reflexivity.
Qed.

Lemma rep4_add (a b : nat) (X : list nat) :
  rep4 (a + b) ++ X = rep4 a ++ (rep4 b ++ X).
Proof.
  induction a as [| a' IH].
  - reflexivity.
  - cbn [Nat.add rep4 app]. rewrite IH. reflexivity.
Qed.

Lemma rep4_snoc (k : nat) (X : list nat) :
  rep4 k ++ (4 :: X) = 4 :: (rep4 k ++ X).
Proof.
  induction k as [| k' IH].
  - reflexivity.
  - cbn [rep4 app]. rewrite IH. reflexivity.
Qed.

Lemma rep02_snoc (k : nat) (X : list nat) :
  rep02 k ++ (0 :: 2 :: X) = 0 :: 2 :: (rep02 k ++ X).
Proof.
  induction k as [| k' IH].
  - reflexivity.
  - cbn [rep02 app]. rewrite IH. reflexivity.
Qed.

Lemma repeat_zero_snoc (n : nat) (R : list nat) :
  repeat 0 n ++ (0 :: R) = repeat 0 (n + 1) ++ R.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - cbn [repeat app]. rewrite IH.
    replace (S n' + 1) with (S (n' + 1)) by lia.
    reflexivity.
Qed.

Lemma repeat_two_snoc (n : nat) (L : list nat) :
  repeat 2 n ++ (2 :: L) = 2 :: (repeat 2 n ++ L).
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - cbn [repeat app]. rewrite IH. reflexivity.
Qed.

Lemma enc1_zero_nil : enc1 [0] = S1 >> const S0.
Proof.
  cbn. rewrite <- const_unfold. reflexivity.
Qed.

Lemma one_cons_enc1 (L : list nat) : S1 >> enc1 L = enc1 (inc1 L).
Proof.
  destruct L as [| a L'].
  - symmetry. exact enc1_zero_nil.
  - cbn [inc1 enc1]. replace (a + 1) with (S a) by lia. reflexivity.
Qed.

Lemma entry_step : Reach c0 (cfg_BR1 [0] []).
Proof.
  unfold Reach, c0, tape0, cfg_BR1.
  rewrite enc1_zero_nil. cbn [enc1].
  eapply evstep_step; [prove_step | simpl_tape; apply evstep_refl].
Qed.

Lemma step_EB1_nil (L : list nat) : Reach (cfg_EB1 L []) (cfg_halt L).
Proof.
  unfold Reach, cfg_EB1, cfg_halt; cbn [enc1].
  eapply evstep_step; [prove_step | simpl_tape; apply evstep_refl].
Qed.

Lemma halts_of_halt (L : list nat) : halts tm (cfg_halt L).
Proof.
  apply halted_halts. reflexivity.
Qed.

Lemma halts_of_EB1_nil (L : list nat) : halts tm (cfg_EB1 L []).
Proof.
  eapply halts_evstep; [exact (halts_of_halt L) | exact (step_EB1_nil L)].
Qed.

Lemma step_EB1_zero (L R' : list nat) :
  Reach (cfg_EB1 L (0 :: R')) (cfg_BR1 (0 :: inc1 L) R').
Proof.
  unfold Reach, cfg_EB1, cfg_BR1. cbn [enc1 onesWord Str_app].
  rewrite <- (one_cons_enc1 L).
  do 3 (eapply evstep_step; [prove_step | simpl_tape]).
  apply evstep_refl.
Qed.

Lemma step_EB1_succ (d : nat) (L R' : list nat) :
  Reach (cfg_EB1 L ((d + 1) :: R')) (cfg_EB1 (inc1 L) (d :: R')).
Proof.
  replace (d + 1) with (S d) by lia.
  unfold Reach, cfg_EB1. rewrite <- (one_cons_enc1 L). cbn [enc1 onesWord Str_app].
  do 3 (eapply evstep_step; [prove_step | simpl_tape]).
  apply evstep_refl.
Qed.

Lemma sweep_EB1_cons (d : nat) : forall (L R' : list nat),
  Reach (cfg_EB1 L (d :: R')) (cfg_BR1 (0 :: addTop (d + 1) L) R').
Proof.
  induction d as [| d' IH]; intros L R'.
  - exact (step_EB1_zero L R').
  - replace (S d' + 1) with (S (d' + 1)) by lia.
    cbn [addTop].
    replace (S d') with (d' + 1) by lia.
    exact (reach_trans (step_EB1_succ d' L R') (IH (inc1 L) R')).
Qed.

Lemma step_BR1_nil (L : list nat) : Reach (cfg_BR1 L []) (cfg_CL1 L [0]).
Proof.
  unfold Reach, cfg_BR1, cfg_CL1. rewrite enc1_zero_nil. cbn [enc1].
  eapply evstep_step; [prove_step | simpl_tape; apply evstep_refl].
Qed.

Lemma step_BR1_zero (L R1 : list nat) :
  Reach (cfg_BR1 L (0 :: R1)) (cfg_EB1 (inc1 L) R1).
Proof.
  unfold Reach, cfg_BR1, cfg_EB1. rewrite <- (one_cons_enc1 L). cbn [enc1 onesWord Str_app].
  eapply evstep_step; [prove_step | simpl_tape; apply evstep_refl].
Qed.

Lemma step_BR1_ge2 (d1 : nat) (L R1 : list nat) :
  Reach (cfg_BR1 L ((d1 + 2) :: R1)) (cfg_EL1 (inc1 (inc1 L)) (d1 :: R1)).
Proof.
  replace (d1 + 2) with (S (S d1)) by lia.
  unfold Reach, cfg_BR1, cfg_EL1.
  rewrite <- (one_cons_enc1 (inc1 L)), <- (one_cons_enc1 L).
  cbn [enc1 onesWord Str_app].
  eapply evstep_step; [prove_step | simpl_tape; apply evstep_refl].
Qed.

Lemma step_BR1_one_nil (L : list nat) :
  Reach (cfg_BR1 L [1]) (cfg_EL1 (inc1 (inc1 L)) []).
Proof.
  unfold Reach, cfg_BR1, cfg_EL1.
  rewrite <- (one_cons_enc1 (inc1 L)), <- (one_cons_enc1 L).
  cbn [enc1 onesWord Str_app].
  eapply evstep_step; [prove_step | simpl_tape; apply evstep_refl].
Qed.

Lemma step_BR1_00 (L R : list nat) :
  Reach (cfg_BR1 (0 :: L) (0 :: 0 :: R)) (cfg_BR1 (0 :: 2 :: L) R).
Proof.
  exact (reach_trans (step_BR1_zero (0 :: L) (0 :: R)) (step_EB1_zero (1 :: L) R)).
Qed.

Lemma sweep_BR_00 (k : nat) : forall (L R : list nat),
  Reach (cfg_BR1 (0 :: L) (repeat 0 (2 * k) ++ R))
        (cfg_BR1 (0 :: (repeat 2 k ++ L)) R).
Proof.
  induction k as [| k' IH]; intros L R.
  - apply reach_refl.
  - replace (2 * S k') with (S (S (2 * k'))) by lia.
    cbn [repeat app].
    pose proof (step_BR1_00 L (repeat 0 (2 * k') ++ R)) as h1.
    pose proof (IH (2 :: L) R) as h2.
    rewrite repeat_two_snoc in h2.
    exact (reach_trans h1 h2).
Qed.

Lemma step_BR1_0d (d : nat) (L R : list nat) :
  Reach (cfg_BR1 (0 :: L) (0 :: d :: R)) (cfg_BR1 (0 :: (d + 2) :: L) R).
Proof.
  pose proof (step_BR1_zero (0 :: L) (d :: R)) as h1.
  pose proof (sweep_EB1_cons d (1 :: L) R) as h2.
  rewrite addTop_cons in h2.
  replace (1 + (d + 1)) with (d + 2) in h2 by lia.
  exact (reach_trans h1 h2).
Qed.

Lemma sweep_BR_p02_one (L R : list nat) :
  Reach (cfg_BR1 (0 :: L) (0 :: 2 :: R)) (cfg_BR1 (0 :: 4 :: L) R).
Proof.
  exact (step_BR1_0d 2 L R).
Qed.

Lemma sweep_BR_p02 (k : nat) : forall (L R : list nat),
  Reach (cfg_BR1 (0 :: L) (rep02 k ++ R)) (cfg_BR1 (0 :: (rep4 k ++ L)) R).
Proof.
  induction k as [| k' IH]; intros L R.
  - apply reach_refl.
  - cbn [rep02 app].
    pose proof (sweep_BR_p02_one L (rep02 k' ++ R)) as h1.
    pose proof (IH (4 :: L) R) as h2.
    rewrite rep4_snoc in h2.
    exact (reach_trans h1 h2).
Qed.

Lemma step_EL1_zero (L' R : list nat) :
  Reach (cfg_EL1 (0 :: L') R) (cfg_CL1 (inc1 L') (inc1 R)).
Proof.
  unfold Reach, cfg_EL1, cfg_CL1.
  rewrite <- (one_cons_enc1 L'), <- (one_cons_enc1 R).
  cbn [enc1 onesWord Str_app].
  do 3 (eapply evstep_step; [prove_step | simpl_tape]).
  apply evstep_refl.
Qed.

Lemma step_EL1_one (L' R : list nat) :
  Reach (cfg_EL1 (1 :: L') R) (cfg_EB1 L' (0 :: R)).
Proof.
  unfold Reach, cfg_EL1, cfg_EB1; cbn [enc1 onesWord Str_app].
  do 2 (eapply evstep_step; [prove_step | simpl_tape]).
  apply evstep_refl.
Qed.

Lemma step_EL1_add_two (a : nat) (L' R : list nat) :
  Reach (cfg_EL1 ((a + 2) :: L') R) (cfg_EL1 (a :: L') (0 :: R)).
Proof.
  replace (a + 2) with (S (S a)) by lia.
  unfold Reach, cfg_EL1; cbn [enc1 onesWord Str_app].
  do 2 (eapply evstep_step; [prove_step | simpl_tape]).
  apply evstep_refl.
Qed.

Lemma peel_EL1_even (k : nat) : forall (a : nat) (L' R : list nat),
  Reach (cfg_EL1 ((a + 2 * k) :: L') R) (cfg_EL1 (a :: L') (repeat 0 k ++ R)).
Proof.
  induction k as [| k' IH]; intros a L' R.
  - replace (a + 2 * 0) with a by lia. apply reach_refl.
  - replace (a + 2 * S k') with ((a + 2 * k') + 2) by lia.
    pose proof (step_EL1_add_two (a + 2 * k') L' R) as h1.
    pose proof (IH a L' (0 :: R)) as h2.
    rewrite repeat_zero_snoc in h2.
    replace (k' + 1) with (S k') in h2 by lia.
    exact (reach_trans h1 h2).
Qed.

Lemma step_EL1_nil_cons (d : nat) (R' : list nat) :
  Reach (cfg_EL1 [] (d :: R')) (cfg_BR1 [0; d] R').
Proof.
  change (cfg_EL1 [] (d :: R')) with (cfg_EB1 [] (d :: R')).
  pose proof (sweep_EB1_cons d [] R') as h1.
  rewrite addTop_succ_nil in h1.
  exact h1.
Qed.

Lemma step_CL1_nil (R : list nat) :
  Reach (cfg_CL1 [] R) (cfg_EL1 [] (inc1 R)).
Proof.
  unfold Reach, cfg_CL1, cfg_EL1. rewrite <- (one_cons_enc1 R). cbn [enc1].
  eapply evstep_step; [prove_step | simpl_tape; apply evstep_refl].
Qed.

Lemma step_CL1_zero (L' R : list nat) :
  Reach (cfg_CL1 (0 :: L') R) (cfg_CL1 L' (inc1 (inc1 R))).
Proof.
  unfold Reach, cfg_CL1.
  rewrite <- (one_cons_enc1 (inc1 R)), <- (one_cons_enc1 R).
  cbn [enc1 onesWord Str_app].
  do 2 (eapply evstep_step; [prove_step | simpl_tape]).
  apply evstep_refl.
Qed.

Lemma step_CL1_one (L' R : list nat) :
  Reach (cfg_CL1 (1 :: L') R) (cfg_CL1 (inc1 L') (inc1 (inc1 R))).
Proof.
  unfold Reach, cfg_CL1.
  rewrite <- (one_cons_enc1 L'), <- (one_cons_enc1 (inc1 R)), <- (one_cons_enc1 R).
  cbn [enc1 onesWord Str_app].
  do 4 (eapply evstep_step; [prove_step | simpl_tape]).
  apply evstep_refl.
Qed.

Lemma step_CL1_two (L' R : list nat) :
  Reach (cfg_CL1 (2 :: L') R) (cfg_EB1 L' (0 :: inc1 R)).
Proof.
  unfold Reach, cfg_CL1, cfg_EB1. cbn [enc1 onesWord Str_app].
  rewrite <- (one_cons_enc1 R).
  do 3 (eapply evstep_step; [prove_step | simpl_tape]).
  apply evstep_refl.
Qed.

Lemma step_CL1_add_three (a : nat) (L' R : list nat) :
  Reach (cfg_CL1 ((a + 3) :: L') R) (cfg_EL1 (a :: L') (0 :: inc1 R)).
Proof.
  replace (a + 3) with (S (S (S a))) by lia.
  unfold Reach, cfg_CL1, cfg_EL1. cbn [enc1 onesWord Str_app].
  rewrite <- (one_cons_enc1 R).
  do 3 (eapply evstep_step; [prove_step | simpl_tape]).
  apply evstep_refl.
Qed.

Lemma sweep_EL_f4_one (L R : list nat) :
  Reach (cfg_EL1 (0 :: 4 :: L) (0 :: R)) (cfg_EL1 (0 :: L) (0 :: 0 :: 2 :: R)).
Proof.
  eapply reach_trans; [exact (step_EL1_zero (4 :: L) (0 :: R)) |].
  eapply reach_trans; [exact (step_CL1_add_three 2 L (1 :: R)) |].
  exact (step_EL1_add_two 0 L (0 :: 2 :: R)).
Qed.

Lemma sweep_EL_f4 (k : nat) : forall (L R : list nat),
  Reach (cfg_EL1 (0 :: (rep4 k ++ L)) (0 :: R)) (cfg_EL1 (0 :: L) (0 :: (rep02 k ++ R))).
Proof.
  induction k as [| k' IH]; intros L R.
  - apply reach_refl.
  - cbn [rep4 app].
    pose proof (sweep_EL_f4_one (rep4 k' ++ L) R) as h1.
    pose proof (IH L (0 :: 2 :: R)) as h2.
    rewrite rep02_snoc in h2.
    exact (reach_trans h1 h2).
Qed.

Lemma sweep_EL3_f4_one (L R : list nat) :
  Reach (cfg_EL1 (3 :: 4 :: L) (0 :: 2 :: 2 :: R))
        (cfg_EL1 (3 :: L) (0 :: 2 :: 2 :: 0 :: 2 :: R)).
Proof.
  eapply reach_trans; [exact (step_EL1_add_two 1 (4 :: L) (0 :: 2 :: 2 :: R)) |].
  eapply reach_trans; [exact (step_EL1_one (4 :: L) (0 :: 0 :: 2 :: 2 :: R)) |].
  eapply reach_trans; [exact (step_EB1_zero (4 :: L) (0 :: 0 :: 2 :: 2 :: R)) |].
  eapply reach_trans; [exact (step_BR1_zero (0 :: 5 :: L) (0 :: 2 :: 2 :: R)) |].
  eapply reach_trans; [exact (step_EB1_zero (1 :: 5 :: L) (2 :: 2 :: R)) |].
  eapply reach_trans; [exact (step_BR1_ge2 0 (0 :: 2 :: 5 :: L) (2 :: R)) |].
  eapply reach_trans; [exact (step_EL1_add_two 0 (2 :: 5 :: L) (0 :: 2 :: R)) |].
  eapply reach_trans; [exact (step_EL1_zero (2 :: 5 :: L) (0 :: 0 :: 2 :: R)) |].
  eapply reach_trans; [exact (step_CL1_add_three 0 (5 :: L) (1 :: 0 :: 2 :: R)) |].
  eapply reach_trans; [exact (step_EL1_zero (5 :: L) (0 :: 2 :: 0 :: 2 :: R)) |].
  exact (step_CL1_add_three 3 L (1 :: 2 :: 0 :: 2 :: R)).
Qed.

Lemma sweep_EL3_f4 (k : nat) : forall (L R : list nat),
  Reach (cfg_EL1 (3 :: (rep4 k ++ L)) (0 :: 2 :: 2 :: R))
        (cfg_EL1 (3 :: L) (0 :: 2 :: 2 :: (rep02 k ++ R))).
Proof.
  induction k as [| k' IH]; intros L R.
  - apply reach_refl.
  - cbn [rep4 app].
    pose proof (sweep_EL3_f4_one (rep4 k' ++ L) R) as h1.
    pose proof (IH L (0 :: 2 :: R)) as h2.
    rewrite rep02_snoc in h2.
    exact (reach_trans h1 h2).
Qed.

(** * Section 1b: Suffix-Polymorphic Symbolic 4-Mode Evaluator *)

Inductive Mode4 : Type := mEL | mCL | mEB | mBR.

Definition eval4 (m : Mode4) (L R S : list nat) : Q * tape :=
  match m with
  | mEL => cfg_EL1 L (R ++ S)
  | mCL => cfg_CL1 L (R ++ S)
  | mEB => cfg_EB1 L (R ++ S)
  | mBR => cfg_BR1 L (R ++ S)
  end.

Definition step4 (st : Mode4 * (list nat * list nat)) :
  option (Mode4 * (list nat * list nat)) :=
  match st with
  | (mEB, (ls, d :: rs')) => Some (mBR, (0 :: addTop (d + 1) ls, rs'))
  | (mBR, (ls, 0 :: rs')) => Some (mEB, (inc1 ls, rs'))
  | (mBR, (ls, S (S d) :: rs')) => Some (mEL, (inc1 (inc1 ls), d :: rs'))
  | (mEL, ([], d :: rs')) => Some (mBR, ([0; d], rs'))
  | (mEL, (0 :: ls', d :: rs')) => Some (mCL, (inc1 ls', (d + 1) :: rs'))
  | (mEL, (1 :: ls', rs)) => Some (mEB, (ls', 0 :: rs))
  | (mEL, (S (S a) :: ls', rs)) => Some (mEL, (a :: ls', 0 :: rs))
  | (mCL, ([], d :: rs')) => Some (mEL, ([], (d + 1) :: rs'))
  | (mCL, (0 :: ls', d :: rs')) => Some (mCL, (ls', (d + 2) :: rs'))
  | (mCL, (1 :: ls', d :: rs')) => Some (mCL, (inc1 ls', (d + 2) :: rs'))
  | (mCL, (2 :: ls', d :: rs')) => Some (mEB, (ls', 0 :: (d + 1) :: rs'))
  | (mCL, (S (S (S a)) :: ls', d :: rs')) => Some (mEL, (a :: ls', 0 :: (d + 1) :: rs'))
  | _ => None
  end.

Lemma step4_sound (s s' : Mode4 * (list nat * list nat))
  (h : step4 s = Some s') (S_tail : list nat) :
  Reach (eval4 (fst s) (fst (snd s)) (snd (snd s)) S_tail)
        (eval4 (fst s') (fst (snd s')) (snd (snd s')) S_tail).
Proof.
  destruct s as [m [L R]].
  destruct m.
  - (* mEL *)
    destruct L as [| v L'].
    + destruct R as [| d R']; [discriminate h |].
      inversion h; subst; clear h; cbn.
      exact (step_EL1_nil_cons d (R' ++ S_tail)).
    + destruct v as [| [| a]].
      * destruct R as [| d R']; [discriminate h |].
        inversion h; subst; clear h; cbn.
        exact (step_EL1_zero L' (d :: R' ++ S_tail)).
      * inversion h; subst; clear h; cbn.
        exact (step_EL1_one L' (R ++ S_tail)).
      * inversion h; subst; clear h; cbn.
        replace (S (S a)) with (a + 2) by lia.
        exact (step_EL1_add_two a L' (R ++ S_tail)).
  - (* mCL *)
    destruct L as [| v L'].
    + destruct R as [| d R']; [discriminate h |].
      inversion h; subst; clear h; cbn.
      exact (step_CL1_nil (d :: R' ++ S_tail)).
    + destruct R as [| d R'].
      * destruct v as [| [| [| a]]]; discriminate h.
      * destruct v as [| [| [| a]]].
        -- inversion h; subst; clear h; cbn.
           pose proof (step_CL1_zero L' (d :: R' ++ S_tail)) as hs.
           cbn [inc1] in hs. replace (d + 1 + 1) with (d + 2) in hs by lia.
           exact hs.
        -- inversion h; subst; clear h; cbn.
           pose proof (step_CL1_one L' (d :: R' ++ S_tail)) as hs.
           cbn [inc1] in hs. replace (d + 1 + 1) with (d + 2) in hs by lia.
           exact hs.
        -- inversion h; subst; clear h; cbn.
           exact (step_CL1_two L' (d :: R' ++ S_tail)).
        -- inversion h; subst; clear h; cbn.
           replace (S (S (S a))) with (a + 3) by lia.
           exact (step_CL1_add_three a L' (d :: R' ++ S_tail)).
  - (* mEB *)
    destruct R as [| d R']; [discriminate h |].
    inversion h; subst; clear h; cbn.
    exact (sweep_EB1_cons d L (R' ++ S_tail)).
  - (* mBR *)
    destruct R as [| d R']; [discriminate h |].
    destruct d as [| [| d2]].
    + inversion h; subst; clear h; cbn.
      exact (step_BR1_zero L (R' ++ S_tail)).
    + discriminate h.
    + inversion h; subst; clear h; cbn.
      replace (S (S d2)) with (d2 + 2) by lia.
      exact (step_BR1_ge2 d2 L (R' ++ S_tail)).
Qed.

Fixpoint run4 (n : nat) (s : Mode4 * (list nat * list nat)) :
  option (Mode4 * (list nat * list nat)) :=
  match n with
  | 0 => Some s
  | S n' =>
    match step4 s with
    | None => None
    | Some s1 => run4 n' s1
    end
  end.

Lemma run4_sound (n : nat) : forall (s s' : Mode4 * (list nat * list nat)),
  run4 n s = Some s' -> forall (S_tail : list nat),
    Reach (eval4 (fst s) (fst (snd s)) (snd (snd s)) S_tail)
          (eval4 (fst s') (fst (snd s')) (snd (snd s')) S_tail).
Proof.
  induction n as [| n' IH]; intros s s' h S_tail.
  - inversion h; subst. apply reach_refl.
  - cbn [run4] in h.
    destruct (step4 s) as [s1 |] eqn:hs; [| discriminate h].
    exact (reach_trans (step4_sound s s1 hs S_tail) (IH s1 s' h S_tail)).
Qed.

Fixpoint natListEq (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => andb (Nat.eqb x y) (natListEq xs ys)
  | _, _ => false
  end.

Lemma natListEq_eq : forall (l1 l2 : list nat), natListEq l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [| x xs IH]; intros [| y ys] h; try discriminate h.
  - reflexivity.
  - cbn [natListEq] in h.
    apply Bool.andb_true_iff in h as [h1 h2].
    apply Nat.eqb_eq in h1.
    f_equal; [exact h1 | exact (IH ys h2)].
Qed.

Definition mode4Eq (m1 m2 : Mode4) : bool :=
  match m1, m2 with
  | mEL, mEL => true
  | mCL, mCL => true
  | mEB, mEB => true
  | mBR, mBR => true
  | _, _ => false
  end.

Lemma mode4Eq_eq (m1 m2 : Mode4) (h : mode4Eq m1 m2 = true) : m1 = m2.
Proof.
  destruct m1, m2; try reflexivity; discriminate h.
Qed.

Definition checkRun4 (n : nat) (s s' : Mode4 * (list nat * list nat)) : bool :=
  match run4 n s with
  | None => false
  | Some s1 =>
    andb (andb (mode4Eq (fst s1) (fst s')) (natListEq (fst (snd s1)) (fst (snd s'))))
         (natListEq (snd (snd s1)) (snd (snd s')))
  end.

Lemma run4_of_check {n : nat} {s s' : Mode4 * (list nat * list nat)}
  (h : checkRun4 n s s' = true) (S_tail : list nat) :
  Reach (eval4 (fst s) (fst (snd s)) (snd (snd s)) S_tail)
        (eval4 (fst s') (fst (snd s')) (snd (snd s')) S_tail).
Proof.
  unfold checkRun4 in h.
  destruct (run4 n s) as [s1 |] eqn:hr; [| discriminate h].
  apply Bool.andb_true_iff in h as [h12 h3].
  apply Bool.andb_true_iff in h12 as [h1 h2].
  destruct s1 as [m1 [l1 r1]], s' as [m2 [l2 r2]]; cbn in h1, h2, h3.
  rewrite (mode4Eq_eq m1 m2 h1), (natListEq_eq l1 l2 h2), (natListEq_eq r1 r2 h3) in hr.
  exact (run4_sound n s (m2, (l2, r2)) hr S_tail).
Qed.

Lemma rep4_succ_r (k : nat) : rep4 (k + 1) = 4 :: rep4 k.
Proof.
  replace (k + 1) with (S k) by lia. reflexivity.
Qed.

Lemma rep02_succ_r (k : nat) : rep02 (k + 1) = 0 :: 2 :: rep02 k.
Proof.
  replace (k + 1) with (S k) by lia. reflexivity.
Qed.

Lemma rstep_lemma {g1 c1 c2 g3 : Q * tape}
  (h : Reach c1 c2) (heq : g1 = c1) (hrest : Reach c2 g3) : Reach g1 g3.
Proof.
  subst g1. exact (reach_trans h hrest).
Qed.

Lemma rdone_lemma {g1 c1 c2 g2 : Q * tape}
  (h : Reach c1 c2) (heq1 : g1 = c1) (heq2 : c2 = g2) : Reach g1 g2.
Proof.
  subst g1 g2. exact h.
Qed.

Ltac eq_cfg :=
  cbn [inc1 addTop];
  repeat rewrite rep4_succ_r;
  repeat rewrite rep02_succ_r;
  repeat rewrite <- app_assoc;
  cbn [app];
  solve [repeat (reflexivity || lia || f_equal)].

Ltac rstep H :=
  eapply (rstep_lemma H); [eq_cfg |].

Ltac rdone H :=
  eapply (rdone_lemma H); [eq_cfg | eq_cfg].

(** * Section 2: Universal Weight wf, W, psi and Master Theorem mCL_bump_spec *)

Fixpoint div4 (n : nat) : nat :=
  match n with
  | S (S (S (S n'))) => S (div4 n')
  | _ => 0
  end.

Lemma div4_spec (n : nat) : 4 * div4 n <= n /\ n < 4 * div4 n + 4.
Proof.
  induction n as [n IH] using strong_induction.
  destruct n as [| [| [| [| n']]]]; cbn [div4]; try lia.
  specialize (IH n' ltac:(lia)); lia.
Qed.

Lemma mod4_cases (n : nat) :
  exists q, n = 4 * q \/ n = 4 * q + 1 \/ n = 4 * q + 2 \/ n = 4 * q + 3.
Proof.
  induction n as [| n' [q IH]].
  - exists 0; left; reflexivity.
  - destruct IH as [-> | [-> | [-> | ->]]].
    + exists q; right; left; lia.
    + exists q; right; right; left; lia.
    + exists q; right; right; right; lia.
    + exists (q + 1); left; lia.
Qed.

Definition wf (v : nat) : nat :=
  match v with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 2
  | 6 => 2
  | _ => div4 v + 2
  end.

Lemma wf_ge7 (v : nat) (hv : 7 <= v) : wf v = div4 v + 2.
Proof.
  do 7 (destruct v as [| v]; [lia |]).
  reflexivity.
Qed.

Fixpoint W (L : list nat) : nat :=
  match L with
  | [] => 0
  | v :: L' => wf v + W L'
  end.

Definition psi (L : list nat) : nat :=
  match L with
  | [] => 0
  | v :: M => if Nat.eqb v 2 then 2 * W M + 1 else 2 * (wf v + W M)
  end.

Lemma psi_cons_two (M : list nat) : psi (2 :: M) = 2 * W M + 1.
Proof.
  reflexivity.
Qed.

Lemma psi_cons_four (M : list nat) : psi (4 :: M) = 2 * W M.
Proof.
  cbn [psi Nat.eqb W wf]; lia.
Qed.

Lemma psi_cons_ne2 {v : nat} (hv : v <> 2) (M : list nat) :
  psi (v :: M) = 2 * (wf v + W M).
Proof.
  unfold psi.
  destruct (Nat.eqb v 2) eqn:hb.
  - apply Nat.eqb_eq in hb. exfalso; exact (hv hb).
  - reflexivity.
Qed.

Lemma psi_le (L : list nat) : psi L <= 2 * W L.
Proof.
  destruct L as [| v M].
  - cbn. lia.
  - destruct (Nat.eq_dec v 2) as [-> | hv].
    + rewrite psi_cons_two. cbn [W wf]. lia.
    + rewrite (psi_cons_ne2 hv). cbn [W]. lia.
Qed.

Lemma wf_add_one_le (v : nat) : wf (v + 1) <= wf v + 2.
Proof.
  do 7 (destruct v as [| v]; [cbn; lia |]).
  set (v0 := S (S (S (S (S (S (S v))))))).
  rewrite (wf_ge7 (v0 + 1)) by (unfold v0; lia).
  rewrite (wf_ge7 v0) by (unfold v0; lia).
  pose proof (div4_spec (v0 + 1)); pose proof (div4_spec v0).
  lia.
Qed.

Lemma wf_add_one_le_ne4 {v : nat} (hv : v <> 4) : wf (v + 1) <= wf v + 1.
Proof.
  do 7 (destruct v as [| v]; [try (exfalso; apply hv; reflexivity); cbn; lia |]).
  set (v0 := S (S (S (S (S (S (S v))))))).
  rewrite (wf_ge7 (v0 + 1)) by (unfold v0; lia).
  rewrite (wf_ge7 v0) by (unfold v0; lia).
  pose proof (div4_spec (v0 + 1)); pose proof (div4_spec v0).
  lia.
Qed.

Lemma wf_even_step (c : nat) : wf (2 * (c + 1) + 4) <= wf (2 * c + 4) + 2.
Proof.
  do 3 (destruct c as [| c]; [cbn; lia |]).
  set (c0 := S (S (S c))).
  rewrite (wf_ge7 (2 * (c0 + 1) + 4)) by (unfold c0; lia).
  rewrite (wf_ge7 (2 * c0 + 4)) by (unfold c0; lia).
  pose proof (div4_spec (2 * (c0 + 1) + 4)); pose proof (div4_spec (2 * c0 + 4)).
  lia.
Qed.

Lemma wf_even_mono {c : nat} (hc : 1 <= c) : wf (2 * c + 2) <= wf (2 * c + 4).
Proof.
  do 3 (destruct c as [| c]; [try lia; cbn; lia |]).
  set (c0 := S (S (S c))).
  rewrite (wf_ge7 (2 * c0 + 2)) by (unfold c0; lia).
  rewrite (wf_ge7 (2 * c0 + 4)) by (unfold c0; lia).
  pose proof (div4_spec (2 * c0 + 2)); pose proof (div4_spec (2 * c0 + 4)).
  lia.
Qed.

Lemma W_inc1_le (L : list nat) : W (inc1 L) <= W L + 2.
Proof.
  destruct L as [| v M].
  - cbn. lia.
  - cbn [inc1 W]. pose proof (wf_add_one_le v). lia.
Qed.

Lemma W_rep4_append (k : nat) (L : list nat) : W (rep4 k ++ L) = W L.
Proof.
  induction k as [| k' IH].
  - reflexivity.
  - cbn [rep4 app W wf]. exact IH.
Qed.

Lemma W_repeat_two (k : nat) (L : list nat) : W (repeat 2 k ++ L) = k + W L.
Proof.
  induction k as [| k' IH].
  - reflexivity.
  - cbn [repeat app W wf]. rewrite IH. lia.
Qed.

Lemma psi_repeat_two_succ (k : nat) (L : list nat) :
  psi (repeat 2 (k + 1) ++ L) = 2 * (k + W L) + 1.
Proof.
  replace (k + 1) with (S k) by lia.
  cbn [repeat app].
  rewrite psi_cons_two, W_repeat_two.
  reflexivity.
Qed.

Lemma wf_4r3 (r : nat) : wf (4 * r + 3) = r + 2.
Proof.
  destruct r as [| r'].
  - reflexivity.
  - rewrite wf_ge7 by lia.
    pose proof (div4_spec (4 * S r' + 3)). lia.
Qed.

Lemma wf_inc_class (v : nat) :
  (v = 4) \/ (wf (v + 1) <= wf v) \/ (v = 0) \/ (v = 2) \/ (v = 6) \/
  (exists m, v = 4 * (m + 1) + 3).
Proof.
  do 7 (destruct v as [| v]; [
    try (left; reflexivity);
    try (right; left; cbn; lia);
    try (right; right; left; reflexivity);
    try (right; right; right; left; reflexivity);
    try (right; right; right; right; left; reflexivity)
  |]).
  destruct (mod4_cases v) as [q [hq | [hq | [hq | hq]]]].
  - right; right; right; right; right.
    exists q. lia.
  - right; left.
    set (v0 := S (S (S (S (S (S (S v))))))).
    rewrite (wf_ge7 (v0 + 1)) by (unfold v0; lia).
    rewrite (wf_ge7 v0) by (unfold v0; lia).
    pose proof (div4_spec (v0 + 1)); pose proof (div4_spec v0).
    unfold v0 in *; lia.
  - right; left.
    set (v0 := S (S (S (S (S (S (S v))))))).
    rewrite (wf_ge7 (v0 + 1)) by (unfold v0; lia).
    rewrite (wf_ge7 v0) by (unfold v0; lia).
    pose proof (div4_spec (v0 + 1)); pose proof (div4_spec v0).
    unfold v0 in *; lia.
  - right; left.
    set (v0 := S (S (S (S (S (S (S v))))))).
    rewrite (wf_ge7 (v0 + 1)) by (unfold v0; lia).
    rewrite (wf_ge7 v0) by (unfold v0; lia).
    pose proof (div4_spec (v0 + 1)); pose proof (div4_spec v0).
    unfold v0 in *; lia.
Qed.

Fixpoint strip4 (L : list nat) : nat * list nat :=
  match L with
  | [] => (0, [])
  | a :: L' =>
    if Nat.eqb a 4 then
      let r := strip4 L' in (fst r + 1, snd r)
    else (0, a :: L')
  end.

Lemma strip4_spec (L : list nat) :
  L = rep4 (fst (strip4 L)) ++ snd (strip4 L) /\
  (forall v T, snd (strip4 L) = v :: T -> v <> 4).
Proof.
  induction L as [| a M [ih1 ih2]].
  - split; [reflexivity | intros v T h; discriminate h].
  - cbn [strip4].
    destruct (Nat.eqb a 4) eqn:ha.
    + apply Nat.eqb_eq in ha; subst a.
      cbn [fst snd]. rewrite rep4_succ_r. cbn [app].
      split; [f_equal; exact ih1 | exact ih2].
    + apply Nat.eqb_neq in ha.
      cbn [fst snd rep4 app].
      split; [reflexivity | intros v T h; inversion h; subst; exact ha].
Qed.

Lemma cl_6_rep4_step (k c : nat) (M' S_tail : list nat) :
  Reach (cfg_CL1 (6 :: (rep4 (k + 1) ++ M')) ((2 * c + 1) :: S_tail))
        (cfg_EL1 (0 :: inc1 M') (rep02 (k + 2) ++ ((2 * c) :: S_tail))).
Proof.
  rstep (step_CL1_add_three 3 (rep4 (k + 1) ++ M') ((2 * c + 1) :: S_tail)).
  rstep (step_EL1_add_two 1 (4 :: rep4 k ++ M') (0 :: (2 * c + 2) :: S_tail)).
  rstep (step_EL1_one (4 :: rep4 k ++ M') (0 :: 0 :: (2 * c + 2) :: S_tail)).
  rstep (step_EB1_zero (4 :: rep4 k ++ M') (0 :: 0 :: (2 * c + 2) :: S_tail)).
  rstep (step_BR1_zero (0 :: 5 :: rep4 k ++ M') (0 :: (2 * c + 2) :: S_tail)).
  rstep (step_EB1_zero (1 :: 5 :: rep4 k ++ M') ((2 * c + 2) :: S_tail)).
  rstep (step_BR1_ge2 (2 * c) (0 :: 2 :: 5 :: rep4 k ++ M') S_tail).
  rstep (step_EL1_add_two 0 (2 :: 5 :: rep4 k ++ M') ((2 * c) :: S_tail)).
  rstep (step_EL1_zero (2 :: 5 :: rep4 k ++ M') (0 :: (2 * c) :: S_tail)).
  rstep (step_CL1_add_three 0 (5 :: rep4 k ++ M') (1 :: (2 * c) :: S_tail)).
  rstep (step_EL1_zero (5 :: rep4 k ++ M') (0 :: 2 :: (2 * c) :: S_tail)).
  rstep (step_CL1_add_three 3 (rep4 k ++ M') (1 :: 2 :: (2 * c) :: S_tail)).
  rstep (sweep_EL3_f4 k M' ((2 * c) :: S_tail)).
  rstep (step_EL1_add_two 1 M' (0 :: 2 :: 2 :: (rep02 k ++ (2 * c) :: S_tail))).
  rstep (step_EL1_one M' (0 :: 0 :: 2 :: 2 :: (rep02 k ++ (2 * c) :: S_tail))).
  rstep (step_EB1_zero M' (0 :: 0 :: 2 :: 2 :: (rep02 k ++ (2 * c) :: S_tail))).
  rstep (step_BR1_zero (0 :: inc1 M') (0 :: 2 :: 2 :: (rep02 k ++ (2 * c) :: S_tail))).
  rstep (step_EB1_zero (1 :: inc1 M') (2 :: 2 :: (rep02 k ++ (2 * c) :: S_tail))).
  rstep (step_BR1_ge2 0 (0 :: 2 :: inc1 M') (2 :: (rep02 k ++ (2 * c) :: S_tail))).
  rstep (step_EL1_add_two 0 (2 :: inc1 M') (0 :: 2 :: (rep02 k ++ (2 * c) :: S_tail))).
  rstep (step_EL1_zero (2 :: inc1 M') (0 :: 0 :: 2 :: (rep02 k ++ (2 * c) :: S_tail))).
  replace (k + 2) with ((k + 1) + 1) by lia.
  rdone (step_CL1_add_three 0 (inc1 M') (1 :: 0 :: 2 :: (rep02 k ++ (2 * c) :: S_tail))).
Qed.

Lemma cl_6_nil_step (c : nat) (S_tail : list nat) :
  Reach (cfg_CL1 [6] ((2 * c + 1) :: S_tail))
        (cfg_BR1 [0; 2 * c + 2; 2; 4; 4; 4] S_tail).
Proof.
  rstep (step_CL1_add_three 3 [] ((2 * c + 1) :: S_tail)).
  rstep (step_EL1_add_two 1 [] (0 :: (2 * c + 2) :: S_tail)).
  rstep (step_EL1_one [] (0 :: 0 :: (2 * c + 2) :: S_tail)).
  rstep (step_EB1_zero [] (0 :: 0 :: (2 * c + 2) :: S_tail)).
  rstep (step_BR1_00 [0] ((2 * c + 2) :: S_tail)).
  rstep (step_BR1_ge2 (2 * c) [0; 2; 0] S_tail).
  rstep (step_EL1_add_two 0 [2; 0] ((2 * c) :: S_tail)).
  assert (h8 : Reach (cfg_EL1 [0; 2; 0] (0 :: (2 * c) :: S_tail))
                     (cfg_BR1 [0; 2; 4; 4; 4] (0 :: (2 * c) :: S_tail))).
  { exact (@run4_of_check 50 (mEL, ([0; 2; 0], [0])) (mBR, ([0; 2; 4; 4; 4], [0]))
      ltac:(vm_compute; reflexivity) ((2 * c) :: S_tail)). }
  rstep h8.
  rdone (step_BR1_0d (2 * c) [2; 4; 4; 4] S_tail).
Qed.

Lemma br_6_202_step (S_tail : list nat) :
  Reach (cfg_BR1 [0; 6] (2 :: 0 :: 2 :: S_tail)) (cfg_BR1 (0 :: rep4 6) (0 :: S_tail)).
Proof.
  exact (@run4_of_check 98 (mBR, ([0; 6], [2; 0; 2])) (mBR, (0 :: rep4 6, [0]))
    ltac:(vm_compute; reflexivity) S_tail).
Qed.

Lemma br_rep4_6_002_step (S_tail : list nat) :
  Reach (cfg_BR1 (0 :: rep4 6) (0 :: 0 :: 2 :: S_tail)) (cfg_BR1 (0 :: 2 :: rep4 8) S_tail).
Proof.
  exact (@run4_of_check 83 (mBR, (0 :: rep4 6, [0; 0; 2])) (mBR, (0 :: 2 :: rep4 8, []))
    ltac:(vm_compute; reflexivity) S_tail).
Qed.

Lemma br_46_002_step (S_tail : list nat) :
  Reach (cfg_BR1 [0; 4; 6] (0 :: 0 :: 2 :: S_tail)) (cfg_BR1 (0 :: 2 :: 2 :: rep4 7) S_tail).
Proof.
  exact (@run4_of_check 179 (mBR, ([0; 4; 6], [0; 0; 2])) (mBR, (0 :: 2 :: 2 :: rep4 7, []))
    ltac:(vm_compute; reflexivity) S_tail).
Qed.

Lemma br_42_002_step (L' R : list nat) :
  Reach (cfg_BR1 (0 :: 4 :: 2 :: L') (0 :: 0 :: 2 :: R))
        (cfg_EL1 (0 :: L') (0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R)).
Proof.
  rstep (step_BR1_00 (4 :: 2 :: L') (2 :: R)).
  rstep (step_BR1_ge2 0 (0 :: 2 :: 4 :: 2 :: L') R).
  rstep (step_EL1_add_two 0 (2 :: 4 :: 2 :: L') (0 :: R)).
  rstep (step_EL1_zero (2 :: 4 :: 2 :: L') (0 :: 0 :: R)).
  rstep (step_CL1_add_three 0 (4 :: 2 :: L') (1 :: 0 :: R)).
  rstep (sweep_EL_f4_one (2 :: L') (2 :: 0 :: R)).
  rstep (step_EL1_zero (2 :: L') (0 :: 0 :: 2 :: 2 :: 0 :: R)).
  rdone (step_CL1_add_three 0 L' (1 :: 0 :: 2 :: 2 :: 0 :: R)).
Qed.

Definition GoodOut (M : list nat) (c : nat) (S_tail : list nat) : Prop :=
  (exists L', Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail)) (cfg_BR1 (0 :: L') S_tail) /\
              2 * W L' <= psi M + 2 * wf (2 * c + 4) /\
              (c = 0 -> (exists T, M = 5 :: T) -> psi L' + 1 <= psi M)) \/
  (exists L', Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail)) (cfg_BR1 (0 :: L') (0 :: S_tail)) /\
              2 * W L' + 1 <= psi M).

Definition ELResult (L S_tail : list nat) : Prop :=
  (exists L', Reach (cfg_EL1 (0 :: L) (0 :: S_tail)) (cfg_BR1 (0 :: L') S_tail) /\
              2 * W L' <= psi L) \/
  (exists L', Reach (cfg_EL1 (0 :: L) (0 :: S_tail)) (cfg_BR1 (0 :: L') (0 :: S_tail)) /\
              2 * W L' + 1 <= psi L).

Definition ELIH (limit : nat) : Prop :=
  forall L, psi L < limit -> forall S_tail, ELResult L S_tail.

Lemma good_to_el {L S_tail} : GoodOut L 0 S_tail -> ELResult L S_tail.
Proof.
  intros [[T [hr [hw _]]] | [T [hr hw]]].
  - left. exists T.
    split; [exact (reach_trans (step_EL1_zero L (0 :: S_tail)) hr) | cbn [Nat.mul Nat.add wf] in hw; lia].
  - right. exists T.
    split; [exact (reach_trans (step_EL1_zero L (0 :: S_tail)) hr) | exact hw].
Qed.

Lemma step_even_ih {limit : nat} (ihEL : ELIH limit) (c : nat) :
  forall (L : list nat), psi L < limit -> forall (S_tail : list nat),
    (exists L', Reach (cfg_BR1 (0 :: L) ((2 * c + 2) :: S_tail)) (cfg_BR1 (0 :: L') (0 :: S_tail)) /\
                2 * W L' <= psi L) \/
    (exists L', Reach (cfg_BR1 (0 :: L) ((2 * c + 2) :: S_tail)) (cfg_BR1 (0 :: L') S_tail) /\
                (c = 0 -> psi L' <= psi L /\ 2 * W L' <= psi L + 1 /\ exists T, L' = 2 :: T) /\
                (1 <= c -> 2 * W L' <= psi L + 2 * wf (2 * c + 2))).
Proof.
  induction c as [| c' IHc]; intros L hL S_tail.
  - assert (hst : Reach (cfg_BR1 (0 :: L) ((2 * 0 + 2) :: S_tail)) (cfg_EL1 (0 :: L) (0 :: 0 :: S_tail))).
    { rstep (step_BR1_ge2 0 (0 :: L) S_tail).
      rdone (step_EL1_add_two 0 L (0 :: S_tail)). }
    destruct (ihEL L hL (0 :: S_tail)) as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
    + left. exists L1. split; [exact (reach_trans hst hr1) | exact hw1].
    + right. exists (2 :: L1).
      split; [exact (reach_trans (reach_trans hst hr1) (step_BR1_00 L1 S_tail)) |].
      split; [| lia].
      intros _. split; [rewrite psi_cons_two; lia |].
      split; [cbn [W wf]; lia | exists L1; reflexivity].
  - assert (hst : Reach (cfg_BR1 (0 :: L) ((2 * S c' + 2) :: S_tail))
                        (cfg_EL1 (0 :: L) (0 :: (2 * c' + 2) :: S_tail))).
    { rstep (step_BR1_ge2 (2 * c' + 2) (0 :: L) S_tail).
      rdone (step_EL1_add_two 0 L ((2 * c' + 2) :: S_tail)). }
    destruct (ihEL L hL ((2 * c' + 2) :: S_tail)) as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
    + assert (hp1 : psi L1 < limit) by (pose proof (psi_le L1); lia).
      destruct (IHc L1 hp1 S_tail) as [[L2 [hr2 hw2]] | [L2 [hr2 [h0 hge1]]]].
      * left. exists L2.
        split; [exact (reach_trans (reach_trans hst hr1) hr2) | pose proof (psi_le L1); lia].
      * right. exists L2.
        split; [exact (reach_trans (reach_trans hst hr1) hr2) |].
        split; [lia | intros _].
        destruct c' as [| c''].
        -- destruct (h0 eq_refl) as [hp2 [_ [T ->]]].
           rewrite psi_cons_two in hp2.
           pose proof (psi_le L1).
           replace (2 * S 0 + 2) with 4 by lia.
           cbn [W wf]. lia.
        -- pose proof (hge1 ltac:(lia)) as hrec.
           pose proof (@wf_even_mono (S c'') ltac:(lia)) as hmono.
           pose proof (psi_le L1).
           replace (2 * S (S c'') + 2) with (2 * S c'' + 4) by lia.
           lia.
    + right. exists ((2 * S c' + 2) :: L1).
      split.
      * pose proof (step_BR1_0d (2 * c' + 2) L1 S_tail) as h2.
        replace (2 * c' + 2 + 2) with (2 * S c' + 2) in h2 by lia.
        exact (reach_trans (reach_trans hst hr1) h2).
      * split; [lia | intros _; cbn [W]; lia].
Qed.

Lemma finish_no0 {M L S_tail : list nat} {c : nat}
  (ihEL : ELIH (psi M))
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail)) (cfg_BR1 (0 :: L) ((2 * c) :: S_tail)))
  (hw : 2 * W L + 1 <= psi M) :
  GoodOut M c S_tail.
Proof.
  destruct c as [| c'].
  - right. exists L. split; [exact hr | exact hw].
  - assert (hlt : psi L < psi M) by (pose proof (psi_le L); lia).
    assert (hr' : Reach (cfg_CL1 (inc1 M) ((2 * S c' + 1) :: S_tail))
                        (cfg_BR1 (0 :: L) ((2 * c' + 2) :: S_tail))) by (rdone hr).
    destruct (step_even_ih ihEL c' L hlt S_tail) as [[L1 [hr1 hw1]] | [L1 [hr1 [h0 hge1]]]].
    + right. exists L1.
      split; [exact (reach_trans hr' hr1) | pose proof (psi_le L); lia].
    + left. exists L1.
      split; [exact (reach_trans hr' hr1) |].
      split; [| lia].
      destruct c' as [| c''].
      * destruct (h0 eq_refl) as [_ [hw1 _]].
        pose proof (psi_le L).
        replace (2 * S 0 + 4) with 6 by lia.
        cbn [wf]. lia.
      * pose proof (hge1 ltac:(lia)) as hrec.
        pose proof (@wf_even_mono (S c'') ltac:(lia)) as hmono1.
        pose proof (@wf_even_mono (S (S c'')) ltac:(lia)) as hmono2.
        replace (2 * S (S c'') + 2) with (2 * S c'' + 4) in hmono2 by lia.
        pose proof (psi_le L).
        lia.
Qed.

Lemma finish_has0 {M L S_tail : list nat} {c : nat}
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail)) (cfg_BR1 (0 :: L) (0 :: (2 * c) :: S_tail)))
  (hw : 2 * W L + 2 <= psi M) :
  GoodOut M c S_tail.
Proof.
  pose proof (reach_trans hr (step_BR1_0d (2 * c) L S_tail)) as h1.
  left. exists ((2 * c + 2) :: L).
  split; [exact h1 |].
  split.
  - destruct c as [| c'].
    + cbn [Nat.mul Nat.add W wf]. lia.
    + pose proof (@wf_even_mono (S c') ltac:(lia)). cbn [W]. lia.
  - intros -> _. rewrite psi_cons_two. lia.
Qed.

Lemma step_p02_one_ih {limit : nat} (ihEL : ELIH limit)
  (L : list nat) (hL : psi L < limit) (S_tail : list nat) :
  (exists L', Reach (cfg_BR1 (0 :: L) (0 :: 0 :: 2 :: S_tail)) (cfg_BR1 (0 :: L') (0 :: S_tail)) /\
              psi L' + 1 <= psi L /\ 2 * W L' <= psi L) \/
  (exists L', Reach (cfg_BR1 (0 :: L) (0 :: 0 :: 2 :: S_tail)) (cfg_BR1 (0 :: 2 :: L') S_tail) /\
              2 * W L' <= psi L).
Proof.
  assert (h0 : Reach (cfg_BR1 (0 :: L) (0 :: 0 :: 2 :: S_tail))
                     (cfg_EL1 (0 :: L) (0 :: 2 :: 0 :: S_tail))).
  { rstep (step_BR1_00 L (2 :: S_tail)).
    rstep (step_BR1_ge2 0 (0 :: 2 :: L) S_tail).
    rstep (step_EL1_add_two 0 (2 :: L) (0 :: S_tail)).
    rstep (step_EL1_zero (2 :: L) (0 :: 0 :: S_tail)).
    rdone (step_CL1_add_three 0 L (1 :: 0 :: S_tail)). }
  destruct (ihEL L hL (2 :: 0 :: S_tail)) as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
  - assert (hp1 : psi L1 < limit) by (pose proof (psi_le L1); lia).
    assert (h2 : Reach (cfg_BR1 (0 :: L1) (2 :: 0 :: S_tail))
                       (cfg_EL1 (0 :: L1) (0 :: 0 :: 0 :: S_tail))).
    { rstep (step_BR1_ge2 0 (0 :: L1) (0 :: S_tail)).
      rdone (step_EL1_add_two 0 L1 (0 :: 0 :: S_tail)). }
    destruct (ihEL L1 hp1 (0 :: 0 :: S_tail)) as [[L2 [hr2 hw2]] | [L2 [hr2 hw2]]].
    + right. exists L2.
      split.
      * exact (reach_trans (reach_trans (reach_trans h0 hr1) (reach_trans h2 hr2)) (step_BR1_00 L2 S_tail)).
      * pose proof (psi_le L1); lia.
    + left. exists (2 :: L2).
      split.
      * exact (reach_trans (reach_trans (reach_trans h0 hr1) (reach_trans h2 hr2)) (step_BR1_00 L2 (0 :: S_tail))).
      * rewrite psi_cons_two; cbn [W wf]; pose proof (psi_le L1); lia.
  - left. exists (4 :: L1).
    split.
    + exact (reach_trans (reach_trans h0 hr1) (sweep_BR_p02_one L1 (0 :: S_tail))).
    + rewrite psi_cons_four; cbn [W wf]; lia.
Qed.

Lemma step_p02_many_ih {limit : nat} (ihEL : ELIH limit) (k : nat) :
  forall (L : list nat), psi L < limit -> forall (S_tail : list nat),
    (exists L', Reach (cfg_BR1 (0 :: L) (0 :: (rep02 (k + 1) ++ S_tail)))
                      (cfg_BR1 (0 :: L') (0 :: S_tail)) /\
                psi L' + (k + 1) <= psi L /\ 2 * W L' <= psi L) \/
    (exists a L', Reach (cfg_BR1 (0 :: L) (0 :: (rep02 (k + 1) ++ S_tail)))
                        (cfg_BR1 (0 :: (rep4 a ++ 2 :: L')) S_tail) /\
                  2 * W L' <= psi L).
Proof.
  induction k as [| k' IHk]; intros L hL S_tail.
  - cbn [Nat.add rep02 app].
    destruct (step_p02_one_ih ihEL L hL S_tail) as [[L1 [hr1 [hp1 hw1]]] | [L1 [hr1 hw1]]].
    + left. exists L1. split; [exact hr1 | lia].
    + right. exists 0, L1. cbn [rep4 app]. split; [exact hr1 | exact hw1].
  - replace (S k' + 1) with (S (k' + 1)) by lia.
    cbn [rep02 app].
    destruct (step_p02_one_ih ihEL L hL (rep02 (k' + 1) ++ S_tail))
      as [[L1 [hr1 [hp1 hw1]]] | [L1 [hr1 hw1]]].
    + assert (hp1' : psi L1 < limit) by lia.
      destruct (IHk L1 hp1' S_tail) as [[L2 [hr2 [hp2 hw2]]] | [a [L2 [hr2 hw2]]]].
      * left. exists L2. split; [exact (reach_trans hr1 hr2) | lia].
      * right. exists a, L2. split; [exact (reach_trans hr1 hr2) | lia].
    + right. exists (k' + 1), L1.
      split; [exact (reach_trans hr1 (sweep_BR_p02 (k' + 1) (2 :: L1) S_tail)) | exact hw1].
Qed.

Definition IsEven (n : nat) : Prop := exists q, n = 2 * q.

Lemma finish_0_p02_2c {M L S_tail : list nat} {k c : nat}
  (ihEL : ELIH (psi M))
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail))
              (cfg_BR1 (0 :: L) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))))
  (heven : IsEven (psi M))
  (hp : psi L + 3 <= psi M) :
  GoodOut M c S_tail.
Proof.
  destruct heven as [q_ev hq_ev].
  assert (hlt : psi L < psi M) by lia.
  destruct (step_p02_many_ih ihEL k L hlt ((2 * c) :: S_tail))
    as [[L1 [hr1 [_ hw1]]] | [a [L1 [hr1 hw1]]]].
  - exact (finish_has0 (reach_trans hr hr1) ltac:(lia)).
  - refine (finish_no0 ihEL (reach_trans hr hr1) _).
    rewrite W_rep4_append. cbn [W wf]. lia.
Qed.

Lemma finish_EL_p02_2c {M L S_tail : list nat} {k c : nat}
  (ihEL : ELIH (psi M))
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail))
              (cfg_EL1 (0 :: L) (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))))
  (heven : IsEven (psi M))
  (hp : psi L + 4 <= psi M) :
  GoodOut M c S_tail.
Proof.
  assert (hlt : psi L < psi M) by lia.
  destruct (ihEL L hlt (2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
    as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
  - assert (hlt1 : psi L1 < psi M) by (pose proof (psi_le L1); lia).
    assert (h2 : Reach (cfg_BR1 (0 :: L1) (2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
                       (cfg_EL1 (0 :: L1) (0 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))).
    { rstep (step_BR1_ge2 0 (0 :: L1) (rep02 (k + 1) ++ ((2 * c) :: S_tail))).
      rdone (step_EL1_add_two 0 L1 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))). }
    destruct (ihEL L1 hlt1 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
      as [[L2 [hr2 hw2]] | [L2 [hr2 hw2]]].
    + refine (finish_0_p02_2c ihEL (reach_trans (reach_trans hr hr1) (reach_trans h2 hr2)) heven _).
      pose proof (psi_le L2); pose proof (psi_le L1); lia.
    + pose proof (reach_trans (reach_trans (reach_trans hr hr1) (reach_trans h2 hr2))
        (reach_trans (step_BR1_00 L2 (rep02 (k + 1) ++ ((2 * c) :: S_tail)))
                     (sweep_BR_p02 (k + 1) (2 :: L2) ((2 * c) :: S_tail)))) as hsw.
      refine (finish_no0 ihEL hsw _).
      rewrite W_rep4_append; cbn [W wf]; pose proof (psi_le L1); lia.
  - pose proof (reach_trans (reach_trans hr hr1)
      (reach_trans (sweep_BR_p02_one L1 (rep02 (k + 1) ++ ((2 * c) :: S_tail)))
                   (sweep_BR_p02 (k + 1) (4 :: L1) ((2 * c) :: S_tail)))) as hsw.
    refine (finish_no0 ihEL hsw _).
    rewrite W_rep4_append; cbn [W wf]; lia.
Qed.

Lemma finish_BR_22_p02_2c {M L S_tail : list nat} {k c : nat}
  (ihEL : ELIH (psi M))
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail))
              (cfg_BR1 (0 :: L) (2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))))
  (heven : IsEven (psi M))
  (hp : psi L + 4 <= psi M) :
  GoodOut M c S_tail.
Proof.
  assert (hlt : psi L < psi M) by lia.
  assert (h1 : Reach (cfg_BR1 (0 :: L) (2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
                     (cfg_EL1 (0 :: L) (0 :: 0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))).
  { rstep (step_BR1_ge2 0 (0 :: L) (2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))).
    rdone (step_EL1_add_two 0 L (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))). }
  destruct (ihEL L hlt (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
    as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
  - pose proof (reach_trans (reach_trans (reach_trans hr h1) hr1)
      (reach_trans (sweep_BR_p02_one L1 (rep02 (k + 1) ++ ((2 * c) :: S_tail)))
                   (sweep_BR_p02 (k + 1) (4 :: L1) ((2 * c) :: S_tail)))) as hsw.
    refine (finish_no0 ihEL hsw _).
    rewrite W_rep4_append; cbn [W wf]; lia.
  - assert (h2 : Reach (cfg_BR1 (0 :: L1) (0 :: 0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
                       (cfg_EL1 (0 :: 2 :: L1) (0 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))).
    { rstep (step_BR1_00 L1 (2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))).
      rstep (step_BR1_ge2 0 (0 :: 2 :: L1) (rep02 (k + 1) ++ ((2 * c) :: S_tail))).
      rdone (step_EL1_add_two 0 (2 :: L1) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))). }
    assert (hp2 : psi (2 :: L1) < psi M) by (rewrite psi_cons_two; lia).
    destruct (ihEL (2 :: L1) hp2 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
      as [[L2 [hr2 hw2]] | [L2 [hr2 hw2]]].
    + rewrite psi_cons_two in hw2.
      refine (finish_0_p02_2c ihEL
        (reach_trans (reach_trans (reach_trans hr h1) hr1) (reach_trans h2 hr2)) heven _).
      pose proof (psi_le L2); lia.
    + rewrite psi_cons_two in hw2.
      pose proof (reach_trans
        (reach_trans (reach_trans (reach_trans hr h1) hr1) (reach_trans h2 hr2))
        (reach_trans (step_BR1_00 L2 (rep02 (k + 1) ++ ((2 * c) :: S_tail)))
                     (sweep_BR_p02 (k + 1) (2 :: L2) ((2 * c) :: S_tail)))) as hsw.
      refine (finish_no0 ihEL hsw _).
      rewrite W_rep4_append; cbn [W wf]; lia.
Qed.

Lemma finish_0_p02_opt {M L S_tail : list nat} {k c : nat}
  (ihEL : ELIH (psi M))
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail))
              (cfg_BR1 (0 :: L) (0 :: (rep02 k ++ ((2 * c) :: S_tail)))))
  (heven : IsEven (psi M))
  (hL : 2 * W L + 2 <= psi M)
  (hL_psi : psi L + 3 <= psi M) :
  GoodOut M c S_tail.
Proof.
  destruct k as [| k'].
  - cbn [rep02 app] in hr. exact (finish_has0 hr hL).
  - replace (S k') with (k' + 1) in hr by lia.
    exact (finish_0_p02_2c ihEL hr heven hL_psi).
Qed.

(* The 20 front is a complete call, regardless of how we reached it.
   Its two exits differ by one remaining zero in front of the pairs. *)
Lemma finish_BR20 {M L S_tail : list nat} {k c : nat}
  (ihEL : ELIH (psi M))
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail))
    (cfg_BR1 (0 :: L) (2 :: 0 :: (rep02 k ++ ((2 * c) :: S_tail)))))
  (heven : IsEven (psi M))
  (hp : psi L + 3 <= psi M) :
  GoodOut M c S_tail.
Proof.
  destruct (step_even_ih ihEL 0 L ltac:(lia) (0 :: (rep02 k ++ ((2 * c) :: S_tail))))
    as [[U [hu hw]] | [U [hu [h0 _]]]].
  - refine (finish_no0 ihEL (reach_trans hr (reach_trans hu _)) _).
    + rstep (step_BR1_00 U (rep02 k ++ ((2 * c) :: S_tail))).
      rdone (sweep_BR_p02 k (2 :: U) ((2 * c) :: S_tail)).
    + rewrite W_rep4_append. cbn [W wf]. lia.
  - destruct (h0 eq_refl) as [hpU [hwU _]].
    exact (finish_0_p02_opt ihEL (reach_trans hr hu) heven ltac:(lia) ltac:(lia)).
Qed.

Lemma finish_42_0_p02_2c {M T S_tail : list nat} {k c : nat}
  (ihEL : ELIH (psi M))
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail))
              (cfg_BR1 (0 :: 4 :: 2 :: T) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))))
  (heven : IsEven (psi M))
  (hT : 2 * W T + 4 <= psi M) :
  GoodOut M c S_tail.
Proof.
  rewrite rep02_succ_r in hr; cbn [app] in hr.
  pose proof (reach_trans hr (br_42_002_step T (rep02 k ++ ((2 * c) :: S_tail)))) as h1.
  set (R := rep02 k ++ ((2 * c) :: S_tail)) in *.
  assert (hltT : psi T < psi M) by (pose proof (psi_le T); lia).
  destruct (ihEL T hltT (2 :: 0 :: 2 :: 2 :: 0 :: R)) as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
  - assert (hlt1 : psi L1 < psi M) by (pose proof (psi_le L1); pose proof (psi_le T); lia).
    assert (hs1 : Reach (cfg_BR1 (0 :: L1) (2 :: 0 :: 2 :: 2 :: 0 :: R))
                        (cfg_EL1 (0 :: L1) (0 :: 0 :: 0 :: 2 :: 2 :: 0 :: R))).
    { rstep (step_BR1_ge2 0 (0 :: L1) (0 :: 2 :: 2 :: 0 :: R)).
      rdone (step_EL1_add_two 0 L1 (0 :: 0 :: 2 :: 2 :: 0 :: R)). }
    pose proof (reach_trans (reach_trans h1 hr1) hs1) as pre.
    destruct (ihEL L1 hlt1 (0 :: 0 :: 2 :: 2 :: 0 :: R)) as [[L2 [hr2 hw2]] | [L2 [hr2 hw2]]].
    + assert (hlt2 : psi L2 < psi M)
        by (pose proof (psi_le L2); pose proof (psi_le L1); pose proof (psi_le T); lia).
      destruct (step_p02_one_ih ihEL L2 hlt2 (2 :: 0 :: R))
        as [[L3 [hr3 [hp3 hw3]]] | [L3 [hr3 hw3]]].
      * refine (finish_0_p02_opt ihEL
          (reach_trans (reach_trans pre hr2) (reach_trans hr3 (sweep_BR_p02_one L3 (0 :: R))))
          heven _ _).
        -- cbn [W wf]; pose proof (psi_le L2); pose proof (psi_le L1); pose proof (psi_le T); lia.
        -- rewrite psi_cons_four; pose proof (psi_le L2); pose proof (psi_le L1); pose proof (psi_le T); lia.
      * refine (finish_BR20 ihEL (reach_trans (reach_trans pre hr2) hr3) heven _).
        rewrite psi_cons_two; pose proof (psi_le L2); pose proof (psi_le L1); pose proof (psi_le T); lia.
    + refine (finish_BR20 ihEL (reach_trans (reach_trans pre hr2) _) heven _).
      * rstep (step_BR1_00 L2 (0 :: 2 :: 2 :: 0 :: R)).
        exact (sweep_BR_p02_one (2 :: L2) (2 :: 0 :: R)).
      * rewrite psi_cons_four. cbn [W wf]. pose proof (psi_le L1); pose proof (psi_le T); lia.
  - refine (finish_BR20 ihEL (reach_trans (reach_trans h1 hr1) _) heven _).
    + rstep (sweep_BR_p02_one L1 (0 :: 2 :: 2 :: 0 :: R)).
      exact (sweep_BR_p02_one (4 :: L1) (2 :: 0 :: R)).
    + rewrite psi_cons_four. cbn [W wf]. pose proof (psi_le T); lia.
Qed.

Lemma finish_EL_p02_0_p02_2c {M L S_tail : list nat} {k c : nat}
  (ihEL : ELIH (psi M))
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail))
              (cfg_EL1 (0 :: L) (0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))))
  (heven : IsEven (psi M))
  (hL : 2 * W L + 4 <= psi M) :
  GoodOut M c S_tail.
Proof.
  assert (hlt : psi L < psi M) by (pose proof (psi_le L); lia).
  destruct (ihEL L hlt (0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
    as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
  - pose proof (reach_trans (reach_trans hr hr1)
      (sweep_BR_p02_one L1 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))) as hsw.
    refine (finish_0_p02_2c ihEL hsw heven _).
    rewrite psi_cons_four; cbn [W wf]; pose proof (psi_le L); lia.
  - assert (hlt1 : psi L1 < psi M) by (pose proof (psi_le L1); pose proof (psi_le L); lia).
    destruct (step_p02_one_ih ihEL L1 hlt1 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
      as [[L2 [hr2 [_ hw2]]] | [L2 [hr2 hw2]]].
    + pose proof (reach_trans (reach_trans (reach_trans hr hr1) hr2)
        (reach_trans (step_BR1_00 L2 (rep02 (k + 1) ++ ((2 * c) :: S_tail)))
                     (sweep_BR_p02 (k + 1) (2 :: L2) ((2 * c) :: S_tail)))) as hsw.
      refine (finish_no0 ihEL hsw _).
      rewrite W_rep4_append; cbn [W wf]; pose proof (psi_le L1); pose proof (psi_le L); lia.
    + refine (finish_0_p02_2c ihEL (reach_trans (reach_trans hr hr1) hr2) heven _).
      rewrite psi_cons_two; pose proof (psi_le L1); pose proof (psi_le L); lia.
Qed.

Lemma finish_2D {M Y S_tail : list nat} {k c : nat}
  (ihEL : ELIH (psi M))
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail))
              (cfg_EL1 (0 :: Y) (0 :: 2 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))))
  (heven : IsEven (psi M))
  (hY : 2 * W Y + 4 <= psi M) :
  GoodOut M c S_tail.
Proof.
  assert (hltY : psi Y < psi M) by (pose proof (psi_le Y); lia).
  destruct (ihEL Y hltY (2 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
    as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
  - assert (hlt1 : psi L1 < psi M) by (pose proof (psi_le L1); pose proof (psi_le Y); lia).
    assert (hs1 : Reach (cfg_BR1 (0 :: L1) (2 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
                        (cfg_EL1 (0 :: L1) (0 :: 0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))).
    { rstep (step_BR1_ge2 0 (0 :: L1) (0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))).
      rdone (step_EL1_add_two 0 L1 (0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))). }
    destruct (ihEL L1 hlt1 (0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
      as [[L2 [hr2 hw2]] | [L2 [hr2 hw2]]].
    + assert (hlt2 : psi L2 < psi M)
        by (pose proof (psi_le L2); pose proof (psi_le L1); pose proof (psi_le Y); lia).
      destruct (step_p02_one_ih ihEL L2 hlt2 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
        as [[L3 [hr3 [_ hw3]]] | [L3 [hr3 hw3]]].
      * pose proof (reach_trans
          (reach_trans (reach_trans (reach_trans hr hr1) (reach_trans hs1 hr2)) hr3)
          (reach_trans (step_BR1_00 L3 (rep02 (k + 1) ++ ((2 * c) :: S_tail)))
                       (sweep_BR_p02 (k + 1) (2 :: L3) ((2 * c) :: S_tail)))) as hsw.
        refine (finish_no0 ihEL hsw _).
        rewrite W_rep4_append; cbn [W wf].
        pose proof (psi_le L2); pose proof (psi_le L1); pose proof (psi_le Y); lia.
      * refine (finish_0_p02_2c ihEL
          (reach_trans (reach_trans (reach_trans hr hr1) (reach_trans hs1 hr2)) hr3) heven _).
        rewrite psi_cons_two; pose proof (psi_le L2); pose proof (psi_le L1); pose proof (psi_le Y); lia.
    + pose proof (reach_trans (reach_trans (reach_trans hr hr1) (reach_trans hs1 hr2))
        (reach_trans (step_BR1_00 L2 (0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
                     (sweep_BR_p02_one (2 :: L2) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))))) as hsw.
      refine (finish_0_p02_2c ihEL hsw heven _).
      rewrite psi_cons_four; cbn [W wf]; pose proof (psi_le L1); pose proof (psi_le Y); lia.
  - pose proof (reach_trans (reach_trans hr hr1)
      (reach_trans (sweep_BR_p02_one L1 (0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
                   (sweep_BR_p02_one (4 :: L1) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))))) as hsw.
    refine (finish_0_p02_2c ihEL hsw heven _).
    rewrite psi_cons_four; cbn [W wf]; pose proof (psi_le Y); lia.
Qed.

(* A strict decrease in potential pays for either return shape. *)
Lemma finish_even {M L c S_tail}
  (ihEL : ELIH (psi M))
  (pre : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S_tail))
               (cfg_BR1 (0 :: L) ((2 * c + 2) :: S_tail)))
  (hsmall : psi L < psi M) : GoodOut M c S_tail.
Proof.
  destruct (step_even_ih ihEL c L hsmall S_tail) as [[T [hr hw]] | [T [hr [h0 hpos]]]].
  - right. exists T. split; [exact (reach_trans pre hr) | lia].
  - left. exists T. split; [exact (reach_trans pre hr) |].
    split.
    + destruct (Nat.eq_dec c 0) as [hc | hc].
      * subst c. destruct (h0 eq_refl) as [_ [hw _]]. cbn [Nat.mul Nat.add wf]. lia.
      * assert (hc' : 1 <= c) by lia.
        pose proof (hpos hc'). pose proof (wf_even_mono hc'). lia.
    + intros hc _. destruct (h0 hc) as [hp _]. lia.
Qed.

(* Group every pair of zeros into one left 2. Any last zero consumes
   the right digit; otherwise the same even-digit call continues. *)
Lemma finish_zero_run {M L c R n}
  (ihEL : ELIH (psi M))
  (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: R))
       (cfg_BR1 (0 :: L) (repeat 0 n ++ ((2 * c + 2) :: R))))
  (hn : 2 <= n)
  (hw : 2 * (Nat.div2 n + W L) <= psi M)
  (hne : forall T, M <> 5 :: T) :
  GoodOut M c R.
Proof.
  pose proof (Nat.div2_odd n) as Hn.
  set (k := Nat.div2 n) in Hn, hw.
  destruct (Nat.odd n); cbn [Nat.b2n] in Hn.
  - rewrite Hn, <- repeat_zero_snoc in hr.
    left. exists ((2 * c + 4) :: (repeat 2 k ++ L)). split.
    + rstep hr.
      rstep (sweep_BR_00 k L (0 :: (2 * c + 2) :: R)).
      rdone (step_BR1_0d (2 * c + 2) (repeat 2 k ++ L) R).
    + split.
      * cbn [W]. rewrite W_repeat_two. lia.
      * intros _ [T H]. exact (False_rect _ (hne T H)).
  - replace n with (2 * k) in hr by lia.
    destruct k as [| k]; [lia|].
    eapply finish_even; [exact ihEL| |].
    + exact (reach_trans hr (sweep_BR_00 (S k) L ((2 * c + 2) :: R))).
    + replace (S k) with (k + 1) by lia. rewrite psi_repeat_two_succ. lia.
Qed.

Lemma bump_large_even (n c : nat) (L R : list nat)
  (hn : 2 <= n) (ihEL : ELIH (psi ((2 * n + 2) :: L))) :
  GoodOut ((2 * n + 2) :: L) c R.
Proof.
  assert (hp : psi ((2 * n + 2) :: L) = 2 * (wf (2 * n + 2) + W L))
    by (rewrite psi_cons_ne2; [reflexivity|lia]).
  assert (hc : n + 1 <= 2 * wf (2 * n + 2)).
  { destruct (Nat.eq_dec n 2) as [->|?]; [exact (Nat.le_succ_diag_r 3)|].
    rewrite wf_ge7 by lia. pose proof (div4_spec (2 * n + 2)); lia. }
  assert (hsmall : psi L < psi ((2 * n + 2) :: L))
    by (pose proof (psi_le L); lia).
  set (T := (2 * c + 2) :: R).
  assert (eT : inc1 ((2 * c + 1) :: R) = T)
    by (unfold T; cbn [inc1]; f_equal; lia).
  assert (pre : Reach (cfg_CL1 (inc1 ((2 * n + 2) :: L)) ((2 * c + 1) :: R))
         (cfg_EL1 (0 :: L) (0 :: (repeat 0 n ++ T)))).
  { cbn [inc1].
    rstep (step_CL1_add_three (2 * n) L ((2 * c + 1) :: R)).
    rewrite eT.
    pose proof (peel_EL1_even n 0 L (0 :: T)) as H.
    rewrite repeat_zero_snoc in H.
    replace (n + 1) with (S n) in H by lia. exact H. }
  destruct (ihEL L hsmall (repeat 0 n ++ T)) as [[U [H hU]] | [U [H hU]]].
  - eapply (finish_zero_run ihEL (reach_trans pre H)); try assumption.
    + pose proof (Nat.div2_odd n). pose proof (psi_le L). lia.
    + intros X HX. injection HX as HX. lia.
  - change (Reach (cfg_EL1 (0 :: L) (0 :: (repeat 0 n ++ T)))
             (cfg_BR1 (0 :: U) (repeat 0 (S n) ++ T))) in H.
    eapply (finish_zero_run ihEL (reach_trans pre H)).
    + lia.
    + pose proof (Nat.div2_odd (S n)). pose proof (psi_le L). lia.
    + intros X HX. injection HX as HX. lia.
Qed.

Lemma bump_large_odd (n c : nat) (L R : list nat)
  (hn : 2 <= n) (ihEL : ELIH (psi ((2 * n + 3) :: L))) :
  GoodOut ((2 * n + 3) :: L) c R.
Proof.
  set (T := (2 * c + 2) :: R).
  assert (eT : inc1 ((2 * c + 1) :: R) = T)
    by (unfold T; cbn [inc1]; f_equal; lia).
  assert (pre : Reach (cfg_CL1 (inc1 ((2 * n + 3) :: L)) ((2 * c + 1) :: R))
        (cfg_BR1 (0 :: inc1 L) (repeat 0 (n + 1) ++ T))).
  { cbn [inc1].
    rstep (step_CL1_add_three (1 + 2 * n) L ((2 * c + 1) :: R)).
    rewrite eT.
    rstep (peel_EL1_even n 1 L (0 :: T)).
    rstep (step_EL1_one L (repeat 0 n ++ (0 :: T))).
    rewrite <- repeat_zero_snoc.
    rdone (step_EB1_zero L (repeat 0 n ++ (0 :: T))). }
  eapply (finish_zero_run ihEL pre).
  - lia.
  - rewrite psi_cons_ne2 by lia. rewrite wf_ge7 by lia.
    pose proof (div4_spec (2 * n + 3)) as Hd.
    pose proof (Nat.div2_odd (n + 1)) as Hn.
    destruct (Nat.odd (n + 1)); cbn [Nat.b2n] in Hn;
      pose proof (W_inc1_le L); lia.
  - intros X HX. injection HX as HX. lia.
Qed.


(* Induct first on potential, then on length for zero-cost digits. *)
Lemma psi_length_ind (P : list nat -> Prop) :
  (forall M, (forall L, psi L < psi M \/
    psi L = psi M /\ List.length L < List.length M -> P L) -> P M) ->
  forall M, P M.
Proof.
  intro Hstep.
  assert (H : forall p n M, psi M = p -> List.length M = n -> P M).
  { intro p. induction p as [p IH] using strong_induction.
    intro n. induction n as [n IHn] using strong_induction.
    intros M Hp Hn. apply Hstep. intros L [Hlt | [Heq Hlt]].
    - exact (IH (psi L) ltac:(lia) (List.length L) L eq_refl eq_refl).
    - exact (IHn (List.length L) ltac:(lia) L ltac:(lia) eq_refl). }
  intro M. exact (H _ _ M eq_refl eq_refl).
Qed.

Lemma mCL_bump_spec (M : list nat) (c : nat) (S_tail : list nat) : GoodOut M c S_tail.
Proof.
  revert M c S_tail.
  apply (psi_length_ind (fun M => forall c S_tail, GoodOut M c S_tail)).
  intros M ih c S_tail.
  assert (ihEL : ELIH (psi M)).
  { intros L hL R. exact (good_to_el (ih L (or_introl hL) 0 R)). }
  destruct M as [| v M'].
  - assert (hr : Reach (cfg_CL1 (inc1 []) ((2 * c + 1) :: S_tail))
                       (cfg_BR1 [0; 2 * c + 4] S_tail)).
    { cbn [inc1].
      rstep (step_CL1_zero [] ((2 * c + 1) :: S_tail)).
      rstep (step_CL1_nil ((2 * c + 3) :: S_tail)).
      rdone (step_EL1_nil_cons (2 * c + 4) S_tail). }
    left. exists [2 * c + 4].
    split; [exact hr |].
    split; [cbn [W psi]; lia | intros _ [T hne]; discriminate hne].
  - destruct v as [| [| [| [| [| [| n0]]]]]].
    + (* v = 0 *)
      assert (hpsiM : psi (0 :: M') = 2 * (2 + W M')) by reflexivity.
      assert (hlt : psi M' < psi (0 :: M')) by (pose proof (psi_le M'); lia).
      assert (h1 : Reach (cfg_CL1 (inc1 (0 :: M')) ((2 * c + 1) :: S_tail))
                         (cfg_CL1 (inc1 M') ((2 * (c + 1) + 1) :: S_tail))).
      { cbn [inc1]. rdone (step_CL1_one M' ((2 * c + 1) :: S_tail)). }
      destruct (ih M' (or_introl hlt) (c + 1) S_tail)
        as [[L' [hr [hw _]]] | [L' [hr hw]]].
      * left. exists L'.
        split; [exact (reach_trans h1 hr) |].
        split; [pose proof (wf_even_step c); pose proof (psi_le M'); lia |
                intros _ [T hne]; discriminate hne].
      * right. exists L'.
        split; [exact (reach_trans h1 hr) | pose proof (psi_le M'); lia].
    + (* v = 1 *)
      assert (hpsiM : psi (1 :: M') = 2 * (3 + W M')) by reflexivity.
      assert (h1 : Reach (cfg_CL1 (inc1 (1 :: M')) ((2 * c + 1) :: S_tail))
                         (cfg_BR1 (0 :: inc1 M') ((2 * c + 2) :: S_tail))).
      { cbn [inc1].
        rstep (step_CL1_two M' ((2 * c + 1) :: S_tail)).
        rdone (step_EB1_zero M' ((2 * c + 2) :: S_tail)). }
      assert (hlt : psi (inc1 M') < psi (1 :: M'))
        by (pose proof (psi_le (inc1 M')); pose proof (W_inc1_le M'); lia).
      exact (finish_even ihEL h1 hlt).
    + (* v = 2 *)
      assert (hpsiM : psi (2 :: M') = 2 * W M' + 1) by reflexivity.
      assert (hlt : psi M' < psi (2 :: M')) by (pose proof (psi_le M'); lia).
      assert (h1 : Reach (cfg_CL1 (inc1 (2 :: M')) ((2 * c + 1) :: S_tail))
                         (cfg_EL1 (0 :: M') (0 :: (2 * c + 2) :: S_tail))).
      { cbn [inc1]. rdone (step_CL1_add_three 0 M' ((2 * c + 1) :: S_tail)). }
      destruct (ihEL M' hlt ((2 * c + 2) :: S_tail)) as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
      * assert (hlt1 : psi L1 < psi (2 :: M'))
          by (pose proof (psi_le L1); pose proof (psi_le M'); lia).
        exact (finish_even ihEL (reach_trans h1 hr1) hlt1).
      * left. exists ((2 * c + 4) :: L1).
        split; [rdone (reach_trans (reach_trans h1 hr1) (step_BR1_0d (2 * c + 2) L1 S_tail)) |].
        split; [cbn [W]; pose proof (psi_le M'); lia | intros _ [T hne]; discriminate hne].
    + (* v = 3 *)
      assert (hpsiM : psi (3 :: M') = 2 * (2 + W M')) by reflexivity.
      assert (h1 : Reach (cfg_CL1 (inc1 (3 :: M')) ((2 * c + 1) :: S_tail))
                         (cfg_BR1 (0 :: (2 * c + 4) :: inc1 M') S_tail)).
      { cbn [inc1].
        rstep (step_CL1_add_three 1 M' ((2 * c + 1) :: S_tail)).
        rstep (step_EL1_one M' (0 :: (2 * c + 2) :: S_tail)).
        rstep (step_EB1_zero M' (0 :: (2 * c + 2) :: S_tail)).
        rdone (step_BR1_0d (2 * c + 2) (inc1 M') S_tail). }
      left. exists ((2 * c + 4) :: inc1 M').
      split; [exact h1 |].
      split; [cbn [W]; pose proof (W_inc1_le M'); lia | intros _ [T hne]; discriminate hne].
    + (* v = 4 *)
      assert (hpsiM : psi (4 :: M') = 2 * W M') by (cbn [psi Nat.eqb W wf]; lia).
      assert (h1 : Reach (cfg_CL1 (inc1 (4 :: M')) ((2 * c + 1) :: S_tail))
                         (cfg_EL1 (0 :: M') (0 :: 0 :: (2 * c + 2) :: S_tail))).
      { cbn [inc1].
        rstep (step_CL1_add_three 2 M' ((2 * c + 1) :: S_tail)).
        rdone (step_EL1_add_two 0 M' (0 :: (2 * c + 2) :: S_tail)). }
      assert (hsmall : psi M' < psi (4 :: M') \/
          psi M' = psi (4 :: M') /\ List.length M' < List.length (4 :: M')).
      { pose proof (psi_le M'). cbn [List.length]. lia. }
      pose proof (good_to_el (ih M' hsmall 0 (0 :: (2 * c + 2) :: S_tail))) as hM'.
      destruct hM' as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
      * left. exists ((2 * c + 4) :: L1).
        split; [rdone (reach_trans (reach_trans h1 hr1) (step_BR1_0d (2 * c + 2) L1 S_tail)) |].
        split; [cbn [W]; pose proof (psi_le M'); lia | intros _ [T hne]; discriminate hne].
      * assert (hlt2 : psi (2 :: L1) < psi (4 :: M'))
          by (rewrite psi_cons_two; pose proof (psi_le M'); lia).
        pose proof (reach_trans (reach_trans h1 hr1) (step_BR1_00 L1 ((2 * c + 2) :: S_tail))) as h2.
        exact (finish_even ihEL h2 hlt2).
    + (* v = 5 *)
      assert (hpsiM : psi (5 :: M') = 2 * (2 + W M')) by reflexivity.
      assert (heven : IsEven (psi (5 :: M'))) by (exists (2 + W M'); exact hpsiM).
      destruct M' as [| hd tl].
      * left. exists [2 * c + 2; 2; 4; 4; 4].
        split; [cbn [inc1]; exact (cl_6_nil_step c S_tail) |].
        split.
        -- destruct c as [| c'].
           ++ cbn; lia.
           ++ pose proof (@wf_even_mono (S c') ltac:(lia)).
              cbn [W psi Nat.eqb wf]; lia.
        -- intros -> _. cbn; lia.
      * destruct (Nat.eq_dec hd 4) as [hhd | hne4].
        -- (* hd = 4 *)
           subst hd.
           destruct (strip4_spec tl) as [hstr hne].
           set (k := fst (strip4 tl)) in *.
           set (R_tail := snd (strip4 tl)) in *.
           assert (hlist : 4 :: tl = rep4 (k + 1) ++ R_tail).
           { rewrite rep4_succ_r; cbn [app]; f_equal; exact hstr. }
           assert (hw_eq : W (4 :: tl) = W R_tail) by (rewrite hlist, W_rep4_append; reflexivity).
           assert (hpsi_eq : psi (5 :: 4 :: tl) = 2 * (2 + W R_tail))
             by (rewrite hpsiM, hw_eq; reflexivity).
           assert (hpre : Reach (cfg_CL1 (inc1 (5 :: 4 :: tl)) ((2 * c + 1) :: S_tail))
                                (cfg_EL1 (0 :: inc1 R_tail)
                                  (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))).
           { cbn [inc1]. rewrite hlist.
             pose proof (cl_6_rep4_step k c R_tail S_tail) as hcl.
             replace (k + 2) with (S (k + 1)) in hcl by lia.
             cbn [rep02 app] in hcl. exact hcl. }
           destruct R_tail as [| x M''] eqn:hRt.
           ++ (* R_tail = [] *)
              assert (h0 : Reach (cfg_EL1 [0; 0] (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))
                                 (cfg_BR1 [0; 6] (2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail))))).
              { rstep (step_EL1_zero [0] (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))).
                rstep (step_CL1_one [] (1 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))).
                rstep (step_CL1_zero [] (3 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))).
                rstep (step_CL1_nil (5 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))).
                rdone (step_EL1_nil_cons 6 (2 :: (rep02 (k + 1) ++ ((2 * c) :: S_tail)))). }
              change (inc1 []) with [0] in hpre.
              pose proof (reach_trans hpre h0) as hstart.
              rewrite rep02_succ_r in hstart; cbn [app] in hstart.
              pose proof (reach_trans hstart (br_6_202_step (rep02 k ++ ((2 * c) :: S_tail)))) as h1.
              destruct k as [| k'].
              ** cbn [rep02 app] in h1.
                 refine (finish_has0 h1 _).
                 cbn [W wf rep4] in hpsi_eq |- *; lia.
              ** cbn [rep02 app] in h1.
                 pose proof (reach_trans (reach_trans h1 (br_rep4_6_002_step (rep02 k' ++ ((2 * c) :: S_tail))))
                   (sweep_BR_p02 k' (2 :: rep4 8) ((2 * c) :: S_tail))) as h2.
                 refine (finish_no0 ihEL h2 _).
                 rewrite W_rep4_append; cbn [W wf rep4] in hpsi_eq |- *; lia.
          ++ (* R_tail = x :: M'' *)
              set (R := (rep02 (k + 1) ++ ((2 * c) :: S_tail))) in hpre.
              assert (hxne4 : x <> 4) by (exact (hne x M'' eq_refl)).
              assert (hpsi_x : psi (5 :: 4 :: tl) = 2 * (2 + (wf x + W M'')))
                by (cbn [W] in hpsi_eq; exact hpsi_eq).
              destruct (wf_inc_class x) as [-> | [hle | [-> | [-> | [-> | [m ->]]]]]].
              ** exfalso; exact (hxne4 eq_refl).
              ** (* Case 2A *)
                 refine (finish_EL_p02_2c ihEL hpre heven _).
                 pose proof (psi_le ((x + 1) :: M'')); cbn [inc1 W] in *; lia.
              ** (* Case 2B: x = 0 *)
                 assert (h1 : Reach (cfg_EL1 (0 :: inc1 (0 :: M'')) (0 :: 2 :: R))
                                    (cfg_BR1 (0 :: inc1 M'') (2 :: 2 :: R))).
                 { cbn [inc1].
                   rstep (step_EL1_zero (1 :: M'') (0 :: 2 :: R)).
                   rstep (step_CL1_two M'' (1 :: 2 :: R)).
                   rdone (step_EB1_zero M'' (2 :: 2 :: R)). }
                 refine (finish_BR_22_p02_2c ihEL (reach_trans hpre h1) heven _).
                 pose proof (W_inc1_le M''); pose proof (psi_le (inc1 M'')); cbn [wf] in hpsi_x; lia.
              ** (* Case 2E: x = 2 *)
                 assert (h1 : Reach (cfg_EL1 (0 :: inc1 (2 :: M'')) (0 :: 2 :: R))
                                    (cfg_EL1 (0 :: inc1 M'') (0 :: 0 :: 2 :: 0 :: R))).
                 { cbn [inc1].
                   rstep (step_EL1_zero (3 :: M'') (0 :: 2 :: R)).
                   rstep (step_CL1_add_three 1 M'' (1 :: 2 :: R)).
                   rstep (step_EL1_one M'' (0 :: 2 :: 2 :: R)).
                   rstep (step_EB1_zero M'' (0 :: 2 :: 2 :: R)).
                   rstep (sweep_BR_p02_one (inc1 M'') (2 :: R)).
                   rstep (step_BR1_ge2 0 (0 :: 4 :: inc1 M'') R).
                   rstep (step_EL1_add_two 0 (4 :: inc1 M'') (0 :: R)).
                   rdone (sweep_EL_f4_one (inc1 M'') (0 :: R)). }
                 pose proof (reach_trans hpre h1) as h2.
                 cbn [wf] in hpsi_x.
                 destruct M'' as [| y M'''].
                 --- (* M'' = [] *)
                     assert (hc1 : Reach (cfg_EL1 [0; 0] (0 :: 0 :: 2 :: 0 :: R))
                                         (cfg_BR1 [0; 4; 6] (0 :: R))).
                     { set (R0 := 0 :: 2 :: 0 :: R).
                       rstep (step_EL1_zero [0] (0 :: R0)).
                       rstep (step_CL1_one [] (1 :: R0)).
                       rstep (step_CL1_zero [] (3 :: R0)).
                       rstep (step_CL1_nil (5 :: R0)).
                       rstep (step_EL1_nil_cons 6 R0).
                       unfold R0; rdone (sweep_BR_p02_one [6] (0 :: R)). }
                     assert (hc2 : Reach (cfg_BR1 [0; 4; 6] (0 :: R))
                                         (cfg_BR1 (0 :: (rep4 k ++ 2 :: 2 :: rep4 7)) ((2 * c) :: S_tail))).
                     { unfold R. rewrite rep02_succ_r; cbn [app].
                       exact (reach_trans (br_46_002_step (rep02 k ++ ((2 * c) :: S_tail)))
                                          (sweep_BR_p02 k (2 :: 2 :: rep4 7) ((2 * c) :: S_tail))). }
                     change (inc1 []) with [0] in h2.
                     refine (finish_no0 ihEL (reach_trans (reach_trans h2 hc1) hc2) _).
                     rewrite W_rep4_append; cbn [W wf rep4] in hpsi_x |- *; lia.
                 --- (* M'' = y :: M''' *)
                     destruct (Nat.eq_dec y 4) as [hy4 | hyne4].
                     +++ (* y = 4 *)
                         subst y.
                         assert (hpsi5 : psi (5 :: M''') = 2 * (2 + W M''')) by reflexivity.
                         assert (hlt5 : psi (5 :: M''') < psi (5 :: 4 :: tl)) by (cbn [W wf] in hpsi_x; lia).
                         destruct (ih (5 :: M''') (or_introl hlt5) 0 (0 :: 2 :: 0 :: R))
                           as [[L1 [hr1 [hw1 hstr5]]] | [L1 [hr1 hw1]]].
                         *** change (inc1 (4 :: M''')) with (5 :: M''') in h2.
                             pose proof (reach_trans h2
                               (reach_trans (step_EL1_zero (5 :: M''') (0 :: 0 :: 2 :: 0 :: R)) hr1)) as hreach1.
                             assert (hpsL1 : psi L1 + 1 <= psi (5 :: M''')).
                             { apply hstr5; [reflexivity | exists M'''; reflexivity]. }
                             destruct L1 as [| z Z].
                             ---- pose proof (reach_trans hreach1
                                    (sweep_BR_p02_one [] (0 :: R))) as hsw.
                                  refine (finish_0_p02_2c ihEL hsw heven _).
                                  cbn [psi Nat.eqb W wf] in hpsi_x |- *; lia.
                             ---- destruct (Nat.eq_dec z 2) as [-> | hzne2].
                                  ++++ rewrite psi_cons_two in hpsL1.
                                       pose proof (reach_trans hreach1
                                         (sweep_BR_p02_one (2 :: Z) (0 :: R))) as hsw.
                                       refine (finish_42_0_p02_2c ihEL hsw heven _).
                                       cbn [W wf] in hpsi_x; lia.
                                  ++++ rewrite (psi_cons_ne2 hzne2) in hpsL1.
                                       pose proof (reach_trans hreach1
                                         (sweep_BR_p02_one (z :: Z) (0 :: R))) as hsw.
                                       refine (finish_0_p02_2c ihEL hsw heven _).
                                       rewrite psi_cons_four; cbn [W wf] in hpsi_x |- *; lia.
                         *** change (inc1 (4 :: M''')) with (5 :: M''') in h2.
                             pose proof (reach_trans h2
                               (reach_trans (step_EL1_zero (5 :: M''') (0 :: 0 :: 2 :: 0 :: R)) hr1)) as hreach1.
                             cbn [W wf] in hpsi_x.
                             assert (hlt1 : psi L1 < psi (5 :: 4 :: tl))
                               by (pose proof (psi_le L1); lia).
                             destruct (step_p02_one_ih ihEL L1 hlt1 (0 :: R))
                               as [[L2 [hr2 [_ hw2]]] | [L2 [hr2 hw2]]].
                             ---- pose proof (reach_trans (reach_trans hreach1 hr2)
                                    (reach_trans (step_BR1_00 L2 R)
                                                 (sweep_BR_p02 (k + 1) (2 :: L2) ((2 * c) :: S_tail)))) as hsw.
                                  refine (finish_no0 ihEL hsw _).
                                  rewrite W_rep4_append; cbn [W wf]; pose proof (psi_le L1); lia.
                             ---- refine (finish_0_p02_2c ihEL (reach_trans hreach1 hr2) heven _).
                                  rewrite psi_cons_two; pose proof (psi_le L1); lia.
                     +++ (* y <> 4 *)
                         refine (finish_EL_p02_0_p02_2c ihEL h2 heven _).
                         cbn [inc1 W] in hpsi_x |- *; pose proof (wf_add_one_le_ne4 hyne4); lia.
              ** (* Case 2D: x = 6 *)
                 assert (h1 : Reach (cfg_EL1 (0 :: inc1 (6 :: M'')) (0 :: 2 :: R))
                                    (cfg_EL1 (0 :: inc1 M'') (0 :: 2 :: 0 :: 2 :: 0 :: R))).
                 { cbn [inc1].
                   rstep (step_EL1_zero (7 :: M'') (0 :: 2 :: R)).
                   rstep (step_CL1_add_three 5 M'' (1 :: 2 :: R)).
                   rstep (step_EL1_add_two 3 M'' (0 :: 2 :: 2 :: R)).
                   rstep (step_EL1_add_two 1 M'' (0 :: 0 :: 2 :: 2 :: R)).
                   rstep (step_EL1_one M'' (0 :: 0 :: 0 :: 2 :: 2 :: R)).
                   rstep (step_EB1_zero M'' (0 :: 0 :: 0 :: 2 :: 2 :: R)).
                   rstep (step_BR1_00 (inc1 M'') (0 :: 2 :: 2 :: R)).
                   rstep (sweep_BR_p02_one (2 :: inc1 M'') (2 :: R)).
                   rstep (step_BR1_ge2 0 (0 :: 4 :: 2 :: inc1 M'') R).
                   rstep (step_EL1_add_two 0 (4 :: 2 :: inc1 M'') (0 :: R)).
                   rstep (sweep_EL_f4_one (2 :: inc1 M'') (0 :: R)).
                   rstep (step_EL1_zero (2 :: inc1 M'') (0 :: 0 :: 2 :: 0 :: R)).
                   rdone (step_CL1_add_three 0 (inc1 M'') (1 :: 0 :: 2 :: 0 :: R)). }
                 refine (finish_2D ihEL (reach_trans hpre h1) heven _).
                 pose proof (W_inc1_le M''); cbn [wf] in hpsi_x; lia.
              ** (* Case 2C: x = 4 * (m + 1) + 3 *)
                 pose proof (wf_4r3 (m + 1)) as hwx.
                 assert (h1 : Reach (cfg_EL1 (0 :: inc1 ((4 * (m + 1) + 3) :: M''))
                                      (0 :: 2 :: R))
                                    (cfg_EL1 (0 :: M'')
                                      (0 :: (repeat 0 (2 * m + 3) ++ (2 :: 2 :: R))))).
                 { cbn [inc1].
                   rstep (step_EL1_zero ((4 * (m + 1) + 3 + 1) :: M'') (0 :: 2 :: R)).
                   rstep (step_CL1_add_three (2 * (2 * m + 3)) M'' (1 :: 2 :: R)).
                   pose proof (peel_EL1_even (2 * m + 3) 0 M'' (0 :: 2 :: 2 :: R)) as a3.
                   rewrite repeat_zero_snoc in a3.
                   replace (2 * m + 3 + 1) with (S (2 * m + 3)) in a3 by lia.
                   cbn [repeat app] in a3.
                   rdone a3. }
                 assert (hltM'' : psi M'' < psi (5 :: 4 :: tl))
                   by (pose proof (psi_le M''); rewrite hwx in hpsi_x; lia).
                 destruct (ihEL M'' hltM'' (repeat 0 (2 * m + 3) ++ (2 :: 2 :: R)))
                   as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
                 --- assert (hrep : repeat 0 (2 * m + 3) ++ (2 :: 2 :: R) =
                       repeat 0 (2 * (m + 1)) ++ (0 :: 2 :: 2 :: R)).
                     { rewrite repeat_zero_snoc. f_equal; f_equal; lia. }
                     rewrite hrep in h1, hr1.
                     pose proof (reach_trans (reach_trans (reach_trans hpre h1) hr1)
                       (reach_trans (sweep_BR_00 (m + 1) L1 (0 :: 2 :: 2 :: R))
                                    (sweep_BR_p02_one (repeat 2 (m + 1) ++ L1) (2 :: R)))) as hs.
                     pose proof (reach_trans hs
                       (reach_trans (step_BR1_ge2 0 (0 :: 4 :: (repeat 2 (m + 1) ++ L1)) R)
                                    (step_EL1_add_two 0 (4 :: (repeat 2 (m + 1) ++ L1)) (0 :: R)))) as hs2.
                     assert (hltL : psi (4 :: (repeat 2 (m + 1) ++ L1)) < psi (5 :: 4 :: tl)).
                     { rewrite psi_cons_four, W_repeat_two; cbn [W wf].
                       rewrite hwx in hpsi_x; pose proof (psi_le M''); lia. }
                     destruct (ihEL (4 :: (repeat 2 (m + 1) ++ L1)) hltL (0 :: R))
                       as [[L2 [hr2 hw2]] | [L2 [hr2 hw2]]].
                     +++ refine (finish_0_p02_2c ihEL (reach_trans hs2 hr2) heven _).
                         rewrite psi_cons_four, W_repeat_two in hw2; cbn [W wf] in hw2.
                         rewrite hwx in hpsi_x; pose proof (psi_le L2); pose proof (psi_le M''); lia.
                     +++ pose proof (reach_trans (reach_trans hs2 hr2)
                           (reach_trans (step_BR1_00 L2 R)
                                        (sweep_BR_p02 (k + 1) (2 :: L2) ((2 * c) :: S_tail)))) as hsw.
                         refine (finish_no0 ihEL hsw _).
                         rewrite W_rep4_append; cbn [W wf].
                         rewrite psi_cons_four, W_repeat_two in hw2; cbn [W wf] in hw2.
                         rewrite hwx in hpsi_x; pose proof (psi_le M''); lia.
                 --- assert (hrep : 0 :: (repeat 0 (2 * m + 3) ++ (2 :: 2 :: R)) =
                       repeat 0 (2 * (m + 2)) ++ (2 :: 2 :: R)).
                     { replace (2 * (m + 2)) with (S (2 * m + 3)) by lia. reflexivity. }
                     rewrite hrep in h1, hr1.
                     pose proof (reach_trans (reach_trans (reach_trans hpre h1) hr1)
                       (sweep_BR_00 (m + 2) L1 (2 :: 2 :: R))) as hs.
                     refine (finish_BR_22_p02_2c ihEL hs heven _).
                     replace (m + 2) with ((m + 1) + 1) by lia.
                     rewrite psi_repeat_two_succ.
                     rewrite hwx in hpsi_x; pose proof (psi_le M''); lia.
        -- (* hd <> 4 *)
           assert (h1 : Reach (cfg_CL1 (inc1 (5 :: hd :: tl)) ((2 * c + 1) :: S_tail))
                              (cfg_BR1 (0 :: 2 :: inc1 (hd :: tl)) ((2 * c + 2) :: S_tail))).
           { cbn [inc1].
             rstep (step_CL1_add_three 3 (hd :: tl) ((2 * c + 1) :: S_tail)).
             rstep (step_EL1_add_two 1 (hd :: tl) (0 :: (2 * c + 2) :: S_tail)).
             rstep (step_EL1_one (hd :: tl) (0 :: 0 :: (2 * c + 2) :: S_tail)).
             rstep (step_EB1_zero (hd :: tl) (0 :: 0 :: (2 * c + 2) :: S_tail)).
             rdone (step_BR1_00 (inc1 (hd :: tl)) ((2 * c + 2) :: S_tail)). }
           assert (hwinc : W (inc1 (hd :: tl)) <= W (hd :: tl) + 1)
             by (cbn [inc1 W]; pose proof (wf_add_one_le_ne4 hne4); lia).
           assert (hltY : psi (2 :: inc1 (hd :: tl)) < psi (5 :: hd :: tl))
             by (rewrite psi_cons_two; lia).
           exact (finish_even ihEL h1 hltY).

    + (* A large head is reduced to a zero run and a residual bit. *)
      pose proof (Nat.div2_odd n0) as Hn.
      set (k := Nat.div2 n0) in Hn.
      set (v := S (S (S (S (S (S n0)))))) in *.
      destruct (Nat.odd n0); cbn [Nat.b2n] in Hn.
      * replace v with (2 * (k + 2) + 3) in ihEL |- * by (unfold v; lia).
        apply bump_large_odd; [lia|exact ihEL].
      * replace v with (2 * (k + 2) + 2) in ihEL |- * by (unfold v; lia).
        apply bump_large_even; [lia|exact ihEL].
Qed.

Lemma mEL_spec (L S_tail : list nat) : ELResult L S_tail.
Proof. apply good_to_el, mCL_bump_spec. Qed.

Lemma step_p02_one (L S_tail : list nat) :
  (exists L', Reach (cfg_BR1 (0 :: L) (0 :: 0 :: 2 :: S_tail)) (cfg_BR1 (0 :: L') (0 :: S_tail)) /\
              psi L' + 1 <= psi L /\ 2 * W L' <= psi L) \/
  (exists L', Reach (cfg_BR1 (0 :: L) (0 :: 0 :: 2 :: S_tail)) (cfg_BR1 (0 :: 2 :: L') S_tail) /\
              2 * W L' <= psi L).
Proof.
  exact (@step_p02_one_ih (psi L + 1) (fun X _ S' => mEL_spec X S') L ltac:(lia) S_tail).
Qed.

Lemma p02_zero_drop (p : nat) :
  forall (L S_tail : list nat) (n : nat),
    psi L = p -> p + 1 <= n ->
    exists (a' : nat) (L' : list nat),
      Reach (cfg_BR1 (0 :: L) (0 :: (rep02 n ++ S_tail)))
            (cfg_BR1 (0 :: (rep4 a' ++ L')) S_tail) /\
      n + 2 * W L' <= a' + psi L + 3 /\ 2 * W L' <= psi L + 2.
Proof.
  induction p as [p ih] using strong_induction.
  intros L S_tail [| m] hp hn; [lia |].
  cbn [rep02 app].
  destruct (step_p02_one L (rep02 m ++ S_tail)) as [[L1 [hr1 [hp1 _]]] | [L1 [hr1 hw1]]].
  - destruct (ih (psi L1) ltac:(lia) L1 S_tail m eq_refl ltac:(lia))
      as [a' [L' [hr' [hadd hle]]]].
    exists a', L'.
    split; [exact (reach_trans hr1 hr') | lia].
  - exists m, (2 :: L1).
    split; [exact (reach_trans hr1 (sweep_BR_p02 m (2 :: L1) S_tail)) | cbn [W wf]; lia].
Qed.

(** * Section 3: Amortized Potential Lemmas, Hub Rules, and Stage 2 Loops *)

Lemma mEL_pot_1 (a : nat) (L S_tail : list nat) (ha : 2 * W L + 1 <= a) :
  exists (a' : nat) (L' : list nat),
    Reach (cfg_EL1 (0 :: (rep4 a ++ L)) (0 :: S_tail))
          (cfg_BR1 (0 :: (rep4 a' ++ L')) S_tail) /\
    a + 2 * W L' <= a' + 2 * W L + 1.
Proof.
  pose proof (sweep_EL_f4 a L S_tail) as h1.
  destruct (mEL_spec L (rep02 a ++ S_tail)) as [[L1 [hr1 hw1]] | [L1 [hr1 hw1]]].
  - exists a, L1.
    split; [exact (reach_trans (reach_trans h1 hr1) (sweep_BR_p02 a L1 S_tail)) |
            pose proof (psi_le L); lia].
  - pose proof (psi_le L) as hpsiL.
    pose proof (psi_le L1) as hpsi1.
    destruct (p02_zero_drop (psi L1) L1 S_tail a eq_refl ltac:(lia))
      as [a' [L' [hr' [hadd _]]]].
    exists a', L'.
    split; [exact (reach_trans (reach_trans h1 hr1) hr') | lia].
Qed.

Lemma cross_d2_1 (a : nat) (L S_tail : list nat) (ha : 2 * W L + 1 <= a) :
  exists (a' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: (rep4 a ++ L)) (2 :: S_tail))
          (cfg_BR1 (0 :: (rep4 a' ++ L')) (0 :: S_tail)) /\
    a + 2 * W L' <= a' + 2 * W L + 1.
Proof.
  assert (h0 : Reach (cfg_BR1 (0 :: (rep4 a ++ L)) (2 :: S_tail))
                     (cfg_EL1 (0 :: (rep4 a ++ L)) (0 :: 0 :: S_tail))).
  { rstep (step_BR1_ge2 0 (0 :: (rep4 a ++ L)) S_tail).
    rdone (step_EL1_add_two 0 (rep4 a ++ L) (0 :: S_tail)). }
  destruct (mEL_pot_1 a L (0 :: S_tail) ha) as [a' [L' [hr' hadd]]].
  exists a', L'. split; [exact (reach_trans h0 hr') | exact hadd].
Qed.

Lemma zero_p02_1 (m a : nat) (L S_tail : list nat) (ha : 2 * W L + 2 <= a) :
  exists (a' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: (rep4 a ++ L)) (0 :: (rep02 (m + 1) ++ S_tail)))
          (cfg_BR1 (0 :: (rep4 m ++ 2 :: (rep4 a' ++ L'))) S_tail) /\
    a + 2 * W L' <= a' + 2 * W L + 2.
Proof.
  rewrite rep02_succ_r; cbn [app].
  assert (h0 : Reach (cfg_BR1 (0 :: (rep4 a ++ L)) (0 :: 0 :: 2 :: (rep02 m ++ S_tail)))
                     (cfg_EL1 (0 :: (rep4 a ++ L)) (0 :: 2 :: 0 :: (rep02 m ++ S_tail)))).
  { rstep (step_BR1_00 (rep4 a ++ L) (2 :: (rep02 m ++ S_tail))).
    rstep (step_BR1_ge2 0 (0 :: 2 :: (rep4 a ++ L)) (rep02 m ++ S_tail)).
    rstep (step_EL1_add_two 0 (2 :: (rep4 a ++ L)) (0 :: (rep02 m ++ S_tail))).
    rstep (step_EL1_zero (2 :: (rep4 a ++ L)) (0 :: 0 :: (rep02 m ++ S_tail))).
    rdone (step_CL1_add_three 0 (rep4 a ++ L) (1 :: 0 :: (rep02 m ++ S_tail))). }
  destruct (mEL_pot_1 a L (2 :: 0 :: (rep02 m ++ S_tail)) ltac:(lia)) as [a1 [L1 [hr1 hd1]]].
  destruct (cross_d2_1 a1 L1 (0 :: (rep02 m ++ S_tail)) ltac:(lia)) as [a2 [L2 [hr2 hd2]]].
  pose proof (reach_trans (reach_trans (reach_trans h0 hr1) hr2)
    (reach_trans (step_BR1_00 (rep4 a2 ++ L2) (rep02 m ++ S_tail))
                 (sweep_BR_p02 m (2 :: (rep4 a2 ++ L2)) S_tail))) as h3.
  exists a2, L2. split; [exact h3 | lia].
Qed.

Lemma mEL_pot_2 (a0 a1 : nat) (L S_tail : list nat)
  (ha0 : 1 <= a0) (ha1 : 2 * W L + 4 <= a1) :
  exists (a1' : nat) (L' : list nat),
    Reach (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (0 :: S_tail))
          (cfg_BR1 (0 :: (rep4 (a0 - 1) ++ 2 :: (rep4 a1' ++ L'))) S_tail) /\
    a1 + 2 * W L' <= a1' + 2 * W L + 4.
Proof.
  destruct a0 as [| m]; [lia |].
  replace (S m - 1) with m by lia.
  replace (S m) with (m + 1) by lia.
  assert (h0 : Reach (cfg_EL1 (0 :: (rep4 (m + 1) ++ 2 :: (rep4 a1 ++ L))) (0 :: S_tail))
                     (cfg_EL1 (0 :: (rep4 a1 ++ L)) (0 :: 2 :: (rep02 (m + 1) ++ S_tail)))).
  { rstep (sweep_EL_f4 (m + 1) (2 :: (rep4 a1 ++ L)) S_tail).
    rstep (step_EL1_zero (2 :: (rep4 a1 ++ L)) (0 :: (rep02 (m + 1) ++ S_tail))).
    rdone (step_CL1_add_three 0 (rep4 a1 ++ L) (1 :: (rep02 (m + 1) ++ S_tail))). }
  destruct (mEL_pot_1 a1 L (2 :: (rep02 (m + 1) ++ S_tail)) ltac:(lia)) as [b1 [L1 [hr1 hd1]]].
  destruct (cross_d2_1 b1 L1 (rep02 (m + 1) ++ S_tail) ltac:(lia)) as [b2 [L2 [hr2 hd2]]].
  destruct (zero_p02_1 m b2 L2 S_tail ltac:(lia)) as [b3 [L3 [hr3 hd3]]].
  exists b3, L3.
  split; [exact (reach_trans (reach_trans (reach_trans h0 hr1) hr2) hr3) | lia].
Qed.

Lemma cross_d2_2 (a0 a1 : nat) (L S_tail : list nat)
  (ha0 : 1 <= a0) (ha1 : 2 * W L + 4 <= a1) :
  exists (a1' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (2 :: S_tail))
          (cfg_BR1 (0 :: (rep4 (a0 - 1) ++ 2 :: (rep4 a1' ++ L'))) (0 :: S_tail)) /\
    a1 + 2 * W L' <= a1' + 2 * W L + 4.
Proof.
  assert (h0 : Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (2 :: S_tail))
                     (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (0 :: 0 :: S_tail))).
  { rstep (step_BR1_ge2 0 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) S_tail).
    rdone (step_EL1_add_two 0 (rep4 a0 ++ 2 :: (rep4 a1 ++ L)) (0 :: S_tail)). }
  destruct (mEL_pot_2 a0 a1 L (0 :: S_tail) ha0 ha1) as [a1' [L' [hr' hd]]].
  exists a1', L'. split; [exact (reach_trans h0 hr') | exact hd].
Qed.

Lemma zero_p02_2 (m a0 a1 : nat) (L S_tail : list nat)
  (ha0 : 2 <= a0) (ha1 : 2 * W L + 8 <= a1) :
  exists (a1' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (0 :: (rep02 (m + 1) ++ S_tail)))
          (cfg_BR1 (0 :: (rep4 m ++ 2 :: (rep4 (a0 - 2) ++ 2 :: (rep4 a1' ++ L')))) S_tail) /\
    a1 + 2 * W L' <= a1' + 2 * W L + 8.
Proof.
  rewrite rep02_succ_r; cbn [app].
  set (X := rep4 a0 ++ 2 :: (rep4 a1 ++ L)).
  assert (h0 : Reach (cfg_BR1 (0 :: X) (0 :: 0 :: 2 :: (rep02 m ++ S_tail)))
                     (cfg_EL1 (0 :: X) (0 :: 2 :: 0 :: (rep02 m ++ S_tail)))).
  { rstep (step_BR1_00 X (2 :: (rep02 m ++ S_tail))).
    rstep (step_BR1_ge2 0 (0 :: 2 :: X) (rep02 m ++ S_tail)).
    rstep (step_EL1_add_two 0 (2 :: X) (0 :: (rep02 m ++ S_tail))).
    rstep (step_EL1_zero (2 :: X) (0 :: 0 :: (rep02 m ++ S_tail))).
    rdone (step_CL1_add_three 0 X (1 :: 0 :: (rep02 m ++ S_tail))). }
  unfold X in h0.
  destruct (mEL_pot_2 a0 a1 L (2 :: 0 :: (rep02 m ++ S_tail)) ltac:(lia) ltac:(lia))
    as [b1 [L1 [hr1 hd1]]].
  destruct (cross_d2_2 (a0 - 1) b1 L1 (0 :: (rep02 m ++ S_tail)) ltac:(lia) ltac:(lia))
    as [b2 [L2 [hr2 hd2]]].
  replace (a0 - 1 - 1) with (a0 - 2) in hr2 by lia.
  pose proof (reach_trans (reach_trans (reach_trans h0 hr1) hr2)
    (reach_trans (step_BR1_00 (rep4 (a0 - 2) ++ 2 :: (rep4 b2 ++ L2)) (rep02 m ++ S_tail))
                 (sweep_BR_p02 m (2 :: (rep4 (a0 - 2) ++ 2 :: (rep4 b2 ++ L2))) S_tail))) as h3.
  exists b2, L2. split; [exact h3 | lia].
Qed.

Lemma mEL_pot_3 (a0 a1 a2 : nat) (L S_tail : list nat)
  (ha0 : 1 <= a0) (ha1 : 4 <= a1) (ha2 : 2 * W L + 16 <= a2) :
  exists (a2' : nat) (L' : list nat),
    Reach (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) (0 :: S_tail))
          (cfg_BR1 (0 :: (rep4 (a0 - 1) ++ 2 :: (rep4 (a1 - 4) ++ 2 :: (rep4 a2' ++ L')))) S_tail) /\
    a2 + 2 * W L' <= a2' + 2 * W L + 16.
Proof.
  destruct a0 as [| m]; [lia |].
  replace (S m - 1) with m by lia.
  replace (S m) with (m + 1) by lia.
  assert (h0 : Reach (cfg_EL1 (0 :: (rep4 (m + 1) ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) (0 :: S_tail))
                     (cfg_EL1 (0 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) (0 :: 2 :: (rep02 (m + 1) ++ S_tail)))).
  { rstep (sweep_EL_f4 (m + 1) (2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) S_tail).
    rstep (step_EL1_zero (2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) (0 :: (rep02 (m + 1) ++ S_tail))).
    rdone (step_CL1_add_three 0 (rep4 a1 ++ 2 :: (rep4 a2 ++ L)) (1 :: (rep02 (m + 1) ++ S_tail))). }
  destruct (mEL_pot_2 a1 a2 L (2 :: (rep02 (m + 1) ++ S_tail)) ltac:(lia) ltac:(lia))
    as [b1 [L1 [hr1 hd1]]].
  destruct (cross_d2_2 (a1 - 1) b1 L1 (rep02 (m + 1) ++ S_tail) ltac:(lia) ltac:(lia))
    as [b2 [L2 [hr2 hd2]]].
  destruct (zero_p02_2 m (a1 - 1 - 1) b2 L2 S_tail ltac:(lia) ltac:(lia))
    as [b3 [L3 [hr3 hd3]]].
  replace (a1 - 1 - 1 - 2) with (a1 - 4) in hr3 by lia.
  exists b3, L3.
  split; [exact (reach_trans (reach_trans (reach_trans h0 hr1) hr2) hr3) | lia].
Qed.

Lemma cross_d2_3 (a0 a1 a2 : nat) (L S_tail : list nat)
  (ha0 : 1 <= a0) (ha1 : 4 <= a1) (ha2 : 2 * W L + 16 <= a2) :
  exists (a2' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) (2 :: S_tail))
          (cfg_BR1 (0 :: (rep4 (a0 - 1) ++ 2 :: (rep4 (a1 - 4) ++ 2 :: (rep4 a2' ++ L')))) (0 :: S_tail)) /\
    a2 + 2 * W L' <= a2' + 2 * W L + 16.
Proof.
  assert (h0 : Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) (2 :: S_tail))
                     (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) (0 :: 0 :: S_tail))).
  { rstep (step_BR1_ge2 0 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) S_tail).
    rdone (step_EL1_add_two 0 (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) (0 :: S_tail)). }
  destruct (mEL_pot_3 a0 a1 a2 L (0 :: S_tail) ha0 ha1 ha2) as [a2' [L' [hr' hd]]].
  exists a2', L'. split; [exact (reach_trans h0 hr') | exact hd].
Qed.

Lemma hub_0_step (a0 : nat) (L : list nat) :
  Reach (cfg_BR1 (0 :: (rep4 (a0 + 2) ++ L)) [])
        (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ L)) []).
Proof.
  replace (a0 + 2) with (S (S a0)) by lia; cbn [rep4 app].
  rstep (step_BR1_nil (0 :: 4 :: 4 :: (rep4 a0 ++ L))).
  rstep (step_CL1_zero (4 :: 4 :: (rep4 a0 ++ L)) [0]).
  rstep (step_CL1_add_three 1 (4 :: (rep4 a0 ++ L)) [2]).
  rstep (step_EL1_one (4 :: (rep4 a0 ++ L)) [0; 3]).
  rstep (step_EB1_zero (4 :: (rep4 a0 ++ L)) [0; 3]).
  rdone (step_BR1_0d 3 (5 :: (rep4 a0 ++ L)) []).
Qed.

Lemma br_d3_to_el (L : list nat) :
  Reach (cfg_BR1 (0 :: L) [3]) (cfg_EL1 (0 :: L) [0; 1]).
Proof.
  rstep (step_BR1_ge2 1 (0 :: L) []).
  rdone (step_EL1_add_two 0 L [1]).
Qed.

Lemma br_d1_to_el (L : list nat) :
  Reach (cfg_BR1 (0 :: L) [1]) (cfg_EL1 (0 :: L) [0]).
Proof.
  rstep (step_BR1_one_nil (0 :: L)).
  rdone (step_EL1_add_two 0 L []).
Qed.

Lemma hub_03_entry (L : list nat) :
  Reach (cfg_BR1 (0 :: 3 :: L) []) (cfg_EL1 (0 :: L) [0; 3]).
Proof.
  rstep (step_BR1_nil (0 :: 3 :: L)).
  rstep (step_CL1_zero (3 :: L) [0]).
  rdone (step_CL1_add_three 0 L [2]).
Qed.

Lemma hub_03_2 (a0 a1 : nat) (L : list nat)
  (ha0 : 3 <= a0) (ha1 : 2 * W L + 12 <= a1) :
  exists (a1' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: 3 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
          (cfg_BR1 (0 :: (rep4 (a0 - 3) ++ 2 :: (rep4 a1' ++ L'))) []) /\
    a1 + 2 * W L' <= a1' + 2 * W L + 12.
Proof.
  pose proof (hub_03_entry (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) as h0.
  destruct (mEL_pot_2 a0 a1 L [3] ltac:(lia) ltac:(lia)) as [b1 [L1 [hr1 hd1]]].
  destruct (mEL_pot_2 (a0 - 1) b1 L1 [1] ltac:(lia) ltac:(lia)) as [b2 [L2 [hr2 hd2]]].
  destruct (mEL_pot_2 (a0 - 1 - 1) b2 L2 [] ltac:(lia) ltac:(lia)) as [b3 [L3 [hr3 hd3]]].
  replace (a0 - 1 - 1 - 1) with (a0 - 3) in hr3 by lia.
  exists b3, L3.
  split; [| lia].
  exact (reach_trans
    (reach_trans (reach_trans (reach_trans (reach_trans h0 hr1) (br_d3_to_el _)) hr2)
                 (br_d1_to_el _))
    hr3).
Qed.

Lemma hub_03_3 (a0 a1 a2 : nat) (L : list nat)
  (ha0 : 3 <= a0) (ha1 : 12 <= a1) (ha2 : 2 * W L + 48 <= a2) :
  exists (a2' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: 3 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
          (cfg_BR1 (0 :: (rep4 (a0 - 3) ++ 2 :: (rep4 (a1 - 12) ++ 2 :: (rep4 a2' ++ L')))) []) /\
    a2 + 2 * W L' <= a2' + 2 * W L + 48.
Proof.
  pose proof (hub_03_entry (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) as h0.
  destruct (mEL_pot_3 a0 a1 a2 L [3] ltac:(lia) ltac:(lia) ltac:(lia)) as [b1 [L1 [hr1 hd1]]].
  destruct (mEL_pot_3 (a0 - 1) (a1 - 4) b1 L1 [1] ltac:(lia) ltac:(lia) ltac:(lia)) as [b2 [L2 [hr2 hd2]]].
  destruct (mEL_pot_3 (a0 - 1 - 1) (a1 - 4 - 4) b2 L2 [] ltac:(lia) ltac:(lia) ltac:(lia)) as [b3 [L3 [hr3 hd3]]].
  replace (a0 - 1 - 1 - 1) with (a0 - 3) in hr3 by lia.
  replace (a1 - 4 - 4 - 4) with (a1 - 12) in hr3 by lia.
  exists b3, L3.
  split; [| lia].
  exact (reach_trans
    (reach_trans (reach_trans (reach_trans (reach_trans h0 hr1) (br_d3_to_el _)) hr2)
                 (br_d1_to_el _))
    hr3).
Qed.

Lemma hub_03_halt (a1 : nat) (L : list nat) (ha1 : 2 * W L + 10 <= a1) :
  halts tm (cfg_BR1 (0 :: 3 :: (rep4 2 ++ 2 :: (rep4 a1 ++ L))) []).
Proof.
  pose proof (hub_03_entry (rep4 2 ++ 2 :: (rep4 a1 ++ L))) as h0.
  destruct (mEL_pot_2 2 a1 L [3] ltac:(lia) ltac:(lia)) as [b1 [L1 [hr1 hd1]]].
  destruct (mEL_pot_2 1 b1 L1 [1] ltac:(lia) ltac:(lia)) as [b2 [L2 [hr2 hd2]]].
  cbn [Nat.sub rep4 app] in hr1, hr2.
  assert (h3 : Reach (cfg_BR1 (0 :: 2 :: (rep4 b2 ++ L2)) [1])
                     (cfg_EL1 (0 :: (rep4 b2 ++ L2)) [0; 2])).
  { rstep (br_d1_to_el (2 :: (rep4 b2 ++ L2))).
    rstep (step_EL1_zero (2 :: (rep4 b2 ++ L2)) [0]).
    rdone (step_CL1_add_three 0 (rep4 b2 ++ L2) [1]). }
  destruct (mEL_pot_1 b2 L2 [2] ltac:(lia)) as [b3 [L3 [hr3 hd3]]].
  destruct (cross_d2_1 b3 L3 [] ltac:(lia)) as [b4 [L4 [hr4 _]]].
  pose proof (reach_trans
    (reach_trans (reach_trans (reach_trans (reach_trans (reach_trans (reach_trans h0 hr1)
      (br_d3_to_el _)) hr2) h3) hr3) hr4)
    (step_BR1_zero (0 :: (rep4 b4 ++ L4)) [])) as hreach.
  exact (halts_evstep tm _ _ (halts_of_EB1_nil _) hreach).
Qed.

Lemma hub_052_2 (a0 a1 : nat) (L : list nat)
  (ha0 : 4 <= a0) (ha1 : 2 * W L + 16 <= a1) :
  exists (a1' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: 5 :: 2 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
          (cfg_BR1 (0 :: 3 :: (rep4 (a0 - 4) ++ 2 :: (rep4 a1' ++ L'))) []) /\
    a1 + 2 * W L' <= a1' + 2 * W L + 16.
Proof.
  set (X := rep4 a0 ++ 2 :: (rep4 a1 ++ L)).
  assert (h0 : Reach (cfg_BR1 (0 :: 5 :: 2 :: X) []) (cfg_EL1 (0 :: X) [0; 2; 0; 3])).
  { rstep (step_BR1_nil (0 :: 5 :: 2 :: X)).
    rstep (step_CL1_zero (5 :: 2 :: X) [0]).
    rstep (step_CL1_add_three 2 (2 :: X) [2]).
    rstep (step_EL1_add_two 0 (2 :: X) [0; 3]).
    rstep (step_EL1_zero (2 :: X) [0; 0; 3]).
    rdone (step_CL1_add_three 0 X [1; 0; 3]). }
  unfold X in h0.
  destruct (mEL_pot_2 a0 a1 L [2; 0; 3] ltac:(lia) ltac:(lia)) as [b1 [L1 [hr1 hd1]]].
  destruct (cross_d2_2 (a0 - 1) b1 L1 [0; 3] ltac:(lia) ltac:(lia)) as [b2 [L2 [hr2 hd2]]].
  assert (hmid : Reach (cfg_BR1 (0 :: (rep4 (a0 - 1 - 1) ++ 2 :: (rep4 b2 ++ L2))) [0; 0; 3])
                       (cfg_EL1 (0 :: (rep4 (a0 - 1 - 1) ++ 2 :: (rep4 b2 ++ L2))) [0; 2; 1])).
  { set (Y := rep4 (a0 - 1 - 1) ++ 2 :: (rep4 b2 ++ L2)).
    rstep (step_BR1_00 Y [3]).
    rstep (br_d3_to_el (2 :: Y)).
    rstep (step_EL1_zero (2 :: Y) [0; 1]).
    rdone (step_CL1_add_three 0 Y [1; 1]). }
  destruct (mEL_pot_2 (a0 - 1 - 1) b2 L2 [2; 1] ltac:(lia) ltac:(lia)) as [b3 [L3 [hr3 hd3]]].
  destruct (cross_d2_2 (a0 - 1 - 1 - 1) b3 L3 [1] ltac:(lia) ltac:(lia)) as [b4 [L4 [hr4 hd4]]].
  replace (a0 - 1 - 1 - 1 - 1) with (a0 - 4) in hr4 by lia.
  exists b4, L4.
  split; [| lia].
  exact (reach_trans
    (reach_trans (reach_trans (reach_trans (reach_trans (reach_trans h0 hr1) hr2) hmid) hr3) hr4)
    (step_BR1_0d 1 _ [])).
Qed.

Lemma hub_055_entry (k : nat) (L : list nat) :
  Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 (k + 1) ++ 2 :: L)) [])
        (cfg_BR1 (0 :: inc1 L) (0 :: 2 :: 2 :: (rep02 (k + 1) ++ [0; 0; 3]))).
Proof.
  rstep (step_BR1_nil (0 :: 5 :: 5 :: (rep4 (k + 1) ++ 2 :: L))).
  rstep (step_CL1_zero (5 :: 5 :: (rep4 (k + 1) ++ 2 :: L)) [0]).
  rstep (step_CL1_add_three 2 (5 :: (rep4 (k + 1) ++ 2 :: L)) [2]).
  rstep (step_EL1_add_two 0 (5 :: (rep4 (k + 1) ++ 2 :: L)) [0; 3]).
  rstep (step_EL1_zero (5 :: (rep4 (k + 1) ++ 2 :: L)) [0; 0; 3]).
  pose proof (cl_6_rep4_step k 0 (2 :: L) [0; 3]) as h6.
  replace (k + 2) with (S (k + 1)) in h6 by lia; cbn [rep02 app] in h6.
  rstep h6.
  rstep (step_EL1_zero (3 :: L) (0 :: 2 :: (rep02 (k + 1) ++ [0; 0; 3]))).
  rstep (step_CL1_add_three 1 L (1 :: 2 :: (rep02 (k + 1) ++ [0; 0; 3]))).
  rstep (step_EL1_one L (0 :: 2 :: 2 :: (rep02 (k + 1) ++ [0; 0; 3]))).
  rdone (step_EB1_zero L (0 :: 2 :: 2 :: (rep02 (k + 1) ++ [0; 0; 3]))).
Qed.

Lemma scan_55_ge2 (k : nat) (L R : list nat) :
  Reach (cfg_BR1 (0 :: 5 :: (rep4 (k + 1) ++ 2 :: L)) (0 :: 2 :: 2 :: R))
        (cfg_BR1 (0 :: inc1 L) (0 :: 2 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R)))).
Proof.
  rstep (sweep_BR_p02_one (5 :: (rep4 (k + 1) ++ 2 :: L)) (2 :: R)).
  rstep (step_BR1_ge2 0 (0 :: 4 :: 5 :: (rep4 (k + 1) ++ 2 :: L)) R).
  rstep (step_EL1_add_two 0 (4 :: 5 :: (rep4 (k + 1) ++ 2 :: L)) (0 :: R)).
  rstep (sweep_EL_f4_one (5 :: (rep4 (k + 1) ++ 2 :: L)) (0 :: R)).
  rstep (step_EL1_zero (5 :: (rep4 (k + 1) ++ 2 :: L)) (0 :: 0 :: 2 :: 0 :: R)).
  pose proof (cl_6_rep4_step k 0 (2 :: L) (0 :: 2 :: 0 :: R)) as h6.
  replace (k + 2) with (S (k + 1)) in h6 by lia; cbn [rep02 app] in h6.
  rstep h6.
  rstep (step_EL1_zero (3 :: L) (0 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R)))).
  rstep (step_CL1_add_three 1 L (1 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R)))).
  rstep (step_EL1_one L (0 :: 2 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R)))).
  rdone (step_EB1_zero L (0 :: 2 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R)))).
Qed.

Lemma inc1_rep4_succ (n : nat) (L : list nat) :
  inc1 (rep4 (n + 1) ++ L) = 5 :: (rep4 n ++ L).
Proof.
  rewrite rep4_succ_r; reflexivity.
Qed.

Lemma scan_55_tail_any (k : nat) (L R : list nat) (hk : 2 * W L + 6 <= k) :
  exists (b : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: 5 :: (rep4 (k + 1) ++ L)) (0 :: 2 :: 2 :: R))
          (cfg_BR1 (0 :: (rep4 b ++ L')) (0 :: 0 :: 2 :: 0 :: R)) /\
    (k + 2) + 2 * W L' <= b + 2 * W L + 8.
Proof.
  assert (hpre : Reach (cfg_BR1 (0 :: 5 :: (rep4 (k + 1) ++ L)) (0 :: 2 :: 2 :: R))
                       (cfg_EL1 (0 :: inc1 L) (0 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R))))).
  { rstep (sweep_BR_p02_one (5 :: (rep4 (k + 1) ++ L)) (2 :: R)).
    rstep (step_BR1_ge2 0 (0 :: 4 :: 5 :: (rep4 (k + 1) ++ L)) R).
    rstep (step_EL1_add_two 0 (4 :: 5 :: (rep4 (k + 1) ++ L)) (0 :: R)).
    rstep (sweep_EL_f4_one (5 :: (rep4 (k + 1) ++ L)) (0 :: R)).
    rstep (step_EL1_zero (5 :: (rep4 (k + 1) ++ L)) (0 :: 0 :: 2 :: 0 :: R)).
    pose proof (cl_6_rep4_step k 0 L (0 :: 2 :: 0 :: R)) as h6.
    replace (k + 2) with (S (k + 1)) in h6 by lia; cbn [rep02 app] in h6.
    rdone h6. }
  set (S_tl := 0 :: 0 :: 2 :: 0 :: R) in *.
  set (X := inc1 L) in *.
  pose proof (W_inc1_le L) as hWX; fold X in hWX.
  assert (hpsiX : psi X <= 2 * W L + 4) by (pose proof (psi_le X); lia).
  destruct (mEL_spec X (2 :: (rep02 (k + 1) ++ S_tl))) as [[X1 [hr1 hw1]] | [X1 [hr1 hw1]]].
  - assert (hcross : Reach (cfg_BR1 (0 :: X1) (2 :: (rep02 (k + 1) ++ S_tl)))
                           (cfg_EL1 (0 :: X1) (0 :: 0 :: (rep02 (k + 1) ++ S_tl)))).
    { rstep (step_BR1_ge2 0 (0 :: X1) (rep02 (k + 1) ++ S_tl)).
      rdone (step_EL1_add_two 0 X1 (0 :: (rep02 (k + 1) ++ S_tl))). }
    assert (hpsi1 : psi X1 <= 2 * W L + 4) by (pose proof (psi_le X1); lia).
    destruct (mEL_spec X1 (0 :: (rep02 (k + 1) ++ S_tl))) as [[X2 [hr2 hw2]] | [X2 [hr2 hw2]]].
    + assert (hpsi2 : psi X2 <= 2 * W L + 4) by (pose proof (psi_le X2); lia).
      destruct (p02_zero_drop (psi X2) X2 S_tl (k + 1) eq_refl ltac:(lia))
        as [b [L' [hr' [hadd _]]]].
      exists b, L'.
      split; [exact (reach_trans (reach_trans (reach_trans (reach_trans hpre hr1) hcross) hr2) hr') | lia].
    + pose proof (reach_trans
        (reach_trans (reach_trans (reach_trans (reach_trans hpre hr1) hcross) hr2)
                     (step_BR1_00 X2 (rep02 (k + 1) ++ S_tl)))
        (sweep_BR_p02 (k + 1) (2 :: X2) S_tl)) as hsw.
      exists (k + 1), (2 :: X2).
      split; [exact hsw | cbn [W wf]; lia].
  - assert (hsw : Reach (cfg_BR1 (0 :: X1) (0 :: 2 :: (rep02 (k + 1) ++ S_tl)))
                        (cfg_BR1 (0 :: (rep4 (k + 2) ++ X1)) S_tl)).
    { pose proof (sweep_BR_p02 (k + 2) X1 S_tl) as hs.
      replace (k + 2) with (S (k + 1)) in hs at 1 by lia; cbn [rep02 app] in hs.
      exact hs. }
    exists (k + 2), X1.
    split; [exact (reach_trans (reach_trans hpre hr1) hsw) | lia].
Qed.

Lemma step_55_pair_1 (m b : nat) (L R : list nat)
  (hm : 2 <= m) (hb : 2 * W L + 5 <= b) :
  exists (b' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: (rep4 b ++ L)) (0 :: 0 :: 2 :: 0 :: (rep02 m ++ R)))
          (cfg_BR1 (0 :: (rep4 (m - 2) ++ 2 :: (rep4 b' ++ L'))) R) /\
    b + 2 * W L' <= b' + 2 * W L + 5.
Proof.
  destruct m as [| [| m2]]; [lia | lia |].
  replace (S (S m2) - 2) with m2 by lia.
  cbn [rep02 app]; replace (S m2) with (m2 + 1) by lia.
  destruct (zero_p02_1 0 b L (0 :: 0 :: 2 :: (rep02 (m2 + 1) ++ R)) ltac:(lia)) as [b1 [L1 [hr1 hd1]]].
  cbn [Nat.add rep4 app] in hr1.
  assert (hmid : Reach (cfg_BR1 (0 :: 2 :: (rep4 b1 ++ L1)) (0 :: 0 :: 2 :: (rep02 (m2 + 1) ++ R)))
                       (cfg_EL1 (0 :: (rep4 b1 ++ L1)) (0 :: 2 :: 2 :: 0 :: (rep02 (m2 + 1) ++ R)))).
  { set (X := rep4 b1 ++ L1).
    set (Qr := rep02 (m2 + 1) ++ R).
    rstep (step_BR1_00 (2 :: X) (2 :: Qr)).
    rstep (step_BR1_ge2 0 (0 :: 2 :: 2 :: X) Qr).
    rstep (step_EL1_add_two 0 (2 :: 2 :: X) (0 :: Qr)).
    rstep (step_EL1_zero (2 :: 2 :: X) (0 :: 0 :: Qr)).
    rstep (step_CL1_add_three 0 (2 :: X) (1 :: 0 :: Qr)).
    rstep (step_EL1_zero (2 :: X) (0 :: 2 :: 0 :: Qr)).
    rdone (step_CL1_add_three 0 X (1 :: 2 :: 0 :: Qr)). }
  destruct (mEL_pot_1 b1 L1 (2 :: 2 :: 0 :: (rep02 (m2 + 1) ++ R)) ltac:(lia)) as [b2 [L2 [hr2 hd2]]].
  destruct (cross_d2_1 b2 L2 (2 :: 0 :: (rep02 (m2 + 1) ++ R)) ltac:(lia)) as [b3 [L3 [hr3 hd3]]].
  assert (hinc : Reach (cfg_BR1 (0 :: (rep4 b3 ++ L3)) (0 :: 2 :: 0 :: (rep02 (m2 + 1) ++ R)))
                       (cfg_BR1 (0 :: (rep4 (b3 + 1) ++ L3)) (0 :: (rep02 (m2 + 1) ++ R)))).
  { rewrite rep4_succ_r; cbn [app].
    exact (sweep_BR_p02_one (rep4 b3 ++ L3) (0 :: (rep02 (m2 + 1) ++ R))). }
  destruct (zero_p02_1 m2 (b3 + 1) L3 R ltac:(lia)) as [b4 [L4 [hr4 hd4]]].
  exists b4, L4.
  split; [| lia].
  rdone (reach_trans
    (reach_trans (reach_trans (reach_trans (reach_trans hr1 hmid) hr2) hr3) hinc) hr4).
Qed.

Lemma hub_055_2 (a0 a1 : nat) (L : list nat)
  (ha0 : 4 <= a0) (ha1 : 2 * W L + 21 <= a1) :
  exists (a1' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
          (cfg_BR1 (0 :: 3 :: (rep4 (a0 - 4) ++ 2 :: (rep4 a1' ++ L'))) []) /\
    a1 + 2 * W L' <= a1' + 2 * W L + 21.
Proof.
  set (k0 := a0 - 1); set (k1 := a1 - 2).
  assert (hsc1 : Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
                       (cfg_BR1 (0 :: 5 :: (rep4 (k1 + 1) ++ L))
                                (0 :: 2 :: 2 :: (rep02 a0 ++ [0; 0; 3])))).
  { replace a0 with (k0 + 1) by (unfold k0; lia).
    replace a1 with ((k1 + 1) + 1) by (unfold k1; lia).
    pose proof (hub_055_entry k0 (rep4 ((k1 + 1) + 1) ++ L)) as h.
    rewrite (inc1_rep4_succ (k1 + 1) L) in h.
    exact h. }
  destruct (scan_55_tail_any k1 L (rep02 a0 ++ [0; 0; 3]) ltac:(unfold k1; lia))
    as [b1 [L1 [hr1 hd1]]].
  destruct (step_55_pair_1 a0 b1 L1 [0; 0; 3] ltac:(lia) ltac:(unfold k1 in *; lia))
    as [b2 [L2 [hr2 hd2]]].
  assert (hmid : Reach (cfg_BR1 (0 :: (rep4 (a0 - 2) ++ 2 :: (rep4 b2 ++ L2))) [0; 0; 3])
                       (cfg_EL1 (0 :: (rep4 (a0 - 2) ++ 2 :: (rep4 b2 ++ L2))) [0; 2; 1])).
  { set (Y := rep4 (a0 - 2) ++ 2 :: (rep4 b2 ++ L2)).
    rstep (step_BR1_00 Y [3]).
    rstep (br_d3_to_el (2 :: Y)).
    rstep (step_EL1_zero (2 :: Y) [0; 1]).
    rdone (step_CL1_add_three 0 Y [1; 1]). }
  destruct (mEL_pot_2 (a0 - 2) b2 L2 [2; 1] ltac:(lia) ltac:(unfold k1 in *; lia))
    as [b3 [L3 [hr3 hd3]]].
  destruct (cross_d2_2 (a0 - 2 - 1) b3 L3 [1] ltac:(lia) ltac:(unfold k1 in *; lia))
    as [b4 [L4 [hr4 hd4]]].
  replace (a0 - 2 - 1 - 1) with (a0 - 4) in hr4 by lia.
  exists b4, L4.
  split; [| unfold k1 in *; lia].
  exact (reach_trans
    (reach_trans (reach_trans (reach_trans (reach_trans (reach_trans hsc1 hr1) hr2) hmid) hr3) hr4)
    (step_BR1_0d 1 _ [])).
Qed.

Lemma step_55_pair_2 (m a1 a2 : nat) (L R : list nat)
  (hm : 2 <= m) (ha1 : 6 <= a1) (ha2 : 2 * W L + 24 <= a2) :
  exists (a2' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) (0 :: 0 :: 2 :: 0 :: (rep02 m ++ R)))
          (cfg_BR1 (0 :: (rep4 (m - 2) ++ 2 :: (rep4 (a1 - 5) ++ 2 :: (rep4 a2' ++ L')))) R) /\
    a2 + 2 * W L' <= a2' + 2 * W L + 24.
Proof.
  destruct m as [| [| m2]]; [lia | lia |].
  replace (S (S m2) - 2) with m2 by lia.
  cbn [rep02 app]; replace (S m2) with (m2 + 1) by lia.
  destruct (zero_p02_2 0 a1 a2 L (0 :: 0 :: 2 :: (rep02 (m2 + 1) ++ R)) ltac:(lia) ltac:(lia))
    as [b1 [L1 [hr1 hd1]]].
  cbn [Nat.add rep4 app] in hr1.
  assert (hmid : Reach (cfg_BR1 (0 :: 2 :: (rep4 (a1 - 2) ++ 2 :: (rep4 b1 ++ L1)))
                                (0 :: 0 :: 2 :: (rep02 (m2 + 1) ++ R)))
                       (cfg_EL1 (0 :: (rep4 (a1 - 2) ++ 2 :: (rep4 b1 ++ L1)))
                                (0 :: 2 :: 2 :: 0 :: (rep02 (m2 + 1) ++ R)))).
  { set (X := rep4 (a1 - 2) ++ 2 :: (rep4 b1 ++ L1)).
    set (Qr := rep02 (m2 + 1) ++ R).
    rstep (step_BR1_00 (2 :: X) (2 :: Qr)).
    rstep (step_BR1_ge2 0 (0 :: 2 :: 2 :: X) Qr).
    rstep (step_EL1_add_two 0 (2 :: 2 :: X) (0 :: Qr)).
    rstep (step_EL1_zero (2 :: 2 :: X) (0 :: 0 :: Qr)).
    rstep (step_CL1_add_three 0 (2 :: X) (1 :: 0 :: Qr)).
    rstep (step_EL1_zero (2 :: X) (0 :: 2 :: 0 :: Qr)).
    rdone (step_CL1_add_three 0 X (1 :: 2 :: 0 :: Qr)). }
  destruct (mEL_pot_2 (a1 - 2) b1 L1 (2 :: 2 :: 0 :: (rep02 (m2 + 1) ++ R)) ltac:(lia) ltac:(lia))
    as [b2 [L2 [hr2 hd2]]].
  destruct (cross_d2_2 (a1 - 2 - 1) b2 L2 (2 :: 0 :: (rep02 (m2 + 1) ++ R)) ltac:(lia) ltac:(lia))
    as [b3 [L3 [hr3 hd3]]].
  assert (hinc : Reach (cfg_BR1 (0 :: (rep4 (a1 - 2 - 1 - 1) ++ 2 :: (rep4 b3 ++ L3)))
                                (0 :: 2 :: 0 :: (rep02 (m2 + 1) ++ R)))
                       (cfg_BR1 (0 :: (rep4 (a1 - 3) ++ 2 :: (rep4 b3 ++ L3)))
                                (0 :: (rep02 (m2 + 1) ++ R)))).
  { replace (a1 - 3) with ((a1 - 2 - 1 - 1) + 1) by lia.
    rewrite rep4_succ_r; cbn [app].
    exact (sweep_BR_p02_one (rep4 (a1 - 2 - 1 - 1) ++ 2 :: (rep4 b3 ++ L3))
                            (0 :: (rep02 (m2 + 1) ++ R))). }
  destruct (zero_p02_2 m2 (a1 - 3) b3 L3 R ltac:(lia) ltac:(lia)) as [b4 [L4 [hr4 hd4]]].
  replace (a1 - 3 - 2) with (a1 - 5) in hr4 by lia.
  exists b4, L4.
  split; [| lia].
  rdone (reach_trans
    (reach_trans (reach_trans (reach_trans (reach_trans hr1 hmid) hr2) hr3) hinc) hr4).
Qed.

Lemma hub_055_3 (a0 a1 a2 : nat) (L : list nat)
  (ha0 : 4 <= a0) (ha1 : 16 <= a1) (ha2 : 2 * W L + 69 <= a2) :
  exists (a2' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
          (cfg_BR1 (0 :: 3 :: (rep4 (a0 - 4) ++ 2 :: (rep4 (a1 - 16) ++ 2 :: (rep4 a2' ++ L')))) []) /\
    a2 + 2 * W L' <= a2' + 2 * W L + 69.
Proof.
  set (k0 := a0 - 1); set (k1 := a1 - 2); set (k2 := a2 - 2).
  assert (hsc1 : Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
                       (cfg_BR1 (0 :: 5 :: (rep4 (k1 + 1) ++ 2 :: (rep4 a2 ++ L)))
                                (0 :: 2 :: 2 :: (rep02 a0 ++ [0; 0; 3])))).
  { replace a0 with (k0 + 1) by (unfold k0; lia).
    replace a1 with ((k1 + 1) + 1) by (unfold k1; lia).
    pose proof (hub_055_entry k0 (rep4 ((k1 + 1) + 1) ++ 2 :: (rep4 a2 ++ L))) as h.
    rewrite (inc1_rep4_succ (k1 + 1) (2 :: (rep4 a2 ++ L))) in h.
    exact h. }
  assert (hsc2 : Reach (cfg_BR1 (0 :: 5 :: (rep4 (k1 + 1) ++ 2 :: (rep4 a2 ++ L)))
                                (0 :: 2 :: 2 :: (rep02 a0 ++ [0; 0; 3])))
                       (cfg_BR1 (0 :: 5 :: (rep4 (k2 + 1) ++ L))
                                (0 :: 2 :: 2 :: (rep02 (k1 + 1) ++ (0 :: 0 :: 2 :: 0 :: (rep02 a0 ++ [0; 0; 3])))))).
  { replace a2 with ((k2 + 1) + 1) by (unfold k2; lia).
    pose proof (scan_55_ge2 k1 (rep4 ((k2 + 1) + 1) ++ L) (rep02 a0 ++ [0; 0; 3])) as h.
    rewrite (inc1_rep4_succ (k2 + 1) L) in h.
    exact h. }
  destruct (scan_55_tail_any k2 L (rep02 (k1 + 1) ++ (0 :: 0 :: 2 :: 0 :: (rep02 a0 ++ [0; 0; 3])))
              ltac:(unfold k2; lia)) as [b1 [L1 [hr1 hd1]]].
  destruct (step_55_pair_1 (k1 + 1) b1 L1 (0 :: 0 :: 2 :: 0 :: (rep02 a0 ++ [0; 0; 3]))
              ltac:(unfold k1; lia) ltac:(unfold k2 in *; lia)) as [b2 [L2 [hr2 hd2]]].
  destruct (step_55_pair_2 a0 (k1 + 1 - 2) b2 L2 [0; 0; 3]
              ltac:(lia) ltac:(unfold k1; lia) ltac:(unfold k2 in *; lia)) as [b3 [L3 [hr3 hd3]]].
  replace (k1 + 1 - 2 - 5) with (a1 - 8) in hr3 by (unfold k1; lia).
  assert (hmid : Reach (cfg_BR1 (0 :: (rep4 (a0 - 2) ++ 2 :: (rep4 (a1 - 8) ++ 2 :: (rep4 b3 ++ L3)))) [0; 0; 3])
                       (cfg_EL1 (0 :: (rep4 (a0 - 2) ++ 2 :: (rep4 (a1 - 8) ++ 2 :: (rep4 b3 ++ L3)))) [0; 2; 1])).
  { set (Y := rep4 (a0 - 2) ++ 2 :: (rep4 (a1 - 8) ++ 2 :: (rep4 b3 ++ L3))).
    rstep (step_BR1_00 Y [3]).
    rstep (br_d3_to_el (2 :: Y)).
    rstep (step_EL1_zero (2 :: Y) [0; 1]).
    rdone (step_CL1_add_three 0 Y [1; 1]). }
  destruct (mEL_pot_3 (a0 - 2) (a1 - 8) b3 L3 [2; 1]
              ltac:(lia) ltac:(lia) ltac:(unfold k2 in *; lia)) as [b4 [L4 [hr4 hd4]]].
  destruct (cross_d2_3 (a0 - 2 - 1) (a1 - 8 - 4) b4 L4 [1]
              ltac:(lia) ltac:(lia) ltac:(unfold k2 in *; lia)) as [b5 [L5 [hr5 hd5]]].
  replace (a0 - 2 - 1 - 1) with (a0 - 4) in hr5 by lia.
  replace (a1 - 8 - 4 - 4) with (a1 - 16) in hr5 by lia.
  exists b5, L5.
  split; [| unfold k2 in *; lia].
  exact (reach_trans
    (reach_trans (reach_trans (reach_trans (reach_trans (reach_trans
      (reach_trans (reach_trans hsc1 hsc2) hr1) hr2) hr3) hmid) hr4) hr5)
    (step_BR1_0d 1 _ [])).
Qed.

Lemma hub_055_one (a1 a2 : nat) (L : list nat)
  (ha1 : 8 <= a1) (ha2 : 2 * W L + 29 <= a2) :
  exists (a2' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 1 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
          (cfg_BR1 (0 :: 5 :: 2 :: (rep4 (a1 - 6) ++ 2 :: (rep4 a2' ++ L'))) []) /\
    a2 + 2 * W L' <= a2' + 2 * W L + 29.
Proof.
  set (k1 := a1 - 2); set (k2 := a2 - 2).
  assert (hsc1 : Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 1 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
                       (cfg_BR1 (0 :: 5 :: (rep4 (k1 + 1) ++ 2 :: (rep4 a2 ++ L)))
                                (0 :: 2 :: 2 :: (rep02 1 ++ [0; 0; 3])))).
  { replace a1 with ((k1 + 1) + 1) by (unfold k1; lia).
    pose proof (hub_055_entry 0 (rep4 ((k1 + 1) + 1) ++ 2 :: (rep4 a2 ++ L))) as h.
    rewrite (inc1_rep4_succ (k1 + 1) (2 :: (rep4 a2 ++ L))) in h.
    exact h. }
  assert (hsc2 : Reach (cfg_BR1 (0 :: 5 :: (rep4 (k1 + 1) ++ 2 :: (rep4 a2 ++ L)))
                                (0 :: 2 :: 2 :: (rep02 1 ++ [0; 0; 3])))
                       (cfg_BR1 (0 :: 5 :: (rep4 (k2 + 1) ++ L))
                                (0 :: 2 :: 2 :: (rep02 (k1 + 1) ++ (0 :: 0 :: 2 :: 0 :: (rep02 1 ++ [0; 0; 3])))))).
  { replace a2 with ((k2 + 1) + 1) by (unfold k2; lia).
    pose proof (scan_55_ge2 k1 (rep4 ((k2 + 1) + 1) ++ L) (rep02 1 ++ [0; 0; 3])) as h.
    rewrite (inc1_rep4_succ (k2 + 1) L) in h.
    exact h. }
  destruct (scan_55_tail_any k2 L (rep02 (k1 + 1) ++ (0 :: 0 :: 2 :: 0 :: (rep02 1 ++ [0; 0; 3])))
              ltac:(unfold k2; lia)) as [b1 [L1 [hr1 hd1]]].
  destruct (step_55_pair_1 (k1 + 1) b1 L1 (0 :: 0 :: 2 :: 0 :: (rep02 1 ++ [0; 0; 3]))
              ltac:(unfold k1; lia) ltac:(unfold k2 in *; lia)) as [b2 [L2 [hr2 hd2]]].
  destruct (zero_p02_2 0 (k1 + 1 - 2) b2 L2 (0 :: (rep02 1 ++ [0; 0; 3]))
              ltac:(unfold k1; lia) ltac:(unfold k2 in *; lia)) as [b3 [L3 [hr3 hd3]]].
  cbn [Nat.add rep4 rep02 app] in hr2, hr3.
  replace (k1 + 1 - 2 - 2) with (a1 - 5) in hr3 by (unfold k1; lia).
  assert (hmid : Reach (cfg_BR1 (0 :: 2 :: (rep4 (a1 - 5) ++ 2 :: (rep4 b3 ++ L3))) [0; 0; 2; 0; 0; 3])
                       (cfg_EL1 (0 :: (rep4 (a1 - 5) ++ 2 :: (rep4 b3 ++ L3))) [0; 2; 2; 0; 0; 0; 3])).
  { set (X := rep4 (a1 - 5) ++ 2 :: (rep4 b3 ++ L3)).
    rstep (step_BR1_00 (2 :: X) [2; 0; 0; 3]).
    rstep (step_BR1_ge2 0 (0 :: 2 :: 2 :: X) [0; 0; 3]).
    rstep (step_EL1_add_two 0 (2 :: 2 :: X) [0; 0; 0; 3]).
    rstep (step_EL1_zero (2 :: 2 :: X) [0; 0; 0; 0; 3]).
    rstep (step_CL1_add_three 0 (2 :: X) [1; 0; 0; 0; 3]).
    rstep (step_EL1_zero (2 :: X) [0; 2; 0; 0; 0; 3]).
    rdone (step_CL1_add_three 0 X [1; 2; 0; 0; 0; 3]). }
  destruct (mEL_pot_2 (a1 - 5) b3 L3 [2; 2; 0; 0; 0; 3]
              ltac:(lia) ltac:(unfold k2 in *; lia)) as [b4 [L4 [hr4 hd4]]].
  destruct (cross_d2_2 (a1 - 5 - 1) b4 L4 [2; 0; 0; 0; 3]
              ltac:(lia) ltac:(unfold k2 in *; lia)) as [b5 [L5 [hr5 hd5]]].
  assert (hfin : Reach (cfg_BR1 (0 :: (rep4 (a1 - 5 - 1 - 1) ++ 2 :: (rep4 b5 ++ L5))) [0; 2; 0; 0; 0; 3])
                       (cfg_BR1 (0 :: 5 :: 2 :: (rep4 (a1 - 6) ++ 2 :: (rep4 b5 ++ L5))) [])).
  { assert (s1 : Reach (cfg_BR1 (0 :: (rep4 (a1 - 5 - 1 - 1) ++ 2 :: (rep4 b5 ++ L5))) [0; 2; 0; 0; 0; 3])
                       (cfg_BR1 (0 :: (rep4 (a1 - 6) ++ 2 :: (rep4 b5 ++ L5))) [0; 0; 0; 3])).
    { replace (a1 - 6) with ((a1 - 5 - 1 - 1) + 1) by lia.
      rewrite rep4_succ_r; cbn [app].
      exact (sweep_BR_p02_one (rep4 (a1 - 5 - 1 - 1) ++ 2 :: (rep4 b5 ++ L5)) [0; 0; 0; 3]). }
    exact (reach_trans (reach_trans s1 (step_BR1_00 _ [0; 3])) (step_BR1_0d 3 _ [])). }
  exists b5, L5.
  split; [| unfold k2 in *; lia].
  exact (reach_trans
    (reach_trans (reach_trans (reach_trans (reach_trans (reach_trans
      (reach_trans (reach_trans hsc1 hsc2) hr1) hr2) hr3) hmid) hr4) hr5)
    hfin).
Qed.

Lemma cycle_3_step (a0 a1 a2 : nat) (L : list nat)
  (ha0 : 9 <= a0) (ha1 : 28 <= a1) (ha2 : 2 * W L + 117 <= a2) :
  exists (a2' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
          (cfg_BR1 (0 :: 5 :: 5 :: (rep4 (a0 - 9) ++ 2 :: (rep4 (a1 - 28) ++ 2 :: (rep4 a2' ++ L')))) []) /\
    a2 + 2 * W L' <= a2' + 2 * W L + 117.
Proof.
  destruct (hub_055_3 a0 a1 a2 L ltac:(lia) ltac:(lia) ltac:(lia)) as [b1 [L1 [hr1 hd1]]].
  destruct (hub_03_3 (a0 - 4) (a1 - 16) b1 L1 ltac:(lia) ltac:(lia) ltac:(lia)) as [b2 [L2 [hr2 hd2]]].
  replace (a0 - 4 - 3) with ((a0 - 9) + 2) in hr2 by lia.
  replace (a1 - 16 - 12) with (a1 - 28) in hr2 by lia.
  pose proof (hub_0_step (a0 - 9) (2 :: (rep4 (a1 - 28) ++ 2 :: (rep4 b2 ++ L2)))) as hr3.
  exists b2, L2.
  split; [exact (reach_trans (reach_trans hr1 hr2) hr3) | lia].
Qed.

Lemma cycle_3_iter (n : nat) :
  forall (a0 a1 a2 : nat) (L : list nat),
    9 * n <= a0 -> 28 * n <= a1 -> 2 * W L + 117 * n <= a2 ->
    exists (a2' : nat) (L' : list nat),
      Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
            (cfg_BR1 (0 :: 5 :: 5 :: (rep4 (a0 - 9 * n) ++ 2 :: (rep4 (a1 - 28 * n) ++ 2 :: (rep4 a2' ++ L')))) []) /\
      a2 + 2 * W L' <= a2' + 2 * W L + 117 * n.
Proof.
  induction n as [| n' IH]; intros a0 a1 a2 L ha0 ha1 ha2.
  - exists a2, L.
    replace (a0 - 9 * 0) with a0 by lia.
    replace (a1 - 28 * 0) with a1 by lia.
    split; [apply reach_refl | lia].
  - destruct (cycle_3_step a0 a1 a2 L ltac:(lia) ltac:(lia) ltac:(lia)) as [b1 [L1 [hr1 hd1]]].
    destruct (IH (a0 - 9) (a1 - 28) b1 L1 ltac:(lia) ltac:(lia) ltac:(lia)) as [b2 [L2 [hr2 hd2]]].
    replace (a0 - 9 - 9 * n') with (a0 - 9 * S n') in hr2 by lia.
    replace (a1 - 28 - 28 * n') with (a1 - 28 * S n') in hr2 by lia.
    exists b2, L2.
    split; [exact (reach_trans hr1 hr2) | lia].
Qed.

Lemma cycle_2_step (a0 a1 : nat) (L : list nat)
  (ha0 : 9 <= a0) (ha1 : 2 * W L + 33 <= a1) :
  exists (a1' : nat) (L' : list nat),
    Reach (cfg_BR1 (0 :: 3 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
          (cfg_BR1 (0 :: 3 :: (rep4 (a0 - 9) ++ 2 :: (rep4 a1' ++ L'))) []) /\
    a1 + 2 * W L' <= a1' + 2 * W L + 33.
Proof.
  destruct (hub_03_2 a0 a1 L ltac:(lia) ltac:(lia)) as [b1 [L1 [hr1 hd1]]].
  replace (a0 - 3) with ((a0 - 5) + 2) in hr1 by lia.
  pose proof (hub_0_step (a0 - 5) (2 :: (rep4 b1 ++ L1))) as hr2.
  destruct (hub_055_2 (a0 - 5) b1 L1 ltac:(lia) ltac:(lia)) as [b2 [L2 [hr3 hd3]]].
  replace (a0 - 5 - 4) with (a0 - 9) in hr3 by lia.
  exists b2, L2.
  split; [exact (reach_trans (reach_trans hr1 hr2) hr3) | lia].
Qed.

Lemma cycle_2_iter (n : nat) :
  forall (a0 a1 : nat) (L : list nat),
    9 * n <= a0 -> 2 * W L + 33 * n <= a1 ->
    exists (a1' : nat) (L' : list nat),
      Reach (cfg_BR1 (0 :: 3 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
            (cfg_BR1 (0 :: 3 :: (rep4 (a0 - 9 * n) ++ 2 :: (rep4 a1' ++ L'))) []) /\
      a1 + 2 * W L' <= a1' + 2 * W L + 33 * n.
Proof.
  induction n as [| n' IH]; intros a0 a1 L ha0 ha1.
  - exists a1, L.
    replace (a0 - 9 * 0) with a0 by lia.
    split; [apply reach_refl | lia].
  - destruct (cycle_2_step a0 a1 L ltac:(lia) ltac:(lia)) as [b1 [L1 [hr1 hd1]]].
    destruct (IH (a0 - 9) b1 L1 ltac:(lia) ltac:(lia)) as [b2 [L2 [hr2 hd2]]].
    replace (a0 - 9 - 9 * n') with (a0 - 9 * S n') in hr2 by lia.
    exists b2, L2.
    split; [exact (reach_trans hr1 hr2) | lia].
Qed.

Lemma halts_from_H11120 (L : list nat) (hWL : W L <= 14) :
  halts tm
    (cfg_BR1 (0 :: 5 :: 5 ::
      (rep4 (N.to_nat 156691%N) ++ 2 ::
       (rep4 (N.to_nat 3931792%N) ++ 2 ::
        (rep4 (N.to_nat 19317108%N) ++ L)))) []).
Proof.
  destruct (cycle_3_iter (N.to_nat 17410%N)
              (N.to_nat 156691%N) (N.to_nat 3931792%N) (N.to_nat 19317108%N) L
              ltac:(lia) ltac:(lia) ltac:(lia))
    as [a2_1 [L1 [hr1 hd1]]].
  replace (N.to_nat 156691%N - 9 * N.to_nat 17410%N) with 1 in hr1 by lia.
  replace (N.to_nat 3931792%N - 28 * N.to_nat 17410%N) with (N.to_nat 3444312%N) in hr1 by lia.
  destruct (hub_055_one (N.to_nat 3444312%N) a2_1 L1 ltac:(lia) ltac:(lia))
    as [a2_2 [L2 [hr2 hd2]]].
  replace (N.to_nat 3444312%N - 6) with (N.to_nat 3444306%N) in hr2 by lia.
  destruct (hub_052_2 (N.to_nat 3444306%N) a2_2 L2 ltac:(lia) ltac:(lia))
    as [a2_3 [L3 [hr3 hd3]]].
  replace (N.to_nat 3444306%N - 4) with (N.to_nat 3444302%N) in hr3 by lia.
  destruct (cycle_2_iter (N.to_nat 382700%N) (N.to_nat 3444302%N) a2_3 L3
              ltac:(lia) ltac:(lia))
    as [a2_4 [L4 [hr4 hd4]]].
  replace (N.to_nat 3444302%N - 9 * N.to_nat 382700%N) with 2 in hr4 by lia.
  pose proof (hub_03_halt a2_4 L4 ltac:(lia)) as hhalt.
  exact (halts_evstep tm _ _ hhalt
    (reach_trans (reach_trans (reach_trans hr1 hr2) hr3) hr4)).
Qed.

(** * Section 4: Stage 1 Exact Block-List Stepper over Binary N *)

Inductive Pfx : Type := p0 | p03 | p05 | p055.


Definition encPfx (pf : Pfx) : list nat :=
  match pf with
  | p0 => [0]
  | p03 => [0; 3]
  | p05 => [0; 5]
  | p055 => [0; 5; 5]
  end.

Fixpoint encBlks (bs : list nat) : list nat :=
  match bs with
  | [] => []
  | a :: rest =>
    match rest with
    | [] => rep4 a
    | _ :: _ => rep4 a ++ 2 :: encBlks rest
    end
  end.

Definition encBlks_N (bs : list N) : list nat :=
  encBlks (List.map N.to_nat bs).

Definition encHub (pf : Pfx) (bs : list N) : Q * tape :=
  cfg_BR1 (encPfx pf ++ encBlks_N bs) [].

Lemma encBlks_cons_ne (a : nat) {bs : list nat} (hne : bs <> []) :
  encBlks (a :: bs) = rep4 a ++ 2 :: encBlks bs.
Proof.
  destruct bs as [| b0 tl]; [exfalso; exact (hne eq_refl) | reflexivity].
Qed.

Lemma encBlks_add_head (a n : nat) (bs : list nat) :
  rep4 n ++ encBlks (a :: bs) = encBlks ((a + n) :: bs).
Proof.
  destruct bs as [| b0 tl].
  - cbn [encBlks].
    pose proof (rep4_add n a []) as h1.
    rewrite !app_nil_r in h1.
    replace (a + n) with (n + a) by lia.
    symmetry; exact h1.
  - cbn [encBlks].
    replace (a + n) with (n + a) by lia.
    symmetry; exact (rep4_add n a (2 :: encBlks (b0 :: tl))).
Qed.

Lemma W_encBlks_cons (bs : list nat) :
  forall (a : nat), W (encBlks (a :: bs)) = List.length bs.
Proof.
  induction bs as [| b0 tl IH]; intro a.
  - cbn [encBlks List.length].
    pose proof (W_rep4_append a []) as h; rewrite app_nil_r in h; exact h.
  - rewrite (encBlks_cons_ne a (bs := b0 :: tl) ltac:(discriminate)).
    rewrite W_rep4_append.
    cbn [W wf div4 Nat.mul Nat.add List.length].
    rewrite (IH b0). lia.
Qed.

Lemma map_to_nat_ne_nil {bs : list N} (hne : bs <> []) :
  List.map N.to_nat bs <> [].
Proof.
  destruct bs as [| x0 xtl]; [exfalso; exact (hne eq_refl) | discriminate].
Qed.

Lemma encBlks_N_cons_ne (a : N) {bs : list N} (hne : bs <> []) :
  encBlks_N (a :: bs) = rep4 (N.to_nat a) ++ 2 :: encBlks_N bs.
Proof.
  unfold encBlks_N; cbn [List.map].
  exact (encBlks_cons_ne (N.to_nat a) (map_to_nat_ne_nil hne)).
Qed.

Lemma encBlks_N_zero_cons {bs : list N} (hne : bs <> []) :
  encBlks_N (0%N :: bs) = 2 :: encBlks_N bs.
Proof.
  rewrite (encBlks_N_cons_ne 0%N hne); reflexivity.
Qed.

Lemma encBlks_N_add_head (a n : N) (bs : list N) :
  rep4 (N.to_nat n) ++ encBlks_N (a :: bs) = encBlks_N ((a + n)%N :: bs).
Proof.
  unfold encBlks_N; cbn [List.map].
  rewrite N2Nat.inj_add.
  exact (encBlks_add_head (N.to_nat a) (N.to_nat n) (List.map N.to_nat bs)).
Qed.

Lemma W_encBlks_N_cons (bs : list N) (a : N) :
  W (encBlks_N (a :: bs)) = List.length bs.
Proof.
  unfold encBlks_N; cbn [List.map].
  rewrite W_encBlks_cons, length_map.
  reflexivity.
Qed.


Inductive RTag : Type := r_z0 | r_z2 | r_p.

Fixpoint encR_N (rs : list (RTag * N)) : list nat :=
  match rs with
  | [] => []
  | (r_z0, _) :: tl => 0 :: encR_N tl
  | (r_z2, _) :: tl => 2 :: encR_N tl
  | (r_p, n) :: tl => rep02 (N.to_nat n) ++ encR_N tl
  end.

(** ** Exact Linear Operator subTail over N and Soundness *)

Fixpoint subTail (d : N) (bs : list N) : option (list N) :=
  match bs with
  | [] => None
  | b0 :: rest =>
    match rest with
    | [] => Some [(b0 + d)%N]
    | _ :: _ =>
      if N.leb d b0 then
        match subTail (4 * d)%N rest with
        | None => None
        | Some tl' => Some ((b0 - d)%N :: tl')
        end
      else None
    end
  end.

Lemma subTail_cons_cons (d b0 c0 : N) (tl : list N) :
  subTail d (b0 :: c0 :: tl) =
    if N.leb d b0 then
      match subTail (4 * d)%N (c0 :: tl) with
      | None => None
      | Some tl' => Some ((b0 - d)%N :: tl')
      end
    else None.
Proof. reflexivity. Qed.

Lemma subTail_length (bs : list N) :
  forall (d : N) (out : list N),
    subTail d bs = Some out -> List.length out = List.length bs.
Proof.
  induction bs as [| b0 [| c0 tl] IH]; intros d out h.
  - discriminate h.
  - inversion h; subst; reflexivity.
  - rewrite subTail_cons_cons in h.
    destruct (N.leb d b0) eqn:hb; [| discriminate h].
    destruct (subTail (4 * d)%N (c0 :: tl)) as [tl' |] eqn:ht; [| discriminate h].
    inversion h; subst; clear h.
    cbn [List.length]. f_equal. exact (IH (4 * d)%N tl' ht).
Qed.

Lemma subTail_ne_nil {d : N} {bs out : list N} (h : subTail d bs = Some out) :
  out <> [].
Proof.
  pose proof (subTail_length bs d out h) as hl.
  destruct bs as [| x0 xtl]; [discriminate h |].
  intros ->; discriminate hl.
Qed.

Lemma subTail_zero (bs : list N) : bs <> [] -> subTail 0%N bs = Some bs.
Proof.
  induction bs as [| b0 [| c0 tl] IH]; intro hne.
  - exfalso; exact (hne eq_refl).
  - cbn [subTail]. rewrite N.add_0_r. reflexivity.
  - rewrite subTail_cons_cons.
    replace (N.leb 0%N b0) with true by (symmetry; apply N.leb_le; lia).
    replace (4 * 0)%N with 0%N by lia.
    rewrite (IH ltac:(discriminate)).
    rewrite N.sub_0_r. reflexivity.
Qed.

Lemma subTail_split (bs : list N) :
  forall (d1 d2 : N) (out : list N),
    subTail (d1 + d2)%N bs = Some out ->
    exists mid, subTail d1 bs = Some mid /\ subTail d2 mid = Some out.
Proof.
  induction bs as [| b0 [| c0 tl] IH]; intros d1 d2 out h.
  - discriminate h.
  - inversion h; subst; clear h.
    exists [(b0 + d1)%N].
    split; [reflexivity | cbn [subTail]; do 2 f_equal; lia].
  - rewrite subTail_cons_cons in h.
    destruct (N.leb (d1 + d2)%N b0) eqn:hb; [| discriminate h].
    apply N.leb_le in hb.
    destruct (subTail (4 * (d1 + d2))%N (c0 :: tl)) as [out_tl |] eqn:ht; [| discriminate h].
    inversion h; subst; clear h.
    replace (4 * (d1 + d2))%N with (4 * d1 + 4 * d2)%N in ht by lia.
    destruct (IH (4 * d1)%N (4 * d2)%N out_tl ht) as [mid_tl [hm1 hm2]].
    pose proof (subTail_ne_nil hm1) as hne.
    destruct mid_tl as [| mhd mtl]; [exfalso; exact (hne eq_refl) |].
    exists ((b0 - d1)%N :: mhd :: mtl).
    split.
    + rewrite subTail_cons_cons.
      replace (N.leb d1 b0) with true by (symmetry; apply N.leb_le; lia).
      rewrite hm1; reflexivity.
    + rewrite subTail_cons_cons.
      replace (N.leb d2 (b0 - d1)%N) with true by (symmetry; apply N.leb_le; lia).
      rewrite hm2; do 2 f_equal; lia.
Qed.

Lemma mEL_single (a : nat) (S_tail : list nat) :
  Reach (cfg_EL1 (0 :: rep4 a) (0 :: S_tail)) (cfg_BR1 (0 :: rep4 (a + 1)) S_tail).
Proof.
  pose proof (sweep_EL_f4 a [] S_tail) as h1.
  rewrite app_nil_r in h1.
  assert (h2 : Reach (cfg_EL1 [0] (0 :: (rep02 a ++ S_tail)))
                     (cfg_BR1 [0; 4] (rep02 a ++ S_tail))).
  { rstep (step_EL1_zero [] (0 :: (rep02 a ++ S_tail))).
    rstep (step_CL1_zero [] (1 :: (rep02 a ++ S_tail))).
    rstep (step_CL1_nil (3 :: (rep02 a ++ S_tail))).
    rdone (step_EL1_nil_cons 4 (rep02 a ++ S_tail)). }
  pose proof (sweep_BR_p02 a [4] S_tail) as h3.
  assert (hrep : rep4 a ++ [4] = rep4 (a + 1)).
  { pose proof (rep4_snoc a []) as hs; rewrite app_nil_r in hs; rewrite rep4_succ_r; exact hs. }
  rewrite hrep in h3.
  exact (reach_trans (reach_trans h1 h2) h3).
Qed.

Lemma mEL_subTail_one (n : nat) :
  forall (bs out : list N),
    List.length bs = n -> subTail 1%N bs = Some out ->
    forall (S_tail : list nat),
      Reach (cfg_EL1 (0 :: encBlks_N bs) (0 :: S_tail))
            (cfg_BR1 (0 :: encBlks_N out) S_tail).
Proof.
  induction n as [| n' IH]; intros bs out hlen hsub S_tail.
  - destruct bs as [| x0 xtl]; [discriminate hsub | discriminate hlen].
  - destruct bs as [| a [| b0 rest]]; [discriminate hsub | |].
    + inversion hsub; subst; clear hsub.
      unfold encBlks_N; cbn [List.map encBlks].
      rewrite N2Nat.inj_add.
      change (N.to_nat 1%N) with 1.
      exact (mEL_single (N.to_nat a) S_tail).
    + rewrite subTail_cons_cons in hsub.
      destruct (N.leb 1%N a) eqn:hb; [| discriminate hsub].
      apply N.leb_le in hb.
      change (4 * 1)%N with 4%N in hsub.
      destruct (subTail 4%N (b0 :: rest)) as [out_tl |] eqn:ht; [| discriminate hsub].
      inversion hsub; subst; clear hsub.
      change 4%N with (1 + 3)%N in ht.
      destruct (subTail_split (b0 :: rest) 1%N 3%N out_tl ht) as [t1 [ht1 ht13]].
      change 3%N with (1 + 2)%N in ht13.
      destruct (subTail_split t1 1%N 2%N out_tl ht13) as [t2 [ht2 ht22]].
      change 2%N with (1 + 1)%N in ht22.
      destruct (subTail_split t2 1%N 1%N out_tl ht22) as [t3 [ht3 ht4]].
      assert (hl0 : List.length (b0 :: rest) = n') by (cbn [List.length] in hlen |- *; lia).
      assert (hl1 : List.length t1 = n') by (rewrite (subTail_length _ _ _ ht1); exact hl0).
      assert (hl2 : List.length t2 = n') by (rewrite (subTail_length _ _ _ ht2); exact hl1).
      assert (hl3 : List.length t3 = n') by (rewrite (subTail_length _ _ _ ht3); exact hl2).
      pose proof (subTail_ne_nil ht4) as hout_ne.
      rewrite (encBlks_N_cons_ne (a - 1)%N hout_ne).
      set (m := N.to_nat (a - 1)%N).
      assert (hm : N.to_nat a = m + 1) by (unfold m; lia).
      assert (hcons_lhs : encBlks_N (a :: b0 :: rest) =
                          rep4 (m + 1) ++ 2 :: encBlks_N (b0 :: rest)).
      { unfold encBlks_N; cbn [List.map encBlks]; rewrite hm; reflexivity. }
      rewrite hcons_lhs.
      assert (s0 : Reach (cfg_EL1 (0 :: (rep4 (m + 1) ++ 2 :: encBlks_N (b0 :: rest))) (0 :: S_tail))
                         (cfg_EL1 (0 :: encBlks_N (b0 :: rest)) (0 :: 2 :: (rep02 (m + 1) ++ S_tail)))).
      { rstep (sweep_EL_f4 (m + 1) (2 :: encBlks_N (b0 :: rest)) S_tail).
        rstep (step_EL1_zero (2 :: encBlks_N (b0 :: rest)) (0 :: (rep02 (m + 1) ++ S_tail))).
        rdone (step_CL1_add_three 0 (encBlks_N (b0 :: rest)) (1 :: (rep02 (m + 1) ++ S_tail))). }
      pose proof (IH (b0 :: rest) t1 hl0 ht1 (2 :: (rep02 (m + 1) ++ S_tail))) as s1.
      assert (sc1 : Reach (cfg_BR1 (0 :: encBlks_N t1) (2 :: (rep02 (m + 1) ++ S_tail)))
                          (cfg_EL1 (0 :: encBlks_N t1) (0 :: 0 :: (rep02 (m + 1) ++ S_tail)))).
      { rstep (step_BR1_ge2 0 (0 :: encBlks_N t1) (rep02 (m + 1) ++ S_tail)).
        rdone (step_EL1_add_two 0 (encBlks_N t1) (0 :: (rep02 (m + 1) ++ S_tail))). }
      pose proof (IH t1 t2 hl1 ht2 (0 :: (rep02 (m + 1) ++ S_tail))) as s2.
      rewrite rep02_succ_r in s0, s1, sc1, s2; cbn [app] in s0, s1, sc1, s2.
      assert (smid : Reach (cfg_BR1 (0 :: encBlks_N t2) (0 :: 0 :: 2 :: (rep02 m ++ S_tail)))
                           (cfg_EL1 (0 :: encBlks_N t2) (0 :: 2 :: 0 :: (rep02 m ++ S_tail)))).
      { rstep (step_BR1_00 (encBlks_N t2) (2 :: (rep02 m ++ S_tail))).
        rstep (step_BR1_ge2 0 (0 :: 2 :: encBlks_N t2) (rep02 m ++ S_tail)).
        rstep (step_EL1_add_two 0 (2 :: encBlks_N t2) (0 :: (rep02 m ++ S_tail))).
        rstep (step_EL1_zero (2 :: encBlks_N t2) (0 :: 0 :: (rep02 m ++ S_tail))).
        rdone (step_CL1_add_three 0 (encBlks_N t2) (1 :: 0 :: (rep02 m ++ S_tail))). }
      pose proof (IH t2 t3 hl2 ht3 (2 :: 0 :: (rep02 m ++ S_tail))) as s3.
      assert (sc2 : Reach (cfg_BR1 (0 :: encBlks_N t3) (2 :: 0 :: (rep02 m ++ S_tail)))
                          (cfg_EL1 (0 :: encBlks_N t3) (0 :: 0 :: 0 :: (rep02 m ++ S_tail)))).
      { rstep (step_BR1_ge2 0 (0 :: encBlks_N t3) (0 :: (rep02 m ++ S_tail))).
        rdone (step_EL1_add_two 0 (encBlks_N t3) (0 :: 0 :: (rep02 m ++ S_tail))). }
      pose proof (IH t3 out_tl hl3 ht4 (0 :: 0 :: (rep02 m ++ S_tail))) as s4.
      pose proof (reach_trans (step_BR1_00 (encBlks_N out_tl) (rep02 m ++ S_tail))
                              (sweep_BR_p02 m (2 :: encBlks_N out_tl) S_tail)) as sfin.
      exact (reach_trans
        (reach_trans (reach_trans (reach_trans (reach_trans (reach_trans
          (reach_trans s0 s1) sc1) s2) smid) s3) sc2)
        (reach_trans s4 sfin)).
Qed.

Lemma mEL_subTail_zero_two {bs out : list N} (hne : bs <> [])
  (hsub : subTail 2%N bs = Some out) (S_tail : list nat) :
  Reach (cfg_EL1 (0 :: encBlks_N (0%N :: bs)) (0 :: S_tail))
        (cfg_BR1 (0 :: encBlks_N out) (0 :: S_tail)).
Proof.
  change 2%N with (1 + 1)%N in hsub.
  destruct (subTail_split bs 1%N 1%N out hsub) as [mid [hm1 hm2]].
  rewrite (encBlks_N_zero_cons hne).
  assert (s0 : Reach (cfg_EL1 (0 :: 2 :: encBlks_N bs) (0 :: S_tail))
                     (cfg_EL1 (0 :: encBlks_N bs) (0 :: 2 :: S_tail))).
  { rstep (step_EL1_zero (2 :: encBlks_N bs) (0 :: S_tail)).
    rdone (step_CL1_add_three 0 (encBlks_N bs) (1 :: S_tail)). }
  pose proof (mEL_subTail_one (List.length bs) bs mid eq_refl hm1 (2 :: S_tail)) as s1.
  assert (sc : Reach (cfg_BR1 (0 :: encBlks_N mid) (2 :: S_tail))
                     (cfg_EL1 (0 :: encBlks_N mid) (0 :: 0 :: S_tail))).
  { rstep (step_BR1_ge2 0 (0 :: encBlks_N mid) S_tail).
    rdone (step_EL1_add_two 0 (encBlks_N mid) (0 :: S_tail)). }
  pose proof (mEL_subTail_one (List.length mid) mid out eq_refl hm2 (0 :: S_tail)) as s2.
  exact (reach_trans (reach_trans (reach_trans s0 s1) sc) s2).
Qed.

Lemma zero_p02_subTail {bs out : list N} (n : N)
  (hsub : subTail 2%N bs = Some out) (S_tail : list nat) :
  Reach (cfg_BR1 (0 :: encBlks_N bs) (0 :: (rep02 (N.to_nat n + 1) ++ S_tail)))
        (cfg_BR1 (0 :: encBlks_N (n :: out)) S_tail).
Proof.
  change 2%N with (1 + 1)%N in hsub.
  destruct (subTail_split bs 1%N 1%N out hsub) as [mid [hm1 hm2]].
  pose proof (subTail_ne_nil hm2) as hout_ne.
  rewrite (encBlks_N_cons_ne n hout_ne).
  rewrite rep02_succ_r; cbn [app].
  set (nv := N.to_nat n).
  assert (s0 : Reach (cfg_BR1 (0 :: encBlks_N bs) (0 :: 0 :: 2 :: (rep02 nv ++ S_tail)))
                     (cfg_EL1 (0 :: encBlks_N bs) (0 :: 2 :: 0 :: (rep02 nv ++ S_tail)))).
  { rstep (step_BR1_00 (encBlks_N bs) (2 :: (rep02 nv ++ S_tail))).
    rstep (step_BR1_ge2 0 (0 :: 2 :: encBlks_N bs) (rep02 nv ++ S_tail)).
    rstep (step_EL1_add_two 0 (2 :: encBlks_N bs) (0 :: (rep02 nv ++ S_tail))).
    rstep (step_EL1_zero (2 :: encBlks_N bs) (0 :: 0 :: (rep02 nv ++ S_tail))).
    rdone (step_CL1_add_three 0 (encBlks_N bs) (1 :: 0 :: (rep02 nv ++ S_tail))). }
  pose proof (mEL_subTail_one (List.length bs) bs mid eq_refl hm1 (2 :: 0 :: (rep02 nv ++ S_tail))) as s1.
  assert (sc : Reach (cfg_BR1 (0 :: encBlks_N mid) (2 :: 0 :: (rep02 nv ++ S_tail)))
                     (cfg_EL1 (0 :: encBlks_N mid) (0 :: 0 :: 0 :: (rep02 nv ++ S_tail)))).
  { rstep (step_BR1_ge2 0 (0 :: encBlks_N mid) (0 :: (rep02 nv ++ S_tail))).
    rdone (step_EL1_add_two 0 (encBlks_N mid) (0 :: 0 :: (rep02 nv ++ S_tail))). }
  pose proof (mEL_subTail_one (List.length mid) mid out eq_refl hm2 (0 :: 0 :: (rep02 nv ++ S_tail))) as s2.
  pose proof (reach_trans (step_BR1_00 (encBlks_N out) (rep02 nv ++ S_tail))
                          (sweep_BR_p02 nv (2 :: encBlks_N out) S_tail)) as sfin.
  exact (reach_trans (reach_trans (reach_trans (reach_trans s0 s1) sc) s2) sfin).
Qed.

Lemma hub_03_subTail {bs out : list N} (hsub : subTail 3%N bs = Some out) :
  Reach (encHub p03 bs) (encHub p0 out).
Proof.
  change 3%N with (1 + 2)%N in hsub.
  destruct (subTail_split bs 1%N 2%N out hsub) as [t1 [ht1 ht12]].
  change 2%N with (1 + 1)%N in ht12.
  destruct (subTail_split t1 1%N 1%N out ht12) as [t2 [ht2 ht3]].
  pose proof (hub_03_entry (encBlks_N bs)) as s0.
  pose proof (mEL_subTail_one (List.length bs) bs t1 eq_refl ht1 [3]) as s1.
  pose proof (mEL_subTail_one (List.length t1) t1 t2 eq_refl ht2 [1]) as s2.
  pose proof (mEL_subTail_one (List.length t2) t2 out eq_refl ht3 []) as s3.
  exact (reach_trans
    (reach_trans (reach_trans (reach_trans (reach_trans s0 s1) (br_d3_to_el _)) s2)
                 (br_d1_to_el _))
    s3).
Qed.

Lemma hub_05_entry (L : list nat) :
  Reach (cfg_BR1 (0 :: 5 :: L) []) (cfg_EL1 (0 :: L) [0; 0; 3]).
Proof.
  rstep (step_BR1_nil (0 :: 5 :: L)).
  rstep (step_CL1_zero (5 :: L) [0]).
  rstep (step_CL1_add_three 2 L [2]).
  rdone (step_EL1_add_two 0 L [0; 3]).
Qed.

Lemma hub_05_subTail_one {bs out : list N} (hsub : subTail 1%N bs = Some out) :
  Reach (encHub p05 bs) (encHub p05 out).
Proof.
  exact (reach_trans
    (reach_trans (hub_05_entry (encBlks_N bs))
                 (mEL_subTail_one (List.length bs) bs out eq_refl hsub [0; 3]))
    (step_BR1_0d 3 (encBlks_N out) [])).
Qed.

Lemma hub_05_batch (m : N) :
  forall (bs out : list N),
    subTail m bs = Some out -> Reach (encHub p05 bs) (encHub p05 out).
Proof.
  pattern m; apply N.peano_ind.
  - intros bs out h.
    assert (hne : bs <> []) by (destruct bs; [discriminate h | discriminate]).
    rewrite (subTail_zero bs hne) in h.
    inversion h; subst. apply reach_refl.
  - intros m' IHm bs out h.
    replace (N.succ m') with (1 + m')%N in h by lia.
    destruct (subTail_split bs 1%N m' out h) as [mid [hm1 hmm]].
    exact (reach_trans (hub_05_subTail_one hm1) (IHm mid out hmm)).
Qed.

(** ** Mutual evalBody and runStream over N + Soundness *)

Fixpoint evalBody (fuel : nat) (bs : list N) {struct fuel} : option (list N * bool) :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match bs with
    | [] => None
    | [a] => Some ([(a + 1)%N], false)
    | a :: b0 :: tl =>
      if N.eqb a 0%N then
        match subTail 2%N (b0 :: tl) with
        | Some out => Some (out, true)
        | None =>
          match evalBody fuel' (b0 :: tl) with
          | None => None
          | Some (ls, has0) =>
            runStream fuel' ls (if has0 then [(r_z0, 0%N); (r_z2, 0%N)] else [(r_z2, 0%N)])
          end
        end
      else
        match subTail 1%N (a :: b0 :: tl) with
        | Some out => Some (out, false)
        | None =>
          match evalBody fuel' (b0 :: tl) with
          | None => None
          | Some (ls, has0) =>
            runStream fuel' ls
              (if has0 then [(r_z0, 0%N); (r_z2, 0%N); (r_p, a)] else [(r_z2, 0%N); (r_p, a)])
          end
        end
    end
  end
with runStream (fuel : nat) (ls : list N) (rs : list (RTag * N)) {struct fuel} :
  option (list N * bool) :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match ls with
    | [] => None
    | a :: tl =>
      match rs with
      | [] => Some (a :: tl, false)
      | (r_p, n) :: rs' =>
        runStream fuel' ((a + n)%N :: tl) rs'
      | (r_z2, _) :: rs' =>
        match evalBody fuel' (a :: tl) with
        | None => None
        | Some (ls2, false) => runStream fuel' ls2 ((r_z0, 0%N) :: rs')
        | Some (ls2, true) => runStream fuel' (0%N :: ls2) rs'
        end
      | [(r_z0, _)] => Some (a :: tl, true)
      | (r_z0, _) :: (r_z0, _) :: rs2 =>
        runStream fuel' (0%N :: a :: tl) rs2
      | (r_z0, _) :: (r_z2, _) :: rs2 =>
        runStream fuel' ((a + 1)%N :: tl) rs2
      | (r_z0, _) :: (r_p, n) :: rs2 =>
        if N.eqb n 0%N then
          runStream fuel' (a :: tl) ((r_z0, 0%N) :: rs2)
        else
          match subTail 2%N (a :: tl) with
          | Some ls2 => runStream fuel' ((n - 1)%N :: ls2) rs2
          | None =>
            runStream fuel' (0%N :: a :: tl)
              (if N.eqb n 1%N then (r_z2, 0%N) :: rs2 else (r_z2, 0%N) :: (r_p, (n - 1)%N) :: rs2)
          end
      end
    end
  end.

Lemma eval_run_sound (fuel : nat) :
  (forall (bs out : list N) (has0 : bool),
    evalBody fuel bs = Some (out, has0) ->
    out <> [] /\ forall S_tail : list nat,
      Reach (cfg_EL1 (0 :: encBlks_N bs) (0 :: S_tail))
            (cfg_BR1 (0 :: encBlks_N out) (if has0 then 0 :: S_tail else S_tail))) /\
  (forall (ls : list N) (rs : list (RTag * N)) (out : list N) (has0 : bool),
    runStream fuel ls rs = Some (out, has0) ->
    out <> [] /\ forall S_tail : list nat,
      Reach (cfg_BR1 (0 :: encBlks_N ls) (encR_N rs ++ S_tail))
            (cfg_BR1 (0 :: encBlks_N out) (if has0 then 0 :: S_tail else S_tail))).
Proof.
  induction fuel as [| fuel' [ihEL ihRS]].
  - split; intros; discriminate.
  - split.
    + (* evalBody (S fuel') *)
      intros bs out has0 h.
      destruct bs as [| a [| b0 rest]]; [discriminate h | |].
      * inversion h; subst; clear h.
        split; [discriminate | intro S_tail].
        unfold encBlks_N; cbn [List.map encBlks].
        rewrite N2Nat.inj_add.
        change (N.to_nat 1%N) with 1.
        exact (mEL_single (N.to_nat a) S_tail).
      * cbn [evalBody] in h.
        destruct (N.eqb a 0%N) eqn:ha0.
        -- apply N.eqb_eq in ha0; subst a.
           destruct (subTail 2%N (b0 :: rest)) as [out' |] eqn:hst.
           ++ inversion h; subst; clear h.
              split; [exact (subTail_ne_nil hst) |
                      intro S_tail; exact (mEL_subTail_zero_two (bs := b0 :: rest) ltac:(discriminate) hst S_tail)].
           ++ destruct (evalBody fuel' (b0 :: rest)) as [[ls h0] |] eqn:heb; [| discriminate h].
              destruct (ihEL (b0 :: rest) ls h0 heb) as [_ hEL].
              assert (s0 : forall S_tail,
                Reach (cfg_EL1 (0 :: encBlks_N (0%N :: b0 :: rest)) (0 :: S_tail))
                      (cfg_EL1 (0 :: encBlks_N (b0 :: rest)) (0 :: 2 :: S_tail))).
              { intro S_tail.
                rewrite (encBlks_N_zero_cons (bs := b0 :: rest) ltac:(discriminate)).
                rstep (step_EL1_zero (2 :: encBlks_N (b0 :: rest)) (0 :: S_tail)).
                rdone (step_CL1_add_three 0 (encBlks_N (b0 :: rest)) (1 :: S_tail)). }
              destruct h0.
              ** destruct (ihRS ls [(r_z0, 0%N); (r_z2, 0%N)] out has0 h) as [hne hRS].
                 split; [exact hne | intro S_tail].
                 exact (reach_trans (reach_trans (s0 S_tail) (hEL (2 :: S_tail))) (hRS S_tail)).
              ** destruct (ihRS ls [(r_z2, 0%N)] out has0 h) as [hne hRS].
                 split; [exact hne | intro S_tail].
                 exact (reach_trans (reach_trans (s0 S_tail) (hEL (2 :: S_tail))) (hRS S_tail)).
        -- destruct (subTail 1%N (a :: b0 :: rest)) as [out' |] eqn:hst.
           ++ inversion h; subst; clear h.
              split; [exact (subTail_ne_nil hst) |
                      intro S_tail; exact (mEL_subTail_one _ _ _ eq_refl hst S_tail)].
           ++ destruct (evalBody fuel' (b0 :: rest)) as [[ls h0] |] eqn:heb; [| discriminate h].
              destruct (ihEL (b0 :: rest) ls h0 heb) as [_ hEL].
              assert (s0 : forall S_tail,
                Reach (cfg_EL1 (0 :: encBlks_N (a :: b0 :: rest)) (0 :: S_tail))
                      (cfg_EL1 (0 :: encBlks_N (b0 :: rest))
                               (0 :: 2 :: (rep02 (N.to_nat a) ++ S_tail)))).
              { intro S_tail.
                change (encBlks_N (a :: b0 :: rest)) with
                  (rep4 (N.to_nat a) ++ 2 :: encBlks_N (b0 :: rest)).
                rstep (sweep_EL_f4 (N.to_nat a) (2 :: encBlks_N (b0 :: rest)) S_tail).
                rstep (step_EL1_zero (2 :: encBlks_N (b0 :: rest)) (0 :: (rep02 (N.to_nat a) ++ S_tail))).
                rdone (step_CL1_add_three 0 (encBlks_N (b0 :: rest)) (1 :: (rep02 (N.to_nat a) ++ S_tail))). }
              destruct h0.
              ** destruct (ihRS ls [(r_z0, 0%N); (r_z2, 0%N); (r_p, a)] out has0 h) as [hne hRS].
                 split; [exact hne | intro S_tail].
                 pose proof (hRS S_tail) as hRS'; cbn [encR_N app] in hRS'; rewrite app_nil_r in hRS'.
                 exact (reach_trans (reach_trans (s0 S_tail) (hEL (2 :: (rep02 (N.to_nat a) ++ S_tail)))) hRS').
              ** destruct (ihRS ls [(r_z2, 0%N); (r_p, a)] out has0 h) as [hne hRS].
                 split; [exact hne | intro S_tail].
                 pose proof (hRS S_tail) as hRS'; cbn [encR_N app] in hRS'; rewrite app_nil_r in hRS'.
                 exact (reach_trans (reach_trans (s0 S_tail) (hEL (2 :: (rep02 (N.to_nat a) ++ S_tail)))) hRS').
    + (* runStream (S fuel') *)
      intros ls rs out has0 h.
      destruct ls as [| a tl]; [discriminate h |].
      destruct rs as [| [tag val] rs']; [inversion h; subst; split; [discriminate | intro; apply reach_refl] |].
      destruct tag.
      * (* r_z0 *)
        destruct rs' as [| [tag2 val2] rs2].
        -- inversion h; subst; clear h.
           split; [discriminate | intro S_tail; apply reach_refl].
        -- destruct tag2.
           ++ (* r_z0 :: r_z0 *)
              cbn [runStream] in h.
              destruct (ihRS (0%N :: a :: tl) rs2 out has0 h) as [hne hRS].
              split; [exact hne | intro S_tail].
              cbn [encR_N app].
              pose proof (step_BR1_00 (encBlks_N (a :: tl)) (encR_N rs2 ++ S_tail)) as s00.
              rewrite <- (encBlks_N_zero_cons (bs := a :: tl) ltac:(discriminate)) in s00.
              exact (reach_trans s00 (hRS S_tail)).
           ++ (* r_z0 :: r_z2 *)
              cbn [runStream] in h.
              destruct (ihRS ((a + 1)%N :: tl) rs2 out has0 h) as [hne hRS].
              split; [exact hne | intro S_tail].
              cbn [encR_N app].
              pose proof (sweep_BR_p02_one (encBlks_N (a :: tl)) (encR_N rs2 ++ S_tail)) as s1.
              change (4 :: encBlks_N (a :: tl)) with (rep4 (N.to_nat 1%N) ++ encBlks_N (a :: tl)) in s1.
              rewrite (encBlks_N_add_head a 1%N tl) in s1.
              exact (reach_trans s1 (hRS S_tail)).
           ++ (* r_z0 :: r_p *)
              cbn [runStream] in h.
              destruct (N.eqb val2 0%N) eqn:hv0.
              ** apply N.eqb_eq in hv0; subst val2.
                 destruct (ihRS (a :: tl) ((r_z0, 0%N) :: rs2) out has0 h) as [hne hRS].
                 split; [exact hne | intro S_tail; exact (hRS S_tail)].
              ** apply N.eqb_neq in hv0.
                 set (m_n := (val2 - 1)%N).
                 assert (hval_nat : N.to_nat val2 = N.to_nat m_n + 1) by (unfold m_n; lia).
                 destruct (subTail 2%N (a :: tl)) as [ls2 |] eqn:hst.
                 --- fold m_n in h.
                     destruct (ihRS (m_n :: ls2) rs2 out has0 h) as [hne hRS].
                     split; [exact hne | intro S_tail].
                     cbn [encR_N app]; rewrite <- app_assoc, hval_nat.
                     exact (reach_trans (zero_p02_subTail m_n hst (encR_N rs2 ++ S_tail)) (hRS S_tail)).
                 --- destruct (N.eqb val2 1%N) eqn:hm1.
                     +++ apply N.eqb_eq in hm1; subst val2.
                         destruct (ihRS (0%N :: a :: tl) ((r_z2, 0%N) :: rs2) out has0 h) as [hne hRS].
                         split; [exact hne | intro S_tail].
                         change (N.to_nat 1%N) with 1; cbn [encR_N rep02 app].
                         pose proof (step_BR1_00 (encBlks_N (a :: tl)) (2 :: (encR_N rs2 ++ S_tail))) as s00.
                         rewrite <- (encBlks_N_zero_cons (bs := a :: tl) ltac:(discriminate)) in s00.
                         exact (reach_trans s00 (hRS S_tail)).
                     +++ fold m_n in h.
                         destruct (ihRS (0%N :: a :: tl) ((r_z2, 0%N) :: (r_p, m_n) :: rs2) out has0 h)
                           as [hne hRS].
                         split; [exact hne | intro S_tail].
                         cbn [encR_N app]; rewrite <- app_assoc, hval_nat, rep02_succ_r; cbn [app].
                         pose proof (step_BR1_00 (encBlks_N (a :: tl))
                           (2 :: (rep02 (N.to_nat m_n) ++ (encR_N rs2 ++ S_tail)))) as s00.
                         rewrite <- (encBlks_N_zero_cons (bs := a :: tl) ltac:(discriminate)) in s00.
                         pose proof (hRS S_tail) as hRS'; cbn [encR_N app] in hRS'; rewrite <- app_assoc in hRS'.
                         exact (reach_trans s00 hRS').
      * (* r_z2 *)
        cbn [runStream] in h.
        destruct (evalBody fuel' (a :: tl)) as [[ls2 h2] |] eqn:heb; [| discriminate h].
        destruct (ihEL (a :: tl) ls2 h2 heb) as [hls2_ne hEL].
        destruct h2.
        -- destruct (ihRS (0%N :: ls2) rs' out has0 h) as [hne hRS].
           split; [exact hne | intro S_tail].
           cbn [encR_N app].
           assert (sc : Reach (cfg_BR1 (0 :: encBlks_N (a :: tl)) (2 :: (encR_N rs' ++ S_tail)))
                              (cfg_EL1 (0 :: encBlks_N (a :: tl)) (0 :: 0 :: (encR_N rs' ++ S_tail)))).
           { rstep (step_BR1_ge2 0 (0 :: encBlks_N (a :: tl)) (encR_N rs' ++ S_tail)).
             rdone (step_EL1_add_two 0 (encBlks_N (a :: tl)) (0 :: (encR_N rs' ++ S_tail))). }
           pose proof (step_BR1_00 (encBlks_N ls2) (encR_N rs' ++ S_tail)) as s00.
           rewrite <- (encBlks_N_zero_cons hls2_ne) in s00.
           exact (reach_trans (reach_trans (reach_trans sc (hEL (0 :: (encR_N rs' ++ S_tail)))) s00) (hRS S_tail)).
        -- destruct (ihRS ls2 ((r_z0, 0%N) :: rs') out has0 h) as [hne hRS].
           split; [exact hne | intro S_tail].
           cbn [encR_N app].
           assert (sc : Reach (cfg_BR1 (0 :: encBlks_N (a :: tl)) (2 :: (encR_N rs' ++ S_tail)))
                              (cfg_EL1 (0 :: encBlks_N (a :: tl)) (0 :: 0 :: (encR_N rs' ++ S_tail)))).
           { rstep (step_BR1_ge2 0 (0 :: encBlks_N (a :: tl)) (encR_N rs' ++ S_tail)).
             rdone (step_EL1_add_two 0 (encBlks_N (a :: tl)) (0 :: (encR_N rs' ++ S_tail))). }
           exact (reach_trans (reach_trans sc (hEL (0 :: (encR_N rs' ++ S_tail)))) (hRS S_tail)).
      * (* r_p *)
        cbn [runStream] in h.
        destruct (ihRS ((a + val)%N :: tl) rs' out has0 h) as [hne hRS].
        split; [exact hne | intro S_tail].
        cbn [encR_N]; rewrite <- app_assoc.
        pose proof (sweep_BR_p02 (N.to_nat val) (encBlks_N (a :: tl)) (encR_N rs' ++ S_tail)) as s1.
        rewrite (encBlks_N_add_head a val tl) in s1.
        exact (reach_trans s1 (hRS S_tail)).
Qed.

(** ** Exact scan55 and Base Hub Lemmas *)

Lemma el_00_p02_end (k : nat) (S_tail : list nat) :
  Reach (cfg_EL1 [0; 0] (rep02 (k + 3) ++ S_tail))
        (cfg_BR1 (0 :: (rep4 k ++ 2 :: rep4 8)) S_tail).
Proof.
  replace (k + 3) with (S (S (S k))) by lia; cbn [rep02 app].
  assert (h0 : Reach (cfg_EL1 [0; 0] (0 :: 2 :: 0 :: 2 :: 0 :: 2 :: (rep02 k ++ S_tail)))
                     (cfg_BR1 [0; 6] (2 :: 0 :: 2 :: 0 :: 2 :: (rep02 k ++ S_tail)))).
  { rstep (step_EL1_zero [0] (0 :: 2 :: 0 :: 2 :: 0 :: 2 :: (rep02 k ++ S_tail))).
    rstep (step_CL1_one [] (1 :: 2 :: 0 :: 2 :: 0 :: 2 :: (rep02 k ++ S_tail))).
    rstep (step_CL1_zero [] (3 :: 2 :: 0 :: 2 :: 0 :: 2 :: (rep02 k ++ S_tail))).
    rstep (step_CL1_nil (5 :: 2 :: 0 :: 2 :: 0 :: 2 :: (rep02 k ++ S_tail))).
    rdone (step_EL1_nil_cons 6 (2 :: 0 :: 2 :: 0 :: 2 :: (rep02 k ++ S_tail))). }
  pose proof (br_6_202_step (0 :: 2 :: (rep02 k ++ S_tail))) as h1.
  pose proof (br_rep4_6_002_step (rep02 k ++ S_tail)) as h2.
  pose proof (sweep_BR_p02 k (2 :: rep4 8) S_tail) as h3.
  exact (reach_trans (reach_trans (reach_trans h0 h1) h2) h3).
Qed.

Lemma hub_0_zero : Reach (encHub p0 [0%N]) (encHub p03 [0%N]).
Proof.
  unfold encHub, encPfx, encBlks_N; cbn [List.map encBlks rep4 app].
  rstep (step_BR1_nil [0]).
  rstep (step_CL1_zero [] [0]).
  rstep (step_CL1_nil [2]).
  rdone (step_EL1_nil_cons 3 []).
Qed.

Lemma hub_055_one_single : Reach (encHub p055 [1%N]) (encHub p05 [0%N; 6%N]).
Proof.
  unfold encHub, encPfx, encBlks_N.
  change (List.map N.to_nat [1%N]) with [1].
  change (List.map N.to_nat [0%N; 6%N]) with [0; 6].
  cbn [encBlks rep4 app].
  pose proof (step_BR1_nil [0; 5; 5; 4]) as h1.
  assert (h2 : Reach (cfg_CL1 [0; 5; 5; 4] [0]) (cfg_BR1 (0 :: 5 :: 2 :: rep4 6) [])).
  { exact (@run4_of_check 132 (mCL, ([0; 5; 5; 4], [0])) (mBR, (0 :: 5 :: 2 :: rep4 6, []))
      ltac:(vm_compute; reflexivity) []). }
  exact (reach_trans h1 h2).
Qed.

Lemma hub_055_single_ge2 (k : N) :
  Reach (encHub p055 [(k + 2)%N]) (cfg_BR1 (0 :: encBlks_N [k; 8%N]) [0; 0; 3]).
Proof.
  unfold encHub, encPfx, encBlks_N; cbn [List.map encBlks].
  rewrite N2Nat.inj_add.
  change (N.to_nat 2%N) with 2; change (N.to_nat 8%N) with 8; cbn [app].
  set (kn := N.to_nat k).
  assert (h0 : Reach (cfg_BR1 (0 :: 5 :: 5 :: rep4 (kn + 2)) [])
                     (cfg_CL1 (6 :: rep4 (kn + 2)) [1; 0; 3])).
  { rstep (step_BR1_nil (0 :: 5 :: 5 :: rep4 (kn + 2))).
    rstep (step_CL1_zero (5 :: 5 :: rep4 (kn + 2)) [0]).
    rstep (step_CL1_add_three 2 (5 :: rep4 (kn + 2)) [2]).
    rstep (step_EL1_add_two 0 (5 :: rep4 (kn + 2)) [0; 3]).
    rdone (step_EL1_zero (5 :: rep4 (kn + 2)) [0; 0; 3]). }
  pose proof (cl_6_rep4_step (kn + 1) 0 [] [0; 3]) as h1.
  rewrite app_nil_r in h1.
  replace ((kn + 1) + 1) with (kn + 2) in h1 by lia.
  replace ((kn + 1) + 2) with (kn + 3) in h1 by lia.
  cbn [inc1] in h1.
  exact (reach_trans (reach_trans h0 h1) (el_00_p02_end kn [0; 0; 3])).
Qed.

Lemma hub_055_entry_zero (L : list nat) :
  Reach (cfg_BR1 (0 :: 5 :: 5 :: 2 :: L) [])
        (cfg_BR1 (0 :: inc1 L) [0; 2; 2; 0; 0; 3]).
Proof.
  rstep (step_BR1_nil (0 :: 5 :: 5 :: 2 :: L)).
  rstep (step_CL1_zero (5 :: 5 :: 2 :: L) [0]).
  rstep (step_CL1_add_three 2 (5 :: 2 :: L) [2]).
  rstep (step_EL1_add_two 0 (5 :: 2 :: L) [0; 3]).
  rstep (step_EL1_zero (5 :: 2 :: L) [0; 0; 3]).
  rstep (step_CL1_add_three 3 (2 :: L) [1; 0; 3]).
  rstep (step_EL1_add_two 1 (2 :: L) [0; 2; 0; 3]).
  rstep (step_EL1_one (2 :: L) [0; 0; 2; 0; 3]).
  rstep (step_EB1_zero (2 :: L) [0; 0; 2; 0; 3]).
  rstep (step_BR1_00 (3 :: L) [2; 0; 3]).
  rstep (step_BR1_ge2 0 (0 :: 2 :: 3 :: L) [0; 3]).
  rstep (step_EL1_add_two 0 (2 :: 3 :: L) [0; 0; 3]).
  rstep (step_EL1_zero (2 :: 3 :: L) [0; 0; 0; 3]).
  rstep (step_CL1_add_three 0 (3 :: L) [1; 0; 0; 3]).
  rstep (step_EL1_zero (3 :: L) [0; 2; 0; 0; 3]).
  rstep (step_CL1_add_three 1 L [1; 2; 0; 0; 3]).
  rstep (step_EL1_one L [0; 2; 2; 0; 0; 3]).
  rdone (step_EB1_zero L [0; 2; 2; 0; 0; 3]).
Qed.

Lemma scan55_end_ge3 (k : nat) (R : list nat) :
  Reach (cfg_BR1 (0 :: 5 :: rep4 (k + 2)) (0 :: 2 :: 2 :: R))
        (cfg_BR1 (0 :: (rep4 k ++ 2 :: rep4 8)) (0 :: 0 :: 2 :: 0 :: R)).
Proof.
  assert (h0 : Reach (cfg_BR1 (0 :: 5 :: rep4 (k + 2)) (0 :: 2 :: 2 :: R))
                     (cfg_CL1 (6 :: rep4 (k + 2)) (1 :: 0 :: 2 :: 0 :: R))).
  { rstep (sweep_BR_p02_one (5 :: rep4 (k + 2)) (2 :: R)).
    rstep (step_BR1_ge2 0 (0 :: 4 :: 5 :: rep4 (k + 2)) R).
    rstep (step_EL1_add_two 0 (4 :: 5 :: rep4 (k + 2)) (0 :: R)).
    rstep (sweep_EL_f4_one (5 :: rep4 (k + 2)) (0 :: R)).
    rdone (step_EL1_zero (5 :: rep4 (k + 2)) (0 :: 0 :: 2 :: 0 :: R)). }
  pose proof (cl_6_rep4_step (k + 1) 0 [] (0 :: 2 :: 0 :: R)) as h1.
  rewrite app_nil_r in h1.
  replace ((k + 1) + 1) with (k + 2) in h1 by lia.
  replace ((k + 1) + 2) with (k + 3) in h1 by lia.
  cbn [inc1] in h1.
  exact (reach_trans (reach_trans h0 h1) (el_00_p02_end k (0 :: 0 :: 2 :: 0 :: R))).
Qed.

Lemma scan55_zero_end_ge3 (k : nat) (R : list nat) :
  Reach (cfg_BR1 (0 :: 3 :: rep4 (k + 3)) (0 :: 2 :: 2 :: (0 :: 2 :: R)))
        (cfg_BR1 (0 :: (rep4 k ++ 2 :: rep4 8)) (0 :: 0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R)).
Proof.
  replace (k + 3) with (S (k + 2)) by lia; cbn [rep4].
  set (L := rep4 (k + 2)).
  assert (hc12 : Reach (cfg_BR1 (0 :: 3 :: 4 :: L) (0 :: 2 :: 2 :: (0 :: 2 :: R)))
                       (cfg_CL1 (6 :: L) (1 :: 0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R))).
  { rstep (sweep_BR_p02_one (3 :: 4 :: L) (2 :: 0 :: 2 :: R)).
    rstep (step_BR1_ge2 0 (0 :: 4 :: 3 :: 4 :: L) (0 :: 2 :: R)).
    rstep (step_EL1_add_two 0 (4 :: 3 :: 4 :: L) (0 :: 0 :: 2 :: R)).
    rstep (sweep_EL_f4_one (3 :: 4 :: L) (0 :: 0 :: 2 :: R)).
    rstep (step_EL1_zero (3 :: 4 :: L) (0 :: 0 :: 2 :: 0 :: 0 :: 2 :: R)).
    rstep (step_CL1_add_three 1 (4 :: L) (1 :: 0 :: 2 :: 0 :: 0 :: 2 :: R)).
    rstep (step_EL1_one (4 :: L) (0 :: 2 :: 0 :: 2 :: 0 :: 0 :: 2 :: R)).
    rstep (step_EB1_zero (4 :: L) (0 :: 2 :: 0 :: 2 :: 0 :: 0 :: 2 :: R)).
    rstep (sweep_BR_p02 2 (5 :: L) (0 :: 0 :: 2 :: R)).
    rstep (step_BR1_00 (4 :: 4 :: 5 :: L) (2 :: R)).
    rstep (step_BR1_ge2 0 (0 :: 2 :: 4 :: 4 :: 5 :: L) R).
    rstep (step_EL1_add_two 0 (2 :: 4 :: 4 :: 5 :: L) (0 :: R)).
    rstep (step_EL1_zero (2 :: 4 :: 4 :: 5 :: L) (0 :: 0 :: R)).
    rstep (step_CL1_add_three 0 (4 :: 4 :: 5 :: L) (1 :: 0 :: R)).
    rstep (sweep_EL_f4 2 (5 :: L) (2 :: 0 :: R)).
    rdone (step_EL1_zero (5 :: L) (0 :: 0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R)). }
  unfold L in hc12.
  pose proof (cl_6_rep4_step (k + 1) 0 [] (0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R)) as h1.
  rewrite app_nil_r in h1.
  replace ((k + 1) + 1) with (k + 2) in h1 by lia.
  replace ((k + 1) + 2) with (k + 3) in h1 by lia.
  cbn [inc1] in h1.
  exact (reach_trans (reach_trans hc12 h1) (el_00_p02_end k (0 :: 0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R))).
Qed.

Fixpoint scan55 (bs : list N) (rs : list (RTag * N)) :
  option (list N * list (RTag * N)) :=
  match bs with
  | [] => None
  | b0 :: rest =>
    match rest with
    | [] =>
      if N.leb 3%N b0 then
        Some ([(b0 - 3)%N; 8%N], (r_z0, 0%N) :: (r_p, 1%N) :: (r_z0, 0%N) :: rs)
      else None
    | c0 :: tl =>
      if N.eqb b0 0%N then
        match tl, rs with
        | [], (r_p, m) :: rs' =>
          if andb (N.leb 3%N c0) (N.leb 1%N m) then
            Some ([(c0 - 3)%N; 8%N],
              (r_z0, 0%N) :: (r_p, 1%N) :: (r_z0, 0%N) :: (r_z2, 0%N) :: (r_z2, 0%N) :: (r_z0, 0%N) ::
                (if N.eqb m 1%N then rs' else (r_p, (m - 1)%N) :: rs'))
          else None
        | _, _ => None
        end
      else if N.leb 2%N b0 then
        scan55 rest ((r_p, (b0 - 1)%N) :: (r_z0, 0%N) :: (r_p, 1%N) :: (r_z0, 0%N) :: rs)
      else None
    end
  end.

Lemma scan55_cons_cons (b0 c0 : N) (tl : list N) (rs : list (RTag * N)) :
  scan55 (b0 :: c0 :: tl) rs =
    if N.eqb b0 0%N then
      match tl, rs with
      | [], (r_p, m) :: rs' =>
        if andb (N.leb 3%N c0) (N.leb 1%N m) then
          Some ([(c0 - 3)%N; 8%N],
            (r_z0, 0%N) :: (r_p, 1%N) :: (r_z0, 0%N) :: (r_z2, 0%N) :: (r_z2, 0%N) :: (r_z0, 0%N) ::
              (if N.eqb m 1%N then rs' else (r_p, (m - 1)%N) :: rs'))
        else None
      | _, _ => None
      end
    else if N.leb 2%N b0 then
      scan55 (c0 :: tl) ((r_p, (b0 - 1)%N) :: (r_z0, 0%N) :: (r_p, 1%N) :: (r_z0, 0%N) :: rs)
    else None.
Proof. reflexivity. Qed.

Lemma scan55_sound (bs : list N) :
  forall (rs : list (RTag * N)) (ls' : list N) (rs' : list (RTag * N)),
    scan55 bs rs = Some (ls', rs') ->
    forall S_tail : list nat,
      Reach (cfg_BR1 (0 :: inc1 (encBlks_N bs)) (0 :: 2 :: 2 :: (encR_N rs ++ S_tail)))
            (cfg_BR1 (0 :: encBlks_N ls') (encR_N rs' ++ S_tail)).
Proof.
  induction bs as [| b0 [| c0 tl] IH]; intros rs ls' rs' h S_tail.
  - discriminate h.
  - cbn [scan55] in h.
    destruct (N.leb 3%N b0) eqn:hb; [| discriminate h].
    apply N.leb_le in hb.
    inversion h; subst; clear h.
    set (kn := N.to_nat (b0 - 3)%N).
    assert (hb_nat : N.to_nat b0 = (kn + 2) + 1) by (unfold kn; lia).
    unfold encBlks_N; cbn [List.map encBlks].
    change (N.to_nat 8%N) with 8; change (N.to_nat 1%N) with 1.
    rewrite hb_nat, rep4_succ_r; cbn [inc1 encR_N rep02 app].
    exact (scan55_end_ge3 kn (encR_N rs ++ S_tail)).
  - rewrite scan55_cons_cons in h.
    destruct (N.eqb b0 0%N) eqn:hb0.
    + apply N.eqb_eq in hb0; subst b0.
      destruct tl as [| x0 xtl]; [| discriminate h].
      destruct rs as [| [tag0 m] rt]; [discriminate h |].
      destruct tag0; try discriminate h.
      destruct (andb (N.leb 3%N c0) (N.leb 1%N m)) eqn:hcond; [| discriminate h].
      apply Bool.andb_true_iff in hcond as [hc hm].
      apply N.leb_le in hc; apply N.leb_le in hm.
      inversion h; subst; clear h.
      set (kn := N.to_nat (c0 - 3)%N).
      assert (hc_nat : N.to_nat c0 = kn + 3) by (unfold kn; lia).
      set (mn := N.to_nat (m - 1)%N).
      assert (hm_nat : N.to_nat m = mn + 1) by (unfold mn; lia).
      unfold encBlks_N; cbn [List.map encBlks rep4 inc1 app].
      change (N.to_nat 8%N) with 8; rewrite hc_nat.
      cbn [encR_N]; rewrite <- app_assoc, hm_nat, rep02_succ_r; cbn [app].
      destruct (N.eqb m 1%N) eqn:hm1.
      * apply N.eqb_eq in hm1.
        assert (hmn0 : mn = 0) by (unfold mn; lia).
        rewrite hmn0; cbn [rep02 app].
        change (N.to_nat 1%N) with 1; cbn [encR_N rep02 app].
        exact (scan55_zero_end_ge3 kn (encR_N rt ++ S_tail)).
      * change (N.to_nat 1%N) with 1; cbn [encR_N rep02 app]; rewrite <- app_assoc.
        fold mn.
        exact (scan55_zero_end_ge3 kn (rep02 mn ++ (encR_N rt ++ S_tail))).
    + destruct (N.leb 2%N b0) eqn:hb2; [| discriminate h].
      apply N.leb_le in hb2.
      pose proof (IH ((r_p, (b0 - 1)%N) :: (r_z0, 0%N) :: (r_p, 1%N) :: (r_z0, 0%N) :: rs)
                     ls' rs' h S_tail) as ih_step.
      set (kn := N.to_nat (b0 - 2)%N).
      assert (hb1_nat : N.to_nat (b0 - 1)%N = kn + 1) by (unfold kn; lia).
      assert (hb0_nat : N.to_nat b0 = (kn + 1) + 1) by (unfold kn; lia).
      cbn [encR_N] in ih_step; change (N.to_nat 1%N) with 1 in ih_step;
        cbn [rep02 app] in ih_step; rewrite <- app_assoc in ih_step; rewrite hb1_nat in ih_step.
      assert (hstep :
        Reach (cfg_BR1 (0 :: inc1 (encBlks_N (b0 :: c0 :: tl))) (0 :: 2 :: 2 :: (encR_N rs ++ S_tail)))
              (cfg_BR1 (0 :: inc1 (encBlks_N (c0 :: tl)))
                       (0 :: 2 :: 2 :: (rep02 (kn + 1) ++ (0 :: 0 :: 2 :: 0 :: (encR_N rs ++ S_tail)))))).
      { change (encBlks_N (b0 :: c0 :: tl)) with (rep4 (N.to_nat b0) ++ 2 :: encBlks_N (c0 :: tl)).
        rewrite hb0_nat, inc1_rep4_succ.
        exact (scan_55_ge2 kn (encBlks_N (c0 :: tl)) (encR_N rs ++ S_tail)). }
      exact (reach_trans hstep ih_step).
Qed.

(** ** Top-Level Hub Stepper stepHub, runHubs, and Checkers *)

Definition finishD3 (fuel : nat) (ls : list N) (has0 : bool) : option (Pfx * list N) :=
  if has0 then Some (p05, ls)
  else
    match evalBody fuel ls with
    | None => None
    | Some (ls1, true) => Some (p03, ls1)
    | Some (ls1, false) =>
      match evalBody fuel ls1 with
      | None => None
      | Some (_, true) => None
      | Some (ls2, false) => Some (p0, ls2)
      end
    end.

Lemma finishD3_sound {fuel : nat} {ls : list N} {has0 : bool} {pf' : Pfx} {bs' : list N}
  (h : finishD3 fuel ls has0 = Some (pf', bs')) :
  Reach (cfg_BR1 (0 :: encBlks_N ls) (if has0 then [0; 3] else [3])) (encHub pf' bs').
Proof.
  unfold finishD3 in h.
  destruct has0.
  - inversion h; subst; clear h.
    exact (step_BR1_0d 3 (encBlks_N bs') []).
  - destruct (evalBody fuel ls) as [[ls1 h1] |] eqn:heb1; [| discriminate h].
    destruct ((proj1 (eval_run_sound fuel)) ls ls1 h1 heb1) as [_ hEL1].
    destruct h1.
    + inversion h; subst; clear h.
      exact (reach_trans (reach_trans (br_d3_to_el (encBlks_N ls)) (hEL1 [1]))
                         (step_BR1_0d 1 (encBlks_N bs') [])).
    + destruct (evalBody fuel ls1) as [[ls2 h2] |] eqn:heb2; [| discriminate h].
      destruct ((proj1 (eval_run_sound fuel)) ls1 ls2 h2 heb2) as [_ hEL2].
      destruct h2; [discriminate h |].
      inversion h; subst; clear h.
      exact (reach_trans
        (reach_trans (reach_trans (br_d3_to_el (encBlks_N ls)) (hEL1 [1]))
                     (br_d1_to_el (encBlks_N ls1)))
        (hEL2 [])).
Qed.

Definition stepHub (fuel : nat) (st : Pfx * list N) : option (Pfx * list N) :=
  match st with
  | (p0, []) => None
  | (p0, a :: tl) =>
    if N.eqb a 0%N then
      match tl with
      | [] => Some (p03, [0%N])
      | _ :: _ => None
      end
    else if N.leb 2%N a then
      Some (p055, (a - 2)%N :: tl)
    else None
  | (p03, bs) =>
    match subTail 3%N bs with
    | Some out => Some (p0, out)
    | None =>
      match evalBody fuel bs with
      | None => None
      | Some (ls1, h1) => finishD3 fuel ls1 h1
      end
    end
  | (p05, bs) =>
    match subTail 1%N bs with
    | Some out => Some (p05, out)
    | None =>
      match evalBody fuel bs with
      | None => None
      | Some (ls1, true) => finishD3 fuel (0%N :: ls1) false
      | Some (ls1, false) => finishD3 fuel ls1 true
      end
    end
  | (p055, []) => None
  | (p055, [a]) =>
    if N.eqb a 1%N then Some (p05, [0%N; 6%N])
    else if N.leb 2%N a then
      match runStream fuel [(a - 2)%N; 8%N] [(r_z0, 0%N); (r_z0, 0%N)] with
      | None => None
      | Some (lout, hout) => finishD3 fuel lout hout
      end
    else None
  | (p055, a :: c0 :: tl) =>
    if N.eqb a 0%N then
      match scan55 (c0 :: tl) [(r_z0, 0%N); (r_z0, 0%N)] with
      | None => None
      | Some (le, re) =>
        match runStream fuel le re with
        | None => None
        | Some (lout, hout) => finishD3 fuel lout hout
        end
      end
    else
      match scan55 (c0 :: tl) [(r_p, a); (r_z0, 0%N); (r_z0, 0%N)] with
      | None => None
      | Some (le, re) =>
        match runStream fuel le re with
        | None => None
        | Some (lout, hout) => finishD3 fuel lout hout
        end
      end
  end.

Lemma stepHub_sound {fuel : nat} {s s' : Pfx * list N}
  (h : stepHub fuel s = Some s') :
  Reach (encHub (fst s) (snd s)) (encHub (fst s') (snd s')).
Proof.
  destruct s as [pf bs], s' as [pf' bs']; cbn [fst snd].
  destruct pf.
  - (* p0 *)
    destruct bs as [| a tl]; [discriminate h |].
    cbn [stepHub] in h.
    destruct (N.eqb a 0%N) eqn:ha0.
    + apply N.eqb_eq in ha0; subst a.
      destruct tl as [| x0 xtl]; [| discriminate h].
      inversion h; subst; exact hub_0_zero.
    + destruct (N.leb 2%N a) eqn:ha2; [| discriminate h].
      apply N.leb_le in ha2.
      inversion h; subst; clear h.
      assert (heq : N.to_nat a = N.to_nat (a - 2)%N + 2) by lia.
      destruct tl as [| b0 rest].
      * unfold encHub, encPfx, encBlks_N; cbn [List.map encBlks app].
        pose proof (hub_0_step (N.to_nat (a - 2)%N) []) as hs.
        rewrite !app_nil_r in hs; rewrite <- heq in hs.
        exact hs.
      * unfold encHub, encPfx; change (encBlks_N (a :: b0 :: rest)) with
          (rep4 (N.to_nat a) ++ 2 :: encBlks_N (b0 :: rest));
        change (encBlks_N ((a - 2)%N :: b0 :: rest)) with
          (rep4 (N.to_nat (a - 2)%N) ++ 2 :: encBlks_N (b0 :: rest));
        cbn [app].
        rewrite heq.
        exact (hub_0_step (N.to_nat (a - 2)%N) (2 :: encBlks_N (b0 :: rest))).
  - (* p03 *)
    cbn [stepHub] in h.
    destruct (subTail 3%N bs) as [out |] eqn:hst.
    + inversion h; subst; exact (hub_03_subTail hst).
    + destruct (evalBody fuel bs) as [[ls1 h1] |] eqn:heb; [| discriminate h].
      destruct ((proj1 (eval_run_sound fuel)) bs ls1 h1 heb) as [_ hEL].
      exact (reach_trans (reach_trans (hub_03_entry (encBlks_N bs)) (hEL [3]))
                         (finishD3_sound h)).
  - (* p05 *)
    cbn [stepHub] in h.
    destruct (subTail 1%N bs) as [out |] eqn:hst.
    + inversion h; subst; exact (hub_05_subTail_one hst).
    + destruct (evalBody fuel bs) as [[ls1 h1] |] eqn:heb; [| discriminate h].
      destruct ((proj1 (eval_run_sound fuel)) bs ls1 h1 heb) as [hls1_ne hEL].
      destruct h1.
      * pose proof (step_BR1_00 (encBlks_N ls1) [3]) as s00.
        rewrite <- (encBlks_N_zero_cons hls1_ne) in s00.
        exact (reach_trans (reach_trans (reach_trans (hub_05_entry (encBlks_N bs)) (hEL [0; 3])) s00)
                           (finishD3_sound h)).
      * exact (reach_trans (reach_trans (hub_05_entry (encBlks_N bs)) (hEL [0; 3]))
                           (finishD3_sound h)).
  - (* p055 *)
    destruct bs as [| a [| c0 rest]]; [discriminate h | |].
    + cbn [stepHub] in h.
      destruct (N.eqb a 1%N) eqn:ha1.
      * apply N.eqb_eq in ha1; subst a.
        inversion h; subst; exact hub_055_one_single.
      * destruct (N.leb 2%N a) eqn:ha2; [| discriminate h].
        apply N.leb_le in ha2.
        destruct (runStream fuel [(a - 2)%N; 8%N] [(r_z0, 0%N); (r_z0, 0%N)])
          as [[lout hout] |] eqn:hrs; [| discriminate h].
        destruct ((proj2 (eval_run_sound fuel)) [(a - 2)%N; 8%N] [(r_z0, 0%N); (r_z0, 0%N)] lout hout hrs)
          as [_ hRS].
        pose proof (hub_055_single_ge2 (a - 2)%N) as hs0.
        replace ((a - 2) + 2)%N with a in hs0 by lia.
        exact (reach_trans (reach_trans hs0 (hRS [3])) (finishD3_sound h)).
    + cbn [stepHub] in h.
      destruct (N.eqb a 0%N) eqn:ha0.
      * apply N.eqb_eq in ha0; subst a.
        destruct (scan55 (c0 :: rest) [(r_z0, 0%N); (r_z0, 0%N)]) as [[le re] |] eqn:hsc; [| discriminate h].
        destruct (runStream fuel le re) as [[lout hout] |] eqn:hrs; [| discriminate h].
        pose proof (hub_055_entry_zero (encBlks_N (c0 :: rest))) as s0.
        pose proof (scan55_sound (c0 :: rest) [(r_z0, 0%N); (r_z0, 0%N)] le re hsc [3]) as s1.
        destruct ((proj2 (eval_run_sound fuel)) le re lout hout hrs) as [_ hRS].
        exact (reach_trans (reach_trans (reach_trans s0 s1) (hRS [3])) (finishD3_sound h)).
      * apply N.eqb_neq in ha0.
        destruct (scan55 (c0 :: rest) [(r_p, a); (r_z0, 0%N); (r_z0, 0%N)]) as [[le re] |] eqn:hsc; [| discriminate h].
        destruct (runStream fuel le re) as [[lout hout] |] eqn:hrs; [| discriminate h].
        set (k0 := N.to_nat (a - 1)%N).
        assert (ha_nat : N.to_nat a = k0 + 1) by (unfold k0; lia).
        pose proof (hub_055_entry k0 (encBlks_N (c0 :: rest))) as s0.
        pose proof (scan55_sound (c0 :: rest) [(r_p, a); (r_z0, 0%N); (r_z0, 0%N)] le re hsc [3]) as s1.
        cbn [encR_N app] in s1; rewrite <- app_assoc in s1; rewrite ha_nat in s1.
        destruct ((proj2 (eval_run_sound fuel)) le re lout hout hrs) as [_ hRS].
        change (encHub p055 (a :: c0 :: rest)) with
          (cfg_BR1 (0 :: 5 :: 5 :: (rep4 (N.to_nat a) ++ 2 :: encBlks_N (c0 :: rest))) []).
        rewrite ha_nat.
        exact (reach_trans (reach_trans (reach_trans s0 s1) (hRS [3])) (finishD3_sound h)).
Qed.

Lemma encHub_p055_3 (a b c d : N) (rest : list N) :
  encHub p055 (a :: b :: c :: d :: rest) =
    cfg_BR1 (0 :: 5 :: 5 ::
      (rep4 (N.to_nat a) ++ 2 ::
       (rep4 (N.to_nat b) ++ 2 ::
        (rep4 (N.to_nat c) ++ (2 :: encBlks_N (d :: rest)))))) [].
Proof.
  reflexivity.
Qed.

Definition terminal (s : Pfx * list N) : bool :=
  match s with
  | (p055, a :: b :: c :: _ :: rest) =>
    N.eqb a 156691%N && N.eqb b 3931792%N && N.eqb c 19317108%N &&
    Nat.leb (1 + List.length rest) 14
  | _ => false
  end.

Lemma terminal_sound s :
  terminal s = true -> halts tm (encHub (fst s) (snd s)).
Proof.
  destruct s as [[| | |] [| a [| b [| c [| d rest]]]]]; try discriminate.
  cbn [terminal fst snd].
  rewrite !Bool.andb_true_iff.
  intros [[[Ha Hb] Hc] Hw].
  apply N.eqb_eq in Ha, Hb, Hc. subst a b c.
  rewrite encHub_p055_3. apply halts_from_H11120.
  change (1 + W (encBlks_N (d :: rest)) <= 14).
  rewrite W_encBlks_N_cons. now apply Nat.leb_le.
Qed.

(* d is affordable if each nonfinal block b_i can pay 4^i * d.
   None denotes no bound from the remaining blocks. *)
Fixpoint allowance (bs : list N) : option N :=
  match bs with
  | [] => None
  | a :: tl =>
    match tl with
    | [] => None
    | _ :: _ =>
      Some (match allowance tl with
            | Some d => N.min a (N.div d 4)
            | None => a
            end)
    end
  end.

Definition stepHubFast (s : Pfx * list N) : option (Pfx * list N) :=
  match s with
  | (p05, bs) =>
    match allowance bs with
    | Some (Npos p) => option_map (fun out => (p05,out)) (subTail (Npos p) bs)
    | _ => stepHub 200 s
    end
  | _ => stepHub 200 s
  end.

Lemma stepHubFast_sound s out :
  stepHubFast s = Some out ->
  Reach (encHub (fst s) (snd s)) (encHub (fst out) (snd out)).
Proof.
  destruct s as [p bs], p; cbn [stepHubFast]; try apply stepHub_sound.
  destruct (allowance bs) as [[|p]|]; try apply stepHub_sound.
  destruct (subTail (Npos p) bs) as [r|] eqn:H; try discriminate.
  intros [= <-]. exact (hub_05_batch _ _ _ H).
Qed.

Fixpoint check_hubs (fuel : nat) (s : Pfx * list N) : bool :=
  if terminal s then true else
    match fuel with
    | O => false
    | S f => match stepHubFast s with Some out => check_hubs f out | None => false end
    end.

Lemma check_hubs_sound fuel s : check_hubs fuel s = true ->
  halts tm (encHub (fst s) (snd s)).
Proof.
  revert s. induction fuel as [|f IH]; intros s; cbn [check_hubs];
    destruct (terminal s) eqn:H; try discriminate;
    try (intros _; exact (terminal_sound s H)).
  destruct (stepHubFast s) as [out|] eqn:E; try discriminate.
  intros h. exact (halts_evstep tm _ _ (IH out h) (stepHubFast_sound s out E)).
Qed.

Definition initial_hub : Pfx * list N := (p0, [0%N]).

Lemma check_hubs_ok : check_hubs 1400 initial_hub = true.
Proof. vm_check_eq. Qed.

Lemma is_halt_proof : halts tm c0.
Proof.
  exact (halts_evstep tm _ _ (check_hubs_sound 1400 initial_hub check_hubs_ok) entry_step).
Qed.

End MachineProof.

Theorem halt : halts tm c0.
Proof. exact MachineProof.is_halt_proof. Qed.

Print Assumptions halt.
